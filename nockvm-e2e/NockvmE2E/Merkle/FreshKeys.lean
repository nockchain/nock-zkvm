/-
Merkle (B) file: B's fresh-key bound (support-wise `queryBound`) and `pairMsgs` coherence.
-/
import NockvmE2E.Merkle.Reduction
import NockvmE2E.Merkle.VerifyTransport

open OracleComp OracleSpec MeasureTheory
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.FreshKeys

section Generic

variable {D : Type} {R : D → Type} [DecidableEq D] [∀ d, SampleableType (R d)]

theorem loggedRun_map {α β : Type} (f : α → β) (oa : OracleComp (unifSpec + ofFn R) α)
    (c : (ofFn R).QueryCache) :
    randomOracleLoggedRun (f <$> oa) c =
      (fun r => ((f r.1.1, r.1.2), r.2)) <$> randomOracleLoggedRun oa c := by
  simp [randomOracleLoggedRun, simulateQ_map, StateT.run_map]

/-- Source-level query logging does not change the output, the ordered random-oracle log or the cache. -/
theorem loggedRun_withQueryLog {α : Type} (oa : OracleComp (unifSpec + ofFn R) α)
    (c : (ofFn R).QueryCache) :
    (fun z => ((z.1.1.1, z.1.2), z.2)) <$> randomOracleLoggedRun oa.withQueryLog c =
      randomOracleLoggedRun oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [OracleComp.withQueryLog, randomOracleLoggedRun]
  | query_bind t k ih =>
    rw [show (liftM ((unifSpec + ofFn R).query t) >>= k).withQueryLog = _ from
      OracleComp.run_simulateQ_loggingOracle_query_bind t k]
    rw [randomOracleLoggedRun_bind, randomOracleLoggedRun_bind, map_bind]
    refine bind_congr fun p => ?_
    have h1 := ih p.1.1 p.2
    simp only [loggedRun_map, Functor.map_map]
    rw [← h1]
    simp only [Functor.map_map]
    rfl

/-- One random-oracle step: the answer is cached, and only the queried key can be new. -/
theorem randomOracle_step (t : D) (c : (ofFn R).QueryCache) (p : R t × (ofFn R).QueryCache)
    (hp : p ∈ support (((ofFn R).randomOracle t).run c)) :
    (c t).isSome ∧ p.2 = c ∨ (c t).isNone ∧ p.2 = c.cacheQuery t p.1 := by
  rw [randomOracle.run_eq] at hp
  rcases h : c t with _ | u
  · rw [h] at hp
    simp at hp
    obtain ⟨a, rfl⟩ := hp
    simp [h]
  · rw [h] at hp
    simp at hp
    subst hp
    simp [h]

/-- Cache domain versus log: every key cached by a logged run is old or in its log. -/
theorem loggedRun_cache_log {α : Type} (oa : OracleComp (unifSpec + ofFn R) α)
    (c : (ofFn R).QueryCache) (w : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache)
    (hw : w ∈ support (randomOracleLoggedRun oa c)) (t : D) (ht : (w.2 t).isSome) :
    (c t).isSome ∨ t ∈ freshKeysOfLog w.1.2 := by
  induction oa using OracleComp.inductionOn generalizing c w with
  | pure a =>
    simp [randomOracleLoggedRun] at hw
    subst hw
    exact Or.inl ht
  | query_bind q k ih =>
    rw [randomOracleLoggedRun_bind, mem_support_bind_iff] at hw
    obtain ⟨p, hp, hw⟩ := hw
    rw [support_map] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have h2 := ih p.1.1 p.2 w' hw' ht
    cases q with
    | inl n =>
      rw [randomOracleLoggedRun_uniformQuery, support_map] at hp
      obtain ⟨u, _, rfl⟩ := hp
      simpa using h2
    | inr t' =>
      rw [randomOracleLoggedRun_hashQuery, support_map] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      have hs := randomOracle_step t' c p' hp'
      simp only [mem_freshKeysOfLog, List.mem_append]
      rcases h2 with h2 | h2
      · rcases hs with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · rw [h4] at h2; exact Or.inl h2
        · rw [h4, QueryCache.isSome_cacheQuery_apply_iff] at h2
          rcases h2 with rfl | h2
          · exact Or.inr ⟨⟨_, p'.1⟩, Or.inl (List.mem_singleton_self _), rfl⟩
          · exact Or.inl h2
      · obtain ⟨e, he, rfl⟩ := (mem_freshKeysOfLog _ _).mp h2
        exact Or.inr ⟨e, Or.inr he, rfl⟩

theorem liftComp_logged {α : Type} (oa : ProbComp α) (c : (ofFn R).QueryCache)
    (z : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache)
    (hz : z ∈ support (randomOracleLoggedRun (OracleComp.liftComp oa (unifSpec + ofFn R)) c)) :
    z.1.2 = [] ∧ z.2 = c := by
  induction oa using OracleComp.inductionOn generalizing c z with
  | pure a =>
    simp [randomOracleLoggedRun] at hz
    subst hz; simp
  | query_bind t k ih =>
    simp only [liftComp_bind] at hz
    have hq : liftComp (liftM (OracleSpec.query t) : OracleComp unifSpec (unifSpec.Range t))
        (unifSpec + ofFn R) =
        (liftM ((unifSpec + ofFn R).query (.inl t)) : OracleComp (unifSpec + ofFn R) _) := by
      simp
      rfl
    rw [hq, randomOracleLoggedRun_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [randomOracleLoggedRun_uniformQuery, support_map] at hp
    obtain ⟨u, _, rfl⟩ := hp
    obtain ⟨h1, h2⟩ := ih u c w hw
    simp [h1, h2]

theorem liftComp_map_logged {α β : Type} (f : α → β) (oa : ProbComp α) (c : (ofFn R).QueryCache)
    (z : (β × QueryLog (ofFn R)) × (ofFn R).QueryCache)
    (hz : z ∈ support (randomOracleLoggedRun (f <$> OracleComp.liftComp oa (unifSpec + ofFn R)) c)) :
    z.1.2 = [] ∧ z.2 = c ∧ ∃ a, z.1.1 = f a := by
  rw [loggedRun_map, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨h1, h2⟩ := liftComp_logged oa c w hw
  exact ⟨h1, h2, w.1.1, rfl⟩

theorem query_map_logged {α : Type} (t : D) (f : R t → α) (c : (ofFn R).QueryCache)
    (z : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache)
    (hz : z ∈ support (randomOracleLoggedRun
      (f <$> (liftM ((unifSpec + ofFn R).query (.inr t)) : OracleComp (unifSpec + ofFn R) (R t))) c)) :
    ∃ a, z.1.2 = [⟨t, a⟩] ∧ z.1.1 = f a := by
  rw [loggedRun_map, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [randomOracleLoggedRun_hashQuery, support_map] at hw
  obtain ⟨p, _, rfl⟩ := hw
  exact ⟨p.1, rfl, rfl⟩

end Generic

section Real

open NockvmE2E.Merkle.Rename

variable {Q D σ : Type} [DecidableEq Q] [DecidableEq D] {RH : Q → Type} {R : D → Type}
  [∀ q, SampleableType (RH q)] [∀ d, SampleableType (R d)]
  (obs : σ → (t : Q ⊕ D) → Sum.elim RH R t → σ)

/-- The observed real world is the logged lazy random oracle on its output and cache. -/
theorem realImpl_logged {α : Type} (oa : OracleComp (ClientSpec RH R) α) :
    ∀ (s : σ) (c : (OracleSpec.ofFn (Sum.elim RH R)).QueryCache)
      (z : α × (σ × (OracleSpec.ofFn (Sum.elim RH R)).QueryCache)),
      z ∈ support ((simulateQ (realImpl obs) oa).run (s, c)) →
      ∃ w ∈ support (randomOracleLoggedRun oa c), w.1.1 = z.1 ∧ w.2 = z.2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s c z hz
    simp at hz
    subst hz
    exact ⟨((a, []), c), by simp [randomOracleLoggedRun], rfl, rfl⟩
  | query_bind t k ih =>
    intro s c z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    obtain ⟨w', hw', h1, h2⟩ := ih p.1 p.2.1 p.2.2 z hz
    cases t with
    | inl n =>
      obtain ⟨u, hu, hpu⟩ : ∃ u, u ∈ support (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) ∧
          p = (u, (s, c)) := by
        simp [realImpl] at hp
        obtain ⟨y, rfl⟩ := hp
        exact ⟨y, by simp, rfl⟩
      subst hpu
      refine ⟨((w'.1.1, [] ++ w'.1.2), w'.2), ?_, h1, h2⟩
      rw [randomOracleLoggedRun_bind, mem_support_bind_iff]
      refine ⟨((u, []), c), ?_, ?_⟩
      · rw [randomOracleLoggedRun_uniformQuery, support_map]
        exact ⟨u, hu, rfl⟩
      · rw [support_map]
        exact ⟨w', hw', rfl⟩
    | inr t' =>
      rw [realImpl_run, support_map] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      refine ⟨((w'.1.1, [⟨t', p'.1⟩] ++ w'.1.2), w'.2), ?_, h1, h2⟩
      rw [randomOracleLoggedRun_bind, mem_support_bind_iff]
      refine ⟨((p'.1, [⟨t', p'.1⟩]), p'.2), ?_, ?_⟩
      · rw [randomOracleLoggedRun_hashQuery, support_map]
        exact ⟨p', hp', rfl⟩
      · rw [support_map]
        exact ⟨w', hw', rfl⟩

end Real

section BSide

open NockvmE2E.Merkle.Rename

variable {Q D D' σ : Type} [DecidableEq Q] [DecidableEq D] [DecidableEq D']
  {RH : Q → Type} {R : D → Type} {R' : D' → Type}
  [∀ q, SampleableType (RH q)] [∀ d, SampleableType (R d)] [∀ d', SampleableType (R' d')]

/-- `Good c₀ c₁ log`: the local FS cache grew monotonically from `c₀` to `c₁`, and the distinct keys
of the oracle log are at most the number of keys newly cached. -/
def Good (c₀ c₁ : (OracleSpec.ofFn R).QueryCache) (log : QueryLog (OracleSpec.ofFn R')) : Prop :=
  (∀ d, (c₀ d).isSome → (c₁ d).isSome) ∧
    ∃ F : Finset D, (∀ d ∈ F, (c₀ d).isNone ∧ (c₁ d).isSome) ∧ (freshKeysOfLog log).card ≤ F.card

theorem Good.refl (c : (OracleSpec.ofFn R).QueryCache) : Good c c (R' := R') [] :=
  ⟨fun _ h => h, ∅, by simp, by simp⟩

theorem Good.trans {c₀ c₁ c₂ : (OracleSpec.ofFn R).QueryCache} {l₁ l₂ : QueryLog (OracleSpec.ofFn R')}
    (h₁ : Good c₀ c₁ l₁) (h₂ : Good c₁ c₂ l₂) : Good c₀ c₂ (l₁ ++ l₂) := by
  obtain ⟨m₁, F₁, hF₁, k₁⟩ := h₁
  obtain ⟨m₂, F₂, hF₂, k₂⟩ := h₂
  refine ⟨fun d h => m₂ d (m₁ d h), F₁ ∪ F₂, ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact ⟨(hF₁ d hd).1, m₂ d (hF₁ d hd).2⟩
    · refine ⟨?_, (hF₂ d hd).2⟩
      rcases h : c₀ d with _ | v
      · rfl
      · exfalso
        have := m₁ d (by simp [h])
        have h2 := (hF₂ d hd).1
        simp_all
  · have hdisj : Disjoint F₁ F₂ := by
      rw [Finset.disjoint_left]
      intro d h1 h2
      have a := (hF₁ d h1).2
      have b := (hF₂ d h2).1
      simp_all
    have hsub : freshKeysOfLog (l₁ ++ l₂) ⊆ freshKeysOfLog l₁ ∪ freshKeysOfLog l₂ := by
      intro t ht
      simp only [mem_freshKeysOfLog, List.mem_append, Finset.mem_union] at ht ⊢
      rcases ht with ⟨q, hq | hq, rfl⟩
      · exact Or.inl ⟨q, hq, rfl⟩
      · exact Or.inr ⟨q, hq, rfl⟩
    calc _ ≤ (freshKeysOfLog l₁ ∪ freshKeysOfLog l₂).card := Finset.card_le_card hsub
      _ ≤ (freshKeysOfLog l₁).card + (freshKeysOfLog l₂).card := Finset.card_union_le _ _
      _ ≤ F₁.card + F₂.card := Nat.add_le_add k₁ k₂
      _ = (F₁ ∪ F₂).card := (Finset.card_union_of_disjoint hdisj).symm

theorem good_add (cF : (OracleSpec.ofFn R).QueryCache) (d : D) (a : R d) :
    Good (R' := R') cF (cF.cacheQuery d a) [] := by
  refine ⟨?_, ∅, by simp, by simp⟩
  intro d0 hd0
  rw [QueryCache.isSome_cacheQuery_apply_iff]
  exact Or.inr hd0

theorem good_add_one (cF : (OracleSpec.ofFn R).QueryCache) (d : D) (a : R d) (h : cF d = none)
    (l : QueryLog (OracleSpec.ofFn R')) (hl : (freshKeysOfLog l).card ≤ 1) :
    Good cF (cF.cacheQuery d a) l := by
  refine ⟨?_, {d}, ?_, by simpa using hl⟩
  · intro d0 hd0
    rw [QueryCache.isSome_cacheQuery_apply_iff]
    exact Or.inr hd0
  · intro d0 hd0
    rw [Finset.mem_singleton] at hd0
    subst hd0
    refine ⟨by simp [h], ?_⟩
    rw [QueryCache.isSome_cacheQuery_apply_iff]
    exact Or.inl rfl

variable (obs : σ → (t : Q ⊕ D) → Sum.elim RH R t → σ)
    (e : σ → D → Option D') (u : D' → D) (hu : ∀ s d d', e s d = some d' → u d' = d)
    (hR : ∀ d', R' d' = R (u d'))

theorem step_good (t : (ClientSpec RH R).Domain)
    (st : σ × (OracleSpec.ofFn RH).QueryCache × (OracleSpec.ofFn R).QueryCache)
    (c : (OracleSpec.ofFn R').QueryCache)
    (z : (((ClientSpec RH R).Range t × (σ × (OracleSpec.ofFn RH).QueryCache ×
        (OracleSpec.ofFn R).QueryCache)) × QueryLog (OracleSpec.ofFn R')) ×
          (OracleSpec.ofFn R').QueryCache)
    (hz : z ∈ support (randomOracleLoggedRun ((bImpl obs e u hu hR t).run st) c)) :
    Good (R' := R') st.2.2 z.1.1.2.2.2 z.1.2 := by
  obtain ⟨s0, cH, cF⟩ := st
  rcases t with n | q | d
  · have e1 : (bImpl obs e u hu hR (.inl n)).run (s0, cH, cF) =
        (fun a => (a, (s0, cH, cF))) <$>
          (liftM ((unifSpec + OracleSpec.ofFn R').query (.inl n)) :
            OracleComp (unifSpec + OracleSpec.ofFn R') (Fin (n+1))) := by
      simp [bImpl]
    rw [e1, loggedRun_map, support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [randomOracleLoggedRun_uniformQuery, support_map] at hw
    obtain ⟨a, _, rfl⟩ := hw
    exact Good.refl _
  · rcases h : cH q with _ | a
    · simp only [bImpl, StateT.run_mk, h] at hz
      have hz' : z ∈ support (randomOracleLoggedRun
          ((fun a : RH q => ((a : (ClientSpec RH R).Range (Sum.inr (Sum.inl q))),
            obs s0 (Sum.inl q) a, cH.cacheQuery q a, cF)) <$>
            OracleComp.liftComp ($ᵗ RH q) (unifSpec + OracleSpec.ofFn R')) c) := by
        rw [map_eq_bind_pure_comp]; exact hz
      obtain ⟨h1, -, a, ha⟩ := liftComp_map_logged _ _ c z hz'
      show Good cF z.1.1.2.2.2 z.1.2
      rw [h1, ha]; exact Good.refl _
    · simp only [bImpl, StateT.run_mk, h] at hz
      simp [randomOracleLoggedRun] at hz
      subst hz
      exact Good.refl _
  · rcases h : cF d with _ | a
    · rcases h' : e s0 d with _ | d'
      · simp only [bImpl_fs_none obs e u hu hR s0 cH cF d h h'] at hz
        obtain ⟨h1, -, a, ha⟩ := liftComp_map_logged _ _ c z hz
        rw [h1, ha]
        exact good_add (R' := R') cF d _
      · simp only [bImpl_fs_some obs e u hu hR s0 cH cF d d' h h'] at hz
        obtain ⟨a', h1, ha⟩ := query_map_logged _ _ c z hz
        rw [h1, ha]
        exact good_add_one (R' := R') cF d _ h _ (by simp)
    · simp only [bImpl, StateT.run_mk, h] at hz
      simp [randomOracleLoggedRun] at hz
      subst hz
      exact Good.refl _

theorem bImpl_good {α : Type} (oa : OracleComp (ClientSpec RH R) α) :
    ∀ (st : σ × (OracleSpec.ofFn RH).QueryCache × (OracleSpec.ofFn R).QueryCache)
      (c : (OracleSpec.ofFn R').QueryCache)
      (z : ((α × (σ × (OracleSpec.ofFn RH).QueryCache × (OracleSpec.ofFn R).QueryCache)) ×
          QueryLog (OracleSpec.ofFn R')) × (OracleSpec.ofFn R').QueryCache),
      z ∈ support (randomOracleLoggedRun ((simulateQ (bImpl obs e u hu hR) oa).run st) c) →
      Good (R' := R') st.2.2 z.1.1.2.2.2 z.1.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st c z hz
    simp [randomOracleLoggedRun] at hz
    subst hz
    exact Good.refl _
  | query_bind t k ih =>
    intro st c z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    rw [randomOracleLoggedRun_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (step_good obs e u hu hR t st c p hp).trans (ih p.1.1.1 p.1.1.2 p.2 w hw)

/-- Every run of B (with its final local caches) is, up to the merged cache, a run of the observed
real world: the support-level form of `evalDist_adaptiveRename` keeping the cache. -/
theorem bImpl_to_real
    (hS : ∀ d', letI : MeasurableSpace (R (u d')) := ⊤
      𝒟[(cast (hR d') <$> ($ᵗ (R' d')) : ProbComp (R (u d')))] = 𝒟[($ᵗ (R (u d')) : ProbComp (R (u d')))])
    {α : Type} (oa : OracleComp (ClientSpec RH R) α) (s₀ : σ)
    (p : ((α × (σ × (OracleSpec.ofFn RH).QueryCache × (OracleSpec.ofFn R).QueryCache)) ×
          QueryLog (OracleSpec.ofFn R')) × (OracleSpec.ofFn R').QueryCache)
    (hp : p ∈ support (randomOracleLoggedRun
      ((simulateQ (bImpl obs e u hu hR) oa).run (s₀, ∅, ∅)) ∅)) :
    ∃ r ∈ support ((simulateQ (realImpl obs) oa).run (s₀, ∅)),
      r.1 = p.1.1.1 ∧ r.2 = (p.1.1.2.1, merge p.1.1.2.2.1 p.1.1.2.2.2) := by
  letI : MeasurableSpace (α × (σ × (OracleSpec.ofFn (Sum.elim RH R)).QueryCache)) := ⊤
  have h := (intertwines obs e u hu hR hS).evalDist_simulateQ_run (preserves obs e u hu hR) oa
    ((s₀, ∅, ∅), ∅) (fun d' hd => by exact absurd hd (by simp [QueryCache.empty_apply]))
    (fun a s => (pure (a, s) : ProbComp (α × (σ × (OracleSpec.ofFn (Sum.elim RH R)).QueryCache))))
  have hφ : φ (((s₀, ∅, ∅), ∅) : S₁ RH R R' σ) = (s₀, ∅) := by
    simp only [φ, merge_empty]
  rw [hφ] at h
  simp only [pure_bind] at h
  have hsupp := support_eq_of_evalDistEq (EvalDistEq.of_evalDist_eq h)
  have hmem : (p.1.1.1, φ ((p.1.1.2, p.2) : S₁ RH R R' σ)) ∈
      support ((simulateQ (impl₁ obs e u hu hR) oa).run ((s₀, ∅, ∅), ∅) >>= fun z =>
        (pure (z.1, φ z.2) : ProbComp _)) := by
    rw [mem_support_bind_iff]
    refine ⟨(p.1.1.1, (p.1.1.2, p.2)), ?_, by simp⟩
    rw [sim_impl₁, support_map, ← randomOracleLoggedRun_project]
    simp only [support_map]
    exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  rw [hsupp, mem_support_bind_iff] at hmem
  obtain ⟨r, hr, hr2⟩ := hmem
  refine ⟨r, hr, ?_⟩
  simp at hr2
  subst hr2
  exact ⟨rfl, rfl⟩

end BSide

section Bound

open NockvmE2E.Merkle.Rename

variable {Q D D' σ : Type} [DecidableEq Q] [DecidableEq D] [DecidableEq D']
  {RH : Q → Type} {R : D → Type} {R' : D' → Type}
  [∀ q, SampleableType (RH q)] [∀ d, SampleableType (R d)] [∀ d', SampleableType (R' d')]

/-- The distinct FS keys (right summand) of a random-oracle log on hash keys and FS keys. -/
noncomputable def fsKeysOfLog (log : QueryLog (OracleSpec.ofFn (Sum.elim RH R))) : Finset D :=
  (freshKeysOfLog log).preimage Sum.inr Sum.inr_injective.injOn

theorem mem_fsKeysOfLog (log : QueryLog (OracleSpec.ofFn (Sum.elim RH R))) (d : D) :
    d ∈ fsKeysOfLog log ↔ (Sum.inr d : Q ⊕ D) ∈ freshKeysOfLog log := by
  simp [fsKeysOfLog]

/-- **B's fresh-key bound, generic form.** If A's logged lazy-RO runs (all supports) have at most
`Qfs` distinct FS keys, every logged run of B's simulation of A queries at most `Qfs` distinct keys
of B's own oracle. -/
theorem bImpl_queryBound
    (obs : σ → (t : Q ⊕ D) → Sum.elim RH R t → σ)
    (e : σ → D → Option D') (u : D' → D) (hu : ∀ s d d', e s d = some d' → u d' = d)
    (hR : ∀ d', R' d' = R (u d'))
    (hS : ∀ d', letI : MeasurableSpace (R (u d')) := ⊤
      𝒟[(cast (hR d') <$> ($ᵗ (R' d')) : ProbComp (R (u d')))] = 𝒟[($ᵗ (R (u d')) : ProbComp (R (u d')))])
    {α : Type} (oa : OracleComp (ClientSpec RH R) α) (s₀ : σ) (Qfs : ℕ)
    (hA : ∀ w ∈ support (randomOracleLoggedRun oa.withQueryLog ∅), (fsKeysOfLog w.1.2).card ≤ Qfs)
    (p : ((α × (σ × (OracleSpec.ofFn RH).QueryCache × (OracleSpec.ofFn R).QueryCache)) ×
          QueryLog (OracleSpec.ofFn R')) × (OracleSpec.ofFn R').QueryCache)
    (hp : p ∈ support (randomOracleLoggedRun
      ((simulateQ (bImpl obs e u hu hR) oa).run (s₀, ∅, ∅)) ∅)) :
    (freshKeysOfLog p.1.2).card ≤ Qfs := by
  obtain ⟨-, F, hF, hcard⟩ := bImpl_good obs e u hu hR oa (s₀, ∅, ∅) ∅ p hp
  obtain ⟨r, hr, -, hr2⟩ := bImpl_to_real obs e u hu hR hS oa s₀ p hp
  obtain ⟨w, hw, -, hw2⟩ := realImpl_logged obs oa s₀ ∅ r hr
  have hmap := loggedRun_withQueryLog oa ∅
  have hw' : ((w.1.1, w.1.2), w.2) ∈ support ((fun z => ((z.1.1.1, z.1.2), z.2)) <$>
      randomOracleLoggedRun oa.withQueryLog ∅) := by
    rw [hmap]; exact hw
  rw [support_map] at hw'
  obtain ⟨w', hw'', hw'e⟩ := hw'
  have hlog : w'.1.2 = w.1.2 := congrArg (fun x => x.1.2) hw'e
  refine le_trans hcard (le_trans (Finset.card_le_card ?_) (hA w' hw''))
  intro d hd
  rw [mem_fsKeysOfLog, hlog]
  have h1 : (w.2 (Sum.inr d)).isSome := by
    rw [hw2, hr2]
    exact (hF d hd).2
  rcases loggedRun_cache_log oa ∅ w hw (Sum.inr d) h1 with h | h
  · simp [QueryCache.empty_apply] at h
  · exact h

end Bound

section Merkle

open NockvmE2E.Merkle NockvmE2E.Merkle.Reduction

variable {Y : Type} [Finite Y] [DecidableEq Y] [SampleableType Y] {Op : Type} [Finite Op]
  [DecidableEq Op] {Query : Type} [DecidableEq Query] {Statement Salt W : Type}
  [DecidableEq Statement] [DecidableEq Salt] {ms : MRounds Y}
  (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)

/-- The FS keys of a log of A's lazy random oracle (hash keys and compiled FS keys). -/
noncomputable abbrev fsKeysOfLogK
    (log : QueryLog (OracleSpec.ofFn (succinctRange Y Op Query Statement Salt ms))) :
    Finset (Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)) :=
  fsKeysOfLog (RH := fun _ : Query => Y) (R := Key.Challenge) log

theorem hS_K : ∀ d' : Key (Statement × Salt) PUnit (pairedRoundsK Y ms),
    letI : MeasurableSpace (Key.Challenge (untranslateK Y Op ms d')) := ⊤
    𝒟[(cast ((untranslate_challengeK Y Op ms d').symm) <$> ($ᵗ (Key.Challenge d')) :
      ProbComp (Key.Challenge (untranslateK Y Op ms d')))] =
      𝒟[($ᵗ (Key.Challenge (untranslateK Y Op ms d')) : ProbComp _)] := by
  intro d'
  have := Rename.sample_untranslateK (Y := Y) (Op := Op) ms d'
  simp only [id] at this
  exact congrArg _ this

theorem inst_eq : (fun d => succinctRange_sampleable Y Op Query Statement Salt ms d) =
    (fun d => Rename.sumElimSampleable (RH := fun _ : Query => Y) (R := Key.Challenge) d) := by
  funext d
  cases d <;> rfl

/-- **`reductionB` satisfies QD's `queryBound`** (support-wise, not in expectation): if every
logged lazy-RO run of A queries at most `Qfs` distinct FS keys, every phase of `reductionB A`
has at most `Qfs` distinct fresh keys. -/
theorem reductionB_queryBound
    (A : SuccinctAdversaryK Y Op Query Statement Salt W ms) (Qfs : ℕ)
    (hA : ∀ w ∈ support (randomOracleLoggedRun A.withQueryLog ∅),
      (fsKeysOfLogK (Op := Op) w.1.2).card ≤ Qfs) :
    ∀ phase ∈ support (randomOracleLoggedRun (reductionB ext A).withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Qfs := by
  intro phase hphase
  have hmap := loggedRun_withQueryLog (reductionB ext A) ∅
  have h1 : ((phase.1.1.1, phase.1.2), phase.2) ∈ support ((fun z => ((z.1.1.1, z.1.2), z.2)) <$>
      randomOracleLoggedRun (reductionB ext A).withQueryLog ∅) := by
    rw [support_map]; exact ⟨phase, hphase, rfl⟩
  rw [hmap] at h1
  unfold reductionB at h1
  rw [randomOracleLoggedRun_bind, mem_support_bind_iff] at h1
  obtain ⟨p, hp, h2⟩ := h1
  rw [support_map] at h2
  obtain ⟨w, hw, hw2⟩ := h2
  have hlog : phase.1.2 = p.1.2 := by
    have := congrArg (fun x => x.1.2) hw2
    simp only at this
    rw [← this]
    obtain ⟨⟨r, st⟩, _⟩ := p
    rcases r with _ | ⟨statement, ⟨salt, msgs⟩, wit⟩
    · simp [randomOracleLoggedRun] at hw
      simp [hw]
    · simp [randomOracleLoggedRun] at hw
      simp [hw]
  rw [hlog]
  have key := bImpl_queryBound (RH := fun _ : Query => Y) (R := Key.Challenge)
    (R' := (Key.Challenge : Key (Statement × Salt) PUnit (pairedRoundsK Y ms) → Type))
    (obsStep Y Op ms (Query := Query) (Statement := Statement) (Salt := Salt))
    (fun s => translateK Y Op ms (memoWords ext s) [])
    (untranslateK Y Op ms)
    (fun s d d' h => untranslate_translateK Y Op ms (memoWords ext s) [] d d' h)
    (fun d' => (untranslate_challengeK Y Op ms d').symm)
    (hS_K (Op := Op)) (α := Option (Statement × SaltedProof Salt (compiledRoundsK Y Op ms) × W))
    A Obs.init Qfs (by
      have e := inst_eq (Y := Y) (Op := Op) (Query := Query) (Statement := Statement) (Salt := Salt) (ms := ms)
      convert hA using 5
      exact e.symm)
  exact key p hp


end Merkle

/-! ## Coherence of the keys built from `pairMsgs` -/

section Coherence

open NockvmE2E.Merkle NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.VerifyTransport

variable {Y : Type} [Finite Y] [DecidableEq Y] {Op : Type} [Finite Op] [DecidableEq Op]
  {Input : Type}

/-- `KeyAlong ms pm k`: the paired key `k` is one the paired verifier builds along the messages
`pm` (a `here` key at some round carries that round's message; a `later` key carries the round's
message and continues along the tail). -/
def KeyAlong : (ms : MRounds Y) → PublicMessages (pairedRoundsK Y ms) →
    Key Input PUnit (pairedRoundsK Y ms) → Prop
  | [], _, _ => True
  | ⟨_, .clear⟩ :: _, (m, _), .inl (_, m', _) => m' = m
  | ⟨_, .clear⟩ :: ms, (m, rest), .inr (m', _, k) => m' = m ∧ KeyAlong ms rest k
  | ⟨_, .merkle _ _ _ _ _⟩ :: _, (m, _), .inl (_, m', _) => m' = m
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, (m, rest), .inr (m', _, k) => m' = m ∧ KeyAlong ms rest k

/-- **`pairMsgs` coherence.** Every paired key built along `pairMsgs z words ms pre cm` (inputs
`z`) is `Coherent` with `words` at root prefix `pre`: its merkle messages carry exactly the words
that `words` assigns to their roots. No assumption on the messages is needed: `words` is total
(`memoWords ext s` returns `ext r hr pre [] root` where the memo has no entry, so `ext` is the only place
where inhabitedness of the round messages is used). -/
theorem pairMsgs_coherent (z : Input) (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message) :
    (ms : MRounds Y) → (pre : List Y) → (cm : PublicMessages (compiledRoundsK Y Op ms)) →
    (k : Key Input PUnit (pairedRoundsK Y ms)) → k.input = z →
    KeyAlong ms (pairMsgs z words ms pre cm) k → Coherent words ms pre k
  | [], _, _, _, _, _ => trivial
  | ⟨_, .clear⟩ :: _, _, _, .inl _, _, _ => trivial
  | ⟨_, .clear⟩ :: ms, pre, (_, rest), .inr (m', _, k), hz, h => by
      obtain ⟨rfl, h2⟩ := h
      exact pairMsgs_coherent z words ms pre rest k hz h2
  | ⟨r, .merkle _ _ ne _ we⟩ :: _, pre, (root, _), .inl (z', m', _), hz, h => by
      simp only [KeyAlong, pairMsgs] at h
      subst h
      have hz' : z' = z := hz
      subst hz'
      rfl
  | ⟨r, .merkle _ _ ne _ we⟩ :: ms, pre, (root, rest), .inr (m', _, k), hz, h => by
      obtain ⟨h1, h2⟩ := h
      have h1' : m' = (words r (merkle_nonempty ne we) z pre root, root) := h1
      subst h1'
      have hz' : k.input = z := hz
      subst hz'
      exact ⟨rfl, pairMsgs_coherent k.input words ms _ rest k rfl h2⟩

/-- The key B's FS oracle is asked (the `translateK` of the compiled image) is the paired key itself,
for every paired key built along `pairMsgs` with the words `words`. -/
theorem translateK_untranslateK_pairMsgs (z : Input)
    (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message) (ms : MRounds Y) (pre : List Y)
    (cm : PublicMessages (compiledRoundsK Y Op ms)) (k : Key Input PUnit (pairedRoundsK Y ms))
    (hz : k.input = z) (hk : KeyAlong ms (pairMsgs z words ms pre cm) k) :
    translateK Y Op ms words pre (untranslateK Y Op ms k) = some k :=
  translateK_untranslateK words ms pre k (pairMsgs_coherent z words ms pre cm k hz hk)

/-- The instance B uses: words read from the end-of-A memo `finalObs …`. -/
theorem translateK_untranslateK_final {Query : Type} {Statement Salt : Type} {ms : MRounds Y}
    [DecidableEq Statement] [DecidableEq Salt]
    (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)
    (s : Obs Query Statement Salt Y) (z : Statement × Salt)
    (cm : PublicMessages (compiledRoundsK Y Op ms))
    (k : Key (Statement × Salt) PUnit (pairedRoundsK Y ms))
    (hz : k.input = z)
    (hk : KeyAlong ms
      (pairMsgs z (memoWords ext (finalObs (Op := Op) (ms := ms) s z cm)) ms [] cm) k) :
    translateK Y Op ms (memoWords ext (finalObs (Op := Op) (ms := ms) s z cm)) []
      (untranslateK Y Op ms k) = some k :=
  translateK_untranslateK_pairMsgs z _ ms [] cm k hz hk

end Coherence

end NockvmE2E.Merkle.FreshKeys
