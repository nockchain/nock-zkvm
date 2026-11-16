/-
(section 2, section 6 row 3): the adaptive Fiat-Shamir renaming law.

* `bImpl`      : reduction side (B). Coins forwarded, hash simulated lazily with B's own coins, a compiled
                 FS key `d` answered from B's local cache, else by B's FS oracle at the renamed key `e s d`.
* `realImpl`   : one lazy random oracle on `Q ⊕ D` with a deterministic observer.
* `evalDist_adaptiveRename` : B run against the lazy RO of the renamed keys, jointly with the observer
                 state, has the distribution of the real world. No eager table, no finiteness of `D`.
                 Proof by `QueryImpl.IntertwinesOn.evalDist_simulateQ_run` (fill map `φ`, invariant `Inv`).
* `evalDist_adaptiveRenameK`: the instance at the masked compiled/paired keys (`translateK`, `untranslateK`).

Statement change: an extra hypothesis `hS` (the sampler of
`R' d'`, cast along `hR d'`, is distributed as the sampler of `R (u d')`). Without it the statement is
false, because `SampleableType` instances on `R'` and `R` are unrelated in the generic setting.
-/
import NockvmE2E.Merkle.Compiled
import VCVio.OracleComp.SimSemantics.StateT.Measure
import VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun

open OracleComp OracleSpec MeasureTheory

namespace NockvmE2E.Merkle.Rename

set_option linter.unusedSectionVars false

variable {Q D D' σ : Type} [DecidableEq Q] [DecidableEq D] [DecidableEq D']
  {RH : Q → Type} {R : D → Type} {R' : D' → Type}
  [∀ q, SampleableType (RH q)] [∀ d, SampleableType (R d)] [∀ d', SampleableType (R' d')]

/-- Client oracle: private coins, then ONE lazy RO on hash ⊕ compiled-FS keys. -/
abbrev ClientSpec (RH : Q → Type) (R : D → Type) := unifSpec + OracleSpec.ofFn (Sum.elim RH R)

instance (priority := low) sumElimSampleable : ∀ t : Q ⊕ D, SampleableType (Sum.elim RH R t)
  | .inl q => inferInstanceAs (SampleableType (RH q))
  | .inr d => inferInstanceAs (SampleableType (R d))

/-- Real world (W0'): the lazy RO on `Q ⊕ D`, with a deterministic observer `obs`
(hash log, memo) updated on every RO answer. -/
noncomputable def realImpl (obs : σ → (t : Q ⊕ D) → Sum.elim RH R t → σ) :
    QueryImpl (ClientSpec RH R)
      (StateT (σ × (OracleSpec.ofFn (Sum.elim RH R)).QueryCache) ProbComp)
  | .inl n => (liftM (unifSpec.query n) : ProbComp _)
  | .inr t => StateT.mk fun st => do
      let (a, c') ← ((OracleSpec.ofFn (Sum.elim RH R)).randomOracle t).run st.2
      return (a, (obs st.1 t a, c'))

/-- Reduction side (B): coins forwarded; hash simulated lazily with B's own coins; a compiled
FS key `d` answered from B's local cache, else by B's FS oracle at the renamed key `e s d`. -/
noncomputable def bImpl (obs : σ → (t : Q ⊕ D) → Sum.elim RH R t → σ)
    (e : σ → D → Option D') (u : D' → D) (hu : ∀ s d d', e s d = some d' → u d' = d) (hR : ∀ d', R' d' = R (u d')) :
    QueryImpl (ClientSpec RH R)
      (StateT (σ × (OracleSpec.ofFn RH).QueryCache × (OracleSpec.ofFn R).QueryCache)
        (OracleComp (unifSpec + OracleSpec.ofFn R')))
  | .inl n => liftM ((unifSpec + OracleSpec.ofFn R').query (.inl n))
  | .inr (.inl q) => StateT.mk fun st =>
      match st.2.1 q with
      | some a => pure (a, (obs st.1 (.inl q) a, st.2))
      | none => do
          let a ← OracleComp.liftComp ($ᵗ (RH q)) (unifSpec + OracleSpec.ofFn R')
          return (a, (obs st.1 (.inl q) a, st.2.1.cacheQuery q a, st.2.2))
  | .inr (.inr d) => StateT.mk fun st =>
      match st.2.2 d with
      | some a => pure (a, (obs st.1 (.inr d) a, st.2))
      | none =>
        match h : e st.1 d with
        | some d' => do
            let a' ← liftM ((unifSpec + OracleSpec.ofFn R').query (.inr d'))
            let a : R d := cast ((hR d').trans (congrArg R (hu st.1 d d' h))) a'
            return (a, (obs st.1 (.inr d) a, st.2.1, st.2.2.cacheQuery d a))
        | none => do
            let a ← OracleComp.liftComp ($ᵗ (R d)) (unifSpec + OracleSpec.ofFn R')
            return (a, (obs st.1 (.inr d) a, st.2.1, st.2.2.cacheQuery d a))


section proof
variable (obs : σ → (t : Q ⊕ D) → Sum.elim RH R t → σ)
    (e : σ → D → Option D') (u : D' → D) (hu : ∀ s d d', e s d = some d' → u d' = d)
    (hR : ∀ d', R' d' = R (u d'))

/-- Combined state: B's state and the outer lazy RO cache. -/
abbrev S₁ (RH : Q → Type) (R : D → Type) (R' : D' → Type) (σ : Type) :=
  (σ × (OracleSpec.ofFn RH).QueryCache × (OracleSpec.ofFn R).QueryCache) × (OracleSpec.ofFn R').QueryCache

/-- B composed with the outer lazy RO, as one handler. -/
noncomputable def impl₁ : QueryImpl (ClientSpec RH R) (StateT (S₁ RH R R' σ) ProbComp) :=
  fun t => StateT.mk fun s =>
    (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (OracleSpec.ofFn R').romImpl ((bImpl obs e u hu hR t).run s.1)).run s.2

theorem sim_impl₁ {α : Type} (oa : OracleComp (ClientSpec RH R) α)
    (st : σ × (OracleSpec.ofFn RH).QueryCache × (OracleSpec.ofFn R).QueryCache)
    (c : (OracleSpec.ofFn R').QueryCache) :
    (simulateQ (impl₁ obs e u hu hR) oa).run (st, c) =
      (fun w => (w.1.1, (w.1.2, w.2))) <$>
        (simulateQ (OracleSpec.ofFn R').romImpl ((simulateQ (bImpl obs e u hu hR) oa).run st)).run c := by
  induction oa using OracleComp.inductionOn generalizing st c with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [impl₁, StateT.run_mk, map_bind, bind_map_left]
    refine bind_congr fun p => ?_
    simp only [map_eq_bind_pure_comp, ih]


/-- Merge the two typed caches of B into the single cache of the real world. -/
def merge (cH : (OracleSpec.ofFn RH).QueryCache) (cF : (OracleSpec.ofFn R).QueryCache) :
    (OracleSpec.ofFn (Sum.elim RH R)).QueryCache :=
  QueryCache.ofFn fun t => match t with
    | .inl q => cH q
    | .inr d => cF d

def φ (s : S₁ RH R R' σ) : σ × (OracleSpec.ofFn (Sum.elim RH R)).QueryCache :=
  (s.1.1, merge s.1.2.1 s.1.2.2)

def Inv (u : D' → D) (s : S₁ RH R R' σ) : Prop :=
  ∀ d', (s.2 d').isSome → (s.1.2.2 (u d')).isSome

theorem step_inl (n : ℕ) (s : S₁ RH R R' σ) {γ : Type} (f : Fin (n+1) → σ × (OracleSpec.ofFn (Sum.elim RH R)).QueryCache → ProbComp γ) :
    ((impl₁ obs e u hu hR (.inl n)).run s >>= fun z => f z.1 (φ z.2)) =
      ((realImpl obs (.inl n)).run (φ s) >>= fun z => f z.1 z.2) := by
  obtain ⟨⟨s0, cH, cF⟩, cR⟩ := s
  simp [impl₁, bImpl, realImpl, φ]
  have h : (unifFwdImpl (OracleSpec.ofFn R') n).run cR =
      (fun u => (u, cR)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n+1))) := rfl
  rw [h]; simp


theorem lift_run {α : Type} (oa : ProbComp α) (c : (OracleSpec.ofFn R').QueryCache) :
    (simulateQ (OracleSpec.ofFn R').romImpl
      (OracleComp.liftComp oa (unifSpec + OracleSpec.ofFn R'))).run c = (fun x => (x, c)) <$> oa := by
  rw [roSim.simulateQ_liftComp]; exact unifFwdImpl.simulateQ_run oa c

theorem merge_inl (cH : (OracleSpec.ofFn RH).QueryCache) (cF : (OracleSpec.ofFn R).QueryCache) (q : Q) :
    (merge cH cF) (Sum.inl q) = cH q := rfl

theorem merge_inr (cH : (OracleSpec.ofFn RH).QueryCache) (cF : (OracleSpec.ofFn R).QueryCache) (d : D) :
    (merge cH cF) (Sum.inr d) = cF d := rfl

theorem merge_cacheQuery_inl (cH : (OracleSpec.ofFn RH).QueryCache) (cF : (OracleSpec.ofFn R).QueryCache)
    (q : Q) (a : RH q) :
    merge (cH.cacheQuery q a) cF = (merge cH cF).cacheQuery (Sum.inl q) a := by
  refine QueryCache.ext fun t => ?_
  rcases t with q' | d'
  · by_cases hq : q' = q
    · subst hq
      exact (merge_inl _ _ _).trans ((QueryCache.cacheQuery_self cH q' a).trans
        (QueryCache.cacheQuery_self (merge cH cF) (Sum.inl q') a).symm)
    · exact (merge_inl _ _ _).trans ((QueryCache.cacheQuery_of_ne cH a hq).trans
        ((merge_inl cH cF q').symm.trans
          (QueryCache.cacheQuery_of_ne (merge cH cF) (t' := Sum.inl q') (t := Sum.inl q) a (fun h => hq (Sum.inl.inj h))).symm))
  · exact (merge_inr _ _ _).trans ((merge_inr cH cF d').symm.trans
      (QueryCache.cacheQuery_of_ne (merge cH cF) (t' := Sum.inr d') (t := Sum.inl q) a (by simp)).symm)

theorem merge_cacheQuery_inr (cH : (OracleSpec.ofFn RH).QueryCache) (cF : (OracleSpec.ofFn R).QueryCache)
    (d : D) (a : R d) :
    merge cH (cF.cacheQuery d a) = (merge cH cF).cacheQuery (Sum.inr d) a := by
  refine QueryCache.ext fun t => ?_
  rcases t with q' | d'
  · exact (merge_inl _ _ _).trans ((merge_inl cH cF q').symm.trans
      (QueryCache.cacheQuery_of_ne (merge cH cF) (t' := Sum.inl q') (t := Sum.inr d) a (by simp)).symm)
  · by_cases hd : d' = d
    · subst hd
      exact (merge_inr _ _ _).trans ((QueryCache.cacheQuery_self cF d' a).trans
        (QueryCache.cacheQuery_self (merge cH cF) (Sum.inr d') a).symm)
    · exact (merge_inr _ _ _).trans ((QueryCache.cacheQuery_of_ne cF a hd).trans
        ((merge_inr cH cF d').symm.trans
          (QueryCache.cacheQuery_of_ne (merge cH cF) (t' := Sum.inr d') (t := Sum.inr d) a (fun h => hd (Sum.inr.inj h))).symm))

theorem realImpl_run (t : Q ⊕ D) (s : σ) (c : (OracleSpec.ofFn (Sum.elim RH R)).QueryCache) :
    (realImpl obs (.inr t)).run (s, c) =
      (fun p => (p.1, (obs s t p.1, p.2))) <$> ((OracleSpec.ofFn (Sum.elim RH R)).randomOracle t).run c := by
  simp [realImpl]

theorem step_hash (q : Q) (s : S₁ RH R R' σ) {γ : Type} (f : RH q → σ × (OracleSpec.ofFn (Sum.elim RH R)).QueryCache → ProbComp γ) :
    ((impl₁ obs e u hu hR (.inr (.inl q))).run s >>= fun z => f z.1 (φ z.2)) =
      ((realImpl obs (.inr (.inl q))).run (φ s) >>= fun z => f z.1 z.2) := by
  obtain ⟨⟨s0, cH, cF⟩, cR⟩ := s
  rw [φ, realImpl_run, randomOracle.run_eq]
  rcases h : cH q with _ | a
  · simp [impl₁, bImpl, φ, h, merge_inl, merge_cacheQuery_inl]
    rw [roSim.run_liftM (OracleSpec.ofFn R').randomOracle]
    simp
    rfl
  · simp [impl₁, bImpl, φ, h, merge_inl]


theorem bImpl_fs_none (s0 : σ) (cH : (OracleSpec.ofFn RH).QueryCache) (cF : (OracleSpec.ofFn R).QueryCache)
    (d : D) (h : cF d = none) (h' : e s0 d = none) :
    (bImpl obs e u hu hR (.inr (.inr d))).run (s0, cH, cF) =
      (fun a => (a, obs s0 (.inr d) a, cH, cF.cacheQuery d a)) <$>
        OracleComp.liftComp ($ᵗ (R d)) (unifSpec + OracleSpec.ofFn R') := by
  simp only [bImpl, StateT.run_mk, h]
  split
  · rename_i x hx; rw [h'] at hx; cases hx
  · simp

theorem bImpl_fs_some (s0 : σ) (cH : (OracleSpec.ofFn RH).QueryCache) (cF : (OracleSpec.ofFn R).QueryCache)
    (d : D) (d' : D') (h : cF d = none) (h' : e s0 d = some d') :
    (bImpl obs e u hu hR (.inr (.inr d))).run (s0, cH, cF) =
      (fun a' => let a : R d := cast ((hR d').trans (congrArg R (hu s0 d d' h'))) a'
                 (a, obs s0 (.inr d) a, cH, cF.cacheQuery d a)) <$>
        (liftM ((unifSpec + OracleSpec.ofFn R').query (.inr d')) : OracleComp (unifSpec + OracleSpec.ofFn R') (R' d')) := by
  simp only [bImpl, StateT.run_mk, h]
  split
  · rename_i x d'' hx
    have : d'' = d' := by rw [h'] at hx; exact (Option.some.inj hx).symm
    subst this
    simp
  · rename_i hx; rw [h'] at hx; cases hx

theorem step_fs (hS : ∀ d', letI : MeasurableSpace (R (u d')) := ⊤
      𝒟[(cast (hR d') <$> ($ᵗ (R' d')) : ProbComp (R (u d')))] = 𝒟[($ᵗ (R (u d')) : ProbComp (R (u d')))])
    (d : D) (s : S₁ RH R R' σ) (hs : Inv u s) {γ : Type} [MeasurableSpace γ]
    (f : R d → σ × (OracleSpec.ofFn (Sum.elim RH R)).QueryCache → ProbComp γ) :
    𝒟[((impl₁ obs e u hu hR (.inr (.inr d))).run s >>= fun z => f z.1 (φ z.2))] =
      𝒟[((realImpl obs (.inr (.inr d))).run (φ s) >>= fun z => f z.1 z.2)] := by
  obtain ⟨⟨s0, cH, cF⟩, cR⟩ := s
  rw [φ, realImpl_run, randomOracle.run_eq]
  rcases h : cF d with _ | a
  · rcases h' : e s0 d with _ | d'
    · simp only [impl₁, StateT.run_mk, bImpl_fs_none obs e u hu hR s0 cH cF d h h', φ]
      simp [merge_inr, merge_cacheQuery_inr, h]
      rw [roSim.run_liftM (OracleSpec.ofFn R').randomOracle]
      simp
      rfl
    · simp only [impl₁, StateT.run_mk, bImpl_fs_some obs e u hu hR s0 cH cF d d' h h', φ]
      have hc : cR d' = none := by
        by_contra hne
        have := hs d' (by cases hh : cR d' <;> simp_all)
        rw [hu s0 d d' h'] at this
        simp [h] at this
      have hc' : cR.toFn d' = none := hc
      simp [merge_inr, h, hc']
      obtain rfl := hu s0 d d' h'
      let : MeasurableSpace (R (u d')) := ⊤
      have : DiscreteMeasurableSpace (R (u d')) := ⟨fun _ => trivial⟩
      have hh : R' d' = R (u d') := hR d'
      set g : R (u d') → ProbComp γ := fun a =>
        f a (obs s0 (Sum.inr (u d')) a, (merge cH cF).cacheQuery (Sum.inr (u d')) a) with hg
      have e1 : (do let a ← $ᵗ (OracleSpec.ofFn R').Range d'
                    f (cast hh a) (obs s0 (Sum.inr (u d')) (cast hh a), merge cH (cF.cacheQuery (u d') (cast hh a)))) =
                ((cast hh <$> ($ᵗ (R' d')) : ProbComp (R (u d'))) >>= g) := by
        simp [hg, merge_cacheQuery_inr]
      refine (congrArg (fun x => 𝒟[x]) e1).trans ?_
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, hS d']
      rfl
  · simp [impl₁, bImpl, φ, h, merge_inr]


theorem impl₁_run_inl (n : ℕ) (s : S₁ RH R R' σ) :
    (impl₁ obs e u hu hR (.inl n)).run s = (fun a => (a, s)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n+1))) := by
  obtain ⟨⟨s0, cH, cF⟩, cR⟩ := s
  have h : (unifFwdImpl (OracleSpec.ofFn R') n).run cR =
      (fun u => (u, cR)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n+1))) := rfl
  simp [impl₁, bImpl, h]

theorem inv_update {s0 s1 : σ} {cH cH' : (OracleSpec.ofFn RH).QueryCache} {cF : (OracleSpec.ofFn R).QueryCache}
    {cR : (OracleSpec.ofFn R').QueryCache} (hs : Inv u ((s0, cH, cF), cR)) (d : D) (a : R d) :
    Inv u ((s1, cH', cF.cacheQuery d a), cR) := by
  intro d' hd'
  rw [QueryCache.isSome_cacheQuery_apply_iff]
  exact Or.inr (hs d' hd')

theorem inv_update2 {s0 s1 : σ} {cH cH' : (OracleSpec.ofFn RH).QueryCache} {cF : (OracleSpec.ofFn R).QueryCache}
    {cR : (OracleSpec.ofFn R').QueryCache} (hs : Inv u ((s0, cH, cF), cR)) (d : D) (a : R d)
    (d' : D') (hd' : u d' = d) (a' : R' d') :
    Inv u ((s1, cH', cF.cacheQuery d a), cR.cacheQuery d' a') := by
  intro d'' hd''
  rw [QueryCache.isSome_cacheQuery_apply_iff] at hd'' ⊢
  rcases hd'' with rfl | hd''
  · exact Or.inl hd'
  · exact Or.inr (hs d'' hd'')

theorem preserves : QueryImpl.PreservesInv (impl₁ obs e u hu hR) (Inv u) := by
  intro t s hs z hz
  obtain ⟨⟨s0, cH, cF⟩, cR⟩ := s
  rcases t with n | q | d
  · rw [impl₁_run_inl] at hz
    simp at hz
    obtain ⟨a, rfl⟩ := hz
    exact hs
  · rcases h : cH q with _ | a
    · simp [impl₁, bImpl, h] at hz
      rw [roSim.run_liftM (OracleSpec.ofFn R').randomOracle, support_map] at hz
      obtain ⟨p, ⟨a, _, rfl⟩, rfl⟩ := hz
      exact hs
    · simp [impl₁, bImpl, h] at hz
      subst hz
      exact hs
  · rcases h : cF d with _ | a
    · rcases h' : e s0 d with _ | d'
      · simp only [impl₁, StateT.run_mk, bImpl_fs_none obs e u hu hR s0 cH cF d h h'] at hz
        simp at hz
        rw [roSim.run_liftM (OracleSpec.ofFn R').randomOracle, support_map] at hz
        obtain ⟨p, ⟨a, _, rfl⟩, rfl⟩ := hz
        exact inv_update u hs d a
      · have hc : cR d' = none := by
          by_contra hne
          have := hs d' (by cases hh : cR d' <;> simp_all)
          rw [hu s0 d d' h'] at this
          simp [h] at this
        have hc' : cR.toFn d' = none := hc
        simp only [impl₁, StateT.run_mk, bImpl_fs_some obs e u hu hR s0 cH cF d d' h h'] at hz
        simp [hc'] at hz
        obtain ⟨a, rfl⟩ := hz
        exact inv_update2 u hs d _ d' (hu s0 d d' h') a
    · simp [impl₁, bImpl, h] at hz
      subst hz
      exact hs


theorem intertwines
    (hS : ∀ d', letI : MeasurableSpace (R (u d')) := ⊤
      𝒟[(cast (hR d') <$> ($ᵗ (R' d')) : ProbComp (R (u d')))] = 𝒟[($ᵗ (R (u d')) : ProbComp (R (u d')))]) :
    QueryImpl.IntertwinesOn (Inv u) (fun s => (pure (φ s) : ProbComp _))
      (impl₁ obs e u hu hR) (realImpl obs) := by
  intro t s hs γ _ f
  simp only [pure_bind]
  rcases t with n | q | d
  · exact congrArg _ (step_inl obs e u hu hR n s f)
  · exact congrArg _ (step_hash obs e u hu hR q s f)
  · exact step_fs obs e u hu hR hS d s hs f

theorem merge_empty : merge (∅ : (OracleSpec.ofFn RH).QueryCache) (∅ : (OracleSpec.ofFn R).QueryCache) = ∅ := by
  refine QueryCache.ext fun t => ?_
  rcases t with q | d <;> rfl

/-- **Adaptive renaming law.** -/
theorem evalDist_adaptiveRename {α : Type}
    (hS : ∀ d', letI : MeasurableSpace (R (u d')) := ⊤
      𝒟[(cast (hR d') <$> ($ᵗ (R' d')) : ProbComp (R (u d')))] = 𝒟[($ᵗ (R (u d')) : ProbComp (R (u d')))])
    (oa : OracleComp (ClientSpec RH R) α) (s₀ : σ) :
    letI : MeasurableSpace (α × σ) := ⊤
    𝒟[(fun z => (z.1.1.1, z.1.1.2.1)) <$>
        randomOracleLoggedRun ((simulateQ (bImpl obs e u hu hR) oa).run (s₀, ∅, ∅)) ∅] =
      𝒟[(fun z => (z.1, z.2.1)) <$> (simulateQ (realImpl obs) oa).run (s₀, ∅)] := by
  letI : MeasurableSpace (α × σ) := ⊤
  have hL : (fun z => (z.1.1.1, z.1.1.2.1)) <$>
        randomOracleLoggedRun ((simulateQ (bImpl obs e u hu hR) oa).run (s₀, ∅, ∅)) ∅ =
      (fun z => (z.1, z.2.1.1)) <$> (simulateQ (impl₁ obs e u hu hR) oa).run ((s₀, ∅, ∅), ∅) := by
    rw [sim_impl₁, Functor.map_map, ← randomOracleLoggedRun_project, Functor.map_map]
  have h := (intertwines obs e u hu hR hS).evalDist_simulateQ_run (preserves obs e u hu hR) oa
    ((s₀, ∅, ∅), ∅) (fun d' hd => by exact absurd hd (by simp [QueryCache.empty_apply])) (fun a s => (pure (a, s.1) : ProbComp (α × σ)))
  rw [hL]
  have hφ : φ (((s₀, ∅, ∅), ∅) : S₁ RH R R' σ) = (s₀, ∅) := by
    simp only [φ, merge_empty]
  rw [hφ] at h
  simp only [pure_bind] at h
  simpa [map_eq_bind_pure_comp, φ] using h

end proof

/-! ## Instance at the masked compiled / paired keys -/

section Instance

open Interaction.Oracle Interaction.Oracle.Security.StateRestoration NockvmE2E.Merkle

variable {Y : Type} [Finite Y] [DecidableEq Y] [SampleableType Y]
  {Op : Type} [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query]
  {Statement Salt : Type} [DecidableEq Statement] [DecidableEq Salt] (ms : MRounds Y)

/-- The challenge sampler of a paired key is, after the cast along `untranslate_challengeK`, the
sampler of its compiled image. -/
theorem sample_untranslateK {Input : Type} :
    (ms : MRounds Y) → (k : Key Input PUnit (pairedRoundsK Y ms)) →
    (cast (congrArg id (untranslate_challengeK Y Op ms k).symm) <$> ($ᵗ k.Challenge) :
      ProbComp (untranslateK Y Op ms k).Challenge) = $ᵗ (untranslateK Y Op ms k).Challenge
  | [], k => nomatch k
  | ⟨_, .clear⟩ :: _, .inl _ => id_map _
  | ⟨_, .clear⟩ :: ms, .inr (_, _, k) => sample_untranslateK ms k
  | ⟨_, .merkle _ _ _ _ _⟩ :: _, .inl _ => id_map _
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, .inr (_, _, k) => sample_untranslateK ms k

/-- **Adaptive renaming at the compiled keys.** The memo `memo s` (an abstract function of the
observer state, defined in `Reduction.lean`) fixes the word of each root prefix; B asks its FS oracle
at `translateK … (memo s) []`. -/
theorem evalDist_adaptiveRenameK {σ α : Type}
    (memo : σ → (r : Round) → Nonempty r.Message → Statement × Salt → List Y → Y → r.Message)
    (obs : σ → (t : Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)) →
      Sum.elim (fun _ : Query => Y) Key.Challenge t → σ)
    (oa : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α) (s₀ : σ) :
    letI : MeasurableSpace (α × σ) := ⊤
    𝒟[(fun z => (z.1.1.1, z.1.1.2.1)) <$>
        randomOracleLoggedRun
          ((simulateQ (bImpl (RH := fun _ : Query => Y) (R := Key.Challenge)
              (R' := (Key.Challenge : Key (Statement × Salt) PUnit (pairedRoundsK Y ms) → Type)) obs
            (fun s => translateK Y Op ms (memo s) [])
            (untranslateK Y Op ms)
            (fun s d d' h => untranslate_translateK Y Op ms (memo s) [] d d' h)
            (fun d' => (untranslate_challengeK Y Op ms d').symm)) oa).run (s₀, ∅, ∅)) ∅] =
      𝒟[(fun z => (z.1, z.2.1)) <$> (simulateQ (realImpl obs) oa).run (s₀, ∅)] := by
  refine evalDist_adaptiveRename _ _ _ _ _ ?_ oa s₀
  intro d'
  have := sample_untranslateK (Y := Y) (Op := Op) ms d'
  simp only [id] at this
  exact congrArg _ this

end Instance

end NockvmE2E.Merkle.Rename
