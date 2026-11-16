import NockvmE2E.Exec.HFixFriC
import NockvmE2E.Exec.E2E
import NockvmE2E.Ung.Consist
import VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure
import ToMathlib.Data.ENNReal.Gauss

/-!  birthday bound on NODE keys only, for the logged lazy random oracle with private coins and
FS keys of other ranges (the hcoll side oracle shape `unifSpec + ofFn (Sum.elim (fun _ => YY) Rc)`), eager -> lazy transfer
for a recorded hash-only program, and `hcoll_generic`. -/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace NockvmE2E.Exec.LazyColl

variable {QQ YY KK : Type} {Rc : KK → Type}

abbrev RF (QQ YY : Type) (Rc : KK → Type) : QQ ⊕ KK → Type := Sum.elim (fun _ => YY) Rc

/-- node (hash) queries of the side oracle -/
def isNodeQ : (unifSpec + ofFn (RF QQ YY Rc)).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

instance : DecidablePred (isNodeQ (QQ := QQ) (YY := YY) (Rc := Rc)) := fun t => by
  rcases t with _ | (_ | _)
  · exact isFalse (by simp [isNodeQ])
  · exact isTrue trivial
  · exact isFalse (by simp [isNodeQ])

/-- two distinct node keys with the same cached digest -/
def NodeColl (c : (ofFn (RF QQ YY Rc)).QueryCache) : Prop :=
  ∃ q1 q2 : QQ, q1 ≠ q2 ∧ ∃ u : YY, c (.inl q1) = some u ∧ c (.inl q2) = some u

/-- the cached digest at node key `q` (default `y0`) -/
def cv (c : (ofFn (RF QQ YY Rc)).QueryCache) (y0 : YY) (q : QQ) : YY :=
  match c (.inl q) with
  | some u => u
  | none => y0

theorem cv_of_some (c : (ofFn (RF QQ YY Rc)).QueryCache) (y0 : YY) (q : QQ) (u : YY) (h : c (.inl q) = some u) :
    cv c y0 q = u := by
  unfold cv; rw [h]

variable [DecidableEq QQ] [DecidableEq KK] [Fintype YY] [Nonempty YY] [∀ d, SampleableType (RF QQ YY Rc d)]

/-- the induction core (k = node keys already cached, m = node-query budget) -/
theorem nodeColl_aux {α : Type} (oa : OracleComp (unifSpec + ofFn (RF QQ YY Rc)) α) :
    ∀ (m k : ℕ) (cache : (ofFn (RF QQ YY Rc)).QueryCache),
      IsQueryBoundP oa (isNodeQ (QQ := QQ) (YY := YY) (Rc := Rc)) m → ¬ NodeColl cache →
      (∃ S : Finset QQ, S.card ≤ k ∧ ∀ q, cache (.inl q) ≠ none → q ∈ S) →
      Pr{let z ← randomOracleLoggedRun oa cache}[NodeColl z.2] ≤
        ∑ j ∈ Finset.range m, ((k + j : ℕ) : ℝ≥0∞) * (Fintype.card YY : ℝ≥0∞)⁻¹ := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro m k cache _ hnc _
    have : randomOracleLoggedRun (pure a : OracleComp (unifSpec + ofFn (RF QQ YY Rc)) α) cache =
        pure ((a, []), cache) := by simp [randomOracleLoggedRun]
    rw [this, prEvent_pure]
    simp [hnc]
  | query_bind t kk ih =>
    intro m k cache hm hnc hS
    rw [isQueryBoundP_query_bind_iff] at hm
    obtain ⟨hpos, hrest⟩ := hm
    rw [randomOracleLoggedRun_bind]
    -- the continuation's event reads only the final cache
    have hmap : ∀ (L : QueryLog (ofFn (RF QQ YY Rc))) (u) (c : (ofFn (RF QQ YY Rc)).QueryCache),
        Pr{let z ← (fun q => ((q.1.1, L ++ q.1.2), q.2)) <$> randomOracleLoggedRun (kk u) c}[NodeColl z.2] =
        Pr{let z ← randomOracleLoggedRun (kk u) c}[NodeColl z.2] := by
      intro L u c; rw [prEvent_map]
    rcases t with n | (q | key)
    · -- private coin: cache unchanged
      rw [randomOracleLoggedRun_uniformQuery, bind_map_left]
      refine prEvent_bind_le_of_forall_le _ _ _ fun u => ?_
      rw [hmap]
      exact ih u m k cache (by simpa [isNodeQ] using hrest u) hnc hS
    · -- node query
      have hm1 : ∀ u, IsQueryBoundP (kk u) (isNodeQ (QQ := QQ) (YY := YY) (Rc := Rc)) (m - 1) := fun u => by simpa [isNodeQ] using hrest u
      have hm0 : 0 < m := by simpa [isNodeQ] using hpos
      rw [randomOracleLoggedRun_hashQuery, bind_map_left, randomOracle.run_eq]
      have hsum_mono : ∑ j ∈ Finset.range (m - 1), ((k + j : ℕ) : ℝ≥0∞) * (Fintype.card YY : ℝ≥0∞)⁻¹ ≤
          ∑ j ∈ Finset.range m, ((k + j : ℕ) : ℝ≥0∞) * (Fintype.card YY : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le m 1))
      rcases hc : cache (.inl q) with _ | v
      · -- miss: a fresh uniform digest
        simp only [bind_assoc, pure_bind]
        obtain ⟨S, hSc, hSm⟩ := hS
        -- the digests already cached at node keys, as a `Fin S.card`-indexed family
        letI : Fintype (RF QQ YY Rc (.inl q)) := inferInstanceAs (Fintype YY)
        let vals : Fin S.card → RF QQ YY Rc (.inl q) := fun i =>
          cv (YY := YY) (Rc := Rc) cache (Classical.arbitrary YY) (S.equivFin.symm i).1
        have hbad : ∀ u : RF QQ YY Rc (.inl q), NodeColl (cache.cacheQuery (.inl q) u) → ∃ i, vals i = u := by
          rintro u ⟨q1, q2, hne, w, h1, h2⟩
          by_cases e1 : q1 = q
          · subst e1
            have hq2 : q2 ≠ q1 := Ne.symm hne
            rw [QueryCache.cacheQuery_self] at h1
            rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hq2)] at h2
            have hu : u = w := Option.some.inj h1
            have hm2 := hSm q2 (by rw [h2]; simp)
            refine ⟨S.equivFin ⟨q2, hm2⟩, ?_⟩
            simp only [vals, Equiv.symm_apply_apply]
            rw [cv_of_some (YY := YY) (Rc := Rc) cache _ q2 w h2, hu]
          · by_cases e2 : q2 = q
            · subst e2
              rw [QueryCache.cacheQuery_self] at h2
              rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using e1)] at h1
              have hu : u = w := Option.some.inj h2
              have hm1 := hSm q1 (by rw [h1]; simp)
              refine ⟨S.equivFin ⟨q1, hm1⟩, ?_⟩
              simp only [vals, Equiv.symm_apply_apply]
              rw [cv_of_some (YY := YY) (Rc := Rc) cache _ q1 w h1, hu]
            · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using e1)] at h1
              rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using e2)] at h2
              exact absurd ⟨q1, q2, hne, w, h1, h2⟩ hnc
        have hstep : Pr{let u ← ($ᵗ (RF QQ YY Rc (.inl q)))}[NodeColl (cache.cacheQuery (.inl q) u)] ≤
            (k : ℝ≥0∞) * (Fintype.card YY : ℝ≥0∞)⁻¹ := by
          have h1 := SampleableType.prEvent_uniformSample_exists_eq_le (α := RF QQ YY Rc (.inl q)) vals
          refine (prEvent_mono_of_support _ _ _ (fun u _ hu => hbad u hu)).trans (h1.trans ?_)
          rw [div_eq_mul_inv]
          gcongr
          all_goals first | exact_mod_cast hSc | exact le_rfl
        have hcont : ∀ u ∈ support ($ᵗ (RF QQ YY Rc (.inl q))), ¬ NodeColl (cache.cacheQuery (.inl q) u) →
            Pr{let z ← (fun r => ((r.1.1, [⟨Sum.inl q, u⟩] ++ r.1.2), r.2)) <$>
              randomOracleLoggedRun (kk u) (cache.cacheQuery (.inl q) u)}[NodeColl z.2] ≤
            ∑ j ∈ Finset.range (m - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) * (Fintype.card YY : ℝ≥0∞)⁻¹ := by
          intro u _ hnc'
          rw [hmap]
          refine ih u (m - 1) (k + 1) _ (hm1 u) hnc' ⟨insert q S, (Finset.card_insert_le q S).trans (by omega), ?_⟩
          intro q' hq'
          by_cases e : q' = q
          · subst e; exact Finset.mem_insert_self _ _
          · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using e)] at hq'
            exact Finset.mem_insert_of_mem (hSm q' hq')
        refine (prEvent_bind_le_prEvent_add_of_support _ _ _ _ hcont).trans ?_
        refine (add_le_add hstep le_rfl).trans (le_of_eq ?_)
        conv_rhs => rw [show m = (m - 1) + 1 from by omega]
        rw [Finset.sum_range_succ' (fun j => ((k + j : ℕ) : ℝ≥0∞) * (Fintype.card YY : ℝ≥0∞)⁻¹)]
        simp only [Nat.add_zero]
        rw [add_comm, Finset.sum_congr rfl fun j _ => by rw [show k + 1 + j = k + (j + 1) from by omega]]
      · -- hit
        simp only [hc, pure_bind]
        rw [hmap]
        exact (ih v (m - 1) k cache (hm1 v) hnc hS).trans hsum_mono
    · -- FS key: node entries unchanged
      rw [randomOracleLoggedRun_hashQuery, bind_map_left, randomOracle.run_eq]
      rcases hc : cache (.inr key) with _ | v
      · simp only [hc, bind_assoc, pure_bind]
        refine prEvent_bind_le_of_forall_le _ _ _ fun u => ?_
        rw [hmap]
        refine ih u m k _ (by simpa [isNodeQ] using hrest u) ?_ ?_
        · rintro ⟨q1, q2, hne, w, h1, h2⟩
          rw [QueryCache.cacheQuery_of_ne _ _ (by simp)] at h1 h2
          exact hnc ⟨q1, q2, hne, w, h1, h2⟩
        · obtain ⟨S, hSc, hSm⟩ := hS
          refine ⟨S, hSc, fun q' hq' => hSm q' ?_⟩
          rwa [QueryCache.cacheQuery_of_ne _ _ (by simp)] at hq'
      · simp only [hc, pure_bind]
        rw [hmap]
        exact ih v m k cache (by simpa [isNodeQ] using hrest v) hnc hS


theorem prEvent_nodeColl_le {α : Type} (oa : OracleComp (unifSpec + ofFn (RF QQ YY Rc)) α) (n : ℕ)
    (hn : IsQueryBoundP oa (isNodeQ (QQ := QQ) (YY := YY) (Rc := Rc)) n) :
    Pr{let z ← randomOracleLoggedRun oa ∅}[NodeColl z.2] ≤ ((n ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card YY) := by
  have h := nodeColl_aux oa n 0 ∅ hn (by rintro ⟨q1, q2, -, u, h1, -⟩; simp at h1)
    ⟨∅, by simp, fun q hq => by simp at hq⟩
  refine h.trans ?_
  have hg := ENNReal.gauss_sum_inv_eq n (Fintype.card YY : ℝ≥0∞)
  simp only [Nat.zero_add] at hg ⊢
  rw [hg]
  gcongr
  exact_mod_cast (show n * (n - 1) ≤ n ^ 2 by rw [pow_two]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))


/-! ### a hash-only program run with RECORDED answers -/

section Rec
variable {β : Type}

/-- one node query, its answer appended to the record -/
def recImpl : QueryImpl (QQ →ₒ YY) (StateT (List (QQ × YY)) (OracleComp (unifSpec + ofFn (RF QQ YY Rc)))) :=
  fun q => do
    let u ← (liftM ((unifSpec + ofFn (RF QQ YY Rc)).query (.inr (.inl q))) :
      OracleComp (unifSpec + ofFn (RF QQ YY Rc)) (RF QQ YY Rc (.inl q)))
    modify (fun L => L ++ [(q, (u : YY))])
    pure (u : YY)

/-- the program `P` over the side oracle's node half, recording `(key, answer)` of every query -/
def recRun (P : OracleComp (QQ →ₒ YY) β) (L0 : List (QQ × YY)) : OracleComp (unifSpec + ofFn (RF QQ YY Rc)) (β × List (QQ × YY)) :=
  (simulateQ (recImpl (Rc := Rc)) P).run L0

/-- the same against a total table `h` (pure) -/
def tabImpl (h : QQ → YY) : QueryImpl (QQ →ₒ YY) (StateM (List (QQ × YY))) :=
  fun q => do modify (fun L => L ++ [(q, h q)]); pure (h q)

def tabRun (h : QQ → YY) (P : OracleComp (QQ →ₒ YY) β) (L0 : List (QQ × YY)) : β × List (QQ × YY) :=
  (simulateQ (tabImpl h) P).run L0

theorem recRun_query_bind (q : QQ) (k : YY → OracleComp (QQ →ₒ YY) β) (L0 : List (QQ × YY)) :
    recRun (Rc := Rc) (liftM ((QQ →ₒ YY).query q) >>= k) L0 =
      (liftM ((unifSpec + ofFn (RF QQ YY Rc)).query (.inr (.inl q))) :
        OracleComp (unifSpec + ofFn (RF QQ YY Rc)) (RF QQ YY Rc (.inl q))) >>= fun u =>
        recRun (Rc := Rc) (k u) (L0 ++ ([((q : QQ), (show YY from u))] : List (QQ × YY))) := by
  simp [recRun, recImpl, StateT.run_bind, simulateQ_bind]
  rfl

/-- eager: against the table `gF` the recorded run is the point mass at the pure run -/
theorem recRun_withTable (gF : ∀ d, RF QQ YY Rc d) (P : OracleComp (QQ →ₒ YY) β) (L0 : List (QQ × YY)) :
    simulateQ (NockvmE2E.Exec.E2E.withTable gF) (recRun P L0) = pure (tabRun (fun q => gF (.inl q)) P L0) := by
  induction P using OracleComp.inductionOn generalizing L0 with
  | pure a => simp [recRun, tabRun]; rfl
  | query_bind q k ih =>
    have e1 : recRun (Rc := Rc) (liftM ((QQ →ₒ YY).query q) >>= k) L0 =
        (liftM ((unifSpec + ofFn (RF QQ YY Rc)).query (.inr (.inl q))) :
          OracleComp (unifSpec + ofFn (RF QQ YY Rc)) (RF QQ YY Rc (.inl q))) >>= fun u =>
          recRun (Rc := Rc) (k u) (L0 ++ ([((q : QQ), (show YY from u))] : List (QQ × YY))) := by
      simp [recRun, recImpl, StateT.run_bind, simulateQ_bind]
      rfl
    have e2 : tabRun (fun q => gF (.inl q)) (liftM ((QQ →ₒ YY).query q) >>= k) L0 =
        tabRun (fun q => gF (.inl q)) (k (gF (.inl q))) (L0 ++ ([((q : QQ), (show YY from gF (.inl q)))] : List (QQ × YY))) := by
      simp [tabRun, tabImpl, StateT.run_bind, simulateQ_bind]
      rfl
    have e3 : simulateQ (NockvmE2E.Exec.E2E.withTable gF)
        (liftM ((unifSpec + ofFn (RF QQ YY Rc)).query (.inr (.inl q))) :
          OracleComp (unifSpec + ofFn (RF QQ YY Rc)) (RF QQ YY Rc (.inl q))) = pure (gF (.inl q)) := by
      simp [NockvmE2E.Exec.E2E.withTable]; rfl
    rw [e1, e2, simulateQ_bind, e3, pure_bind]
    exact ih _ _

/-- lazy: every recorded pair is in the final cache (given the initial record is) -/
theorem recRun_cached (P : OracleComp (QQ →ₒ YY) β) :
    ∀ (L0 : List (QQ × YY)) (cache : (ofFn (RF QQ YY Rc)).QueryCache),
      (∀ p ∈ L0, cache (.inl p.1) = some p.2) →
      ∀ z ∈ support (randomOracleLoggedRun (recRun (Rc := Rc) P L0) cache), ∀ p ∈ z.1.1.2, z.2 (.inl p.1) = some p.2 := by
  induction P using OracleComp.inductionOn with
  | pure a =>
    intro L0 cache hL z hz p hp
    have e : randomOracleLoggedRun (recRun (Rc := Rc) (pure a : OracleComp (QQ →ₒ YY) β) L0) cache =
        pure (((a, L0), []), cache) := by simp [recRun, randomOracleLoggedRun]
    rw [e, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hL p hp
  | query_bind q k ih =>
    intro L0 cache hL z hz p hp
    rw [recRun_query_bind, randomOracleLoggedRun_bind, support_bind] at hz
    simp only [Set.mem_iUnion, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, z', hz', rfl⟩ := hz
    obtain ⟨hq, hle⟩ := NockvmE2E.Ung.ro_hash_support (Sum.inl q) cache r hr
    refine ih r.1.1 _ r.2 ?_ z' hz' p hp
    intro p' hp'
    rcases List.mem_append.1 hp' with h | h
    · exact hle (hL p' h)
    · simp only [List.mem_singleton] at h
      subst h
      exact hq

/-- the query count of the recorded run is the program's -/
theorem recRun_bound (P : OracleComp (QQ →ₒ YY) β) :
    ∀ (m : ℕ) (L0 : List (QQ × YY)), IsTotalQueryBound P m →
      IsQueryBoundP (recRun (Rc := Rc) P L0) (isNodeQ (QQ := QQ) (YY := YY) (Rc := Rc)) m := by
  induction P using OracleComp.inductionOn with
  | pure a => intro m L0 _; simp [recRun]
  | query_bind q k ih =>
    intro m L0 hm
    rw [isTotalQueryBound_query_bind_iff] at hm
    rw [recRun_query_bind, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr hm.1, fun u => ?_⟩
    simpa [isNodeQ] using ih u (m - 1) _ (hm.2 u)

end Rec

section Transfer
variable {O β : Type}

/-- two recorded pairs with distinct keys and equal answers -/
def TraceColl (L : List (QQ × YY)) : Prop := ∃ p1 ∈ L, ∃ p2 ∈ L, p1.1 ≠ p2.1 ∧ p1.2 = p2.2

/-- the continuation: the recorded run of `P o` -/
def contRec (P : O → OracleComp (QQ →ₒ YY) β) : Option O → OracleComp (unifSpec + ofFn (RF QQ YY Rc)) (Option (β × List (QQ × YY)))
  | none => pure none
  | some o => some <$> recRun (Rc := Rc) (P o) []

theorem ro_map {α γ : Type} (f : α → γ) (oa : OracleComp (unifSpec + ofFn (RF QQ YY Rc)) α) (cache : (ofFn (RF QQ YY Rc)).QueryCache) :
    randomOracleLoggedRun (f <$> oa) cache = (fun z => ((f z.1.1, z.1.2), z.2)) <$> randomOracleLoggedRun oa cache := by
  rw [map_eq_bind_pure_comp, randomOracleLoggedRun_bind]
  simp [NockvmE2E.Ung.ro_pure, map_eq_bind_pure_comp]

/-- **eager -> lazy, trace collisions**: if the eager event forces a collision in the recorded trace of `P o` against the table,
it is bounded by the node-key birthday bound of the adversary's and `P`'s node queries -/
theorem pr_eager_traceColl_le [Finite (QQ ⊕ KK)] [SampleableType (∀ d, RF QQ YY Rc d)]
    (oa : OracleComp (unifSpec + ofFn (RF QQ YY Rc)) (Option O)) (P : O → OracleComp (QQ →ₒ YY) β)
    (E : (∀ d, RF QQ YY Rc d) → Option O → Prop) (nA m : ℕ)
    (hA : IsQueryBoundP oa (isNodeQ (QQ := QQ) (YY := YY) (Rc := Rc)) nA) (hP : ∀ o, IsTotalQueryBound (P o) m)
    (hE : ∀ gF o, E gF o → ∃ o', o = some o' ∧ TraceColl (tabRun (fun q => gF (.inl q)) (P o') []).2) :
    Pr{let gF ← $ᵗ (∀ d, RF QQ YY Rc d); let o ← simulateQ (NockvmE2E.Exec.E2E.withTable gF) oa}[E gF o] ≤
      (((nA + m) ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card YY) := by
  classical
  let B : Option (β × List (QQ × YY)) → Prop := fun c => match c with
    | none => False
    | some c => TraceColl c.2
  refine (NockvmE2E.Exec.E2E.pr_flat_le_audited oa (contRec (Rc := Rc) P) E B ?_).trans ?_
  · intro gF o hEo
    obtain ⟨o', rfl, hc⟩ := hE gF o hEo
    refine ⟨some (tabRun (fun q => gF (.inl q)) (P o') []), ?_, hc⟩
    simp only [contRec, simulateQ_map, recRun_withTable, map_pure]
  · have hq : IsQueryBoundP (oa >>= contRec (Rc := Rc) P) (isNodeQ (QQ := QQ) (YY := YY) (Rc := Rc)) (nA + m) := by
      refine isQueryBoundP_bind hA fun o _ => ?_
      rcases o with _ | o
      · exact isQueryBoundP_pure (p := isNodeQ (QQ := QQ) (YY := YY) (Rc := Rc)) _ _
      · exact (isQueryBoundP_map_iff _ _ _).2 (recRun_bound _ m [] (hP o))
    refine le_trans (prEvent_mono_of_support _ _ (fun j => NodeColl j.2) ?_) (prEvent_nodeColl_le _ _ hq)
    intro j hj hB
    rw [randomOracleLoggedRun_bind, support_bind] at hj
    simp only [Set.mem_iUnion, support_map, Set.mem_image] at hj
    obtain ⟨r, _, z', hz', rfl⟩ := hj
    rcases hr : r.1.1 with _ | o
    · rw [hr] at hz'
      simp only [contRec, NockvmE2E.Ung.ro_pure, support_pure, Set.mem_singleton_iff] at hz'
      subst hz'
      exact hB.elim
    · rw [hr] at hz'
      simp only [contRec, ro_map, support_map, Set.mem_image] at hz'
      obtain ⟨w, hw, rfl⟩ := hz'
      obtain ⟨p1, h1, p2, h2, hne, heq⟩ := hB
      have hc := recRun_cached (Rc := Rc) (P o) [] r.2 (by simp) w hw
      exact ⟨p1.1, p2.1, hne, p1.2, hc p1 h1, by rw [heq]; exact hc p2 h2⟩

end Transfer


section Assembly
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.E2E NockvmE2E.Exec.E2EOnlineP NockvmE2E.Merkle NockvmE2E.Merkle.BadBound
open Interaction.Oracle Interaction.Oracle.FiatShamir Interaction.Oracle.Security.StateRestoration ProtocolSpec

/-- **hcoll, generic form**: an eager side-table event that forces a collision in the recorded trace of a hash-only program `P o`
(at most `m` node queries) has probability at most `(Q_H + m)^2 / (2|Dg|)`, `Q_H` the side adversary's node-query budget -/
theorem hcoll_generic {D : Type} {R : D → Type} [DecidableEq D] [instR : SampleableType (∀ d, R d)] {O β : Type}
    {skelsF : List BinaryTree.Skeleton} [Finite (NQuery skelsF)]
    {Op : Type} [Finite Op] [DecidableEq Op] {Stmt Salt : Type} [DecidableEq Stmt] [DecidableEq Salt] [Finite Stmt] [Finite Salt]
    {ms : MRounds DgJ8}
    [instRF : SampleableType (∀ d', succinctRange DgJ8 Op (NQuery skelsF) Stmt Salt ms d')]
    (sideOf : (∀ d, R d) → O → Stmt × Salt × PublicMessages (compiledRoundsK DgJ8 Op ms))
    (Aon : OracleComp ((unifSpec + OracleSpec.ofFn R) + OracleSpec.ofFn (succinctRange DgJ8 Op (NQuery skelsF) Stmt Salt ms)) (Option O))
    (Q_H m : ℕ)
    (hH : ∀ g, IsQueryBoundP (sideAdv sideOf Aon g)
      (@isHashQuery (NQuery skelsF) DgJ8 _ (SoundnessWorld.KC DgJ8 Op Stmt Salt ms)) Q_H)
    (P : O → OracleComp (NQuery skelsF →ₒ DgJ8) β) (hP : ∀ o, IsTotalQueryBound (P o) m)
    (E : (∀ d', succinctRange DgJ8 Op (NQuery skelsF) Stmt Salt ms d') → O → Prop)
    (htr : ∀ gF o, E gF o → TraceColl (tabRun (fun q => gF (.inl q)) (P o) []).2) :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange DgJ8 Op (NQuery skelsF) Stmt Salt ms d');
        let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => E gF o] ≤ (((Q_H + m) ^ 2 : ℕ) : ℝ≥0∞) / (2 * Fintype.card DgJ8) := by
  refine triple_le _ _ _ _ _ (fun g => ?_)
  have hre : ∀ gF, simulateQ (withTable2 g gF) Aon = simulateQ (withTable gF) (simulateQ (mainImpl g) Aon) :=
    fun gF => (sim_main g gF Aon).symm
  simp only [hre]
  have hA : IsQueryBoundP (simulateQ (mainImpl (RF := succinctRange DgJ8 Op (NQuery skelsF) Stmt Salt ms) g) Aon)
      (isNodeQ (QQ := NQuery skelsF) (YY := DgJ8) (Rc := Key.Challenge)) Q_H := by
    have := hH g
    unfold sideAdv at this
    rw [isQueryBoundP_map_iff] at this
    refine (isQueryBoundP_congr_pred ?_).1 this
    intro t; rcases t with _ | (_ | _) <;> simp [isNodeQ, isHashQuery]
  exact pr_eager_traceColl_le (QQ := NQuery skelsF) (YY := DgJ8) (Rc := Key.Challenge) _ P
    (fun gF o => match o with | none => False | some o => E gF o) Q_H m hA hP
    (fun gF o h => by
      rcases o with _ | o
      · exact h.elim
      · exact ⟨o, rfl, htr gF o h⟩)

end Assembly

end NockvmE2E.Exec.LazyColl
#print axioms NockvmE2E.Exec.LazyColl.hcoll_generic
#print axioms NockvmE2E.Exec.LazyColl.prEvent_nodeColl_le
#print axioms NockvmE2E.Exec.LazyColl.recRun_withTable
#print axioms NockvmE2E.Exec.LazyColl.recRun_cached
#print axioms NockvmE2E.Exec.LazyColl.recRun_bound
#print axioms NockvmE2E.Exec.LazyColl.pr_eager_traceColl_le
