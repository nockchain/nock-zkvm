/-
Merkle (B) file 8: the real-world bad-event bound ("BadBound"). Integrates `Phases.pr_bad_advOf_le` over the seed with `Derand.derand_prEvent_le`,
and derives Phases' `hbud` / `hH` for every seed from A-level (syntactic) bounds.
-/
import NockvmE2E.Merkle.Phases

open OracleComp OracleSpec MerkleTreeMultiExtractability
open NockvmE2E.Merkle.Derand NockvmE2E.Merkle.Phases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.BadBound

section Bounds

variable {Q Y : Type} {K J : Type} {Rc : K → Type} {C : J → Type}
variable {Cfg Address : Type} {config : Configuration Cfg Address}
variable [DecidableEq Q] [DecidableEq K] [DecidableEq J] [DecidableEq Y]
variable [∀ j, SampleableType (C j)] [∀ j, Finite (C j)] [∀ j, Nonempty (C j)]
variable [SampleableType Y] [Finite Y] [Nonempty Y]
variable [Inhabited Cfg] [Inhabited Y]
variable (keyRoots : K → List (Cfg × Y)) (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k)

/-- hash queries of the real program -/
def isHashQuery : (realSpec Q Y Rc).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

instance : DecidablePred (isHashQuery (Q := Q) (Y := Y) (Rc := Rc)) := fun t => by
  cases t with
  | inl _ => exact isFalse (by simp [isHashQuery])
  | inr t => cases t with
    | inl _ => exact isTrue trivial
    | inr _ => exact isFalse (by simp [isHashQuery])

/-- **FS-key budget**: along every run of `A` in which FS answers agree with the cache `seen`
(hash and coin answers arbitrary), at most `n` further distinct FS keys are fresh. -/
inductive FsBound {α : Type} :
    (ofFn Rc).QueryCache → ℕ → OracleComp (realSpec Q Y Rc) α → Prop
  | pure (a : α) (seen : (ofFn Rc).QueryCache) (n : ℕ) : FsBound seen n (.pure a)
  | coin (c : ℕ) (k : (realSpec Q Y Rc).Range (.inl c) → OracleComp (realSpec Q Y Rc) α)
      (seen : (ofFn Rc).QueryCache) (n : ℕ) :
      (∀ u, FsBound seen n (k u)) → FsBound seen n (.queryBind (.inl c) k)
  | hash (q : Q) (k : (realSpec Q Y Rc).Range (.inr (.inl q)) → OracleComp (realSpec Q Y Rc) α)
      (seen : (ofFn Rc).QueryCache) (n : ℕ) :
      (∀ u, FsBound seen n (k u)) → FsBound seen n (.queryBind (.inr (.inl q)) k)
  | fs (key : K) (k : (realSpec Q Y Rc).Range (.inr (.inr key)) → OracleComp (realSpec Q Y Rc) α)
      (seen : (ofFn Rc).QueryCache) (n : ℕ) :
      (∀ v, seen key = some v → FsBound seen n (k (ofF key v))) →
      (seen key = none → 0 < n) →
      (∀ v : Rc key, seen key = none →
        FsBound (seen.cacheQuery key v) (n - 1) (k (ofF key v))) →
      FsBound seen n (.queryBind (.inr (.inr key)) k)

theorem Obs.hash_seen (ob : Obs Q Y Rc config) (q : Q) (y : Y) : (ob.hash q y).seen = ob.seen := rfl
theorem Obs.hash_ext (ob : Obs Q Y Rc config) (q : Q) (y : Y) : (ob.hash q y).ext = ob.ext := rfl

theorem Obs.fresh_seen (ob : Obs Q Y Rc config) (key : K) (v : Rc key) :
    (ob.fresh keyRoots key v).seen = ob.seen.cacheQuery key v := by
  unfold Obs.fresh
  rcases keyRoots key with _ | ⟨x, xs⟩ <;> rfl

theorem Obs.fresh_len (k0 : ℕ) (hk : ∀ key, (keyRoots key).length ≤ k0)
    (ob : Obs Q Y Rc config) (key : K) (v : Rc key) :
    (ob.fresh keyRoots key v).ext.checkpoints.length ≤ ob.ext.checkpoints.length + k0 := by
  have := hk key
  unfold Obs.fresh
  rcases h : keyRoots key with _ | ⟨x, xs⟩
  · simp
  · simp only [h]
    rw [Obs.stop_ext, recQ_length]
    simp [h] at this ⊢; omega

/-- hash-query budget of `bs`, for every seed and observer -/
theorem bs_hashBound {α : Type} (A : OracleComp (realSpec Q Y Rc) α) (n : ℕ)
    (h : IsQueryBoundP A (isHashQuery (Q := Q) (Y := Y) (Rc := Rc)) n) :
    ∀ (ob : Obs Q Y Rc config) (sd : QuerySeed (progSpec Q Y C)),
      IsTotalQueryBound (bs keyRoots rd e A ob sd) n := by
  induction A generalizing n with
  | pure a => intro ob sd; simp only [bs]; exact trivial
  | queryBind t k ih =>
    intro ob sd
    have h := (isQueryBoundP_query_bind_iff (p := isHashQuery (Q := Q) (Y := Y) (Rc := Rc)) t k n).mp h
    rcases t with c | q | key
    · simp only [bs]
      exact ih _ n (by simpa [isHashQuery] using h.2 _) _ _
    · simp only [bs]
      have h1 := h.1
      have h2 := h.2
      simp only [isHashQuery, not_true_eq_false, false_or, ite_true] at h1 h2
      exact isTotalQueryBound_query_bind_iff.mpr ⟨h1, fun y => ih _ _ (h2 _) _ _⟩
    · simp only [bs]
      have h2 := fun u => by simpa [isHashQuery] using h.2 u
      rcases hs : ob.seen key with _ | v
      · exact ih _ n (h2 _) _ _
      · exact ih _ n (h2 _) _ _

/-- checkpoint budget of `bs` -/
theorem bs_ckptBound {α : Type} (k0 : ℕ) (hk : ∀ key, (keyRoots key).length ≤ k0)
    {seen : (ofFn Rc).QueryCache} {n : ℕ} {A : OracleComp (realSpec Q Y Rc) α}
    (h : FsBound seen n A) :
    ∀ (B : ℕ) (ob : Obs Q Y Rc config) (sd : QuerySeed (progSpec Q Y C)), ob.seen = seen →
      ob.ext.checkpoints.length + k0 * n ≤ B →
      ∀ r ∈ support (bs keyRoots rd e A ob sd), r.2.1.ext.checkpoints.length ≤ B := by
  induction h with
  | pure a seen n =>
    intro B ob sd _ hB r hr
    simp [bs] at hr; subst hr; simp; omega
  | coin c k seen n _ ih =>
    intro B ob sd hs hB r hr
    simp only [bs] at hr
    exact ih _ B ob _ hs hB r hr
  | hash q k seen n _ ih =>
    intro B ob sd hs hB r hr
    simp only [bs, mem_support_bind_iff] at hr
    obtain ⟨y, _, hr⟩ := hr
    exact ih _ B (ob.hash q y) sd (by rw [Obs.hash_seen, hs]) (by rw [Obs.hash_ext]; exact hB) r hr
  | fs key k seen n _ hn _ ih1 ih2 =>
    intro B ob sd hs hB r hr
    simp only [bs] at hr
    rcases hs' : ob.seen key with _ | v
    · rw [hs'] at hr
      simp only at hr
      have hsn : seen.toFn key = none := by rw [← hs]; exact hs'
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hn hsn; omega⟩
      have := Obs.fresh_len keyRoots k0 hk ob key (e key (popCoin (Y := Y) sd (.inr (rd key))).1)
      exact ih2 _ hsn B _ _ (by rw [Obs.fresh_seen, hs]) (by simp [Nat.mul_succ] at hB ⊢; omega) r hr
    · rw [hs'] at hr
      simp only at hr
      exact ih1 v (by rw [← hs]; exact hs') B ob sd hs hB r hr
variable {α : Type}

theorem finalNE_len (finalRoots : α → List (Cfg × Y)) (k0 : ℕ) (hk0 : 1 ≤ k0)
    (hfin : ∀ a, (finalRoots a).length ≤ k0) (a : α) :
    (finalNE finalRoots a).2.length + 1 ≤ k0 := by
  have := hfin a
  unfold finalNE
  rcases h : finalRoots a with _ | ⟨x, xs⟩
  · simpa using hk0
  · simp [h] at this ⊢; omega

/-- **hH for every seed** from the syntactic hash-query bound of `A`. -/
theorem hH_of_hashBound (A : OracleComp (realSpec Q Y Rc) α) (Q_H : ℕ)
    (h : IsQueryBoundP A (isHashQuery (Q := Q) (Y := Y) (Rc := Rc)) Q_H)
    (σ : QuerySeed (progSpec Q Y C)) :
    IsTotalQueryBound (seededProg rd e (instr (config := config) keyRoots A) σ) Q_H := by
  rw [seededProg_instr]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr
    (bs_hashBound (config := config) (C := C) keyRoots rd e A Q_H h _ _)

/-- **hbud for every seed** from the FS-key budget of `A`: each fresh FS key adds at most `k0` roots,
the final stop at most `k0`, so the run fits in `k0 * (Q_FS + 1)` phases. -/
theorem hbud_of_fsBound (finalRoots : α → List (Cfg × Y)) (A : OracleComp (realSpec Q Y Rc) α)
    (k0 Q_FS : ℕ) (hk0 : 1 ≤ k0) (hk : ∀ key, (keyRoots key).length ≤ k0)
    (hfin : ∀ a, (finalRoots a).length ≤ k0)
    (h : FsBound (∅ : (ofFn Rc).QueryCache) Q_FS A) (σ : QuerySeed (progSpec Q Y C)) :
    ∀ z ∈ support (seededProg rd e (instr (config := config) keyRoots A) σ),
      (finalObs finalRoots z.1.1 z.1.2).ext.checkpoints.length ≤ k0 * (Q_FS + 1) := by
  intro z hz
  rw [seededProg_instr, support_map] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have h1 := bs_ckptBound (config := config) (C := C) keyRoots rd e k0 hk h (k0 * Q_FS)
    (Obs.init : Obs Q Y Rc config) σ rfl (by simp [Obs.init, ExtractorState.empty]) r hr
  have h2 := finalNE_len finalRoots k0 hk0 hfin r.1
  simp only [finalObs, Obs.stop_ext, recQ_length]
  simp only [List.length_cons]
  have : k0 * (Q_FS + 1) = k0 * Q_FS + k0 := by ring
  omega

end Bounds

section RealWorld

variable {Q Y : Type} {K J : Type} {Rc : K → Type} {C : J → Type}
variable {Cfg Address : Type} {config : Configuration Cfg Address}
variable [DecidableEq Q] [DecidableEq K] [DecidableEq J] [DecidableEq Y]
variable [∀ j, SampleableType (C j)] [∀ k, SampleableType (Rc k)]
  [∀ j, Finite (C j)] [∀ j, Nonempty (C j)]
variable [SampleableType Y] [Finite Y] [Nonempty Y]
variable [Inhabited Cfg] [Inhabited Y]
variable (keyRoots : K → List (Cfg × Y)) (rd : K → J) (e : ∀ k, C (rd k) ≃ Rc k)
variable {α : Type}

/-- a hash query of the real world, answered in `Y` -/
def hashImpl : QueryImpl (hashSpec Q Y) (OracleComp (realSpec Q Y Rc)) :=
  fun q => toH q <$> qH q

/-- hash-only programs (the honest verification) run inside the real world -/
def liftV {β : Type} (g : OracleComp (hashSpec Q Y) β) : OracleComp (realSpec Q Y Rc) β :=
  simulateQ hashImpl g

theorem seeded_liftV {β : Type} (g : OracleComp (hashSpec Q Y) β)
    (c : (ofFn Rc).QueryCache) (σ : QuerySeed (progSpec Q Y C)) :
    (simulateQ sodImpl ((simulateQ (foldImpl rd e) (liftV g)).run c)).run σ =
      (fun b => ((b, c), σ)) <$> g := by
  induction g using OracleComp.inductionOn generalizing c σ with
  | pure a => simp [liftV]
  | query_bind q k ih =>
    simp only [liftV, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, hashImpl, StateT.run_bind, map_bind] at ih ⊢
    have h1 : (simulateQ sodImpl ((simulateQ (foldImpl rd e) (toH q <$> qH q : OracleComp (realSpec Q Y Rc) Y)).run c)).run σ =
        (fun y => ((y, c), σ)) <$> (liftM (OracleSpec.query q) : OracleComp (hashSpec Q Y) Y) := by
      rw [simulateQ_map, simulateQ_qH]
      simp only [foldImpl, StateT.run_map]
      simp [StateT.run_lift, simulateQ_map, sodImpl, toH]
    rw [h1]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
    refine bind_congr fun y => ?_
    have := ih y c σ
    simpa [map_eq_bind_pure_comp] using this

theorem seeded_bind_liftV {β γ : Type} (x : OracleComp (realSpec Q Y Rc) α)
    (g : α → OracleComp (hashSpec Q Y) β) (h : α → β → γ) (σ : QuerySeed (progSpec Q Y C)) :
    seededProg rd e (x >>= fun a => liftV (g a) >>= fun b => pure (h a b)) σ =
      seededProg rd e x σ >>= fun z => (fun b => (h z.1 b, z.2)) <$> g z.1 := by
  simp only [seededProg, foldProg, simulateQ_bind, StateT.run_bind, StateT.run'_eq, map_bind]
  rw [map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun a => ?_
  rw [seeded_liftV rd e (g a.1.1) a.1.2 a.2]
  simp [map_eq_bind_pure_comp]

/-- **The real world W0'**: `A` with the observer, then the honest verification's hash queries
(on the claims `mkTerminal` computes from A's output and the final extractor state), as one
program over the single lazy RO; its output is the game transcript. -/
def realWorld (model : MerkleTreeExtractability.NodeQueryModel Q Address Y)
    (finalRoots : α → List (Cfg × Y))
    (mkTerminal : α → ExtractorState Cfg Q Address Y config → List (OpeningClaim Q Y config))
    (rounds : ℕ) (A : OracleComp (realSpec Q Y Rc) α) :
    OracleComp (realSpec Q Y Rc) (Transcript Cfg Q Address Y config) :=
  instr (config := config) keyRoots A >>= fun r =>
    liftV (verifyOpeningClaims model
        (mkTerminal r.1 (finalExt (Address := Address) finalRoots rounds r.1 r.2))) >>= fun attempts =>
      pure ({ extractorState := finalExt (Address := Address) finalRoots rounds r.1 r.2,
              attempts, terminalSuffix := [] } : Transcript Cfg Q Address Y config)

/-- **`bad_real_le`**: the bad event (any checkpoint extraction disagreement) has probability at most
`N(nodeBudget, checkpointCount, verifierOverhead, Q_H) / |Y|` in the QD logged lazy-RO real world running
`A` and the honest verification. `hbud`/`hH` are Phases' pointwise-in-σ hypotheses. -/
theorem bad_real_le [DecidableEq Address]
    (model : MerkleTreeExtractability.NodeQueryModel Q Address Y)
    (finalRoots : α → List (Cfg × Y))
    (mkTerminal : α → ExtractorState Cfg Q Address Y config → List (OpeningClaim Q Y config))
    (A : OracleComp (realSpec Q Y Rc) α)
    (rounds Q_H nodeBudget checkpointCount verifierOverhead perCheckpoint : ℕ)
    (hbud : ∀ σ : QuerySeed (progSpec Q Y C),
      ∀ z ∈ support (seededProg rd e (instr (config := config) keyRoots A) σ),
      (finalObs finalRoots z.1.1 z.1.2).ext.checkpoints.length ≤ rounds)
    (hH : ∀ σ : QuerySeed (progSpec Q Y C),
      IsTotalQueryBound (seededProg rd e (instr (config := config) keyRoots A) σ) Q_H)
    (hterm : ∀ a ext, claimsQueryCount (mkTerminal a ext) ≤ verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hnodes : rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : rounds ≤ checkpointCount) :
    Pr{let z ← realObs <$> randomOracleLoggedRun
        (realWorld keyRoots model finalRoots mkTerminal rounds A) ∅}[
        Transcript.HasAnyCheckpointExtractionDisagreement model z.1] ≤
      (multiCheckpointROMErrorNumerator nodeBudget checkpointCount verifierOverhead Q_H : ENNReal) *
        (Nat.card Y : ENNReal)⁻¹ := by
  refine derand_prEvent_le rd e _ (fun z => Transcript.HasAnyCheckpointExtractionDisagreement model z.1)
    fun σ => ?_
  have hmap : Prod.fst <$> seededProg rd e (realWorld keyRoots model finalRoots mkTerminal rounds A) σ =
      extractabilityInner model config rounds (advOf keyRoots rd e finalRoots mkTerminal A σ) := by
    rw [extractabilityInner_advOf keyRoots rd e model finalRoots mkTerminal A σ rounds (hbud σ)]
    unfold realWorld
    rw [seeded_bind_liftV]
    simp [map_eq_bind_pure_comp]
  have := pr_bad_advOf_le keyRoots rd e model finalRoots mkTerminal A rounds Q_H nodeBudget
    checkpointCount verifierOverhead perCheckpoint hbud hH hterm hconfig hnodes hcheckpoints σ
  unfold extractabilityExperiment at this
  rw [← hmap, withCacheOverlay_map, prEvent_map] at this
  exact this

include rd e in
/-- **`bad_real_le_of_bounds`**: the bound with A-level hypotheses only. `hQ`: A makes at most `Q_H` hash
queries on every path (`IsQueryBoundP A isHashQuery Q_H`); `hFS`: A makes at most `Q_FS` distinct fresh FS keys
on every path with FS-consistent answers (`FsBound ∅ Q_FS A`); `k0` bounds the roots per FS key and in the
final stop. With `K = k0 * (Q_FS + 1)` phases the bound is `N(K * perCheckpoint, K, overhead, Q_H) / |Y|`. -/
theorem bad_real_le_of_bounds [DecidableEq Address]
    (model : MerkleTreeExtractability.NodeQueryModel Q Address Y)
    (finalRoots : α → List (Cfg × Y))
    (mkTerminal : α → ExtractorState Cfg Q Address Y config → List (OpeningClaim Q Y config))
    (A : OracleComp (realSpec Q Y Rc) α)
    (k0 Q_FS Q_H verifierOverhead perCheckpoint : ℕ) (hk0 : 1 ≤ k0)
    (hk : ∀ key, (keyRoots key).length ≤ k0) (hfin : ∀ a, (finalRoots a).length ≤ k0)
    (hQ : IsQueryBoundP A (isHashQuery (Q := Q) (Y := Y) (Rc := Rc)) Q_H)
    (hFS : FsBound (∅ : (ofFn Rc).QueryCache) Q_FS A)
    (hterm : ∀ a ext, claimsQueryCount (mkTerminal a ext) ≤ verifierOverhead)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint) :
    Pr{let z ← realObs <$> randomOracleLoggedRun
        (realWorld keyRoots model finalRoots mkTerminal (k0 * (Q_FS + 1)) A) ∅}[
        Transcript.HasAnyCheckpointExtractionDisagreement model z.1] ≤
      (multiCheckpointROMErrorNumerator ((k0 * (Q_FS + 1)) * perCheckpoint) (k0 * (Q_FS + 1))
          verifierOverhead Q_H : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  bad_real_le keyRoots rd e model finalRoots mkTerminal A (k0 * (Q_FS + 1)) Q_H
    ((k0 * (Q_FS + 1)) * perCheckpoint) (k0 * (Q_FS + 1)) verifierOverhead perCheckpoint
    (hbud_of_fsBound keyRoots rd e finalRoots A k0 Q_FS hk0 hk hfin hFS)
    (hH_of_hashBound keyRoots rd e A Q_H hQ) hterm hconfig le_rfl le_rfl

end RealWorld


end NockvmE2E.Merkle.BadBound
