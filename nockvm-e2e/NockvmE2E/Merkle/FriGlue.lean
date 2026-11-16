/-
Merkle (B) file 11, part 2: the FRI glue. Transport of FRI's paired soundness
(`fri_paired_singleSalt_soundness`, over `(friAltP …).rounds`) to the `hclear` hypothesis of the
masked compiled protocol (over `pairedRoundsK Dg (friMask …)`, `pairGuards`, `pairAccepts friAccepts'`).
-/
import NockvmE2E.Merkle.Fri

open BinaryTree OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain NockvmE2E.FriPort
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.Fri

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

/-! ## Casting paths along an equality of round lists -/

/-- Transport of an execution path along an equality of round lists. -/
def castPath {R R' : List Round} (e : R = R') (p : (protocol R).tree.ExecutionPath) :
    (protocol R').tree.ExecutionPath :=
  cast (congrArg (fun R => (protocol R).tree.ExecutionPath) e) p

theorem castPath_cons {r r' : Round} {ts ts' : List Round} (e1 : r = r') (e2 : ts = ts')
    (e : r :: ts = r' :: ts') (p : (protocol (r :: ts)).tree.ExecutionPath)
    (q : (protocol (r' :: ts')).tree.ExecutionPath) (h : castPath e p = q) :
    HEq p.1 q.1 ∧ HEq p.2.1 q.2.1 ∧ castPath e2 p.2.2 = q.2.2 := by
  subst e1 e2
  unfold castPath at h
  rw [cast_eq] at h
  subst h
  exact ⟨HEq.rfl, HEq.rfl, by unfold castPath; rw [cast_eq]⟩

theorem fst_of_heq_neg {c : Prop} [Decidable c] (hc : ¬ c) {A Dg : Type} (x : PM c A Dg) (y : A)
    (h : HEq x y) : PM.fst c x = y := by
  unfold PM.fst
  simp only [hc, ↓reduceDIte]
  apply eq_of_heq
  exact (cast_heq _ _).trans h

theorem fst_of_heq_pos {c : Prop} [Decidable c] (hc : c) {A Dg : Type} (x : PM c A Dg) (y : A × Dg)
    (h : HEq x y) : PM.fst c x = y.1 := by
  unfold PM.fst
  simp only [hc, ↓reduceDIte]
  have : cast (PM_pos hc) x = y := eq_of_heq ((cast_heq _ _).trans h)
  rw [this]

section Glue

variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : FriLeaves (ω := ω) s) (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg)


/-- **The legacy transcript of a paired path is the one of its forgotten native path** (tail). `q` is the
path of the masked paired tail, `p` the same path read in `friAltP`'s own round list. -/
theorem tailPath_paired : (i c : ℕ) → (h : i + c = k) →
    (tr : (friAlt (ω := ω) s d l).PosTr i (by have := friAlt_r (ω := ω) s d l; omega)) →
    (p : (protocol ((friAltP (ω := ω) s d l Dg).tailRounds i (c + 1)
        (by have : (friAltP (ω := ω) s d l Dg).r = k + 1 := rfl; omega))).tree.ExecutionPath) →
    (q : (protocol (pairedRoundsK Dg (friMerkleMask s d l L Dg enc i c h))).tree.ExecutionPath) →
    castPath (friAltP_tailRounds s d l L Dg enc i c h) p = q →
    (friAltP (ω := ω) s d l Dg).tailPath i (c + 1) (by have : (friAltP (ω := ω) s d l Dg).r = k + 1 := rfl; omega) tr p =
    (friAlt (ω := ω) s d l).tailPath i (c + 1) (by have := friAlt_r (ω := ω) s d l; omega) tr
      (toTail s d l L Dg enc i c h (forgetPath Dg (friMerkleMask s d l L Dg enc i c h) q))
  | i, 0, h, tr, p, q, hpq => by
      have hik : ¬ i < k := by omega
      obtain ⟨h1, h2, -⟩ := castPath_cons (friAltP_midRound_neg s d l Dg i (by omega) hik) rfl _ p q hpq
      have e1 := fst_of_heq_neg hik _ _ h1
      have e2 := eq_of_heq h2
      simp only [Lift.Alternating.tailPath, toTail]
      congr 1
      have e3 : (friAltP (ω := ω) s d l Dg).emb i (Lift.Alternating.lt_of_lt_r (friAlt (ω := ω) s d l) (show i < (friAlt (ω := ω) s d l).r by have := friAlt_r (ω := ω) s d l; omega)) p.1 =
          (friAlt (ω := ω) s d l).emb i (Lift.Alternating.lt_of_lt_r (friAlt (ω := ω) s d l) (show i < (friAlt (ω := ω) s d l).r by have := friAlt_r (ω := ω) s d l; omega)) q.1 := by
        show (friAlt (ω := ω) s d l).emb _ _ (PM.fst (i < k) p.1) = _
        rw [e1]
      unfold Lift.Alternating.step
      rw [e3, e2]
      rfl
  | i, c + 1, h, tr, p, q, hpq => by
      have hik : i < k := by omega
      obtain ⟨h1, h2, h3⟩ := castPath_cons (friAltP_midRound_pos s d l Dg i (by omega) hik)
        (friAltP_tailRounds s d l L Dg enc i.succ c (by omega)) _ p q hpq
      have e1 := fst_of_heq_pos hik _ _ h1
      have e2 := eq_of_heq h2
      have e3 : (friAltP (ω := ω) s d l Dg).emb i (Lift.Alternating.lt_of_lt_r (friAlt (ω := ω) s d l) (show i < (friAlt (ω := ω) s d l).r by have := friAlt_r (ω := ω) s d l; omega)) p.1 =
          (friAlt (ω := ω) s d l).emb i (Lift.Alternating.lt_of_lt_r (friAlt (ω := ω) s d l) (show i < (friAlt (ω := ω) s d l).r by have := friAlt_r (ω := ω) s d l; omega)) q.1.1 := by
        show (friAlt (ω := ω) s d l).emb _ _ (PM.fst (i < k) p.1) = _
        rw [e1]
      have hlt : i < (friAlt (ω := ω) s d l).r := by have := friAlt_r (ω := ω) s d l; omega
      have hs : (friAltP (ω := ω) s d l Dg).step i hlt tr p.1 p.2.1 =
          (friAlt (ω := ω) s d l).step i hlt tr q.1.1 q.2.1 := by
        unfold Lift.Alternating.step
        rw [e3, e2]
      have ih := tailPath_paired i.succ c (by omega)
        ((friAlt (ω := ω) s d l).step i hlt tr q.1.1 q.2.1) p.2.2 q.2.2 h3
      simp only [Lift.Alternating.tailPath, toTail]
      rw [hs]
      exact ih

/-- **The legacy transcript of a path of `friAltP.rounds`** equals the one of the native FRI path
obtained by forgetting the roots of the same path read in `pairedRoundsK Dg (friMask …)`. -/
theorem pathTranscript_paired
    (p : (protocol (friAltP (ω := ω) s d l Dg).rounds).tree.ExecutionPath)
    (q : (protocol (pairedRoundsK Dg (friMask s d l L Dg enc))).tree.ExecutionPath)
    (hpq : castPath (friAltP_rounds s d l L Dg enc) p = q) :
    (friAltP (ω := ω) s d l Dg).pathTranscript p =
      (friAlt (ω := ω) s d l).pathTranscript
        (toFriPath s d l L Dg enc (forgetPath Dg (friMask s d l L Dg enc) q)) := by
  obtain ⟨h1, h2, h3⟩ := castPath_cons (r := (friAltP (ω := ω) s d l Dg).headRound)
    (r' := (friAlt (ω := ω) s d l).headRound) rfl
    (friAltP_tailRounds s d l L Dg enc 0 k (by omega)) _ p q hpq
  have e2 := eq_of_heq h2
  have := tailPath_paired s d l L Dg enc 0 k (by omega)
    (Transcript.concat (m := ⟨0, (friAlt (ω := ω) s d l).lt_of_le_r (Nat.zero_le _)⟩) q.2.1
      (Lift.tr0 (pSpec k (ω := ω) s l))) p.2.2 q.2.2 h3
  unfold Lift.Alternating.pathTranscript
  rw [e2]
  exact this

variable [SampleableType F]

/-- The FRI paired soundness bound. -/
noncomputable def friEpsFS (θ δ : ℝ) (Q : ℕ) : ℝ≥0∞ :=
  Q * Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)) +
    (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞)

/-- **FRI paired soundness over any round list equal to `friAltP.rounds`**, with an arbitrary
acceptance predicate `acc` that implies the legacy acceptance on the decoded transcript. -/
theorem fri_soundness_of_rounds_eq (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (θ δ : ℝ)
    {Salt W : Type} [DecidableEq (FriStmt (ω := ω) s)] [DecidableEq Salt]
    (R : List Round) (e : (friAltP (ω := ω) s d l Dg).rounds = R)
    (guards : GuardSchedule (FriStmt (ω := ω) s × Salt) PUnit R)
    (acc : FriStmt (ω := ω) s × Salt → (protocol R).tree.ExecutionPath → Bool)
    (hacc : ∀ z p, acc z p = true →
      queryBad s d l (round_bound hdom) (initialOracle s z.1)
        (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
          ((friAltP (ω := ω) s d l Dg).pathTranscript (castPath e.symm p))))
    (adversary : SingleSaltAdversary (FriStmt (ω := ω) s) Salt W R)
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
      (singleSaltAcceptedExecution R guards acc adversary) ∅)}[
      match joint.1.1.1 with
      | none => False
      | some (z, _, _) => initialOracle s z.1 ∉ proximityLanguage s d δ] ≤
    friEpsFS (ω := ω) s d l θ δ Q := by
  subst e
  have hs := round_bound hdom
  have h := (friAltP (ω := ω) s d l Dg).singleSalt_soundness_of_stateFamily'
    {stmt | initialOracle s stmt ∈ proximityLanguage s d δ}
    (friState s d l hs θ δ)
    (fun stmt h0 => by
      rcases h0 with h0 | ⟨_, hi, _⟩
      · exact h0
      · exact absurd hi (Nat.not_lt_zero _))
    (fun stmt m hm tr msg hafter => by
      by_contra hb
      exact Verifier.badEventState_prover_next _ _ m hm _ tr hb msg hafter)
    (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))
    (fun stmt hstmt => friState_challengeLaw s d l hs θ δ stmt hstmt)
    guards acc adversary (fun _ _ _ => True)
    (fun z path _ hacc' _ => Or.inr ⟨queryChallenge s l, (queryChallenge s l).1.isLt,
      (badEvent_query s d l hs θ _ _).mpr (by
        have := hacc z path hacc'
        simpa [castPath] using this)⟩)
    Q queryBound
  rw [← ENNReal.ofNNReal_finsetSum, sum_challengeError] at h
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hbad
  · exact hbad.elim
  · exact ⟨hbad, trivial⟩

/-- The legacy acceptance on the decoded transcript, for the masked paired acceptance predicate. -/
theorem pairAccepts_friAccepts'_imp (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) {Salt : Type}
    (z : FriStmt (ω := ω) s × Salt)
    (p : (protocol (pairedRoundsK Dg (friMask s d l L Dg enc))).tree.ExecutionPath)
    (h : pairAccepts Dg (friMask s d l L Dg enc) (friAccepts' s d l L Dg enc hdom (Salt := Salt)) z p = true) :
    queryBad s d l (round_bound hdom) (initialOracle s z.1)
      (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
        ((friAltP (ω := ω) s d l Dg).pathTranscript
          (castPath (friAltP_rounds s d l L Dg enc).symm p))) := by
  have hq : castPath (friAltP_rounds s d l L Dg enc) (castPath (friAltP_rounds s d l L Dg enc).symm p) = p := by
    unfold castPath; rw [cast_cast]; exact cast_eq _ _
  rw [pathTranscript_paired s d l L Dg enc _ p hq]
  exact (friAccepts_iff s d l hdom z _).mp h

/-- **FRI's `hclear`** for the masked compiled protocol: the hypothesis of `merkle_singleSalt_soundness`
(over `pairedRoundsK Dg (friMask …)`, with `pairGuards` and `pairAccepts friAccepts'`), discharged with
`εFS Q = Q · max challengeError + (Σ foldingError + (1 − min θ δ)^l)`. -/
theorem fri_hclear (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (θ δ : ℝ)
    {Salt W : Type} [DecidableEq (FriStmt (ω := ω) s)] [DecidableEq Salt]
    (Op : Type) [Finite Op] [DecidableEq Op]
    (guards : GuardSchedule (FriStmt (ω := ω) s × Salt) PUnit
      (compiledRoundsK Dg Op (friMask s d l L Dg enc)))
    (B : SingleSaltAdversary (FriStmt (ω := ω) s) Salt W (pairedRoundsK Dg (friMask s d l L Dg enc)))
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun B.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let j ← randomOracleLoggedRun (singleSaltAcceptedExecution
        (pairedRoundsK Dg (friMask s d l L Dg enc))
        (pairGuards Dg Op (friMask s d l L Dg enc) guards)
        (pairAccepts Dg (friMask s d l L Dg enc) (friAccepts' s d l L Dg enc hdom (Salt := Salt))) B) ∅}[
      match j.1.1.1 with
      | none => False
      | some (z, _, _) => z.1 ∉ {stmt | initialOracle s stmt ∈ proximityLanguage s d δ}] ≤
    friEpsFS (ω := ω) s d l θ δ Q := by
  refine le_trans (prEvent_mono _ _ _ ?_) (fri_soundness_of_rounds_eq s d l Dg hdom θ δ _ (friAltP_rounds s d l L Dg enc)
    (pairGuards Dg Op (friMask s d l L Dg enc) guards)
    (pairAccepts Dg (friMask s d l L Dg enc) (friAccepts' s d l L Dg enc hdom (Salt := Salt)))
    (pairAccepts_friAccepts'_imp s d l L Dg enc hdom) B Q queryBound)
  rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hbad
  · exact hbad
  · exact hbad

end Glue

/-! ## Non-vacuity: a concrete FRI parameter set -/

namespace NonVacuous

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private instance : NonBinaryField (ZMod 17) where
  toField := inferInstance
  char_neq_2 := by decide

private def root : (ZMod 17)ˣ := ⟨4, 13, by decide, by decide⟩

/-- A smooth coset domain of size `2^2` in `ZMod 17`. -/
private def domain : SmoothCosetFftDomain 2 (ZMod 17) where
  subgroupDomain :=
    { toFun := fun i ↦ root ^ i.toAdd.val
      map_one' := by decide
      map_mul' := by decide }
  subgroupDomain_inj := by decide
  cosetGenerator := ⟨3, 6, by decide, by decide⟩

private def sched2 : Fin 2 → ℕ+ := fun _ ↦ 1

noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

/-- Uniform sampling of every FRI challenge (finite and nonempty, FriPort `friChal_finite`/`friChal_nonempty`). -/
noncomputable local instance instSampChal :
    ∀ j, SampleableType ((pSpec 1 (ω := domain) sched2 1).Challenge j) := fun j =>
  haveI := friChal_nonempty (ω := domain) sched2 1 j
  haveI := friChal_finite (ω := domain) sched2 1 j
  haveI := Fintype.ofFinite ((pSpec 1 (ω := domain) sched2 1).Challenge j)
  SampleableType.ofFintype _

private theorem hdom2 : 2 ^ (∑ j, (sched2 j).val) * (1 : ℕ+).val ≤ 2 ^ 2 := by
  simp [sched2]

noncomputable local instance instDecStmt : DecidableEq (FriStmt (ω := domain) sched2) := Classical.decEq _

/-- `fri_hclear` at `F = ZMod 17`, `n = 2`, `k = 1`, `s = (1, 1)`, `d = 1`, `l = 1`, digests `ZMod 17`,
`Op = Unit`, `Salt = W = Unit`: every instance argument is built; the hypothesis is the genuine `hclear`. -/
theorem nonvac_fri_hclear (θ δ : ℝ) :
    ∀ (guards : GuardSchedule (FriStmt (ω := domain) sched2 × Unit) PUnit
        (compiledRoundsK (ZMod 17) Unit (friMask (ω := domain) sched2 1 1
          (perfectLeaves (ω := domain) sched2) (ZMod 17) (Function.Embedding.refl (ZMod 17)))))
      (B : SingleSaltAdversary (FriStmt (ω := domain) sched2) Unit Unit
        (pairedRoundsK (ZMod 17) (friMask (ω := domain) sched2 1 1 (perfectLeaves (ω := domain) sched2)
          (ZMod 17) (Function.Embedding.refl (ZMod 17))))) (Q : ℕ),
      (∀ phase ∈ support (randomOracleLoggedRun B.withQueryLog ∅),
        (freshKeysOfLog phase.1.2).card ≤ Q) →
      Pr{let j ← randomOracleLoggedRun (singleSaltAcceptedExecution
          (pairedRoundsK (ZMod 17) (friMask (ω := domain) sched2 1 1 (perfectLeaves (ω := domain) sched2)
            (ZMod 17) (Function.Embedding.refl (ZMod 17))))
          (pairGuards (ZMod 17) Unit (friMask (ω := domain) sched2 1 1 (perfectLeaves (ω := domain) sched2)
            (ZMod 17) (Function.Embedding.refl (ZMod 17))) guards)
          (pairAccepts (ZMod 17) (friMask (ω := domain) sched2 1 1 (perfectLeaves (ω := domain) sched2)
            (ZMod 17) (Function.Embedding.refl (ZMod 17)))
            (friAccepts' (ω := domain) sched2 1 1 (perfectLeaves (ω := domain) sched2) (ZMod 17)
              (Function.Embedding.refl (ZMod 17)) hdom2 (Salt := Unit))) B) ∅}[
        match j.1.1.1 with
        | none => False
        | some (z, _, _) => z.1 ∉ {stmt | initialOracle sched2 stmt ∈ proximityLanguage sched2 1 δ}] ≤
      friEpsFS (ω := domain) sched2 1 1 θ δ Q :=
  fun guards B Q hQ => by
    have h := fri_hclear (ω := domain) sched2 1 1 (perfectLeaves (ω := domain) sched2)
      (ZMod 17) (Function.Embedding.refl (ZMod 17)) hdom2 θ δ (W := Unit) (Salt := Unit) Unit
      guards B Q hQ
    refine le_trans (prEvent_mono _ _ _ ?_) h
    rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hb
    · exact hb
    · exact hb

end NonVacuous

end NockvmE2E.Merkle.Fri
