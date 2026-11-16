/-
Merkle (B) file 10: `merkle_singleSalt_soundness` and its non-vacuity witness.
-/
import NockvmE2E.Merkle.SoundnessCoupling
import NockvmE2E.Merkle.FsBoundSupport

open OracleComp OracleSpec MerkleTreeMultiExtractability
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle

open Reduction Good SoundnessWorld SoundnessCoupling BadBound

variable {Y : Type} [Finite Y] [DecidableEq Y] [SampleableType Y] [Inhabited Y]
  {Op : Type} [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]

/-- **Merkle single-salt soundness.** Hypotheses beyond the plain statement: `hpos` (at least one merkle
round), `hFS` on `verifiedFS A` (QD's support-wise query bound H1′ is derived from it),
`hterm` (verifier hash-query overhead). -/
theorem merkle_singleSalt_soundness (ms : MRounds Y) (hpos : 0 < (merkleSkels ms).length)
    (decode : Op → OpenAll Y (merkleSkels ms))
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ms)) Y)
    (guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
    (accepts : Statement × Salt → (protocol (baseRounds Y ms)).tree.ExecutionPath → Bool)
    (localAccepts : Statement × Salt → (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath → Bool)
    (hlocal : QueryOnly ms decode accepts localAccepts) (L : Set Statement) (εFS : ℕ → ℝ≥0∞)
    (hclear : ∀ (B : SingleSaltAdversary Statement Salt (WB Y Op Query Statement Salt W ms)
        (pairedRoundsK Y ms)) (Q : ℕ),
      (∀ phase ∈ support (randomOracleLoggedRun B.withQueryLog ∅), (freshKeysOfLog phase.1.2).card ≤ Q) →
      Pr{let j ← randomOracleLoggedRun (singleSaltAcceptedExecution (pairedRoundsK Y ms)
          (pairGuards Y Op ms guards) (pairAccepts Y ms accepts) B) ∅}[
        match j.1.1.1 with | none => False | some (z, _, _) => z.1 ∉ L] ≤ εFS Q)
    (A : SuccinctAdversaryK Y Op Query Statement Salt W ms) (Q_FS Q_H V P : ℕ)
    (hFS : FsBound (Q := Query) (Y := Y) (∅ : (ofFn (KC Y Op Statement Salt ms)).QueryCache) Q_FS
      (verifiedFS guards A))
    (hH : IsQueryBoundP A (isHashQuery (Q := Query) (Y := Y) (Rc := KC Y Op Statement Salt ms)) Q_H)
    (hterm : ∀ (roots : List Y) (h : roots.length = (merkleSkels ms).length) (op : Op)
      (logs : Fin (merkleSkels ms).length → MerkleTreeExtractor.QueryLog Query Y),
      claimsQueryCount (mkClaims (merkleSkels ms) roots h (decode op) logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels ms)).nodeBudget tag ≤ P) :
    Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK guards
        (merkleCheck (merkleSkels ms) model decode) localAccepts A) ∅}[
      match j.1.1 with | none => False | some (z, _, _) => z.1 ∉ L] ≤
    εFS Q_FS + (multiCheckpointROMErrorNumerator (((merkleSkels ms).length * (Q_FS + 1)) * P)
      ((merkleSkels ms).length * (Q_FS + 1)) V Q_H : ℝ≥0∞) * (Nat.card Y : ℝ≥0∞)⁻¹ := by
  let : Inhabited (Fin (merkleSkels ms).length) := ⟨⟨0, hpos⟩⟩
  refine (le_of_eq (pr_real_eq hpos guards model decode A localAccepts
    ((merkleSkels ms).length * (Q_FS + 1)) L)).trans ?_
  refine (pr_world_split hpos guards model decode A default accepts localAccepts hlocal _ L).trans
    (add_le_add ?_ (pr_bad_le hpos guards model decode A Q_FS Q_H V P (hQ_instrA guards A Q_H hH)
      (fsBound_obsR hFS _) hterm hconfig))
  rw [pr_instrA_eq_B (NonVacuous.extTree ms model.view default) guards A
    (goodB L accepts (NonVacuous.extTree ms model.view default))]
  exact (pr_B_le_qd _ guards A accepts L).trans
    (hclear _ Q_FS (reductionB₂_queryBound _ guards A Q_FS (FsBoundSupport.supportFS_of_FsBound hFS)))

/-! ## Non-vacuity: one merkle round, `Bool` digests -/

section NonVacuity

/-- a word of one `Bool` leaf -/
def leafEquiv : Bool ≃ BinaryTree.LeafData Bool .leaf where
  toFun b := .leaf b
  invFun x := match x with | .leaf b => b
  left_inv _ := rfl
  right_inv x := by cases x; rfl
/-- one merkle round (message `Bool`, a single leaf) -/
def ms1 : MRounds Bool :=
  [⟨openingRound Bool, .merkle .leaf Bool ⟨true⟩ (Function.Embedding.refl Bool) leafEquiv⟩]
/-- hash queries: address and children -/
abbrev Q1 := MAddress (merkleSkels ms1) × (Bool × Bool)

def model1 : MerkleTreeExtractability.NodeQueryModel Q1 (MAddress (merkleSkels ms1)) Bool :=
  ⟨⟨Prod.fst, Prod.snd⟩, Prod.mk, fun _ _ => rfl, fun _ _ => rfl⟩
/-- guards that always pass -/
def guards1 : GuardSchedule (Unit × Unit) PUnit (compiledRoundsK Bool (OpenAll Bool (merkleSkels ms1)) ms1) :=
  (fun _ _ _ => true, fun _ _ _ => (fun _ _ _ => true, fun _ _ _ => PUnit.unit))
/-- Every hypothesis of `merkle_singleSalt_soundness` is dischargeable on `ms1` (here even `hclear`,
with the trivial `εFS = 1`), for the adversary that outputs nothing. -/
theorem merkle_singleSalt_soundness_nonvacuous (L : Set Unit) : True := by
  have hp : 0 < (merkleSkels ms1).length := by decide
  have h1 : ∀ j : Fin (merkleSkels ms1).length, j = ⟨0, hp⟩ := fun j =>
    Fin.ext (by have := j.2; simp [ms1, merkleSkels] at this; omega)
  have _ := merkle_singleSalt_soundness (Query := Q1) (W := Unit) ms1 hp id model1 guards1
    (fun _ _ => false) (fun _ _ => false) (fun _ _ _ _ h => by cases h) L (fun _ => 1)
    (fun _ _ _ => prEvent_le_one _) (pure none) 0 0 0 ((mconfig (merkleSkels ms1)).nodeBudget ⟨0, hp⟩)
    (FsBound.pure _ _ _)
    trivial
    (fun roots h op logs => by
      have h0 : ∀ j, (OpenAll.get (merkleSkels ms1) op j).proof.queryCount = 0 := fun j =>
        Nat.le_zero.mp ((OpenAll.get _ op j).proof.queryCount_le_leafCount_sub_one.trans
          (by rw [h1 j]; rfl))
      simp only [claimsQueryCount, mkClaims, List.map_ofFn, Function.comp_def, OpeningClaim.queryCount,
        id_eq]
      exact (List.sum_eq_zero fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx; exact h0 j).le)
    (fun tag => by rw [h1 tag])
  trivial

end NonVacuity

end NockvmE2E.Merkle
