/-
  Nock/NockVMROM/Thm54/TraceGen/GenProgramKit.lean

  **The three `genComputeSkeleton` arms the emission kit was missing: `OP_2`, `OP_3`, `OP_8`.**

  Committing a program to the generator route means producing a term of
  `genComputeSkeleton fuel subject formula =.ok (t, result)` with `t` written out, because that
  equation is every generic theorem's only link to the program (`GenSemanticData.lean:119`).

  The compositional alternative — one lemma per arm, each stating that arm's output in terms of its
  children's already-proved outputs — **already exists** in `GenMatmul.lean:752-865`, for nine of
  the eleven states: `gen_quote` / `gen_op1` (`OP_1`), `gen_op0`, `gen_op4`, `gen_op5`,
  `gen_op6_zero` / `gen_op6_one`, `gen_op7`, `gen_op9`, `gen_cons`.  This module was first
  written with all twelve arms; the nine duplicates were deleted after grepping, which is `EV` §1's
  lesson applied.

  What was genuinely absent is `OP_2`, `OP_3` and `OP_8` — the three arms the matmul program does
  not use.  They are added here in the same shape, so that a program using any of the eleven states
  now composes from one import.  `Gen.lean` is untouched and each lemma is read off its own `match`
  arm.

  Fuel discipline (the kit's, unchanged): every lemma takes its children at `n` and delivers the
  parent at `n + 1`, so a program of emission depth `d` composes at fuel `n + d`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmul
import Nock.NockVMROM.Thm54.GenericHonestCommitment

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

/-- `OP_3`: the cell test `*[a 3 b] = ?*[a b]`.  Total — no side condition on the
call's result, and the row's evaluation **is** `Noun.wut` of it. -/
theorem gen_op3 (n : ℕ) {subject tail callResult : Noun}
    {callTree : NTree (GenComputeRow K)}
    (hc : genComputeSkeleton (K := K) n subject tail = .ok (callTree, callResult)) :
    genComputeSkeleton (K := K) (n + 1) subject (.cell (.atom 3) tail)
      = .ok (.node (skelNode (genSkelOp3 subject (.cell (.atom 3) tail) (.atom 3) tail
            subject tail callResult (Noun.wut callResult))
          [⟨.cell (.atom 3) tail, tail, 3, 0⟩]) [callTree], Noun.wut callResult) := by
  simp only [genComputeSkeleton, hc]

/-- `OP_8`: push/declare `*[a 8 b c] = *[[*[a b] a] c]`.  The second call runs
against the autocons `[sb a]` of the computed helper with the original subject — the one arm whose
threaded subject is not simply a previous evaluation. -/
theorem gen_op8 (n : ℕ) {subject b c sb result : Noun}
    {bTree cTree : NTree (GenComputeRow K)}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n (.cell sb subject) c = .ok (cTree, result)) :
    genComputeSkeleton (K := K) (n + 1) subject (.cell (.atom 8) (.cell b c))
      = .ok (.node (skelNode (genSkelOp8 subject (.cell (.atom 8) (.cell b c)) (.atom 8)
            (.cell b c) b c sb result)
          [⟨.cell (.atom 8) (.cell b c), .cell b c, 3, 0⟩, ⟨.cell b c, b, 2, 0⟩])
          [bTree, cTree], result) := by
  simp only [genComputeSkeleton, hb, hc]

/-- `OP_2`: eval `*[a 2 b c] = *[*[a b] *[a c]]`.  Fan-out `3`; the third child's
subject is the computed `sf1` and its formula the computed `sf2`. -/
theorem gen_op2 (n : ℕ) {subject b c sf1 sf2 result : Noun}
    {bTree cTree mTree : NTree (GenComputeRow K)}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (cTree, sf2))
    (hm : genComputeSkeleton (K := K) n sf1 sf2 = .ok (mTree, result)) :
    genComputeSkeleton (K := K) (n + 1) subject (.cell (.atom 2) (.cell b c))
      = .ok (.node (skelNode (genSkelOp2 subject (.cell (.atom 2) (.cell b c)) (.atom 2)
            (.cell b c) b c sf1 sf2 result)
          [⟨.cell (.atom 2) (.cell b c), .cell b c, 3, 0⟩, ⟨.cell b c, b, 2, 0⟩])
          [bTree, cTree, mTree], result) := by
  simp only [genComputeSkeleton, hb, hc, hm]

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op2
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op3
#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op8
