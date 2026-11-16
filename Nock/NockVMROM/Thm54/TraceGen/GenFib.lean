/-
  Nock/NockVMROM/Thm54/TraceGen/GenFib.lean

  Peano encoding of n, so decrement is an axis read rather than a growth
  theorem: `1 ↦ 0`, `2 ↦ [0 0]`, `3 ↦ [0 [0 0]]`, `4 ↦ [0 [0 [0 0]]]`.
  Halt vs decompose is OP3 (atom vs cell), matching the paper's
  `S_leaf = {halt}` / `fanout(decompose) = 2` (`:779`).

  Opcodes the 2×2 matmul does not use: OP2, OP3, OP8.  Matmul recurses
  with OP7+OP9 (`GenMatmul.lean`).

  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenProgramKit
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSize
import Nock.NockVMROM.Thm54.TraceGen.GenGuardedRom
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded
import Nock.NockVMROM.Thm54.TraceGen.GenLeafWindow
import Nock.FieldEmbedding
import Nock.NockVMROM.Thm54.CensusExtraClosure

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open ComputeTable

variable {K : Type} [Field K]

/-! ## Formula fragments the matmul kit does not name -/

/-- `[2 [b c]]` -/
def op2 (b c : Noun) : Noun :=
  .cell (.atom 2) (.cell b c)

/-- `[3 t]` -/
def op3 (t : Noun) : Noun :=
  .cell (.atom 3) t

/-- `[8 [b c]]` -/
def op8 (b c : Noun) : Noun :=
  .cell (.atom 8) (.cell b c)

/-! ## Peano subjects — paper clauses 1–3 -/

/-- n = 1, halt, F = 1. -/
def fibN1 : Noun := .atom 0
/-- n = 2, halt, F = 1. -/
def fibN2 : Noun := .cell (.atom 0) (.atom 0)
/-- n = 3, decompose, F = 2. -/
def fibN3 : Noun := .cell (.atom 0) fibN2
/-- n = 4, decompose, F = 3.  The compiled program. -/
def fibN4 : Noun := .cell (.atom 0) fibN3

/-- Halt result F = 1 (`:738`). -/
def fibHalt : Noun := op1 1
def fibF1 : Noun := .atom 1
def fibF2 : Noun := .atom 2
def fibF3 : Noun := .atom 3

def fibRecSample : Noun :=
  .cell (op0 2) (op0 7)

/-- `*[ [body, n-1]  body ]` via OP2 -/
def fibRec : Noun :=
  op2 fibRecSample (op0 2)

/-- `1 + fib(n-1)` — valid for n = 3, 4 by clauses 2–3. -/
def fibInc : Noun :=
  op4 fibRec

/-- Inner test: is n-1 an atom? (n = 2 vs n ≥ 3). -/
def fibInner : Noun :=
  op6 (op3 (op0 7)) fibInc fibHalt

def fibBody : Noun :=
  op6 (op3 (op0 3)) fibInner fibHalt

/-- `[8 [1 body] body]` — pin then evaluate -/
def fibFormula : Noun :=
  op8 (quote fibBody) fibBody

def fibSubject : Noun := fibN4
def fibResult : Noun := fibF3


def fibPushed (n : Noun) : Noun := .cell fibBody n

theorem fib_slot2 (n : Noun) :
    Noun.slot 2 (fibPushed n) = some fibBody := by
  simp [fibPushed, Noun.slot]

theorem fib_slot3 (n : Noun) :
    Noun.slot 3 (fibPushed n) = some n := by
  simp [fibPushed, Noun.slot]

theorem fib_slot7 (rest : Noun) :
    Noun.slot 7 (fibPushed (.cell (.atom 0) rest)) = some rest := by
  simp [fibPushed, Noun.slot]

theorem fib_wut_n1 : Noun.wut fibN1 = .atom 1 := rfl
theorem fib_wut_n2 : Noun.wut fibN2 = .atom 0 := rfl
theorem fib_wut_n3 : Noun.wut fibN3 = .atom 0 := rfl
theorem fib_wut_n4 : Noun.wut fibN4 = .atom 0 := rfl
theorem fib_lus_1 : Noun.lus fibF1 = some fibF2 := rfl
theorem fib_lus_2 : Noun.lus fibF2 = some fibF3 := rfl

/-! ## Guarded-ROM combinators the residuals file does not carry -/

theorem evalGRom_op3 (q n : ℕ) {subject tail callResult : Noun}
    (hc : evalGRom q n subject tail = some callResult) :
    evalGRom q (n + 1) subject (op3 tail) = some (Noun.wut callResult) := by
  simp [op3, evalGRom, hc]

theorem evalGRom_op2 (q n : ℕ) {subject b c sf1 sf2 result : Noun}
    (hb : evalGRom q n subject b = some sf1)
    (hc : evalGRom q n subject c = some sf2)
    (hm : evalGRom q n sf1 sf2 = some result) :
    evalGRom q (n + 1) subject (op2 b c) = some result := by
  simp [op2, evalGRom, hb, hc, hm]

theorem evalGRom_op8 (q n : ℕ) {subject b c sb result : Noun}
    (hb : evalGRom q n subject b = some sb)
    (hc : evalGRom q n (.cell sb subject) c = some result) :
    evalGRom q (n + 1) subject (op8 b c) = some result := by
  simp [op8, evalGRom, hb, hc]

/-! ## Shared leaves

`OP_1` halt and the two axis reads. -/

def fibHaltTree (s : Noun) : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp1 s fibHalt (.atom 1) (.atom 1))
    [⟨fibHalt, .atom 1, 3, 0⟩]) []

def fibOp0Tree (s : Noun) (ax : ℕ) (r : Noun) : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp0 s (op0 ax) (.atom 0) (.atom ax) r ax)
    [⟨op0 ax, .atom ax, 3, 0⟩, ⟨s, r, ax, 0⟩]) []

def fibOp3Tree (s tail r : Noun) (call : NTree (GenComputeRow K)) :
    NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp3 s (op3 tail) (.atom 3) tail s tail r (Noun.wut r))
    [⟨op3 tail, tail, 3, 0⟩]) [call]

def fibOp6Tree (s b c d vb takenF result : Noun)
    (condT takenT : NTree (GenComputeRow K)) :
    NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp6 s (op6 b c d) (.atom 6) (.cell b (.cell c d))
      b (.cell c d) c d vb takenF result)
    [⟨op6 b c d, .cell b (.cell c d), 3, 0⟩,
     ⟨.cell b (.cell c d), b, 2, 0⟩,
     ⟨.cell c d, c, 2, 0⟩])
    [condT, takenT]

theorem fib_gen_halt (n : ℕ) (s : Noun) :
    genComputeSkeleton (K := K) (n + 1) s fibHalt =
      .ok (fibHaltTree s, fibF1) :=
  gen_op1 n s 1

theorem fib_gen_op0 (n : ℕ) {s : Noun} {ax : ℕ} {r : Noun}
    (h : Noun.slot ax s = some r) :
    genComputeSkeleton (K := K) (n + 1) s (op0 ax) =
      .ok (fibOp0Tree s ax r, r) :=
  gen_op0 n h

/-! ## Body at n = 1 (atom) — cond = 1, else halt -/

def fibBodyN1Tree : NTree (GenComputeRow K) :=
  fibOp6Tree (fibPushed fibN1) (op3 (op0 3)) fibInner fibHalt (.atom 1) fibHalt fibF1
    (fibOp3Tree (fibPushed fibN1) (op0 3) fibN1 (fibOp0Tree (fibPushed fibN1) 3 fibN1))
    (fibHaltTree (fibPushed fibN1))

theorem fib_gen_body_n1 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 3) (fibPushed fibN1) fibBody =
      .ok (fibBodyN1Tree, fibF1) := by
  have h0 := fib_gen_op0 (K := K) n (fib_slot3 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN1)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInner) h3 h1
  simpa [fibBody, fibBodyN1Tree, fibOp6Tree, fibOp3Tree, fibOp0Tree, fibHaltTree,
    fib_wut_n1, op3, op6, fibInner, fibHalt] using h6

/-! ## Body at n = 2 — outer then, inner else halt -/

def fibBodyN2Tree : NTree (GenComputeRow K) :=
  fibOp6Tree (fibPushed fibN2) (op3 (op0 3)) fibInner fibHalt (.atom 0) fibInner fibF1
    (fibOp3Tree (fibPushed fibN2) (op0 3) fibN2 (fibOp0Tree (fibPushed fibN2) 3 fibN2))
    (fibOp6Tree (fibPushed fibN2) (op3 (op0 7)) fibInc fibHalt (.atom 1) fibHalt fibF1
      (fibOp3Tree (fibPushed fibN2) (op0 7) fibN1 (fibOp0Tree (fibPushed fibN2) 7 fibN1))
      (fibHaltTree (fibPushed fibN2)))

theorem fib_gen_inner_n2 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 3) (fibPushed fibN2) fibInner =
      .ok (fibOp6Tree (fibPushed fibN2) (op3 (op0 7)) fibInc fibHalt (.atom 1)
        fibHalt fibF1
        (fibOp3Tree (fibPushed fibN2) (op0 7) fibN1
          (fibOp0Tree (fibPushed fibN2) 7 fibN1))
        (fibHaltTree (fibPushed fibN2)), fibF1) := by
  have h0 := fib_gen_op0 (K := K) n (fib_slot7 fibN1)
  have h3 := gen_op3 (K := K) (n + 1) h0
  have h1 := fib_gen_halt (K := K) (n + 1) (fibPushed fibN2)
  have h6 := gen_op6_one (K := K) (n + 2) (c := fibInc) h3 h1
  simpa [fibInner, fibOp6Tree, fibOp3Tree, fibOp0Tree, fibHaltTree,
    fib_wut_n1, op3, op6, fibInc, fibHalt, fibN2, fibN1] using h6

theorem fib_gen_body_n2 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 4) (fibPushed fibN2) fibBody =
      .ok (fibBodyN2Tree, fibF1) := by
  have h0 := fib_gen_op0 (K := K) (n + 1) (fib_slot3 fibN2)
  have h3 := gen_op3 (K := K) (n + 2) h0
  have hI := fib_gen_inner_n2 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 3) (d := fibHalt) h3 hI
  simpa [fibBody, fibBodyN2Tree, fibOp6Tree, fibOp3Tree, fibOp0Tree,
    fib_wut_n2, op3, op6, fibInner, fibHalt, fibN2, fibN1] using h6

/-! ## Body at n = 3 — recurse on n = 2, increment. Paper clause 2 (`:739`) -/

def fibConsTree (s lh lt tail lRes rRes : Noun)
    (lT rT : NTree (GenComputeRow K)) : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelCons s (.cell lh lt) tail lRes rRes)
    [⟨.cell (.cell lh lt) tail, tail, 3, 0⟩]) [lT, rT]

def fibOp2Tree (s b c sf1 sf2 result : Noun)
    (bT cT mT : NTree (GenComputeRow K)) : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp2 s (op2 b c) (.atom 2) (.cell b c) b c sf1 sf2 result)
    [⟨op2 b c, .cell b c, 3, 0⟩, ⟨.cell b c, b, 2, 0⟩])
    [bT, cT, mT]

def fibOp4Tree (s tail callRes result : Noun)
    (callT : NTree (GenComputeRow K)) : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp4 s (op4 tail) (.atom 4) tail s tail callRes result)
    [⟨op4 tail, tail, 3, 0⟩]) [callT]

def fibRecSampleTreeOf (s rest : Noun) : NTree (GenComputeRow K) :=
  fibConsTree s (.atom 0) (.atom 2) (op0 7) fibBody rest
    (fibOp0Tree s 2 fibBody) (fibOp0Tree s 7 rest)

def fibRecTreeOf (s rest result : Noun) (bodyT : NTree (GenComputeRow K)) :
    NTree (GenComputeRow K) :=
  fibOp2Tree s fibRecSample (op0 2) (fibPushed rest) fibBody result
    (fibRecSampleTreeOf s rest) (fibOp0Tree s 2 fibBody) bodyT

def fibIncTreeOf (s rest callRes result : Noun)
    (bodyT : NTree (GenComputeRow K)) : NTree (GenComputeRow K) :=
  fibOp4Tree s fibRec callRes result (fibRecTreeOf s rest callRes bodyT)

def fibBodyN3Tree : NTree (GenComputeRow K) :=
  fibOp6Tree (fibPushed fibN3) (op3 (op0 3)) fibInner fibHalt (.atom 0) fibInner fibF2
    (fibOp3Tree (fibPushed fibN3) (op0 3) fibN3 (fibOp0Tree (fibPushed fibN3) 3 fibN3))
    (fibOp6Tree (fibPushed fibN3) (op3 (op0 7)) fibInc fibHalt (.atom 0) fibInc fibF2
      (fibOp3Tree (fibPushed fibN3) (op0 7) fibN2
        (fibOp0Tree (fibPushed fibN3) 7 fibN2))
      (fibIncTreeOf (fibPushed fibN3) fibN2 fibF1 fibF2 fibBodyN2Tree))

theorem fib_gen_recSample (n : ℕ) (rest : Noun) :
    genComputeSkeleton (K := K) (n + 2) (fibPushed (.cell (.atom 0) rest))
      fibRecSample =
      .ok (fibRecSampleTreeOf (fibPushed (.cell (.atom 0) rest)) rest,
        fibPushed rest) := by
  have h2 := fib_gen_op0 (K := K) n
    (fib_slot2 (.cell (.atom 0) rest))
  have h7 := fib_gen_op0 (K := K) n (fib_slot7 rest)
  have hc := gen_cons (K := K) (n + 1) h2 h7
  simpa [fibRecSample, fibRecSampleTreeOf, fibConsTree, fibOp0Tree, fibPushed,
    op0, fibN2, fibN3, fibN4] using hc

theorem fib_gen_rec_n3 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 5) (fibPushed fibN3) fibRec =
      .ok (fibRecTreeOf (fibPushed fibN3) fibN2 fibF1 fibBodyN2Tree, fibF1) := by
  have hs := fib_gen_recSample (K := K) (n + 2) fibN2
  have hc := fib_gen_op0 (K := K) (n + 3) (fib_slot2 fibN3)
  have hm := fib_gen_body_n2 (K := K) n
  have h2 := gen_op2 (K := K) (n + 4) hs hc hm
  simpa [fibRec, fibRecTreeOf, fibOp2Tree, fibRecSample, op2, op0, fibN3, fibN2,
    fibPushed] using h2

theorem fib_gen_inc_n3 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 6) (fibPushed fibN3) fibInc =
      .ok (fibIncTreeOf (fibPushed fibN3) fibN2 fibF1 fibF2 fibBodyN2Tree, fibF2) := by
  have hr := fib_gen_rec_n3 (K := K) n
  have h4 := gen_op4 (K := K) (n + 5) hr fib_lus_1
  simpa [fibInc, fibIncTreeOf, fibOp4Tree, op4] using h4

theorem fib_gen_inner_n3 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 7) (fibPushed fibN3) fibInner =
      .ok (fibOp6Tree (fibPushed fibN3) (op3 (op0 7)) fibInc fibHalt (.atom 0)
        fibInc fibF2
        (fibOp3Tree (fibPushed fibN3) (op0 7) fibN2
          (fibOp0Tree (fibPushed fibN3) 7 fibN2))
        (fibIncTreeOf (fibPushed fibN3) fibN2 fibF1 fibF2 fibBodyN2Tree),
        fibF2) := by
  have h0 := fib_gen_op0 (K := K) (n + 4) (fib_slot7 fibN2)
  have h3 := gen_op3 (K := K) (n + 5) h0
  have hi := fib_gen_inc_n3 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 6) (d := fibHalt) h3 hi
  simpa [fibInner, fibOp6Tree, fibOp3Tree, fibOp0Tree, fib_wut_n2, op3, op6,
    fibInc, fibHalt, fibN3, fibN2] using h6

theorem fib_gen_body_n3 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 8) (fibPushed fibN3) fibBody =
      .ok (fibBodyN3Tree, fibF2) := by
  have h0 := fib_gen_op0 (K := K) (n + 5) (fib_slot3 fibN3)
  have h3 := gen_op3 (K := K) (n + 6) h0
  have hI := fib_gen_inner_n3 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 7) (d := fibHalt) h3 hI
  simpa [fibBody, fibBodyN3Tree, fibOp6Tree, fibOp3Tree, fibOp0Tree,
    fib_wut_n3, op3, op6, fibInner, fibHalt, fibN3, fibN2] using h6

/-! ## Body at n = 4 — recurse on n = 3, increment. Paper clause 3 (`:740`) -/

def fibBodyN4Tree : NTree (GenComputeRow K) :=
  fibOp6Tree (fibPushed fibN4) (op3 (op0 3)) fibInner fibHalt (.atom 0) fibInner fibF3
    (fibOp3Tree (fibPushed fibN4) (op0 3) fibN4 (fibOp0Tree (fibPushed fibN4) 3 fibN4))
    (fibOp6Tree (fibPushed fibN4) (op3 (op0 7)) fibInc fibHalt (.atom 0) fibInc fibF3
      (fibOp3Tree (fibPushed fibN4) (op0 7) fibN3
        (fibOp0Tree (fibPushed fibN4) 7 fibN3))
      (fibIncTreeOf (fibPushed fibN4) fibN3 fibF2 fibF3 fibBodyN3Tree))

theorem fib_gen_rec_n4 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 9) (fibPushed fibN4) fibRec =
      .ok (fibRecTreeOf (fibPushed fibN4) fibN3 fibF2 fibBodyN3Tree, fibF2) := by
  have hs := fib_gen_recSample (K := K) (n + 6) fibN3
  have hc := fib_gen_op0 (K := K) (n + 7) (fib_slot2 fibN4)
  have hm := fib_gen_body_n3 (K := K) n
  have h2 := gen_op2 (K := K) (n + 8) hs hc hm
  simpa [fibRec, fibRecTreeOf, fibOp2Tree, fibRecSample, op2, op0, fibN4, fibN3,
    fibPushed] using h2

theorem fib_gen_inc_n4 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 10) (fibPushed fibN4) fibInc =
      .ok (fibIncTreeOf (fibPushed fibN4) fibN3 fibF2 fibF3 fibBodyN3Tree, fibF3) := by
  have hr := fib_gen_rec_n4 (K := K) n
  have h4 := gen_op4 (K := K) (n + 9) hr fib_lus_2
  simpa [fibInc, fibIncTreeOf, fibOp4Tree, op4, fibN4, fibN3] using h4

theorem fib_gen_inner_n4 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 11) (fibPushed fibN4) fibInner =
      .ok (fibOp6Tree (fibPushed fibN4) (op3 (op0 7)) fibInc fibHalt (.atom 0)
        fibInc fibF3
        (fibOp3Tree (fibPushed fibN4) (op0 7) fibN3
          (fibOp0Tree (fibPushed fibN4) 7 fibN3))
        (fibIncTreeOf (fibPushed fibN4) fibN3 fibF2 fibF3 fibBodyN3Tree),
        fibF3) := by
  have h0 := fib_gen_op0 (K := K) (n + 8) (fib_slot7 fibN3)
  have h3 := gen_op3 (K := K) (n + 9) h0
  have hi := fib_gen_inc_n4 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 10) (d := fibHalt) h3 hi
  simpa [fibInner, fibOp6Tree, fibOp3Tree, fibOp0Tree, fib_wut_n3, op3, op6,
    fibInc, fibHalt, fibN4, fibN3] using h6

theorem fib_gen_body_n4 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 12) (fibPushed fibN4) fibBody =
      .ok (fibBodyN4Tree, fibF3) := by
  have h0 := fib_gen_op0 (K := K) (n + 9) (fib_slot3 fibN4)
  have h3 := gen_op3 (K := K) (n + 10) h0
  have hI := fib_gen_inner_n4 (K := K) n
  have h6 := gen_op6_zero (K := K) (n + 11) (d := fibHalt) h3 hI
  simpa [fibBody, fibBodyN4Tree, fibOp6Tree, fibOp3Tree, fibOp0Tree,
    fib_wut_n4, op3, op6, fibInner, fibHalt, fibN4, fibN3] using h6

/-! ## Formula = OP8 pin + body. Clauses 1–3 and the compiled n = 4 run. -/

def fibOp8Tree (s : Noun) (bodyT : NTree (GenComputeRow K))
    (result : Noun) : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp8 s fibFormula (.atom 8) (.cell (quote fibBody) fibBody)
      (quote fibBody) fibBody fibBody result)
    [⟨fibFormula, .cell (quote fibBody) fibBody, 3, 0⟩,
     ⟨.cell (quote fibBody) fibBody, quote fibBody, 2, 0⟩])
    [.node (skelNode (genSkelOp1 s (quote fibBody) fibBody (.atom 1))
        [⟨quote fibBody, fibBody, 3, 0⟩]) [], bodyT]

theorem fib_gen_formula (n : ℕ) {subj result : Noun}
    {bodyT : NTree (GenComputeRow K)}
    (hbody : genComputeSkeleton (K := K) (n + 1) (fibPushed subj) fibBody =
      .ok (bodyT, result)) :
    genComputeSkeleton (K := K) (n + 2) subj fibFormula =
      .ok (fibOp8Tree subj bodyT result, result) := by
  have hq := gen_quote (K := K) n subj fibBody
  have h8 := gen_op8 (K := K) (n + 1) hq hbody
  simpa [fibFormula, fibOp8Tree, op8, quote] using h8

theorem fib_gen_n1 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 5) fibN1 fibFormula =
      .ok (fibOp8Tree fibN1 fibBodyN1Tree fibF1, fibF1) :=
  fib_gen_formula (n + 3) (fib_gen_body_n1 (n + 1))

theorem fib_gen_n2 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 6) fibN2 fibFormula =
      .ok (fibOp8Tree fibN2 fibBodyN2Tree fibF1, fibF1) :=
  fib_gen_formula (n + 4) (fib_gen_body_n2 (n + 1))

theorem fib_gen_n3 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 10) fibN3 fibFormula =
      .ok (fibOp8Tree fibN3 fibBodyN3Tree fibF2, fibF2) :=
  fib_gen_formula (n + 8) (fib_gen_body_n3 (n + 1))

theorem fib_gen_n4 (n : ℕ) :
    genComputeSkeleton (K := K) (n + 14) fibN4 fibFormula =
      .ok (fibOp8Tree fibN4 fibBodyN4Tree fibF3, fibF3) :=
  fib_gen_formula (n + 12) (fib_gen_body_n4 (n + 1))

/-- The compiled program: n = 4, F = 3. -/
theorem fibTree_gen :
    genComputeSkeleton (K := K) 32 fibSubject fibFormula =
      .ok (fibOp8Tree fibN4 fibBodyN4Tree fibF3, fibResult) :=
  fib_gen_n4 (K := K) 18

def fibTree : NTree (GenComputeRow K) :=
  fibOp8Tree fibN4 fibBodyN4Tree fibF3

theorem fibTree_eq :
    genComputeSkeleton (K := K) 32 fibSubject fibFormula =
      .ok (fibTree, fibResult) :=
  fibTree_gen

/-! ## `evalN` / `evalGRom` at the four paper clauses -/

theorem fib_evalN_n1 : Nock.evalN 32 fibN1 fibFormula = some fibF1 :=
  genComputeSkeleton_evalN (fib_gen_n1 (K := ℚ) 27)

theorem fib_evalN_n2 : Nock.evalN 32 fibN2 fibFormula = some fibF1 :=
  genComputeSkeleton_evalN (fib_gen_n2 (K := ℚ) 26)

theorem fib_evalN_n3 : Nock.evalN 32 fibN3 fibFormula = some fibF2 :=
  genComputeSkeleton_evalN (fib_gen_n3 (K := ℚ) 22)

theorem fib_evalN_n4 : Nock.evalN 32 fibSubject fibFormula = some fibResult :=
  genComputeSkeleton_evalN (fibTree_eq (K := ℚ))

/-! ## Program-text leaf numerals (not a growth theorem) -/

theorem fibHalt_leaves : fibHalt.leaves = 2 := by
  simp [fibHalt, op1, cell_leaves, atom_leaves]

theorem fibRecSample_leaves : fibRecSample.leaves = 4 := by
  simp [fibRecSample, op0, cell_leaves, atom_leaves]

theorem fibRec_leaves : fibRec.leaves = 7 := by
  simp [fibRec, op2, fibRecSample, op0, cell_leaves, atom_leaves]

theorem fibInc_leaves : fibInc.leaves = 8 := by
  simp [fibInc, op4, fibRec, op2, fibRecSample, op0, cell_leaves, atom_leaves]

theorem fibInner_leaves : fibInner.leaves = 14 := by
  simp [fibInner, op6, op3, op0, fibInc, op4, fibRec, op2, fibRecSample,
    fibHalt, op1, cell_leaves, atom_leaves]

theorem fibBody_leaves : fibBody.leaves = 20 := by
  simp [fibBody, op6, op3, op0, fibInner, op4, fibInc, fibRec, op2,
    fibRecSample, fibHalt, op1, cell_leaves, atom_leaves]

theorem fibFormula_leaves : fibFormula.leaves = 42 := by
  simp [fibFormula, op8, quote, fibBody, op6, op3, op0, fibInner, op4, fibInc,
    fibRec, op2, fibRecSample, fibHalt, op1, cell_leaves, atom_leaves]

theorem fibN1_leaves : fibN1.leaves = 1 := by simp [fibN1, atom_leaves]
theorem fibN2_leaves : fibN2.leaves = 2 := by simp [fibN2, cell_leaves, atom_leaves]
theorem fibN3_leaves : fibN3.leaves = 3 := by
  simp [fibN3, fibN2, cell_leaves, atom_leaves]
theorem fibN4_leaves : fibN4.leaves = 4 := by
  simp [fibN4, fibN3, fibN2, cell_leaves, atom_leaves]

theorem fibPushed_leaves (n : Noun) :
    (fibPushed n).leaves = 20 + n.leaves := by
  simp [fibPushed, cell_leaves, fibBody_leaves]

theorem fibF1_leaves : fibF1.leaves = 1 := by simp [fibF1, atom_leaves]
theorem fibF2_leaves : fibF2.leaves = 1 := by simp [fibF2, atom_leaves]
theorem fibF3_leaves : fibF3.leaves = 1 := by simp [fibF3, atom_leaves]
theorem fibResult_leaves : fibResult.leaves = 1 := fibF3_leaves
theorem fibSubject_leaves : fibSubject.leaves = 4 := by
  simp [fibSubject, fibN4_leaves]

end Nock.NockVMROM.Thm54.TraceGen
