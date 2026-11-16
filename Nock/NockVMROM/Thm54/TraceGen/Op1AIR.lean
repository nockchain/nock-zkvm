/-
  Nock/NockVMROM/Thm54/TraceGen/Op1AIR.lean

  Phase 1 of the trace-generator track (compute-AIR vertical slice for `OP_1`).

  A fresh, directly-built compute row for the ROM program `*[subject [1 result]] = result`
  over `F = ZMod 97`, and the *theorem* — not an `#eval` — that every constraint of the reified
  per-row compute AIR `computeAIR` evaluates to zero at the honest witness for that row.  The
  discharge is `computeAIR_sound.mpr ⟨op1_rapcomp, op1_z_ne_zero⟩`: a genuine satisfaction of the
  full per-row compute RAP `RAPcomp`, so `native_decide` is not used anywhere.

  This is the row-local compute chip only.  Assembling the row into a full
  `HonestCommitment.Data` / `BuildableNockExecution` (with the memory forest, the census closure,
  and the IO twin) is the larger, still-open remainder of Phase 1 and the later phases.

  Concrete constants (plan day-one): `z = 8`, `α = 4`, `a = b = c = 0`, `q = 97 = ringChar (ZMod 97)`,
  subject `.atom 0`, formula `[1 5] =.cell (.atom 1) (.atom 5)`, result `.atom 5`.
-/
import Nock.AIR
import Nock.GlobalCarryRecognizer
import Nock.FieldEmbedding
import Nock.NockVMROM.Thm54.TraceGen.Encode
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op1

open Nock Nock.ComputeTable Nock.Reified Nock.GlobalCarryRecognizer
open Nock.NockVMROM.Thm54.TraceGen

/-- `ZMod 97` is a field. -/
instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The Phase-1 slice field: the paper's `ExactConfig` uses `eDeg = 1`, so a prime field suffices. -/
abbrev F : Type := ZMod 97

/-! ## The fresh ROM program and its one honest compute row -/

/-- Subject `0`. -/
def subject : Noun := .atom 0
/-- Formula `[1 5]` (`OP_1`, constant): `*[s [1 b]] = b`. -/
def formula : Noun := .cell (.atom 1) (.atom 5)
/-- Result `5`. -/
def result : Noun := .atom 5

/-- `*[0 [1 5]] = 5` under the capstone evaluator `evalFBy q`; `q = 97`, one
    unit of fuel.  The `OP_1` clause returns the formula tail regardless of subject, so this is
    literally `rfl` against `FieldEmbedding.evalFBy`. -/
theorem op1_evalFBy : FieldEmbedding.evalFBy 97 1 subject formula = some result := rfl

/-- The RAP inputs `(α, z, a, b, c)`: `z = 8`, `α = 4`, equality RLC off. -/
def op1Inp : Inputs F := { α := 4, z := 8, a := 0, b := 0, c := 0 }

/-- The `OP_1` formula head fingerprint `enc z 1` (an atom: `(z, 0, 1)`). -/
def fh : FP F := encC op1Inp.z (.atom 1)
/-- The formula tail fingerprint `enc z 5` (an atom: `(z, 0, 5)`), which is also the evaluation. -/
def ft : FP F := encC op1Inp.z (.atom 5)

/-- The public label + witness `x^comp`, `x_out^comp`, `W_comp` of the one `OP_1` row: the constant opcode fills the three subformula slots with `⊥ ≡ 0`, and
    the only live memory record is `mem_record₁ = (f, f_t, 3, ln_prev·α)`. -/
def op1Pub : Pub F where
  state := .s1
  s := encC op1Inp.z subject
  f := encC op1Inp.z formula
  e := encC op1Inp.z result
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := op1Inp.α
  mr1 := ⟨encC op1Inp.z formula, ft, 3, 1 * op1Inp.α⟩
  mr2 := MemRec.zero
  mr3 := MemRec.zero

/-- The formula-decomposition columns: `f_h` the `cons`-preimage head,
    `f_t` the tail; the deeper openings are unused by `OP_1`. -/
def op1Dec : Dec F where
  f_h := fh
  f_t := ft
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

/-- The auxiliary gate columns `(cons_inv, inv_gen)`; `OP_1` uses neither. -/
def op1Ex : Extra F := ⟨0, 0⟩

/-! ## The row satisfies the per-row compute RAP -/

/-- The seed is nonzero. -/
theorem op1_z_ne_zero : op1Inp.z ≠ 0 := by decide

/-- **The `OP_1` row satisfies `RAP_comp`**: the formula decomposes as a
    `cons` of head/tail, `mem_record₁` is the paper's `(f, f_t, 3, ln_prev·α)`, the State-Variables
    block is one-hot at `OP_1` pinning the head to the atom `(z, 0, 1)`, and both the memory block and the evaluation block hold. -/
theorem op1_rapcomp : RAPcomp op1Inp op1Pub op1Dec op1Ex := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- pub.f = FP.cons z f_h f_t
    show encC op1Inp.z formula
        = FP.cons op1Inp.z (encC op1Inp.z (.atom 1)) (encC op1Inp.z (.atom 5))
    simp only [encC_eq]
    exact enc_cons op1_z_ne_zero (.atom 1) (.atom 5)
  · -- mr1 = (f, f_t, 3, ln_prev·α)
    rfl
  ·
    have hsize : op1Dec.f_h.size = op1Inp.z := by
      show (encC op1Inp.z (Noun.atom 1)).size = op1Inp.z
      rw [encC_eq, enc_atom]; simp
    have hdyck : op1Dec.f_h.dyck = 0 := by
      show (encC op1Inp.z (Noun.atom 1)).dyck = 0
      rw [encC_eq, enc_atom]; simp
    have hleaf : op1Dec.f_h.leaf = ((1 : ℕ) : F) := by
      show (encC op1Inp.z (Noun.atom 1)).leaf = _
      rw [encC_eq, enc_atom]; simp
    refine ⟨opSel_boolean _, opSel_oneHot _, ?_, ?_, ?_⟩
    · show (1 - opSel op1Pub.state State.cons) * op1Dec.f_h.size
          = op1Inp.z * sum09 (opSel op1Pub.state)
      rw [hsize]
      simp [opcons_val, sum09_val, show op1Pub.state = State.s1 from rfl]
    · show (1 - opSel op1Pub.state State.cons) * op1Dec.f_h.dyck
          + opSel op1Pub.state State.cons * (1 - op1Dec.f_h.dyck * op1Ex.consInv) = 0
      rw [hdyck]
      simp [opcons_val, show op1Pub.state = State.s1 from rfl]
    · show (1 - opSel op1Pub.state State.cons) * op1Dec.f_h.leaf
          = sumJ (opSel op1Pub.state)
      rw [hleaf]
      simp [opcons_val, sumJ_val, show op1Pub.state = State.s1 from rfl, State.toNat]
  · -- memBlk (OP_1): mr2 = mr3 = 0, ln = ln_prev·α
    exact ⟨rfl, rfl, (one_mul _).symm⟩
  · -- evalR (OP_1): e = f_t and the three subformula slots are ⊥
    exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **Phase-1 deliverable (theorem, not `#eval`).**  Every constraint of the reified per-row
    compute AIR `computeAIR` evaluates to
    zero on the honest environment of the fresh `OP_1` row, via the tight biconditional
    `computeAIR_sound` applied to `op1_rapcomp`. -/
theorem op1_computeAIR_zero :
    ∀ c ∈ computeAIR.constraints,
      c.expr.eval (computeEnvFull op1Inp (opSel op1Pub.state) op1Pub op1Dec op1Ex) = 0 :=
  (computeAIR_sound op1Inp op1Pub op1Dec op1Ex).mpr ⟨op1_rapcomp, op1_z_ne_zero⟩

end Nock.NockVMROM.Thm54.TraceGen.Op1
