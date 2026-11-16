/-
  NockvmE2E/Emit/ChipsJ9AL.lean   (a)

  The J-9 AL ALU chip `aluChipJ9` (upstream `AluSZChipJ9.aluTemplateSZ`, width 196 = 94 base + 18 round-1 𝕂 + 16 round-2 𝕂, three limbs each)
  as an emitter spec with kernel-checked `decodeDag (emitDag aluSpec) = some aluSpec.gates`.

  Challenges (`chalsALJ8E`, CheckJ9AL.lean:76-79): leaves `j ∈ [40,106)` are `Re/Im y^((j-40)/2)`, the powers `t ≤ 32` of the limb coin
  `y = (χ17, χ18)`; every other leaf is `chalsAJ8ZE` = the atom map `fA`.  The emitter slot map is
  `fL j = if 40 ≤ j < 106 then 41 + (j-40) else fA j` (slots `41..106`, behind the 22 γ′ slots `19..40` of `jDers`).
  `jDers` itself is NOT changed (every J-8 / J-9 A literal and proof sha depends on it); the ALU gets `aluDers := jDers ++ yDers`.
  Fixed columns (kind 1): masks at 0, 1 and the preg layout `sP, pId, pOp` at 2, 3, 4 (values are a function of the primitive table;
  the verifier/prover side supplies them, not this spec).
-/
import NockvmE2E.Emit.Chips
import NockvmE2E.Exec.J8Chips
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9

set_option autoImplicit false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace Nock.Emit

open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle

/-- The ALU slot map: `chalsALJ8E` (`CheckJ9AL.lean:76-79`) → the document's slots. -/
def fL (j : ℕ) : ℕ := if 40 ≤ j ∧ j < 106 then 41 + (j - 40) else fA j

/-- The derived-slot table of the limb-coin powers `y^t`, `t ≤ 32`, `y = (χ17, χ18)`: slots `41 + 2t` (Re) and `42 + 2t` (Im). -/
def yDers : Array NockvmE2E.Exec.Aux.Der :=
  ((List.range 33).flatMap fun (t : ℕ) =>
    [(⟨41 + 2 * t, 17, 18, t, true⟩ : NockvmE2E.Exec.Aux.Der), ⟨42 + 2 * t, 17, 18, t, false⟩]).toArray

/-- The ALU's `ders` argument of `verifierChipT`: the J-8 γ′ slots (unchanged) then the y-power slots. -/
def aluDers : Array NockvmE2E.Exec.Aux.Der := NockvmE2E.Exec.J8Chips.jDers ++ yDers

def aluTemplate : ChipTemplate Gl := AluSZChipJ9.aluTemplateSZ δ

def aluSpec : TSpec := (TSpec.ofTemplate aluTemplate).rename fL id id

def emit_alu := emitDag aluSpec

/-- Physical round of local column `c` (`colR`): base `0..93` round 0, round-1 𝕂 columns `94..147`, round-2 `148..195`. -/
def aluColR (c : ℕ) : ℕ := if c < 94 then 0 else if c < 148 then 1 else 2

theorem aluSpec_shape : aluSpec.baseCols = [94, 0, 0] ∧ aluSpec.extCols = [0, 18, 16] ∧ aluSpec.rounds = 3 ∧
    aluSpec.baseCols.sum + 3 * aluSpec.extCols.sum = 196 ∧ 94 + 3 * 18 = 148 ∧ 148 + 3 * 16 = 196 ∧
    aluSpec.base.length = 180 ∧ aluSpec.mixed.length = 78 := by decide +kernel

theorem aluColR_shape : aluColR 0 = 0 ∧ aluColR 93 = 0 ∧ aluColR 94 = 1 ∧ aluColR 147 = 1 ∧ aluColR 148 = 2 ∧
    aluColR 195 = 2 := by decide

/-- The five fixed (kind-1) columns of the ALU: masks `0, 1`, preg layout `sP, pId, pOp = 2, 3, 4`
(`AluSZChipJ9.sP/pId/pOp`). -/
theorem alu_pre_cols : [AluSZChipJ9.isFT, AluSZChipJ9.isLT, AluSZChipJ9.sP, AluSZChipJ9.pId, AluSZChipJ9.pOp] = [0, 1, 2, 3, 4] := rfl

theorem alu_ders_shape : yDers.size = 66 ∧ aluDers.size = 88 ∧ NockvmE2E.Exec.J8Chips.jDers.size = 22 := by decide +kernel

theorem fL_shape : fL 39 = 39 ∧ fL 40 = 41 ∧ fL 41 = 42 ∧ fL 105 = 106 ∧ fL 106 = 106 ∧ fL 2 = 17 ∧ fL 3 = 18 ∧
    fL 37 = 2 ∧ fL 38 = 3 ∧ fL 0 = 0 ∧ fL 11 = 19 := by decide +kernel

theorem emit_alu_eq : decodeDag emit_alu = some aluSpec.gates := by decide +kernel

end Nock.Emit

#print axioms Nock.Emit.emit_alu_eq
#print axioms Nock.Emit.aluSpec_shape
#print axioms Nock.Emit.aluColR_shape
#print axioms Nock.Emit.alu_pre_cols
#print axioms Nock.Emit.alu_ders_shape
#print axioms Nock.Emit.fL_shape
