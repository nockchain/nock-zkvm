/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluSatBlock.lean

  **Assembly**: the four gate groups (C common, A add/sub/lt, M mul, D div/mod) assembled
  into the per-call block obligations `BlockBaseSat` / `BlockIdentSat`, and into the exact `hblk` binder of
  `AluSatRows.tblP_chain` / `aluSZChipJ9_honest_sat_tblP` / `AluSatPreg.aluSZChipJ9_honest_sat_preg`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatCommon
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatA
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatM
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatD

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSatBlock

open Nock Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.Jet.Prim (PrimOp)

section Block
variable {p : ℕ} [Fact p.Prime]

/-- The op split of a served call: add/sub/lt, mul, div/mod (`dec` is excluded by `CallOK.notDec`). -/
theorem op_cases {cl : CallL} (hcl : CallOK p cl) :
    (cl.op = .add ∨ cl.op = .sub ∨ cl.op = .lt) ∨ cl.op = .mul ∨ (cl.op = .div ∨ cl.op = .mod) := by
  have := hcl.notDec
  rcases h : cl.op with _ | _ | _ | _ | _ | _ | _ <;> simp_all

/-- `gSeq` for every served op. -/
theorem gSeq_G (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl AluSZChipJ9.gSeq := by
  rcases op_cases hcl with h | h | h
  · exact AluSatA.groupSat_gSeq_A p cl h
  · exact AluSatM.gSeq_sat_mul p cl hpG h
  · exact AluSatD.gSeq_sat p cl hpG hcl h

/-- `gCoef` for every served op. -/
theorem gCoef_G (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl AluSZChipJ9.gCoef := by
  rcases op_cases hcl with h | h | h
  · exact AluSatA.groupSat_gCoef_A p cl h
  · exact AluSatM.gCoef_sat_mul p cl hpG h
  · exact AluSatD.gCoef_sat p cl hpG hcl h

/-- `gBits` for every served op: the 32 booleans and the `mQM` part. -/
theorem gBits_G (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    GroupSat (F := ZMod p) p cl AluSZChipJ9.gBits := by
  have hB := AluSatCommon.gBitsB_sat hpG hcl
  have hsplit : GroupSat (F := ZMod p) p cl
      ((AluSatCommon.gBitsB : List (AxisChipJ9.AG (ZMod p))) ++ AluSatCommon.gBitsQM) →
      GroupSat (F := ZMod p) p cl AluSZChipJ9.gBits := fun h => h
  refine hsplit ((groupSat_append _ _ _ _).2 ⟨hB, ?_⟩)
  rcases op_cases hcl with h | h | h
  · exact AluSatA.groupSat_gBitsQM_A p cl h
  · exact AluSatM.gBitsM_sat_mul p cl hpG h hcl
  · exact AluSatD.gBitsM_sat p cl hpG hcl h

/-- **`blockBaseSat_G`**: every served call's block satisfies every base gate. -/
theorem blockBaseSat_G (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) :
    BlockBaseSat (F := ZMod p) p cl :=
  blockBaseSat_of_groups p cl (AluSatCommon.gKind_sat hpG hcl) (AluSatCommon.gSlot_sat hpG hcl)
    (gSeq_G hpG hcl) (AluSatCommon.gCompat_sat hpG hcl) (AluSatCommon.gFlag_sat hpG hcl)
    (gCoef_G hpG hcl) (AluSatCommon.gHdr_sat hpG hcl) (AluSatCommon.gConst_sat hpG hcl)
    (AluSatCommon.gBind_sat hpG hcl) (gBits_G hpG hcl) (AluSatCommon.gSplit_sat hpG hcl)
    (AluSatCommon.gCap_sat hpG hcl)

/-- The mode-5 word bound `qSat_common` needs: vacuous for add/sub/lt (no `mQM` slot), the carry bound `Q < 2^25`
for mul (M) and div/mod (D). -/
theorem hQ_G (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    ∀ s ∈ slotsOf p cl, s.mode = 5 → ∀ w ∈ s.words, w < 2 ^ 32 := by
  intro s hs h5 w hw
  rcases op_cases hcl with h | h | h
  · obtain ⟨s1, s2, s3, s4, hss, sh⟩ := AluSatA.shape_A p cl h
    rw [hss] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · have := sh.m1; omega
    · have := sh.m2; omega
    · have := sh.m3; omega
    · have := sh.m4; omega
  · have := AluSatM.sQ_words_lt p cl hpG h hcl
    rw [AluSatM.slotsOf_mul p cl h] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · rcases (AluSatM.sA_shape p cl).2.1 with h' | h' <;> omega
    · rcases (AluSatM.sB_shape p cl).2.1 with h' | h' <;> omega
    · rcases (AluSatM.sC_shape p cl).2.1 with h' | h' <;> omega
    · exact lt_of_lt_of_le (this w hw) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  · obtain ⟨sA, sX, sB, sY, sS, qM, q1, heq, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmode⟩ :=
      AluSatD.dm_shapes p cl hpG hcl h
    rw [heq] at hs
    rcases hmode s hs with h' | h'
    · exact absurd h5 h'
    · exact lt_of_lt_of_le (h' w hw) (Nat.pow_le_pow_right (by norm_num) (by norm_num))

end Block

section Ident
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

/-- The terminal `S1 = S2 = 0` equations for every served op. -/
theorem qSat_term_G (hpG : p = Nock.Atoms.p) {cl : CallL} (hcl : CallOK p cl) :
    QSat (K := K) δ p cl
      ((AluSZChipJ9.identQ δ : List (QE (ZMod p))).drop 23) := by
  rcases op_cases hcl with h | h | h
  · exact AluSatA.qSat_term_A (K := K) δ p hpG cl hcl h
  · exact AluSatM.termS_sat_mul (K := K) δ p cl hpG h hcl
  · exact AluSatD.termS_sat (K := K) δ p cl hpG hcl h

/-- **`blockIdentSat_G`**: every served call's block satisfies every `identQ` equation. -/
theorem blockIdentSat_G (hpG : p = Nock.Atoms.p) (cl : CallL) (hcl : CallOK p cl) :
    BlockIdentSat (K := K) δ p cl := by
  rw [blockIdentSat_iff]
  have e : (AluSZChipJ9.identQ δ : List (QE (ZMod p))) =
      (AluSZChipJ9.identQ δ : List (QE (ZMod p))).take 23 ++ (AluSZChipJ9.identQ δ : List (QE (ZMod p))).drop 23 :=
    (List.take_append_drop 23 _).symm
  rw [e, qSat_append]
  exact ⟨AluSatCommon.qSat_common δ hpG hcl (hQ_G hpG hcl), qSat_term_G δ hpG hcl⟩

/-- **`hblk_of_callOK`**: the `hblk` binder of `AluSatRows.tblP_chain` / `aluSZChipJ9_honest_sat_tblP` /
`AluSatPreg.aluSZChipJ9_honest_sat_preg`, from `CallOK` of every call.  `pN` is the table's prime (`pN = p`). -/
theorem hblk_of_callOK (hpG : p = Nock.Atoms.p) (pN : ℕ) (hpN : pN = p) (cls : List CallL)
    (hok : ∀ cl ∈ cls, CallOK pN cl) :
    ∀ cl ∈ cls, BlockBaseSat (F := ZMod p) pN cl ∧ BlockIdentSat (K := K) δ pN cl := by
  subst hpN
  intro cl hcl
  exact ⟨blockBaseSat_G hpG cl (hok cl hcl), blockIdentSat_G δ hpG cl (hok cl hcl)⟩

end Ident

end Nock.NockVMROM.Thm54.VclL.Handle.AluSatBlock
