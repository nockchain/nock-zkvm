/-
  Nock/NockVMROM/Thm54/TraceGen/Op2MemoryWebK3.lean

  Stage 3 of the OP2 Layer-2 CORE, over `K3`: the per-row `Vmem` acceptance, genericity
  (`WF`), whole-forest row acceptance, BFS LogUp chain, and arity-2 `Fmem` topology of
  the twenty-three-row single-root memory reconstruction of

      `*[0 [2 [1 [0 1]] [1 [1 5]]]] = 5`

  Five committed records (`mr1` formula@3, `mr2` formula-tail@2, three child formula@3
  records) with timestamps `α,…,α⁵`.  The axis-2 left descent on the formula tail is
  the OP2-specific memory shape.
  There is no Layer-1 served-memory fixture; this is reconstruction, not a served
  lookup (`requiredServedLookups.s2 = 0`)
-/
import Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3
import Nock.NockVMROM.Thm54.TraceGen.Op2RowWebK3
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.ExactTraversal

namespace Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

open Nock Nock.Walk Nock.MemoryTable Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

/-! ## The LogUp pole is the record root's fingerprint size -/

theorem pole_eq (r : MemRec K) : pole (memInputs seedZ) r 1 = r.root.size := by
  simp [pole, recRLC, memInputs]

theorem pole_row_eq (r : MemRec K) :
    pole (memInputs seedZ) (NockVM.formRRow r MemoryTable.formRDefault)
      (NockVM.formRCprime r MemoryTable.formRDefault) = pole (memInputs seedZ) r 1 := by
  simp [pole, memInputs, recRLC, NockVM.formRRow]

theorem poleF_ne : pole (memInputs seedZ) (recF seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op2ParentFormula).size ≠ 0
  simp only [fp, GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ seedZ_ne_zero

theorem poleT_ne : pole (memInputs seedZ) (recT seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op2ParentTail).size ≠ 0
  simp only [fp, GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ seedZ_ne_zero

theorem poleB_ne : pole (memInputs seedZ) (recB seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op2ChildFormula1).size ≠ 0
  simp only [fp, GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ seedZ_ne_zero

theorem poleC_ne : pole (memInputs seedZ) (recC seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op2ChildFormula2).size ≠ 0
  simp only [fp, GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ seedZ_ne_zero

theorem poleS_ne : pole (memInputs seedZ) (recS seedZ alphaA) 1 ≠ 0 := by
  rw [pole_eq]
  show (fp seedZ op2Sf2).size ≠ 0
  simp only [fp, GlobalCarryRecognizer.enc_size]
  exact pow_ne_zero _ seedZ_ne_zero

/-! ## The twenty-three memory rows are accepted by `V_mem` -/

theorem pReadF_accepts : Vmem (memInputs seedZ) (pReadF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadF, readPub, cReadF, cDecF, recF, Pub.lambda,
  Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadF, readPub, cReadF, cDecF, recF, Pub.lambda,
  Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · show (pReadF seedZ alphaA).icur - (pReadF seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadF seedZ alphaA).mem (pReadF seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadF, readPub, qF, Pub.lambda, Pub.cprime, Option.getD,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify]
      <;> first | ring | skip

theorem pDecF_accepts : Vmem (memInputs seedZ) (pDecF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op2Head op2ParentTail
  · simp [pDecF, decPub, cDecF, cHalt2, cVerifyF, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · simp [pDecF, decPub, cDecF, cHalt2, cVerifyF, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · show (pDecF seedZ alphaA).icur = (pDecF seedZ alphaA).ipre; rfl

theorem pHalt2_accepts : Vmem (memInputs seedZ) (pHalt2 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt2, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt2, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyF_accepts : Vmem (memInputs seedZ) (pVerifyF seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyF, verifyPub, cVerifyF, cReadT, recF,
  Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyF, verifyPub, cVerifyF, cReadT, recF,
  Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · show (pVerifyF seedZ alphaA).ipre - (pVerifyF seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyF seedZ alphaA).mem (pVerifyF seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyF, verifyPub, qF, Pub.lambda, Pub.cprime, Option.getD,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip

theorem pReadT_accepts : Vmem (memInputs seedZ) (pReadT seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadT, readPub, cReadT, cDecT, recT, Pub.lambda,
  Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadT, readPub, cReadT, cDecT, recT, Pub.lambda,
  Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · show (pReadT seedZ alphaA).icur - (pReadT seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadT seedZ alphaA).mem (pReadT seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadT, readPub, qT, Pub.lambda, Pub.cprime, Option.getD,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip

theorem pDecT_accepts : Vmem (memInputs seedZ) (pDecT seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op2ChildFormula1 op2ChildFormula2
  · simp [pDecT, decPub, cDecT, cVerifyT, cReadC, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · simp [pDecT, decPub, cDecT, cVerifyT, cReadC, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · show (pDecT seedZ alphaA).icur = (pDecT seedZ alphaA).ipre; rfl

theorem pVerifyT_accepts : Vmem (memInputs seedZ) (pVerifyT seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyT, verifyPub, cVerifyT, cReadB, recT,
  Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyT, verifyPub, cVerifyT, cReadB, recT,
  Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · show (pVerifyT seedZ alphaA).ipre - (pVerifyT seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyT seedZ alphaA).mem (pVerifyT seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyT, verifyPub, qT, Pub.lambda, Pub.cprime, Option.getD,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip

theorem pReadC_accepts : Vmem (memInputs seedZ) (pReadC seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadC, readPub, cReadC, cDecC, recC, Pub.lambda,
  Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadC, readPub, cReadC, cDecC, recC, Pub.lambda,
  Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · show (pReadC seedZ alphaA).icur - (pReadC seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadC seedZ alphaA).mem (pReadC seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadC, readPub, qC, Pub.lambda, Pub.cprime, Option.getD,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip

theorem pReadB_accepts : Vmem (memInputs seedZ) (pReadB seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadB, readPub, cReadB, cDecB, recB, Pub.lambda,
  Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadB, readPub, cReadB, cDecB, recB, Pub.lambda,
  Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · show (pReadB seedZ alphaA).icur - (pReadB seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadB seedZ alphaA).mem (pReadB seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadB, readPub, qC, qB, Pub.lambda, Pub.cprime, Option.getD,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip

theorem pDecC_accepts : Vmem (memInputs seedZ) (pDecC seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op1Head op2Sf2
  · simp [pDecC, decPub, cDecC, cHaltC1, cVerifyC, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · simp [pDecC, decPub, cDecC, cHaltC1, cVerifyC, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · show (pDecC seedZ alphaA).icur = (pDecC seedZ alphaA).ipre; rfl

theorem pDecB_accepts : Vmem (memInputs seedZ) (pDecB seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op1Head op2Sf1
  · simp [pDecB, decPub, cDecB, cHaltB1, cVerifyB, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · simp [pDecB, decPub, cDecB, cHaltB1, cVerifyB, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · show (pDecB seedZ alphaA).icur = (pDecB seedZ alphaA).ipre; rfl

theorem pHaltC1_accepts : Vmem (memInputs seedZ) (pHaltC1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltC1, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltC1, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyC_accepts : Vmem (memInputs seedZ) (pVerifyC seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyC, verifyPub, cVerifyC, cReadS, recC,
  Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyC, verifyPub, cVerifyC, cReadS, recC,
  Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · show (pVerifyC seedZ alphaA).ipre - (pVerifyC seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyC seedZ alphaA).mem (pVerifyC seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyC, verifyPub, qC, qB, Pub.lambda, Pub.cprime, Option.getD,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip

theorem pHaltB1_accepts : Vmem (memInputs seedZ) (pHaltB1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltB1, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltB1, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyB_accepts : Vmem (memInputs seedZ) (pVerifyB seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyB, verifyPub, cVerifyB, cDecSf1, recB,
  Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyB, verifyPub, cVerifyB, cDecSf1, recB,
  Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · show (pVerifyB seedZ alphaA).ipre - (pVerifyB seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyB seedZ alphaA).mem (pVerifyB seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyB, verifyPub, qB, Pub.lambda, Pub.cprime, Option.getD,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip

theorem pReadS_accepts : Vmem (memInputs seedZ) (pReadS seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadS, readPub, cReadS, cDecS, recS, Pub.lambda,
  Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pReadS, readPub, cReadS, cDecS, recS, Pub.lambda,
  Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · show (pReadS seedZ alphaA).icur - (pReadS seedZ alphaA).ipre =
      (pole (memInputs seedZ) (pReadS seedZ alphaA).mem (pReadS seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pReadS, readPub, qS, Pub.lambda, Pub.cprime, Option.getD,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip

theorem pDecSf1_accepts : Vmem (memInputs seedZ) (pDecSf1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero (.atom 0) (.atom 1)
  · simp [pDecSf1, decPub, cDecSf1, cHalt0, cHalt1s, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · simp [pDecSf1, decPub, cDecSf1, cHalt0, cHalt1s, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · show (pDecSf1 seedZ alphaA).icur = (pDecSf1 seedZ alphaA).ipre; rfl

theorem pDecS_accepts : Vmem (memInputs seedZ) (pDecS seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, ?_, rfl⟩, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons seedZ_ne_zero op1Head op2Result
  · simp [pDecS, decPub, cDecS, cHaltS1, cVerifyS, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · simp [pDecS, decPub, cDecS, cHaltS1, cVerifyS, Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip
  · show (pDecS seedZ alphaA).icur = (pDecS seedZ alphaA).ipre; rfl

theorem pHalt0_accepts : Vmem (memInputs seedZ) (pHalt0 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt0, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt0, fp, GlobalCarryRecognizer.enc_atom]

theorem pHalt1s_accepts : Vmem (memInputs seedZ) (pHalt1s seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt1s, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt1s, fp, GlobalCarryRecognizer.enc_atom]

theorem pHaltS1_accepts : Vmem (memInputs seedZ) (pHaltS1 seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHaltS1, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHaltS1, fp, GlobalCarryRecognizer.enc_atom]

theorem pVerifyS_accepts : Vmem (memInputs seedZ) (pVerifyS seedZ alphaA) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyS, verifyPub, cVerifyS, cHalt5, recS,
  Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · simp [NockVM.formRRow, NockVM.formRCprime, pVerifyS, verifyPub, cVerifyS, cHalt5, recS,
  Pub.lambda, Pub.cprime, Option.getD, MemoryTable.pwScaleExp, one_pow, cellRead, cellDec,
  cellVerify] <;> first | ring | skip
  · show (pVerifyS seedZ alphaA).ipre - (pVerifyS seedZ alphaA).icur =
      (pole (memInputs seedZ) (pVerifyS seedZ alphaA).mem (pVerifyS seedZ alphaA).cprime)⁻¹
    simp [pole_row_eq, pVerifyS, verifyPub, qS, Pub.lambda, Pub.cprime, Option.getD,
      MemoryTable.pwScaleExp, one_pow, cellRead, cellDec, cellVerify] <;> first | ring | skip

theorem pHalt5_accepts : Vmem (memInputs seedZ) (pHalt5 seedZ) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [haltPub, pHalt5, fp, GlobalCarryRecognizer.enc_atom, memInputs]
  · simp [haltPub, pHalt5, fp, GlobalCarryRecognizer.enc_atom]

/-! ## Whole-forest row acceptance -/

theorem memoryRows_eq :
    (exec seedZ alphaA).memoryRows =
      [lblOf seedZ (pReadF seedZ alphaA), lblOf seedZ (pDecF seedZ alphaA),
        lblOf seedZ (pHalt2 seedZ alphaA), lblOf seedZ (pVerifyF seedZ alphaA),
        lblOf seedZ (pReadT seedZ alphaA), lblOf seedZ (pDecT seedZ alphaA),
        lblOf seedZ (pVerifyT seedZ alphaA), lblOf seedZ (pReadC seedZ alphaA),
        lblOf seedZ (pReadB seedZ alphaA), lblOf seedZ (pDecC seedZ alphaA),
        lblOf seedZ (pDecB seedZ alphaA), lblOf seedZ (pHaltC1 seedZ alphaA),
        lblOf seedZ (pVerifyC seedZ alphaA), lblOf seedZ (pHaltB1 seedZ alphaA),
        lblOf seedZ (pVerifyB seedZ alphaA), lblOf seedZ (pReadS seedZ alphaA),
        lblOf seedZ (pDecSf1 seedZ alphaA), lblOf seedZ (pDecS seedZ alphaA),
        lblOf seedZ (pHalt0 seedZ alphaA), lblOf seedZ (pHalt1s seedZ alphaA),
        lblOf seedZ (pHaltS1 seedZ alphaA), lblOf seedZ (pVerifyS seedZ alphaA),
        lblOf seedZ (pHalt5 seedZ)] := by
  simp [ExactExecution.memoryRows, exec, rootTree, tDecF, tHalt2, tVerifyF, tReadT,
    tDecT, tVerifyT, tReadC, tReadB, tDecC, tDecB, tHaltC1, tVerifyC, tHaltB1, tVerifyB,
    tReadS, tDecSf1, tDecS, tHalt0, tHalt1s, tHaltS1, tVerifyS, tHalt5, mLeaf, mOne, mTwo,
    bfsForest]

theorem memoryRowsAccepted : (exec seedZ alphaA).MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, memoryRows_eq]
  intro row hrow
  simp [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, pReadF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt2_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyF_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyT_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadC_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadB_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecC_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecB_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltC1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyC_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltB1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyB_accepts, rfl⟩
  · exact ⟨rfl, rfl, pReadS_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecSf1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pDecS_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt0_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt1s_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHaltS1_accepts, rfl⟩
  · exact ⟨rfl, rfl, pVerifyS_accepts, rfl⟩
  · exact ⟨rfl, rfl, pHalt5_accepts, rfl⟩

/-! ## Memory genericity (`WF`) -/

theorem pReadF_wf : MemoryTable.WF (memInputs seedZ) (pReadF seedZ alphaA) where
  pole_ne _ := by simpa [pole_row_eq, pReadF, readPub, Pub.cprime] using poleF_ne
theorem pVerifyF_wf : MemoryTable.WF (memInputs seedZ) (pVerifyF seedZ alphaA) where
  pole_ne _ := by simpa [pole_row_eq, pVerifyF, verifyPub, Pub.cprime] using poleF_ne
theorem pReadT_wf : MemoryTable.WF (memInputs seedZ) (pReadT seedZ alphaA) where
  pole_ne _ := by simpa [pole_row_eq, pReadT, readPub, Pub.cprime] using poleT_ne
theorem pVerifyT_wf : MemoryTable.WF (memInputs seedZ) (pVerifyT seedZ alphaA) where
  pole_ne _ := by simpa [pole_row_eq, pVerifyT, verifyPub, Pub.cprime] using poleT_ne
theorem pReadC_wf : MemoryTable.WF (memInputs seedZ) (pReadC seedZ alphaA) where
  pole_ne _ := by simpa [pole_row_eq, pReadC, readPub, Pub.cprime] using poleC_ne
theorem pVerifyC_wf : MemoryTable.WF (memInputs seedZ) (pVerifyC seedZ alphaA) where
  pole_ne _ := by simpa [pole_row_eq, pVerifyC, verifyPub, Pub.cprime] using poleC_ne
theorem pReadB_wf : MemoryTable.WF (memInputs seedZ) (pReadB seedZ alphaA) where
  pole_ne _ := by simpa [pole_row_eq, pReadB, readPub, Pub.cprime] using poleB_ne
theorem pVerifyB_wf : MemoryTable.WF (memInputs seedZ) (pVerifyB seedZ alphaA) where
  pole_ne _ := by simpa [pole_row_eq, pVerifyB, verifyPub, Pub.cprime] using poleB_ne
theorem pReadS_wf : MemoryTable.WF (memInputs seedZ) (pReadS seedZ alphaA) where
  pole_ne _ := by simpa [pole_row_eq, pReadS, readPub, Pub.cprime] using poleS_ne
theorem pVerifyS_wf : MemoryTable.WF (memInputs seedZ) (pVerifyS seedZ alphaA) where
  pole_ne _ := by simpa [pole_row_eq, pVerifyS, verifyPub, Pub.cprime] using poleS_ne

theorem halt_wf (k : ℕ) (acc : K) :
    MemoryTable.WF (memInputs seedZ) (haltPub seedZ k acc) where
  pole_ne h := by simp [haltPub] at h

theorem dec_wf (pt lc rc : MemoryTable.Cell K) (lcSt rcSt : MemoryTable.MState) (acc : K) :
    MemoryTable.WF (memInputs seedZ) (decPub seedZ pt lc rc lcSt rcSt acc) where
  pole_ne h := by simp [decPub] at h

/-! ## BFS re-indexing of the canonical memory rows -/

theorem memoryPubAt_0 :
    (exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩ = pReadF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_1 :
    (exec seedZ alphaA).memoryPubAt ⟨1, by norm_num [cfg]⟩ = pDecF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_2 :
    (exec seedZ alphaA).memoryPubAt ⟨2, by norm_num [cfg]⟩ = pHalt2 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_3 :
    (exec seedZ alphaA).memoryPubAt ⟨3, by norm_num [cfg]⟩ = pVerifyF seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_4 :
    (exec seedZ alphaA).memoryPubAt ⟨4, by norm_num [cfg]⟩ = pReadT seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_5 :
    (exec seedZ alphaA).memoryPubAt ⟨5, by norm_num [cfg]⟩ = pDecT seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_6 :
    (exec seedZ alphaA).memoryPubAt ⟨6, by norm_num [cfg]⟩ = pVerifyT seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_7 :
    (exec seedZ alphaA).memoryPubAt ⟨7, by norm_num [cfg]⟩ = pReadC seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_8 :
    (exec seedZ alphaA).memoryPubAt ⟨8, by norm_num [cfg]⟩ = pReadB seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_9 :
    (exec seedZ alphaA).memoryPubAt ⟨9, by norm_num [cfg]⟩ = pDecC seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_10 :
    (exec seedZ alphaA).memoryPubAt ⟨10, by norm_num [cfg]⟩ = pDecB seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_11 :
    (exec seedZ alphaA).memoryPubAt ⟨11, by norm_num [cfg]⟩ = pHaltC1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_12 :
    (exec seedZ alphaA).memoryPubAt ⟨12, by norm_num [cfg]⟩ = pVerifyC seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_13 :
    (exec seedZ alphaA).memoryPubAt ⟨13, by norm_num [cfg]⟩ = pHaltB1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_14 :
    (exec seedZ alphaA).memoryPubAt ⟨14, by norm_num [cfg]⟩ = pVerifyB seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_15 :
    (exec seedZ alphaA).memoryPubAt ⟨15, by norm_num [cfg]⟩ = pReadS seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_16 :
    (exec seedZ alphaA).memoryPubAt ⟨16, by norm_num [cfg]⟩ = pDecSf1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_17 :
    (exec seedZ alphaA).memoryPubAt ⟨17, by norm_num [cfg]⟩ = pDecS seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_18 :
    (exec seedZ alphaA).memoryPubAt ⟨18, by norm_num [cfg]⟩ = pHalt0 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_19 :
    (exec seedZ alphaA).memoryPubAt ⟨19, by norm_num [cfg]⟩ = pHalt1s seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_20 :
    (exec seedZ alphaA).memoryPubAt ⟨20, by norm_num [cfg]⟩ = pHaltS1 seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_21 :
    (exec seedZ alphaA).memoryPubAt ⟨21, by norm_num [cfg]⟩ = pVerifyS seedZ alphaA := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]
theorem memoryPubAt_22 :
    (exec seedZ alphaA).memoryPubAt ⟨22, by norm_num [cfg]⟩ = pHalt5 seedZ := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, memoryRows_eq, cfg, lblOf]

theorem memory_wf_all :
    ∀ i, MemoryTable.WF (cfg seedZ alphaA).challenges.memoryInputs
      ((exec seedZ alphaA).memoryPubAt i) := by
  intro i
  fin_cases i
  · rw [memoryPubAt_0]; exact pReadF_wf
  · rw [memoryPubAt_1]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_2]; exact halt_wf _ _
  · rw [memoryPubAt_3]; exact pVerifyF_wf
  · rw [memoryPubAt_4]; exact pReadT_wf
  · rw [memoryPubAt_5]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_6]; exact pVerifyT_wf
  · rw [memoryPubAt_7]; exact pReadC_wf
  · rw [memoryPubAt_8]; exact pReadB_wf
  · rw [memoryPubAt_9]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_10]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_11]; exact halt_wf _ _
  · rw [memoryPubAt_12]; exact pVerifyC_wf
  · rw [memoryPubAt_13]; exact halt_wf _ _
  · rw [memoryPubAt_14]; exact pVerifyB_wf
  · rw [memoryPubAt_15]; exact pReadS_wf
  · rw [memoryPubAt_16]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_17]; exact dec_wf _ _ _ _ _ _
  · rw [memoryPubAt_18]; exact halt_wf _ _
  · rw [memoryPubAt_19]; exact halt_wf _ _
  · rw [memoryPubAt_20]; exact halt_wf _ _
  · rw [memoryPubAt_21]; exact pVerifyS_wf
  · rw [memoryPubAt_22]; exact halt_wf _ _

/-- Adjacent memory rows share the LogUp boundary (`icur` of `i` is `ipre` of `i+1`). -/
theorem memory_chain :
    ∀ i : Fin (cfg seedZ alphaA).memRows,
      ∀ _ : (i : ℕ) + 1 < (cfg seedZ alphaA).memRows,
        ((exec seedZ alphaA).memoryPubAt i).icur =
          ((exec seedZ alphaA).memoryPubAt ⟨(i : ℕ) + 1, by omega⟩).ipre := by
  intro i hi
  fin_cases i
  · rw [memoryPubAt_0, memoryPubAt_1]; rfl
  · rw [memoryPubAt_1, memoryPubAt_2]; rfl
  · rw [memoryPubAt_2, memoryPubAt_3]; rfl
  · rw [memoryPubAt_3, memoryPubAt_4]; rfl
  · rw [memoryPubAt_4, memoryPubAt_5]; rfl
  · rw [memoryPubAt_5, memoryPubAt_6]; rfl
  · rw [memoryPubAt_6, memoryPubAt_7]; rfl
  · rw [memoryPubAt_7, memoryPubAt_8]; rfl
  · rw [memoryPubAt_8, memoryPubAt_9]; rfl
  · rw [memoryPubAt_9, memoryPubAt_10]; rfl
  · rw [memoryPubAt_10, memoryPubAt_11]; rfl
  · rw [memoryPubAt_11, memoryPubAt_12]; rfl
  · rw [memoryPubAt_12, memoryPubAt_13]; rfl
  · rw [memoryPubAt_13, memoryPubAt_14]; rfl
  · rw [memoryPubAt_14, memoryPubAt_15]; rfl
  · rw [memoryPubAt_15, memoryPubAt_16]; rfl
  · rw [memoryPubAt_16, memoryPubAt_17]; rfl
  · rw [memoryPubAt_17, memoryPubAt_18]; rfl
  · rw [memoryPubAt_18, memoryPubAt_19]; rfl
  · rw [memoryPubAt_19, memoryPubAt_20]; rfl
  · rw [memoryPubAt_20, memoryPubAt_21]; rfl
  · rw [memoryPubAt_21, memoryPubAt_22]; rfl
  · simp [cfg] at hi

/-! ## Arity-2 `Fmem` topology on the twenty-three-row forest -/

theorem fmem_leaf {pub : MemoryTable.Pub K} (hv : Vmem (memInputs seedZ) pub)
    (hf : MemoryTable.fanoutMem pub.st = 0) :
    MemoryTable.Fmem (lblOf seedZ pub) (fun _ => none) := by
  refine ⟨rfl, hv, ?_, ?_⟩
  · intro i
    refine ⟨fun h => ?_, fun h => absurd rfl h⟩
    rw [show (lblOf seedZ pub).1 = pub.st from rfl, hf] at h
    omega
  · intro i hi
    rw [show (lblOf seedZ pub).1 = pub.st from rfl, hf] at hi
    omega

theorem rvt_one {pub : MemoryTable.Pub K} {ct : NTree MLbl}
    (hv : Vmem (memInputs seedZ) pub) (hf : MemoryTable.fanoutMem pub.st = 1)
    (hpt : ct.label.2.2.pt = pub.lc) (hct : RVT (MemoryTable.Fmem (K := K)) ct) :
    RVT (MemoryTable.Fmem (K := K)) (mOne seedZ pub ct) := by
  unfold mOne RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hv, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [NTree.childLabel, NTree.childOpt, lblOf, hf]
    · intro i hi
      fin_cases i
      · simpa [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf, NTree.label]
          using hpt
      · exact absurd hi (by rw [show (lblOf seedZ pub).1 = pub.st from rfl, hf]; decide)
  · intro s hs
    simp [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    exact hct
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    rw [show (lblOf seedZ pub).1 = pub.st from rfl, hf] at h0
    simp at h0

theorem rvt_two {pub : MemoryTable.Pub K} {lt rt : NTree MLbl}
    (hv : Vmem (memInputs seedZ) pub) (hf : MemoryTable.fanoutMem pub.st = 2)
    (hl : lt.label.2.2.pt = pub.lc) (hr : rt.label.2.2.pt = pub.rc)
    (hlt : RVT (MemoryTable.Fmem (K := K)) lt)
    (hrt : RVT (MemoryTable.Fmem (K := K)) rt) :
    RVT (MemoryTable.Fmem (K := K)) (mTwo seedZ pub lt rt) := by
  unfold mTwo RVT
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hv, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [NTree.childLabel, NTree.childOpt, lblOf, hf]
    · intro i hi
      fin_cases i
      · simpa [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf, NTree.label]
          using hl
      · simpa [NTree.childLabel, NTree.childOpt, MemoryTable.memCell, lblOf, NTree.label]
          using hr
  · intro s hs
    simp [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hlt
    · exact hrt
  · refine ⟨fun h => absurd h (by simp [NTree.isLeaf]), fun h => ?_⟩
    exfalso
    have h0 := h.2.2.1 ⟨0, by norm_num⟩
    rw [show (lblOf seedZ pub).1 = pub.st from rfl, hf] at h0
    simp at h0

theorem halt_tree_rvt {k : ℕ} {acc : K}
    (hv : Vmem (memInputs seedZ) (haltPub seedZ k acc)) :
    RVT (MemoryTable.Fmem (K := K)) (mLeaf seedZ (haltPub seedZ k acc)) := by
  unfold mLeaf RVT
  exact ⟨fmem_leaf hv rfl, by simp,
    ⟨fun _ => fmem_leaf hv rfl, fun _ => rfl⟩⟩

theorem tHalt5_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt5 seedZ) :=
  halt_tree_rvt pHalt5_accepts
theorem tHaltS1_rvt : RVT (MemoryTable.Fmem (K := K)) (tHaltS1 seedZ alphaA) :=
  halt_tree_rvt pHaltS1_accepts
theorem tHalt0_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt0 seedZ alphaA) :=
  halt_tree_rvt pHalt0_accepts
theorem tHalt1s_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt1s seedZ alphaA) :=
  halt_tree_rvt pHalt1s_accepts
theorem tHaltB1_rvt : RVT (MemoryTable.Fmem (K := K)) (tHaltB1 seedZ alphaA) :=
  halt_tree_rvt pHaltB1_accepts
theorem tHaltC1_rvt : RVT (MemoryTable.Fmem (K := K)) (tHaltC1 seedZ alphaA) :=
  halt_tree_rvt pHaltC1_accepts
theorem tHalt2_rvt : RVT (MemoryTable.Fmem (K := K)) (tHalt2 seedZ alphaA) :=
  halt_tree_rvt pHalt2_accepts

theorem tVerifyS_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyS seedZ alphaA) :=
  rvt_one pVerifyS_accepts rfl rfl tHalt5_rvt
theorem tDecS_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecS seedZ alphaA) :=
  rvt_two pDecS_accepts rfl rfl rfl tHaltS1_rvt tVerifyS_rvt
theorem tReadS_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadS seedZ alphaA) :=
  rvt_one pReadS_accepts rfl rfl tDecS_rvt
theorem tDecSf1_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecSf1 seedZ alphaA) :=
  rvt_two pDecSf1_accepts rfl rfl rfl tHalt0_rvt tHalt1s_rvt
theorem tVerifyB_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyB seedZ alphaA) :=
  rvt_one pVerifyB_accepts rfl rfl tDecSf1_rvt
theorem tDecB_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecB seedZ alphaA) :=
  rvt_two pDecB_accepts rfl rfl rfl tHaltB1_rvt tVerifyB_rvt
theorem tReadB_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadB seedZ alphaA) :=
  rvt_one pReadB_accepts rfl rfl tDecB_rvt
theorem tVerifyC_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyC seedZ alphaA) :=
  rvt_one pVerifyC_accepts rfl rfl tReadS_rvt
theorem tDecC_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecC seedZ alphaA) :=
  rvt_two pDecC_accepts rfl rfl rfl tHaltC1_rvt tVerifyC_rvt
theorem tReadC_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadC seedZ alphaA) :=
  rvt_one pReadC_accepts rfl rfl tDecC_rvt
theorem tVerifyT_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyT seedZ alphaA) :=
  rvt_one pVerifyT_accepts rfl rfl tReadB_rvt
theorem tDecT_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecT seedZ alphaA) :=
  rvt_two pDecT_accepts rfl rfl rfl tVerifyT_rvt tReadC_rvt
theorem tReadT_rvt : RVT (MemoryTable.Fmem (K := K)) (tReadT seedZ alphaA) :=
  rvt_one pReadT_accepts rfl rfl tDecT_rvt
theorem tVerifyF_rvt : RVT (MemoryTable.Fmem (K := K)) (tVerifyF seedZ alphaA) :=
  rvt_one pVerifyF_accepts rfl rfl tReadT_rvt
theorem tDecF_rvt : RVT (MemoryTable.Fmem (K := K)) (tDecF seedZ alphaA) :=
  rvt_two pDecF_accepts rfl rfl rfl tHalt2_rvt tVerifyF_rvt
theorem rootTree_rvt : RVT (MemoryTable.Fmem (K := K)) (rootTree seedZ alphaA) :=
  rvt_one pReadF_accepts rfl rfl tDecF_rvt

theorem memory_topology : MemoryExactTopology (exec seedZ alphaA) := by
  intro t ht
  simp [exec, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  refine ⟨rootTree_rvt, ?_⟩
  show ProperArity 2 (rootTree seedZ alphaA)
  simp [rootTree, tDecF, tHalt2, tVerifyF, tReadT, tDecT, tVerifyT, tReadC, tReadB,
    tDecC, tDecB, tHaltC1, tVerifyC, tHaltB1, tVerifyB, tReadS, tDecSf1, tDecS, tHalt0,
    tHalt1s, tHaltS1, tVerifyS, tHalt5, mLeaf, mOne, mTwo]

end

end Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.pReadF_accepts
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.pVerifyT_accepts
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.memoryRowsAccepted
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.memory_topology
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op2ConfigK3.memory_chain
