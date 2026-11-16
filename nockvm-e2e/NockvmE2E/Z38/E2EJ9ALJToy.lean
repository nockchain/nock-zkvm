/-
NockvmE2E/Z38/E2EJ9ALJToy.lean: the datum-side non-vacuity witness of `nock_e2e_J9ALJ_succinct` at the executed template-jet
instance `jpX` (Exec/JpALR.lean): `jp_witness` (`Wit9LJ (XI170 jpX) cJ Q` for the claim = nockvm's kernel run of `jp`, and the claim holds) and `jp_witness_false`
(the false twin `jpXF`).  `shapeOkF` stays the executed hypothesis `hsh` (as at J-9 A / AL).  Every `LinkOK9LJ` / `JetLink` conjunct, every `pregOkF` column and
every `jetPreOkF` column is proved ONE BY ONE (`decide +kernel` on the field, never on the whole instance).  `Q := fun _ => True`.
Not zero-knowledge.
-/
import NockvmE2E.Exec.JpALR
import NockvmE2E.Z38.JpClaim
import NockvmE2E.Z38.WitJ9ALJ

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Z38.E2EJ9ALJToy

open Nock.NockVMROM.Thm54 (P8PublicClaim)
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.J9A.RunGate9L NockvmE2E.J9AL.WitJ9AL NockvmE2E.J9AL.RunGate9LVRun NockvmE2E.J9AL.PbOfX9L
open NockvmE2E.J8.InstJ8 (P tabOf hNof)
open NockvmE2E.Exec.JpALR
open NockvmE2E.Z38.JpClaim (cJ cJF)
open NockvmE2E.Z38.JetPre NockvmE2E.Z38.RunGate9LJ NockvmE2E.Z38.IfaceJ NockvmE2E.Z38.WitJ9ALJ
open NockvmE2E.Exec.VF (PN)
open NockvmE2E.Exec.MaskOk (evalNodes)

abbrev XJ : ExecInst := XI170 jpX
abbrev XJF : ExecInst := XI170 jpXF

theorem can_jp : inpCanOkL XJ.pubIn = true := by decide +kernel
theorem can_jpF : inpCanOkL XJF.pubIn = true := by decide +kernel

/-! ## 1. the link gate, per conjunct -/

set_option maxHeartbeats 8000000 in
theorem link_jp : LinkOK9LJ XJ cJ := by
  unfold LinkOK9LJ LinkBaseLJ PrimsLink JetLink jLen jPinB jPinN jRegsCat jRegsNd jDisj jSmall jUniq jCalls
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (intro t; fin_cases t <;> decide +kernel) | decide +kernel

set_option maxHeartbeats 8000000 in
theorem link_jpF : LinkOK9LJ XJF cJF := by
  unfold LinkOK9LJ LinkBaseLJ PrimsLink JetLink jLen jPinB jPinN jRegsCat jRegsNd jDisj jSmall jUniq jCalls
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | (intro t; fin_cases t <;> decide +kernel) | decide +kernel


/-! ## 2. `pregOkF`: only the ALU table (tab 5) is constrained; its header and three columns one by one -/

theorem tabs_size : XJ.tabs.size = 6 := by decide +kernel
theorem tabs_sizeF : XJF.tabs.size = 6 := by decide +kernel

theorem preg_hdr : (decide (XJ.pubIn.prims.length ≤ jpT5.hN) &&
    XJ.pubIn.prims.all (fun q => decide (q.id < PN) && decide (q.code < PN))) = true := by decide +kernel
theorem preg_k0 : (decide ((XJ.pre.getD (jpT5.col0 + 2 + 0) #[]).size ≤ jpT5.hN) &&
    evalNodes (XJ.pre.getD (jpT5.col0 + 2 + 0) #[]) XJ.hGen jpT5.hN ==
      (Array.range jpT5.hN).map (pregVal XJ.pubIn.prims 0)) = true := by decide +kernel
theorem preg_k1 : (decide ((XJ.pre.getD (jpT5.col0 + 2 + 1) #[]).size ≤ jpT5.hN) &&
    evalNodes (XJ.pre.getD (jpT5.col0 + 2 + 1) #[]) XJ.hGen jpT5.hN ==
      (Array.range jpT5.hN).map (pregVal XJ.pubIn.prims 1)) = true := by decide +kernel
theorem preg_k2 : (decide ((XJ.pre.getD (jpT5.col0 + 2 + 2) #[]).size ≤ jpT5.hN) &&
    evalNodes (XJ.pre.getD (jpT5.col0 + 2 + 2) #[]) XJ.hGen jpT5.hN ==
      (Array.range jpT5.hN).map (pregVal XJ.pubIn.prims 2)) = true := by decide +kernel

theorem preg_jp : pregOkF XJ = true := by
  unfold pregOkF
  rw [Array.all_eq_true]
  intro i hi
  rw [tabs_size] at hi
  interval_cases i
  · show (if (jpT0.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (jpT0.chip.id == "aluChipJ9") = false := by decide +kernel
    simp [h]
  · show (if (jpT1.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (jpT1.chip.id == "aluChipJ9") = false := by decide +kernel
    simp [h]
  · show (if (jpT2.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (jpT2.chip.id == "aluChipJ9") = false := by decide +kernel
    simp [h]
  · show (if (jpT3.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (jpT3.chip.id == "aluChipJ9") = false := by decide +kernel
    simp [h]
  · show (if (jpT4.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (jpT4.chip.id == "aluChipJ9") = false := by decide +kernel
    simp [h]
  · show (if (jpT5.chip.id == "aluChipJ9") = true then _ else true) = true
    have h : (jpT5.chip.id == "aluChipJ9") = true := by decide +kernel
    simp only [h, ite_true]
    rw [Bool.and_eq_true]
    refine ⟨preg_hdr, ?_⟩
    rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range] at hk
    interval_cases k
    · exact preg_k0
    · exact preg_k1
    · exact preg_k2

/-- `pregOkF` reads only the tables, the preprocessed columns, `hGen` and the primitive records -/
theorem pregOkF_congr (A B : ExecInst) (ht : A.tabs = B.tabs) (hp : A.pubIn.prims = B.pubIn.prims) (hpre : A.pre = B.pre)
    (hg : A.hGen = B.hGen) : pregOkF A = pregOkF B := by
  unfold pregOkF; rw [ht, hp, hpre, hg]

theorem preg_jpF : pregOkF XJF = true := by
  rw [pregOkF_congr XJF XJ rfl rfl rfl rfl]; exact preg_jp

/-! ## 3. `jetPreOkF`: the jet table (tab 3), layout length, masks, and the 16 layout columns one by one -/

theorem jlen_jp : jetLayLenOk XJ jpT3 = true := by decide +kernel
theorem jmask_jp : jetMasksOk XJ jpT3 = true := by decide +kernel
theorem jcol_0 : jetColOk XJ jpT3 0 = true := by decide +kernel
theorem jcol_1 : jetColOk XJ jpT3 1 = true := by decide +kernel
theorem jcol_2 : jetColOk XJ jpT3 2 = true := by decide +kernel
theorem jcol_3 : jetColOk XJ jpT3 3 = true := by decide +kernel
theorem jcol_4 : jetColOk XJ jpT3 4 = true := by decide +kernel
theorem jcol_5 : jetColOk XJ jpT3 5 = true := by decide +kernel
theorem jcol_6 : jetColOk XJ jpT3 6 = true := by decide +kernel
theorem jcol_7 : jetColOk XJ jpT3 7 = true := by decide +kernel
theorem jcol_8 : jetColOk XJ jpT3 8 = true := by decide +kernel
theorem jcol_9 : jetColOk XJ jpT3 9 = true := by decide +kernel
theorem jcol_10 : jetColOk XJ jpT3 10 = true := by decide +kernel
theorem jcol_13 : jetColOk XJ jpT3 13 = true := by decide +kernel
theorem jcol_14 : jetColOk XJ jpT3 14 = true := by decide +kernel
theorem jcol_15 : jetColOk XJ jpT3 15 = true := by decide +kernel
theorem jcol_16 : jetColOk XJ jpT3 16 = true := by decide +kernel
theorem jcol_17 : jetColOk XJ jpT3 17 = true := by decide +kernel

theorem jcols_jp : jetColsOk XJ jpT3 = true := by
  unfold jetColsOk
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  interval_cases c
  · simp [jcol_0]
  · simp [jcol_1]
  · simp [jcol_2]
  · simp [jcol_3]
  · simp [jcol_4]
  · simp [jcol_5]
  · simp [jcol_6]
  · simp [jcol_7]
  · simp [jcol_8]
  · simp [jcol_9]
  · simp [jcol_10]
  · rfl
  · rfl
  · simp [jcol_13]
  · simp [jcol_14]
  · simp [jcol_15]
  · simp [jcol_16]
  · simp [jcol_17]

theorem jetpre_jp : jetPreOkF XJ = true := by
  unfold jetPreOkF
  rw [Array.all_eq_true]
  intro i hi
  rw [tabs_size] at hi
  interval_cases i
  · show (if (jpT0.chip.id == "jetChipJ8") = true then _ else true) = true
    have h : (jpT0.chip.id == "jetChipJ8") = false := by decide +kernel
    simp [h]
  · show (if (jpT1.chip.id == "jetChipJ8") = true then _ else true) = true
    have h : (jpT1.chip.id == "jetChipJ8") = false := by decide +kernel
    simp [h]
  · show (if (jpT2.chip.id == "jetChipJ8") = true then _ else true) = true
    have h : (jpT2.chip.id == "jetChipJ8") = false := by decide +kernel
    simp [h]
  · show (if (jpT3.chip.id == "jetChipJ8") = true then _ else true) = true
    have h : (jpT3.chip.id == "jetChipJ8") = true := by decide +kernel
    simp only [h, ite_true, Bool.and_eq_true]
    exact ⟨⟨jlen_jp, jmask_jp⟩, jcols_jp⟩
  · show (if (jpT4.chip.id == "jetChipJ8") = true then _ else true) = true
    have h : (jpT4.chip.id == "jetChipJ8") = false := by decide +kernel
    simp [h]
  · show (if (jpT5.chip.id == "jetChipJ8") = true then _ else true) = true
    have h : (jpT5.chip.id == "jetChipJ8") = false := by decide +kernel
    simp [h]

/-- `jetPreOkF` at a copy of `A` with another public input of the same pins and calls -/
theorem jetPreOkF_congr (A : ExecInst) (q : PE.PubIn) (hp : q.pins = A.pubIn.pins) (hc : q.calls = A.pubIn.calls) :
    jetPreOkF { A with pubIn := q } = jetPreOkF A := by
  have hl : layJ q = layJ A.pubIn := by
    unfold layJ regsOfPub; rw [hp, hc]
  unfold jetPreOkF jetLayLenOk jetMasksOk jetColsOk jetColOk
  simp only [hl]
  rfl

theorem jetpre_jpF : jetPreOkF XJF = true := by
  have h : jetPreOkF { XJ with pubIn := jpPubInF } = jetPreOkF XJ := jetPreOkF_congr XJ jpPubInF rfl rfl
  exact h.trans jetpre_jp

/-! ## 4. the witnesses -/

/-- **`jp_witness`** [kernel job, modulo the executed gate `hsh`]: every datum premise of `nock_e2e_J9ALJ_succinct` (`Wit9LJ`) holds at the executed `jp`
instance, for the claim = nockvm's kernel run of the program, and the claim holds. -/
theorem jp_witness (hsh : shapeOkF famJ9AL XJ = true) :
    Wit9LJ XJ cJ (fun _ => True) ∧ (Nock.V1J8.Gen.runX NockvmE2E.Z38.CatJ.catJ.toVR.R 4 NockvmE2E.Z38.HF1LJ.sJ NockvmE2E.Z38.HF1LJ.fJ).map (·.res) = some cJ.result ∧
      Nock.Jet.HoldsN cJ :=
  ⟨witness9LJ XJ cJ hsh preg_jp jetpre_jp (primsCan_of_inpCanOkL can_jp) link_jp _ (fun _ => trivial),
    NockvmE2E.Z38.JpClaim.run_jp, NockvmE2E.Z38.JpClaim.holds_jp⟩

/-- **`jp_witness_false`** [kernel job, modulo `hsh` at the twin]: at `jpXF` (result `p+9`) every datum premise holds for `cJF`, the run is still
nockvm's (`p+8`), the two results differ, and `¬ HoldsN cJF`. -/
theorem jp_witness_false (hsh : shapeOkF famJ9AL XJF = true) :
    Wit9LJ XJF cJF (fun _ => True) ∧ (Nock.V1J8.Gen.runX NockvmE2E.Z38.CatJ.catJ.toVR.R 4 NockvmE2E.Z38.HF1LJ.sJ NockvmE2E.Z38.HF1LJ.fJ).map (·.res) = some NockvmE2E.Z38.JpClaim.cJ.result ∧
      cJF.result ≠ NockvmE2E.Z38.JpClaim.cJ.result ∧ ¬ Nock.Jet.HoldsN cJF :=
  ⟨witness9LJ XJF cJF hsh preg_jpF jetpre_jpF (primsCan_of_inpCanOkL can_jpF) link_jpF _ (fun _ => trivial),
    NockvmE2E.Z38.JpClaim.run_jp, NockvmE2E.Z38.JpClaim.rJ_ne, NockvmE2E.Z38.JpClaim.not_holds_jpF⟩


/-! ## 5. the stronger premise `QJ`: the witness visibly uses the template jet -/

open NockvmE2E.J9AL.InstJ9AL (Datum9AL)
open NockvmE2E.J9A.RunGate9L (kOfL kVOfL)

/-- registry `[7]`, one call of id 7, a non-empty jet table, the registered template at id 7 is `TN`, ALU on, the primitive `(8, add)` -/
def QJ (d : Datum9AL) : Prop :=
  d.Pb.regs = [7] ∧ d.Pb.ids = [7] ∧ 0 < d.Pb.nJ ∧ d.Pb.Rt 7 = NockvmE2E.Z38.CatJ.TN ∧ d.Pb.aluOn = true ∧
    d.Pb.prims = [(8, Nock.Jet.Prim.PrimOp.add)]

theorem hQJ_jp (hsh : shapeOkF famJ9AL XJ = true) (hlen : (layJ XJ.pubIn).length = hNof XJ "jetChipJ8") :
    QJ (DX9LJ XJ hsh hlen (kOfL XJ) (kVOfL XJ) cJ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show regsOfPub XJ.pubIn = [7]; decide +kernel
  · show XJ.pubIn.calls = [7]; decide +kernel
  · show 0 < hNof XJ "jetChipJ8"; decide +kernel
  · rfl
  · show (tabOf XJ "aluChipJ9").isSome = true; decide +kernel
  · show primsOf XJ = [(8, Nock.Jet.Prim.PrimOp.add)]; decide +kernel

/-- **`jp_witnessQ`** [kernel job, modulo `hsh`]: `jp_witness` with the premise `QJ` (registry `[7]`, call `[7]`, non-empty J table, `Rt 7 = TN`, ALU, prim `(8, add)`). -/
theorem jp_witnessQ (hsh : shapeOkF famJ9AL XJ = true) : Wit9LJ XJ cJ QJ :=
  witness9LJ XJ cJ hsh preg_jp jetpre_jp (primsCan_of_inpCanOkL can_jp) link_jp QJ (fun hlen => hQJ_jp hsh hlen)

end NockvmE2E.Z38.E2EJ9ALJToy

#print axioms NockvmE2E.Z38.E2EJ9ALJToy.can_jp
#print axioms NockvmE2E.Z38.E2EJ9ALJToy.link_jp
#print axioms NockvmE2E.Z38.E2EJ9ALJToy.link_jpF
#print axioms NockvmE2E.Z38.E2EJ9ALJToy.preg_jp
#print axioms NockvmE2E.Z38.E2EJ9ALJToy.jetpre_jp
#print axioms NockvmE2E.Z38.E2EJ9ALJToy.jp_witness
#print axioms NockvmE2E.Z38.E2EJ9ALJToy.jp_witness_false
#print axioms NockvmE2E.Z38.E2EJ9ALJToy.hQJ_jp
#print axioms NockvmE2E.Z38.E2EJ9ALJToy.jp_witnessQ
