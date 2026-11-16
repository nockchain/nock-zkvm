/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9A.lean

  Extends `GenPortJ9.genJ9A_pointer_data`.

  * `mhCountsX9E_eq`: the executable `mhCountsX9E` (`V1J9A/GenJ9AX`) is `ComplJ9ADataRec.mhCountsX9` at `P`;
  * `basesX9_eq`: the executable twin base columns (`GenCompX9.basesX9`) are `basesA9` at `P`;
  * `hdlB_eq_hdlP`: `hdlB = hdlP P`;
  * **`genJ9AX_data`**: on a jet-free run at Goldilocks, the cell-walk rows / roots `ws kr`, the atom-walk rows /
    roots `vs krV`, the multiplicities `mx mxA mhA` and the handle multiplicity `mh` that `genJ9AX` builds are
    `j9aDataOf`'s.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ADataRec
import Nock.V1J9A.GenJ9AX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.V1J8.Gen (P stopEdges ptrE sxE hdlB idxN padN mxCounts wCounts walkGen lastIdxOf combP pairReads)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf readsA preadsA mhCountsX9 basesA9)

/-! ## 1. Per-field lemmas -/

theorem xConsumesX9E_eq (e : Nock.Reified.Env (ZMod P)) :
    Nock.V1J9A.GenJ9AX.xConsumesX9E e = ComplJ9ADataRec.xConsumesX9 P e := rfl

/-- **`mhCountsX9E` is `mhCountsX9` at `P`.** -/
theorem mhCountsX9E_eq (cs : List Noun) (bs : List (ℕ → ZMod P)) (ws : List Nock.V1J8.Gen.WRow) :
    Nock.V1J9A.GenJ9AX.mhCountsX9E cs bs ws = mhCountsX9 P cs bs ws := rfl

/-- **The executable twin base columns are `basesA9`.** -/
theorem basesX9_eq (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree ComplJ9AGen.LX9)) :
    Nock.V1J9A.GenCompX9.basesX9 H pd idOf W = basesA9 P H pd idOf W := by
  unfold Nock.V1J9A.GenCompX9.basesX9 basesA9
  refine List.map_congr_left fun j _ => ?_
  unfold Nock.V1J9A.GenCompX9.baseFn9 HonestTraceX9.baseT9
  funext c
  rw [Nock.V1J9A.FillX9.colX9E_eq]

theorem hdlB_eq_hdlP (cs acsL : List Noun) : hdlB cs acsL = ComplJ8Data.hdlP P cs acsL := by
  funext n
  cases n <;> rfl

/-! ## 2. At the run -/

section Run
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`genJ9AX`'s memory data is `j9aDataOf`'s** (Goldilocks, a jet-free run). -/
theorem genJ9AX_data (hpG : p = P) (hnc : Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t) = []) (χe : Nock.V1J8.Exe.CoinsE) :
    let rows := ComplJ8Data.rowsOfT t
    let rows9 := ComplJ9AGen.rowsOfT9 t
    let acsL := GenPortJ9.acsRun s f r t
    let cs := Nock.V1J8.Gen.cellsOfRoots (Nock.V1J8.Gen.rootsOf ⟨s, f, r⟩ rows)
    let H := hdlB cs acsL
    let pt := ptrE acsL (stopEdges rows)
    let pd := HonestPairX.pdX (sxE pt)
    let W9 := bfsForest [ComplJ9AGen.genX9T t]
    let fx := ComplJ9AData.fieldAx9 P rows9
    let idOf := ComplJ9AChains.idOf9 P acsL.length H fx
    let comp := Nock.V1J9A.GenCompX9.compGenX9 ⟨s, f, r⟩ H pd idOf W9 χe
    let wk := walkGen (cs.headD (.atom 0))
      (ComplJ9AReads.walkReadsX9 rows9 ++ ComplJ9AChainsRun.axChainReadsK9 rows9)
    let reads := pairReads H pd rows ++ ComplJ9AChainsRun.axReadsK9 P rows9
    let vk : List Nock.V1J8.Gen.WRow × ℕ := if reads.isEmpty then ([], 0) else walkGen padN reads
    let rIA : Noun → ℕ := fun n => if n = combP then lastIdxOf acsL combP else idxN acsL n
    wk.1 = (j9aDataOf p Rg Rt hgen).ws ∧ wk.2 = (j9aDataOf p Rg Rt hgen).kr ∧
    vk.1 = (j9aDataOf p Rg Rt hgen).vs ∧ vk.2 = (j9aDataOf p Rg Rt hgen).krV ∧
    mxCounts cs wk.1 = (j9aDataOf p Rg Rt hgen).mx ∧
    wCounts rIA acsL vk.1 = (j9aDataOf p Rg Rt hgen).mxA ∧
    wCounts rIA acsL vk.1 = (j9aDataOf p Rg Rt hgen).mhA ∧
    Nock.V1J9A.GenJ9AX.mhCountsX9E cs comp.bases wk.1 = (j9aDataOf p Rg Rt hgen).mh := by
  subst hpG
  obtain ⟨-, hcs, hacs⟩ := ComplJ9BClosed.genJ9A_data Rt hgen rfl hnc
  have hjr : (j8DataOf P Rg Rt hgen).jrows = [] := by
    show ComplJ8Data.mvFixP _ (Nock.Jet.ChipJ8.honestJ8G _ _ (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).dedup
      (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))) _ = []
    rw [hnc]; rfl
  have hH : hdlB (Nock.V1J8.Gen.cellsOfRoots (Nock.V1J8.Gen.rootsOf ⟨s, f, r⟩ (ComplJ8Data.rowsOfT t)))
      (GenPortJ9.acsRun s f r t) = (j8DataOf P Rg Rt hgen).H := by
    have hacs' : GenPortJ9.acsRun s f r t = (j8DataOf P Rg Rt hgen).acs := hacs
    rw [hdlB_eq_hdlP, hcs, hacs']; rfl
  obtain ⟨-, -, hpd⟩ := GenPortJ9.genJ9A_pointer_data Rt hgen rfl hnc
  have hacs' : GenPortJ9.acsRun s f r t = (j8DataOf P Rg Rt hgen).acs := hacs
  have hrows : (j8DataOf P Rg Rt hgen).rows = ComplJ8Data.rowsOfT t := rfl
  dsimp only
  rw [hH, hpd, hcs, hacs']
  have hbs := basesX9_eq (j8DataOf P Rg Rt hgen).H (j8DataOf P Rg Rt hgen).pd
    (ComplJ9AChains.idOf9 P (j8DataOf P Rg Rt hgen).acs.length (j8DataOf P Rg Rt hgen).H
      (ComplJ9AData.fieldAx9 P (ComplJ9AGen.rowsOfT9 t))) (bfsForest [ComplJ9AGen.genX9T t])
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  show Nock.V1J9A.GenJ9AX.mhCountsX9E _ (Nock.V1J9A.GenCompX9.basesX9 _ _ _ _) _ = ComplJ8Data.mhJP P _ _
  rw [hbs, hjr]
  rfl

end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A.mhCountsX9E_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A.basesX9_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A.hdlB_eq_hdlP
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A.genJ9AX_data
