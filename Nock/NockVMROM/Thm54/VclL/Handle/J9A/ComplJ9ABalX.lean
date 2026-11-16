/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalX.lean

* `xRecsA D bs`: J-8's `xRecs` with the compute part the twin `.x` consumes (`xConsumesX9`) at the base columns
    `bs` (the honest value: `basesA9 …` of the twin rows).
  * **`mh_eq_cntA`**: `(j9aDataOf …).mh.getD j 0 = cnt (xRecsA DA basesA) j` at every in-range serial (twin of
    `ComplJ8Data.mh_eq_cnt`).  This is the counting half of `hGx` (the cell handle-export terminal is the
    `mh`-weighted sum, `ComplJ8OfBalG.chT_eq`, generic in the record); the consumer half (the twin compute's `.x`
    total `ρ 3` against `wsum` of the compute records) is proved separately.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ADataRec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalX

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf xConsumesX9 mhCountsX9 basesA9)
open Nock.V1J8.Gen (WRow bump)

noncomputable section

section Recs
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **The J-9 A export consumers**: the twin compute's `.x` consumes at the base columns `bs`, the cell-walk rows,
the J export reads. -/
def xRecsA (D : J8Data p Rg fuel s f r) (bs : List (ℕ → ZMod p)) : List NamedRecs :=
  [⟨"compute", bs.flatMap fun b => xConsumesX9 p (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))⟩,
   ⟨"walk", cellPairs D.cells (D.ws.map WRow.node)⟩,
   ⟨"J", D.jrows.flatMap fun row => (Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row).map fun κ =>
      ((κ.headD 0).val, 1)⟩]

end Recs

section Counts
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- `mhCountsX9` as two bumps (the body of J-8's `mh_eq_cnt`, at the twin consumes). -/
theorem mhCountsX9_eq (cs : List Noun) (bs : List (ℕ → ZMod p)) (ws : List WRow) : mhCountsX9 p cs bs ws =
    bumpAll (bumpAll (Array.replicate cs.length 0)
      (bs.flatMap fun b => xConsumesX9 p (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))))
      (cellPairs cs (ws.map WRow.node)) := by
  unfold mhCountsX9
  simp only
  have hb : ∀ (a : Array ℕ) (bs : List (ℕ → ZMod p)),
      bs.foldl (fun a b => (xConsumesX9 p (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))).foldl
        (fun a q => bump a q.1 q.2) a) a =
      bumpAll a (bs.flatMap fun b => xConsumesX9 p (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))) := by
    intro a bs
    induction bs generalizing a with
    | nil => rfl
    | cons b bs ih => simp only [List.foldl_cons, List.flatMap_cons, bumpAll_append]; rw [ih]; rfl
  rw [hb]
  generalize bumpAll (Array.replicate cs.length 0) _ = a
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons, List.map_cons]
    rcases hw : w.node with v | ⟨x, y⟩
    · rw [ih]; simp [cellPairs]
    · rw [ih]; simp only [cellPairs, List.filterMap_cons]; rfl

/-- `mhJP` as a bump of the J export reads. -/
theorem mhJP_eq (mh : Array ℕ) (rows : List (Nock.Jet.ChipJ8.CRow (ZMod p))) : mhJP p mh rows =
    bumpAll mh (rows.flatMap fun row => (Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row).map fun κ =>
      ((κ.headD 0).val, 1)) := by
  unfold mhJP
  induction rows generalizing mh with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.foldl_cons, List.flatMap_cons, bumpAll_append]
    rw [ih]
    congr 1
    generalize Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row = ks
    induction ks generalizing mh with
    | nil => rfl
    | cons κ ks ihk => simp only [List.foldl_cons, List.map_cons]; rw [ihk]; rfl

/-- The honest twin base columns of the run. -/
abbrev basesA (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) : List (ℕ → ZMod p) :=
  basesA9 p (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
    (ComplJ9AChains.idOf9 p (j8DataOf p Rg Rt hgen).acs.length (j8DataOf p Rg Rt hgen).H
      (ComplJ9AData.fieldAx9 p (ComplJ9AGen.rowsOfT9 t)))
    (bfsForest [ComplJ9AGen.genX9T t])

/-- **The J-9 A `mh` is the count of the J-9 A export consumers** (twin compute `.x` consumes, cell-walk rows, J
export reads). -/
theorem mh_eq_cntA (j : ℕ) (hj : j < (j9aDataOf p Rg Rt hgen).cells.length) :
    (j9aDataOf p Rg Rt hgen).mh.getD j 0 =
      cnt (xRecsA (j9aDataOf p Rg Rt hgen) (basesA p Rg Rt hgen)) j := by
  rw [ComplJ9ADataRec.j9aDataOf_mh, mhJP_eq, mhCountsX9_eq, cnt_eq_sumAt]
  rw [bumpAll_getD _ _ _ (by rw [bumpAll_size, bumpAll_size, Array.size_replicate]; exact hj)]
  refine (congrArg (· + _) (bumpAll2_getD _ _ _ _ hj)).trans ?_
  simp only [xRecsA, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
  rfl

end Counts

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalX

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalX
#print axioms mhCountsX9_eq
#print axioms mhJP_eq
#print axioms mh_eq_cntA
end Axioms
