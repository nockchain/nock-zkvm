/-
  NockvmE2E/Exec/Toy1XOk.lean   (Mathlib-free kernel facts about the generated literal `toy1X`)

  `j8ShapeOk toy1X`, `j8ShapeXOk toy1X`, `chipsOk`, `maskOk`, `numeralOk`, all by `decide +kernel`, split per conjunct.  The chip conjuncts (`chipCanon`, `chipNo63`, `chipReadsLtB`)
  go through the list twins of `ChipShapeL` (the audited `j8ShapeOk` is not edited: it is `rw`-ed with the bridged facts).  No `native_decide`.
-/
import NockvmE2E.Exec.Toy1X
import NockvmE2E.Exec.ChipShapeL

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.Toy1X
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8Shape NockvmE2E.Exec.ChipShapeL NockvmE2E.Exec.MaskOk

theorem tabs_list : toy1X.tabs.toList = [toy1T0, toy1T1, toy1T2, toy1T3] := rfl

theorem c0 : chipCanonL toy1T0.chip = true := (canonL_tags chipCompute toy1T0.chip.sharedK toy1T0.chip.consK).trans compute_canon
theorem c1 : chipCanonL toy1T1.chip = true := (canonL_tags chipCell toy1T1.chip.sharedK toy1T1.chip.consK).trans cell_canon
theorem c2 : chipCanonL toy1T2.chip = true := (canonL_tags chipWalkJ8_1 toy1T2.chip.sharedK toy1T2.chip.consK).trans walk1_canon
theorem c3 : chipCanonL toy1T3.chip = true := (canonL_tags chipAtom toy1T3.chip.sharedK toy1T3.chip.consK).trans atom_canon
theorem n0 : chipNo63L toy1T0.chip = true := (no63L_tags chipCompute toy1T0.chip.sharedK toy1T0.chip.consK).trans compute_no63
theorem n1 : chipNo63L toy1T1.chip = true := (no63L_tags chipCell toy1T1.chip.sharedK toy1T1.chip.consK).trans cell_no63
theorem n2 : chipNo63L toy1T2.chip = true := (no63L_tags chipWalkJ8_1 toy1T2.chip.sharedK toy1T2.chip.consK).trans walk1_no63
theorem n3 : chipNo63L toy1T3.chip = true := (no63L_tags chipAtom toy1T3.chip.sharedK toy1T3.chip.consK).trans atom_no63
theorem r0 : chipReadsLtL toy1T0.chip 123 33 19 = true := (readsL_tags chipCompute toy1T0.chip.sharedK toy1T0.chip.consK 123 33 19).trans compute_reads
theorem r1 : chipReadsLtL toy1T1.chip 242 18 19 = true := (readsL_tags chipCell toy1T1.chip.sharedK toy1T1.chip.consK 242 18 19).trans cell_reads
theorem r2 : chipReadsLtL toy1T2.chip 166 24 19 = true := (readsL_tags chipWalkJ8_1 toy1T2.chip.sharedK toy1T2.chip.consK 166 24 19).trans walk1_reads
theorem r3 : chipReadsLtL toy1T3.chip 349 36 19 = true := (readsL_tags chipAtom toy1T3.chip.sharedK toy1T3.chip.consK 349 36 19).trans atom_reads

theorem h_canon63 : (toy1X.tabs.all fun t => chipCanon t.chip && chipNo63 t.chip) = true := by
  rw [← Array.all_toList, tabs_list]
  simp only [List.all_cons, List.all_nil, Bool.and_true, chipCanon_eq, chipNo63_eq, c0, c1, c2, c3, n0, n1, n2, n3, Bool.and_self]

theorem h_reads : (toy1X.tabs.all fun t => chipReadsLtB t.chip (t.nc - t.npub) t.npub 19) = true := by
  rw [← Array.all_toList, tabs_list]
  simp only [List.all_cons, List.all_nil, Bool.and_true, chipReadsLt_eq]
  have e0 : chipReadsLtL toy1T0.chip (toy1T0.nc - toy1T0.npub) toy1T0.npub 19 = true := r0
  have e1 : chipReadsLtL toy1T1.chip (toy1T1.nc - toy1T1.npub) toy1T1.npub 19 = true := r1
  have e2 : chipReadsLtL toy1T2.chip (toy1T2.nc - toy1T2.npub) toy1T2.npub 19 = true := r2
  have e3 : chipReadsLtL toy1T3.chip (toy1T3.nc - toy1T3.npub) toy1T3.npub 19 = true := r3
  simp only [e0, e1, e2, e3, Bool.and_self]

theorem sh_params : paramsOk toy1X = true := by decide +kernel
theorem sh_tabs : tabsOk toy1X = true := by decide +kernel
theorem sh_layout : layoutShapeOk toy1X = true := by decide +kernel
theorem sh_mand : mandatoryOk toy1X = true := by decide +kernel
theorem sh_prek : preKindOk toy1X = true := by decide +kernel
theorem sh_orbit : orbitOk toy1X = true := by decide +kernel
theorem sh_width : widthOk toy1X = true := by decide +kernel
theorem sh_slot : slotOfOk toy1X = true := by decide +kernel
theorem sh_kind01 : (toy1X.tabs.all fun t => (List.range (t.nc - t.npub)).all fun c =>
    toy1X.colKind[t.col0 + c]! == 0 || toy1X.colKind[t.col0 + c]! == 1) = true := by decide +kernel
theorem sh_pre : (toy1X.pre.size == toy1X.nc && toy1X.pre.all (fun a => decide (a.size ≤ toy1X.hN + 1))) = true := by decide +kernel
theorem sh_preBased : (toy1X.pre.all (·.all fun x => VF.based x.toNat)) = true := by decide +kernel

theorem toy1X_shape : j8ShapeOk toy1X = true := by
  unfold j8ShapeOk
  rw [sh_params, sh_tabs, sh_layout, sh_mand, sh_prek, sh_orbit, sh_width, sh_slot, sh_kind01, h_canon63, h_reads]
  decide +kernel

theorem toy1X_shapeX : j8ShapeXOk toy1X = true := by decide +kernel
theorem toy1X_chips : chipsOk toy1X = true := by decide +kernel
theorem toy1X_mask : maskOk toy1X = true := by decide +kernel
theorem toy1X_numeral : numeralOk toy1X = true := by decide +kernel

end NockvmE2E.Exec.Toy1X

#print axioms NockvmE2E.Exec.Toy1X.toy1X_shape
#print axioms NockvmE2E.Exec.Toy1X.toy1X_shapeX
#print axioms NockvmE2E.Exec.Toy1X.toy1X_chips
#print axioms NockvmE2E.Exec.Toy1X.toy1X_mask
#print axioms NockvmE2E.Exec.Toy1X.toy1X_numeral
