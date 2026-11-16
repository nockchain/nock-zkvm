/-
  NockvmE2E/J8/HopsLit.lean

  `hopZero_of_tie`: the exe's literal check (`chipEqB c lit`, `chipsOk`) together with the kernel tie of the literal (`J8ChipsK.tieB s lit`, the per-literal
  `J8ChipsK_*` theorems) gives the (weakened, fields-only) `TieJ8.HopZero` for a loaded table.  No hypothesis on the loader's `sharedK`/`consK` tags.
-/
import NockvmE2E.J8.TieJ8
import NockvmE2E.Exec.J8ChipsK

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.J8.HopsLit
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.VC NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit
open NockvmE2E.J8.TieJ8

/-- `chipOfDag` splits into the bucket-wise parses that `HopZero` quotes -/
theorem chipOfDag_split (D : DagGates) (c0 : Chip) (h : chipOfDag D = some c0) :
    ∃ sh cb ce cm c1 c3 cq : List NockvmE2E.Emit.Ex,
      D.defs.mapM toEx = some sh ∧ D.base.mapM toEx = some cb ∧ D.ext.mapM toEx = some ce ∧ D.mixed.mapM toEx = some cm ∧
      D.ext1.mapM toEx = some c1 ∧ D.ext3.mapM toEx = some c3 ∧ D.eqc.mapM toEx = some cq ∧
      c0.shared = sh.toArray ∧ c0.cons.toList.map (·.e) = cb ++ ce ++ cm ++ c1 ++ c3 ++ cq := by
  cases hsh : D.defs.mapM toEx with
  | none => simp [chipOfDag, hsh] at h
  | some sh =>
  cases hb : D.base.mapM toEx with
  | none => simp [chipOfDag, hsh, hb, List.mapM_append] at h
  | some cb =>
  cases he : D.ext.mapM toEx with
  | none => simp [chipOfDag, hsh, hb, he, List.mapM_append] at h
  | some ce =>
  cases hm : D.mixed.mapM toEx with
  | none => simp [chipOfDag, hsh, hb, he, hm, List.mapM_append] at h
  | some cm =>
  cases h1 : D.ext1.mapM toEx with
  | none => simp [chipOfDag, hsh, hb, he, hm, h1, List.mapM_append] at h
  | some c1 =>
  cases h3 : D.ext3.mapM toEx with
  | none => simp [chipOfDag, hsh, hb, he, hm, h1, h3, List.mapM_append] at h
  | some c3 =>
  cases hq : D.eqc.mapM toEx with
  | none => simp [chipOfDag, hsh, hb, he, hm, h1, h3, hq, List.mapM_append] at h
  | some cq =>
    simp [chipOfDag, hsh, hb, he, hm, h1, h3, hq, List.mapM_append] at h
    subst h
    refine ⟨sh, cb, ce, cm, c1, c3, cq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [List.map_map, Function.comp_def]

/-- **hop 0 from the exe check**: the literal ties to the emitted DAG `s` (kernel, `tieB`) and the loaded chip passes `chipEqB` against the literal -/
theorem hopZero_of_tie (s : TSpec) (lit c : Chip) (h1 : tieB s lit = true) (h2 : chipEqB c lit = true) :
    HopZero c (emitDag s) jDers jMeta c.baseCols := by
  obtain ⟨c0, hc, hs, hcons⟩ := chipEqB_tie s lit c h1 h2
  obtain ⟨sh, cb, ce, cm, c1, c3, cq, hsh, hcb, hce, hcm, hc1, hc3, hcq, hs0, hc0⟩ := chipOfDag_split _ c0 hc
  refine ⟨{ c0 with baseCols := c.baseCols }, sh, cb, ce, cm, c1, c3, cq, hsh, hcb, hce, hcm, hc1, hc3, hcq, hs0, hc0, ?_, ?_, rfl⟩
  · exact hs
  · exact hcons

end NockvmE2E.J8.HopsLit

#print axioms NockvmE2E.J8.HopsLit.chipOfDag_split
#print axioms NockvmE2E.J8.HopsLit.hopZero_of_tie
