/-
 Nock/NockVMROM/Thm54/VclL/Handle/GenXDetRows.lean

 **The row arrays of a genuine tree on the fragment `{0, 7, 10, autocons}`.**

 Corollaries of `Nock.Edit.GenX.genuineNX_eq_genX` at the interface of `ComplJ8Data`:

 * `relabelT_eq_mapT` — the relabelling of `GenXDet` is `LocalVSX.mapT`.
 * `genuineNX_eq_mapT_genX` — a genuine tree rooted at `(s, f)`, `f ∈ P1Frag`, is
 `mapT SkelX.row t` for the generated tree `t` of `(s, f)`.
 * **`genuineNX_rowsOfT_eq`** — its `SkelX` lift has the same BFS row array:
 `rowsOfT (skelOfT T) = rowsOfT t`. (`rowsOfT` reads each node's `kids` field, so it is
 applied to the lift `skelOfT T`, whose `kids` are the node's children's labels.)
-/
import Nock.Edit.GenXDet
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenXDetRows

open Nock Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (mapT)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)

/-- `relabelT` is `LocalVSX.mapT`. -/
theorem relabelT_eq_mapT {α β : Type} (g : α → β) : ∀ t : NTree α, relabelT g t = mapT g t
  | .node l cs => by
    simp only [relabelT_node, mapT, NTree.node.injEq, true_and]
    exact List.map_congr_left (fun u _ => relabelT_eq_mapT g u)

/-- **The recon's form**: a genuine tree on the fragment is the generated tree, relabelled. -/
theorem genuineNX_eq_mapT_genX {R : Registry} (hR : R.Faithful) {f : Noun} (hfrag : P1Frag f)
    {n : ℕ} {s r : Noun} {t : NTree SkelX} {T : NTree RowX} (h : genX R n s f = some (t, r))
    (hT : GenuineNX R T) (hs : T.label.subject = s) (hf : T.label.formula = f) :
    T = mapT SkelX.row t := by
  rw [← relabelT_eq_mapT]
  exact (genuineNX_eq_genX hR hfrag h hT hs hf).1

/-- **The row arrays agree**: the `SkelX` lift of a genuine tree on the fragment has the
generated tree's BFS rows. -/
theorem genuineNX_rowsOfT_eq {R : Registry} (hR : R.Faithful) {f : Noun} (hfrag : P1Frag f)
    {n : ℕ} {s r : Noun} {t : NTree SkelX} {T : NTree RowX} (h : genX R n s f = some (t, r))
    (hT : GenuineNX R T) (hs : T.label.subject = s) (hf : T.label.formula = f) :
    rowsOfT (skelOfT T) = rowsOfT t := by
  rw [(genuineNX_eq_genX hR hfrag h hT hs hf).2]

end Nock.NockVMROM.Thm54.VclL.Handle.GenXDetRows

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenXDetRows.genuineNX_eq_mapT_genX
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenXDetRows.genuineNX_rowsOfT_eq
