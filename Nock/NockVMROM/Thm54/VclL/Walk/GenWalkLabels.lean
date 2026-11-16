/-
  Nock/NockVMROM/Thm54/VclL/Walk/GenWalkLabels.lean

  **The honest walk rows' fingerprint labels.**

  |bits|⟩)` (`WalkInstance.DT`).  **`dtW_child`**: the data of a trie child is exactly the in-gate
-/
import Nock.NockVMROM.Thm54.VclL.Walk.GenWalkRows
import Nock.NockVMROM.Thm54.VclL.Chips.RowBridgeW
import Nock.GlobalCarryRecognizer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.GenWalk

open Nock Nock.Walk Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.TraceGen
open Nock.ComputeTable (FP)

noncomputable section

variable {q : ℕ} {Kfp : Type} [Field Kfp] (z : Kfp) (cells : List Noun)

/-- The export key a walk row consumes: `(fp p, fp l, fp r, idx)`. -/
def keyW (t : NTree WN) : XKey Kfp :=
  (GlobalCarryRecognizer.enc z t.label.node, GlobalCarryRecognizer.enc z (hdN t.label.node),
    GlobalCarryRecognizer.enc z (tlN t.label.node), cells.idxOf t.label.node)

def dtW (t : NTree WN) : WalkVCL.DT q Kfp :=
  ⟨GlobalCarryRecognizer.enc z t.label.node, (axisFold t.label.bits : ZMod q),
    GlobalCarryRecognizer.enc z t.label.root, (cells.idxOf t.label.root : ZMod q),
    (t.label.bits.length : ZMod q)⟩

def lblW (t : NTree WN) : WalkVCL.LT q Kfp := ((t.label.cL, t.label.cR), dtW (q := q) z cells t)

theorem dtW_child (root l r : Noun) (bs : List Bool) (T : List (List Bool)) (b : Bool) :
    dtW (q := q) z cells (trie root (if b then r else l) (bs ++ [b]) (contT b T)) =
      Chips.ChipRAP.childDT (keyW z cells (trie root (.cell l r) bs T)) b
        (dtW (q := q) z cells (trie root (.cell l r) bs T)) := by
  obtain ⟨n1, b1, r1⟩ := trie_label root (if b then r else l) (bs ++ [b]) (contT b T)
  obtain ⟨n0, b0, r0⟩ := trie_label root (.cell l r) bs T
  simp only [dtW, keyW, Chips.ChipRAP.childDT, WalkVCL.tgt, WalkVCL.keyEdge, childOf, n1, b1, r1, n0, b0, r0,
    hdN, tlN, axisFold_append, WalkVCL.bitZ, List.length_append, List.length_singleton]
  congr 1
  · cases b <;> simp
  · cases b <;> push_cast <;> ring
  · push_cast; ring

/-- The root rows' data: prefix `1`, `len 0`, `node = root` (the root gate's values). -/
theorem dtW_root {t : NTree WN} (hb : t.label.bits = []) (hn : t.label.node = t.label.root) :
    (dtW (q := q) z cells t).pre = 1 ∧ (dtW (q := q) z cells t).len = 0 ∧
      (dtW (q := q) z cells t).node = (dtW (q := q) z cells t).root ∧
      (dtW (q := q) z cells t).ridx = ((keyW z cells t).2.2.2 : ZMod q) := by
  simp [dtW, keyW, hb, hn, axisFold]

end

end Nock.NockVMROM.Thm54.VclL.GenWalk
