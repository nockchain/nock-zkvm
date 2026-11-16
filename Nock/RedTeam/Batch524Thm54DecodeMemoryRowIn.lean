/-
  Nock/RedTeam/Batch524Thm54DecodeMemoryRowIn.lean

  **Fill the paper-`⊥` halves.**

  `decodeMemoryRowIn q forest` writes
  `read_root.memoryRecord.child := nounByFP q forest (record.child)`
  and `verify_child.memoryRecord.root := nounByFP q forest (record.root)`,
  `axis := leafAtomOf q record.axis`.
  `decodedSkeleton` uses the forest-aware decoder.

  `BindMemRec` follows from `recordHalfJoin_of_deployed` +
  `decode_fingerprint` + an axis-window hit.  `MemoryTreeBinds` is
  the remaining row binding (`BindMemoryRow`), compiled below.
-/
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.NockVMROM.Thm54.SemanticStrategy
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree
import Nock.RedTeam.Batch515Thm54MemoryTreeBinds
import Nock.RedTeam.Batch516Thm54ComputeJoinSound
import Nock.RedTeam.Batch523Thm54RecordHalfJoinDeployed
import Nock.NockVMROM.Thm54.P8Core.Batch524Thm54DecodeMemoryRowIn

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch524

open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.RedTeam.Batch515
open Nock.RedTeam.Batch516 (ServedFingerprint)
open scoped Classical

variable {K : Type} [Field K] [DecidableEq K]

theorem nounByFP_empty (q : ℕ) (fp : FP K) :
    nounByFP (K := K) q [] fp = Noun.atom 0 :=
  nounByFP_nil q fp

theorem decodeMemoryRow_eq_emptyForest (q : ℕ)
    (t : NTree (MState × DTmem K)) :
    decodeMemoryRow (K := K) q t = decodeMemoryRowIn q [] t :=
  rfl

theorem decodeMemoryRowIn_readRoot_child (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (data : DTmem K) (child : NTree (MState × DTmem K)) :
    ((decodeMemoryRowIn (K := K) q forest
        (.node (.read_root, data) [child])).memoryRecord
      (by simp [decodeMemoryRowIn_readRoot_state, memoryMemRecKind])).child =
      nounByFP q forest data.2.mem.child :=
  rfl

theorem decodeMemoryRowIn_readRoot_axis (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (data : DTmem K) (child : NTree (MState × DTmem K)) :
    ((decodeMemoryRowIn (K := K) q forest
        (.node (.read_root, data) [child])).memoryRecord
      (by simp [decodeMemoryRowIn_readRoot_state, memoryMemRecKind])).axis =
      leafAtomOf q data.2.mem.axis :=
  rfl

theorem decodeMemoryRowIn_verifyChild_root (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (data : DTmem K) (child : NTree (MState × DTmem K)) :
    ((decodeMemoryRowIn (K := K) q forest
        (.node (.verify_child, data) [child])).memoryRecord
      (by simp [decodeMemoryRowIn_verifyChild_state, memoryMemRecKind])).root =
      nounByFP q forest data.2.mem.root :=
  rfl

theorem decodeMemoryRowIn_verifyChild_axis (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (data : DTmem K) (child : NTree (MState × DTmem K)) :
    ((decodeMemoryRowIn (K := K) q forest
        (.node (.verify_child, data) [child])).memoryRecord
      (by simp [decodeMemoryRowIn_verifyChild_state, memoryMemRecKind])).axis =
      leafAtomOf q data.2.mem.axis :=
  rfl

/-- Axis lands in `[0, q)` so `BindMemRec`'s `r.axis = (s.axis : K)`. -/
def AxisInWindow (q : ℕ) (v : K) : Prop :=
  ∃ k : ℕ, k < q ∧ (k : K) = v

theorem bindMemRec_axis_of_window {q : ℕ} {v : K}
    (h : AxisInWindow q v) :
    v = (leafAtomOf q v : K) :=
  (leafAtomOf_cast h).symm

/-- `BindMemRec` on a `read_root` row after the forest fill, given the
    served child hit, parent fingerprint equation, and axis window. -/
theorem bindMemRec_readRoot_of_fill {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (data : DTmem K) (child : NTree (MState × DTmem K))
    (hroot : bindFP z (decodeNoun q child) data.2.mem.root)
    (hchild : ServedFingerprint forest data.2.mem.child)
    (haxis : AxisInWindow q data.2.mem.axis)
    (hstruct : ∀ t ∈ bfsForest forest, MemoryFingerprintStructure z t)
    (hleaves : ∀ t ∈ bfsForest forest, MemoryLeafAtomsRealized q t) :
    BindMemRec z
      ((decodeMemoryRowIn (K := K) q forest
          (.node (.read_root, data) [child])).memoryRecord
        (by simp [decodeMemoryRowIn_readRoot_state, memoryMemRecKind]))
      data.2.mem := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [decodeMemoryRowIn] using hroot
  · simpa [decodeMemoryRowIn] using
      bindFP_of_nounByFP_hit hz hstruct hleaves hchild
  · simpa [decodeMemoryRowIn] using bindMemRec_axis_of_window haxis

theorem bindMemRec_verifyChild_of_fill {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (data : DTmem K) (child : NTree (MState × DTmem K))
    (hroot : ServedFingerprint forest data.2.mem.root)
    (hchild : bindFP z (decodeNoun q child) data.2.mem.child)
    (haxis : AxisInWindow q data.2.mem.axis)
    (hstruct : ∀ t ∈ bfsForest forest, MemoryFingerprintStructure z t)
    (hleaves : ∀ t ∈ bfsForest forest, MemoryLeafAtomsRealized q t) :
    BindMemRec z
      ((decodeMemoryRowIn (K := K) q forest
          (.node (.verify_child, data) [child])).memoryRecord
        (by simp [decodeMemoryRowIn_verifyChild_state, memoryMemRecKind]))
      data.2.mem := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [decodeMemoryRowIn] using
      bindFP_of_nounByFP_hit hz hstruct hleaves hroot
  · simpa [decodeMemoryRowIn] using hchild
  · simpa [decodeMemoryRowIn] using bindMemRec_axis_of_window haxis

/-- Local facts `BindMemoryRow` reads off `Fmem` + the paper-`⊥` fill. -/
def MemoryNodeFacts (z : K) (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (node : NTree (MState × DTmem K)) : Prop :=
  node.label.2.1.z = z ∧
    node.label.2.2.st = node.label.1 ∧
    eqBlk node.label.2.1 node.label.2.2 ∧
    childLinkMem node.label (fun i : Fin 2 => node.childLabel i) ∧
    node.label.2.2.ver = decide (node.label.1 = .read_root) ∧
    (node.label.1 = .read_root → ServedFingerprint forest node.label.2.2.mem.child) ∧
    (node.label.1 = .verify_child → ServedFingerprint forest node.label.2.2.mem.root) ∧
    (memoryMemRecKind node.label.1 = .active → AxisInWindow q node.label.2.2.mem.axis)

/-- `Fmem` at every node of an `RVTWithArity` tree, plus the honest `ver`
    pin and the paper-`⊥` served/axis windows. -/
theorem memoryNodeFacts_of_rvt {z : K} {q : ℕ}
    {forest : List (NTree (MState × DTmem K))}
    {t : NTree (MState × DTmem K)}
    (htop : RVTWithArity (Fmem (K := K)) t)
    (hseed : ∀ node, InTree t node → node.label.2.1.z = z)
    (hver : ∀ node, InTree t node →
      node.label.2.2.ver = decide (node.label.1 = .read_root))
    (hservedChild : ∀ node, InTree t node → node.label.1 = .read_root →
      ServedFingerprint forest node.label.2.2.mem.child)
    (hservedRoot : ∀ node, InTree t node → node.label.1 = .verify_child →
      ServedFingerprint forest node.label.2.2.mem.root)
    (haxis : ∀ node, InTree t node →
      memoryMemRecKind node.label.1 = .active →
        AxisInWindow q node.label.2.2.mem.axis)
    {node : NTree (MState × DTmem K)} (hin : InTree t node) :
    MemoryNodeFacts z q forest node := by
  have hF :=
    ((RVT_iff_forall_InTree (F := Fmem (K := K)) t).mp htop.rvt node hin).1
  refine ⟨hseed node hin, hF.1, hF.2.1.2.1, hF.2.2.2, hver node hin,
    hservedChild node hin, hservedRoot node hin, haxis node hin⟩

theorem bindMemoryRow_halt {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (data : DTmem K)
    (hfacts : MemoryNodeFacts z q forest (.node (.halt, data) []))
    (hatom : data.2.pt.noun.size = z ∧ data.2.pt.noun.dyck = 0)
    (hleaves : MemoryLeafAtomsRealized (K := K) q (.node (.halt, data) [])) :
    BindMemoryRowA z
      (decodeMemoryRowIn (K := K) q forest (.node (.halt, data) []))
      (.halt, data) := by
  obtain ⟨hseed, hst, heq, _, hver, _, _, _⟩ := hfacts
  have heq' : eqBlk data.1 data.2 := heq
  have hstD : data.2.st = .halt := by simpa using hst
  unfold eqBlk at heq'
  rw [hstD] at heq'
  refine ⟨rfl, hseed, hst, ?_, ?_, ?_, hver⟩
  · simpa [decodeMemoryRowIn] using bindFP_halt_parent hatom hleaves
  · intro i
    have hfo : ¬ (i : ℕ) < fanoutMem .halt := by
      simp [fanoutMem]
    simp only [hfo, ↓reduceDIte]
    fin_cases i
    · exact heq'.2.2.2.2.1
    · exact heq'.2.2.2.2.2.1
  · have hpad : ¬ memoryMemRecKind (decodeMemoryRowIn (K := K) q forest
        (.node (.halt, data) [])).state = .active := by
      simp [decodeMemoryRowIn, memoryMemRecKind]
    simp only [hpad, ↓reduceDIte]
    exact heq'.2.2.2.2.2.2

theorem bindMemoryRow_decompose {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (data : DTmem K)
    (left right : NTree (MState × DTmem K))
    (hfacts : MemoryNodeFacts z q forest (.node (.decompose, data) [left, right]))
    (hL : MemoryFingerprintStructure z left)
    (hR : MemoryFingerprintStructure z right)
    (hleavesL : MemoryLeafAtomsRealized q left)
    (hleavesR : MemoryLeafAtomsRealized q right) :
    BindMemoryRowA z
      (decodeMemoryRowIn (K := K) q forest (.node (.decompose, data) [left, right]))
      (.decompose, data) := by
  obtain ⟨hseed, hst, heq, hlink, hver, _, _, _⟩ := hfacts
  have heq' : eqBlk data.1 data.2 := heq
  have hstD : data.2.st = .decompose := by simpa using hst
  unfold eqBlk at heq'
  rw [hstD] at heq'
  have hleftLink := hlink 0 (by simp [fanoutMem])
  have hrightLink := hlink 1 (by simp [fanoutMem])
  simp only [NTree.childLabel, NTree.childOpt, NTree.children_node,
    Fin.val_zero, Fin.val_one, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.map_some, memCell,
    Option.some.injEq] at hleftLink hrightLink
  have hleftCell : left.label.2.2.pt = data.2.lc := hleftLink
  have hrightCell : right.label.2.2.pt = data.2.rc := hrightLink
  refine ⟨rfl, hseed, hst, ?_, ?_, ?_, hver⟩
  · have hencL := decode_fingerprint hz hL hleavesL
    have hencR := decode_fingerprint hz hR hleavesR
    simp only [bindFP, decodeMemoryRowIn, GlobalCarryRecognizer.enc_cons hz]
    rw [heq'.1, show data.1.z = z from hseed]
    rw [← congrArg Cell.noun hleftCell, ← congrArg Cell.noun hrightCell]
    simp [memoryTreeRootFP] at hencL hencR
    rw [← hencL, ← hencR]
  · intro i
    have hfo : (i : ℕ) < fanoutMem .decompose := i.isLt
    simp only [hfo, ↓reduceDIte, decodeMemoryRowIn]
    fin_cases i
    · simp only [Fin.val_zero, ↓reduceIte, memoryChildCell, bindFP]
      have hencL := decode_fingerprint hz hL hleavesL
      rw [← congrArg Cell.noun hleftCell]
      simpa [memoryTreeRootFP] using hencL.symm
    · simp only [Fin.val_one, ↓reduceIte, memoryChildCell, bindFP]
      have hencR := decode_fingerprint hz hR hleavesR
      rw [← congrArg Cell.noun hrightCell]
      simpa [memoryTreeRootFP] using hencR.symm
  · have hpad : ¬ memoryMemRecKind (decodeMemoryRowIn (K := K) q forest
        (.node (.decompose, data) [left, right])).state = .active := by
      simp [decodeMemoryRowIn, memoryMemRecKind]
    simp only [hpad, ↓reduceDIte]
    exact heq'.2.2.2

/-- The decoded skeleton binds the a-bearing rows of
    `execOfTraces` (`BindMemoryRowA`); the row-level `MemoryTreeBinds` of the executed rows
    needs the (parked) `specialize`/`encodeRow` transport.  Provisional local definition. -/
inductive MemoryTreeBindsA (z : K) :
    NTree MemoryRowSkeleton →
      NTree (MemoryTable.MState × MemoryTable.DTmem K) → Prop
  | node {s sc row rc}
      (shape : sc.length = MemoryTable.fanoutMem s.state)
      (rowBinding : BindMemoryRowA z s row)
      (children : List.Forall₂ (MemoryTreeBindsA z) sc rc) :
      MemoryTreeBindsA z (.node s sc) (.node row rc)

theorem bindMemoryRow_readRoot {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (data : DTmem K)
    (child : NTree (MState × DTmem K))
    (hfacts : MemoryNodeFacts z q forest (.node (.read_root, data) [child]))
    (hchild : MemoryFingerprintStructure z child)
    (hleavesC : MemoryLeafAtomsRealized q child)
    (hstructF : ForestFPFacts z q forest) :
    BindMemoryRowA z
      (decodeMemoryRowIn (K := K) q forest (.node (.read_root, data) [child]))
      (.read_root, data) := by
  obtain ⟨hseed, hst, heq, hlink, hver, hservedC, _, haxis⟩ := hfacts
  have heq' : eqBlk data.1 data.2 := heq
  have hstD : data.2.st = .read_root := by simpa using hst
  unfold eqBlk at heq'
  rw [hstD] at heq'
  have hchildLink := hlink 0 (by simp [fanoutMem])
  simp only [NTree.childLabel, NTree.childOpt, NTree.children_node,
    Fin.val_zero, List.getElem?_cons_zero, Option.map_some, memCell,
    Option.some.injEq] at hchildLink
  have hchildCell : child.label.2.2.pt = data.2.lc := hchildLink
  have henc := decode_fingerprint hz hchild hleavesC
  have hroot : bindFP z (decodeNoun q child) data.2.mem.root := by
    rw [bindFP, heq'.2.2.2.2.1, heq'.1, ← congrArg Cell.noun hchildCell]
    simpa [memoryTreeRootFP] using henc.symm
  have hmem :=
    bindMemRec_readRoot_of_fill hz forest data child hroot
      (hservedC rfl) (haxis (by simp [memoryMemRecKind]))
      hstructF.1 hstructF.2
  refine ⟨rfl, hseed, hst, ?_, ?_, ?_, hver⟩
  · simp only [bindFP, decodeMemoryRowIn]
    rw [heq'.1, ← congrArg Cell.noun hchildCell]
    simpa [memoryTreeRootFP] using henc.symm
  · intro i
    fin_cases i
    · have hfo : (0 : ℕ) < fanoutMem .read_root := by simp [fanoutMem]
      simp only [hfo, ↓reduceDIte, decodeMemoryRowIn, memoryChildCell]
      rw [bindFP, ← congrArg Cell.noun hchildCell]
      simpa [memoryTreeRootFP] using henc.symm
    · have hfo : ¬ (1 : ℕ) < fanoutMem .read_root := by simp [fanoutMem]
      simp only [hfo, ↓reduceDIte, memoryChildCell]
      exact heq'.2.2.2.2.2
  · rw [dif_pos (by simp [decodeMemoryRowIn, memoryMemRecKind])]
    exact hmem

theorem bindMemoryRow_verifyChild {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (data : DTmem K)
    (child : NTree (MState × DTmem K))
    (hfacts : MemoryNodeFacts z q forest (.node (.verify_child, data) [child]))
    (hchild : MemoryFingerprintStructure z child)
    (hleavesC : MemoryLeafAtomsRealized q child)
    (hstructF : ForestFPFacts z q forest) :
    BindMemoryRowA z
      (decodeMemoryRowIn (K := K) q forest (.node (.verify_child, data) [child]))
      (.verify_child, data) := by
  obtain ⟨hseed, hst, heq, hlink, hver, _, hservedR, haxis⟩ := hfacts
  have heq' : eqBlk data.1 data.2 := heq
  have hstD : data.2.st = .verify_child := by simpa using hst
  unfold eqBlk at heq'
  rw [hstD] at heq'
  have hchildLink := hlink 0 (by simp [fanoutMem])
  simp only [NTree.childLabel, NTree.childOpt, NTree.children_node,
    Fin.val_zero, List.getElem?_cons_zero, Option.map_some, memCell,
    Option.some.injEq] at hchildLink
  have hchildCell : child.label.2.2.pt = data.2.lc := hchildLink
  have henc := decode_fingerprint hz hchild hleavesC
  have hch : bindFP z (decodeNoun q child) data.2.mem.child := by
    rw [bindFP, heq'.2.2.2.2.1, heq'.1, ← congrArg Cell.noun hchildCell]
    simpa [memoryTreeRootFP] using henc.symm
  have hmem :=
    bindMemRec_verifyChild_of_fill hz forest data child
      (hservedR rfl) hch (haxis (by simp [memoryMemRecKind]))
      hstructF.1 hstructF.2
  refine ⟨rfl, hseed, hst, ?_, ?_, ?_, hver⟩
  · simp only [bindFP, decodeMemoryRowIn]
    rw [heq'.1, ← congrArg Cell.noun hchildCell]
    simpa [memoryTreeRootFP] using henc.symm
  · intro i
    fin_cases i
    · have hfo : (0 : ℕ) < fanoutMem .verify_child := by simp [fanoutMem]
      simp only [hfo, ↓reduceDIte, decodeMemoryRowIn, memoryChildCell]
      rw [bindFP, ← congrArg Cell.noun hchildCell]
      simpa [memoryTreeRootFP] using henc.symm
    · have hfo : ¬ (1 : ℕ) < fanoutMem .verify_child := by simp [fanoutMem]
      simp only [hfo, ↓reduceDIte, memoryChildCell]
      exact heq'.2.2.2.2.2
  · rw [dif_pos (by simp [decodeMemoryRowIn, memoryMemRecKind])]
    exact hmem

/-- `BindMemoryRow` at a reconstructed node. -/
def RemainingBindMemoryRow (z : K) (q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (MState × DTmem K)) : Prop :=
  BindMemoryRowA z (decodeMemoryRowIn q forest t) t.label

theorem remainingBindMemoryRow_of_fill {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (MState × DTmem K))
    (hstruct : MemoryFingerprintStructure z t)
    (hleaves : MemoryLeafAtomsRealized q t)
    (hfacts : MemoryNodeFacts z q forest t)
    (hstructF : ForestFPFacts z q forest) :
    RemainingBindMemoryRow z q forest t := by
  cases hstruct with
  | halt data atomShape =>
      exact bindMemoryRow_halt forest data hfacts atomShape hleaves
  | decompose data left right consEq hL hR =>
      exact bindMemoryRow_decompose hz forest data left right hfacts hL hR
        hleaves.1 hleaves.2
  | readRoot data child passEq childStructure =>
      exact bindMemoryRow_readRoot hz forest data child hfacts childStructure
        hleaves hstructF
  | verifyChild data child passEq childStructure =>
      exact bindMemoryRow_verifyChild hz forest data child hfacts childStructure
        hleaves hstructF

/-- **`MemoryTreeBinds`** after the forest fill: row binding +
    `children.length = fanoutMem` from the reconstructed shape. -/
theorem memoryTreeBinds_of_fill {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (MState × DTmem K))
    (hstruct : MemoryFingerprintStructure z t)
    (hleaves : MemoryLeafAtomsRealized q t)
    (hfacts : ∀ node, InTree t node → MemoryNodeFacts z q forest node)
    (hstructF : ForestFPFacts z q forest) :
    MemoryTreeBindsA z (decodeMemoryTree q forest t) t := by
  cases hstruct with
  | halt data atomShape =>
      simp only [decodeMemoryTree]
      exact MemoryTreeBindsA.node (by simp [decodeMemoryRowIn, fanoutMem])
        (bindMemoryRow_halt forest data (hfacts _ (InTree.here _)) atomShape hleaves)
        .nil
  | decompose data left right consEq hL hR =>
      have hhere := hfacts _ (InTree.here _)
      have ihL := memoryTreeBinds_of_fill hz forest left hL hleaves.1
        (fun n hn => hfacts n (InTree.sub (by simp) hn)) hstructF
      have ihR := memoryTreeBinds_of_fill hz forest right hR hleaves.2
        (fun n hn => hfacts n (InTree.sub (by simp [List.mem_cons]) hn)) hstructF
      simp only [decodeMemoryTree]
      exact MemoryTreeBindsA.node (by simp [decodeMemoryRowIn, fanoutMem])
        (bindMemoryRow_decompose hz forest data left right hhere hL hR
          hleaves.1 hleaves.2)
        (.cons ihL (.cons ihR .nil))
  | readRoot data child passEq childStructure =>
      have hhere := hfacts _ (InTree.here _)
      have ih := memoryTreeBinds_of_fill hz forest child childStructure hleaves
        (fun n hn => hfacts n (InTree.sub (by simp) hn)) hstructF
      simp only [decodeMemoryTree]
      exact MemoryTreeBindsA.node (by simp [decodeMemoryRowIn, fanoutMem])
        (bindMemoryRow_readRoot hz forest data child hhere childStructure
          hleaves hstructF)
        (.cons ih .nil)
  | verifyChild data child passEq childStructure =>
      have hhere := hfacts _ (InTree.here _)
      have ih := memoryTreeBinds_of_fill hz forest child childStructure hleaves
        (fun n hn => hfacts n (InTree.sub (by simp) hn)) hstructF
      simp only [decodeMemoryTree]
      exact MemoryTreeBindsA.node (by simp [decodeMemoryRowIn, fanoutMem])
        (bindMemoryRow_verifyChild hz forest data child hhere childStructure
          hleaves hstructF)
        (.cons ih .nil)

private theorem forall₂_map_self {α β : Type*} {R : β → α → Prop}
    (f : α → β) : ∀ l : List α, (∀ x ∈ l, R (f x) x) →
    List.Forall₂ R (l.map f) l
  | [], _ => .nil
  | x :: xs, h =>
      .cons (h x (by simp)) (forall₂_map_self f xs fun y hy => h y (by simp [hy]))

/-- Forest form: every reconstructed tree binds. -/
theorem memoryForestBinds_of_fill {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (hstruct : ∀ t ∈ forest, MemoryFingerprintStructure z t)
    (hleaves : ∀ t ∈ forest, MemoryLeafAtomsRealized q t)
    (hfacts : ∀ t ∈ forest, ∀ node, InTree t node →
      MemoryNodeFacts z q forest node)
    (hstructF : ForestFPFacts z q forest) :
    List.Forall₂ (MemoryTreeBindsA z) (decodedMemoryForest q forest) forest := by
  simpa [decodedMemoryForest] using
    forall₂_map_self (decodeMemoryTree (K := K) q forest) forest fun t ht =>
      memoryTreeBinds_of_fill hz forest t (hstruct t ht) (hleaves t ht)
        (hfacts t ht) hstructF

/-- Topology + shared seed + honest `ver` + paper-`⊥` windows ⇒ `MemoryTreeBinds`. -/
theorem memoryTreeBinds_of_topology {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (MState × DTmem K))
    (htop : RVTWithArity (Fmem (K := K)) t)
    (hseed : ∀ node, InTree t node → node.label.2.1.z = z)
    (hleaves : MemoryLeafAtomsRealized q t)
    (hver : ∀ node, InTree t node →
      node.label.2.2.ver = decide (node.label.1 = .read_root))
    (hservedChild : ∀ node, InTree t node → node.label.1 = .read_root →
      ServedFingerprint forest node.label.2.2.mem.child)
    (hservedRoot : ∀ node, InTree t node → node.label.1 = .verify_child →
      ServedFingerprint forest node.label.2.2.mem.root)
    (haxis : ∀ node, InTree t node →
      memoryMemRecKind node.label.1 = .active →
        AxisInWindow q node.label.2.2.mem.axis)
    (hstructF : ForestFPFacts z q forest) :
    MemoryTreeBindsA z (decodeMemoryTree q forest t) t :=
  memoryTreeBinds_of_fill hz forest t
    (MemoryFingerprintStructure.of_rvtWithArity z t htop hseed) hleaves
    (fun node hin =>
      memoryNodeFacts_of_rvt htop hseed hver hservedChild hservedRoot haxis hin)
    hstructF

/-- `memoryNodeFacts_of_rvt` on the β-free predicate (M′): the facts it reads off `Fmem` are
exactly `FmemTopo`'s conjuncts (state, `eqBlk`, child link). -/
theorem memoryNodeFacts_of_rvt' {z : K} {q : ℕ}
    {forest : List (NTree (MState × DTmem K))}
    {t : NTree (MState × DTmem K)}
    (htop : RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t)
    (hseed : ∀ node, InTree t node → node.label.2.1.z = z)
    (hver : ∀ node, InTree t node →
      node.label.2.2.ver = decide (node.label.1 = .read_root))
    (hservedChild : ∀ node, InTree t node → node.label.1 = .read_root →
      ServedFingerprint forest node.label.2.2.mem.child)
    (hservedRoot : ∀ node, InTree t node → node.label.1 = .verify_child →
      ServedFingerprint forest node.label.2.2.mem.root)
    (haxis : ∀ node, InTree t node →
      memoryMemRecKind node.label.1 = .active →
        AxisInWindow q node.label.2.2.mem.axis)
    {node : NTree (MState × DTmem K)} (hin : InTree t node) :
    MemoryNodeFacts z q forest node := by
  have hF :=
    ((RVT_iff_forall_InTree (F := MemoryTopoBetaFree.FmemTopo (K := K)) t).mp
      htop.rvt node hin).1
  exact ⟨hseed node hin, hF.1, hF.2.1, hF.2.2.2, hver node hin,
    hservedChild node hin, hservedRoot node hin, haxis node hin⟩

/-- `memoryTreeBinds_of_topology` with `RVTWithArity Fmem t` weakened to the β-free
`RVTWithArity FmemTopo t` (no `Vmem`/`interV`); every other hypothesis unchanged.  Binding never
reads the `intermediate` accumulator or the inputs' `β` (`Batch715.bindMemoryRow_beta_free`), so the
β-free topology suffices. -/
theorem memoryTreeBinds_of_topology' {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (MState × DTmem K))
    (htop : RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t)
    (hseed : ∀ node, InTree t node → node.label.2.1.z = z)
    (hleaves : MemoryLeafAtomsRealized q t)
    (hver : ∀ node, InTree t node →
      node.label.2.2.ver = decide (node.label.1 = .read_root))
    (hservedChild : ∀ node, InTree t node → node.label.1 = .read_root →
      ServedFingerprint forest node.label.2.2.mem.child)
    (hservedRoot : ∀ node, InTree t node → node.label.1 = .verify_child →
      ServedFingerprint forest node.label.2.2.mem.root)
    (haxis : ∀ node, InTree t node →
      memoryMemRecKind node.label.1 = .active →
        AxisInWindow q node.label.2.2.mem.axis)
    (hstructF : ForestFPFacts z q forest) :
    MemoryTreeBindsA z (decodeMemoryTree q forest t) t :=
  memoryTreeBinds_of_fill hz forest t
    (MemoryTopoBetaFree.memoryFingerprintStructure_of_rvtWithArity_topo z t htop hseed) hleaves
    (fun _ hin =>
      memoryNodeFacts_of_rvt' htop hseed hver hservedChild hservedRoot haxis hin)
    hstructF

theorem historical_decodeMemoryRow_readRoot_child_atom0
    (q : ℕ) (data : DTmem K) (child : NTree (MState × DTmem K)) :
    ((decodeMemoryRow (K := K) q (.node (.read_root, data) [child])).memoryRecord
      (by simp [decodeMemoryRow, decodeMemoryRowIn_readRoot_state,
        memoryMemRecKind])).child =
      Noun.atom 0 :=
  nounByFP_empty q data.2.mem.child

end Nock.RedTeam.Batch524

#print axioms Nock.RedTeam.Batch524.nounByFP_empty
#print axioms Nock.RedTeam.Batch524.decodeMemoryRowIn_readRoot_child
#print axioms Nock.RedTeam.Batch524.bindFP_of_nounByFP_hit
#print axioms Nock.RedTeam.Batch524.bindMemRec_readRoot_of_fill
#print axioms Nock.RedTeam.Batch524.bindMemRec_verifyChild_of_fill
#print axioms Nock.RedTeam.Batch524.bindMemoryRow_halt
#print axioms Nock.RedTeam.Batch524.bindMemoryRow_decompose
#print axioms Nock.RedTeam.Batch524.bindMemoryRow_readRoot
#print axioms Nock.RedTeam.Batch524.bindMemoryRow_verifyChild
#print axioms Nock.RedTeam.Batch524.memoryTreeBinds_of_fill
#print axioms Nock.RedTeam.Batch524.memoryForestBinds_of_fill
#print axioms Nock.RedTeam.Batch524.historical_decodeMemoryRow_readRoot_child_atom0
#print axioms Nock.RedTeam.Batch524.memoryTreeBinds_of_topology'
