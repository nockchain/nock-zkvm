/-
  Nock/NockVMROM/Thm54/P8Core/Batch1010Thm54AxisViewMemoryTreeBinds.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch1010Thm54AxisViewMemoryTreeBinds`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch1010Thm54AxisViewMemoryTreeBinds.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch524Thm54DecodeMemoryRowIn
import Nock.NockVMROM.Thm54.StrategyOfTracesR0A

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1010

open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.RedTeam.Batch516 (ServedFingerprint)
open Nock.RedTeam.Batch524 (ForestFPFacts bindFP_of_nounByFP_hit bindFP_halt_parent)
open scoped Classical
variable {K : Type} [Field K] [DecidableEq K]

def NodeFactsA (z : K)
    (forest : List (NTree (MState × DTmem K)))
    (node : NTree (MState × DTmem K)) : Prop :=
  node.label.2.1.z = z ∧
    node.label.2.2.st = node.label.1 ∧
    eqBlk node.label.2.1 node.label.2.2 ∧
    childLinkMem node.label (fun i : Fin 2 => node.childLabel i) ∧
    node.label.2.2.ver = decide (node.label.1 = .read_root) ∧
    (node.label.1 = .read_root → ServedFingerprint forest node.label.2.2.mem.child) ∧
    (node.label.1 = .verify_child → ServedFingerprint forest node.label.2.2.mem.root)

/-- **The a-bearing axis facts** of a node: on an active row the stored `(T, C')` are the Form R
encode of the supplied axis `ax node.label` at the row's own `λ` (`BindMemRow`'s two record
equations, `SemanticStrategy.BindMemRow`). -/
def AxisFacts (ax : MState × DTmem K → ℕ) (node : NTree (MState × DTmem K)) : Prop :=
  memoryMemRecKind node.label.1 = .active →
    node.label.2.2.mem.axis =
        formRT node.label.2.2.lambda (nockAxisOf ((ax node.label : ℕ) : K)) ∧
      node.label.2.2.cprime =
        formRC node.label.2.2.lambda (nockAxisOf ((ax node.label : ℕ) : K))

theorem nodeFactsA_of_rvt' {z : K}
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
    {node : NTree (MState × DTmem K)} (hin : InTree t node) :
    NodeFactsA z forest node := by
  have hF :=
    ((RVT_iff_forall_InTree (F := MemoryTopoBetaFree.FmemTopo (K := K)) t).mp
      htop.rvt node hin).1
  exact ⟨hseed node hin, hF.1, hF.2.1, hF.2.2.2, hver node hin,
    hservedChild node hin, hservedRoot node hin⟩

/-- `BindMemRow` on a `read_root` row: parent fingerprint equation, served child, and the a-bearing
axis facts. -/
theorem bindMemRow_readRoot_of_fill {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (data : DTmem K) (child : NTree (MState × DTmem K))
    (hroot : bindFP z (decodeNoun q child) data.2.mem.root)
    (hchild : ServedFingerprint forest data.2.mem.child)
    (hax : data.2.mem.axis = formRT data.2.lambda (nockAxisOf ((ax (.read_root, data) : ℕ) : K)) ∧
      data.2.cprime = formRC data.2.lambda (nockAxisOf ((ax (.read_root, data) : ℕ) : K)))
    (hstruct : ∀ t ∈ bfsForest forest, MemoryFingerprintStructure z t)
    (hleaves : ∀ t ∈ bfsForest forest, MemoryLeafAtomsRealized q t) :
    BindMemRow z
      ((decodeMemoryRowAx (K := K) q forest ax
          (.node (.read_root, data) [child])).memoryRecord
        (by simp [memoryMemRecKind]))
      data.2.mem data.2.cprime data.2.lambda := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [decodeMemoryRowAx] using hroot
  · simpa [decodeMemoryRowAx] using
      bindFP_of_nounByFP_hit hz hstruct hleaves hchild
  · simpa [decodeMemoryRowAx] using hax.1
  · simpa [decodeMemoryRowAx] using hax.2

theorem bindMemRow_verifyChild_of_fill {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (data : DTmem K) (child : NTree (MState × DTmem K))
    (hroot : ServedFingerprint forest data.2.mem.root)
    (hchild : bindFP z (decodeNoun q child) data.2.mem.child)
    (hax : data.2.mem.axis = formRT data.2.lambda (nockAxisOf ((ax (.verify_child, data) : ℕ) : K)) ∧
      data.2.cprime = formRC data.2.lambda (nockAxisOf ((ax (.verify_child, data) : ℕ) : K)))
    (hstruct : ∀ t ∈ bfsForest forest, MemoryFingerprintStructure z t)
    (hleaves : ∀ t ∈ bfsForest forest, MemoryLeafAtomsRealized q t) :
    BindMemRow z
      ((decodeMemoryRowAx (K := K) q forest ax
          (.node (.verify_child, data) [child])).memoryRecord
        (by simp [memoryMemRecKind]))
      data.2.mem data.2.cprime data.2.lambda := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [decodeMemoryRowAx] using
      bindFP_of_nounByFP_hit hz hstruct hleaves hroot
  · simpa [decodeMemoryRowAx] using hchild
  · simpa [decodeMemoryRowAx] using hax.1
  · simpa [decodeMemoryRowAx] using hax.2

theorem bindMemoryRow_halt {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (data : DTmem K)
    (hfacts : NodeFactsA z forest (.node (.halt, data) []))
    (hatom : data.2.pt.noun.size = z ∧ data.2.pt.noun.dyck = 0)
    (hleaves : MemoryLeafAtomsRealized (K := K) q (.node (.halt, data) [])) :
    BindMemoryRow z
      (decodeMemoryRowAx (K := K) q forest ax (.node (.halt, data) []))
      (.halt, data) := by
  obtain ⟨hseed, hst, heq, _, hver, _, _⟩ := hfacts
  have heq' : eqBlk data.1 data.2 := heq
  have hstD : data.2.st = .halt := by simpa using hst
  unfold eqBlk at heq'
  rw [hstD] at heq'
  refine ⟨rfl, hseed, hst, ?_, ?_, ?_, hver⟩
  · simpa [decodeMemoryRowAx] using bindFP_halt_parent hatom hleaves
  · intro i
    have hfo : ¬ (i : ℕ) < fanoutMem .halt := by
      simp [fanoutMem]
    simp only [hfo, ↓reduceDIte]
    fin_cases i
    · exact heq'.2.2.2.2.1
    · exact heq'.2.2.2.2.2.1
  · have hpad : ¬ memoryMemRecKind (decodeMemoryRowAx (K := K) q forest ax
        (.node (.halt, data) [])).state = .active := by
      simp [decodeMemoryRowAx, memoryMemRecKind]
    simp only [hpad, ↓reduceDIte]
    exact heq'.2.2.2.2.2.2

theorem bindMemoryRow_decompose {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (data : DTmem K)
    (left right : NTree (MState × DTmem K))
    (hfacts : NodeFactsA z forest (.node (.decompose, data) [left, right]))
    (hL : MemoryFingerprintStructure z left)
    (hR : MemoryFingerprintStructure z right)
    (hleavesL : MemoryLeafAtomsRealized q left)
    (hleavesR : MemoryLeafAtomsRealized q right) :
    BindMemoryRow z
      (decodeMemoryRowAx (K := K) q forest ax (.node (.decompose, data) [left, right]))
      (.decompose, data) := by
  obtain ⟨hseed, hst, heq, hlink, hver, _, _⟩ := hfacts
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
    simp only [bindFP, decodeMemoryRowAx, GlobalCarryRecognizer.enc_cons hz]
    rw [heq'.1, show data.1.z = z from hseed]
    rw [← congrArg Cell.noun hleftCell, ← congrArg Cell.noun hrightCell]
    simp [memoryTreeRootFP] at hencL hencR
    rw [← hencL, ← hencR]
  · intro i
    have hfo : (i : ℕ) < fanoutMem .decompose := i.isLt
    simp only [hfo, ↓reduceDIte, decodeMemoryRowAx]
    fin_cases i
    · simp only [Fin.val_zero, ↓reduceIte, memoryChildCell, bindFP]
      have hencL := decode_fingerprint hz hL hleavesL
      rw [← congrArg Cell.noun hleftCell]
      simpa [memoryTreeRootFP] using hencL.symm
    · simp only [Fin.val_one, ↓reduceIte, memoryChildCell, bindFP]
      have hencR := decode_fingerprint hz hR hleavesR
      rw [← congrArg Cell.noun hrightCell]
      simpa [memoryTreeRootFP] using hencR.symm
  · have hpad : ¬ memoryMemRecKind (decodeMemoryRowAx (K := K) q forest ax
        (.node (.decompose, data) [left, right])).state = .active := by
      simp [decodeMemoryRowAx, memoryMemRecKind]
    simp only [hpad, ↓reduceDIte]
    exact heq'.2.2.2

theorem bindMemoryRow_readRoot {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (data : DTmem K)
    (child : NTree (MState × DTmem K))
    (hfacts : NodeFactsA z forest (.node (.read_root, data) [child]))
    (haxis : AxisFacts ax (.node (.read_root, data) [child]))
    (hchild : MemoryFingerprintStructure z child)
    (hleavesC : MemoryLeafAtomsRealized q child)
    (hstructF : ForestFPFacts z q forest) :
    BindMemoryRow z
      (decodeMemoryRowAx (K := K) q forest ax (.node (.read_root, data) [child]))
      (.read_root, data) := by
  obtain ⟨hseed, hst, heq, hlink, hver, hservedC, _⟩ := hfacts
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
  have hax := haxis (by simp [memoryMemRecKind])
  have hmem :=
    bindMemRow_readRoot_of_fill hz forest ax data child hroot (hservedC rfl) hax
      hstructF.1 hstructF.2
  refine ⟨rfl, hseed, hst, ?_, ?_, ?_, hver⟩
  · simp only [bindFP, decodeMemoryRowAx]
    rw [heq'.1, ← congrArg Cell.noun hchildCell]
    simpa [memoryTreeRootFP] using henc.symm
  · intro i
    fin_cases i
    · have hfo : (0 : ℕ) < fanoutMem .read_root := by simp [fanoutMem]
      simp only [hfo, ↓reduceDIte, decodeMemoryRowAx, memoryChildCell]
      rw [bindFP, ← congrArg Cell.noun hchildCell]
      simpa [memoryTreeRootFP] using henc.symm
    · have hfo : ¬ (1 : ℕ) < fanoutMem .read_root := by simp [fanoutMem]
      simp only [hfo, ↓reduceDIte, memoryChildCell]
      exact heq'.2.2.2.2.2
  · rw [dif_pos (by simp [decodeMemoryRowAx, memoryMemRecKind])]
    exact hmem

theorem bindMemoryRow_verifyChild {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (data : DTmem K)
    (child : NTree (MState × DTmem K))
    (hfacts : NodeFactsA z forest (.node (.verify_child, data) [child]))
    (haxis : AxisFacts ax (.node (.verify_child, data) [child]))
    (hchild : MemoryFingerprintStructure z child)
    (hleavesC : MemoryLeafAtomsRealized q child)
    (hstructF : ForestFPFacts z q forest) :
    BindMemoryRow z
      (decodeMemoryRowAx (K := K) q forest ax (.node (.verify_child, data) [child]))
      (.verify_child, data) := by
  obtain ⟨hseed, hst, heq, hlink, hver, _, hservedR⟩ := hfacts
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
  have hax := haxis (by simp [memoryMemRecKind])
  have hmem :=
    bindMemRow_verifyChild_of_fill hz forest ax data child (hservedR rfl) hch hax
      hstructF.1 hstructF.2
  refine ⟨rfl, hseed, hst, ?_, ?_, ?_, hver⟩
  · simp only [bindFP, decodeMemoryRowAx]
    rw [heq'.1, ← congrArg Cell.noun hchildCell]
    simpa [memoryTreeRootFP] using henc.symm
  · intro i
    fin_cases i
    · have hfo : (0 : ℕ) < fanoutMem .verify_child := by simp [fanoutMem]
      simp only [hfo, ↓reduceDIte, decodeMemoryRowAx, memoryChildCell]
      rw [bindFP, ← congrArg Cell.noun hchildCell]
      simpa [memoryTreeRootFP] using henc.symm
    · have hfo : ¬ (1 : ℕ) < fanoutMem .verify_child := by simp [fanoutMem]
      simp only [hfo, ↓reduceDIte, memoryChildCell]
      exact heq'.2.2.2.2.2
  · rw [dif_pos (by simp [decodeMemoryRowAx, memoryMemRecKind])]
    exact hmem

/-- **`MemoryTreeBinds` (row-level) after the fill**: row binding + `children.length = fanoutMem`
from the reconstructed shape, by induction on the fingerprint structure. -/
theorem memoryTreeBinds_of_fillA {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (t : NTree (MState × DTmem K))
    (hstruct : MemoryFingerprintStructure z t)
    (hleaves : MemoryLeafAtomsRealized q t)
    (hfacts : ∀ node, InTree t node → NodeFactsA z forest node)
    (haxis : ∀ node, InTree t node → AxisFacts ax node)
    (hstructF : ForestFPFacts z q forest) :
    MemoryTreeBinds z (decodeMemoryTreeAx q forest ax t) t := by
  induction hstruct with
  | halt data atomShape =>
      simp only [decodeMemoryTreeAx]
      exact MemoryTreeBinds.node (by simp [decodeMemoryRowAx, fanoutMem])
        (bindMemoryRow_halt forest ax data (hfacts _ (InTree.here _)) atomShape hleaves)
        .nil
  | decompose data left right consEq hL hR ihL ihR =>
      have hhere := hfacts _ (InTree.here _)
      have ihL' := ihL hleaves.1
        (fun n hn => hfacts n (InTree.sub (by simp) hn))
        (fun n hn => haxis n (InTree.sub (by simp) hn))
      have ihR' := ihR hleaves.2
        (fun n hn => hfacts n (InTree.sub (by simp [List.mem_cons]) hn))
        (fun n hn => haxis n (InTree.sub (by simp [List.mem_cons]) hn))
      simp only [decodeMemoryTreeAx]
      exact MemoryTreeBinds.node (by simp [decodeMemoryRowAx, fanoutMem])
        (bindMemoryRow_decompose hz forest ax data left right hhere hL hR
          hleaves.1 hleaves.2)
        (.cons ihL' (.cons ihR' .nil))
  | readRoot data child passEq childStructure ih =>
      have hhere := hfacts _ (InTree.here _)
      have ih' := ih hleaves
        (fun n hn => hfacts n (InTree.sub (by simp) hn))
        (fun n hn => haxis n (InTree.sub (by simp) hn))
      simp only [decodeMemoryTreeAx]
      exact MemoryTreeBinds.node (by simp [decodeMemoryRowAx, fanoutMem])
        (bindMemoryRow_readRoot hz forest ax data child hhere (haxis _ (InTree.here _))
          childStructure hleaves hstructF)
        (.cons ih' .nil)
  | verifyChild data child passEq childStructure ih =>
      have hhere := hfacts _ (InTree.here _)
      have ih' := ih hleaves
        (fun n hn => hfacts n (InTree.sub (by simp) hn))
        (fun n hn => haxis n (InTree.sub (by simp) hn))
      simp only [decodeMemoryTreeAx]
      exact MemoryTreeBinds.node (by simp [decodeMemoryRowAx, fanoutMem])
        (bindMemoryRow_verifyChild hz forest ax data child hhere (haxis _ (InTree.here _))
          childStructure hleaves hstructF)
        (.cons ih' .nil)

/-- **The a-bearing analogue of `Batch524.memoryTreeBinds_of_topology'`.**  Same premises, except
that the axis premise `haxisA` reads the a-bearing axis `ax` (the stored `(T, C')` are its Form R
encode at the row's `λ`), not the stored slot; and the conclusion is the row-level
`SemanticStrategy.MemoryTreeBinds` that `BindsAt.memoryForest` reads, of the decoder
`decodeMemoryTreeAx q forest ax`. -/
theorem memoryTreeBinds_of_topologyA {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
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
    (haxisA : ∀ node, InTree t node →
      memoryMemRecKind node.label.1 = .active →
        node.label.2.2.mem.axis =
            formRT node.label.2.2.lambda (nockAxisOf ((ax node.label : ℕ) : K)) ∧
          node.label.2.2.cprime =
            formRC node.label.2.2.lambda (nockAxisOf ((ax node.label : ℕ) : K)))
    (hstructF : ForestFPFacts z q forest) :
    MemoryTreeBinds z (decodeMemoryTreeAx q forest ax t) t :=
  memoryTreeBinds_of_fillA hz forest ax t
    (MemoryTopoBetaFree.memoryFingerprintStructure_of_rvtWithArity_topo z t htop hseed) hleaves
    (fun _ hin => nodeFactsA_of_rvt' htop hseed hver hservedChild hservedRoot hin)
    (fun node hin => haxisA node hin)
    hstructF

private theorem forall₂_map_self {α β : Type*} {R : β → α → Prop}
    (f : α → β) : ∀ l : List α, (∀ x ∈ l, R (f x) x) →
    List.Forall₂ R (l.map f) l
  | [], _ => .nil
  | x :: xs, h =>
      .cons (h x (by simp)) (forall₂_map_self f xs fun y hy => h y (by simp [hy]))

/-- Forest form: the decoded forest (every tree) binds, in `BindsAt.memoryForest`'s shape. -/
theorem memoryForestBinds_of_topologyA {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (htop : ∀ t ∈ forest, RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t)
    (hseed : ∀ t ∈ forest, ∀ node, InTree t node → node.label.2.1.z = z)
    (hleaves : ∀ t ∈ forest, MemoryLeafAtomsRealized q t)
    (hver : ∀ t ∈ forest, ∀ node, InTree t node →
      node.label.2.2.ver = decide (node.label.1 = .read_root))
    (hservedChild : ∀ t ∈ forest, ∀ node, InTree t node → node.label.1 = .read_root →
      ServedFingerprint forest node.label.2.2.mem.child)
    (hservedRoot : ∀ t ∈ forest, ∀ node, InTree t node → node.label.1 = .verify_child →
      ServedFingerprint forest node.label.2.2.mem.root)
    (haxisA : ∀ t ∈ forest, ∀ node, InTree t node →
      memoryMemRecKind node.label.1 = .active →
        node.label.2.2.mem.axis =
            formRT node.label.2.2.lambda (nockAxisOf ((ax node.label : ℕ) : K)) ∧
          node.label.2.2.cprime =
            formRC node.label.2.2.lambda (nockAxisOf ((ax node.label : ℕ) : K)))
    (hstructF : ForestFPFacts z q forest) :
    List.Forall₂ (MemoryTreeBinds z) (decodedMemoryForestAx q forest ax) forest := by
  simpa [decodedMemoryForestAx] using
    forall₂_map_self (decodeMemoryTreeAx (K := K) q forest ax) forest fun t ht =>
      memoryTreeBinds_of_topologyA hz forest ax t (htop t ht) (hseed t ht) (hleaves t ht)
        (hver t ht) (hservedChild t ht) (hservedRoot t ht) (haxisA t ht) hstructF

/-- Bounded halt leaves at every `halt` node of a structured tree give `MemoryLeafAtomsRealized`. -/
theorem leafAtomsRealized_of_structure {z : K} {q : ℕ}
    {t : NTree (MState × DTmem K)}
    (hstruct : MemoryFingerprintStructure z t)
    (hhalt : ∀ node, InTree t node → node.label.1 = .halt →
      ∃ k : ℕ, k < q ∧ (k : K) = node.label.2.2.pt.noun.leaf) :
    MemoryLeafAtomsRealized q t := by
  induction hstruct with
  | halt data atomShape =>
      exact hhalt _ (InTree.here _) rfl
  | decompose data left right consEq hL hR ihL ihR =>
      exact ⟨ihL (fun n hn => hhalt n (InTree.sub (by simp) hn)),
        ihR (fun n hn => hhalt n (InTree.sub (by simp [List.mem_cons]) hn))⟩
  | readRoot data child passEq childStructure ih =>
      exact ih (fun n hn => hhalt n (InTree.sub (by simp) hn))
  | verifyChild data child passEq childStructure ih =>
      exact ih (fun n hn => hhalt n (InTree.sub (by simp) hn))

/-- `ForestFPFacts` from the forest's topology, shared seed and bounded halt leaves. -/
theorem forestFPFacts_of_topology {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (htop : ∀ t ∈ forest, RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t)
    (hseed : ∀ t ∈ forest, ∀ node, InTree t node → node.label.2.1.z = z)
    (hhalt : ∀ t ∈ forest, ∀ node, InTree t node → node.label.1 = .halt →
      ∃ k : ℕ, k < q ∧ (k : K) = node.label.2.2.pt.noun.leaf) :
    ForestFPFacts z q forest := by
  have hroots : ∀ root ∈ forest, MemoryFingerprintStructure z root := fun root hroot =>
    MemoryTopoBetaFree.memoryFingerprintStructure_of_rvtWithArity_topo z root (htop root hroot)
      (hseed root hroot)
  refine ⟨fun u hu => Batch515.MemoryFingerprintStructure.of_bfsForest hroots hu, fun u hu => ?_⟩
  obtain ⟨root, hroot, hin⟩ := (mem_bfsForest forest u).1 hu
  exact leafAtomsRealized_of_structure
    (Batch515.MemoryFingerprintStructure.of_InTree (hroots root hroot) hin)
    (fun n hn hst => hhalt root hroot n (InTree_trans hin hn) hst)

end Nock.RedTeam.Batch1010
