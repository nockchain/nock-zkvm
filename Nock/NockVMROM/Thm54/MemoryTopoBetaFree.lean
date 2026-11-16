/-
  Nock/NockVMROM/Thm54/MemoryTopoBetaFree.lean

  `FmemTopo := state ∧ eqBlk ∧ fanout ∧ childLink` — the production `Fmem` with its `Vmem` conjunct replaced by the β-free
  `eqBlk` conjunct: no `Vmem`, no `interV`, so nothing here reads the `intermediate` accumulator,
  the inputs' `β`, or the record RLC (`:2123`).

  Provided: `FmemTopo`, `fmemTopo_of_fmem`, `eqBlk_beta_acc_free`, `fmemTopo_beta_free`,
  `mem_stateSep_topo` (`StateSep`), `memPtOf` / `respects_pt_topo` (`RespectsChildLabels`), and
  `memoryFingerprintStructure_of_rvtWithArity_topo` (`MemoryFingerprintStructure.of_rvtWithArity`
  re-run on the β-free predicate; it reads only the state / `eqBlk` / child-link conjuncts and
  the arity).  The production `MemoryExactTopology` (`ExactTraversal.lean`, on `Fmem`) is NOT
  re-based here (that cell is Part 2's census).
-/
import Nock.NockVMROM.Thm54.NounRealization

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.MemoryTopoBetaFree

open Nock Nock.Walk Nock.MemoryTable Nock.ComputeTable

/-! ## A. The β-free topology predicate -/

section Predicate
variable {K : Type} [Field K]

/-- M′'s per-node predicate: `Fmem` with `Vmem` replaced by `eqBlk`. -/
def FmemTopo : (MState × DTmem K) → (Fin 2 → Option (MState × DTmem K)) → Prop :=
  fun lbl xout =>
    lbl.2.2.st = lbl.1 ∧ eqBlk lbl.2.1 lbl.2.2 ∧
      (∀ i : Fin 2, (i : ℕ) < fanoutMem lbl.1 ↔ xout i ≠ none) ∧
      childLinkMem lbl xout

theorem fmemTopo_of_fmem (lbl : MState × DTmem K) (xout : Fin 2 → Option (MState × DTmem K))
    (h : Fmem lbl xout) : FmemTopo lbl xout :=
  ⟨h.1, h.2.1.2.1, h.2.2.1, h.2.2.2⟩

/-- `eqBlk` reads neither `β` nor the accumulator pair. -/
theorem eqBlk_beta_acc_free (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K) (β' ipre' icur' : K) :
    eqBlk { inp with β := β' } { p with ipre := ipre', icur := icur' } ↔ eqBlk inp p := by
  cases hst : p.st <;> simp [eqBlk, hst, MemoryTable.Pub.lambda, MemoryTable.Pub.cprime]

/-- The predicate is invariant under the node's `β`, `ipre`, `icur` (the three things the
ten-slot pole moves).  This is why no mirror change is needed for the topology receipts. -/
theorem fmemTopo_beta_free (st : MState) (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K)
    (xout : Fin 2 → Option (MState × DTmem K)) (β' ipre' icur' : K) :
    FmemTopo (st, ({ inp with β := β' }, { p with ipre := ipre', icur := icur' })) xout ↔
      FmemTopo (st, (inp, p)) xout := by
  simp only [FmemTopo, childLinkMem, memCell]
  rw [eqBlk_beta_acc_free]

/-- `StateSep` for the β-free predicate (`mem_stateSep` with the same fanout). -/
noncomputable def mem_stateSep_topo : StateSep (FmemTopo (K := K)) where
  Sleaf := fun s => fanoutMem s = 0
  fanout := fanoutMem
  fanout_le := by intro s; cases s <;> simp [fanoutMem]
  fanout_leaf := fun s h => h
  dynamic := by intro s d xout hF i; exact hF.2.2.1 i
  solely := by
    rintro ⟨⟨s, d⟩, ch⟩ hrvt
    rw [RVT] at hrvt
    obtain ⟨hF, _hch, hleaf⟩ := hrvt
    simp only [NTree.label_node]
    constructor
    · intro hsl
      rw [hleaf]
      refine ⟨hF.1, hF.2.1, ?_, ?_⟩
      · intro i
        exact ⟨fun hlt => absurd (hsl ▸ hlt) (Nat.not_lt_zero _), fun hne => absurd rfl hne⟩
      · intro i hi; exact absurd (hsl ▸ hi) (Nat.not_lt_zero _)
    · intro hil
      rw [hleaf] at hil
      have h0 := hil.2.2.1 ⟨0, by norm_num⟩
      simp only [ne_eq, not_true_eq_false, iff_false, not_lt, Nat.le_zero] at h0
      exact h0

def memPtOf (l : MState × DTmem K) : Cell K := l.2.2.pt

theorem respects_pt_topo : RespectsChildLabels (FmemTopo (K := K)) memPtOf := by
  intro lbl xout xout' hx hF
  obtain ⟨hst, hV, hslot, hlink⟩ := hF
  refine ⟨hst, hV, ?_, ?_⟩
  · intro i
    rw [hslot i]
    have := hx i
    constructor
    · intro hne hnone; rw [hnone] at this; cases h : xout i
      · exact hne h
      · rw [h] at this; simp at this
    · intro hne hnone; rw [hnone] at this; cases h : xout' i
      · exact hne h
      · rw [h] at this; simp at this
  · intro i hi
    have hli := hlink i hi
    have hj := hx i
    cases hxout : xout i with
    | none => rw [hxout] at hli; simp at hli
    | some child =>
      cases hxout' : xout' i with
      | none =>
        rw [hxout, hxout'] at hj; simp at hj
      | some child' =>
        rw [hxout] at hli
        simp only [Option.map_some, Option.some.injEq] at hli
        rw [hxout, hxout'] at hj
        simp only [Option.map_some, Option.some.injEq] at hj
        simp only [Option.map_some, Option.some.injEq]
        exact hj.symm.trans hli

end Predicate

/-! ## B. Fingerprint structure from the β-free topology (`NounRealization.of_rvtWithArity`
re-run; it reads only `st`, `eqBlk`, `childLinkMem` and the arity) -/

section Structure
variable {K : Type} [Field K]

theorem memoryFingerprintStructure_of_rvtWithArity_topo
    (z : K)
    (tree : NTree (MState × DTmem K))
    (htopology : RVTWithArity (FmemTopo (K := K)) tree)
    (hseed : ∀ node, InTree tree node → node.label.2.1.z = z) :
    MemoryFingerprintStructure z tree := by
  suffices H :
      ∀ n : ℕ,
        ∀ tree : NTree (MState × DTmem K),
          sizeOf tree ≤ n →
          RVTWithArity (FmemTopo (K := K)) tree →
          (∀ node, InTree tree node → node.label.2.1.z = z) →
          MemoryFingerprintStructure z tree by
    exact H (sizeOf tree) tree le_rfl htopology hseed
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro tree hsize htopology hseed
      have hFcon :=
        (RVT_iff_forall_InTree (FmemTopo (K := K)) tree).mp
          htopology.rvt tree (InTree.here tree)
      have hshape :=
        fanout_eq_children_length_of_properArity
          (mem_stateSep_topo (K := K))
          htopology.rvt htopology.arity tree (InTree.here tree)
      have hrootSeed := hseed tree (InTree.here tree)
      cases tree with
      | node lbl children =>
          obtain ⟨state, data⟩ := lbl
          simp only [NTree.label_node, NTree.children_node] at hFcon hshape hrootSeed hsize
          have hstate : data.2.st = state := hFcon.1.1
          have heq : eqBlk data.1 data.2 := hFcon.1.2.1
          have hlink :
              childLinkMem (state, data)
                (fun i : Fin 2 => (NTree.node (state, data) children).childLabel i) :=
            hFcon.1.2.2.2
          cases state with
          | halt =>
              have hlen : children.length = 0 := by
                change 0 = children.length at hshape
                exact hshape.symm
              have hnil : children = [] := List.eq_nil_of_length_eq_zero hlen
              subst children
              simp only [eqBlk, hstate] at heq
              exact .halt data ⟨heq.1.trans hrootSeed, heq.2.1⟩
          | decompose =>
              have hlen : children.length = 2 := by
                change 2 = children.length at hshape
                exact hshape.symm
              obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hlen
              have hleftLink := hlink 0 (by simp [fanoutMem])
              have hrightLink := hlink 1 (by simp [fanoutMem])
              simp only [NTree.childLabel, NTree.childOpt, NTree.children_node,
                Fin.val_zero, Fin.val_one, List.getElem?_cons_zero,
                List.getElem?_cons_succ, Option.map_some, memCell,
                Option.some.injEq] at hleftLink hrightLink
              simp only [eqBlk, hstate] at heq
              have hleftIn :
                  InTree (NTree.node (MState.decompose, data) [left, right]) left :=
                InTree.sub (by simp) (InTree.here left)
              have hrightIn :
                  InTree (NTree.node (MState.decompose, data) [left, right]) right :=
                InTree.sub (by simp) (InTree.here right)
              have hleftSize :
                  sizeOf left < sizeOf (NTree.node (MState.decompose, data) [left, right]) := by
                simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
                omega
              have hrightSize :
                  sizeOf right < sizeOf (NTree.node (MState.decompose, data) [left, right]) := by
                simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
                omega
              have hleftTopology : RVTWithArity (FmemTopo (K := K)) left :=
                ⟨RVT_of_InTree htopology.rvt hleftIn, htopology.arity.ofChild (by simp)⟩
              have hrightTopology : RVTWithArity (FmemTopo (K := K)) right :=
                ⟨RVT_of_InTree htopology.rvt hrightIn, htopology.arity.ofChild (by simp)⟩
              have hleftStructure :=
                ih (sizeOf left) (by omega) left le_rfl hleftTopology
                  (fun node hnode => hseed node (InTree_trans hleftIn hnode))
              have hrightStructure :=
                ih (sizeOf right) (by omega) right le_rfl hrightTopology
                  (fun node hnode => hseed node (InTree_trans hrightIn hnode))
              apply MemoryFingerprintStructure.decompose data left right
              · calc
                  data.2.pt.noun = FP.cons z data.2.lc.noun data.2.rc.noun := by
                    simpa [hrootSeed] using heq.1
                  _ = FP.cons z (memoryTreeRootFP left) (memoryTreeRootFP right) := by
                    rw [← congrArg MemoryTable.Cell.noun hleftLink, ← congrArg MemoryTable.Cell.noun hrightLink]
                    rfl
              · exact hleftStructure
              · exact hrightStructure
          | read_root =>
              have hlen : children.length = 1 := by
                change 1 = children.length at hshape
                exact hshape.symm
              obtain ⟨child, rfl⟩ := List.length_eq_one_iff.mp hlen
              have hchildLink := hlink 0 (by simp [fanoutMem])
              simp only [NTree.childLabel, NTree.childOpt, NTree.children_node,
                Fin.val_zero, List.getElem?_cons_zero, Option.map_some,
                memCell, Option.some.injEq] at hchildLink
              simp only [eqBlk, hstate] at heq
              have hchildIn :
                  InTree (NTree.node (MState.read_root, data) [child]) child :=
                InTree.sub (by simp) (InTree.here child)
              have hchildSize :
                  sizeOf child < sizeOf (NTree.node (MState.read_root, data) [child]) := by
                simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
                omega
              have hchildTopology : RVTWithArity (FmemTopo (K := K)) child :=
                ⟨RVT_of_InTree htopology.rvt hchildIn, htopology.arity.ofChild (by simp)⟩
              have hchildStructure :=
                ih (sizeOf child) (by omega) child le_rfl hchildTopology
                  (fun node hnode => hseed node (InTree_trans hchildIn hnode))
              apply MemoryFingerprintStructure.readRoot data child
              · exact heq.1.trans (congrArg MemoryTable.Cell.noun hchildLink).symm
              · exact hchildStructure
          | verify_child =>
              have hlen : children.length = 1 := by
                change 1 = children.length at hshape
                exact hshape.symm
              obtain ⟨child, rfl⟩ := List.length_eq_one_iff.mp hlen
              have hchildLink := hlink 0 (by simp [fanoutMem])
              simp only [NTree.childLabel, NTree.childOpt, NTree.children_node,
                Fin.val_zero, List.getElem?_cons_zero, Option.map_some,
                memCell, Option.some.injEq] at hchildLink
              simp only [eqBlk, hstate] at heq
              have hchildIn :
                  InTree (NTree.node (MState.verify_child, data) [child]) child :=
                InTree.sub (by simp) (InTree.here child)
              have hchildSize :
                  sizeOf child < sizeOf (NTree.node (MState.verify_child, data) [child]) := by
                simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
                omega
              have hchildTopology : RVTWithArity (FmemTopo (K := K)) child :=
                ⟨RVT_of_InTree htopology.rvt hchildIn, htopology.arity.ofChild (by simp)⟩
              have hchildStructure :=
                ih (sizeOf child) (by omega) child le_rfl hchildTopology
                  (fun node hnode => hseed node (InTree_trans hchildIn hnode))
              apply MemoryFingerprintStructure.verifyChild data child
              · exact heq.1.trans (congrArg MemoryTable.Cell.noun hchildLink).symm
              · exact hchildStructure

end Structure

end Nock.NockVMROM.Thm54.MemoryTopoBetaFree

#print axioms Nock.NockVMROM.Thm54.MemoryTopoBetaFree.fmemTopo_beta_free
#print axioms Nock.NockVMROM.Thm54.MemoryTopoBetaFree.mem_stateSep_topo
#print axioms Nock.NockVMROM.Thm54.MemoryTopoBetaFree.respects_pt_topo
#print axioms Nock.NockVMROM.Thm54.MemoryTopoBetaFree.memoryFingerprintStructure_of_rvtWithArity_topo
