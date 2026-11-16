/-
  Nock/RedTeam/Batch726Thm54DoubleCheckMoveMTopo.lean

  Notes only; no production edit, no digest
  move, no authorization implied.

  * **`FmemTopo`** — the report's `state ∧ eqBlk ∧ fanout ∧ childLink`, i.e. `Fmem` with `Vmem`
    replaced by its β-free `eqBlk` conjunct (`verBool` is a tautology of `ver : Bool`, `interV` is
    the uniform-β accumulator clause that the ten-slot chip violates at every record row with
    `γ ≠ 0`, `Batch679.rowExpTerm_eq_zero_iff`).  `fmemTopo_of_fmem`; `fmemTopo_beta_free`:
    the predicate is invariant under the node's `β`, `ipre`, `icur`.
  CONFIRMED.

  * **Non-vacuity on an honest trace** (`fmemTopo_at_honest_tuple`): at the honest tuple the
    family chip IS the package chip (`memoryChipAt_honest_of_chalVal`), so the package's own
    honest acceptance `memory_satisfies` (completeness, proved in the build) discharges `hsatM`
    (`satisfies_familyQm_of_chip_eq`); nothing in the hypothesis set mentions `γ` or `reqIdx`.
    Contrast: the OLD `hexp0 : ∀ i, rowExpTerm = 0` is FALSE at every honest record row with
    `γ ≠ 0`, so the old statements were vacuous there; the restated one holds at every
    `c` at which the chip accepts, whatever `γ`.

-- the paper
-/
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch524Thm54DecodeMemoryRowIn

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch726

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.MemoryTable Nock.ComputeTable Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.FamilyMemoryRows Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.RedTeam.Batch524
open Nock.RedTeam.Batch516 (ServedFingerprint)
open Nock.Framework Nock.Framework.Reify MonolithicRAP
open Nock.NockVMROM.Thm54.FamilyComputeRows Nock.NockVMROM.Thm54.DeployedAcceptance
open scoped Classical

/-! ## A. The β-free topology predicate -/

section Predicate
variable {K : Type} [Field K]

/-- M′'s per-node predicate: `Fmem` with `Vmem` replaced by `eqBlk`
. -/
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
ten-slot pole moves). -/
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

/-- `RespectsChildLabels` for the β-free predicate. -/
theorem respects_pt_topo : RespectsChildLabels (FmemTopo (K := K)) Batch501.ptOf := by
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

/-! ## C. The binding from the β-free topology (M′'s `memoryTreeBinds_of_topology'`) -/

section Binding
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]


theorem memoryNodeFacts_of_rvt_topo {z : K} {q : ℕ}
    {forest : List (NTree (MState × DTmem K))}
    {t : NTree (MState × DTmem K)}
    (htop : RVTWithArity (FmemTopo (K := K)) t)
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
    ((RVT_iff_forall_InTree (F := FmemTopo (K := K)) t).mp htop.rvt node hin).1
  exact ⟨hseed node hin, hF.1, hF.2.1, hF.2.2.2, hver node hin,
    hservedChild node hin, hservedRoot node hin, haxis node hin⟩


theorem memoryTreeBinds_of_topology_topo {z : K} (hz : z ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (MState × DTmem K))
    (htop : RVTWithArity (FmemTopo (K := K)) t)
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
    (memoryFingerprintStructure_of_rvtWithArity_topo z t htop hseed) hleaves
    (fun _ hin =>
      memoryNodeFacts_of_rvt_topo htop hseed hver hservedChild hservedRoot haxis hin)
    hstructF

end Binding

/-! ## D. -/

section DeployedRows

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (WrapMemoryConjuncts.familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)

include hsatM hchar hz in

theorem deployed_lblM_eqBlk
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    eqBlk (ExecOfTraces.lblM P Qm₀ c i).2.1 (ExecOfTraces.lblM P Qm₀ c i).2.2 := by
  have hi : i - 1 < P.optimized.family.problem.cfg.memRows := by omega
  obtain ⟨st, hone⟩ :=
    baseOneHot_at_family P c (WrapMemoryConjuncts.familyQm P c Qm₀) hsatM ⟨i - 1, hi⟩ hchar
  have hst : (ExecOfTraces.decodeMemPub P
      (honestQm P c (WrapMemoryConjuncts.familyQm P c Qm₀)) c ⟨i - 1, hi⟩).st = st := by
    simp only [ExecOfTraces.decodeMemPub]
    exact memoryStateOf_eq_of_baseOneHot _ _ hone
  have he := eqBlk_of_paper_classes P c (WrapMemoryConjuncts.familyQm P c Qm₀) hsatM
    ⟨i - 1, hi⟩ st hone hst hz
  have hQ : honestQm P c (WrapMemoryConjuncts.familyQm P c Qm₀) = Qm₀ :=
    WalkQueueDeployed.honestQm_familyQm P c Qm₀
  rw [Batch490.lblM_of_pos P c Qm₀ i hi1 hih]
  rw [hQ] at he
  exact he

include hsatM hchar hz in
/-- The hypothesis set does not mention `γ`, `β` or `reqIdx`. -/
theorem hFcommit_memory_topo
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    FmemTopo (ExecOfTraces.lblM P Qm₀ c i)
      (fun j : Fin 2 =>
        if (j : ℕ) < ExecOfTraces.foM P Qm₀ c i then
          some (Batch490.clabOfMem (ExecOfTraces.lblM P Qm₀ c) i ((j : ℕ) + 1))
        else none) := by
  refine ⟨Batch490.lblM_state P c Qm₀ i,
    deployed_lblM_eqBlk P c Qm₀ hsatM hchar hz i hi1 hih, ?_, ?_⟩
  · intro j
    simp only [ExecOfTraces.foM]
    constructor
    · intro hj; simp [hj]
    · intro hne; by_contra hj; simp [hj] at hne
  · intro j hj
    simp only [ExecOfTraces.foM] at hj ⊢
    erw [if_pos hj]
    simp only [Option.map_some, Batch490.clabOfMem]
    have hm : ((j : ℕ) + 1 - 1) % 2 = j := by
      rw [show (j : ℕ) + 1 - 1 = (j : ℕ) by omega]; exact Nat.mod_eq_of_lt j.isLt
    have hfin : (⟨((j : ℕ) + 1 - 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = j :=
      Fin.ext hm
    rw [hfin]

end DeployedRows

/-! ## E. Non-vacuity on an honest trace -/

section Honest

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Transport of the package chip's acceptance to the family chip when the two chips coincide
(the dependent `Fin.cast` is the identity once `C = P.memoryChip`). -/
theorem satisfies_familyQm_of_chip_eq
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hEq : P.memoryChipAt c = P.memoryChip)
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (WrapMemoryConjuncts.familyQm P c Qm) := by
  have key : ∀ (C : _) (h : C = P.memoryChip) (hw : C.rap.w = P.memoryChip.rap.w),
      RAP.SatisfiesWithPreprocessing C (fun j => Qm (Fin.cast hw j)) := by
    intro C h hw
    subst h
    simpa using hsat
  exact key _ hEq (FamilyComputeRows.memoryChipAt_width P c)


theorem fmemTopo_at_honest_tuple
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
    (hchar : MemStateTagChar F)
    (hz : nprSeed P.honestTuple.1 ≠ 0)
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    FmemTopo (ExecOfTraces.lblM P Qm P.honestTuple i)
      (fun j : Fin 2 =>
        if (j : ℕ) < ExecOfTraces.foM P Qm P.honestTuple i then
          some (Batch490.clabOfMem (ExecOfTraces.lblM P Qm P.honestTuple) i ((j : ℕ) + 1))
        else none) :=
  hFcommit_memory_topo P P.honestTuple Qm
    (satisfies_familyQm_of_chip_eq P P.honestTuple Qm (P.memoryChipAt_honest_of_chalVal h) hsat)
    hchar hz i hi1 hih

/-- The same at an arbitrary tuple from `DeployedAcceptanceAt` (the family-chip acceptance the
H1.5 chain carries). -/
theorem fmemTopo_rows_of_deployedAcceptance
    (c : OptimizedProductionChallengeTuple K F)
    (Qc₀ : Fin P.computeChip.rap.w → F[X])
    (Qm₀ : Fin P.memoryChip.rap.w → F[X])
    (hacc : DeployedAcceptanceAt P c (FamilyComputeRows.familyQc P c Qc₀)
      (WrapMemoryConjuncts.familyQm P c Qm₀))
    (hchar : MemStateTagChar F)
    (hz : nprSeed c.1 ≠ 0)
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.memRows) :
    FmemTopo (ExecOfTraces.lblM P Qm₀ c i)
      (fun j : Fin 2 =>
        if (j : ℕ) < ExecOfTraces.foM P Qm₀ c i then
          some (Batch490.clabOfMem (ExecOfTraces.lblM P Qm₀ c) i ((j : ℕ) + 1))
        else none) :=
  hFcommit_memory_topo P c Qm₀ hacc.memory_satisfies hchar hz i hi1 hih

end Honest

end Nock.RedTeam.Batch726

#print axioms Nock.RedTeam.Batch726.memoryTreeBinds_of_topology_topo
#print axioms Nock.RedTeam.Batch726.hFcommit_memory_topo
#print axioms Nock.RedTeam.Batch726.fmemTopo_at_honest_tuple
