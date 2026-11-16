/-
  Nock/RedTeam/Batch509Thm54WrapSpecialize.lean

  `specializedExec` is the wrap-then-specialize of
  `execOfTraces` (`AcceptedContentOfTracesFill.specializedExec_eq`).
  Both per-node maps are the identity on the reconstructed trees:

  * compute: `wrap_fixes_vcomp_row` from `Fcomp` at `lblC`
    (`inp.α = α`, `st = pub.state`, `Vcomp`);
  * memory: `wrap_fixes_vmem_row` from the β-free `FmemTopo` at `lblM`
    (`st`, `eqBlk` padding-zero) plus `MemPower` on active rows (M′: re-typed from
    `Fmem` / the production `MemoryExactTopology`).

  `mapNTree_congr_of_mem` / `mapNTree_buildT` give tree equality;
  `ComputeExactTopology` / the β-free `∀ t, RVTWithArity FmemTopo t` transport by `rw`.
  Ledger **7 → 5** by name.
-/
import Nock.Walk
import Nock.Framework.Traversal
import Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.NockVMROM.Thm54.WrapFixesVcomp
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.ResponseTsMemPowers
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.RedTeam.Batch471Thm54ComputeTopologyPrefix
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch500Thm54GammaTransport
import Nock.RedTeam.Batch501Thm54MemoryTopology
import Nock.RedTeam.Batch502Thm54LedgerTransfer
import Nock.NockVMROM.Thm54.P8Core.Batch509Thm54WrapSpecialize
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nock.RedTeam.Batch509

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.WrapFixesVcomp
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.ResponseTsMemPowers
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.RedTeam.Batch471
open Nock.RedTeam.Batch490
open Nock.RedTeam.Batch500
open Nock.RedTeam.Batch501
open Nock.RedTeam.Batch502
open MonolithicRAP
open scoped Polynomial

/-! ## Ledger 7 → 5 by name -/

/-- Open `AcceptedContent` conjuncts after wrap-specialize. -/
def openConjunctsAfterWrap : List String :=
  ["mem_first_counts", "mem_first_indicator",
    "axisStructural", "rootBoundary", "structuralChecks"]

theorem openConjunctsAfterWrap_length :
    openConjunctsAfterWrap.length = 5 := by decide

theorem topology_names_left :
    "computeTopology" ∉ openConjunctsAfterWrap ∧
      "memoryTopology" ∉ openConjunctsAfterWrap := by
  decide

theorem remaining_five_from_seven :
    openConjunctsAfterWrap =
      Nock.RedTeam.Batch448.openConjunctsAfterVer.filter
        (fun n => n ≠ "computeTopology" ∧ n ≠ "memoryTopology") := by
  decide

theorem openAfterWrapSpecialize_length :
    openConjunctsAfterWrap.length = 5 :=
  openConjunctsAfterWrap_length

/-! ## `mapNTree` identity helpers -/

/-- Labels of every node, root first then children. -/
def ntreeLabels {α : Type*} : NTree α → List α
  | .node l ch => l :: ch.flatMap ntreeLabels

theorem mem_ntreeLabels_root {α : Type*} (l : α) (ch : List (NTree α)) :
    l ∈ ntreeLabels (.node l ch) := by
  simp [ntreeLabels]

theorem mem_ntreeLabels_of_child {α : Type*} {l : α} {ch : List (NTree α)}
    {c : NTree α} {a : α} (hc : c ∈ ch) (ha : a ∈ ntreeLabels c) :
    a ∈ ntreeLabels (.node l ch) := by
  simp only [ntreeLabels, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨c, hc, ha⟩

/-- Relabelling that fixes every present label is the identity on the tree. -/
theorem mapNTree_congr_of_mem {α : Type*} {f : α → α} :
    ∀ t : NTree α, (∀ a ∈ ntreeLabels t, f a = a) → mapNTree f t = t
  | .node l ch, h => by
    have hl : f l = l := h l (mem_ntreeLabels_root l ch)
    have hch : ch.map (mapNTree f) = ch := by
      have : ch.map (mapNTree f) = ch.map id := by
        apply List.map_congr_left
        intro c hc
        exact mapNTree_congr_of_mem c fun a ha =>
          h a (mem_ntreeLabels_of_child hc ha)
      rw [this, List.map_id]
    simp [mapNTree, hl, hch]

theorem mapNTree_id {α : Type*} (t : NTree α) : mapNTree id t = t :=
  mapNTree_congr_of_mem t fun _ _ => rfl

theorem mapNTree_comp {α β γ : Type*} (f : α → β) (g : β → γ) :
    ∀ t : NTree α, mapNTree g (mapNTree f t) = mapNTree (fun a => g (f a)) t
  | .node _ _ => by
    simp only [mapNTree, List.map_map]
    refine congrArg _ ?_
    apply List.map_congr_left
    intro c _
    exact mapNTree_comp f g c

theorem mapNTree_buildT {α β : Type*} (f : α → β)
    (fo : ℕ → ℕ) (lbl : ℕ → α) (h i : ℕ) :
    mapNTree f (buildT fo lbl h i) =
      buildT fo (fun j => f (lbl j)) h i := by
  suffices ∀ d i, h - i = d →
      mapNTree f (buildT fo lbl h i) =
        buildT fo (fun j => f (lbl j)) h i from this (h - i) i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro i hi
    rw [buildT, mapNTree, buildT]
    refine congrArg (NTree.node (f (lbl i))) ?_
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    have hmem : j.1 ∈ childIdxs fo h i := j.property
    have hlt : h - j.1 < d := by
      simp only [childIdxs, List.mem_filter, decide_eq_true_eq] at hmem
      omega
    exact ih (h - j.1) hlt j.1 rfl

theorem mapNTree_reconTree {α β : Type*} (f : α → β)
    (fo : ℕ → ℕ) (lbl : ℕ → α) (h : ℕ) :
    mapNTree f (reconTree fo lbl h) =
      reconTree fo (fun j => f (lbl j)) h :=
  mapNTree_buildT f fo lbl h 1

theorem reconTree_eq_of_lbl {α : Type*} (fo : ℕ → ℕ) {lbl lbl' : ℕ → α}
    (h : ℕ) (heq : ∀ i, lbl i = lbl' i) :
    reconTree fo lbl h = reconTree fo lbl' h := by
  simp [reconTree, funext heq]

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (h : TracesWalkHyps P Qc₀ Qm₀ c)
  (hz : nprSeed c.1 ≠ 0)

/-! ## Compute: wrap is the identity at every `lblC` -/

theorem lblC_alpha (i : ℕ) :
    (lblC P Qc₀ c i).2.1.α = alphaM c.1 := by
  unfold lblC
  split_ifs with hi
  · have := decodeInputs_eq_specialized P Qc₀ c ⟨i - 1, hi⟩
    simpa [lblCAt] using congrArg Inputs.α this
  · have := decodeInputs_eq_specialized P Qc₀ c
      ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩
    simpa [lblCAt] using congrArg Inputs.α this

theorem wrap_fixes_lblC (i : ℕ)
    (hv : Vcomp (lblC P Qc₀ c i).2.1 (lblC P Qc₀ c i).2.2.1
      (lblC P Qc₀ c i).2.2.2) :
    (wrapComputeLabel (lblC P Qc₀ c i)).specialize (alphaM c.1) =
      lblC P Qc₀ c i :=
  wrap_fixes_vcomp_row
    (lblC P Qc₀ c i).1 (lblC P Qc₀ c i).2.1
    (lblC P Qc₀ c i).2.2.1 (lblC P Qc₀ c i).2.2.2
    (alphaM c.1) (lblC_alpha P c Qc₀ i) (lblC_state P c Qc₀ i).symm hv

theorem specialized_computeTree_map :
    ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeTree =
      mapNTree (fun r => (wrapComputeLabel r).specialize (alphaM c.1))
        (execOfTraces P Qc₀ Qm₀ c h).computeTree := by
  rw [specializedExec_eq]
  change mapNTree (fun row => row.specialize (alphaM c.1))
      (mapNTree wrapComputeLabel (execOfTraces P Qc₀ Qm₀ c h).computeTree) =
    mapNTree (fun r => (wrapComputeLabel r).specialize (alphaM c.1))
      (execOfTraces P Qc₀ Qm₀ c h).computeTree
  exact mapNTree_comp wrapComputeLabel
    (fun row => row.specialize (alphaM c.1)) _

theorem fcomp_vcomp_of_topology
    (htop : ComputeExactTopology (execOfTraces P Qc₀ Qm₀ c h))
    (i : ℕ) (hi1 : 1 ≤ i)
    (hih : i ≤ P.optimized.family.problem.cfg.compRows) :
    Vcomp (lblC P Qc₀ c i).2.1 (lblC P Qc₀ c i).2.2.1
      (lblC P Qc₀ c i).2.2.2 := by
  have hrvt : RVT (Fcomp (K := K))
      (execOfTraces P Qc₀ Qm₀ c h).computeTree := htop.rvt
  have hbfs := bfsForest_reconTree (foC P Qc₀ c) (lblC P Qc₀ c)
    P.optimized.family.problem.cfg.compRows h.sfCompute h.validCompute
  have hnode :
      buildT (foC P Qc₀ c) (lblC P Qc₀ c)
          P.optimized.family.problem.cfg.compRows i ∈
        bfsForest [(execOfTraces P Qc₀ Qm₀ c h).computeTree] := by
    change buildT (foC P Qc₀ c) (lblC P Qc₀ c)
        P.optimized.family.problem.cfg.compRows i ∈
      bfsForest [reconTree (foC P Qc₀ c) (lblC P Qc₀ c)
        P.optimized.family.problem.cfg.compRows]
    rw [hbfs]
    refine List.mem_map.mpr ⟨i, ?_, rfl⟩
    exact List.mem_range'.mpr ⟨i - 1, by omega, by omega⟩
  obtain ⟨root, hroot, hin⟩ := (mem_bfsForest _ _).mp hnode
  have hroot' : root = (execOfTraces P Qc₀ Qm₀ c h).computeTree :=
    List.mem_singleton.mp hroot
  subst hroot'
  have hFcon := (RVT_iff_forall_InTree (Fcomp (K := K)) _).1 hrvt _ hin
  have hF : Fcomp (lblC P Qc₀ c i)
      (fun j => (buildT (foC P Qc₀ c) (lblC P Qc₀ c)
        P.optimized.family.problem.cfg.compRows i).childLabel j) := by
    simpa [Fcon, buildT_label] using hFcon.1
  exact hF.2.1

theorem lblC_off_eq_root (i : ℕ)
    (hoff : ¬ (1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.compRows)) :
    lblC P Qc₀ c i = lblC P Qc₀ c 1 := by
  have hN := P.optimized.family.problem.cfg.compRows_pos
  unfold lblC
  by_cases hi : i - 1 < P.optimized.family.problem.cfg.compRows
  · have : i = 0 := by omega
    subst i
    rfl
  · rw [dif_neg hi, dif_pos (by omega : 1 - 1 < P.optimized.family.problem.cfg.compRows)]

theorem wrap_id_lblC_of_topology
    (htop : ComputeExactTopology (execOfTraces P Qc₀ Qm₀ c h))
    (i : ℕ) :
    (wrapComputeLabel (lblC P Qc₀ c i)).specialize (alphaM c.1) =
      lblC P Qc₀ c i := by
  by_cases hi : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.compRows
  · exact wrap_fixes_lblC P c Qc₀ i
      (fcomp_vcomp_of_topology P c Qc₀ Qm₀ h htop i hi.1 hi.2)
  · have heq := lblC_off_eq_root P c Qc₀ i hi
    have hv1 := fcomp_vcomp_of_topology P c Qc₀ Qm₀ h htop 1 le_rfl
      (Nat.succ_le_of_lt P.optimized.family.problem.cfg.compRows_pos)
    have hv : Vcomp (lblC P Qc₀ c i).2.1 (lblC P Qc₀ c i).2.2.1
        (lblC P Qc₀ c i).2.2.2 := by simpa [heq] using hv1
    exact wrap_fixes_lblC P c Qc₀ i hv

theorem specialized_computeTree_eq
    (htop : ComputeExactTopology (execOfTraces P Qc₀ Qm₀ c h)) :
    ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeTree =
      (execOfTraces P Qc₀ Qm₀ c h).computeTree := by
  rw [specialized_computeTree_map]
  change mapNTree (fun r => (wrapComputeLabel r).specialize (alphaM c.1))
      (reconTree (foC P Qc₀ c) (lblC P Qc₀ c)
        P.optimized.family.problem.cfg.compRows) =
    reconTree (foC P Qc₀ c) (lblC P Qc₀ c)
      P.optimized.family.problem.cfg.compRows
  rw [mapNTree_reconTree]
  refine reconTree_eq_of_lbl (foC P Qc₀ c)
    P.optimized.family.problem.cfg.compRows ?_
  intro i
  exact wrap_id_lblC_of_topology P c Qc₀ Qm₀ h htop i

/-- **Compute transport.**  `ComputeExactTopology` of `execOfTraces`
    is `ComputeExactTopology` of `specializedExec`. -/
theorem wrapSpecializeJoinCompute
    (htop : ComputeExactTopology (execOfTraces P Qc₀ Qm₀ c h)) :
    ComputeExactTopology
      ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda) := by
  change RVTWithArity (Fcomp (K := K))
    ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
      (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeTree
  rw [specialized_computeTree_eq P c Qc₀ Qm₀ h hz htop]
  exact htop

theorem specializedComputeTopology_of_exec
    (htop : ComputeExactTopology (execOfTraces P Qc₀ Qm₀ c h)) :
    specializedComputeTopology P c Qc₀ Qm₀ h hz :=
  wrapSpecializeJoinCompute P c Qc₀ Qm₀ h hz htop

/-! ## Memory: wrap is the identity at every `lblM` -/

theorem vmem_padding_mem_zero {inp : MemoryTable.Inputs K} {p : MemoryTable.Pub K}
    (hv : Vmem inp p) (hpad : memoryMemRecKind p.st = .padding) :
    p.mem = MemRec.zero := by
  cases hst : p.st with
  | decompose =>
    have heq : eqBlk inp p := hv.2.1
    simp only [eqBlk, hst] at heq
    exact heq.2.2.2
  | halt =>
    have heq : eqBlk inp p := hv.2.1
    simp only [eqBlk, hst] at heq
    exact heq.2.2.2.2.2.2
  | read_root =>
    simp [memoryMemRecKind, hst] at hpad
  | verify_child =>
    simp [memoryMemRecKind, hst] at hpad

theorem wrap_fixes_lblM_A (i : ℕ)
    (hst : (lblM P Qm₀ c i).1 = (lblM P Qm₀ c i).2.2.st)
    (hpow : memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
      MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts)
    (hpad : memoryMemRecKind (lblM P Qm₀ c i).1 = .padding →
      (lblM P Qm₀ c i).2.2.mem = MemRec.zero) :
    (wrapMemoryLabel (alphaM c.1) (lblM P Qm₀ c i)).specializeA (alphaM c.1) =
      lblM P Qm₀ c i :=
  wrap_fixes_vmem_row (alphaM c.1) (lblM P Qm₀ c i) hst hpow hpad

/-- **Parked memory half of the wrap identity.**  Statement: wrap then specialize is the identity on every `lblM` row. -/
def WrapMemoryIdentity : Prop :=
  ∀ i : ℕ,
    (wrapMemoryLabel (alphaM c.1) (lblM P Qm₀ c i)).specialize (alphaM c.1) c.2.2.2.lambda =
      lblM P Qm₀ c i

/-- The wrap identity for the memory half, on the a-bearing view
    (`specializeA`): this is what the old proof established and remains true.
    Does NOT replace the parked `WrapMemoryIdentity`. -/
theorem wrap_idA_lblM_of_topology
    (htop : ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest,
      RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t)
    (hpow : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
        MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts)
    (i : ℕ) :
    (wrapMemoryLabel (alphaM c.1) (lblM P Qm₀ c i)).specializeA (alphaM c.1) =
      lblM P Qm₀ c i := by
  by_cases hi : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows
  · have hF := fmem_of_topology P c Qc₀ Qm₀ h htop i hi.1 hi.2
    have hst : (lblM P Qm₀ c i).1 = (lblM P Qm₀ c i).2.2.st := hF.1.symm
    have hv : eqBlk (lblM P Qm₀ c i).2.1 (lblM P Qm₀ c i).2.2 := hF.2.1
    have hpad :
        memoryMemRecKind (lblM P Qm₀ c i).1 = .padding →
          (lblM P Qm₀ c i).2.2.mem = MemRec.zero := by
      intro hp
      have hst' : (lblM P Qm₀ c i).2.2.st = (lblM P Qm₀ c i).1 := hF.1
      have hp' : memoryMemRecKind (lblM P Qm₀ c i).2.2.st = .padding := by
        simpa [hst'] using hp
      simpa [hst'] using eqBlk_padding_mem_zero hv hp'
    exact wrap_fixes_lblM_A P c Qm₀ i hst (hpow i hi.1 hi.2) hpad
  · have heq := lblM_off_eq_root P c Qm₀ i hi
    have h1 : 1 ≤ P.optimized.family.problem.cfg.memRows :=
      Nat.succ_le_of_lt P.optimized.family.problem.cfg.memRows_pos
    have hF := fmem_of_topology P c Qc₀ Qm₀ h htop 1 le_rfl h1
    have hst : (lblM P Qm₀ c i).1 = (lblM P Qm₀ c i).2.2.st := by
      simpa [heq] using hF.1.symm
    have hv : eqBlk (lblM P Qm₀ c i).2.1 (lblM P Qm₀ c i).2.2 := by
      simpa [heq] using hF.2.1
    have hpad :
        memoryMemRecKind (lblM P Qm₀ c i).1 = .padding →
          (lblM P Qm₀ c i).2.2.mem = MemRec.zero := by
      intro hp
      have hst' : (lblM P Qm₀ c i).2.2.st = (lblM P Qm₀ c i).1 := by
        simpa [heq] using hF.1
      have hp' : memoryMemRecKind (lblM P Qm₀ c i).2.2.st = .padding := by
        simpa [hst'] using hp
      simpa [hst'] using eqBlk_padding_mem_zero hv hp'
    have hpow' :
        memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
          MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts := by
      intro hact
      have hact1 : memoryMemRecKind (lblM P Qm₀ c 1).1 = .active := by
        simpa [heq] using hact
      simpa [heq] using hpow 1 le_rfl h1 hact1
    exact wrap_fixes_lblM_A P c Qm₀ i hst hpow' hpad

theorem wrap_id_lblM_of_topology
    (hW : WrapMemoryIdentity P c Qm₀) (i : ℕ) :
    (wrapMemoryLabel (alphaM c.1) (lblM P Qm₀ c i)).specialize (alphaM c.1) c.2.2.2.lambda =
      lblM P Qm₀ c i := hW i

theorem specialized_memoryForest_map :
    ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryForest =
      (execOfTraces P Qc₀ Qm₀ c h).memoryForest.map
        (mapNTree (fun r =>
          (wrapMemoryLabel (alphaM c.1) r).specialize (alphaM c.1) c.2.2.2.lambda)) := by
  rw [specializedExec_eq]
  change
    ((execOfTraces P Qc₀ Qm₀ c h).memoryForest.map
        (mapNTree (wrapMemoryLabel (alphaM c.1)))).map
      (mapNTree (fun row => row.specialize (alphaM c.1) c.2.2.2.lambda)) =
    (execOfTraces P Qc₀ Qm₀ c h).memoryForest.map
      (mapNTree (fun r =>
        (wrapMemoryLabel (alphaM c.1) r).specialize (alphaM c.1) c.2.2.2.lambda))
  simp only [List.map_map]
  apply List.map_congr_left
  intro t _
  exact mapNTree_comp (wrapMemoryLabel (alphaM c.1))
    (fun row => row.specialize (alphaM c.1) c.2.2.2.lambda) t

theorem specialized_memoryForest_eq
    (htop : ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest,
      RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t)
    (hW : WrapMemoryIdentity P c Qm₀)
    (hpow : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
        MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts) :
    ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryForest =
      (execOfTraces P Qc₀ Qm₀ c h).memoryForest := by
  rw [specialized_memoryForest_map]
  change (reconForest P.optimized.family.problem.cfg.kMem
      (foM P Qm₀ c) (lblM P Qm₀ c)
      P.optimized.family.problem.cfg.memRows).map
      (mapNTree (fun r =>
        (wrapMemoryLabel (alphaM c.1) r).specialize (alphaM c.1) c.2.2.2.lambda)) =
    reconForest P.optimized.family.problem.cfg.kMem
      (foM P Qm₀ c) (lblM P Qm₀ c)
      P.optimized.family.problem.cfg.memRows
  rw [mapNTree_reconForest]
  refine reconForest_eq_of_lbl P.optimized.family.problem.cfg.kMem
    (foM P Qm₀ c) P.optimized.family.problem.cfg.memRows ?_
  intro i
  exact wrap_id_lblM_of_topology P c Qm₀ hW i

/-- **Memory transport (M′, β-free).**  The β-free memory topology of `execOfTraces`
    (`∀ t, RVTWithArity FmemTopo t`) is that of `specializedExec`, given the parked wrap
    identity `hW`.  Re-typed from the production `MemoryExactTopology` on both sides (M′,
    `m-prime-topo`); the production `MemoryExactTopology` is not concluded. -/
theorem wrapSpecializeJoin
    (htop : ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest,
      RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t)
    (hW : WrapMemoryIdentity P c Qm₀)
    (hpow : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
        MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts) :
    ∀ t ∈ ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryForest,
      RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t := by
  intro t ht
  have hforest := specialized_memoryForest_eq P c Qc₀ Qm₀ h hz htop hW hpow
  rw [hforest] at ht
  exact htop t ht

/-- The β-free twin of `Batch502.specializedMemoryTopology` (M′): the per-node predicate is
`FmemTopo`, not `Fmem`. -/
def specializedMemoryTopologyTopo : Prop :=
  ∀ t ∈ ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
      (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryForest,
    RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t

/-- Re-typed (M′): concludes the β-free `specializedMemoryTopologyTopo`, not the production
`Batch502.specializedMemoryTopology`. -/
theorem specializedMemoryTopology_of_exec
    (htop : ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest,
      RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t)
    (hW : WrapMemoryIdentity P c Qm₀)
    (hpow : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
        MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts) :
    specializedMemoryTopologyTopo P c Qc₀ Qm₀ h hz :=
  wrapSpecializeJoin P c Qc₀ Qm₀ h hz htop hW hpow

/-- Compiled remaining join after the mapNTree identity: active-row
    `MemPower` on `lblM`, including `verify_child`. -/
def remainingActiveMemPower : Prop :=
  ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
    memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
      MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts

end

end Nock.RedTeam.Batch509

#print axioms Nock.RedTeam.Batch509.openAfterWrapSpecialize_length
#print axioms Nock.RedTeam.Batch509.wrapSpecializeJoinCompute
#print axioms Nock.RedTeam.Batch509.wrapSpecializeJoin
#print axioms Nock.RedTeam.Batch509.mapNTree_congr_of_mem
