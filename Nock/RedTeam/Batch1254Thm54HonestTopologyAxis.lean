import Nock.NockVMROM.Thm54.TemplateAxisStructure
import Nock.NockVMROM.Thm54.UniqueExponentsBridge
import Nock.RedTeam.Batch1024Thm54C2BindsAtCoin
import Nock.RedTeam.Batch1170Thm54ServedPathSlot
import Nock.RedTeam.Batch1250Thm54HonestGoodGenerated
import Nock.RedTeam.Batch500Thm54GammaTransport
import Nock.RedTeam.Batch974Thm54Round0WrapJoinForest
import Nock.RedTeam.Batch995Thm54HonestFormRTreeCore
import Nock.RedTeam.Batch999Thm54HonestPathValidity
import Nock.RedTeam.Batch733Thm54DecodedLambdaSlotMapReadSet
import Nock.RedTeam.Batch1140Thm54CertAxesAtTraces
import Nock.RedTeam.Batch1000Thm54HonestLambdaGenerated

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1254Thm54HonestTopologyAxis.lean

* `htopo_of_good` (any package, from acceptance + the pinned `hgood` + Form R side conditions): the Ev topology event
    is the C2 one (`specializedTopologyFailureEvent_agree`), whose bad-γ set is EMPTY.  No condition on `γ`.
  * `haxis_of_facts` / `haxis_pkg`: the R0 template's root axis tree is the decoded tree with round-0 cert axes
    (`templateAxisTree_eq_withA`); at the honest traces it is the renamed exact axis tree, so
    `vaxis = Relaxis` on every paired exponent and the guarded α-set is empty.
  * `T5.htopo_genPkg`, `T5.haxisEv_genPkg`: both at `genPkg` with only the pinned `hgood` beyond its binders.

  -- the paper
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1254

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Framework
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-! ## Generic transport of the compute binding through a payload-preserving relabelling -/

theorem rawComputeBinding_mapNTree (g : State × DTcomp K → State × DTcomp K)
    (hst : ∀ l, (g l).1 = l.1)
    (hs : ∀ l, (g l).2.2.1.s = l.2.2.1.s) (hf : ∀ l, (g l).2.2.1.f = l.2.2.1.f)
    (he : ∀ l, (g l).2.2.1.e = l.2.2.1.e)
    (hsf : ∀ l i, sfTriple (g l).2.2.1 i = sfTriple l.2.2.1 i)
    (t : NTree (State × DTcomp K)) (h : RawComputeTopologyBinding t) :
    RawComputeTopologyBinding (mapNTree g t) := by
  obtain ⟨hfan, hlink⟩ := h
  refine ⟨?_, ?_⟩
  · rw [mapNTree_label, hst, mapNTree_children, List.length_map]; exact hfan
  · intro i hi
    rw [mapNTree_label, hst] at hi
    have := hlink i hi
    simp only at this ⊢
    rw [childLabel_mapNTree, mapNTree_label, hsf, Option.map_map, ← this]
    apply Option.map_congr
    intro c _
    simp [Function.comp, hs, he, hf]

/-! ## The built compute / memory bindings at accepted traces outside the pinned event -/

section AtTraces

variable (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
  (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hacc hgood hax hbasis hwidth

/-- The decoded compute tree has the exact compute topology. -/
theorem execOfTraces_computeTopology :
    ComputeExactTopology
      (StrategyOfTracesLift.execOfTraces P.optimized (honestQc P c Qc) (honestQm P c Qm) c h) :=
  Nock.RedTeam.Batch500.computeTopology_of_deployed_of_good P c (honestQc P c Qc) (honestQm P c Qm)
    (by rw [Nock.RedTeam.Batch824.familyQc_honestQc]; exact hacc.compute_satisfies)
    (by rw [Nock.RedTeam.Batch824.familyQm_honestQm]; exact hacc.memory_satisfies)
    (FamilyIOChain.nprSeed_ne_of_good_at P c Qc Qm hgood)
    (Nock.RedTeam.Batch824.memStateTagChar_of_package P) hax hbasis hwidth
    (by rw [Nock.RedTeam.Batch824.familyQc_honestQc, Nock.RedTeam.Batch824.familyQm_honestQm];
        exact hacc) hgood

/-- **The built family base at the tuple's own coins has no topology bad `γ`.** -/
theorem topologyBadGammas_C2_empty (hz : nprSeed c.1 ≠ 0) :
    topologyBadGammas
      ((Nock.RedTeam.Batch1024.TC P c Qc Qm h).verifier.raw.afterAlphaM (nprSeed c.1) hz
        (alphaM c.1) c.2.2.2.lambda).familyData.base = ∅ := by
  apply MultiRootHonestArrays.topologyBadGammas_empty_of_binding
  constructor
  · intro t ht
    change t ∈ bfsForest [((Nock.RedTeam.Batch1024.TC P c Qc Qm h).specializedExec (nprSeed c.1) hz
      (alphaM c.1) c.2.2.2.lambda).computeTree] at ht
    rw [Nock.RedTeam.Batch1024.specialized_computeTree_C2,
      show [mapNTree (fun row => (StrategyOfTracesLift.wrapComputeLabel row).specialize (alphaM c.1))
          (StrategyOfTracesLift.execOfTraces P.optimized (honestQc P c Qc) (honestQm P c Qm) c
            h).computeTree] =
        [(StrategyOfTracesLift.execOfTraces P.optimized (honestQc P c Qc) (honestQm P c Qm) c
            h).computeTree].map
          (mapNTree (fun row => (StrategyOfTracesLift.wrapComputeLabel row).specialize (alphaM c.1)))
        from rfl, bfsForest_mapNTree] at ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    refine rawComputeBinding_mapNTree
      (fun row => (StrategyOfTracesLift.wrapComputeLabel row).specialize (alphaM c.1)) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun l i => by fin_cases i <;> rfl) t' ?_
    exact computeBinding_of_exactTopology
      (execOfTraces_computeTopology P c Qc Qm h hacc hgood hax hbasis hwidth) t' ht'
  · intro t ht
    change t ∈ bfsForest ((Nock.RedTeam.Batch1024.TC P c Qc Qm h).specializedExec (nprSeed c.1) hz
      (alphaM c.1) c.2.2.2.lambda).memoryForest at ht
    rw [specializedExec_C2_eq, StrategyOfTracesR0A.specializedExec_R0A_eq,
      Nock.RedTeam.Batch974.specialized_memoryForest_R0_eq P c Qc Qm hacc hgood hax hbasis hwidth h hz]
      at ht
    rw [mem_bfsForest] at ht
    obtain ⟨root, hroot, hin⟩ := ht
    have htop := Nock.RedTeam.Batch974.decoded_topology P c Qc Qm hacc hgood hax hbasis hwidth root hroot
    have hF := ((RVT_iff_forall_InTree (FmemTopo (K := K)) root).1 htop.1 t hin).1
    exact ⟨fanout_eq_children_length_of_properArity (mem_stateSep_topo (K := K)) htop.1 htop.2 t hin,
      hF.2.2.2⟩

/-- **`htopo` at any package**, at accepted traces outside the pinned event. -/
theorem htopo_of_good :
    c.1 ∉ specializedTopologyFailureEvent
      (builtStrategyEv P (honestQc P c Qc) (honestQm P c Qm)).verifier.raw c.2.2.2.lambda := by
  have h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c :=
    (Nock.RedTeam.Batch940.tracesWalkHyps_iff P c _ _).2
      (Nock.RedTeam.Batch489.tracesWalkHyps_of_deployed P c (honestQc P c Qc) (honestQm P c Qm)
        (by rw [Nock.RedTeam.Batch824.familyQc_honestQc]; exact hacc.compute_satisfies)
        (by rw [Nock.RedTeam.Batch824.familyQm_honestQm]; exact hacc.memory_satisfies)
        (Nock.RedTeam.Batch824.memStateTagChar_of_package P) hax hbasis hwidth
        (by rw [Nock.RedTeam.Batch824.familyQc_honestQc, Nock.RedTeam.Batch824.familyQm_honestQm];
            exact hacc) hgood)
  have hagree := specializedTopologyFailureEvent_agree P.optimized (honestQc P c Qc)
    (honestQm P c Qm) P.stateTagChar c h c.2.2.2.lambda
  intro hmem
  have hmem' : c.1 ∈ specializedTopologyFailureEvent
      (Nock.RedTeam.Batch1024.TC P c Qc Qm h).verifier.raw c.2.2.2.lambda := by
    rw [hagree]; exact hmem
  rw [mem_specializedTopologyFailureEvent_iff] at hmem'
  obtain ⟨hz, hbad⟩ := hmem'
  rw [topologyBadGammas_C2_empty P c Qc Qm h hacc hgood hax hbasis hwidth hz] at hbad
  exact absurd hbad (Finset.notMem_empty _)

end AtTraces

end

end Nock.RedTeam.Batch1254



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch1254.T2

open Nock Nock.Walk Nock.Reified
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

noncomputable section

/-! ## §A  Writing the verify axes -/

section MT

variable {K : Type} [Field K]

/-- Replace every verify node's `a` by `A` of its exponent. -/
def withA (A : ℕ → K) : MTree K → MTree K
  | .halt => .halt
  | .decompose l r => .decompose (withA A l) (withA A r)
  | .read e c => .read e (withA A c)
  | .verify e _ c => .verify e (A e) (withA A c)

theorem readCount_withA (A : ℕ → K) (e : ℕ) : ∀ t : MTree K, readCount e (withA A t) = readCount e t
  | .halt => rfl
  | .decompose l r => by simp [withA, readCount, readCount_withA A e l, readCount_withA A e r]
  | .read e' c => by simp [withA, readCount, readCount_withA A e c]
  | .verify e' _ c => by simp [withA, readCount, readCount_withA A e c]

theorem verifyCount_withA (A : ℕ → K) (e : ℕ) :
    ∀ t : MTree K, verifyCount e (withA A t) = verifyCount e t
  | .halt => rfl
  | .decompose l r => by simp [withA, verifyCount, verifyCount_withA A e l, verifyCount_withA A e r]
  | .read e' c => by simp [withA, verifyCount, verifyCount_withA A e c]
  | .verify e' _ c => by simp [withA, verifyCount, verifyCount_withA A e c]

theorem vdep_withA (A : ℕ → K) (e : ℕ) : ∀ t : MTree K, vdep e (withA A t) = vdep e t
  | .halt => rfl
  | .decompose l r => by
      simp [withA, vdep, verifyCount_withA, vdep_withA A e l, vdep_withA A e r]
  | .read e' c => by simp [withA, vdep, vdep_withA A e c]
  | .verify e' _ c => by simp [withA, vdep, vdep_withA A e c]

theorem vaddr_withA (A : ℕ → K) (e : ℕ) : ∀ t : MTree K, vaddr e (withA A t) = vaddr e t
  | .halt => rfl
  | .decompose l r => by
      simp [withA, vaddr, verifyCount_withA, vdep_withA, vaddr_withA A e l, vaddr_withA A e r]
  | .read e' c => by simp [withA, vaddr, vaddr_withA A e c]
  | .verify e' _ c => by simp [withA, vaddr, vaddr_withA A e c]

theorem Relaxis_withA (A : ℕ → K) (e : ℕ) : ∀ t : MTree K, Relaxis e (withA A t) = Relaxis e t
  | .halt => rfl
  | .decompose l r => by
      simp [withA, Relaxis, readCount_withA, Relaxis_withA A e l, Relaxis_withA A e r]
  | .read e' c => by simp [withA, Relaxis, vaddr_withA, vdep_withA, Relaxis_withA A e c]
  | .verify e' _ c => by simp [withA, Relaxis, Relaxis_withA A e c]

theorem vaxis_withA (A : ℕ → K) (e : ℕ) :
    ∀ t : MTree K, verifyCount e t = 1 → vaxis e (withA A t) = A e
  | .halt, h => by simp [verifyCount] at h
  | .decompose l r, h => by
      simp only [verifyCount] at h
      simp only [withA, vaxis, verifyCount_withA]
      split_ifs with hl
      · exact vaxis_withA A e l hl
      · exact vaxis_withA A e r (by omega)
  | .read e' c, h => by
      simp only [verifyCount] at h
      simp only [withA, vaxis]
      exact vaxis_withA A e c h
  | .verify e' _ c, h => by
      simp only [withA, vaxis]
      split_ifs with he
      · rw [he]
      · simp only [verifyCount, if_neg he, zero_add] at h
        exact vaxis_withA A e c h

theorem readExps_withA (A : ℕ → K) : ∀ t : MTree K, readExps (withA A t) = readExps t
  | .halt => rfl
  | .decompose l r => by simp [withA, readExps, readExps_withA A l, readExps_withA A r]
  | .read e c => by simp [withA, readExps, readExps_withA A c]
  | .verify e _ c => by simp [withA, readExps, readExps_withA A c]

theorem verifyExps_withA (A : ℕ → K) : ∀ t : MTree K, verifyExps (withA A t) = verifyExps t
  | .halt => rfl
  | .decompose l r => by simp [withA, verifyExps, verifyExps_withA A l, verifyExps_withA A r]
  | .read e c => by simp [withA, verifyExps, verifyExps_withA A c]
  | .verify e _ c => by simp [withA, verifyExps, verifyExps_withA A c]

end MT

/-! ## §B  The committed template axis tree IS the decoded tree with the supplied axes -/

section Link

variable {F K : Type} [Field F] [Field K] [DecidableEq F] [Fintype F] {M : ℕ}
variable (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ)

theorem buildTF_node_gen (fo : ℕ → ℕ) (lbl : ℕ → MemoryRowTemplate (K := K))
    (hSf : kroots + Sf (foOfMem envsF) M = M) (hvalid : BFSValidF kroots (foOfMem envsF) M)
    (hfo : ∀ j, 1 ≤ j → j ≤ M → fo j = foOfMem envsF j)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ M) :
    buildTF kroots fo lbl M i =
      NTree.node (lbl i)
        ((List.range' (childIdx envsF kroots i 1)
          (MemoryTable.fanoutMem (memRowStateOf (envsF ⟨i - 1, by omega⟩)))).map
          (buildTF kroots fo lbl M)) := by
  have hSfeq : ∀ n, n ≤ M → Sf fo n = Sf (foOfMem envsF) n := fun n hn =>
    Nock.RedTeam.Batch1170.Sf_congr_le' _ _ n fun j hj1 hj2 => hfo j hj1 (by omega)
  have hSf' : kroots + Sf fo M = M := by rw [hSfeq M le_rfl]; exact hSf
  have hv' : BFSValidF kroots fo M := by
    intro j hj1 hj2
    rw [hSfeq (j - 1) (by omega)]
    exact hvalid j hj1 hj2
  have hch := childIdxsF_eq kroots fo M hSf' hv' h1 h2
  have hfc : firstCF kroots fo i = childIdx envsF kroots i 1 := by
    unfold firstCF childIdx
    rw [hSfeq (i - 1) (by omega)]
    omega
  have hfoi : fo i = MemoryTable.fanoutMem (memRowStateOf (envsF ⟨i - 1, by omega⟩)) := by
    rw [hfo i h1 h2]; unfold foOfMem; rw [dif_pos ⟨h1, by omega⟩]
  rw [← hfc, ← hfoi, ← hch, ← buildTF_children]
  conv_lhs => rw [show buildTF kroots fo lbl M i =
    NTree.node (buildTF kroots fo lbl M i).label (buildTF kroots fo lbl M i).children by
      cases buildTF kroots fo lbl M i; rfl]
  rw [buildTF_label]

theorem child_le (hSf : kroots + Sf (foOfMem envsF) M = M) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ M)
    (l : ℕ) (hl : 1 ≤ l) (hlf : l ≤ foOfMem envsF i) : childIdx envsF kroots i l ≤ M := by
  unfold childIdx
  have hs : Sf (foOfMem envsF) i = Sf (foOfMem envsF) (i - 1) + foOfMem envsF i := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [Walk.Sf_succ]; simp
  have hm := Walk.Sf_mono (foOfMem envsF) h2
  omega

theorem templateAxisTree_eq_withA (fo : ℕ → ℕ) (lbl : ℕ → MemoryRowTemplate (K := K)) (A : ℕ → K)
    (hSf : kroots + Sf (foOfMem envsF) M = M) (hvalid : BFSValidF kroots (foOfMem envsF) M)
    (hfo : ∀ j, 1 ≤ j → j ≤ M → fo j = foOfMem envsF j)
    (hst : ∀ j (h : 1 ≤ j ∧ j ≤ M),
      (lbl j).timestamp.state = memRowStateOf (envsF ⟨j - 1, by omega⟩))
    (hex : ∀ j (h : 1 ≤ j ∧ j ≤ M),
      (lbl j).timestamp.recordExponent = rowExp envsF ⟨j - 1, by omega⟩)
    (hax : ∀ j (h : 1 ≤ j ∧ j ≤ M),
      (lbl j).placeholder.2.2.mem.axis = A (rowExp envsF ⟨j - 1, by omega⟩)) :
    ∀ i, 1 ≤ i → i ≤ M →
      templateAxisTree (buildTF kroots fo lbl M i) =
        withA A (decodedMTreeOfEnvs envsK envsF kroots i) := by
  intro i
  induction hm : M + 1 - i using Nat.strong_induction_on generalizing i with
  | _ d ih =>
  intro h1 h2
  have hnode := buildTF_node_gen envsF kroots fo lbl hSf hvalid hfo i h1 h2
  have hkid : ∀ l, 1 ≤ l → l ≤ foOfMem envsF i →
      templateAxisTree (buildTF kroots fo lbl M (childIdx envsF kroots i l)) =
        withA A (decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i l)) := by
    intro l hl hlf
    have hlt := Nock.RedTeam.Batch1170.child_lt envsF kroots hSf hvalid i h1 h2 l hl
    have hc := child_le envsF kroots hSf i h1 h2 l hl hlf
    exact ih (M + 1 - childIdx envsF kroots i l) (by omega) _ rfl (by omega) hc
  have hfoi : foOfMem envsF i = MemoryTable.fanoutMem (memRowStateOf (envsF ⟨i - 1, by omega⟩)) := by
    unfold foOfMem; rw [dif_pos ⟨h1, by omega⟩]
  have hc1 := Nock.RedTeam.Batch1170.child_lt envsF kroots hSf hvalid i h1 h2 1 le_rfl
  have hc2 := Nock.RedTeam.Batch1170.child_lt envsF kroots hSf hvalid i h1 h2 2 (by omega)
  have hc12 : childIdx envsF kroots i 2 = childIdx envsF kroots i 1 + 1 := by
    unfold childIdx; omega
  have hsti := hst i ⟨h1, h2⟩
  rw [hnode]
  rcases hs : memRowStateOf (envsF ⟨i - 1, by omega⟩) with _ | _ | _ | _
  · -- decompose
    rw [hs] at hsti hfoi
    rw [tree_decompose_of envsK envsF kroots i ⟨h1, h2⟩ hs, if_pos hc1, if_pos hc2]
    simp only [MemoryTable.fanoutMem] at hfoi ⊢
    rw [show List.range' (childIdx envsF kroots i 1) 2 =
      [childIdx envsF kroots i 1, childIdx envsF kroots i 1 + 1] by simp [List.range'_succ]]
    simp only [List.map_cons, List.map_nil]
    have k1 := hkid 1 le_rfl (by omega)
    have k2 := hkid 2 (by omega) (by omega)
    rw [hc12] at k2
    simp only [templateAxisTree, hsti, withA]
    rw [k1, k2, hc12]
  · -- halt
    rw [tree_halt_of envsK envsF kroots i ⟨h1, h2⟩ hs]
    rw [hs] at hsti
    simp [templateAxisTree, hsti, withA]
  · -- read_root
    rw [hs] at hsti hfoi
    rw [tree_read_of envsK envsF kroots i ⟨h1, h2⟩ hs, if_pos hc1]
    simp only [MemoryTable.fanoutMem] at hfoi ⊢
    simp only [List.range'_one, List.map_cons, List.map_nil]
    have k1 := hkid 1 le_rfl (by omega)
    simp only [templateAxisTree, hsti, withA]
    rw [k1, hex i ⟨h1, h2⟩]
  · -- verify_child
    rw [hs] at hsti hfoi
    rw [tree_verify_of envsK envsF kroots i ⟨h1, h2⟩ hs, if_pos hc1]
    simp only [MemoryTable.fanoutMem] at hfoi ⊢
    simp only [List.range'_one, List.map_cons, List.map_nil]
    have k1 := hkid 1 le_rfl (by omega)
    simp only [templateAxisTree, hsti, withA]
    rw [k1, hex i ⟨h1, h2⟩, hax i ⟨h1, h2⟩]

end Link

end

end Nock.RedTeam.Batch1254.T2



set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1254.T3

open Nock Nock.Walk
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.RedTeam.Batch995 (exps InjOnExps mem_exps_decompose_l mem_exps_decompose_r
  mem_exps_read_c mem_exps_verify_c mem_exps_read_self mem_exps_verify_self rn)

noncomputable section

section MT

variable {K : Type} [Field K]

theorem readExps_reindex (f : ℕ → ℕ) : ∀ t : MTree K,
    readExps (reindexAxisTree f t) = (readExps t).map f
  | .halt => rfl
  | .decompose l r => by simp [reindexAxisTree, readExps, readExps_reindex f l, readExps_reindex f r]
  | .read e c => by simp [reindexAxisTree, readExps, readExps_reindex f c]
  | .verify e _ c => by simp [reindexAxisTree, readExps, readExps_reindex f c]

theorem verifyExps_reindex (f : ℕ → ℕ) : ∀ t : MTree K,
    verifyExps (reindexAxisTree f t) = (verifyExps t).map f
  | .halt => rfl
  | .decompose l r => by
      simp [reindexAxisTree, verifyExps, verifyExps_reindex f l, verifyExps_reindex f r]
  | .read e c => by simp [reindexAxisTree, verifyExps, verifyExps_reindex f c]
  | .verify e _ c => by simp [reindexAxisTree, verifyExps, verifyExps_reindex f c]

theorem exps_reindex (f : ℕ → ℕ) (t : MTree K) :
    exps (reindexAxisTree f t) = (exps t).map f := by
  simp [exps, readExps_reindex, verifyExps_reindex]

variable (f : ℕ → ℕ) (S : ℕ → Prop) (hf : InjOnExps f S) (e : ℕ) (he : S e)
include hf he

theorem readCount_reindex :
    ∀ t : MTree K, (∀ x ∈ exps t, S x) → readCount (f e) (reindexAxisTree f t) = readCount e t
  | .halt, _ => rfl
  | .decompose l r, hS => by
      simp only [reindexAxisTree, readCount]
      rw [readCount_reindex l fun x hx => hS x (mem_exps_decompose_l hx),
        readCount_reindex r fun x hx => hS x (mem_exps_decompose_r hx)]
  | .read e' c, hS => by
      simp only [reindexAxisTree, readCount]
      rw [readCount_reindex c fun x hx => hS x (mem_exps_read_c hx)]
      have : f e' = f e ↔ e' = e :=
        ⟨hf e' e (hS e' (mem_exps_read_self e' c)) he, fun h => h ▸ rfl⟩
      simp only [this]
  | .verify e' _ c, hS => by
      simp only [reindexAxisTree, readCount]
      exact readCount_reindex c fun x hx => hS x (mem_exps_verify_c hx)

theorem verifyCount_reindex :
    ∀ t : MTree K, (∀ x ∈ exps t, S x) → verifyCount (f e) (reindexAxisTree f t) = verifyCount e t
  | .halt, _ => rfl
  | .decompose l r, hS => by
      simp only [reindexAxisTree, verifyCount]
      rw [verifyCount_reindex l fun x hx => hS x (mem_exps_decompose_l hx),
        verifyCount_reindex r fun x hx => hS x (mem_exps_decompose_r hx)]
  | .read e' c, hS => by
      simp only [reindexAxisTree, verifyCount]
      exact verifyCount_reindex c fun x hx => hS x (mem_exps_read_c hx)
  | .verify e' _ c, hS => by
      simp only [reindexAxisTree, verifyCount]
      rw [verifyCount_reindex c fun x hx => hS x (mem_exps_verify_c hx)]
      have : f e' = f e ↔ e' = e :=
        ⟨hf e' e (hS e' (mem_exps_verify_self e' _ c)) he, fun h => h ▸ rfl⟩
      simp only [this]

theorem vdep_reindex :
    ∀ t : MTree K, (∀ x ∈ exps t, S x) → vdep (f e) (reindexAxisTree f t) = vdep e t
  | .halt, _ => rfl
  | .decompose l r, hS => by
      simp only [reindexAxisTree, vdep]
      rw [verifyCount_reindex f S hf e he l fun x hx => hS x (mem_exps_decompose_l hx),
        vdep_reindex l fun x hx => hS x (mem_exps_decompose_l hx),
        vdep_reindex r fun x hx => hS x (mem_exps_decompose_r hx)]
  | .read e' c, hS => by
      simp only [reindexAxisTree, vdep]
      exact vdep_reindex c fun x hx => hS x (mem_exps_read_c hx)
  | .verify e' _ c, hS => by
      simp only [reindexAxisTree, vdep]
      rw [vdep_reindex c fun x hx => hS x (mem_exps_verify_c hx)]
      have : f e' = f e ↔ e' = e :=
        ⟨hf e' e (hS e' (mem_exps_verify_self e' _ c)) he, fun h => h ▸ rfl⟩
      simp only [this]

theorem vaddr_reindex :
    ∀ t : MTree K, (∀ x ∈ exps t, S x) → vaddr (f e) (reindexAxisTree f t) = vaddr e t
  | .halt, _ => rfl
  | .decompose l r, hS => by
      simp only [reindexAxisTree, vaddr]
      rw [verifyCount_reindex f S hf e he l fun x hx => hS x (mem_exps_decompose_l hx),
        vaddr_reindex l fun x hx => hS x (mem_exps_decompose_l hx),
        vaddr_reindex r fun x hx => hS x (mem_exps_decompose_r hx),
        vdep_reindex f S hf e he r fun x hx => hS x (mem_exps_decompose_r hx)]
  | .read e' c, hS => by
      simp only [reindexAxisTree, vaddr]
      exact vaddr_reindex c fun x hx => hS x (mem_exps_read_c hx)
  | .verify e' _ c, hS => by
      simp only [reindexAxisTree, vaddr]
      rw [vaddr_reindex c fun x hx => hS x (mem_exps_verify_c hx)]
      have : f e' = f e ↔ e' = e :=
        ⟨hf e' e (hS e' (mem_exps_verify_self e' _ c)) he, fun h => h ▸ rfl⟩
      simp only [this]

theorem Relaxis_reindex :
    ∀ t : MTree K, (∀ x ∈ exps t, S x) → Relaxis (f e) (reindexAxisTree f t) = Relaxis e t
  | .halt, _ => rfl
  | .decompose l r, hS => by
      simp only [reindexAxisTree, Relaxis]
      rw [readCount_reindex f S hf e he l fun x hx => hS x (mem_exps_decompose_l hx),
        Relaxis_reindex l fun x hx => hS x (mem_exps_decompose_l hx),
        Relaxis_reindex r fun x hx => hS x (mem_exps_decompose_r hx)]
  | .read e' c, hS => by
      simp only [reindexAxisTree, Relaxis]
      rw [Relaxis_reindex c fun x hx => hS x (mem_exps_read_c hx),
        vaddr_reindex f S hf e he c fun x hx => hS x (mem_exps_read_c hx),
        vdep_reindex f S hf e he c fun x hx => hS x (mem_exps_read_c hx)]
      have : f e' = f e ↔ e' = e :=
        ⟨hf e' e (hS e' (mem_exps_read_self e' c)) he, fun h => h ▸ rfl⟩
      simp only [this]
  | .verify e' _ c, hS => by
      simp only [reindexAxisTree, Relaxis]
      exact Relaxis_reindex c fun x hx => hS x (mem_exps_verify_c hx)

theorem vaxis_reindex :
    ∀ t : MTree K, (∀ x ∈ exps t, S x) → vaxis (f e) (reindexAxisTree f t) = vaxis e t
  | .halt, _ => rfl
  | .decompose l r, hS => by
      simp only [reindexAxisTree, vaxis]
      rw [verifyCount_reindex f S hf e he l fun x hx => hS x (mem_exps_decompose_l hx),
        vaxis_reindex l fun x hx => hS x (mem_exps_decompose_l hx),
        vaxis_reindex r fun x hx => hS x (mem_exps_decompose_r hx)]
  | .read e' c, hS => by
      simp only [reindexAxisTree, vaxis]
      exact vaxis_reindex c fun x hx => hS x (mem_exps_read_c hx)
  | .verify e' _ c, hS => by
      simp only [reindexAxisTree, vaxis]
      rw [vaxis_reindex c fun x hx => hS x (mem_exps_verify_c hx)]
      have : f e' = f e ↔ e' = e :=
        ⟨hf e' e (hS e' (mem_exps_verify_self e' _ c)) he, fun h => h ▸ rfl⟩
      simp only [this]

end MT

/-! ## The honest walk's topological axis at each read is its service's axis -/

section Walk

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {cfg : ExactConfig F K} {exec : ExactExecution cfg} {services : List (Service cfg exec)}

theorem walk_Relaxis {n : Noun} {t : MTree K} (h : ServiceWalk services n t) :
    (readExps t).Nodup →
      ∀ e ∈ readExps t, ∃ s ∈ services, s.exponent = e ∧ Relaxis e t = ((s.axis : ℕ) : K) := by
  induction h with
  | halt => intro _ e he; simp [readExps] at he
  | @decompose nl nr l r hl hr ihl ihr =>
      intro hrnd e he
      rw [readExps] at hrnd he
      have hrl : (readExps l).Nodup := hrnd.of_append_left
      have hrr : (readExps r).Nodup := hrnd.of_append_right
      have hrdis : (readExps l).Disjoint (readExps r) := List.disjoint_of_nodup_append hrnd
      rcases List.mem_append.mp he with hel | her
      · have hrl1 : readCount e l = 1 := readCount_eq_one_of_mem e l hrl hel
        simp only [Relaxis, if_pos hrl1]
        exact ihl hrl e hel
      · have hrl0 : readCount e l = 0 := by
          rw [readCount_eq_count, List.count_eq_zero_of_not_mem (fun hc => hrdis hc her)]
        simp only [Relaxis, show readCount e l ≠ 1 by omega, if_false]
        exact ihr hrr e her
  | @read n e' c s hs he hroot route below ih =>
      intro hrnd e hmem
      rw [readExps] at hrnd hmem
      rcases List.mem_cons.mp hmem with rfl | hec
      · obtain ⟨-, -, -, -, hdep, hvaddr, -⟩ := route.spec
        refine ⟨s, hs, he, ?_⟩
        have hpath : pathAxis (axisPath s.axis) = s.axis := pathAxis_axisPath s.axis s.axis_pos
        simp only [Relaxis, hvaddr, hdep, if_pos]
        calc (pathAddress (axisPath s.axis) : K) + (2 : K) ^ (axisPath s.axis).length
            = ((pathAxis (axisPath s.axis) : ℕ) : K) := by
              simp [pathAxis, Nat.cast_add, Nat.cast_pow]
          _ = ((s.axis : ℕ) : K) := by rw [hpath]
      · have hne : e' ≠ e := by
          intro hEq
          exact (List.nodup_cons.mp hrnd).1 (hEq ▸ hec)
        simp only [Relaxis, if_neg hne]
        exact ih (List.nodup_cons.mp hrnd).2 e hec
  | @verify n e' a c below ih =>
      intro hrnd e hmem
      rw [readExps] at hrnd hmem
      simp only [Relaxis]
      exact ih hrnd e hmem

end Walk

end

end Nock.RedTeam.Batch1254.T3


namespace Nock.RedTeam.Batch1254.T4

open scoped Polynomial Classical
open Polynomial
open Nock Nock.Walk Nock.Reified Nock.Framework
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.RedTeam.Batch1254.T2 (withA readCount_withA verifyCount_withA vaxis_withA Relaxis_withA
  readExps_withA verifyExps_withA templateAxisTree_eq_withA)
open Nock.RedTeam.Batch1254.T3 (readExps_reindex verifyExps_reindex exps_reindex vaxis_reindex
  Relaxis_reindex verifyCount_reindex walk_Relaxis)
open Nock.RedTeam.Batch995 (exps InjOnExps rn)

noncomputable section

/-! ## §A  Generic: validity of the built tree from the honest tree -/

section Generic

variable {K : Type} [Field K]

theorem withA_rn (A : ℕ → K) (g : ℕ → ℕ) :
    ∀ t : MTree K, withA A (rn g t) = withA A (reindexAxisTree g t)
  | .halt => rfl
  | .decompose l r => by
      simp only [rn, reindexAxisTree, withA, withA_rn A g l, withA_rn A g r]
  | .read e c => by simp only [rn, reindexAxisTree, withA, withA_rn A g c]
  | .verify e _ c => by simp only [rn, reindexAxisTree, withA, withA_rn A g c]

theorem exps_withA (A : ℕ → K) (t : MTree K) : exps (withA A t) = exps t := by
  simp [exps, readExps_withA, verifyExps_withA]

/-- **The built tree is valid wherever the honest tree's reads have the supplied axis.** -/
theorem built_valid (Xh : MTree K) (g ρ : ℕ → ℕ) (A : ℕ → K)
    (hg : InjOnExps g (fun x => x ∈ exps Xh))
    (hρ : InjOnExps ρ (fun x => x ∈ exps (reindexAxisTree g Xh)))
    (hVn : (verifyExps Xh).Nodup)
    (hW : ∀ e0 ∈ readExps Xh, Relaxis e0 Xh = A (g e0)) :
    ∀ e, e ∈ readExps (reindexAxisTree ρ (withA A (reindexAxisTree g Xh))) →
      e ∈ verifyExps (reindexAxisTree ρ (withA A (reindexAxisTree g Xh))) →
      vaxis e (reindexAxisTree ρ (withA A (reindexAxisTree g Xh))) =
        Relaxis e (reindexAxisTree ρ (withA A (reindexAxisTree g Xh))) := by
  intro e hr hv
  rw [readExps_reindex, readExps_withA, readExps_reindex] at hr
  rw [verifyExps_reindex, verifyExps_withA, verifyExps_reindex] at hv
  obtain ⟨e1, he1, rfl⟩ := List.mem_map.mp hr
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he1
  obtain ⟨e1', he1', hρeq⟩ := List.mem_map.mp hv
  obtain ⟨e0', he0', rfl⟩ := List.mem_map.mp he1'
  have hx0 : e0 ∈ exps Xh := by simp [exps, he0]
  have hx0' : e0' ∈ exps Xh := by simp [exps, he0']
  have hgx : ∀ x ∈ exps Xh, g x ∈ exps (reindexAxisTree g Xh) := by
    intro x hx; rw [exps_reindex]; exact List.mem_map_of_mem hx
  have hge : g e0' = g e0 := hρ _ _ (hgx _ hx0') (hgx _ hx0) hρeq
  have hee : e0' = e0 := hg _ _ hx0' hx0 hge
  subst hee
  have hS : ∀ x ∈ exps (withA A (reindexAxisTree g Xh)), x ∈ exps (reindexAxisTree g Xh) := by
    intro x hx; rwa [exps_withA] at hx
  have hvc : verifyCount e0' Xh = 1 := verifyCount_eq_one_of_mem e0' Xh hVn he0'
  have hvc' : verifyCount (g e0') (reindexAxisTree g Xh) = 1 := by
    rw [verifyCount_reindex g (fun x => x ∈ exps Xh) hg e0' hx0' Xh (fun x hx => hx)]; exact hvc
  rw [vaxis_reindex ρ (fun x => x ∈ exps (reindexAxisTree g Xh)) hρ (g e0') (hgx _ hx0')
      _ hS,
    Relaxis_reindex ρ (fun x => x ∈ exps (reindexAxisTree g Xh)) hρ (g e0') (hgx _ hx0') _ hS,
    vaxis_withA A (g e0') _ hvc', Relaxis_withA,
    Relaxis_reindex g (fun x => x ∈ exps Xh) hg e0' hx0' Xh (fun x hx => hx)]
  exact (hW e0' he0).symm

end Generic

/-! ## §B  The certificate axis round trip -/

theorem certAxis_cert (a : ℕ) (ha : 1 ≤ a) (c : ℕ → Bool)
    (hc : ∀ k, 1 ≤ k → c k = MemoryTable.formRCertBit a (k - 1)) :
    StrategyOfTracesR0.certAxis (MemoryTable.formRCertShift a) c = a := by
  rw [Nock.RedTeam.Batch1170.certAxis_eq_pathAxis]
  have := Nock.RedTeam.Batch995.bitsOf_cert_eq_axisPath a ha c hc
  rw [show Nock.RedTeam.Batch554.bitsOf (MemoryTable.formRCertShift a) c =
    Nock.RedTeam.Batch554.bitsOf (MemoryTable.formRCertShift a) c from rfl] at this
  rw [this]
  exact pathAxis_axisPath a ha

/-! ## §B'  At any package: `haxis` from the honest-tree facts -/

section AnyP

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
variable (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X]) (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)

/-- The round-0 template row axis function. -/
abbrev AR : ℕ → K := fun e =>
  ((certAxisOfEnvs (computeEnvsR0 P.optimized (honestQc P c Qc) c) e : ℕ) : K)

include h in
/-- **`haxis` at any package**, from: the walk hypotheses `h`; the decoded tree of every root is a
renaming `rn g` of a tree `Xh i` (`hdec`); `g` injective on `Xh i`'s exponents with values below
`orderOf (alphaM c.1)`; unique verify exponents; and every read of `Xh i` has topological axis
`AR (g e)` (`hW`). -/
theorem haxis_of_facts
    (envsK : Fin P.optimized.family.problem.cfg.memRows → Env K)
    (Xh : Fin P.optimized.family.problem.cfg.kMem → MTree K) (g : ℕ → ℕ)
    (hdec : ∀ i : Fin P.optimized.family.problem.cfg.kMem,
      decodedMTreeOfEnvs envsK (memoryEnvsR0 P.optimized (honestQm P c Qm) c)
        P.optimized.family.problem.cfg.kMem ((i : ℕ) + 1) = rn g (Xh i))
    (hg : ∀ i, InjOnExps g (fun x => x ∈ exps (Xh i)))
    (hlt : ∀ i, ∀ x ∈ exps (Xh i), g x < orderOf (alphaM c.1))
    (hVn : ∀ i, (verifyExps (Xh i)).Nodup)
    (hW : ∀ i, ∀ e0 ∈ readExps (Xh i), Relaxis e0 (Xh i) = AR P c Qc (g e0)) :
    c.1 ∉ envelopeAxisFailureEvent (builtStrategyEv P (honestQc P c Qc) (honestQm P c Qm))
      c.2.2.2.lambda := by
  intro hmem
  have hmem' : c.1 ∈ envelopeAxisFailureEvent (Nock.RedTeam.Batch1024.TC P c Qc Qm h)
      c.2.2.2.lambda := by
    rw [envelopeAxisFailureEvent_agree P.optimized (honestQc P c Qc) (honestQm P c Qm)
      P.stateTagChar c h]
    exact hmem
  rw [mem_envelopeAxisFailureEvent_iff] at hmem'
  obtain ⟨hz, hα⟩ := hmem'
  have hα' := envelopeRootUnion_subset _ _ hα
  obtain ⟨i, -, hf⟩ := Finset.mem_biUnion.1 hα'
  simp only [verifierGuardedRootAlphas, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  obtain ⟨-, -, ⟨e, hread, hverify, hne⟩, -⟩ := hf
  rw [exactAxisTree_specialize, recoveredAxisTree_eq_reindexAxisTree] at hread hverify hne
  -- the committed root tree
  let i' : Fin P.optimized.family.problem.cfg.kMem := ⟨i.1, i.2⟩
  have htmt : templateMemoryTreeAt (committedTemplate (Nock.RedTeam.Batch1024.TC P c Qc Qm h).verifier
      (nprSeed c.1) hz) i =
      buildTF P.optimized.family.problem.cfg.kMem
        (StrategyOfTracesLift.foM P.optimized (honestQm P c Qm) c)
        (lblMR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
        P.optimized.family.problem.cfg.memRows ((i : ℕ) + 1) := by
    unfold templateMemoryTreeAt
    show (reconForest _ _ _ _).get _ = _
    simp [reconForest, List.get_eq_getElem, Nat.add_comm]
    all_goals (erw [List.get_eq_getElem, List.getElem_map, List.getElem_range']; simp [Nat.add_comm])
  -- the link facts
  have hM := P.optimized.family.problem.cfg.memRows_pos
  set envsF := memoryEnvsR0 P.optimized (honestQm P c Qm) c with henvsF
  have hfo : ∀ j, 1 ≤ j → j ≤ P.optimized.family.problem.cfg.memRows →
      StrategyOfTracesLift.foM P.optimized (honestQm P c Qm) c j = foOfMem envsF j := by
    intro j hj1 hj2
    have hj : j - 1 < P.optimized.family.problem.cfg.memRows := by omega
    simp only [StrategyOfTracesLift.foM, StrategyOfTracesLift.lblM, dif_pos hj, foOfMem,
      dif_pos (show 1 ≤ j ∧ j - 1 < P.optimized.family.problem.cfg.memRows from ⟨hj1, hj⟩)]
    rfl
  have hSfeq : Sf (StrategyOfTracesLift.foM P.optimized (honestQm P c Qm) c)
      P.optimized.family.problem.cfg.memRows = Sf (foOfMem envsF) P.optimized.family.problem.cfg.memRows :=
    Nock.RedTeam.Batch1170.Sf_congr_le' _ _ _ fun j hj1 hj2 => hfo j hj1 hj2
  have hSf : P.optimized.family.problem.cfg.kMem + Sf (foOfMem envsF)
      P.optimized.family.problem.cfg.memRows = P.optimized.family.problem.cfg.memRows := by
    rw [← hSfeq]; exact h.sfMemory
  have hvalid : BFSValidF P.optimized.family.problem.cfg.kMem (foOfMem envsF)
      P.optimized.family.problem.cfg.memRows := by
    intro j hj1 hj2
    rw [← Nock.RedTeam.Batch1170.Sf_congr_le' _ _ (j - 1) fun k hk1 hk2 => hfo k hk1 (by omega)]
    exact h.validMemory j hj1 hj2
  have hst : ∀ j (hj : 1 ≤ j ∧ j ≤ P.optimized.family.problem.cfg.memRows),
      (lblMR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c j).timestamp.state =
        memRowStateOf (envsF ⟨j - 1, by omega⟩) := by
    intro j hj
    have hj' : j - 1 < P.optimized.family.problem.cfg.memRows := by omega
    simp only [lblMR0, wrapR0OfEnvs, wrapMemoryLabelR0_state, StrategyOfTracesLift.lblM, dif_pos hj']
    rfl
  have hex : ∀ j (hj : 1 ≤ j ∧ j ≤ P.optimized.family.problem.cfg.memRows),
      (lblMR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c j).timestamp.recordExponent =
        rowExp envsF ⟨j - 1, by omega⟩ := by
    intro j hj
    have hj' : j - 1 < P.optimized.family.problem.cfg.memRows := by omega
    simp only [lblMR0, wrapR0OfEnvs, wrapMemoryLabelR0_recordExponent, memRowExpOfEnvs, dif_pos hj']
    rfl
  have hax : ∀ j (hj : 1 ≤ j ∧ j ≤ P.optimized.family.problem.cfg.memRows),
      (lblMR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c j).placeholder.2.2.mem.axis =
        AR P c Qc (rowExp envsF ⟨j - 1, by omega⟩) := by
    intro j hj
    have hj' : j - 1 < P.optimized.family.problem.cfg.memRows := by omega
    simp only [lblMR0, wrapR0OfEnvs, wrapMemoryLabelR0, memRowExpOfEnvs, dif_pos hj', AR]
    rfl
  have hlink := templateAxisTree_eq_withA envsK envsF P.optimized.family.problem.cfg.kMem
    (StrategyOfTracesLift.foM P.optimized (honestQm P c Qm) c)
    (lblMR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c) (AR P c Qc) hSf hvalid hfo hst hex hax
    ((i : ℕ) + 1) (by omega)
    (by have hi := i.2; change (i : ℕ) < P.optimized.family.problem.cfg.kMem at hi; omega)
  rw [htmt, hlink, hdec i', withA_rn] at hread hverify hne
  have hρ : InjOnExps (recoveredExponent (alphaM c.1))
      (fun x => x ∈ exps (reindexAxisTree g (Xh i'))) := by
    intro a b ha hb hab
    rw [exps_reindex] at ha hb
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
    exact recoveredExponent_injOn_Iio_orderOf (alphaM c.1) (Set.mem_Iio.mpr (hlt i' a0 ha0))
      (Set.mem_Iio.mpr (hlt i' b0 hb0)) hab
  exact hne (built_valid (Xh i') g (recoveredExponent (alphaM c.1)) (AR P c Qc) (hg i') hρ (hVn i')
    (hW i') e hread hverify)

end AnyP

/-! ## §C  At the generated-shape package -/

section Pkg

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb' : ℕ}

variable (E : BuildableNockExecution F K) (I : BuildableChips.Inputs E) (R : CommitmentResidual E)
  (hzero : I.computeChallenges =
    (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
  (hprl : RowLayout.PairedRecordLayout E.exec)
  (hmore : BuildableAxisWitness.LaterSeedZeros E)
  (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
  (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
  (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
  (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
  (hF : GeneratedField.PrimeFieldElems F)

local notation "PK" => Nock.RedTeam.Batch999.Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF

/-- The decoded tree at the round-0 memory envs of the honest traces is the renamed honest axis
tree (`Batch999.decoded_eq_axisTree`, through the memory read-set congruence). -/
theorem decoded_at_R0 (hC : E.exec.CprimeCoherent) (envsK : Fin E.cfg.memRows → Env K)
    (i : Fin E.cfg.kMem) :
    decodedMTreeOfEnvs envsK
        (memoryEnvsR0 (PK).optimized
          (honestQm (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QmH (PK))) (PK).honestTuple)
        E.cfg.kMem ((i : ℕ) + 1) =
      rn (Nock.RedTeam.Batch998.gExp E) (exactAxisTree E.cfg E.execA i) := by
  have hag : Nock.RedTeam.Batch733.MemoryAgree
      (memoryEnvsR0 (PK).optimized
        (honestQm (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QmH (PK))) (PK).honestTuple)
      (Nock.RedTeam.Batch999.envsF E I R hzero hprl hmore hord hordM hrows hgenF hF) := by
    intro r col _
    rw [← memoryBaseEnv_trace (PK) _ (PK).honestTuple r, Nock.RedTeam.Batch906.honestQm_QmH]
  exact (Nock.RedTeam.Batch733.decodedMTreeOfEnvs_congr hag envsK
    (Nock.RedTeam.Batch999.envsK E I R hzero hprl hmore hord hordM hrows hgenF hF) E.cfg.kMem
      ((i : ℕ) + 1)).trans
    (Nock.RedTeam.Batch999.decoded_eq_axisTree E I R hzero hprl hmore hord hordM hrows hgenF hF hC i)

/-- The round-0 compute envs of the honest traces read the canonical certificate columns. -/
theorem certAxisOfEnvs_R0 :
    certAxisOfEnvs (computeEnvsR0 (PK).optimized
        (honestQc (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QcH (PK))) (PK).honestTuple) =
      certAxisOfEnvs (Nock.RedTeam.Batch997.envsC (PK)) := by
  refine Nock.RedTeam.Batch970.certAxisOfEnvs_congr fun i col _ => ?_
  have hfam : FamilyEnvCore.familyQc (PK).optimized (PK).honestTuple
      (honestQc (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QcH (PK))) =
      Nock.RedTeam.Batch906.QcH (PK) :=
    Nock.RedTeam.Batch824.familyQc_honestQc (PK) _ _
  have htr : (computeEnvsR0 (PK).optimized
      (honestQc (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QcH (PK))) (PK).honestTuple i).trace =
      (Nock.RedTeam.Batch824.envsCR (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QcH (PK)) i).trace := by
    unfold computeEnvsR0
    rw [hfam]
    exact (Nock.RedTeam.Batch823.envsC_trace (PK) _ _ i).symm
  rw [htr]
  show ((PK).computeSourceEnv (honestQc (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QcH (PK))) i).trace col = _
  rw [Nock.RedTeam.Batch906.honestQc_QcH]

/-- **The recovered axis at a service's decoded exponent is the service's axis.** -/
theorem certAxis_at_svc (hax : FormRAxisBound (PK).optimized.sampled (PK).optimized.basis)
    (hwidth : FormRWidth F)
    (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K)
    (i : Fin E.cfg.kMem) {s : Service E.cfg E.execA} (hs : s ∈ (E.memoryTrace.roots i).services) :
    certAxisOfEnvs (computeEnvsR0 (PK).optimized
        (honestQc (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QcH (PK))) (PK).honestTuple)
        (Nock.RedTeam.Batch998.gExp E s.exponent) = s.axis := by
  rw [certAxisOfEnvs_R0]
  have hd := Nock.RedTeam.Batch999.decoded_svc E I R hzero hprl hmore hord hordM hrows hgenF hF hax hwidth
    hsvc i hs
  unfold certAxisOfEnvs
  rw [hd.1]
  exact certAxis_cert s.axis s.axis_pos _ hd.2

/-- The walk hypotheses at the honest tuple from acceptance and the pinned event. -/
theorem walkHyps_of_good (P : OptimizedFullStrictNockVMROMPackage F K hOrb')
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis) (hwidth : FormRWidth F) :
    StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c :=
  (Nock.RedTeam.Batch940.tracesWalkHyps_iff P c _ _).2
    (Nock.RedTeam.Batch489.tracesWalkHyps_of_deployed P c (honestQc P c Qc) (honestQm P c Qm)
      (by rw [Nock.RedTeam.Batch824.familyQc_honestQc]; exact hacc.compute_satisfies)
      (by rw [Nock.RedTeam.Batch824.familyQm_honestQm]; exact hacc.memory_satisfies)
      (Nock.RedTeam.Batch824.memStateTagChar_of_package P) hax hbasis hwidth
      (by rw [Nock.RedTeam.Batch824.familyQc_honestQc, Nock.RedTeam.Batch824.familyQm_honestQm];
          exact hacc) hgood)

/-- **`haxis` at the generated-shape package** (`buildFullPackage E …`, the shape the
`nockCompiles` chain builds): the honest tuple is outside the envelope-guarded axis event at the
built strategy of the honest traces. -/
theorem haxis_pkg
    (hacc : DeployedAcceptanceAt (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QcH (PK))
      (Nock.RedTeam.Batch906.QmH (PK)))
    (hgood : (PK).honestTuple ∉ (PK).optimizedFailureEvent
      (honestQc (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QcH (PK)))
      (honestQm (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QmH (PK))))
    (hax : FormRAxisBound (PK).optimized.sampled (PK).optimized.basis)
    (hbasis : FormRBasis (PK).optimized.basis) (hwidth : FormRWidth F)
    (hC : E.exec.CprimeCoherent)
    (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K)
    (hordα : (Nock.RedTeam.Batch998.reqList E).length + 1 < orderOf (alphaM (PK).honestTuple.1)) :
    (PK).honestTuple.1 ∉ envelopeAxisFailureEvent
      (builtStrategyEv (PK) (honestQc (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QcH (PK)))
        (honestQm (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QmH (PK))))
      (PK).honestTuple.2.2.2.lambda := by
  have h := walkHyps_of_good (PK) (PK).honestTuple _ _ hacc hgood hax hbasis hwidth
  refine haxis_of_facts (PK) (PK).honestTuple (Nock.RedTeam.Batch906.QcH (PK))
    (Nock.RedTeam.Batch906.QmH (PK)) h
    (Nock.RedTeam.Batch999.envsK E I R hzero hprl hmore hord hordM hrows hgenF hF)
    (fun i => exactAxisTree E.cfg E.execA i) (Nock.RedTeam.Batch998.gExp E)
    (fun i => decoded_at_R0 E I R hzero hprl hmore hord hordM hrows hgenF hF hC _ i)
    (fun i => Nock.RedTeam.Batch998.gExp_inj E i) ?_
    (fun i => (E.memoryTrace.roots i).verifyExps_nodup (E.memoryTrace.rootTimestampPowersNodup i)) ?_
  · intro i x hx
    have hle : Nock.RedTeam.Batch998.gExp E x ≤ (Nock.RedTeam.Batch998.reqList E).length + 1 := by
      unfold Nock.RedTeam.Batch998.gExp RecordCarrier.honestExp
      have := List.idxOf_le_length (l := Nock.RedTeam.Batch998.reqList E)
        (a := NockVM.encRecFormR (Nock.RedTeam.Batch998.recOf E x) E.cfg.challenges.lam)
      omega
    omega
  · intro i e0 he0
    have hts := E.memoryTrace.rootTimestampPowersNodup i
    obtain ⟨s, hs, rfl, hrel⟩ := walk_Relaxis (E.memoryTrace.roots i).traversal
      ((E.memoryTrace.roots i).readExps_nodup hts) e0 he0
    rw [hrel]
    show ((s.axis : ℕ) : K) = ((certAxisOfEnvs _ (Nock.RedTeam.Batch998.gExp E s.exponent) : ℕ) : K)
    rw [certAxis_at_svc E I R hzero hprl hmore hord hordM hrows hgenF hF hax hwidth hsvc i hs]

end Pkg

end

end Nock.RedTeam.Batch1254.T4

namespace Nock.RedTeam.Batch1254.T5

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Framework
open Nock.Framework.Thm54
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.RedTeam.Batch1061 (genPkg gen_honest_accepted)
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

section Generated

variable {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K}





set_option quotPrecheck false in
set_option hygiene false in
local notation "GP" => genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
  hinterCard hhon hprl hmore hord hordM hrows

set_option quotPrecheck false in
set_option hygiene false in
local notation "EG" => genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
  hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
  haxis hbad hout hKszChar hprogCap hmemCap hfirst

set_option quotPrecheck false in
set_option hygiene false in
local notation "IG" => inputsOfCarrier (EG) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n
  hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon


/-- **`htopo` at the generated package**, at the honest tuple and honest traces. -/
theorem htopo_genPkg
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hgood : (GP).honestTuple ∉ (GP).optimizedFailureEvent
      (honestQc (GP) (GP).honestTuple (QcH (GP))) (honestQm (GP) (GP).honestTuple (QmH (GP)))) :
    (GP).honestTuple.1 ∉ specializedTopologyFailureEvent
      (builtStrategyEv (GP) (honestQc (GP) (GP).honestTuple (QcH (GP)))
        (honestQm (GP) (GP).honestTuple (QmH (GP)))).verifier.raw (GP).honestTuple.2.2.2.lambda := by
  have G := Nock.RedTeam.Batch993.hgoodFill_generated (F := F) (K := K) stc hK pOrbit hcap n hreq
    hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hacc := gen_honest_accepted (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
    hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  exact Nock.RedTeam.Batch1254.htopo_of_good (GP) (GP).honestTuple _ _ hacc hgood G.hax
    (compilerBasis_formR (F := F) (K := K) hK) G.hwidth

/-- **`haxis` (the envelope axis summand) at the generated package.** -/
theorem haxisEv_genPkg
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hgood : (GP).honestTuple ∉ (GP).optimizedFailureEvent
      (honestQc (GP) (GP).honestTuple (QcH (GP))) (honestQm (GP) (GP).honestTuple (QmH (GP)))) :
    (GP).honestTuple.1 ∉ envelopeAxisFailureEvent
      (builtStrategyEv (GP) (honestQc (GP) (GP).honestTuple (QcH (GP)))
        (honestQm (GP) (GP).honestTuple (QmH (GP)))) (GP).honestTuple.2.2.2.lambda := by
  have G := Nock.RedTeam.Batch993.hgoodFill_generated (F := F) (K := K) stc hK pOrbit hcap n hreq
    hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hacc := gen_honest_accepted (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
    hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hαeq : chal.α = α := by
    have hproj := congrArg (fun inp : ComputeTable.Inputs K => inp.α) hinp
    simpa [ChallengeVector.computeInputs] using hproj
  refine Nock.RedTeam.Batch1254.T4.haxis_pkg _ _ _ _ _ _ _ _ _ _ _ hacc hgood G.hax
    (compilerBasis_formR (F := F) (K := K) hK) G.hwidth
    (Nock.RedTeam.Batch1000.genBuildableOfProgram_cprimeCoherent z α hz htwo a b c chal hinp hmi Ksz
      orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
      hbad hout hKszChar hprogCap hmemCap hfirst)
    (Nock.RedTeam.Batch1000.genBuildableOfProgram_serviceAxes_lt z α hz htwo a b c chal hinp hmi Ksz
      orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
      hbad hout hKszChar hprogCap hmemCap hfirst) ?_
  show _ < orderOf chal.α
  rw [hαeq]
  have hlen := genExactExecution_derivedRequestIO_length (F := F) z α chal Ksz orbit horb a b c t
    (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem
  have hlen' : (EG).exec.derivedRequestIO.length =
      accAt (airReorder t) (bfsRows (airReorder t)).length := hlen
  change (EG).exec.derivedRequestIO.length + 1 < orderOf α
  omega

end Generated

end

end Nock.RedTeam.Batch1254.T5

#print axioms Nock.RedTeam.Batch1254.T5.htopo_genPkg
#print axioms Nock.RedTeam.Batch1254.T5.haxisEv_genPkg
#print axioms Nock.RedTeam.Batch1254.htopo_of_good
#print axioms Nock.RedTeam.Batch1254.T4.haxis_pkg
#print axioms Nock.RedTeam.Batch1254.T4.haxis_of_facts
