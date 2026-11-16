/-
  Nock/RedTeam/Batch2176Thm54VSQNonVacToy.lean

  Measured: compute rows `1`, cell rows `1` (the formula), walk rows `1` (the dummy root: no path read), heights
  `1 1 1`, leaf bound `2`, axis bound `0`.  Every premise of `hsoundVSQ_premises_nonempty` is a closed lemma.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.NonVacVSQ
import Nock.RedTeam.Batch1997Thm54WalkW4dToys
import Nock.NockVMROM.Thm54.VclL.Handle.HonestOp5NC

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Nock.RedTeam.Batch2176

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.RedTeam.Batch1259 (subj0 form0 T0)
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.PullVSQ
open Nock.RedTeam.Batch1956 (instFactSevenNS δ7 hK3_toy h1_32 hbound_toy hs_toy hf_toy hrun_toy)
open Nock.RedTeam.Batch1997 (instFactRCFp instAlgRCFp)
open Nock.RedTeam.Batch1938 (goldilocks_hq)
open Nock.RedTeam.Batch1955 (goldilocks_orbit_dvd)

local notation "Fp" => Nock.Field.Fp
local notation "Kc" => Nock.Field.K

noncomputable section

attribute [local instance] Classical.propDecidable

theorem rows_T0 : bfsRows (airReorder (T0 (K := Fp))) =
    [skelNode (genSkelOp1 subj0 form0 (.atom 0) (.atom 1)) [⟨form0, .atom 0, 3, 0⟩]] := by
  rw [Batch1259.air0, Batch1259.bfsRows0]

theorem nNr_T0 : nNr (T0 (K := Fp)) = 1 := by
  show (bfsForest [airReorder T0]).length = 1
  rw [Batch1259.air0, Batch1259.bfs_leaf]; rfl

theorem nCr_T0 : nCr (T0 (K := Fp)) = 1 := by
  show (demandH2 (bfsRows (airReorder T0))).cells.length = 1
  rw [rows_T0]; decide +kernel

theorem cells_T0 : (demandH2 (bfsRows (airReorder (T0 (K := Fp))))).cells = [form0] := by
  rw [rows_T0]; decide +kernel

theorem roots_T0 : walkRoots (demandH2 (bfsRows (airReorder (T0 (K := Fp))))).preads = [] := by
  rw [rows_T0]; decide +kernel

theorem nWr_T0 : nWr (T0 (K := Fp)) = 1 := by
  show (walkRows (demandH2 (bfsRows (airReorder T0))).cells (demandH2 (bfsRows (airReorder T0))).preads).length = 1
  unfold walkRows walkForest
  rw [if_pos roots_T0, cells_T0, List.headD_cons]
  have : trie form0 form0 [] [] = NTree.node (trie form0 form0 [] []).label [] := rfl
  rw [this, Batch1259.bfs_leaf]; rfl

theorem op5_T0 : programOp5DepthOK (T0 (K := Fp)) :=
  programOp5DepthOK_of_leafBound Batch1259.gen0 (by rw [Batch1259.leaf0]; norm_num)

theorem heights_T0 : max (hCq (T0 (K := Fp))) (max (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp)))) = 1 := by
  show max (VclL.Compute.TowerChosen.heightOf (nNr T0)) (max (VclL.Compute.TowerChosen.heightOf (nCr T0))
    (VclL.Compute.TowerChosen.heightOf (nWr T0))) = 1
  rw [nNr_T0, nCr_T0, nWr_T0]; simp [VclL.Compute.TowerChosen.heightOf]

theorem hFd_T0 : 3 * 2 ^ (max (hCq (T0 (K := Fp))) (max (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))))) ∣
    Fintype.card Fp - 1 := by
  rw [heights_T0]; exact goldilocks_orbit_dvd (by norm_num)

theorem hcK_toy : Fintype.card Kc = VclL.Events.cK := by
  rw [Nock.Field.card_K, VclL.Events.cK_eq, Nock.Field.p_eq]

theorem hleaf_T0 : programLeafBound (airReorder (T0 (K := Fp))) ≤ 2 := (Batch1259.leaf0).le

theorem haxis_T0 : Compute.programAxisBound (airReorder (T0 (K := Fp))) < 2 ^ 63 := by
  rw [Batch1956.axis_T0]; norm_num

abbrev kr0 : ℕ := krW (demandH2 (runRowsH (T0 (K := Fp)))).cells (demandH2 (runRowsH (T0 (K := Fp)))).preads

/-- **Every premise of `hsoundVSQ` at `*[0 [1 0]]`, NO hypotheses**: a verifier datum `V` whose claim is
`⟨0, [1 0], 0⟩`, a staged message `msg` and a coin `χ` with `hV`, `AcceptsG V msg χ` and `hout`. -/
theorem hsoundVSQ_premises_toy :
    ∃ (V : VerifierData Fp Kc (hCq (T0 (K := Fp))) (shapeVSQ (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp)))))
      (msg : MessagesG (compCoreVSQ δ7 (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) (hCq (T0 (K := Fp)))
          (sumCVSQ (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) (hCq (T0 (K := Fp)))))
        (memCoreVSQ δ7 (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) kr0 (hCq (T0 (K := Fp)))
          (sumMVSQ δ7 (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) kr0 (hCq (T0 (K := Fp))))))
      (χ : Coins frameVSQ Kc),
      V.claim = ⟨subj0, form0, .atom 0⟩ ∧
      V.Checks (fun a => (compCoreVSQ δ7 (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) (hCq (T0 (K := Fp)))
            (sumCVSQ (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) (hCq (T0 (K := Fp))))).reqBound V a +
          (memCoreVSQ δ7 (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) kr0 (hCq (T0 (K := Fp)))
            (sumMVSQ δ7 (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) kr0 (hCq (T0 (K := Fp))))).internalBound V a)
        (ringChar (Quad (algebraMap Fp Kc δ7))) ∧
      TracesStaged frameVSQ (tableVSQ (hCq (T0 (K := Fp)))) (shapeVSQ (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))))
        msg.traces ∧
      AcceptsG V msg χ ∧
      ∀ s ∈ allSummandsG (CC := compCoreVSQ δ7 (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) (hCq (T0 (K := Fp)))
            (sumCVSQ (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) (hCq (T0 (K := Fp)))))
          (MC := memCoreVSQ δ7 (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) kr0 (hCq (T0 (K := Fp)))
            (sumMVSQ δ7 (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) kr0 (hCq (T0 (K := Fp)))))
          V msg.msg0C msg.msg0M (jointVSQ δ7 (hTq (T0 (K := Fp))) (hPq (T0 (K := Fp))) (hCq (T0 (K := Fp)))),
        ¬ s.mem (msg.traces χ) χ :=
  hsoundVSQ_premises_nonempty (δF := δ7) hrun_toy Batch1259.gen0 hK3_toy hFd_T0
    (GeneratedField.primeFieldElems_zmod Nock.Field.p) goldilocks_hq hleaf_T0 (by norm_num) haxis_T0 op5_T0
    (by rw [nCr_T0]; norm_num) (by rw [nWr_T0]; norm_num) (by rw [nNr_T0]; norm_num)
    hbound_toy hs_toy hf_toy hcK_toy

end

end Nock.RedTeam.Batch2176

#print axioms Nock.RedTeam.Batch2176.hsoundVSQ_premises_toy
#print axioms Nock.RedTeam.Batch2176.nCr_T0
#print axioms Nock.RedTeam.Batch2176.nWr_T0
#print axioms Nock.RedTeam.Batch2176.op5_T0
#print axioms Nock.RedTeam.Batch2176.hcK_toy
