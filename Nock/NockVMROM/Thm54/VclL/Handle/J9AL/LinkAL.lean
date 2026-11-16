/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/LinkAL.lean

  **Helper: the J-9 AL twins of the cell-validity helpers of
  `SoundJ9A.soundA_core`.**
  * `claimRow0_eqAL`, `claimRecsT9_eqAL`: `LinkV1J9A.claimRow0_eqA` / `claimRecsT9_eqA` at `AcceptsJ9AL` (the compute
    context is `LinkV1J9A.xctxJ9A` at the `toPubJ9A` / `toTrJ9A` projections).
  * `rdV_viewAL`: the #2 / #3 readouts at `RR49AL.valReqsAL` (the AL consumer list).
  * `hcountCAL`: the consumer count `< p` (from `hlenCP`).
  * `hsumCAL`: the cell validity balance for the AL consumer list (`hsumC'` + `HbalJ9AL.aluFpL_sum`).
  * `claimX_factsAL`: `SoundJ9A.claimX_factsA` at `AcceptsJ9AL`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.SoundJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.HbalJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.RR49AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkAL

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsOK_J8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (AcceptsJ9AL pinRecsP)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.LinkV1J9A
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9Z (toMsgJ9Z)
open Nock.NockVMROM.Thm54.VclL.Handle.RealJ9 (claimX claimRow0 claimRecsT9)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9A (claimHJ9_snd)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qM qA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A (rAT)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G (hcountC9G)

noncomputable section

section Link
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`claimRow0_eqA` at `AcceptsJ9AL`.** -/
theorem claimRow0_eqAL (Pb : PubJ9AL p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) {r : RowsJ9AL} {g : ℕ} (hp : 20 < p)
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) (k : Fin 3) :
    claimRow0 Pb.toPubJ8 tr.toJ8 k = (((claimHJ9 p c M.m k).2 : ℕ) : ZMod p) := by
  have XC := xctxJ9A δ b Pb.toPubJ9A c χ M.toMsgJ9A' tr.toTrJ9A hp hacc.hsatX hacc.hinjX hacc.hadjX
  have hd := row0_hdA (tr := tr.toTrJ9A) δ b XC k
  have h2 := congrArg Prod.snd hd
  simp only [hdV] at h2
  have hv := ZMod.val_injective p h2
  have hk : (![xS, xF, xE] k).v < 123 := by fin_cases k <;> decide
  unfold claimRow0
  rw [← trace0_toJ8 δ b Pb.toPubJ9A c χ M.toMsgJ9A' tr.toTrJ9A _ hk]
  exact hv

/-- **`claimRecsT9_eqA` at `AcceptsJ9AL`.** -/
theorem claimRecsT9_eqAL (Pb : PubJ9AL p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) {r : RowsJ9AL} {g : ℕ} (hp : 20 < p)
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) :
    claimRecsT9 δ Pb.toPubJ8 c χ tr.toJ8 = claimRecsJ9 δ χ c M.m := by
  have hs : ∀ k, (isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) →
      claimRow0 Pb.toPubJ8 tr.toJ8 k = (((M.m k).1 : ℕ) : ZMod p) := fun k hk => by
    rw [claimRow0_eqAL δ b Pb Rg c χ M tr hp hacc k, claimHJ9_snd hk]
  unfold claimRecsT9 claimRecsJ9 claimRecsT claimRecsJ8 claimBigRecs
  congr 1
  · refine List.map_congr_left fun k hk => ?_
    have hc : isCellN (claimNoun c k) = true := (List.mem_filter.mp hk).2
    have := hs k (Or.inl hc)
    unfold claimRow0 at this
    rw [this]
  · refine List.map_congr_left fun k hk => ?_
    have hc : isBigN p (claimNoun c k) = true := (List.mem_filter.mp hk).2
    rw [hs k (Or.inr hc)]

/-- **The #2 / #3 readouts at the J-9 AL consumer list.** -/
theorem rdV_viewAL (Pb : PubJ9AL p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) {r : RowsJ9AL} {g : ℕ} (hp : 20 < p)
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) :
    RR49AL.valReqsAL δ b Pb c tr χ = ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ) ++
        (pinRecsP δ Pb χ ++ RR49AL.aluFpL δ b Pb tr χ)) ++
      cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
        (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
          (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
          (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC)) ∧
    RealVJ8.valProvsJ8 δ b Pb.toPubJ8 tr.toJ8 χ = SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC
      (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
        (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
        (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC))) ++
      (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).xsC := by
  have hw : 183 ≤ (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.w := by
    rw [cell_w]; norm_num
  refine ⟨?_, ?_⟩
  · show (claimRecsT9 δ Pb.toPubJ8 c χ tr.toJ8 ++ pinRecsJ8 δ Pb.toPubJ8 χ ++ (pinRecsP δ Pb χ ++ _)) ++ _ =
      (claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ ++ (pinRecsP δ Pb χ ++ _)) ++ _
    rw [claimRecsT9_eqAL δ b Pb Rg c χ M tr hp hacc, cVInt_chip]
    refine congrArg ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ ++ (pinRecsP δ Pb χ ++ RR49AL.aluFpL δ b Pb tr χ)) ++ ·) ?_
    exact cVInt_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.M (Fin.ext rfl)
  · show liftWts _ ++ mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (fun _ => 0) tr.A =
      liftWts _ ++ mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
        (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
    rw [cVRec_chip]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · exact congrArg liftWts
        (cVRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ (by norm_num) hw fun j hj => congrArg tr.M (Fin.ext rfl))
    · exact mbXs_congr δ b Pb.nodesA Pb.orbitA _ _ _ _ _ _ (by norm_num)
        (by rw [AtomChipHQ.atomChipHQ_width]; norm_num) (fun j hj => rfl) rfl rfl

/-- **`hcountC` at the J-9 AL message**: the consumers `≤ 3 + regs + prims + nL + 2 nC`. -/
theorem hcountCAL (Pb : PubJ9AL p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ9AL' p K δ)
    (tr : TrJ9AL (ZMod p))
    (hlen : 3 + Pb.regs.length + Pb.prims.length + Pb.nL + 2 * Pb.nC < p) :
    (((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ) ++ (pinRecsP δ Pb χ ++ RR49AL.aluFpL δ b Pb tr χ)) ++
      cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
        (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
          (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
          (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC))).length
      < p := by
  have h1 := claimRecsJ9_length δ χ c M.m
  have h2 : (cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
      (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
        (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC
        (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) (toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC))).length
      ≤ 2 * Pb.nC := by
    unfold cellVInternal
    refine (AcceptsJ8P.length_flatMap_le _ _ 2 fun i => ?_).trans (by simp)
    rw [List.length_append]
    split_ifs <;> simp
  have hP : (pinRecsP δ Pb χ).length = Pb.prims.length := by simp [pinRecsP]
  have hF : (RR49AL.aluFpL δ b Pb tr χ).length ≤ Pb.nL := by
    unfold RR49AL.aluFpL
    split_ifs
    · unfold aluFpReqsOf
      refine (AcceptsJ8P.length_flatMap_le _ _ 1 fun i => ?_).trans (by simp)
      split_ifs <;> simp
    · simp
  simp only [List.length_append, pinRecsJ8, List.length_map] at *
  omega

/-- **The cell validity balance at the J-9 AL consumer list** (twin of `soundA_core`'s `hsumC`). -/
theorem hsumCAL {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g : ℕ} (hpG : p = Nock.Atoms.p)
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) :
    ((((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ) ++ (pinRecsP δ Pb χ ++ RR49AL.aluFpL δ b Pb tr χ))).map
        fun r => (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
      Quad.mk _ ((toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC 0)
        ((toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).pubsC 1) +
      (((toMsgJ9Z δ b Pb.toPubJ8 c χ M.toMsgJ8' tr.toJ8).xsC).map fun x => x.2 * (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1)⁻¹).sum := by
  subst hpG
  have hA := HbalJ9AL.aluFpL_sum δ b χ hacc.hALk
  have hM := hacc.hsumC'
  show _ = _ + ((mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _).map _).sum
  rw [mbXs_sum δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ hacc.hsatA hacc.hbindA hacc.hinjA
    hacc.hadjA _ _ (chalsAJ8Z_ok δ χ)]
  simp only [List.map_append, List.sum_append] at hM ⊢
  show _ = Quad.mk _ (M.pubsC 0) (M.pubsC 1) + Quad.mk _ (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1))
  linear_combination hM + hA

/-- **`claimX_factsA` at `AcceptsJ9AL`.** -/
theorem claimX_factsAL {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g : ℕ} (hp : 20 < p)
    (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) :
    (∀ k, isBigN p (claimNoun c k) = true → claimNoun c k ∈ claimX (K := K) b Pb.toPubJ8 c tr.toJ8) ∧
    (∀ k, isBigN p (claimNoun c k) = true → ∀ m, extB p (rAT (K := K) b Pb.toPubJ8 tr.toJ8) (M.m k).1 = some m →
      m ∈ claimX (K := K) b Pb.toPubJ8 c tr.toJ8) ∧
    (∀ x ∈ claimX (K := K) b Pb.toPubJ8 c tr.toJ8, (∃ k, isBigN p (claimNoun c k) = true ∧ x = claimNoun c k) ∨
      ∃ j, extB p (rAT (K := K) b Pb.toPubJ8 tr.toJ8) j = some x) := by
  refine ⟨fun k hkb => List.mem_append_left _ (List.mem_map.mpr
    ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, rfl⟩), fun k hkb m hm => ?_, fun x hx => ?_⟩
  · have hI := hacc.hclI k (Or.inr hkb)
    have hr := claimRow0_eqAL δ b Pb Rg c χ M tr hp hacc k
    rw [claimHJ9_snd (Or.inr hkb)] at hr
    have hv : (claimRow0 Pb.toPubJ8 tr.toJ8 k).val = (M.m k).1 := by
      rw [hr]; show (((M.m k).1 : ℕ) : ZMod p).val = _; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hI]
    refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkb⟩, ?_⟩)
    show extB p (rAT (K := K) b Pb.toPubJ8 tr.toJ8) (claimRow0 Pb.toPubJ8 tr.toJ8 k).val = some m
    rw [hv]; exact hm
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact Or.inl ⟨k, (List.mem_filter.mp hk).2, rfl⟩
    · obtain ⟨k, -, hk⟩ := List.mem_filterMap.mp hx
      exact Or.inr ⟨_, hk⟩

end Link

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkAL
