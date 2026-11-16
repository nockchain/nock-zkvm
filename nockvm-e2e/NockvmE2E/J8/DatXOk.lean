/-
(route (c)): **`datX_ok`**, `DatumOK ∧ StmtP` at the static datum
`DX` over any J-8-shaped, jet-free instance `XI` (empty registry, census-corner rows, `g = 2^31`, `Pb = PbOfX XI …`).
Nothing here mentions `AcceptsJ8V`, a trace, or the value of `ω` (only its exact order, through `geom_PbOfX`).
-/
import NockvmE2E.Exec.E2EJ8
import NockvmE2E.J8.RVUJ8
import NockvmE2E.Exec.Field
import Nock.Jet.VerifiedRegistry

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J8.DatXOk

open NockvmE2E.J8.InstJ8
open Nock.TraceGenExe (KC)
open Nock.Jet.ChipJ8 (layoutJ8)
open NockvmE2E.Exec.V (ExecInst)
open NockvmE2E.Exec.E2EJ8.J8X (DatX)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (jCount)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (censusG claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (cornerC)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (corner31 RowsLe)

noncomputable section

/-- an empty layout has no keys -/
theorem jCount_zero (es : List (Nock.Jet.ChipJ8.Kd × List Nock.Jet.ChipJ8.KE)) {n : ℕ} (lay : Fin n → Nock.Jet.ChipJ8.PRow)
    (h : n = 0) : jCount es lay = 0 := by
  subst h; simp [jCount]

/-- the empty layout of an instance without a jet table -/
def layNil (XI : ExecInst) (hJ : hNof XI "jetChipJ8" = 0) : Fin (hNof XI "jetChipJ8") → Nock.Jet.ChipJ8.PRow :=
  fun i => absurd (i.2.trans_eq hJ) (Nat.not_lt_zero _)

/-- the claim side conditions of `StmtP` -/
structure ClaimOK (c : Nock.NockVMROM.Thm54.P8PublicClaim) : Prop where
  hclA : ∀ k : Fin 3, ∀ v, claimNoun c k = .atom v → v < P
  hclR : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < P
  hcen : ∀ x ∈ (claimCells c).map (claimNoun c), x.leaves ≤ Nock.NockVMROM.Thm54.VclL.fuelChip ∧ ∀ v ∈ x.leafList, v < P
  hcellF : isCellN c.formula = true

/-- the static datum over `XI`: empty registry, claim `c`, corner rows, `g = 2^31`; `Pb`, `hN`, `ω` are overwritten by `ofData`
(the three equations are `rfl`) -/
def DX (XI : ExecInst) (hsh : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) (hJ : hNof XI "jetChipJ8" = 0) (kroots krootsV : ℕ)
    (c : Nock.NockVMROM.Thm54.P8PublicClaim) : DatX XI hsh :=
  DatX.ofData XI hsh kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ)
    ⟨PbOfX XI hsh (posX_of_shape hsh) kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ),
      Nock.Jet.VerifiedRegistry.empty.R, c, cornerC, 2 ^ 31, 0, 0⟩

theorem census_eq (XI : ExecInst) (hsh : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) (hJ : hNof XI "jetChipJ8" = 0)
    (kroots krootsV : ℕ) (c : Nock.NockVMROM.Thm54.P8PublicClaim) :
    censusG (PbOfX XI hsh (posX_of_shape hsh) kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ)) c
      = (claimCells c).map (claimNoun c) := rfl

/-- the datum, unfolded -/
theorem DX_d (XI : ExecInst) (hsh : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) (hJ : hNof XI "jetChipJ8" = 0) (kroots krootsV : ℕ)
    (c : Nock.NockVMROM.Thm54.P8PublicClaim) :
    (DX XI hsh hJ kroots krootsV c).d =
      ⟨PbOfX XI hsh (posX_of_shape hsh) kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ),
        Nock.Jet.VerifiedRegistry.empty.R, c, cornerC, 2 ^ 31, XI.hN, ω0 XI⟩ := rfl

theorem datX_ok (XI : ExecInst) (hsh : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) (hJ : hNof XI "jetChipJ8" = 0)
    (kroots krootsV : ℕ) (hk1 : 1 ≤ kroots) (hkW : kroots ≤ hNof XI "walkChipJ8")
    (hV : (tabOf XI "walkChipHQK").isSome = true → 1 ≤ krootsV ∧ krootsV ≤ hNof XI "walkChipHQK")
    (c : Nock.NockVMROM.Thm54.P8PublicClaim) (hc : ClaimOK c) :
    DatumOK (DX XI hsh hJ kroots krootsV c).d ∧ StmtP (DX XI hsh hJ kroots krootsV c).d := by
  have hle := hN_le hsh
  have hnA := hNof_le XI hsh "atomChipHQL"
  have hnC := hNof_le XI hsh "cellChipHQKW"
  have hn := hNof_le XI hsh "computeChipVCLHX"
  have hnW := hNof_le XI hsh "walkChipJ8"
  have hk1' : 1 ≤ XI.hN := by rw [hN_of_shape' hsh]; exact Nat.one_le_two_pow
  have hnV := nV_le XI hsh hk1'
  have hP : (2 : ℕ) * 2 ^ 26 + 4 < P := by norm_num [P, Nock.Field.p]
  have hrc : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n P
  have hg := geom_PbOfX XI hsh (posX_of_shape hsh) kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ)
  have j0 := jCount_zero Nock.Jet.ChipJ8.ents2T (layNil XI hJ) hJ
  have j1 := jCount_zero Nock.Jet.ChipJ8.ents3 (layNil XI hJ) hJ
  have j2 := jCount_zero Nock.Jet.ChipJ8.entsX (layNil XI hJ) hJ
  have j3 := jCount_zero Nock.Jet.ChipJ8.ents0T (layNil XI hJ) hJ
  have j4 := jCount_zero Nock.Jet.ChipJ8.ents1T (layNil XI hJ) hJ
  rw [DX_d]
  have hcard : Fintype.card KC = Nock.NockVMROM.Thm54.VclL.Events.cK := by
    rw [Nock.TraceGenExe.KC_card]; exact Nock.NockVMROM.Thm54.VclL.Events.cK_eq.symm
  have hcell : ∀ x ∈ (claimCells c).map (claimNoun c), True := fun _ _ => trivial
  have hcl : (claimCells c).length ≤ 3 := (List.length_filter_le _ _).trans (by simp)
  have hcorner : cornerC.N = 2 ^ 31 ∧ cornerC.D = 2 ^ 31 ∧ cornerC.W = 2 ^ 31 ∧ cornerC.A = 2 ^ 31 ∧ cornerC.AW = 2 ^ 31 ∧
      cornerC.J = 2 ^ 31 ∧ cornerC.mb = 2 ^ 31 ∧ cornerC.calls = 2 ^ 31 ∧ cornerC.heads = 2 ^ 31 ∧ cornerC.blocks = 2 ^ 31 ∧
      cornerC.rd = 2 ^ 31 ∧ cornerC.maxlen = 2 ^ 31 ∧ cornerC.leaves = 2 * Nock.NockVMROM.Thm54.VclL.fuelChip := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  obtain ⟨cN, cD, cW, cA, cAW, cJ, cmb, ccalls, cheads, cblocks, crd, cmaxlen, cleaves⟩ := hcorner
  constructor
  · refine ⟨Nock.Jet.VerifiedRegistry.empty.faithful, hcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨le_rfl, le_rfl, le_rfl, rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
    · intro x hx
      rw [hrc] at hx
      show Nock.Atoms.lenL x ≤ cornerC.maxlen
      unfold Nock.Atoms.lenL
      rw [if_pos hx, cmaxlen]; norm_num
    · show 2 * Nock.NockVMROM.Thm54.VclL.fuelChip ≤ cornerC.leaves; rw [cleaves]
    · show hNof XI "atomChipHQL" + 2 ≤ cornerC.maxlen; rw [cmaxlen]; omega
    · exact le_rfl
    · show hNof XI "computeChipVCLHX" ≤ cornerC.N; rw [cN]; omega
    · show hNof XI "cellChipHQKW" ≤ cornerC.D; rw [cD]; omega
    · show hNof XI "walkChipJ8" ≤ cornerC.W; rw [cW]; omega
    · show hNof XI "atomChipHQL" ≤ cornerC.A; rw [cA]; omega
    · show (if (tabOf XI "walkChipHQK").isSome then hNof XI "walkChipHQK" else 1) ≤ cornerC.AW; rw [cAW]; omega
    · show hNof XI "cellChipHQKW" ≤ 2 ^ 31; omega
    · show (censusG (PbOfX XI hsh (posX_of_shape hsh) kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0))
        (layNil XI hJ)) c).length ≤ 2 ^ 31
      rw [census_eq, List.length_map]
      omega
    · exact hHt_PbOfX XI hsh (posX_of_shape hsh) kroots krootsV _ _ _ _ _ _ _ rfl rfl rfl
    · exact hcapH_PbOfX XI hsh _ rfl
  · have hgg := hg
    refine ⟨hgg.hinjX, hgg.hadjX, hgg.hinjC, hgg.hadjC, hgg.hnpC, hgg.hinjW, hgg.hadjW, ?_, ?_, ?_, ?_, hgg.hinjA, hgg.hadjA,
      hgg.hnpA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc.hclA, hc.hclR, ?_, ?_, ?_, hc.hcellF, ?_, ?_, ?_⟩
    · exact hk1
    · exact hkW
    · show kroots + hNof XI "walkChipJ8" < ringChar (ZMod P); rw [hrc]; omega
    · intro hne; exact absurd hJ hne
    · intro hne
      have hk0 : (tabOf XI "walkChipHQK").isSome = true := by
        by_contra hh; simp [PbOfX, hh] at hne
      have hh := hV hk0
      obtain ⟨hv1, hv2⟩ := hgg.hVgeom (by show (if (tabOf XI "walkChipHQK").isSome then krootsV else 0) ≠ 0; simp [hk0]; have := hh.1; omega)
      refine ⟨hv1, hv2, ?_, ?_, ?_⟩
      · show 1 ≤ (if (tabOf XI "walkChipHQK").isSome then krootsV else 0); simp [hk0]; exact hh.1
      · show (if (tabOf XI "walkChipHQK").isSome then krootsV else 0) ≤ (if (tabOf XI "walkChipHQK").isSome then hNof XI "walkChipHQK" else 1)
        simp [hk0]; exact hh.2
      · show (if (tabOf XI "walkChipHQK").isSome then krootsV else 0) + (if (tabOf XI "walkChipHQK").isSome then hNof XI "walkChipHQK" else 1) < ringChar (ZMod P)
        rw [hrc]; simp only [if_pos hk0]; have := hh.2; have := hNof_le XI hsh "walkChipHQK"; omega
    · show List.ofFn (layNil XI hJ) = layoutJ8 (fun _ => tplDummy) [] []
      apply List.eq_nil_of_length_eq_zero
      simp [hJ]
    · show ∀ q ∈ layoutJ8 (fun _ => tplDummy) [] [], _
      intro q hq; exact absurd hq (by simp [layoutJ8, Nock.Jet.ChipJ8.blocks])
    · show ((layoutJ8 (fun _ => tplDummy) [] []).filterMap Nock.Jet.ChipJ8.tvKey).Nodup
      simp [layoutJ8, Nock.Jet.ChipJ8.blocks]
    · intro i hi; exact absurd (show i ∈ ([] : List ℕ) from hi) (by simp)
    · show ([] : List ℕ).Nodup; exact List.nodup_nil
    · intro i hi; exact absurd (show i ∈ ([] : List ℕ) from hi) (by simp)
    · intro i hi; exact absurd (show i ∈ ([] : List ℕ) from hi) (by simp)
    · intro i hi; exact absurd (show i ∈ ([] : List ℕ) from hi) (by simp)
    · intro x hx
      rw [census_eq] at hx
      exact hc.hcen x hx
    · show 3 + 0 + 2 * hNof XI "cellChipHQKW" < P; omega
    · show hNof XI "atomChipHQL" + (if (tabOf XI "walkChipHQK").isSome then hNof XI "walkChipHQK" else 1) < P; omega
    · show hNof XI "atomChipHQL" ≤ 2 ^ 62
      have : (2 : ℕ) ^ 26 ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show 3 * hNof XI "computeChipVCLHX" + hNof XI "walkChipJ8" + jCount Nock.Jet.ChipJ8.entsX (layNil XI hJ) ≤ 3 * cornerC.N + cornerC.W + cornerC.rd
        rw [j2, cN, cW, crd]; omega
      · show hNof XI "cellChipHQKW" ≤ cornerC.D; rw [cD]; omega
      · show hNof XI "computeChipVCLHX" ≤ cornerC.N; rw [cN]; omega
      · show hNof XI "walkChipJ8" ≤ cornerC.W; rw [cW]; omega
      · show 2 * hNof XI "computeChipVCLHX" + 0 + (jCount Nock.Jet.ChipJ8.ents0T (layNil XI hJ) + jCount Nock.Jet.ChipJ8.ents1T (layNil XI hJ)) ≤ cornerC.N + 2 * cornerC.J + (2 ^ 31 + cornerC.N)
        rw [j3, j4, cN, cJ]; omega
      · show jCount Nock.Jet.ChipJ8.ents2T (layNil XI hJ) + jCount Nock.Jet.ChipJ8.ents3 (layNil XI hJ) + hNof XI "atomChipHQL" + 2 * (if (tabOf XI "walkChipHQK").isSome then hNof XI "walkChipHQK" else 1) ≤ cornerC.calls + cornerC.heads + cornerC.blocks + cornerC.J
        rw [j0, j1, ccalls, cheads, cblocks, cJ]; omega
    · refine ⟨?_, ?_, ?_, ?_⟩
      · show 0 ≤ 2 ^ 31; omega
      · show hNof XI "atomChipHQL" ≤ cornerC.mb; rw [cmb]; omega
      · show hNof XI "atomChipHQL" ≤ cornerC.A; rw [cA]; omega
      · show (if (tabOf XI "walkChipHQK").isSome then hNof XI "walkChipHQK" else 1) ≤ cornerC.AW; rw [cAW]; omega

/-! ## Non-vacuity -/

/-- the toy1 claim satisfies the claim side conditions -/
theorem claimOK_toy : ClaimOK NockvmE2E.J8.RVUJ8.toyClaim := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k v h; fin_cases k <;> simp [claimNoun, NockvmE2E.J8.RVUJ8.toyClaim, P, Nock.Field.p] at h ⊢ <;> omega
  · intro k h; fin_cases k <;> simp [claimNoun, isCellN, NockvmE2E.J8.RVUJ8.toyClaim, Nock.Noun.internal, P, Nock.Field.p] at h ⊢
  · intro x hx; simp [claimCells, claimNoun, isCellN, NockvmE2E.J8.RVUJ8.toyClaim] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    fin_cases a <;> simp at ha ⊢
    refine ⟨?_, ?_⟩
    · show 2 ≤ Nock.NockVMROM.Thm54.VclL.fuelChip
      unfold Nock.NockVMROM.Thm54.VclL.fuelChip; norm_num
    · intro v hv
      simp [Nock.Noun.leafList] at hv
      rcases hv with rfl | rfl <;> norm_num [P, Nock.Field.p]
  · rfl

open NockvmE2E.Exec.J8Shape (toyShape4 toyShape_ok)

/-- **non-vacuity**: `datX_ok` is instantiated at `toyShape4` (kernel-checked shape, jet-free), kroots `1`, the toy1 claim -/
theorem datX_ok_toy4 :
    DatumOK (DX toyShape4 toyShape_ok hNof_toy_jet 1 0 NockvmE2E.J8.RVUJ8.toyClaim).d ∧
      StmtP (DX toyShape4 toyShape_ok hNof_toy_jet 1 0 NockvmE2E.J8.RVUJ8.toyClaim).d :=
  datX_ok toyShape4 toyShape_ok hNof_toy_jet 1 0 le_rfl
    (by unfold hNof tabOf toyShape4; decide)
    (fun h => by revert h; unfold hNof tabOf toyShape4; decide)
    _ claimOK_toy

end

end NockvmE2E.J8.DatXOk

#print axioms NockvmE2E.J8.DatXOk.datX_ok
#print axioms NockvmE2E.J8.DatXOk.claimOK_toy
#print axioms NockvmE2E.J8.DatXOk.datX_ok_toy4
