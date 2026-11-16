/-
J9A-LINK: `ClaimOK9`, `DX9`, `datX9_ok`: `DatumOK9A ∧ StmtP9A` at the static datum `DX9` over any
jet-free J-9 A instance `XI` (empty registry, census-corner rows `cornerC9`, `g = 2^31`, `Pb = PbOfX9 XI …`, `ω = zv XI.hGen`).
Twin of `J8/DatXOk.lean`. Nothing here mentions `AcceptsJ9A`, a trace, or any chip evaluation.
-/
import NockvmE2E.J9A.PbOfX9
import NockvmE2E.J8.DatXOk

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J9A.DatX9Ok

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.PbOfX9
open NockvmE2E.J8.InstJ8 (P tabOf hNof ω0 tplDummy)
open NockvmE2E.J8.DatXOk (layNil jCount_zero)
open Nock.Jet.ChipJ8 (layoutJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (censusG claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (censusGJ9 claimBigs isBigN)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (cornerC9)

noncomputable section

/-- the claim side conditions of `StmtP9A` at `regs = []`: `hclR`, the census (cell claim nouns, then big-atom claim nouns; this is
`censusGJ9` at `regs = []`), and `hcellF` -/
structure ClaimOK9 (c : P8PublicClaim) (nA : ℕ) : Prop where
  hclR : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < P
  hcen : ∀ x ∈ (claimCells c).map (claimNoun c) ++ (claimBigs P c).map (claimNoun c),
    x.leaves ≤ Nock.NockVMROM.Thm54.VclL.fuelChip ∧ ∀ v ∈ x.leafList, Nock.Atoms.lenL v ≤ nA + 2
  hcellF : isCellN c.formula = true

/-- the static datum over `XI`: empty registry, claim `c`, corner rows `cornerC9`, `g = 2^31`, `hN = XI.hN`, `ω = zv XI.hGen` -/
def DX9 (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (hJ : hNof XI "jetChipJ8" = 0) (kroots krootsV : ℕ)
    (c : P8PublicClaim) : Datum9A :=
  ⟨PbOfX9 XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ),
    Nock.Jet.VerifiedRegistry.empty.R, c, cornerC9, 2 ^ 31, XI.hN, zv XI.hGen⟩

theorem census9_eq (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (hJ : hNof XI "jetChipJ8" = 0)
    (kroots krootsV : ℕ) (c : P8PublicClaim) :
    censusGJ9 (PbOfX9 XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ)).toPubJ8 c
      = (claimCells c).map (claimNoun c) ++ (claimBigs P c).map (claimNoun c) := rfl

theorem census9_eq' (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (hJ : hNof XI "jetChipJ8" = 0)
    (kroots krootsV : ℕ) (c : P8PublicClaim) :
    censusG (PbOfX9 XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ)).toPubJ8 c
      = (claimCells c).map (claimNoun c) := rfl

theorem DX9_d (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (hJ : hNof XI "jetChipJ8" = 0) (kroots krootsV : ℕ)
    (c : P8PublicClaim) :
    (DX9 XI h hJ kroots krootsV c) =
      ⟨PbOfX9 XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ),
        Nock.Jet.VerifiedRegistry.empty.R, c, cornerC9, 2 ^ 31, XI.hN, zv XI.hGen⟩ := rfl

theorem link9_DX9 (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (hJ : hNof XI "jetChipJ8" = 0) (kroots krootsV : ℕ)
    (c : P8PublicClaim) : Link9 XI (DX9 XI h hJ kroots krootsV c) :=
  link9_PbOfX9 XI h kroots krootsV _ _ _ _ _ _ _ rfl rfl rfl

theorem datX9_ok (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (hJ : hNof XI "jetChipJ8" = 0)
    (kroots krootsV : ℕ) (hk1 : 1 ≤ kroots) (hkW : kroots ≤ hNof XI "walkChipJ8")
    (hV : (tabOf XI "walkChipHQK").isSome = true → 1 ≤ krootsV ∧ krootsV ≤ hNof XI "walkChipHQK")
    (hV0 : (tabOf XI "walkChipHQK").isSome = false → krootsV = 0)
    (c : P8PublicClaim) (hc : ClaimOK9 c (hNof XI "atomChipHQL")) :
    DatumOK9A (DX9 XI h hJ kroots krootsV c) ∧ StmtP9A (DX9 XI h hJ kroots krootsV c) := by
  have hle := hN_le_9 h
  have hnA := hNof_le9 XI h "atomChipHQL"
  have hnC := hNof_le9 XI h "cellChipHQKW"
  have hn := hNof_le9 XI h "computeChipVCLHX9"
  have hnW := hNof_le9 XI h "walkChipJ8"
  have hV' := nOpt_le h "walkChipHQK"
  have hX' := nOpt_le h "axisChipJ9"
  have hS' := nOpt_le h "splitChipJ9"
  have hP : (2 : ℕ) * 2 ^ 26 + 4 < P := by norm_num [P, Nock.Field.p]
  have hrc : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n P
  have hg := geom_PbOfX9 XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ)
  have j0 := jCount_zero Nock.Jet.ChipJ8.ents2T (layNil XI hJ) hJ
  have j1 := jCount_zero Nock.Jet.ChipJ8.ents3 (layNil XI hJ) hJ
  have j2 := jCount_zero Nock.Jet.ChipJ8.entsX (layNil XI hJ) hJ
  have j3 := jCount_zero Nock.Jet.ChipJ8.ents0T (layNil XI hJ) hJ
  have j4 := jCount_zero Nock.Jet.ChipJ8.ents1T (layNil XI hJ) hJ
  have hcard : Fintype.card Nock.TraceGenExe.KC = Nock.NockVMROM.Thm54.VclL.Events.cK := by
    rw [Nock.TraceGenExe.KC_card]; exact Nock.NockVMROM.Thm54.VclL.Events.cK_eq.symm
  have hcl : (claimCells c).length ≤ 3 := (List.length_filter_le _ _).trans (by simp)
  have hcorner : cornerC9.N = 2 ^ 31 ∧ cornerC9.D = 2 ^ 31 ∧ cornerC9.W = 2 ^ 31 ∧ cornerC9.A = 2 ^ 31 ∧ cornerC9.AW = 2 ^ 31 ∧
      cornerC9.J = 2 ^ 31 ∧ cornerC9.mb = 2 ^ 31 ∧ cornerC9.calls = 2 ^ 31 ∧ cornerC9.heads = 2 ^ 31 ∧ cornerC9.blocks = 2 ^ 31 ∧
      cornerC9.rd = 2 ^ 31 ∧ cornerC9.maxlen = 2 ^ 31 ∧ cornerC9.leaves = 2 * Nock.NockVMROM.Thm54.VclL.fuelChip ∧
      cornerC9.AX = 2 ^ 31 ∧ cornerC9.SP = 2 ^ 31 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  obtain ⟨cN, cD, cW, cA, cAW, cJ, cmb, ccalls, cheads, cblocks, crd, cmaxlen, cleaves, cAX, cSP⟩ := hcorner
  rw [DX9_d]
  constructor
  · refine ⟨Nock.Jet.VerifiedRegistry.empty.faithful, hcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show RowsLe Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8.cornerC Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8.cornerC
      simp [RowsLe]
    · exact le_rfl
    · exact le_rfl
    · intro x hx
      rw [hrc] at hx
      show Nock.Atoms.lenL x ≤ cornerC9.maxlen
      unfold Nock.Atoms.lenL
      rw [if_pos hx, cmaxlen]; norm_num
    · show 2 * Nock.NockVMROM.Thm54.VclL.fuelChip ≤ cornerC9.leaves; rw [cleaves]
    · show hNof XI "atomChipHQL" + 2 ≤ cornerC9.maxlen; rw [cmaxlen]; omega
    · exact le_rfl
    · show hNof XI "computeChipVCLHX9" ≤ cornerC9.N; rw [cN]; omega
    · show hNof XI "cellChipHQKW" ≤ cornerC9.D; rw [cD]; omega
    · show hNof XI "walkChipJ8" ≤ cornerC9.W; rw [cW]; omega
    · show hNof XI "atomChipHQL" ≤ cornerC9.A; rw [cA]; omega
    · show nOpt XI "walkChipHQK" ≤ cornerC9.AW; rw [cAW]; omega
    · show hNof XI "cellChipHQKW" ≤ 2 ^ 31; omega
    · show (censusG (PbOfX9 XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0))
        (layNil XI hJ)).toPubJ8 c).length + 6 ≤ 2 ^ 31
      rw [census9_eq', List.length_map]
      omega
    · exact hHt_PbOfX9 XI h kroots krootsV _ _ _ _ _ _ _ rfl rfl rfl
    · exact hN_le_9 h
  · refine ⟨hg.hinjX, hg.hadjX, hg.hinjC, hg.hadjC, hg.hnpC, hg.hinjW, hg.hadjW, ?_, ?_, ?_, ?_, hg.hinjA, hg.hadjA,
      hg.hnpA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc.hclR, ?_, ?_, hg.hlenA, hc.hcellF, hg.hnAS, ?_, ?_, hg.hlenX⟩
    · exact hk1
    · exact hkW
    · show kroots + hNof XI "walkChipJ8" < ringChar (ZMod P); rw [hrc]; omega
    · intro hne; exact absurd hJ hne
    · intro hne
      have hk0 : (tabOf XI "walkChipHQK").isSome = true := by
        by_contra hh; simp [PbOfX9, hh] at hne
      have hh := hV hk0
      obtain ⟨hv1, hv2⟩ := hg.hVgeom hne
      refine ⟨hv1, hv2, ?_, ?_, ?_⟩
      · show 1 ≤ (if (tabOf XI "walkChipHQK").isSome then krootsV else 0); simp [hk0]; exact hh.1
      · show (if (tabOf XI "walkChipHQK").isSome then krootsV else 0) ≤ nOpt XI "walkChipHQK"
        unfold nOpt; simp [hk0]; exact hh.2
      · show (if (tabOf XI "walkChipHQK").isSome then krootsV else 0) + nOpt XI "walkChipHQK" < ringChar (ZMod P)
        rw [hrc]; unfold nOpt; simp only [if_pos hk0]; have := hh.2; have := hNof_le9 XI h "walkChipHQK"; omega
    · exact hg.hXgeom
    · exact hg.hSgeom
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
      have hx' : x ∈ censusGJ9 (PbOfX9 XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0))
        (layNil XI hJ)).toPubJ8 c := hx
      rw [census9_eq] at hx'
      exact hc.hcen x hx'
    · show 3 + 0 + 2 * hNof XI "cellChipHQKW" < P; omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show 3 * hNof XI "computeChipVCLHX9" + hNof XI "walkChipJ8" + Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.entsX (layNil XI hJ) ≤ 3 * cornerC9.N + cornerC9.W + cornerC9.rd
        rw [j2, cN, cW, crd]; omega
      · show hNof XI "cellChipHQKW" ≤ cornerC9.D; rw [cD]; omega
      · show hNof XI "computeChipVCLHX9" + nOpt XI "axisChipJ9" ≤ cornerC9.N; rw [cN]; omega
      · show hNof XI "walkChipJ8" ≤ cornerC9.W; rw [cW]; omega
      · show 2 * hNof XI "computeChipVCLHX9" + ([] : List ℕ).length +
          (Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents0T (layNil XI hJ) +
            Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents1T (layNil XI hJ)) + nOpt XI "axisChipJ9" ≤
          cornerC9.N + 2 * cornerC9.J + (2 ^ 31 + cornerC9.N) + cornerC9.AX
        rw [j3, j4, cN, cJ, cAX]; simp; omega
      · show Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents2T (layNil XI hJ) +
          Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents3 (layNil XI hJ) + hNof XI "atomChipHQL" +
          2 * nOpt XI "walkChipHQK" + nOpt XI "axisChipJ9" + 2 * nOpt XI "splitChipJ9" ≤
          cornerC9.calls + cornerC9.heads + cornerC9.blocks + cornerC9.J + cornerC9.AX + 2 * cornerC9.SP
        rw [j0, j1, ccalls, cheads, cblocks, cJ, cAX, cSP]; omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show ([] : List ℕ).length ≤ 2 ^ 31; simp
      · show hNof XI "atomChipHQL" ≤ cornerC9.mb; rw [cmb]; omega
      · show hNof XI "atomChipHQL" ≤ cornerC9.A; rw [cA]; omega
      · show nOpt XI "walkChipHQK" ≤ cornerC9.AW; rw [cAW]; omega
      · show nOpt XI "axisChipJ9" ≤ cornerC9.AX; rw [cAX]; omega
      · show nOpt XI "splitChipJ9" ≤ cornerC9.SP; rw [cSP]; omega

end

end NockvmE2E.J9A.DatX9Ok

#print axioms NockvmE2E.J9A.DatX9Ok.link9_DX9
#print axioms NockvmE2E.J9A.DatX9Ok.datX9_ok
