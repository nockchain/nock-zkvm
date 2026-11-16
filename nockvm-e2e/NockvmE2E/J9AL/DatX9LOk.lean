/-
`DX9L`, `datX9L_ok`: `DatumOK9AL ∧ StmtP9AL` at the static datum `DX9L` over any jet-free J-9 AL instance `XI`
(registry `(addPrims empty prims).R`, census-corner rows `cornerC9L`, `g = 2^31`, `Pb = PbOfX9L XI …`, `ω = zv XI.hGen`).  Twin of `J9A/DatX9Ok.lean`.
Inputs: the family gates `shapeOkF famJ9AL`, `pregOkF`, `PrimsLink`.  Not zero-knowledge.
-/
import NockvmE2E.J9AL.PbOfX9L
import NockvmE2E.J9AL.PregJ9AL
import NockvmE2E.J9AL.LagrJ9AL
import NockvmE2E.J9A.DatX9Ok
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.J9AL.DatX9LOk

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.PbOfX9
open NockvmE2E.J9A.DatX9Ok (ClaimOK9)
open Nock.NockVMROM.Thm54.VclL.Handle
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.PbOfX9L NockvmE2E.J9AL.PregJ9AL
open NockvmE2E.J9A.RunGate9L (PrimsLink primsOfPub primsRoundTrip)
open NockvmE2E.J8.InstJ8 (P tabOf hNof ω0 tplDummy)
open NockvmE2E.J8.DatXOk (layNil jCount_zero)
open Nock.Jet.ChipJ8 (layoutJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (censusG claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (censusGJ9 claimBigs isBigN)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (cornerC9L)
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP (addPrims addPrims_R_of_mem)
open Nock.Jet.Prim (PrimOp primC primSpec)

noncomputable section

/-! ## 1. the static datum -/

/-- the static datum over `XI`: registry of the primitives, claim `c`, corner rows `cornerC9L`, `g = 2^31`, `hN = XI.hN`, `ω = zv XI.hGen` -/
def DX9L (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (hJ : hNof XI "jetChipJ8" = 0) (kroots krootsV : ℕ)
    (c : P8PublicClaim) : Datum9AL :=
  ⟨PbOfX9L XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ),
    (addPrims Nock.Jet.VerifiedRegistry.empty (primsOf XI)).R, c, cornerC9L, 2 ^ 31, XI.hN, zv XI.hGen⟩

theorem DX9L_d (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (hJ : hNof XI "jetChipJ8" = 0) (kroots krootsV : ℕ)
    (c : P8PublicClaim) :
    DX9L XI h hJ kroots krootsV c =
      ⟨PbOfX9L XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ),
        (addPrims Nock.Jet.VerifiedRegistry.empty (primsOf XI)).R, c, cornerC9L, 2 ^ 31, XI.hN, zv XI.hGen⟩ := rfl

theorem link9L_DX9L (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (hJ : hNof XI "jetChipJ8" = 0) (kroots krootsV : ℕ)
    (c : P8PublicClaim) : Link9L XI (DX9L XI h hJ kroots krootsV c) :=
  link9L_PbOfX9L XI h kroots krootsV _ _ _ _ _ _ _ rfl rfl rfl

/-- the census nouns of a primitive are small (the leaf budget and the atom length bound at `nA + 2 ≥ 2`) -/
theorem primC_small (op : PrimOp) :
    (primC op).leaves ≤ Nock.NockVMROM.Thm54.VclL.fuelChip ∧ ∀ v ∈ (primC op).leafList, Nock.Atoms.lenL v ≤ 2 := by
  cases op <;> refine ⟨?_, ?_⟩ <;> decide +kernel

/-! ## 2. facts about the decoded primitive table -/

theorem primsOf_ids (XI : ExecInst) (hrt : primsRoundTrip XI.pubIn.prims = true) :
    (primsOf XI).map Prod.fst = XI.pubIn.prims.map PE.PrimRec.id := by
  obtain ⟨qs, hqs, hmap⟩ := roundtrip_data _ hrt
  rw [primsOf_eq XI qs hqs]
  simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) hmap

theorem primsOf_length (XI : ExecInst) (hrt : primsRoundTrip XI.pubIn.prims = true) :
    (primsOf XI).length = XI.pubIn.prims.length := by
  simpa using congrArg List.length (primsOf_ids XI hrt)

theorem primsOf_nil (XI : ExecInst) (h : XI.pubIn.prims = []) : primsOf XI = [] := by
  unfold primsOf; rw [h]; rfl

theorem idxPOf_lt (XI : ExecInst) (hb : ∀ q ∈ XI.pubIn.prims, q.idx < VF.PN) (id : ℕ) : idxPOf XI id < VF.PN := by
  unfold idxPOf
  cases hf : XI.pubIn.prims.find? (fun q => q.id == id) with
  | none => simp [VF.PN]
  | some q => simpa using hb q (List.mem_of_find?_eq_some hf)

theorem rkPOf_lt (XI : ExecInst) (hb : ∀ q ∈ XI.pubIn.prims, q.hi < VF.PN ∧ q.lo < VF.PN) (id : ℕ) :
    (rkPOf XI id).1 < VF.PN ∧ (rkPOf XI id).2 < VF.PN := by
  unfold rkPOf
  cases hf : XI.pubIn.prims.find? (fun q => q.id == id) with
  | none => simp [VF.PN]
  | some q => simpa using hb q (List.mem_of_find?_eq_some hf)

theorem rkPOf_ne (XI : ExecInst) (hb : ∀ q ∈ XI.pubIn.prims, ¬ (q.hi = 0 ∧ q.lo = 0)) (id : ℕ)
    (hid : id ∈ XI.pubIn.prims.map PE.PrimRec.id) : rkPOf XI id ≠ (0, 0) := by
  unfold rkPOf
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hid
  have hs : (XI.pubIn.prims.find? (fun q => q.id == q0.id)).isSome = true := by
    rw [List.find?_isSome]; exact ⟨q0, hq0, by simp⟩
  cases hf : XI.pubIn.prims.find? (fun q => q.id == q0.id) with
  | none => simp [hf] at hs
  | some q =>
    have := hb q (List.mem_of_find?_eq_some hf)
    simp only [Option.map_some, Option.getD_some, ne_eq, Prod.mk.injEq]
    exact this

theorem P_eq_PN : (P : ℕ) = VF.PN := by
  norm_num [P, Nock.Field.p, VF.PN]

/-! ## 3. `datX9L_ok` -/

theorem datX9L_ok (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (hJ : hNof XI "jetChipJ8" = 0)
    (kroots krootsV : ℕ) (hk1 : 1 ≤ kroots) (hkW : kroots ≤ hNof XI "walkChipJ8")
    (hV : (tabOf XI "walkChipHQK").isSome = true → 1 ≤ krootsV ∧ krootsV ≤ hNof XI "walkChipHQK")
    (hV0 : (tabOf XI "walkChipHQK").isSome = false → krootsV = 0)
    (c : P8PublicClaim) (hc : ClaimOK9 c (hNof XI "atomChipHQL"))
    (hpreg : NockvmE2E.J9A.RunGate9L.pregOkF XI = true) (hpl : PrimsLink XI) :
    DatumOK9AL (DX9L XI h hJ kroots krootsV c) ∧ StmtP9AL (DX9L XI h hJ kroots krootsV c) := by
  obtain ⟨hrt, hprb, hnd, hlenP, -, -, habs⟩ := hpl
  have hle := hN_leL h
  have hnA := hNof_leL XI h "atomChipHQL"
  have hnC := hNof_leL XI h "cellChipHQKW"
  have hn := hNof_leL XI h "computeChipVCLHX9"
  have hnW := hNof_leL XI h "walkChipJ8"
  have hV' := nOpt_leL h "walkChipHQK"
  have hX' := nOpt_leL h "axisChipJ9"
  have hS' := nOpt_leL h "splitChipJ9"
  have hL' := nOpt_leL h "aluChipJ9"
  have hP : (4 : ℕ) * 2 ^ 26 + 4 < P := by norm_num [P, Nock.Field.p]
  have hrc : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n P
  have hg := geom_PbOfX9L XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0)) (layNil XI hJ)
  have j0 := jCount_zero Nock.Jet.ChipJ8.ents2T (layNil XI hJ) hJ
  have j1 := jCount_zero Nock.Jet.ChipJ8.ents3 (layNil XI hJ) hJ
  have j2 := jCount_zero Nock.Jet.ChipJ8.entsX (layNil XI hJ) hJ
  have j3 := jCount_zero Nock.Jet.ChipJ8.ents0T (layNil XI hJ) hJ
  have j4 := jCount_zero Nock.Jet.ChipJ8.ents1T (layNil XI hJ) hJ
  have hcard : Fintype.card Nock.TraceGenExe.KC = Nock.NockVMROM.Thm54.VclL.Events.cK := by
    rw [Nock.TraceGenExe.KC_card]; exact Nock.NockVMROM.Thm54.VclL.Events.cK_eq.symm
  have hcl : (claimCells c).length ≤ 3 := (List.length_filter_le _ _).trans (by simp)
  have hcorner : cornerC9L.N = 2 ^ 31 ∧ cornerC9L.D = 2 ^ 31 ∧ cornerC9L.W = 2 ^ 31 ∧ cornerC9L.A = 2 ^ 31 ∧ cornerC9L.AW = 2 ^ 31 ∧
      cornerC9L.J = 2 ^ 31 ∧ cornerC9L.mb = 2 ^ 31 ∧ cornerC9L.calls = 2 ^ 31 ∧ cornerC9L.heads = 2 ^ 31 ∧ cornerC9L.blocks = 2 ^ 31 ∧
      cornerC9L.rd = 2 ^ 31 ∧ cornerC9L.maxlen = 2 ^ 31 ∧ cornerC9L.leaves = 2 * Nock.NockVMROM.Thm54.VclL.fuelChip ∧
      cornerC9L.AX = 2 ^ 31 ∧ cornerC9L.SP = 2 ^ 31 ∧ cornerC9L.AL = 2 ^ 31 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl
  obtain ⟨cN, cD, cW, cA, cAW, cJ, cmb, ccalls, cheads, cblocks, crd, cmaxlen, cleaves, cAX, cSP, cAL⟩ := hcorner
  -- the primitive table
  have hlenPo : (primsOf XI).length ≤ nOpt XI "aluChipJ9" := by
    rw [primsOf_length XI hrt]
    unfold nOpt
    by_cases hs : (tabOf XI "aluChipJ9").isSome = true
    · simp only [hs, ite_true]; exact hlenP
    · have hs' : (tabOf XI "aluChipJ9").isSome = false := by simpa using hs
      rw [(habs hs').1]; simp [hs]
  have hlenPo' : (primsOf XI).length ≤ 2 ^ 26 := by omega
  have hndPo : ((primsOf XI).map Prod.fst).Nodup := by rw [primsOf_ids XI hrt]; exact hnd
  have hmemP : ∀ q ∈ primsOf XI, q.1 ∈ XI.pubIn.prims.map PE.PrimRec.id := by
    intro q hq; rw [← primsOf_ids XI hrt]; exact List.mem_map_of_mem hq
  have hPN := P_eq_PN
  rw [DX9L_d]
  constructor
  · refine ⟨(addPrims Nock.Jet.VerifiedRegistry.empty (primsOf XI)).faithful, hcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show RowsLe Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8.cornerC Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8.cornerC
      simp [RowsLe]
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · intro x hx
      rw [hrc] at hx
      show Nock.Atoms.lenL x ≤ cornerC9L.maxlen
      unfold Nock.Atoms.lenL
      rw [if_pos hx]
      show 1 ≤ cornerC9L.maxlen
      rw [cmaxlen]; norm_num
    · show 2 * Nock.NockVMROM.Thm54.VclL.fuelChip ≤ cornerC9L.leaves; rw [cleaves]
    · show hNof XI "atomChipHQL" + 2 ≤ cornerC9L.maxlen; rw [cmaxlen]; omega
    · exact le_rfl
    · show hNof XI "computeChipVCLHX9" ≤ cornerC9L.N; rw [cN]; omega
    · show hNof XI "cellChipHQKW" ≤ cornerC9L.D; rw [cD]; omega
    · show hNof XI "walkChipJ8" ≤ cornerC9L.W; rw [cW]; omega
    · show hNof XI "atomChipHQL" ≤ cornerC9L.A; rw [cA]; omega
    · show nOpt XI "walkChipHQK" ≤ cornerC9L.AW; rw [cAW]; omega
    · show hNof XI "cellChipHQKW" ≤ 2 ^ 31; omega
    · show (censusG (PbOfX9L XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0))
        (layNil XI hJ)).toPubJ8 c ++ AcceptsJ9AL.censusP (PbOfX9L XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0)
          (fun _ => (0, 0)) (layNil XI hJ))).length + 6 ≤ 2 ^ 31
      rw [List.length_append]
      have e1 : (censusG (PbOfX9L XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0))
        (layNil XI hJ)).toPubJ8 c).length = (claimCells c).length := by
        show ((claimCells c).map (claimNoun c)).length = _
        rw [List.length_map]
      have e2 : (AcceptsJ9AL.censusP (PbOfX9L XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0)
          (fun _ => (0, 0)) (layNil XI hJ))).length = (primsOf XI).length := by
        show ((primsOf XI).map _).length = _
        rw [List.length_map]
      rw [e1, e2]
      omega
    · intro k
      show (preLOfX XI k).natDegree ≤ XI.hN
      unfold preLOfX
      by_cases hon : (tabOf XI "aluChipJ9").isSome = true
      · obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp hon
        have hmem : tab ∈ XI.tabs.toList := List.mem_of_find?_eq_some htab
        have hid : tab.chip.id = "aluChipJ9" := by
          have := List.find?_some htab; simpa using this
        have hcol : aluCol0 XI = tab.col0 := by unfold aluCol0; rw [htab]; rfl
        have hsz := preL_size_of_pregOkF XI hpreg tab hmem hid k
        have hth := hle_of_shapeF h tab hmem
        simp only [hon, ite_true]; rw [hcol]
        refine Polynomial.natDegree_le_of_degree_le (le_of_lt ?_)
        refine lt_of_lt_of_le (NockvmE2E.Exec.MaskOkK.degree_polyOfList _) ?_
        exact_mod_cast (by simpa [NockvmE2E.Exec.MaskOkK.polyOfArr] using hsz.trans hth)
      · simp [hon]
    · exact hHt_PbOfX9L XI h kroots krootsV _ _ _ _ _ _ _ rfl rfl rfl
    · exact hN_leL h
  · refine ⟨hg.geomA.hinjX, hg.geomA.hadjX, hg.geomA.hinjC, hg.geomA.hadjC, hg.geomA.hnpC, hg.geomA.hinjW, hg.geomA.hadjW, ?_, ?_, ?_, ?_,
      hg.geomA.hinjA, hg.geomA.hadjA, hg.geomA.hnpA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc.hclR, ?_, ?_, hg.geomA.hlenA,
      hc.hcellF, hg.geomA.hnAS, ?_, ?_, hg.geomA.hlenX, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hk1
    · exact hkW
    · show kroots + hNof XI "walkChipJ8" < ringChar (ZMod P); rw [hrc]; omega
    · intro hne; exact absurd hJ hne
    · intro hne
      have hk0 : (tabOf XI "walkChipHQK").isSome = true := by
        by_contra hh; simp [PbOfX9L, hh] at hne
      have hh := hV hk0
      obtain ⟨hv1, hv2⟩ := hg.geomA.hVgeom hne
      refine ⟨hv1, hv2, ?_, ?_, ?_⟩
      · show 1 ≤ (if (tabOf XI "walkChipHQK").isSome then krootsV else 0); simp [hk0]; exact hh.1
      · show (if (tabOf XI "walkChipHQK").isSome then krootsV else 0) ≤ nOpt XI "walkChipHQK"
        unfold nOpt; simp [hk0]; exact hh.2
      · show (if (tabOf XI "walkChipHQK").isSome then krootsV else 0) + nOpt XI "walkChipHQK" < ringChar (ZMod P)
        rw [hrc]; unfold nOpt; simp only [if_pos hk0]; have := hh.2; have := hNof_leL XI h "walkChipHQK"; omega
    · exact hg.geomA.hXgeom
    · exact hg.geomA.hSgeom
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
    · -- hcen'
      intro x hx
      have hx' : x ∈ censusGJ9 (PbOfX9L XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0) (fun _ => (0, 0))
        (layNil XI hJ)).toPubJ8 c ++ AcceptsJ9AL.censusP (PbOfX9L XI h kroots krootsV (fun _ => tplDummy) [] [] (fun _ => 0)
          (fun _ => (0, 0)) (layNil XI hJ)) := hx
      rcases List.mem_append.mp hx' with hx1 | hx2
      · have hx1' : x ∈ (claimCells c).map (claimNoun c) ++ (claimBigs P c).map (claimNoun c) := hx1
        exact hc.hcen x hx1'
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx2
        obtain ⟨hs1, hs2⟩ := primC_small q.2
        refine ⟨hs1, fun v hv => (hs2 v hv).trans ?_⟩
        show 2 ≤ hNof XI "atomChipHQL" + 2
        omega
    · show 3 + 0 + 2 * hNof XI "cellChipHQKW" < P; omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show 3 * hNof XI "computeChipVCLHX9" + hNof XI "walkChipJ8" +
          Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.entsX (layNil XI hJ) + nOpt XI "aluChipJ9" ≤
          3 * cornerC9L.N + cornerC9L.W + cornerC9L.rd + cornerC9L.AL
        rw [j2, cN, cW, crd, cAL]; omega
      · show hNof XI "cellChipHQKW" ≤ cornerC9L.D; rw [cD]; omega
      · show hNof XI "computeChipVCLHX9" + nOpt XI "axisChipJ9" ≤ cornerC9L.N; rw [cN]; omega
      · show hNof XI "walkChipJ8" ≤ cornerC9L.W; rw [cW]; omega
      · show 2 * hNof XI "computeChipVCLHX9" + ([] : List ℕ).length +
          (Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents0T (layNil XI hJ) +
            Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents1T (layNil XI hJ)) + nOpt XI "axisChipJ9" +
            2 * nOpt XI "aluChipJ9" ≤
          cornerC9L.N + 2 * cornerC9L.J + (2 ^ 31 + cornerC9L.N) + cornerC9L.AX + 2 * cornerC9L.AL
        rw [j3, j4, cN, cJ, cAX, cAL]; simp; omega
      · show Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents2T (layNil XI hJ) +
          Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents3 (layNil XI hJ) + hNof XI "atomChipHQL" +
          2 * nOpt XI "walkChipHQK" + nOpt XI "axisChipJ9" + 2 * nOpt XI "splitChipJ9" + 2 * nOpt XI "aluChipJ9" ≤
          cornerC9L.calls + cornerC9L.heads + cornerC9L.blocks + cornerC9L.J + cornerC9L.AX + 2 * cornerC9L.SP + 2 * cornerC9L.AL
        rw [j0, j1, ccalls, cheads, cblocks, cJ, cAX, cSP, cAL]; omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show ([] : List ℕ).length ≤ 2 ^ 31; simp
      · show hNof XI "atomChipHQL" ≤ cornerC9L.mb; rw [cmb]; omega
      · show hNof XI "atomChipHQL" ≤ cornerC9L.A; rw [cA]; omega
      · show nOpt XI "walkChipHQK" ≤ cornerC9L.AW; rw [cAW]; omega
      · show nOpt XI "axisChipJ9" ≤ cornerC9L.AX; rw [cAX]; omega
      · show nOpt XI "splitChipJ9" ≤ cornerC9L.SP; rw [cSP]; omega
    · -- hALst
      intro hon
      refine ⟨hg.hinjL, hg.hadjL, hg.hnpL, ?_⟩
      have hon' : (tabOf XI "aluChipJ9").isSome = true := hon
      obtain ⟨tab, htab⟩ := Option.isSome_iff_exists.mp hon'
      have hmem : tab ∈ XI.tabs.toList := List.mem_of_find?_eq_some htab
      have hid : tab.chip.id = "aluChipJ9" := by
        have := List.find?_some htab; simpa using this
      refine pregOK_of_pregOkF XI h hpreg hrt tab hmem hid _ ?_ ?_ _ ?_
      · show nOpt XI "aluChipJ9" = tab.hN
        unfold nOpt hNof; simp [hon', htab]; try rfl
      · intro i; rfl
      · intro k
        show preLOfX XI k = _
        unfold preLOfX aluCol0
        simp [hon', htab]; try rfl
    · -- hALabs
      intro hoff
      have hoff' : (tabOf XI "aluChipJ9").isSome = false := hoff
      exact primsOf_nil XI (habs hoff').1
    · -- hPrim
      intro q hq
      exact addPrims_R_of_mem Nock.Jet.VerifiedRegistry.empty (primsOf XI) hndPo q hq
    · intro q hq hm; exact absurd (show q.1 ∈ ([] : List ℕ) from hm) (by simp)
    · refine ⟨?_, ?_, ?_⟩
      · show nOpt XI "aluChipJ9" + hNof XI "computeChipVCLHX9" < P; omega
      · show nOpt XI "aluChipJ9" ≤ cornerC9L.AL; rw [cAL]; omega
      · intro q hq
        have hmi := idxPOf_lt XI (fun r hr => (hprb r hr).2.1) q.1
        refine ⟨?_, ?_⟩
        · obtain ⟨r, hr, e⟩ := List.mem_map.mp (hmemP q hq)
          exact lt_of_lt_of_eq (e ▸ (hprb r hr).1) hPN.symm
        · exact lt_of_lt_of_eq hmi hPN.symm
    · exact hndPo
    · intro q hq
      exact rkPOf_ne XI (fun r hr => (hprb r hr).2.2.2.2) q.1 (hmemP q hq)
    · intro q hq
      have h1 := rkPOf_lt XI (fun r hr => ⟨(hprb r hr).2.2.1, (hprb r hr).2.2.2.1⟩) q.1
      have h2 := idxPOf_lt XI (fun r hr => (hprb r hr).2.1) q.1
      have e := (hrc.trans hPN).symm
      exact ⟨lt_of_lt_of_eq h1.1 e, lt_of_lt_of_eq h1.2 e, lt_of_lt_of_eq h2 e⟩
    · show 3 + ([] : List ℕ).length + (primsOf XI).length + nOpt XI "aluChipJ9" + 2 * hNof XI "cellChipHQKW" < P
      simp only [List.length_nil]; omega

end

end NockvmE2E.J9AL.DatX9LOk

#print axioms NockvmE2E.J9AL.DatX9LOk.primC_small
#print axioms NockvmE2E.J9AL.DatX9LOk.link9L_DX9L
#print axioms NockvmE2E.J9AL.DatX9LOk.datX9L_ok
