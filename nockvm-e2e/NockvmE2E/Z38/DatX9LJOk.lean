/-
NockvmE2E/Z38/DatX9LJOk.lean

`datX9LJ_ok`: `DatumOK9AL ∧ StmtP9AL` at the static datum `DX9LJ` over any J-9 AL instance `XI` with a template-jet table over the catalogue `catJ`.
Twin of `J9AL/DatX9LOk.lean` (`datX9L_ok`); the jet sites are discharged from `JetLink XI` (J1..J9) instead of from `hNof jet = 0`.
Also `hpin_PbOfX9LJ` (the pins are the registry templates' tokens, for `InpLink9L`).  Not zero-knowledge.
-/
import NockvmE2E.J9AL.DatX9LOk
import NockvmE2E.Z38.IfaceJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.Z38.DatX9LJOk

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.PbOfX9
open NockvmE2E.J9A.DatX9Ok (ClaimOK9)
open Nock.NockVMROM.Thm54.VclL.Handle
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.PbOfX9L NockvmE2E.J9AL.PregJ9AL
open NockvmE2E.J9AL.DatX9LOk (primsOf_ids primsOf_length primsOf_nil idxPOf_lt rkPOf_lt rkPOf_ne P_eq_PN primC_small)
open NockvmE2E.J9A.RunGate9L (PrimsLink primsOfPub primsRoundTrip pregOkF)
open NockvmE2E.J8.InstJ8 (P tabOf hNof ω0 tplDummy)
open Nock.Jet.ChipJ8 (layoutJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (censusG claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (censusGJ9 claimBigs isBigN)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (cornerC9L PubJ9AL)
open Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistryP (addPrims addPrims_R_of_mem addPrims_R_of_not_mem)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (jCount)
open Nock.Jet.Prim (PrimOp primC primSpec)
open NockvmE2E.Z38.JetPre (layJ regsOfPub idxOfPub rkOfPub)
open NockvmE2E.Z38.IfaceJ (layOfX DX9LJ)
open NockvmE2E.Z38.RunGate9LJ (JetLink jLen jPinB jPinN jRegsCat jRegsNd jDisj jSmall jUniq jCalls)

noncomputable section

abbrev CNJ : Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry.CheckedReg NockvmE2E.Z38.CatJ.pG := NockvmE2E.Z38.CatJ.catJ.toCR

/-! ## 1. the datum's public part -/

/-- the datum's `Pb` over the layout `layOfX` -/
abbrev PbJ (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8")
    (kroots krootsV : ℕ) : PubJ9AL P :=
  PbOfX9L XI h kroots krootsV CNJ.Rt (regsOfPub XI.pubIn) XI.pubIn.calls (idxOfPub XI.pubIn) (rkOfPub XI.pubIn) (layOfX XI hlen)

theorem geom_PbJ (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8")
    (kroots krootsV : ℕ) : Geom9L (PbJ XI h hlen kroots krootsV) :=
  geom_PbOfX9L XI h kroots krootsV CNJ.Rt (regsOfPub XI.pubIn) XI.pubIn.calls (idxOfPub XI.pubIn) (rkOfPub XI.pubIn) (layOfX XI hlen)

theorem DX9LJ_d (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8")
    (kroots krootsV : ℕ) (c : P8PublicClaim) :
    DX9LJ XI h hlen kroots krootsV c =
      ⟨PbJ XI h hlen kroots krootsV, (addPrims CNJ.toVR (primsOf XI)).R, c, cornerC9L, 2 ^ 31, XI.hN, zv XI.hGen⟩ := rfl

theorem link9L_DX9LJ (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8")
    (kroots krootsV : ℕ) (c : P8PublicClaim) : Link9L XI (DX9LJ XI h hlen kroots krootsV c) :=
  link9L_PbOfX9L XI h kroots krootsV _ _ _ _ _ _ _ rfl rfl rfl

/-! ## 2. counting and lookups -/

theorem jCount_le (es : List (Nock.Jet.ChipJ8.Kd × List Nock.Jet.ChipJ8.KE)) {n : ℕ} (lay : Fin n → Nock.Jet.ChipJ8.PRow) :
    jCount es lay ≤ es.length * n := by
  unfold jCount
  have h := List.sum_le_length_nsmul ((List.finRange n).map fun i => (es.filter fun e => e.1 == (lay i).kd).length) es.length (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact List.length_filter_le _ _)
  simpa [mul_comm] using h

theorem layout_ofFn (XI : ExecInst) (hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8") :
    List.ofFn (layOfX XI hlen) = layJ XI.pubIn := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp [List.getElem_ofFn, layOfX]

theorem length_blocks_ge (R : ℕ → Nock.Jet.Autogen.Tpl) : ∀ (ids : List ℕ) (c : ℕ),
    ids.length ≤ (Nock.Jet.ChipJ8.blocks R c ids).length
  | [], _ => by simp [Nock.Jet.ChipJ8.blocks]
  | i :: is, c => by
    have := length_blocks_ge R is (c + 1)
    simp [Nock.Jet.ChipJ8.blocks, Nock.Jet.ChipJ8.blockPre]
    omega

theorem regs_length_le (XI : ExecInst) (hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8") :
    (regsOfPub XI.pubIn).length ≤ hNof XI "jetChipJ8" := by
  rw [← hlen]; unfold layJ layoutJ8; simp

theorem calls_length_le (XI : ExecInst) (hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8") :
    XI.pubIn.calls.length ≤ hNof XI "jetChipJ8" := by
  rw [← hlen]; unfold layJ layoutJ8
  have := length_blocks_ge NockvmE2E.Z38.CatJ.catJ.toCR.Rt XI.pubIn.calls 0
  simp; omega

theorem idxOfPub_lt (p : PE.PubIn) (hb : ∀ q ∈ p.pins, q.idx < VF.PN) (id : ℕ) : idxOfPub p id < VF.PN := by
  unfold idxOfPub
  cases hf : p.pins.find? (fun q => q.key == id) with
  | none => simp [VF.PN]
  | some q => simpa using hb q (List.mem_of_find?_eq_some hf)

theorem rkOfPub_lt (p : PE.PubIn) (hb : ∀ q ∈ p.pins, q.hi < VF.PN ∧ q.lo < VF.PN) (id : ℕ) :
    (rkOfPub p id).1 < VF.PN ∧ (rkOfPub p id).2 < VF.PN := by
  unfold rkOfPub
  cases hf : p.pins.find? (fun q => q.key == id) with
  | none => simp [VF.PN]
  | some q => simpa using hb q (List.mem_of_find?_eq_some hf)

theorem rkOfPub_ne (p : PE.PubIn) (hb : ∀ q ∈ p.pins, ¬ (q.hi = 0 ∧ q.lo = 0)) (id : ℕ)
    (hid : id ∈ regsOfPub p) : rkOfPub p id ≠ (0, 0) := by
  unfold rkOfPub
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hid
  have hs : (p.pins.find? (fun q => q.key == q0.key)).isSome = true := by
    rw [List.find?_isSome]; exact ⟨q0, hq0, by simp⟩
  cases hf : p.pins.find? (fun q => q.key == q0.key) with
  | none => simp [hf] at hs
  | some q =>
    have := hb q (List.mem_of_find?_eq_some hf)
    simp only [Option.map_some, Option.getD_some, ne_eq, Prod.mk.injEq]
    exact this

theorem find_key (ps : List PE.NounRec) (hnd : (ps.map PE.NounRec.key).Nodup) :
    ∀ r ∈ ps, ps.find? (fun q => q.key == r.key) = some r := by
  induction ps with
  | nil => intro r hr; simp at hr
  | cons a l ih =>
    intro r hr
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hr with rfl | hr'
    · simp [List.find?_cons]
    · have hne : a.key ≠ r.key := fun e => hnd.1 (e ▸ List.mem_map_of_mem hr')
      simp [List.find?_cons, hne, ih hnd.2 r hr']

/-- the pins of the public input are the registry templates' tokens at the pin indices and ranks (`InpLink9.hpin` at `DX9LJ`) -/
theorem hpin_PbOfX9LJ (XI : ExecInst) (hN : jRegsNd XI) (hP : jPinN XI) :
    XI.pubIn.pins = (regsOfPub XI.pubIn).map (fun id => (⟨id, NockvmE2E.J8.RVUJ8.toks (Nock.Jet.Autogen.compile P (CNJ.Rt id)),
      idxOfPub XI.pubIn id, (rkOfPub XI.pubIn id).1, (rkOfPub XI.pubIn id).2⟩ : PE.NounRec)) := by
  have hnd : (XI.pubIn.pins.map PE.NounRec.key).Nodup := hN
  unfold regsOfPub
  conv_lhs => rw [← List.map_id XI.pubIn.pins]
  simp only [List.map_map]
  refine List.map_congr_left (fun r hr => ?_)
  have hf := find_key _ hnd r hr
  have hn := hP r hr
  simp only [Function.comp, id, idxOfPub, rkOfPub, hf, Option.map_some, Option.getD_some]
  rw [← hn]

/-- the registry's template entries at the public ids -/
theorem hTpl_catJ (XI : ExecInst) (hrt : primsRoundTrip XI.pubIn.prims = true) (hC : jRegsCat XI) (hD : jDisj XI)
    (i : ℕ) (hi : i ∈ regsOfPub XI.pubIn) :
    (addPrims CNJ.toVR (primsOf XI)).R i = some ⟨(CNJ.Rt i).toTemplate P, Nock.Jet.Autogen.compile P (CNJ.Rt i)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (CNJ.Rt i) = true ∧ (CNJ.Rt i).WellTyped P := by
  have hni : i ∉ (primsOf XI).map Prod.fst := by
    rw [primsOf_ids XI hrt]
    intro hm
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact hD q hq hi
  have hc := hC i hi
  refine ⟨?_, CNJ.axPos i hc, CNJ.wt i hc⟩
  rw [addPrims_R_of_not_mem _ _ i hni]
  simp only [NockvmE2E.Z38.CatJ.CN, Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry.CheckedReg.toVR,
    Nock.Jet.VerifiedRegistry.ofCompiled]
  rw [if_pos hc]

/-- the catalogue template's compiled noun is small (the leaf budget and the atom length bound at `nA + 2 ≥ 2`); a kernel computation on the
fixed catalogue constant `TN` (not on an instance) -/
theorem compileTN_small :
    (Nock.Jet.Autogen.compile P NockvmE2E.Z38.CatJ.TN).leaves ≤ Nock.NockVMROM.Thm54.VclL.fuelChip ∧
      ∀ v ∈ (Nock.Jet.Autogen.compile P NockvmE2E.Z38.CatJ.TN).leafList, Nock.Atoms.lenL v ≤ 2 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-! ## 3. `datX9LJ_ok` -/

theorem datX9LJ_ok (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8")
    (kroots krootsV : ℕ) (hk1 : 1 ≤ kroots) (hkW : kroots ≤ hNof XI "walkChipJ8")
    (hV : (tabOf XI "walkChipHQK").isSome = true → 1 ≤ krootsV ∧ krootsV ≤ hNof XI "walkChipHQK")
    (hV0 : (tabOf XI "walkChipHQK").isSome = false → krootsV = 0)
    (c : P8PublicClaim) (hc : ClaimOK9 c (hNof XI "atomChipHQL"))
    (hpreg : pregOkF XI = true) (hpl : PrimsLink XI) (hJ : JetLink XI) :
    DatumOK9AL (DX9LJ XI h hlen kroots krootsV c) ∧ StmtP9AL (DX9LJ XI h hlen kroots krootsV c) := by
  obtain ⟨hrt, hprb, hnd, hlenP, -, -, habs⟩ := hpl
  obtain ⟨-, jPB, jPN, jRC, jRN, jD, jS, jU, jCl⟩ := hJ
  have hnJ := hNof_leL XI h "jetChipJ8"
  have hrl := regs_length_le XI hlen
  have hcl' := calls_length_le XI hlen
  have hle := hN_leL h
  have hnA := hNof_leL XI h "atomChipHQL"
  have hnC := hNof_leL XI h "cellChipHQKW"
  have hn := hNof_leL XI h "computeChipVCLHX9"
  have hnW := hNof_leL XI h "walkChipJ8"
  have hV' := nOpt_leL h "walkChipHQK"
  have hX' := nOpt_leL h "axisChipJ9"
  have hS' := nOpt_leL h "splitChipJ9"
  have hL' := nOpt_leL h "aluChipJ9"
  have hP : (8 : ℕ) * 2 ^ 26 + 4 < P := by norm_num [P, Nock.Field.p]
  have hrc : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n P
  have hg := geom_PbJ XI h hlen kroots krootsV
  have j0 := jCount_le Nock.Jet.ChipJ8.ents2T (layOfX XI hlen)
  have l0 : Nock.Jet.ChipJ8.ents2T.length = 11 := by first | rfl | decide | simp [Nock.Jet.ChipJ8.ents2T, Nock.Jet.ChipJ8.entsT, Nock.Jet.ChipJ8.ents0, Nock.Jet.ChipJ8.ents1, Nock.Jet.ChipJ8.ents2]
  rw [l0] at j0
  have j1 := jCount_le Nock.Jet.ChipJ8.ents3 (layOfX XI hlen)
  have l1 : Nock.Jet.ChipJ8.ents3.length = 1 := by first | rfl | decide | simp [Nock.Jet.ChipJ8.ents3, Nock.Jet.ChipJ8.entsT, Nock.Jet.ChipJ8.ents0, Nock.Jet.ChipJ8.ents1, Nock.Jet.ChipJ8.ents2]
  rw [l1] at j1
  have j2 := jCount_le Nock.Jet.ChipJ8.entsX (layOfX XI hlen)
  have l2 : Nock.Jet.ChipJ8.entsX.length = 3 := by first | rfl | decide | simp [Nock.Jet.ChipJ8.entsX, Nock.Jet.ChipJ8.entsT, Nock.Jet.ChipJ8.ents0, Nock.Jet.ChipJ8.ents1, Nock.Jet.ChipJ8.ents2]
  rw [l2] at j2
  have j3 := jCount_le Nock.Jet.ChipJ8.ents0T (layOfX XI hlen)
  have l3 : Nock.Jet.ChipJ8.ents0T.length = 9 := by first | rfl | decide | simp [Nock.Jet.ChipJ8.ents0T, Nock.Jet.ChipJ8.entsT, Nock.Jet.ChipJ8.ents0, Nock.Jet.ChipJ8.ents1, Nock.Jet.ChipJ8.ents2]
  rw [l3] at j3
  have j4 := jCount_le Nock.Jet.ChipJ8.ents1T (layOfX XI hlen)
  have l4 : Nock.Jet.ChipJ8.ents1T.length = 4 := by first | rfl | decide | simp [Nock.Jet.ChipJ8.ents1T, Nock.Jet.ChipJ8.entsT, Nock.Jet.ChipJ8.ents0, Nock.Jet.ChipJ8.ents1, Nock.Jet.ChipJ8.ents2]
  rw [l4] at j4
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
  rw [DX9LJ_d]
  constructor
  · refine ⟨(addPrims CNJ.toVR (primsOf XI)).faithful, hcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
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
    · show (censusG (PbJ XI h hlen kroots krootsV).toPubJ8 c ++ AcceptsJ9AL.censusP (PbJ XI h hlen kroots krootsV)).length + 6 ≤ 2 ^ 31
      rw [List.length_append]
      have e1 : (censusG (PbJ XI h hlen kroots krootsV).toPubJ8 c).length =
          (regsOfPub XI.pubIn).length + (claimCells c).length := by
        show ((regsOfPub XI.pubIn).map (fun id => Nock.Jet.Autogen.compile P (CNJ.Rt id)) ++ (claimCells c).map (claimNoun c)).length = _
        rw [List.length_append, List.length_map, List.length_map]
      have e2 : (AcceptsJ9AL.censusP (PbJ XI h hlen kroots krootsV)).length = (primsOf XI).length := by
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
    · exact hg.geomA.hJgeom
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
    · exact layout_ofFn XI hlen
    · exact jS
    · exact jU
    · intro i hi; exact hTpl_catJ XI hrt jRC jD i hi
    · exact jRN
    · intro i hi
      show idxOfPub XI.pubIn i < P
      exact lt_of_lt_of_eq (idxOfPub_lt XI.pubIn (fun q hq => (jPB q hq).2.1) i) hPN.symm
    · intro i hi
      exact rkOfPub_ne XI.pubIn (fun q hq => (jPB q hq).2.2.2.2) i hi
    · intro i hi
      have h1 := rkOfPub_lt XI.pubIn (fun q hq => ⟨(jPB q hq).2.2.1, (jPB q hq).2.2.2.1⟩) i
      have h2 := idxOfPub_lt XI.pubIn (fun q hq => (jPB q hq).2.1) i
      have e := (hrc.trans hPN).symm
      exact ⟨lt_of_lt_of_eq h1.1 e, lt_of_lt_of_eq h1.2 e, lt_of_lt_of_eq h2 e⟩
    · -- hcen'
      intro x hx
      have hx' : x ∈ censusGJ9 (PbJ XI h hlen kroots krootsV).toPubJ8 c ++ AcceptsJ9AL.censusP (PbJ XI h hlen kroots krootsV) := hx
      rcases List.mem_append.mp hx' with hx1 | hx2
      · have hx1' : x ∈ ((regsOfPub XI.pubIn).map (fun id => Nock.Jet.Autogen.compile P (CNJ.Rt id)) ++
            (claimCells c).map (claimNoun c)) ++ (claimBigs P c).map (claimNoun c) := hx1
        rcases List.mem_append.mp hx1' with hx3 | hx4
        · rcases List.mem_append.mp hx3 with hx5 | hx6
          · obtain ⟨id, -, rfl⟩ := List.mem_map.mp hx5
            obtain ⟨hs1, hs2⟩ := compileTN_small
            refine ⟨hs1, fun v hv => (hs2 v hv).trans ?_⟩
            show 2 ≤ hNof XI "atomChipHQL" + 2
            omega
          · exact hc.hcen x (List.mem_append.mpr (Or.inl hx6))
        · exact hc.hcen x (List.mem_append.mpr (Or.inr hx4))
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx2
        obtain ⟨hs1, hs2⟩ := primC_small q.2
        refine ⟨hs1, fun v hv => (hs2 v hv).trans ?_⟩
        show 2 ≤ hNof XI "atomChipHQL" + 2
        omega
    · show 3 + (regsOfPub XI.pubIn).length + 2 * hNof XI "cellChipHQKW" < P; omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show 3 * hNof XI "computeChipVCLHX9" + hNof XI "walkChipJ8" +
          Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.entsX (layOfX XI hlen) + nOpt XI "aluChipJ9" ≤
          3 * cornerC9L.N + cornerC9L.W + cornerC9L.rd + cornerC9L.AL
        rw [cN, cW, crd, cAL]; omega
      · show hNof XI "cellChipHQKW" ≤ cornerC9L.D; rw [cD]; omega
      · show hNof XI "computeChipVCLHX9" + nOpt XI "axisChipJ9" ≤ cornerC9L.N; rw [cN]; omega
      · show hNof XI "walkChipJ8" ≤ cornerC9L.W; rw [cW]; omega
      · show 2 * hNof XI "computeChipVCLHX9" + (regsOfPub XI.pubIn).length +
          (Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents0T (layOfX XI hlen) +
            Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents1T (layOfX XI hlen)) + nOpt XI "axisChipJ9" +
            2 * nOpt XI "aluChipJ9" ≤
          cornerC9L.N + 2 * cornerC9L.J + (2 ^ 31 + cornerC9L.N) + cornerC9L.AX + 2 * cornerC9L.AL
        rw [cN, cJ, cAX, cAL]; omega
      · show Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents2T (layOfX XI hlen) +
          Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount Nock.Jet.ChipJ8.ents3 (layOfX XI hlen) + hNof XI "atomChipHQL" +
          2 * nOpt XI "walkChipHQK" + nOpt XI "axisChipJ9" + 2 * nOpt XI "splitChipJ9" + 2 * nOpt XI "aluChipJ9" ≤
          cornerC9L.calls + cornerC9L.heads + cornerC9L.blocks + cornerC9L.J + cornerC9L.AX + 2 * cornerC9L.SP + 2 * cornerC9L.AL
        rw [ccalls, cheads, cblocks, cJ, cAX, cSP, cAL]; omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (regsOfPub XI.pubIn).length ≤ 2 ^ 31; omega
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
      exact addPrims_R_of_mem CNJ.toVR (primsOf XI) hndPo q hq
    · intro q hq hm
      obtain ⟨r, hr, e⟩ := List.mem_map.mp (hmemP q hq)
      exact jD r hr (e ▸ hm)
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
    · show 3 + (regsOfPub XI.pubIn).length + (primsOf XI).length + nOpt XI "aluChipJ9" + 2 * hNof XI "cellChipHQKW" < P
      omega

end

end NockvmE2E.Z38.DatX9LJOk

#print axioms NockvmE2E.Z38.DatX9LJOk.compileTN_small
#print axioms NockvmE2E.Z38.DatX9LJOk.hpin_PbOfX9LJ
#print axioms NockvmE2E.Z38.DatX9LJOk.hTpl_catJ
#print axioms NockvmE2E.Z38.DatX9LJOk.jCount_le
#print axioms NockvmE2E.Z38.DatX9LJOk.link9L_DX9LJ
#print axioms NockvmE2E.Z38.DatX9LJOk.datX9LJ_ok
