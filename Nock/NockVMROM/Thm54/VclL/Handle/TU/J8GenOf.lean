/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/J8GenOf.lean

 **J-8 completeness over any admissible `J8Data`, continued**: the honest record over `j8DataGen` (`BOfG`, `BRunG`) and the obligation groups of `ComplJ8Of`, the atom-table
 and atom-walk obligations of `ComplJ8OfAtom`.
 Every declaration is the corresponding statement and proof over `j8DataGen … O` (suffix `G`), except where the
 free list orders need a membership or permutation step.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.J8GenData
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
import Nock.NockVMROM.Thm54.VclL.Handle.TU.J8GenOrb

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.V1J8.Gen (cellsOfRoots addCells rootsOf idxOf idxD combOf spineOf padN linkOrder addNew lastIdxOf
  sxOf incChain AInfo atomV hdN' tlN' idxN pathReads walkGen mvCounts mxCounts mvPins wCounts bump callsOf
  WRow budget)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (CRow PRow layoutJ8 keysOf entsX)
open Nock.Jet.RapJetJ8 (consKT provKT tlF)

noncomputable section

/-! ### Twins of `ComplJ8Of` -/

section ComplJ8OfG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8)
noncomputable section
section Obl
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "DD" => j8DataGen p Rg Rt hgen O
/-- The honest record of the run. -/
abbrev BOfG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 DD)) (hC : 0 < (DD).cells.length) (hA : 0 < (DD).acs.length) (AV : AVPart p K)
    (fams : List (List (BadSpec K))) : HonestJ8 p K δ Rg fuel s f r :=
  honestJ8OfO δ b DD o hC hA AV fams

variable (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hC : 0 < (j8DataGen p Rg Rt hgen O).cells.length)
  (hA : 0 < (j8DataGen p Rg Rt hgen O).acs.length) (AV : AVPart p K) (fams : List (List (BadSpec K)))
theorem nodes_okG : Function.Injective (BOfG δ b Rt hgen O o hC hA AV fams).Pb.nodes ∧
    ∀ (i : Fin (BOfG δ b Rt hgen O o hC hA AV fams).Pb.n) (hi : (i : ℕ) + 1 < (BOfG δ b Rt hgen O o hC hA AV fams).Pb.n),
      (BOfG δ b Rt hgen O o hC hA AV fams).Pb.nodes ⟨(i : ℕ) + 1, hi⟩ =
        (BOfG δ b Rt hgen O o hC hA AV fams).Pb.nodes i * (BOfG δ b Rt hgen O o hC hA AV fams).Pb.orbit.ω :=
  powN_ok (o) (le_two_pow_ht _ List.mem_cons_self)

theorem htrC_runG (χ : Coins frameJ8 K) :
    let B := BOfG δ b Rt hgen O o hC hA AV fams
    qX δ b B.Pb (B.tr χ) (chalVJ8 b χ) (pubJ δ b B χ) =
    VclL.HonestTraceX.polyX b δ B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ)
      (VclL.HonestTraceX.lnW (αJ b χ)) (VclL.HonestTraceX.cntW B.W (αJ b χ))
      (VclL.HonestTraceX.accW (F := ZMod p) B.H B.W (αJ b χ) (γJ b χ)) B.Pb.nodes
      (computeChipVCLHX B.Pb.hn B.Pb.nodes b δ (chalVJ8 b χ) (pubJ δ b B χ) B.Pb.orbit).rap.w := rfl

/-- **The compute group of the obligations** (`HdlOK`, `hpair`, `goodC`) at the run, given the bad list
contains the compute pole family `compPoles`. -/
theorem compute_groupG (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hcl : ∀ k : Fin 3, ∀ v, FrameVS.claimNoun (cJ s f r) k = .atom v → v < p)
    (hcomp : ComplJ8CompPole.compPoles (K := K) δ (DD).H (DD).pd (bfsForest [(DD).t])
      (bfsForest [(DD).t]).length ∈ fams) :
    let B := BOfG δ b Rt hgen O o hC hA AV fams
    HonestCompX.HdlOK (ringChar (ZMod p)) B.H ∧
    (∀ u, InTree B.t u → HonestCompX.isPair B.H (rowOfSkelX u.label) →
      HonestCompX.PairOK (F := ZMod p) (B.pd (rowOfSkelX u.label))) ∧
    B.Pb.n = B.W.length ∧
    (∀ χ, limbVal b (pubJ δ b B χ) ChipH.pubIC = αJ b χ) ∧
    (∀ χ, limbVal b (pubJ δ b B χ) ChipH.pubSeed =
      VclL.HonestTraceX.curW (F := ZMod p) B.H B.W (γJ b χ) 1 * αJ b χ) ∧
    (∀ χ, limbVal b (pubJ δ b B χ) ChipH.pubOut = 0) ∧
    (∀ χ, pubJ δ b B χ 0 = HonestCompX.hk B.H s ∧ pubJ δ b B χ 1 = HonestCompX.hv B.H s ∧
      pubJ δ b B χ 2 = HonestCompX.hk B.H f ∧ pubJ δ b B χ 3 = HonestCompX.hv B.H f ∧
      pubJ δ b B χ 4 = HonestCompX.hk B.H r ∧ pubJ δ b B χ 5 = HonestCompX.hv B.H r) ∧
    (∀ χ, ∀ a < 6, ∀ k : Fin 3, pubJ δ b B χ (VclL.HonestTraceX.pubOfA a + k) =
      coord b (VclL.HonestTraceX.accV b δ B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) a B.Pb.n) k) ∧
    (∀ χ, B.Good χ → B.W.length ≤ orderOf (αJ b χ) ∧
      ∀ j < B.Pb.n, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
        HonestSlotX.dVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) ≠ 0 ∨
          HonestSlotX.aVal b δ S (VclL.HonestTraceX.env0 B.H B.pd B.W (chalVJ8 b χ) (pubJ δ b B χ) j) = 0) := by
  intro B
  have hH := hH_runG Rt hgen O (p := p)
  refine ⟨hH, ?_, rfl, fun χ => ComplJ8Comp.hpIC δ b _ _ _ _ χ, fun χ => hpS_runG δ b Rt hgen O hcl χ,
    fun χ => ComplJ8Comp.hpO δ b _ _ _ _ χ, fun χ => hpub_runG δ b Rt hgen O hcl χ,
    fun χ => hρ_runG δ b Rt hgen O χ, ?_⟩
  · exact ComplJ8Atom.hpair_of_binders hgen hH hp63 _ hax hop5
  · refine ComplJ8Bad.goodC_of_cover δ b B _ rfl (List.mem_append_left _ (List.mem_singleton_self _)) ?_
    refine ComplJ8CompPole.denCovered_of_sub δ b B _ (fun e he => ?_) (bfs_pos _)
    exact List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hcomp, he⟩)

/-- **The staging obligation** (`StJ8`): compute, cell and J-8 walk (the seed `z′ = (χ₂, χ₃)` is a
round-0 coin), J, the atom table and atom walk (the parts' own staging). -/
theorem staged_runG
    (hAst : StagedCols frameJ8 TraceJ8.crA (fun χ => AV.trA χ))
    (hVst : StagedCols frameJ8 TraceJ8.crW (fun χ => AV.trV χ)) :
    StJ8 (BOfG δ b Rt hgen O o hC hA AV fams).tr := by
  have hz : ∀ χ χ' : Coins frameJ8 K, (∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → χ i = χ' i) →
      encR δ χ = encR δ χ' := fun χ χ' h =>
    encR_congr δ χ χ' (h WeightsJ8.c2 (by decide)) (h WeightsJ8.c3 (by decide)) (h FrameJ8.cY1 (by decide))
      (h FrameJ8.cY2 (by decide))
  exact ⟨ComplJ8Comp.staged_trCOf δ b _ _ _,
    ComplJ8Enc.cellTrME_staged δ b hC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz,
    ComplJ8Enc.walkTrWE_staged δ b _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz,
    ComplJ8Jet.stJ δ b _ _ _ (fun χ => rfl), hAst, hVst⟩

theorem rowsLe31_ofG (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) :
    RowsLe31 (BOfG δ b Rt hgen O o hC hA AV fams).Pb := by
  refine ⟨h31 _ ?_, h31 _ ?_, h31 _ ?_, h31 _ ?_, h31 _ ?_, h31 _ ?_⟩ <;> simp [sizesJ8, BOfG, honestJ8OfO, PbOfO]

theorem size_lt_pG (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) {x : ℕ}
    (hx : x ∈ sizesJ8 (j8DataGen p Rg Rt hgen O)) : x < p := by
  have := h31 x hx; have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
  omega

/-- **The node obligations of the cell table, the J-8 walk and the atom table.** -/
theorem nodes_groupG (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) :
    let B := BOfG δ b Rt hgen O o hC hA AV fams
    (Function.Injective B.Pb.nodesC ∧
      (∀ (i : Fin B.Pb.nC) (hi : (i : ℕ) + 1 < B.Pb.nC),
        B.Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesC i * B.Pb.orbitC.ω) ∧ B.Pb.nC < ringChar (ZMod p)) ∧
    (Function.Injective B.Pb.nodesW ∧
      (∀ (i : Fin B.Pb.nW) (hi : (i : ℕ) + 1 < B.Pb.nW),
        B.Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesW i * B.Pb.orbitW.ω) ∧
      1 ≤ B.Pb.kroots ∧ B.Pb.kroots ≤ B.Pb.nW ∧ B.Pb.kroots + B.Pb.nW < ringChar (ZMod p)) ∧
    (Function.Injective B.Pb.nodesA ∧
      (∀ (i : Fin B.Pb.nA) (hi : (i : ℕ) + 1 < B.Pb.nA),
        B.Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = B.Pb.nodesA i * B.Pb.orbitA.ω) ∧ B.Pb.nA < p) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hmC : (j8DataGen p Rg Rt hgen O).cells.length ∈ sizesJ8 (j8DataGen p Rg Rt hgen O) := by simp [sizesJ8]
  have hmW : (walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads).length ∈
      sizesJ8 (j8DataGen p Rg Rt hgen O) := by simp [sizesJ8]
  have hmA : (j8DataGen p Rg Rt hgen O).acs.length ∈ sizesJ8 (j8DataGen p Rg Rt hgen O) := by simp [sizesJ8]
  obtain ⟨c1, c2⟩ := powN_ok (o) (le_two_pow_ht _ hmC)
  obtain ⟨w1, w2⟩ := powN_ok (o) (le_two_pow_ht _ hmW)
  obtain ⟨a1, a2⟩ := powN_ok (o) (le_two_pow_ht _ hmA)
  have hWb := h31 _ hmW
  have hk := krW_le_rows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads
  have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
  refine ⟨⟨c1, c2, ?_⟩, ⟨w1, w2, one_le_krW _ _, hk, ?_⟩, ⟨a1, a2, size_lt_pG Rt hgen O hp63 h31 hmA⟩⟩
  · rw [hrc]; exact size_lt_pG Rt hgen O hp63 h31 hmC
  · rw [hrc]; show krW _ _ + (walkRows _ _).length < p; omega

theorem regs_leG (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) : (j8DataGen p Rg Rt hgen O).regs.length ≤ 2 ^ 31 := by
  have h1 : (j8DataGen p Rg Rt hgen O).regs.length ≤ (j8DataGen p Rg Rt hgen O).calls.length := by
    show (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).dedup.length ≤ _
    exact (List.dedup_sublist _).length_le.trans (by simp; rfl)
  have h2 : (j8DataGen p Rg Rt hgen O).calls.length ≤ (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length := by
    show (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t)).length ≤ _
    unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
    exact (List.length_filterMap_le _ _).trans (by simp; rfl)
  exact h1.trans (h2.trans (h31 _ List.mem_cons_self))

/-- **The budget obligation.** -/
theorem budget_runG (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) :
    let B := BOfG δ b Rt hgen O o hC hA AV fams
    3 + B.Pb.regs.length + 2 * B.Pb.nC < p ∧ B.Pb.nA + B.Pb.nV < p ∧ B.Pb.nA ≤ 2 ^ 62 ∧
    RealIOJ8.BudJ8 B.Pb B.rows (B.g + B.rows.N) ∧
    (B.Pb.regs.length ≤ B.g ∧ B.Pb.nA ≤ B.rows.mb ∧ B.Pb.nA ≤ B.rows.A ∧ B.Pb.nV ≤ B.rows.AW) := by
  intro B
  obtain ⟨l1, l2, l3⟩ := ComplJ8Comp.budget_lengths hp63 B.Pb (rowsLe31_ofG δ b Rt hgen O o hC hA AV fams h31)
    (regs_leG Rt hgen O h31)
  obtain ⟨b1, b2, b3, b4, b5⟩ := ComplJ8Comp.budget_canon B.Pb extraRows
  refine ⟨l1, l2, l3, b1, ?_, b3, b4, b5⟩
  show B.Pb.regs.length ≤ ComplJ8Comp.canonG B.Pb
  simp only [ComplJ8Comp.canonG]; omega

/-- **The claim obligation**, from the claim binders: the claim's atoms are `< p` (`hclA`), the registered
formulas' leaves are `< p` (`hregLeaf`), and `hleaf` (every demand root, in particular the claim nouns and the
registered formulas, has `≤ 2^109` leaves). -/
theorem claim_runG (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (cJ s f r) k).leafList, v < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataGen p Rg Rt hgen O).roots)
    (hregLeaf : ∀ id ∈ (j8DataGen p Rg Rt hgen O).regs, ∀ v ∈ (Nock.Jet.Autogen.compile p (Rt id)).leafList, v < p)
    (χ : Coins frameJ8 K) :
    let B := BOfG δ b Rt hgen O o hC hA AV fams
    (∀ k : Fin 3, ∀ v, FrameVS.claimNoun (cJ s f r) k = .atom v → v < p) ∧
    (∀ k : Fin 3, FrameVS.isCellN (FrameVS.claimNoun (cJ s f r) k) = true → ((B.M χ).m k).1 < p) ∧
    (∀ k : Fin 3, FrameVS.isCellN (FrameVS.claimNoun (cJ s f r) k) = true →
      (FrameVS.claimNoun (cJ s f r) k).internal / 2 ^ 62 < p) ∧
    (∀ x ∈ AcceptsJ8P.censusG B.Pb (cJ s f r), x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < p) ∧
    FrameVS.isCellN (cJ s f r).formula = true := by
  intro B
  have hroot : ∀ k : Fin 3, FrameVS.claimNoun (cJ s f r) k ∈ (j8DataGen p Rg Rt hgen O).roots := by
    intro k
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ _
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    fin_cases k <;> simp [FrameVS.claimNoun, cJ]
  have hleafN : ∀ k : Fin 3, (FrameVS.claimNoun (cJ s f r) k).leaves ≤ 2 ^ 110 :=
    fun k => (hleaf _ (hroot k)).trans (by norm_num)
  have hser : ∀ k : Fin 3, FrameVS.isCellN (FrameVS.claimNoun (cJ s f r) k) = true → ((B.M χ).m k).1 < p := by
    intro k hk
    have hlt : (j8DataGen p Rg Rt hgen O).cells.length < p := size_lt_pG Rt hgen O hp63 h31 (by simp [sizesJ8])
    have hne : (j8DataGen p Rg Rt hgen O).cells ≠ [] := List.ne_nil_of_length_pos hC
    show ((j8DataGen p Rg Rt hgen O).H (FrameVS.claimNoun (cJ s f r) k)).2 < p
    generalize FrameVS.claimNoun (cJ s f r) k = x at hk
    cases x with
    | atom v => simp [FrameVS.isCellN] at hk
    | cell a c =>
      exact lt_of_lt_of_le (ComplJ8Data.idxOf_lt_of_ne _ _ hne) hlt.le
  have hreg : ∀ id ∈ B.Pb.regs, (Nock.Jet.Autogen.compile p (B.Pb.Rt id)).leaves ≤ fuelChip ∧
      ∀ v ∈ (Nock.Jet.Autogen.compile p (B.Pb.Rt id)).leafList, v < p := by
    intro id hid
    refine ⟨(hleaf _ ?_).trans (by unfold fuelChip; norm_num), hregLeaf id hid⟩
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP p Rt _ _
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
  have hcf : FrameVS.isCellN (cJ s f r).formula = true := by
    obtain ⟨a, c, hfc⟩ := formula_cell_of_gen hgen
    simp [cJ, hfc, FrameVS.isCellN]
  exact ComplJ8Comp.claim_J8_instance hp63 _ _ hclA hleafN hser B.Pb hreg hcf

/-- **The weight and figure obligations** for any family list of pinned events with `≤ 2^66` pins. -/
theorem bad_groupG (hOK : ∀ L ∈ fams, ∀ e ∈ L, e.OK) (hpin : ∀ L ∈ fams, ∀ e ∈ L, ∀ i N, e ≠ BadSpec.ord i N)
    (hcnt : RowsLe31 (BOfG δ b Rt hgen O o hC hA AV fams).Pb → (fams.map ComplJ8Bad.nPins).sum ≤ 2 ^ 66) :
    let B := BOfG δ b Rt hgen O o hC hA AV fams
    (∀ e ∈ B.bad, (e.1.card : ℚ) / Fintype.card (Coins frameJ8 K) ≤ e.2) ∧
    (p = Nock.Atoms.p → Fintype.card K = VclL.Events.cK → RowsLe31 B.Pb → B.epsC < 1 / 2 ^ 120) := by
  intro B
  refine ⟨ComplJ8Bad.wt_badOf _ (ComplJ8Bad.badList_OK _ fams hOK), ?_⟩
  refine ComplJ8Bad.fig_badList δ B _ fams rfl hpin hcnt (by simp) ?_
  intro hr o ho
  simp only [List.mem_singleton] at ho
  subst ho
  exact hr.1

/-- **The J chip obligation** at a good coin, given the J pole family is in the bad list. -/
theorem jOK_runG (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hJ : famJ δ (j8DataGen p Rg Rt hgen O) ∈ fams) (χ : Coins frameJ8 K)
    (hχ : (BOfG δ b Rt hgen O o hC hA AV fams).Good χ) :
    let B := BOfG δ b Rt hgen O o hC hA AV fams
    JGenJ8.JChipOK δ b B.Pb.nodesJ B.Pb.orbitJ (chalsJJ8 χ) (B.M χ).pubsJ B.Pb.lay
      (qJ δ b B.Pb (B.tr χ) (chalsJJ8 χ) (B.M χ).pubsJ) := by
  intro B
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases h0 : (j8DataGen p Rg Rt hgen O).jrows.length = 0
  · refine ComplJ8Jet.jOK_absent δ b _ _ _ _ _ _ h0 ?_
    have hs : ∀ (g : Fin (j8DataGen p Rg Rt hgen O).jrows.length → Quad (algebraMap (ZMod p) K δ)), ∑ k, g k = 0 := by
      intro g; exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
    have hz : Quad.re _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 ∧ Quad.im _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 :=
      (Quad.mk_eq_zero_iff _ _ _).mp (Quad.mk_re_im _ 0)
    have e : ∀ i, pubsJOf δ (j8DataGen p Rg Rt hgen O) χ i = 0 := by
      intro i
      unfold pubsJOf
      rw [hs, hs]
      split_ifs <;> simp [pub2, hz.1, hz.2]
    exact ⟨e 0, e 1, e 2, e 3⟩
  · have hn : 0 < (j8DataGen p Rg Rt hgen O).jrows.length := Nat.pos_of_ne_zero h0
    obtain ⟨hinj, hadj⟩ := powN_ok (o) (n := (j8DataGen p Rg Rt hgen O).jrows.length)
      (le_two_pow_ht _ (by simp [sizesJ8]))
    have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length)] fams),
        χ ∉ e.1 := hχ
    have hpole := ComplJ8Bad.jNoPole δ (ComplJ8Jet.jKeysT (j8DataGen p Rg Rt hgen O).jrows.get)
      (ComplJ8Jet.jKeysX (j8DataGen p Rg Rt hgen O).jrows.get) χ
      (fun e he => ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hJ, he⟩)))
    have := ComplJ8Jet.jOK_present_trJ δ b (powN (o) _) (o) (chalsJJ8 χ) (pubsJOf δ _ χ)
      (j8DataGen p Rg Rt hgen O).jrows.get hinj hn hadj
      (fun i => jrows_gate_runG Rt hgen O hp hRt _ (List.get_mem _ _))
      (ComplJ8Jet.notJPole_of_keys δ _ _ hpole.1 hpole.2)
      (by simp only [pubsJOf]; exact pub2_mk δ _)
      (by simp only [pubsJOf]; simp [pub2, Quad.mk_re_im])
    exact this

/-- **The cell table obligation** at a good coin, given the cell validity and handle pole families are in the
bad list. -/
theorem cellOK_runG (hpG : p = Nock.Atoms.p) (hp63 : 2 ^ 63 < p) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataGen p Rg Rt hgen O).roots)
    (hV : famCellV δ (j8DataGen p Rg Rt hgen O) ∈ fams)
    (hH : famCellH δ b (j8DataGen p Rg Rt hgen O) hC (o) ∈ fams) (χ : Coins frameJ8 K)
    (hχ : (BOfG δ b Rt hgen O o hC hA AV fams).Good χ) :
    let B := BOfG δ b Rt hgen O o hC hA AV fams
    (CellTwinKW.cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).rap.Satisfies
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) ∧
    (CellTwinKW.cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).BindsPreprocessing
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  obtain ⟨hz, hrows⟩ := famCellV_good δ (j8DataGen p Rg Rt hgen O) χ (hin _ hV)
  obtain ⟨hcell, hrank⟩ := j8_cells_okG p Rg Rt hgen O hleaf
  obtain ⟨hinj, hadj⟩ := powN_ok (o) (n := (j8DataGen p Rg Rt hgen O).cells.length)
    (le_two_pow_ht _ (by simp [sizesJ8]))
  refine ⟨ComplJ8Enc.cellChipHQKW_honest_listE δ b hC (powN (o) _) (o) (chalsMJ8 δ χ)
    (pubsCOf δ b _ hC (o) χ) (by rw [hrc]; exact hp63) (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf _) _
    (mvF _) (mxF _)
    (fun _ => 0) (mhF _) hcell hrank rfl hinj hadj (ProbJ8.chalsOK_J8 δ χ) (InhabJ8MemMain.zJ_chals δ χ) hz
    (encR_cell δ χ) (encR_small δ hpG χ _)
    (fun j hj => (hrows j hj).1) (fun j hj _ => (hrows j hj).2.1) (fun j hj _ => (hrows j hj).2.2.1)
    (fun j hj => (hrows j hj).2.2.2.1) (fun j hj => (hrows j hj).2.2.2.2) ?_ ?_ ?_ ?_,
    ComplJ8Enc.cellChipHQKW_honest_list_bindE δ b hC _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · exact (pub2_mk2 δ (cvT δ _ χ) 0 rfl).symm
  · exact (pub2_mk2 δ (cxT δ _ χ) 2 rfl).symm
  · intro i
    rw [dRowW_split]
    exact ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 _ χ _ (ComplJ8Bad.ρH_re δ χ)
      (hin _ hH _ (List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩))
  · show Quad.mk _ (pub2 δ (chT δ b _ hC (o) χ) 4) (pub2 δ (chT δ b _ hC (o) χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    unfold chT
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dNW_pubs δ b _ hC (o) χ (pubsC0 δ _ χ) (pubsCOf δ b _ hC (o) χ)]

/-- **The J-8 walk obligation** at a good coin, given the walk validity and handle pole families are in the
bad list. -/
theorem walkOK_runG (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).reads)
    (hV : famWalkV δ (j8DataGen p Rg Rt hgen O) ∈ fams) (hH : famWalkH δ (j8DataGen p Rg Rt hgen O) ∈ fams)
    (χ : Coins frameJ8 K) (hχ : (BOfG δ b Rt hgen O o hC hA AV fams).Good χ) :
    let B := BOfG δ b Rt hgen O o hC hA AV fams
    (WalkJ8.walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).rap.Satisfies
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW) ∧
    (WalkJ8.walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).BindsPreprocessing
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  have hmW : (walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads).length ∈
      sizesJ8 (j8DataGen p Rg Rt hgen O) := by simp [sizesJ8]
  obtain ⟨hinj, hadj⟩ := powN_ok (o) (le_two_pow_ht _ hmW)
  have hrows := famWalkV_good δ (j8DataGen p Rg Rt hgen O) χ (hin _ hV)
  have hcl : (j8DataGen p Rg Rt hgen O).cells.length < ringChar (ZMod p) := by
    rw [hrc]; exact size_lt_pG Rt hgen O hp63 h31 (by simp [sizesJ8])
  have hkp : krW (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads +
      (walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads).length < ringChar (ZMod p) := by
    have := h31 _ hmW
    have := krW_le_rows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads
    have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; omega
  have hpoleH : ∀ (i : Fin (walkRows (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).reads).length),
      ∀ x ∈ walkHx δ (j8DataGen p Rg Rt hgen O) i (K := K), ComplJ8Bad.ρH δ χ + x χ ≠ 0 := by
    intro i x hx
    refine ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 x χ _ (ComplJ8Bad.ρH_re δ χ) (hin _ hH _ ?_)
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hsplit := walk_dRow_split δ b (j8DataGen p Rg Rt hgen O) (o) hinj χ
    (pubsWOf δ b (j8DataGen p Rg Rt hgen O) (o) χ)
  have hwalk' := ComplJ8Enc.walkChipJ8_honest_listE δ b (walk_pos _ _) (powN (o) _) (o)
    (chalsMJ8 δ χ) (pubsWOf δ b (j8DataGen p Rg Rt hgen O) (o) χ) (encR δ χ) (γV δ χ) (ρV δ χ) _ _ (kLW _) (vLW _) (kRW _) (vRW _)
    (GeneratedField.primeFieldElems_zmod p) (by rw [hrc]; exact hp63) hcl hwalk hkp rfl hinj hadj
    (ProbJ8.chalsOK_J8 δ χ) (fun j hj => (hrows j hj).1) (fun j hj => (hrows j hj).2.1)
    (fun j hj => (hrows j hj).2.2) (pub2_mk2 δ (wxT δ (j8DataGen p Rg Rt hgen O) χ) 0 rfl).symm (pub2_mk2 δ (wpT δ (j8DataGen p Rg Rt hgen O) χ) 2 rfl).symm
    (fun i => hdl_kind _ _ _) (fun i => hdl_kind _ _ _)
    (fun i => by
      rw [(hsplit i).1]
      exact hpoleH i (fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).idx, (kLW _ i, vLW _ i),
        (kRW _ i, vRW _ i))) (by simp only [walkHx, dif_pos i.isLt]; exact List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.1]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).ridx, 2 * (wValsC δ _ χ i).pre,
        (kLW _ i, vLW _ i))) (by simp only [walkHx, dif_pos i.isLt]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.2]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).ridx, 2 * (wValsC δ _ χ i).pre + 1,
        (kRW _ i, vRW _ i))) (by
          simp only [walkHx, dif_pos i.isLt]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    ?_ ?_
  · exact hwalk'
  · show Quad.mk _ (pub2 δ (whX δ b (j8DataGen p Rg Rt hgen O) (o) χ) 4) (pub2 δ (whX δ b (j8DataGen p Rg Rt hgen O) (o) χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b (j8DataGen p Rg Rt hgen O) (o) hinj χ (pubsW0 δ (j8DataGen p Rg Rt hgen O) χ) (pubsWOf δ b (j8DataGen p Rg Rt hgen O) (o) χ) _ (Or.inl rfl)]
  · show Quad.mk _ (pub2 δ (whP δ b (j8DataGen p Rg Rt hgen O) (o) χ) 6) (pub2 δ (whP δ b (j8DataGen p Rg Rt hgen O) (o) χ) 7) = _
    rw [pub2_mk2 δ _ 6 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b (j8DataGen p Rg Rt hgen O) (o) hinj χ (pubsW0 δ (j8DataGen p Rg Rt hgen O) χ) (pubsWOf δ b (j8DataGen p Rg Rt hgen O) (o) χ) _ (Or.inr (Or.inl rfl)),
      dN_pubs δ b (j8DataGen p Rg Rt hgen O) (o) hinj χ (pubsW0 δ (j8DataGen p Rg Rt hgen O) χ) (pubsWOf δ b (j8DataGen p Rg Rt hgen O) (o) χ) _ (Or.inr (Or.inr rfl))]

end Obl
section Stat
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds HregC)
open Nock.Jet.ChipJ8 (layoutJ8 tvKey axPosB)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
  (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hC : 0 < (j8DataGen p Rg Rt hgen O).cells.length)
  (hA : 0 < (j8DataGen p Rg Rt hgen O).acs.length) (AV : AVPart p K) (fams : List (List (BadSpec K)))
/-- **The static obligation** (`hlay hsmall huniq hTpl hnd hidx hrk hlt`) from the jet binder `hRt` (the witness
of `HregC`), `hax`, `hleaf` and the row binder. -/
theorem stat_runG (hp63 : 2 ^ 63 < p) (hax : ProgAxOK p t) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataGen p Rg Rt hgen O).roots)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    let B := BOfG δ b Rt hgen O o hC hA AV fams
    List.ofFn B.Pb.lay = layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids ∧
    (∀ q ∈ layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids).filterMap tvKey).Nodup ∧
    (∀ i ∈ B.Pb.regs, Rg.R i = some ⟨(B.Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (B.Pb.Rt i)⟩ ∧
      axPosB (B.Pb.Rt i) = true ∧ (B.Pb.Rt i).WellTyped p) ∧
    B.Pb.regs.Nodup ∧ (∀ id ∈ B.Pb.regs, B.Pb.idx id < p) ∧ (∀ id ∈ B.Pb.regs, B.Pb.rk id ≠ (0, 0)) ∧
    (∀ id ∈ B.Pb.regs, (B.Pb.rk id).1 < ringChar (ZMod p) ∧ (B.Pb.rk id).2 < ringChar (ZMod p) ∧
      B.Pb.idx id < ringChar (ZMod p)) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h2 : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
  have hcalls := ComplJ8Jet.calls_of_hregC hgen Rt hRt
  have hcl := calls_called hgen
  have hlt := calls_lt hgen hax
  have hmemR : ∀ id ∈ (j8DataGen p Rg Rt hgen O).regs, ∃ cl ∈ (j8DataGen p Rg Rt hgen O).calls, cl.1 = id := by
    intro id hid
    have := List.mem_dedup.mp hid
    obtain ⟨cl, hcl, e⟩ := List.mem_map.mp this
    exact ⟨cl, hcl, e⟩
  have hlay : List.ofFn B.Pb.lay = layoutJ8 B.Pb.Rt B.Pb.regs B.Pb.ids := by
    show List.ofFn (Nock.Jet.ChipJ8T.HonestRAP.layJ (j8DataGen p Rg Rt hgen O).jrows.get) =
      layoutJ8 Rt (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).ids
    rw [← jrows_pre_runG Rt hgen O]
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp [Nock.Jet.ChipJ8T.HonestRAP.layJ]
  have hJlen : (layoutJ8 Rt (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).ids).length < p := by
    rw [← jrows_pre_runG Rt hgen O, List.length_map]
    exact size_lt_pG Rt hgen O hp63 h31 (by simp [sizesJ8])
  have hcells : (j8DataGen p Rg Rt hgen O).cells.length < p := size_lt_pG Rt hgen O hp63 h31 (by simp [sizesJ8])
  have hidsl : (j8DataGen p Rg Rt hgen O).ids.length < p := by
    have h1 : (j8DataGen p Rg Rt hgen O).ids.length ≤ (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length := by
      show (List.map Prod.fst (Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t))).length ≤ _
      rw [List.length_map]
      unfold Nock.V1J8.Gen.callsOf ComplJ8Data.rowsOfT
      exact (List.length_filterMap_le _ _).trans (by simp; rfl)
    exact lt_of_le_of_lt h1 (size_lt_pG Rt hgen O hp63 h31 List.mem_cons_self)
  have hblk := ComplJ8Jet.blocksOK_of_calls hp Rt (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).calls
    hcalls hlt hJlen
  have hroot : ∀ id ∈ (j8DataGen p Rg Rt hgen O).regs,
      Nock.Jet.Autogen.compile p (Rt id) ∈ (j8DataGen p Rg Rt hgen O).roots := by
    intro id hid
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP p Rt _ _
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
  have hne : (j8DataGen p Rg Rt hgen O).cells ≠ [] := List.ne_nil_of_length_pos hC
  have hidx : ∀ id ∈ (j8DataGen p Rg Rt hgen O).regs, (j8DataGen p Rg Rt hgen O).idx id < p :=
    fun id _ => lt_of_lt_of_le (ComplJ8Data.idxOf_lt_of_ne _ _ hne) hcells.le
  have hrk : ∀ id ∈ (j8DataGen p Rg Rt hgen O).regs, (j8DataGen p Rg Rt hgen O).rk id ≠ (0, 0) :=
    fun id _ => rk_ne _ (ComplJ8Data.compile_isCell p (Rt id))
  have hrkl : ∀ id ∈ (j8DataGen p Rg Rt hgen O).regs, ((j8DataGen p Rg Rt hgen O).rk id).1 < p ∧
      ((j8DataGen p Rg Rt hgen O).rk id).2 < p := by
    intro id hid
    have hl := hleaf _ (hroot id hid)
    have hi := ComplJ8Walk.internal_lt_leaves (Nock.Jet.Autogen.compile p (Rt id))
    have h62 : (Nock.Jet.Autogen.compile p (Rt id)).internal % 2 ^ 62 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
    have hd : (Nock.Jet.Autogen.compile p (Rt id)).internal / 2 ^ 62 ≤ (Nock.Jet.Autogen.compile p (Rt id)).internal :=
      Nat.div_le_self _ _
    have : (2 : ℕ) ^ 62 < 2 ^ 63 := by norm_num
    refine ⟨?_, ?_⟩
    · show (Nock.Jet.Autogen.compile p (Rt id)).internal / 2 ^ 62 < p
      have : (Nock.Jet.Autogen.compile p (Rt id)).internal < 2 ^ 109 := lt_of_lt_of_le hi hl
      have h109 : (Nock.Jet.Autogen.compile p (Rt id)).internal / 2 ^ 62 < 2 ^ 47 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]; calc _ < 2 ^ 109 := this
          _ = 2 ^ 47 * 2 ^ 62 := by rw [← pow_add]
      have : (2 : ℕ) ^ 47 < 2 ^ 63 := by norm_num
      omega
    · show (Nock.Jet.Autogen.compile p (Rt id)).internal % 2 ^ 62 < p
      omega
  refine ComplJ8Jet.stat_of hp Rt _ _ _ _ _ ⟨Rt, hRt⟩ hRt (fun i hi => ?_) hlay (fun i hi => ?_) hidsl
    hblk (List.nodup_dedup _) hidx hrk (fun id hid => ?_)
  · obtain ⟨cl, hcl', rfl⟩ := hmemR i hi; exact hcl cl hcl'
  · obtain ⟨cl, hcl', rfl⟩ := hmemR i hi; exact hlt cl hcl'
  · rw [hrc]; exact ⟨(hrkl id hid).1, (hrkl id hid).2, hidx id hid⟩

end Stat
section Final
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList nPins)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L (qAL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (claimRecsJ8 pinRecsJ8)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **The honest record of the run** (concrete atom part, the run's families). -/
abbrev BRG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hC : 0 < (j8DataGen p Rg Rt hgen O).cells.length)
    (hA : 0 < (j8DataGen p Rg Rt hgen O).acs.length) : HonestJ8 p K δ Rg fuel s f r :=
  BOfG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA)
    (famsOfO δ b (j8DataGen p Rg Rt hgen O) o hC)

theorem regs_calledG :
    ∀ id ∈ (j8DataGen p Rg Rt hgen O).regs, id ∈ CalledIds t := by
  intro id hid
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hid)
  exact calls_called hgen cl hcl

/-- **The cell list is non-empty** (the formula is a cell and a demand root). -/
theorem cells_posG : 0 < (j8DataGen p Rg Rt hgen O).cells.length := by
  obtain ⟨a, c, hf⟩ := formula_cell_of_gen hgen
  have hroot : Noun.cell a c ∈ (j8DataGen p Rg Rt hgen O).roots := by
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ _
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    simp [hf]
  exact List.length_pos_of_mem ((O.permC _).mem_iff.mpr (mem_cellsOfRoots_of_root _ [] a c hroot))

/-- **The atom cell list is non-empty.** -/
theorem acs_posG : 0 < (j8DataGen p Rg Rt hgen O).acs.length :=
  List.length_pos_of_ne_nil (ComplJ8Data.acsP_ne _ _ _)

/-- **The honest record of the run, over any orbit `o` of height `htJ8`** (`hC hA` derived). -/
abbrev BRunG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) : HonestJ8 p K δ Rg fuel s f r :=
  BRG δ b Rt hgen O o (cells_posG Rt hgen O) (acs_posG Rt hgen O)

end Final
end
end ComplJ8OfG_1

/-! ### Twins of `ComplJ8OfAtom` -/

section ComplJ8OfAtomG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList quadPole ReadsOff)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
noncomputable section
section AWAtRun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **`awOK` at the run** (the `OpenJ8.awOK` field at `BOfG … (avOf …) fams`), given the two atom-walk pole families
are in `fams`; binder `hwalkA := WalkDepthOK preads`. -/
theorem awOK_runG (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O))) (hC : 0 < (j8DataGen p Rg Rt hgen O).cells.length)
    (hA : 0 < (j8DataGen p Rg Rt hgen O).acs.length) (fams : List (List (BadSpec K)))
    (hp63 : 2 ^ 63 < p) (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataGen p Rg Rt hgen O).preads)
    (hV : famAWV δ (j8DataGen p Rg Rt hgen O) ∈ fams) (hH : famAWH δ (j8DataGen p Rg Rt hgen O) ∈ fams)
    (χ : Coins frameJ8 K)
    (hχ : (BOfG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams).Good χ) :
    let B := BOfG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams
    AWChipOK δ b B.Pb.krootsV B.Pb.hnV B.Pb.nodesV B.Pb.orbitV (chalsAJ8Z δ χ) (B.M χ).pubsV
      (AcceptsJ8.qV δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsV) := by
  intro B
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  exact awOK_DO δ b (j8DataGen p Rg Rt hgen O) o hp63 h31 hwalkA (fun x => hdl_kind _ _ _) χ (hin _ hV) (hin _ hH)

end AWAtRun
section AcsFacts
open Nock.V1J8.Gen (combOf spineOf hdN' tlN' atomV padN)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom (combOf_cons spineOf_cons2 spineOf_short mem_spineOf
  shape_acsP mem_acsP mem_spineL len_le_of_sub combOf_isCell tl_combOf genHyp_j8)
variable (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **The atom cell list of a generated run** (Goldilocks): every row is a cell, has rank `< 2^110` (from
`|acs| ≤ 2^31`: a spine's rows are distinct members of `acs`, so a comb has at most `|acs| + 1` limbs), and the
tail of a row is a row when it is a cell. -/
theorem acs_okG (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (h31 : Rows31 (j8DataGen Nock.Atoms.p Rg Rt hgen O)) :
    (∀ c ∈ (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs, c.isCell = true) ∧
    (∀ c ∈ (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs, rankOf c < 2 ^ 110) ∧
    (∀ c ∈ (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs, (tlN' c).isCell = true →
      tlN' c ∈ (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs) := by
  have hN : (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataGen Nock.Atoms.p Rg Rt hgen O).t]).length (by simp [sizesJ8])
    rw [data_rowsG hgen O]
    simpa [ComplJ8Data.rowsOfT, j8DataGen] using h
  have h31 : (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length ≤ 2 ^ 31 :=
    h31 _ (by simp [sizesJ8])
  have hg := genHyp_j8G Rg Rt hgen O hax hop5 hN
  have hsp : ∀ a ∈ (j8DataGen Nock.Atoms.p Rg Rt hgen O).bigs, ∀ x ∈ spineOf (Nock.Atoms.limbs a),
      x ∈ (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs := fun a ha x hx =>
    (mem_acsP _ _ x).mpr (Or.inl ((mem_spineL _ x).mpr ⟨a, ha, hx⟩))
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc htl => ?_⟩
  · obtain ⟨l, h2, -, hy, -⟩ := shape_acsP _ _ hg.big c hc
    rw [hy]; exact combOf_isCell l h2
  · obtain ⟨l, h2, -, hy, h3⟩ := shape_acsP _ _ hg.big c hc
    show c.internal < 2 ^ 110
    have e := internal_combOf l h2
    rw [hy]
    by_cases hl : 3 ≤ l.length
    · obtain ⟨-, a, ha, d, rfl⟩ := h3 hl
      have hs := len_le_of_sub (spineOf_facts (Nock.Atoms.limbs a)).1 (hsp a ha)
      have h4 := (spineOf_facts (Nock.Atoms.limbs a)).2
      have h5 : ((Nock.Atoms.limbs a).drop d).length ≤ (Nock.Atoms.limbs a).length := by
        rw [List.length_drop]; omega
      have : (2 : ℕ) ^ 31 + 2 < 2 ^ 110 := by norm_num
      omega
    · have : (2 : ℕ) < 2 ^ 110 := by norm_num
      omega
  · obtain ⟨l, h2, -, hy, h3⟩ := shape_acsP _ _ hg.big c hc
    rw [hy, tl_combOf l h2] at htl ⊢
    by_cases hl : 3 ≤ l.length
    · rw [if_pos hl]
      obtain ⟨-, a, ha, d, rfl⟩ := h3 hl
      refine hsp a ha _ ((mem_spineOf _ _).mpr ⟨d + 1, ?_, ?_⟩)
      · rw [List.length_drop] at hl ⊢; omega
      · rw [List.tail_drop]
    · rw [if_neg hl] at htl; simp [Noun.isCell] at htl

end AcsFacts
section AtomRun
open Nock.V1J8.Gen (hdN' tlN' atomV)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
variable (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **The rows bound from `h31`**: the `GenHyp.rows31` input of `genHyp_j8G` / `genHyp_mb`,
by the recipe of `noIncCorner_of_j8` (`data_rows hgen` + `rowsOfT`). -/
theorem rows_le_of_rows31G (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) :
    (j8DataGen p Rg Rt hgen O).rows.size ≤ 2 ^ 31 := by
  have h := h31 (bfsForest [(j8DataGen p Rg Rt hgen O).t]).length (by simp [sizesJ8])
  rw [data_rowsG hgen O]
  simpa [ComplJ8Data.rowsOfT, j8DataGen] using h

/-- **`atomOK` at the run** (the `OpenJ8.atomOK` field at `BOfG … (avOf …) fams`, Goldilocks), given the six atom
pole families (`famAZ famAV famAH famMB famC famMI`) are in `fams`. Rank bound from `h31`; `hcor`: no inc corner
(`atomOK_runG` below discharges it under `complJ8`'s binders). -/
theorem atomOK_run_genG (hpG : p = Nock.Atoms.p) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O)))
    (hC : 0 < (j8DataGen p Rg Rt hgen O).cells.length) (hA : 0 < (j8DataGen p Rg Rt hgen O).acs.length)
    (fams : List (List (BadSpec K))) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hlast : Nock.V1J8.Gen.lastIdxOf (j8DataGen p Rg Rt hgen O).acs (ComplJ8Data.combPP p) =
      Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).acs (ComplJ8Data.combPP p))
    (mZ : famAZ (K := K) ∈ fams) (mV : famAV δ (j8DataGen p Rg Rt hgen O) ∈ fams)
    (mH : famAH δ b (j8DataGen p Rg Rt hgen O) hA (o) ∈ fams)
    (mMB : famMB δ b (j8DataGen p Rg Rt hgen O) hA (o) ∈ fams)
    (mC : famC δ b (j8DataGen p Rg Rt hgen O) hA (o) ∈ fams)
    (mMI : famMI δ b (j8DataGen p Rg Rt hgen O) hA (o) ∈ fams)
    (χ : Coins frameJ8 K)
    (hχ : (BOfG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams).Good χ) :
    let B := BOfG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) := by
  intro B
  subst hpG
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(j8DataGen Nock.Atoms.p Rg Rt hgen O).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  have hz := famAZ_good δ χ (hin _ mZ)
  have hv := famAV_good δ (j8DataGen Nock.Atoms.p Rg Rt hgen O) χ (hin _ mV)
  obtain ⟨hpH, hpMB, hpC, hpMI⟩ := atomPoles_good δ b (j8DataGen Nock.Atoms.p Rg Rt hgen O) hA (o) χ
    (hin _ mH) (hin _ mMB) (hin _ mC) (hin _ mMI) (pubsAOf δ b (j8DataGen Nock.Atoms.p Rg Rt hgen O) hA (o) χ)
  have hmA : (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length ∈ sizesJ8 (j8DataGen Nock.Atoms.p Rg Rt hgen O) := by
    simp [sizesJ8]
  obtain ⟨hcell, hrank, htl⟩ := acs_okG Rg Rt hgen O hax hop5 h31
  obtain ⟨hinj, hadj⟩ := powN_ok (o) (le_two_pow_ht _ hmA)
  obtain ⟨tV, tX, tH, tMB, tC, tMI⟩ := atomTerms δ b (j8DataGen Nock.Atoms.p Rg Rt hgen O) hA (o) χ
  have hsat0 := ComplJ8Cell.cellChipHQ_honest_listP δ b hA (powN (o) _) (o) (chalsAJ8Z δ χ)
    (pubsAOf δ b (j8DataGen Nock.Atoms.p Rg Rt hgen O) hA (o) χ) (γV δ χ) (ρV δ χ) (zA δ χ) (fun _ => none)
    (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs (mvA _) (mxAF _) (fun _ => 0) (ptA _) (mhvA _) hcell hrank rfl hinj hadj
    (ChalsAZJ8.chalsAJ8Z_ok δ χ) rfl hz (fun j hj => (hv j hj).1) (fun j hj _ => (hv j hj).2.1)
    (fun j hj _ => (hv j hj).2.2.1) (fun j hj => (hv j hj).2.2.2.1) (fun j hj => (hv j hj).2.2.2.2)
    tV tX hpH tH
  have hcol : ∀ i : Fin (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length,
      let y := (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs[(i : ℕ)]
      colAH δ b _ hA (o) χ (pubsAOf δ b _ hA (o) χ) Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA (o) χ (pubsAOf δ b _ hA (o) χ) Cell.idR i =
        (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs
            (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows y else 0 : ℕ))
          : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA (o) χ (pubsAOf δ b _ hA (o) χ) Cell.wL i =
        (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA (o) χ (pubsAOf δ b _ hA (o) χ) Cell.wR i =
        (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA (o) χ (pubsAOf δ b _ hA (o) χ) Cell.aL i =
        ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA (o) χ (pubsAOf δ b _ hA (o) χ) Cell.aR i =
        ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p) := by
    intro i y
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := colAH_fields δ b _ hA (o) χ
      (pubsAOf δ b _ hA (o) χ) i
    refine ⟨c1, ?_, c3, c4, c5, c6⟩
    rw [c2]
    by_cases hc : (tlN' y).isCell = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]; simp
  have res := atomOK_j8_genG δ b Rg Rt hgen O hA (powN (o) _) (o) (chalsAJ8Z δ χ)
    (pubsAOf δ b _ hA (o) χ) (colAH δ b _ hA (o) χ (pubsAOf δ b _ hA (o) χ))
    hax hop5 (rows_le_of_rows31G Rt hgen O h31) hinj hadj hcol hsat0 hpMB hpC hpMI tMB tC tMI
  exact res

/-- **`lastIdxOf = idxOf` at `comb p` under `complJ8`'s binders** (J-8: `bigBound_single`; the premise of
`ComplJ8Data.ptrP_eq_idxOf`). -/
theorem last_eq_of_j8G (hpG : p = Nock.Atoms.p) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O)) :
    Nock.V1J8.Gen.lastIdxOf (j8DataGen p Rg Rt hgen O).acs (ComplJ8Data.combPP p) =
      Nock.V1J8.Gen.idxOf (j8DataGen p Rg Rt hgen O).acs (ComplJ8Data.combPP p) :=
  (bigBound_singleG hgen O hpG (hclA 0) (hclA 1) hRt hop5
    (rows_le_of_rows31G Rt hgen O h31)).2.2.2.2.1

/-- **`atomOK` at the run** (the `OpenJ8.atomOK` field at `BOfG … (avOf …) fams`, Goldilocks), given the six atom
pole families (`famAZ famAV famAH famMB famC famMI`) are in `fams`. Rank bound from `h31`. Also needs `hclA` and `hRt`; the conclusion is false at `hax hop5 h31` alone (the inc corner run, `Batch4851.noIncCorner_neg`). -/
theorem atomOK_runG (hpG : p = Nock.Atoms.p) (o : StrictOrbitDomain (ZMod p) 3 (htJ8 (j8DataGen p Rg Rt hgen O)))
    (hC : 0 < (j8DataGen p Rg Rt hgen O).cells.length) (hA : 0 < (j8DataGen p Rg Rt hgen O).acs.length)
    (fams : List (List (BadSpec K))) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataGen p Rg Rt hgen O))
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (mZ : famAZ (K := K) ∈ fams) (mV : famAV δ (j8DataGen p Rg Rt hgen O) ∈ fams)
    (mH : famAH δ b (j8DataGen p Rg Rt hgen O) hA (o) ∈ fams)
    (mMB : famMB δ b (j8DataGen p Rg Rt hgen O) hA (o) ∈ fams)
    (mC : famC δ b (j8DataGen p Rg Rt hgen O) hA (o) ∈ fams)
    (mMI : famMI δ b (j8DataGen p Rg Rt hgen O) hA (o) ∈ fams)
    (χ : Coins frameJ8 K)
    (hχ : (BOfG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams).Good χ) :
    let B := BOfG δ b Rt hgen O o hC hA (avOfO δ b (j8DataGen p Rg Rt hgen O) o hA) fams
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (AtomChipHQ.atomChipHQ δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8.qA δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).rap.Satisfies
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) ∧
    (atomChipHQL δ b B.Pb.hnA B.Pb.nodesA B.Pb.orbitA (chalsAJ8Z δ χ) (B.M χ).pubsA).BindsPreprocessing
      (AcceptsJ8L.qAL δ b B.Pb (B.tr χ) (chalsAJ8Z δ χ) (B.M χ).pubsA) :=
  atomOK_run_genG δ b Rt hgen O hpG o hC hA fams hax hop5 h31 (last_eq_of_j8G Rt hgen O hpG hop5 hclA hRt h31)
    mZ mV mH mMB mC mMI χ hχ

end AtomRun
end
end ComplJ8OfAtomG_1

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
