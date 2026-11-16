/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALStatic.lean

  **J-9 AL completeness: the static, census, primitive and length facts at the overlay data `DL`.**
  * `stat_L`: the eight static conjuncts of `ComplJ9AOfStatic.stat_A` at `(honestJ8Of … DL …).Pb` (J-only `regs`), from
    the prim-aware binder `hRtJ` (`hRt` on non-primitive called ids only); `stat_core` is not edited, its proof is
    replayed on `DL`.
  * `cen_L`: `hcen'` over `censusGJ9 Pb c ++ psRun.map (primC ·.2)`, bound `(DL).acs.length + 2`.
  * `prims_L`: `hPrim hdisjP hndP hrkP hltP` and the id/index ranges of `hlenL`, at `psRun`.
  * `lengths_L`: the two length facts (`hlenL`'s `nL + n < p`, `hlenCP`).
  * `bud_genericL`: `BudJ9AL` at the canonical rows, and the `hbudV` conjuncts.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALObl
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfStatic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALStatic

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
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)



open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9

open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V (AcceptsJ9V)

open Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ prob_exists_le RowsLe31)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AcceptsJ9A AXChipOK SPChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A

open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (AcceptsJ9AL ALChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (aluSZChipJ9)
open Nock.Jet.Prim (PrimOp)


open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl (HonestJ9A RowsLe31A)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfStatic (p63 lt_p calls_lt9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.Jet.Prim (PrimOp primC primSpec)
open Nock.Jet.ChipJ8 (layoutJ8 tvKey axPosB)
open Nock.V1J8.Gen (callsOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (jCallsP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec)

noncomputable section

section Stat

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf rowsOfT)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (prims : List (ℕ × PrimOp)) (hpG : p = Nock.Atoms.p)
  (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
  (h31 : ComplJ9ARun.Rows31A (ComplJ9ALData.j9alDataOf p Rg Rt prims hgen))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => ComplJ9ALData.j9alDataOf p Rg Rt prims hgen
local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A
set_option quotPrecheck false

include hpG h31 in
theorem hFL : DvdOK (DL) := ComplJ9ARun.dvdOK_of_A (ComplJ9ARun.dvdA_of_rows hpG _ h31)
local notation "FL" => hFL (Rt := Rt) (hgen := hgen) (prims := prims) hpG h31
local notation "psRun" => ComplJ9ALData.primsC prims (List.map Prod.fst (J8Data.calls (DA)))
local notation "vcRun" => ComplJ9ALData.idxPOf (J8Data.cells (DA)) prims
local notation "mRun" => fun id : ℕ =>
  ((ComplJ9ALData.pcallsR (prims.map Prod.fst) (rowsOfT t)).countP fun x => x.1 = id) + 1   -- mP = c+1
local notation "tbR" y:max => AluSatRun.tblRun δ Rt prims hgen psRun vcRun mRun y
local notation "famsJL" => famsOf δ b (DL) FL (cellsL_pos Rt prims hgen) ++
  ComplJ9BOf.famsA9 δ b (DL) (DL) FL (acsL_pos Rt prims hgen)
local notation "AVL" => ComplJ9BBalF.avOf9 δ b (DL) FL (avOf δ b (DL) FL (acsL_pos Rt prims hgen))
local notation "B8L" => honestJ8Of δ b (DL) FL (cellsL_pos Rt prims hgen) (acsL_pos Rt prims hgen) AVL famsJL
-- (`abbrev`s; here `local notation`s, since the section variables are explicit.)
-- ALU terminals, n abstract (padding rows contribute 0):
--   SV n χ := ∑ i : Fin n, AluSatRows.tV δ (chalsALJ8 δ χ) (tbR (yOf δ χ)) i     (likewise SS with tS, SX with tX)



/-! ### Size memberships and call facts at `DL` -/

theorem memL_cells : (DL).cells.length ∈ sizesA (DL) := List.mem_append_left _ (by simp [sizesJ8])
theorem memL_jrows : (DL).jrows.length ∈ sizesA (DL) := List.mem_append_left _ (by simp [sizesJ8])
theorem memL_acs : (DL).acs.length ∈ sizesA (DL) := List.mem_append_left _ (by simp [sizesJ8])
theorem memL_bfs : (bfsForest [(DL).t]).length ∈ sizesA (DL) := List.mem_append_left _ (by simp [sizesJ8])
theorem memL_N9 : N9 t ∈ sizesA (DL) := List.mem_append_right _ List.mem_cons_self

/-- Every J call of the overlay has an id `< p` (the run's call ids, `calls_lt9`). -/
theorem callsL_lt (hax9 : ProgAxOK9A p t) : ∀ cl ∈ (DL).calls, cl.1 < p := fun cl hcl =>
  calls_lt9 hgen hax9 cl (jCallsP_sub _ _ cl (show cl ∈ jCallsP (prims.map Prod.fst) (callsOf (rowsOfT t)) from hcl)).1

/-- The J calls of the overlay are at most the BFS rows. -/
theorem callsL_len : (DL).calls.length ≤ (bfsForest [t]).length := by
  show (jCallsP (prims.map Prod.fst) (callsOf (rowsOfT t))).length ≤ _
  refine (List.length_filter_le _ _).trans ?_
  unfold callsOf rowsOfT
  exact (List.length_filterMap_le _ _).trans (by simp)

/-- The registered ids of the overlay are called ids of the run. -/
theorem regsL_called : ∀ id ∈ (DL).regs, ∃ cl ∈ (DL).calls, cl.1 = id := by
  intro id hid
  rw [ComplJ9ALData.F_regs Rt prims hgen] at hid
  obtain ⟨cl, hcl, e⟩ := List.mem_map.mp (List.mem_dedup.mp hid)
  exact ⟨cl, hcl, e⟩

theorem regsL_sub : ∀ id ∈ (DL).regs, id ∈ (DD).regs := by
  intro id hid
  obtain ⟨cl, hcl, rfl⟩ := regsL_called Rt hgen prims id hid
  have hcl0 : cl ∈ jCallsP (prims.map Prod.fst) (callsOf (rowsOfT t)) := hcl
  have h1 := (jCallsP_sub _ _ cl hcl0).1
  show cl.1 ∈ (List.map Prod.fst (callsOf (rowsOfT t))).dedup
  exact List.mem_dedup.mpr (List.mem_map.mpr ⟨cl, h1, rfl⟩)

theorem regsL_len : (DL).regs.length ≤ (bfsForest [t]).length := by
  rw [ComplJ9ALData.F_regs Rt prims hgen]
  exact ((List.dedup_sublist _).length_le.trans (by rw [List.length_map])).trans (callsL_len Rt hgen prims)

/-! ### The static fields -/

include hpG h31 in
/-- **`stat_L`: the eight static conjuncts of `stat_A` at the overlay layout** (`Pb := (honestJ8Of … DL …).Pb`,
J-only `regs`), from the prim-aware `hRtJ` (`hRt` on non-primitive called ids only). -/
theorem stat_L (hF : DvdOK (DL)) (hC : 0 < (DL).cells.length) (hA : 0 < (DL).acs.length)
    (AV : AVPart p K) (fams : List (List (BadSpec K))) (hax9 : ProgAxOK9A p t) (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    List.ofFn (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.lay =
      layoutJ8 (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.Rt (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.regs
        (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.ids ∧
    (∀ q ∈ layoutJ8 (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.Rt (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.regs
        (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.ids,
      q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
    ((layoutJ8 (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.Rt (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.regs
        (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.ids).filterMap tvKey).Nodup ∧
    (∀ i ∈ (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.regs,
      Rg.R i = some ⟨((honestJ8Of δ b (DL) hF hC hA AV fams).Pb.Rt i).toTemplate p,
        Nock.Jet.Autogen.compile p ((honestJ8Of δ b (DL) hF hC hA AV fams).Pb.Rt i)⟩ ∧
      axPosB ((honestJ8Of δ b (DL) hF hC hA AV fams).Pb.Rt i) = true ∧
      ((honestJ8Of δ b (DL) hF hC hA AV fams).Pb.Rt i).WellTyped p) ∧
    (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.regs.Nodup ∧
    (∀ id ∈ (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.regs, (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.idx id < p) ∧
    (∀ id ∈ (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.regs,
      (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.rk id ≠ (0, 0)) ∧
    (∀ id ∈ (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.regs,
      ((honestJ8Of δ b (DL) hF hC hA AV fams).Pb.rk id).1 < ringChar (ZMod p) ∧
      ((honestJ8Of δ b (DL) hF hC hA AV fams).Pb.rk id).2 < ringChar (ZMod p) ∧
      (honestJ8Of δ b (DL) hF hC hA AV fams).Pb.idx id < ringChar (ZMod p)) := by
  have hp63 := p63 (p := p) hpG
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcalls := ComplJ9ALData.callsL_of_hRt Rt prims hgen hRtJ
  have hlt := callsL_lt Rt hgen prims hax9
  have hjl : (DL).jrows.length < p := lt_p hpG (h31 _ (memL_jrows Rt hgen prims))
  have hcells : (DL).cells.length < p := lt_p hpG (h31 _ (memL_cells Rt hgen prims))
  have hbfs : (bfsForest [t]).length < p := lt_p hpG (h31 _ (memL_bfs Rt hgen prims))
  have hmemR : ∀ id ∈ (DL).regs, ∃ cl ∈ (DL).calls, cl.1 = id := regsL_called Rt hgen prims
  have hlay : List.ofFn (Nock.Jet.ChipJ8T.HonestRAP.layJ (DL).jrows.get) =
      layoutJ8 Rt (DL).regs (DL).ids := by
    rw [← ComplJ9ALData.jrows_preL Rt prims hgen]
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp [Nock.Jet.ChipJ8T.HonestRAP.layJ]
  have hJlen : (layoutJ8 Rt (DL).regs (DL).ids).length < p := by
    rw [← ComplJ9ALData.jrows_preL Rt prims hgen, List.length_map]
    exact hjl
  have hidsl : (DL).ids.length < p := by
    have h1 : (DL).ids.length ≤ (bfsForest [t]).length := by
      show (List.map Prod.fst (DL).calls).length ≤ _
      rw [List.length_map]
      exact callsL_len Rt hgen prims
    exact lt_of_le_of_lt h1 hbfs
  have hblk := ComplJ8Jet.blocksOK_of_calls hp Rt (DL).regs (DL).calls hcalls hlt hJlen
  have hroot : ∀ id ∈ (DL).regs, Nock.Jet.Autogen.compile p (Rt id) ∈ (DD).roots := by
    intro id hid
    have hidD := regsL_sub Rt hgen prims id hid
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP p Rt _ _
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hidD, rfl⟩))
  have hne : (DL).cells ≠ [] := List.ne_nil_of_length_pos hC
  have hidx : ∀ id ∈ (DL).regs, (DL).idx id < p :=
    fun id _ => lt_of_lt_of_le (ComplJ8Data.idxOf_lt_of_ne _ _ hne) hcells.le
  have hrk : ∀ id ∈ (DL).regs, (DL).rk id ≠ (0, 0) :=
    fun id _ => rk_ne _ (ComplJ8Data.compile_isCell p (Rt id))
  have hrkl : ∀ id ∈ (DL).regs, ((DL).rk id).1 < p ∧ ((DL).rk id).2 < p := by
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
  have hTpl : ∀ i ∈ (DL).regs, Rg.R i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p := by
    intro i hi
    obtain ⟨cl, hcl, rfl⟩ := hmemR i hi
    have hcl0 : cl ∈ jCallsP (prims.map Prod.fst) (callsOf (rowsOfT t)) := hcl
    obtain ⟨hc1, hns⟩ := jCallsP_sub _ _ cl hcl0
    exact hRtJ cl.1 (ComplJ8Of.calls_called hgen cl hc1) hns
  have hregp : ∀ i ∈ (DL).regs, i < p := fun i hi => by
    obtain ⟨cl, hcl, rfl⟩ := hmemR i hi; exact hlt cl hcl
  refine ⟨hlay, ComplJ8Jet.hsmall_of_blocks Rt (DL).regs (DL).ids hregp hidsl (fun i hi => (hblk i hi).2) hp,
    ComplJ8Jet.huniq_of_blocks Rt (DL).regs (DL).ids (fun i hi => (hblk i hi).1), hTpl, List.nodup_dedup _, hidx,
    hrk, fun id hid => ?_⟩
  rw [hrc]
  exact ⟨(hrkl id hid).1, (hrkl id hid).2, hidx id hid⟩

/-! ### The census -/

/-- The primitive formula nouns are small: `≤ fuelChip` leaves, every leaf `< p`. -/
theorem primC_census (op : PrimOp) :
    (primC op).leaves ≤ 2 ^ 110 ∧ ∀ v ∈ (primC op).leafList, v < Nock.Atoms.p := by
  cases op <;> exact ⟨by decide, by decide⟩

include hpG in
/-- **`cen_L`**: `hcen'` over the J census of the overlay layout plus the primitive formula nouns. -/
theorem cen_L (hF : DvdOK (DL)) (hC : 0 < (DL).cells.length) (hA : 0 < (DL).acs.length)
    (AV : AVPart p K) (fams : List (List (BadSpec K)))
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots) :
    ∀ x ∈ ClaimJ9.censusGJ9 (honestJ8Of δ b (DL) hF hC hA AV fams).Pb (cJ s f r) ++
        (psRun).map (fun q => primC q.2),
      x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, Nock.Atoms.lenL v ≤ (DL).acs.length + 2 := by
  have hroot : ∀ k : Fin 3, FrameVS.claimNoun (cJ s f r) k ∈ (DD).roots := by
    intro k
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ _
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    fin_cases k <;> simp [FrameVS.claimNoun, cJ]
  have hregR : ∀ id ∈ (DL).regs, Nock.Jet.Autogen.compile p (Rt id) ∈ (DD).roots := by
    intro id hid
    have hidD := regsL_sub Rt hgen prims id hid
    show _ ∈ Nock.V1J8.Gen.rootsOf _ _ ++ ComplJ8Data.jNounsP p Rt _ _
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hidD, rfl⟩))
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · have hxr : x ∈ (DD).roots := by
      simp only [ClaimJ9.censusGJ9, AcceptsJ8P.censusG, List.mem_append, List.mem_map] at hx
      rcases hx with (⟨id, hid, rfl⟩ | ⟨k, -, rfl⟩) | ⟨k, -, rfl⟩
      · exact hregR id hid
      · exact hroot k
      · exact hroot k
    exact ⟨(hleaf _ hxr).trans (by unfold fuelChip; norm_num),
      fun v hv => ComplJ9BOf.lenL_root Rt hgen hpG hxr v hv⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2⟩ := primC_census q.2
    refine ⟨h1.trans (by unfold fuelChip; norm_num), fun v hv => ?_⟩
    have := h2 v hv
    unfold Nock.Atoms.lenL
    simp only [this, ↓reduceIte]
    omega

/-! ### The primitive facts -/

theorem primC_rank (op : PrimOp) :
    (primC op).internal / 2 ^ 62 < 2 ^ 63 ∧ ∃ a c, primC op = .cell a c := by
  cases op <;> exact ⟨by decide, _, _, rfl⟩

include hpG h31 in
/-- **`prims_L`**: the primitive facts of `AcceptsJ9AL` at the called primitives `psRun`. -/
theorem prims_L (hax9 : ProgAxOK9A p t) (hnd : (prims.map Prod.fst).Nodup)
    (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2)) :
    (∀ q ∈ psRun, Rg.R q.1 = some (primSpec q.2)) ∧
    (∀ q ∈ psRun, q.1 ∉ (DL).regs) ∧
    ((psRun).map Prod.fst).Nodup ∧
    (∀ q ∈ psRun, ComplJ9ALData.rkPOf prims q.1 ≠ (0, 0)) ∧
    (∀ q ∈ psRun, (ComplJ9ALData.rkPOf prims q.1).1 < ringChar (ZMod p) ∧
      (ComplJ9ALData.rkPOf prims q.1).2 < ringChar (ZMod p) ∧ (vcRun q.1) < ringChar (ZMod p)) ∧
    (∀ q ∈ psRun, q.1 < p ∧ (vcRun q.1) < p) := by
  have hp63 := p63 (p := p) hpG
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hmemP : ∀ q ∈ psRun, q ∈ prims ∧ q.1 ∈ (J8Data.calls (DA)).map Prod.fst := by
    intro q hq
    simp only [ComplJ9ALData.primsC, List.mem_filter, decide_eq_true_eq] at hq
    exact hq
  have hcells : (DL).cells.length < p := lt_p hpG (h31 _ (memL_cells Rt hgen prims))
  have hne : (J8Data.cells (DA)) ≠ [] := List.ne_nil_of_length_pos (ComplJ9ALData.cellsL_pos Rt prims hgen)
  have hidp : ∀ id, vcRun id < p := fun id =>
    lt_of_lt_of_le (ComplJ8Data.idxOf_lt_of_ne _ _ hne) hcells.le
  refine ⟨fun q hq => hprim q (hmemP q hq).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hreg
    obtain ⟨cl, hcl, e⟩ := regsL_called Rt hgen prims q.1 hreg
    have hcl0 : cl ∈ jCallsP (prims.map Prod.fst) (callsOf (rowsOfT t)) := hcl
    exact (jCallsP_sub _ _ cl hcl0).2 (e ▸ List.mem_map_of_mem (f := Prod.fst) (hmemP q hq).1)
  · have hsub : ((psRun).map Prod.fst).Sublist (prims.map Prod.fst) :=
      List.Sublist.map Prod.fst List.filter_sublist
    exact hnd.sublist hsub
  · intro q _
    exact ComplJ8Of.rk_ne _ (primC_rank _).2
  · intro q hq
    rw [hrc]
    have h1 := (primC_rank (ComplJ9ALData.opOf prims q.1)).1
    have h2 : (primC (ComplJ9ALData.opOf prims q.1)).internal % 2 ^ 62 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
    have h3 : (2 : ℕ) ^ 62 < 2 ^ 63 := by norm_num
    refine ⟨?_, ?_, hidp q.1⟩
    · show (primC (ComplJ9ALData.opOf prims q.1)).internal / 2 ^ 62 < p
      omega
    · show (primC (ComplJ9ALData.opOf prims q.1)).internal % 2 ^ 62 < p
      omega
  · intro q hq
    obtain ⟨cl, hcl, e⟩ := List.mem_map.mp (hmemP q hq).2
    exact ⟨e ▸ calls_lt9 hgen hax9 cl hcl, hidp q.1⟩

/-! ### The lengths -/

include hpG h31 in
/-- **`lengths_L`**: `hlenL`'s `nL + n < p` and `hlenCP`, for an ALU table of `nL ≤ 2^31` rows. -/
theorem lengths_L (hnd : (prims.map Prod.fst).Nodup) (nL : ℕ) (hnL : nL ≤ 2 ^ 31) :
    nL + N9 t < p ∧
    3 + (DL).regs.length + (psRun).length + nL + 2 * (DL).cells.length < p := by
  have hp63 := p63 (p := p) hpG
  have e31 : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
  have hN : N9 t ≤ 2 ^ 31 := h31 _ (memL_N9 Rt hgen prims)
  have hC : (DL).cells.length ≤ 2 ^ 31 := h31 _ (memL_cells Rt hgen prims)
  have hbfs : (bfsForest [t]).length ≤ 2 ^ 31 := h31 _ (memL_bfs Rt hgen prims)
  have hreg : (DL).regs.length ≤ 2 ^ 31 := (regsL_len Rt hgen prims).trans hbfs
  have hps : (psRun).length ≤ 2 ^ 31 := by
    have hsub : ((psRun).map Prod.fst).Sublist (prims.map Prod.fst) := List.Sublist.map Prod.fst List.filter_sublist
    have hnd' : ((psRun).map Prod.fst).Nodup := hnd.sublist hsub
    have hsub2 : (psRun).map Prod.fst ⊆ (J8Data.calls (DA)).map Prod.fst := by
      intro i hi
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
      simp only [ComplJ9ALData.primsC, List.mem_filter, decide_eq_true_eq] at hq
      exact hq.2
    have h1 := (hnd'.subperm hsub2).length_le
    rw [List.length_map, List.length_map] at h1
    have h2 : (J8Data.calls (DA)).length ≤ (bfsForest [t]).length := by
      show (callsOf (rowsOfT t)).length ≤ _
      unfold callsOf rowsOfT
      exact (List.length_filterMap_le _ _).trans (by simp)
    omega
  constructor <;> omega

/-! ### The budget -/

/-- **`bud_genericL`**: `BudJ9AL` at the canonical rows for any ALU layout, and the `hbudV` conjuncts. -/
theorem bud_genericL (Pb : PubJ9AL p) :
    BudJ9AL Pb { toRowsJ9A := rowsA9 Pb.toPubJ9A, AL := Pb.nL }
      (ComplJ8Comp.canonG Pb.toPubJ8 + (rowsA9 Pb.toPubJ9A).N) ∧
    (Pb.regs.length ≤ ComplJ8Comp.canonG Pb.toPubJ8 ∧ Pb.nA ≤ (rowsA9 Pb.toPubJ9A).mb ∧
      Pb.nA ≤ (rowsA9 Pb.toPubJ9A).A ∧ Pb.nV ≤ (rowsA9 Pb.toPubJ9A).AW ∧ Pb.nX ≤ (rowsA9 Pb.toPubJ9A).AX ∧
      Pb.nS ≤ (rowsA9 Pb.toPubJ9A).SP) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [rowsA9, ComplJ8Comp.canonRows, ComplJ8Comp.canonG] <;> omega

end Stat

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALStatic
