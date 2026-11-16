/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8R5.lean

  **The residue-free J-8 bound.**

  * **`linkXU_of_R5`**: `AcceptsJ8'''` + outside `allJ8X` ⇒ `LinkJ8XU` at R4a's real data `RR4` / `LL4`, with NO
    residue: R4a's `linkX_of_R4` derivations, plus `hsA : SmallU` at the reader `rAT` (R3b `smallU_valReader`, from
    the public check `nA ≤ 2^62`, `hservedA` and `ConsumeServedQ` of the #4 export balance) and `hvp` through the
    `SmallU` twin `AtomLeavesUJ8.hvp_of_mbU`.  `hok` is not a field any more: `HokLJ8.acceptsJ8_holdsN_finalL`
    derives it at the variant chip (`hok_of_gatesL`, the ruled gate `isL·c_out = 0`).
  * **`L0d` / `R0d`**: explicit inhabitants of the readout records `Data40J8` / `DataJ8` (empty lists, `h = 0` walk
    data; `R0d.l40 = sum40 L0d`, so `eps40 = epsilon_sum40`).  R4a's statement quantified over arbitrary `R0` / `L0`
    (every field they keep is overwritten by the real readouts or unused by soundness); the final theorem fixes them,
    so no non-statement binder remains and the record types are visibly inhabited.
  * **`probJ8R5_final`**: `Pr_χ[(∃ M, AcceptsJ8''') ∧ ¬ HoldsN c] < 2^-155` with NO `LinkJ8` premise.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
import Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesUJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5

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
open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe realize40 realizeJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
set_option linter.dupNamespace false

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (rowsMJ8 rowsB0 crA)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (censusList2)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z atomTZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_of_ne chalsAJ8Z_ok chalsAJ8Z_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4 (RR4 LL4 hHXV_ofZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)

noncomputable section

/-! ## 1. Inhabitants of the readout records -/

section Default
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  (δ : K) [Fact (¬ IsSquare δ)] {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P : ℕ}

/-- The empty walk data (`h = 0`). -/
def wd0 : WalkVCL.WalkData q (Quad δ) where
  X := []
  lbl := fun _ => ((false, false), ⟨⟨0, 0, 0⟩, 0, ⟨0, 0, 0⟩, 0, 0⟩)
  clab := fun _ _ => ((false, false), ⟨⟨0, 0, 0⟩, 0, ⟨0, 0, 0⟩, 0, 0⟩)
  fo := fun _ => 0
  kroots := 0
  h := 0

/-- A constant compute row. -/
def row0 : LocalVSX.RowVSX :=
  ⟨.s0, (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)⟩

/-- **An inhabitant of `Data40J8`**: empty readouts. -/
def L0d : Data40J8 (q := q) δ Tr St r where
  cRows := fun _ _ => row0
  cH := fun _ => 0
  cH_le := fun _ => Nat.zero_le _
  c_const := fun _ _ _ _ => ⟨rfl, rfl⟩
  rowsD := fun _ => []
  skelD := fun _ => []
  rowsD_le := fun _ => Nat.zero_le _
  skelD_le := fun _ => by simp
  rowsD_const := fun _ _ _ _ => ⟨rfl, rfl⟩
  wdW := fun _ _ => wd0 δ
  wdW_le := fun _ _ => Nat.zero_le _
  wdW_reads := fun _ _ _ _ _ => rfl
  fxReqs := fun _ _ => []
  fxProvs := fun _ _ => []
  fx_reads := fun _ _ _ _ _ => rfl
  vReqs := fun _ _ => []
  vProvs := fun _ _ => []
  v_reads := fun _ _ _ _ _ => rfl
  xReqs := fun _ _ => []
  xProvs := fun _ _ => []
  x_reads := fun _ _ _ _ _ => rfl
  pReqs := fun _ _ => []
  pProvs := fun _ _ => []
  p_reads := fun _ _ _ _ _ => rfl

def R0d : WeightsJ8.DataJ8 (q := q) δ Tr St r P where
  Tr40 := Tr
  St40 := Lift40J8.St40 St
  l40 := Lift40J8.sum40 (L0d (q := q) δ (St := St) (r := r))
  π40 := id
  hπ40 := Lift40J8.hπ40_id St
  eps40 := Lift40J8.epsilon_sum40 _
  valReqs := fun _ _ => []
  valProvs := fun _ _ => []
  val_reads := fun _ _ _ _ _ => rfl
  avReqs := fun _ _ => []
  avProvs := fun _ _ => []
  av_reads := fun _ _ _ _ _ => rfl
  axReqs := fun _ _ => []
  axProvs := fun _ _ => []
  ax_reads := fun _ _ _ _ _ => rfl
  cxReqs := fun _ _ => []
  cxProvs := fun _ _ => []
  cx_reads := fun _ _ _ _ _ => rfl
  svReqs := fun _ _ => []
  svProvs := fun _ _ => []
  sv_reads := fun _ _ _ _ _ => rfl
  rowsA := fun _ => []
  skelA := fun _ => []
  rowsA_le := fun _ => Nat.zero_le _
  skelA_le := fun _ => by simp
  rowsA_const := fun _ _ _ _ => ⟨rfl, rfl⟩
  wdA := fun _ _ => wd0 δ
  wdA_le := fun _ _ => Nat.zero_le _
  wdA_reads := fun _ _ _ _ _ => rfl
  prs := fun _ => []
  prs_le := fun _ => Nat.zero_le _
  prs_const := fun _ _ _ _ => rfl

end Default

/-! ## 2. Every `LinkJ8XU` field derived -/

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- **`LinkJ8XU` at the R4 real data from `AcceptsJ8'''` alone**: every field derived — R4a's `linkX_of_R4` with
`hsA` now DERIVED (`SmallU` at the reader, R3b's `smallU_valReader`, from `nA ≤ 2^62`, `hservedA` and the export
consume `ConsumeServedQ` of the #4 balance), `hvp` through the `SmallU` twin `hvp_of_mbU`, and no `hok` (derived
downstream at the variant chip). -/
theorem linkXU_of_R5 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hpG : p = Nock.Atoms.p) (hr : RowsLe r EncInjJ8.cornerC) (hg : g ≤ 2 ^ 31) (hmax : Pb.nA + 2 ≤ r.maxlen)
    (hacc3 : AcceptsJ8''' δ b Pb Rg c χ M tr r g)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b
      (withLiftC (RR4 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) (LL4 δ b L0 Pb skel hs hL))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
 :
    LinkJ8XU δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr (RR4 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg)
      (LL4 δ b L0 Pb skel hs hL) (rAT b Pb tr) := by
  have hacc' := hacc3.toPP
  have hacc := acceptsJ8Z_of'' δ b hacc'
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp17 : 17 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp64 : 64 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp32 : 2 ^ 32 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq : 2 ^ 63 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hcap := RepriceJ8.hcap_corner32 hr hg hpG
  have hB := hacc'.hbud
  have hΛ : fuelChip ≤ r.Λ := by rw [hr.2.2.2.1]; exact le_refl _
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hout
  set M' := toMsgJ8Z δ b Pb c χ M tr with hM'
  -- L1: the handle balances
  have rX := rdX_realIO δ b (realizeG δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) Pb c χ M' tr
  have rS := rdS_realIO δ b (realizeG δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) Pb c χ M' tr
  have rP := rdP_real40 δ b (realize40 δ b L0 (layPb Pb skel hs) hL) Pb c χ M' tr
  have bX := AcceptsJ8ZB.budX_ofZ δ b Pb c χ M' tr hacc hp17 hB
  have bP := AcceptsJ8ZB.budP_ofZ δ b Pb c χ M' tr hacc hp17 hB
  have bS := AcceptsJ8ZB.budS_ofZ δ b Pb c χ M' tr hacc hp17 hB
  have L2 := AcceptsJ8ZW.linkJ8_L2Z δ b Pb skel hs L0 hL c χ M' tr hacc hp17
  have hx := ListJ8C.hout_x_of_outsideC _ b hoC _ _ rX.1 rX.2 bX.1 bX.2
  have hpp := ListJ8C.hout_p_of_outside40C _ _ b hoC _ _ rP.1 rP.2 bP.1 bP.2
  have hss := ListJ8C.hout_s_of_outsideC _ b hoC _ _ rS.1 rS.2 bS.1 bS.2
  have hcnt := AcceptsJ8ZB.hcount_ofZ δ b Pb c χ M' tr hacc hp17 hB hcap
  -- #2
  have rV := RealVJ8.rdV_view δ b Pb Rg c χ M tr hp17 hacc
  have lV := RealVJ8.valJ8_length δ b Pb c tr χ
  -- the reader at chalsAJ8Z
  have hE := rAT_eq δ b Pb tr (chalsAJ8Z δ χ) M.pubsA
  have hRA : ∀ k : Fin Pb.nA, AtomChipHQ.Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
      (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) k) (rAT b Pb tr k) := by
    rw [← hE]; exact LinkQ2J8.hRA_valReader _
  have hwRA : ∀ j, (rAT (K := K) b Pb tr j).wR ≤ 1 := by
    rw [← hE]; exact LinkQ2J8.hwRA_valReader _ (LinkQ2J8.atom_wR_bool hacc.hsatA)
  have hidxA : ∀ k : Fin Pb.nA, (rAT (K := K) b Pb tr k).idx = k := by
    rw [← hE]; exact ReaderR3bJ8.hidxA_valReader hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hacc.hnpA
  have hBA : AtomChipHQ.LimbsBounded (rAT (K := K) b Pb tr) := by
    rw [← hE]; exact ReaderR3bJ8.hB_valReader hp32 hacc.hsatA
  have hwout : ∀ k, Pb.nA ≤ k → (rAT (K := K) b Pb tr k).wR = 0 := by
    rw [← hE]; exact LinkQ2J8.wR_valReader_out _
  have hTout : ∀ j, Pb.nA ≤ j → (rAT (K := K) b Pb tr j).wR = 0 → (rAT (K := K) b Pb tr j).aR ≠ 0 := by
    rw [← hE]; exact LinkQ2J8.aR_valReader_out _
  -- #3: hservedA
  have hA3 : 3 + 2 * r.A < p := by
    have := hr.2.2.2.2.1; simp only [EncInjJ8.cornerC, corner31] at this
    rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]; omega
  have rAV := RealAJ8.rdAV_view δ b Pb tr (chalsAJ8Z δ χ) M.pubsA
  have hserved := ServedAJ8.hservedA_of_outside
    (withLiftC (RR4 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) (LL4 δ b L0 Pb skel hs hL)) hoC
    hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA (chalsAJ8Z_ok δ χ) hacc'.hvalA0 rAV
    ⟨(RealAJ8.avReqsJ8_length δ b Pb tr).trans (by have := hacc'.hbudV.2.2.1; omega),
      (RealAJ8.avProvsJ8_length δ b Pb tr).le.trans hacc'.hbudV.2.2.1⟩ hA3
  -- #4: houtA
  have rAX := RealAJ8.rdAX_view δ b Pb tr (chalsAJ8Z δ χ) M.pubsA (chalsAJ8Z δ χ) M.pubsV
  have hac : AtomServedQ.acoins δ (chalsAJ8Z δ χ) = AtomServedQ.acoins δ (ProbJ8.chalsAJ8 δ χ) := by
    simp only [AtomServedQ.acoins, chalsAJ8Z_of_ne δ χ (show (33 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (34 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (35 : ℕ) ≠ 37 by decide) (by decide),
      chalsAJ8Z_of_ne δ χ (show (36 : ℕ) ≠ 37 by decide) (by decide)]
  have houtA : ((AtomServedQ.acoins δ (chalsAJ8Z δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8Z δ χ)).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M'.pubsA
          (qA δ b Pb tr (chalsAJ8Z δ χ) M'.pubsA) ++ M'.wreqs).map (BalanceQ.liftRec (K := K) (L := 𝕂′)))
        (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M'.pubsA
          (qA δ b Pb tr (chalsAJ8Z δ χ) M'.pubsA))) := by
    rw [hac]
    refine LinkQ2J8.houtA_of_outside
      (withLiftC (RR4 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) (LL4 δ b L0 Pb skel hs hL)) hoC _ _
      rAX.1 rAX.2 ?_ ?_
    · refine le_trans (le_of_eq (congrArg List.length rAX.1.symm)) ?_
      have := RealAJ8.axReqsJ8_length δ b Pb tr
      have := hacc'.hbudV.2.2.1; have := hacc'.hbudV.2.2.2
      omega
    · refine le_trans (le_of_eq (congrArg List.length rAX.2.symm)) ?_
      rw [RealAJ8.axProvsJ8_length]; exact hacc'.hbudV.2.2.1
  have hcountA := hcountA_ofZ'' δ b Pb c χ M tr hacc'.hlenA
  -- #1.5: hXW
  have hfx := Lift40J8.fpx_out (LL4 δ b L0 Pb skel hs hL) (ListJ8C.outside40C _ _ hoC)
    (by show (RealVJ8.fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr).length ≤ r.W
        rw [RealVJ8.fxReqsJ8, walkXInternal_length]; exact hL.W)
    (by show (RealVJ8.fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr).length ≤ 2 * r.D
        rw [RealVJ8.fxProvsJ8, liftWts_length]
        exact (cXRec_length δ b _ _ _ _ _).trans (by have := hB.x2; omega))
  have hXW := RealVJ8.hXW_of_io δ b Pb c χ M' tr hacc hp64
    (by show Quad.mk _ (M.pubsC 2) (M.pubsC 3) = Quad.mk _ (M.pubsW 0) (M.pubsW 1)
        rw [hacc'.hfxC.1, hacc'.hfxC.2]) hfx
  -- the census
  have hG : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M' tr).map (·.b0))
      (AtomBigJ8.extB p (rAT b Pb tr)) ++ censusG Pb c),
      pr ∈ (RR4 δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg).D.prs tr := by
    intro pr hpr
    show pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 (TraceJ8.rowsMJ8 Pb.nodesC Pb.orbitC tr) (extT8 b Pb tr) ++
      censusG Pb c)
    rw [rowsMJ8_eq_cellT δ b Pb χ M' tr]
    exact hpr
  have hext := LinkQ2J8.hext_of_rows (q := p) hBA hwout hmax
  have hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0 := by
    rw [chalsAJ8Z_of_ne δ χ (by omega) (by omega), chalsAJ8Z_of_ne δ χ (by omega) (by omega)]
    exact (outJ8_of_outside _ _ b hoC).atom_hz
  -- S1: `SmallU` at the reader (R3b), from the export consume of the #4 balance
  have hcs := AtomServedQ.consumeServedQ_of_balance δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M'.pubsA _
    hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA M'.wreqs hacc.hbalA houtA hcountA
  have hsU : ∀ k : Fin Pb.nA, SmallU (rAT (K := K) b Pb tr k) := by
    rw [← hE]
    exact ReaderR3bJ8.smallU_valReader hq hacc'.hnA62 hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hserved hcs
  have hvp := AtomLeavesUJ8.hvp_of_mbU χ hq hpG hacc.hsatA hacc.hbindA hacc.hinjA hacc.hadjA hacc.hnpA hy
    hserved hRA hsU hidxA hBA (fun k => hwRA k) hTout
  exact
    { rdX := rX
      budX := ⟨(congrArg List.length rX.1).le.trans bX.1, (congrArg List.length rX.2).le.trans bX.2⟩
      rdP := rP
      budP := ⟨(congrArg List.length rP.1).le.trans bP.1, (congrArg List.length rP.2).le.trans bP.2⟩
      rdS := rS
      budS := ⟨(congrArg List.length rS.1).le.trans bS.1, (congrArg List.length rS.2).le.trans bS.2⟩
      hcount := hcnt
      rdV := rV
      budV := ⟨lV.1.trans (by have := hacc'.hbudV.1; have := hB.x2; omega),
        lV.2.trans (by have := hacc'.hbudV.2.1; have := hB.x2; omega)⟩
      rdWC := L2.1
      rdWW := L2.2
      hext := hext
      hprs := fun pr hpr => hG pr (censusPairs_append_mem hpr)
      hvp := hvp
      hXW := hXW
      hHXW := AcceptsJ8ZH.hHXW_of_acceptsZ δ b Pb c χ M' tr hacc hp64 hx hpp hss (hcnt .x)
      hRA := hRA
      hsA := hsU
      hidxA := hidxA
      hrn := by rw [← hE]; exact LinkQ2J8.hrn_valReader _
      hB := hBA
      hwRA := hwRA
      houtA := houtA
      hservedA := hserved
      hseedsV := AcceptsJ8ZS.hseedsV_of_outsideZ δ b _ Pb χ M' tr hoC
        (AcceptsJ8ZS.rowsAJ8_eq_atomTZ δ b Pb χ M' tr) hΛ
      hHXV := hHXV_ofZ δ b Pb c χ M' tr hacc rfl houtA hcountA
      hprsG := hG }

/-! ## 3. THE FINAL theorem -/

/-- The public layout bound `LayLe` at the empty skeleton, from the five public table sizes. -/
theorem layLe_of (Pb : PubJ8 p) (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A)
    (hLV : Pb.nV ≤ r.AW) : LayLe (layPb Pb [] (by simp)) r :=
  ⟨hLC, hLM, hLW, hLA, hLV⟩

open Classical in
/-- **THE residue-free J-8 bound.**  For every staged prover trace map `Q`, at the census corner:
`Pr_χ[(∃ M, AcceptsJ8''' … (Q χ) r g) ∧ ¬ HoldsN c] < 2^-155`, with NO `LinkJ8` premise — only statement binders:
the field pin (`hpG`, `hcK`), the corner / maxlen / leaves / registered-id / layout / census binders (`hr`, `hqM`,
`hk`, `hmax`, `hg`, `hLC … hLV`, `hnM`, `hreg`) and the faithful registry (`hRg`). -/
theorem probJ8R5_final [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ8''' δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  RepriceJ8.probJ8X_lt_155_census32
    (AtomFpxJ8.withFpxV δ b
      (withLiftC (RR4 δ b (g := g + r.N) (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
          Pb c [] (by simp) (layLe_of Pb hLC hLM hLW hLA hLV) rfl hnM hreg)
        (LL4 δ b (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb [] (by simp)
          (layLe_of Pb hLC hLM hLW hLA hLV)))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA) Q hQ _ _
    (fun χ hacc hout => by
      obtain ⟨M, hM⟩ := hacc
      exact hsoundJ8XU δ b Pb hRg c χ M (Q χ) _ _ hpG hqM hk hM hout hM.toPP.hbudV.2.2.2 hM.toPP.hbudV.2.2.1
        (wdV_view δ b Pb (Q χ) _ _)
        (linkXU_of_R5 δ b Pb c χ M (Q χ) _ _ [] (by simp) (layLe_of Pb hLC hLM hLW hLA hLV) rfl hnM hreg hpG hr
          hg hmax hM hout))
    hcK hr (le_refl _) (RepriceJ8.g32_of_corner hr hg)

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5
