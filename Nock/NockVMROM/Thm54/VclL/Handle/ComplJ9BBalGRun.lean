/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BBalGRun.lean

`balG_run9`: the `balG` field of `ComplJ9BOf.OpenJ9B` at the J-9 B honest record `BRun9`, at every `BRun9`-good coin,
  from `complJ9B_closed`'s binders `hpG hax hop5 hRt h31 hwalk hwalkA` (no `hclA`, no corner binder). Clause 3: the compute service public `ρS` is the rows' inc + jet + pair consumes
  (`rhoCS_rows`, `termQX_s`, `sSum_expand`), and
  * the inc consumes total `BRun9`'s atom MI terminal: `ComplJ9BBalG.hI9` at `D9 = j9DataOf` (`incInfoOK_run`,
    `idxOOK_run`: GLA's fixes (A)/(B));

-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BOf
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalG
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalJ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalGRun

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (incT jetT awT pubC)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BOf (BRun9 j9DataOf dvd9 acs9_pos)

noncomputable section

section Run
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)


/-- `ComplJ9BBalF.WA9` and `ComplJ9BBalG.WA9` are definitionally equal. -/
theorem WA9_eq_F (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    ComplJ9BBalF.WA9 δ D χ = ComplJ9BBalG.WA9 δ D χ := rfl

set_option maxHeartbeats 4000000 in
/-- **`OpenJ9B.balG` at `BRun9`**, at every `BRun9`-good coin, from `complJ9B_closed`'s binders. -/
theorem balG_run9 (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads) :
    ∀ χ, (BRun9 δ b Rt hgen hpG h31).Good χ →
      ((BRun9 δ b Rt hgen hpG h31).M χ).ρ 3 +
          (Quad.mk _ (((BRun9 δ b Rt hgen hpG h31).M χ).pubsW WalkHQ.pubXQ)
            (((BRun9 δ b Rt hgen hpG h31).M χ).pubsW (WalkHQ.pubXQ + 1)) +
          Quad.mk _ (((BRun9 δ b Rt hgen hpG h31).M χ).pubsJ 2) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsJ 3)) =
        Quad.mk _ (((BRun9 δ b Rt hgen hpG h31).M χ).pubsC CellHQ.pubHQ)
          (((BRun9 δ b Rt hgen hpG h31).M χ).pubsC (CellHQ.pubHQ + 1)) ∧
      ((BRun9 δ b Rt hgen hpG h31).M χ).ρ 4 =
        Quad.mk _ (((BRun9 δ b Rt hgen hpG h31).M χ).pubsW WalkHQ.pubPQ)
          (((BRun9 δ b Rt hgen hpG h31).M χ).pubsW (WalkHQ.pubPQ + 1)) ∧
      ((BRun9 δ b Rt hgen hpG h31).M χ).ρS +
          ((Nock.Jet.PinJ8.pinCons (p := p) (K := K) (BRun9 δ b Rt hgen hpG h31).Pb.regs
            (BRun9 δ b Rt hgen hpG h31).Pb.idx).map fun x =>
            (FiniteIO.compress (TeleCQ.coinsCV b δ (VerJ8.chalVJ8 b χ))
              (BalanceQ.liftRec (L := 𝕂′) x))⁻¹).sum +
          Quad.mk _ (((BRun9 δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsJ 1) =
        Quad.mk _ (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMI)
            (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMI + 1)) +
          Quad.mk _ (((BRun9 δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubPQ)
            (((BRun9 δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubPQ + 1)) := by
  intro χ hχ
  have hG : (BRun δ b Rt hgen hpG h31).Good χ := ComplJ9BOf.good9_run δ b Rt hgen hpG h31 _ _ χ hχ
  refine ⟨ComplJ8OfBalG.balG1_run δ b Rt hgen hpG hax hop5 hRt h31 hwalk χ,
    ComplJ8OfBalG.balG2_run δ b Rt hgen hpG hax hop5 h31 hwalk χ hG, ?_⟩
  set D := j8DataOf p Rg Rt hgen with hD
  -- ρS as the rows' inc + jet + pair consumes (as `balG3_of`)
  have hg0 : ∀ e ∈ ComplJ8Bad.badOf (ComplJ8Bad.badList [(⟨13, by decide⟩, (bfsForest [D.t]).length)]
      (famsOf δ b D (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen))), χ ∉ e.1 := hG
  have hg : ∀ e ∈ ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [t]) (bfsForest [t]).length,
      χ ∉ e.ev := fun e he =>
    ComplJ8Bad.good_spec hg0 (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_cons_self, he⟩))
  have hS : ((BRun9 δ b Rt hgen hpG h31).M χ).ρS =
      ∑ j ∈ Finset.range (bfsForest [t]).length, (incT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ)
        (pubC δ b Rt hgen χ) j + jetT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j +
        awT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j) := by
    show ComplJ8Comp.ρSCOf δ b D.H D.pd (bfsForest [t]) (ComplJ8.cJ s f r) χ = _
    rw [ComplJ8OfBalG.rhoCS_rows]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ComplJ8OfBalG.termQX_s δ b _ _ _ _ _ j
      (ComplJ8OfBalG.hpair_good δ b _ _ _ _ _ χ hg j (Finset.mem_range.mp hj)), ComplJ8OfBalG.sSum_expand]
  -- the inc consumes: `hI9` at `D9`
  have hmA : (j9DataOf p Rg Rt hgen).acs.length ∈ sizesJ8 (j9DataOf p Rg Rt hgen) := by simp [sizesJ8]
  have hinjA := (powN_ok (orbJ8 _ (dvd9 Rt hgen hpG h31)) (le_two_pow_ht (j9DataOf p Rg Rt hgen) hmA)).1
  have eI : ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ)
        (pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMI)
        (((BRun9 δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMI + 1)) := by
    show _ = Quad.mk _ (pubsAOf δ b (j9DataOf p Rg Rt hgen) (acs9_pos Rt hgen) (orbJ8 _ (dvd9 Rt hgen hpG h31)) χ
        AtomChipHQ.pubMI)
      (pubsAOf δ b (j9DataOf p Rg Rt hgen) (acs9_pos Rt hgen) (orbJ8 _ (dvd9 Rt hgen hpG h31)) χ
        (AtomChipHQ.pubMI + 1))
    have hN := ComplJ8OfAtom.rows_le_of_rows31 Rt hgen h31
    exact ComplJ9BBalG.hI9 δ b Rt hgen hpG hax hop5 hN (j9DataOf p Rg Rt hgen) rfl rfl rfl rfl
      (ComplJ9BBalG.incInfoOK_run Rt hgen hpG hax hop5 hN)
      (ComplJ9BBalG.idxOOK_run Rt hgen hpG hax hop5 hN _) (acs9_pos Rt hgen) _ hinjA χ _
  -- the pair consumes: `hA9` with GLB's provide half
  have hV : Quad.mk _ (((BRun9 δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubPQ)
      (((BRun9 δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubPQ + 1)) =
      (D.preads.map (ComplJ9BBalG.WA9 δ D χ)).sum := by
    rw [← WA9_eq_F]
    exact ComplJ9BBalF.vhP9_total δ b Rt hgen hpG h31 hwalkA χ
  have eA := ComplJ9BBalG.hA9 δ b Rt hgen hpG χ (pubC δ b Rt hgen χ)
    ((BRun9 δ b Rt hgen hpG h31).M χ).pubsV hV
  -- jets, pins, J terminal
  have eJ : ∑ j ∈ Finset.range (bfsForest [t]).length, jetT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ)
        (pubC δ b Rt hgen χ) j +
      ((Nock.Jet.PinJ8.pinCons (p := p) (K := K) (BRun9 δ b Rt hgen hpG h31).Pb.regs
          (BRun9 δ b Rt hgen hpG h31).Pb.idx).map fun x =>
        (FiniteIO.compress (TeleCQ.coinsCV b δ (VerJ8.chalVJ8 b χ)) (BalanceQ.liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((BRun9 δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun9 δ b Rt hgen hpG h31).M χ).pubsJ 1) = 0 :=
    ComplJ8OfBalJ.hJ_run δ b Rt hgen hpG hax hRt h31 χ hG
  rw [hS, Finset.sum_add_distrib, Finset.sum_add_distrib]
  linear_combination eI + eA + eJ

end Run

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalGRun
