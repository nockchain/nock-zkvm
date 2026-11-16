/-
  Nock/V1J8/FastStatic.lean

  **Injectivity of the row nodes in O(n) expected, not O(n^2).**  `injB nodes = decide (Injective nodes)`
  tests every pair (each node a `Gold.pow`).  `injBF` inserts the `ZMod.val`s into a hash set and fails at the first
  repeat; `injBF_eq : injBF nodes = injB nodes` for prime moduli.  `checkStaticJ8F` is `checkStaticJ8` with
  `injBF`; `checkStaticJ8F_eq` is kernel-checked.  `nodupB` (the J and atom-walk chips' node check) gets the same
  treatment (`nodupBF`, csimp).
-/
import Nock.V1J8.Static
import Nock.V1J8.MemJAW
import Std.Data.HashSet

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8

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
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V

namespace FastInj

def injGo {α : Type} (f : α → ℕ) : List α → Std.HashSet ℕ → Bool
  | [], _ => true
  | i :: l, s => if s.contains (f i) then false else injGo f l (s.insert (f i))

theorem injGo_iff {α : Type} (f : α → ℕ) (l : List α) (s : Std.HashSet ℕ) :
    injGo f l s = true ↔ (l.map f).Nodup ∧ ∀ i ∈ l, s.contains (f i) = false := by
  induction l generalizing s with
  | nil => simp [injGo]
  | cons i l ih =>
    by_cases h : s.contains (f i) = true
    · have : injGo f (i :: l) s = false := by simp [injGo, h]
      rw [this]
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ hall
      have := hall i (List.mem_cons_self ..)
      rw [h] at this
      exact absurd this (by simp)
    · have h' : s.contains (f i) = false := by simpa using h
      have e : injGo f (i :: l) s = injGo f l (s.insert (f i)) := by simp [injGo, h']
      rw [e, ih]
      simp only [List.map_cons, List.nodup_cons, List.forall_mem_cons, Std.HashSet.contains_insert,
        Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.mem_map, h']
      constructor
      · rintro ⟨hn, hj⟩
        refine ⟨⟨?_, hn⟩, trivial, fun j hj' => (hj j hj').2⟩
        rintro ⟨a, ha, hfa⟩
        exact (hj a ha).1 hfa.symm
      · rintro ⟨⟨hn1, hn⟩, _, hj⟩
        refine ⟨hn, fun j hj' => ⟨?_, hj j hj'⟩⟩
        intro hfj
        exact hn1 ⟨j, hj', hfj.symm⟩


def injBF {p n : ℕ} (nodes : Fin n → ZMod p) : Bool :=
  injGo (fun i => (nodes i).val) (List.finRange n) {}

theorem injBF_iff {p n : ℕ} [NeZero p] (nodes : Fin n → ZMod p) : injBF nodes = true ↔ Function.Injective nodes := by
  rw [injBF, injGo_iff]
  simp only [Std.HashSet.contains_empty, implies_true, and_true]
  rw [List.nodup_map_iff_inj_on (List.nodup_finRange n)]
  constructor
  · intro h a b hab
    exact h a (List.mem_finRange a) b (List.mem_finRange b) (by rw [hab])
  · intro h a _ b _ hab
    exact h (ZMod.val_injective p hab)

theorem injBF_eq {p n : ℕ} [NeZero p] (nodes : Fin n → ZMod p) : injBF nodes = injB nodes :=
  Bool.eq_iff_iff.mpr ((injBF_iff nodes).trans (injB_iff nodes).symm)

end FastInj

section Static
variable {p : ℕ} [Fact p.Prime]

open FastInj

def checkStaticJ8F (Pb : PubJ8 p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ8) (g : ℕ) : Bool :=
  injBF Pb.nodes && adjB Pb.nodes Pb.orbit.ω &&
  injBF Pb.nodesC && adjB Pb.nodesC Pb.orbitC.ω && decide (Pb.nC < p) &&
  injBF Pb.nodesW && adjB Pb.nodesW Pb.orbitW.ω && decide (1 ≤ Pb.kroots) && decide (Pb.kroots ≤ Pb.nW) &&
    decide (Pb.kroots + Pb.nW < p) &&
  injBF Pb.nodesA && adjB Pb.nodesA Pb.orbitA.ω && decide (Pb.nA < p) &&
  decide (List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids) &&
  decide (∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) &&
  decide (((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup) &&
  decide (∀ i ∈ Pb.regs, axPosB (Pb.Rt i) = true) &&
  decide Pb.regs.Nodup &&
  decide (∀ id ∈ Pb.regs, Pb.idx id < p) &&
  decide (∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)) &&
  decide (∀ id ∈ Pb.regs, (Pb.rk id).1 < p ∧ (Pb.rk id).2 < p ∧ Pb.idx id < p) &&
  decide (∀ k : Fin 3, atomLtB p (claimNoun c k) = true) &&
  decide (∀ k : Fin 3, isCellN (claimNoun c k) = true → (m k).1 < p) &&
  decide (∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p) &&
  decide (∀ x ∈ censusG Pb c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < p) &&
  decide (3 + Pb.regs.length + 2 * Pb.nC < p) &&
  decide (Pb.nA + Pb.nV < p) &&
  isCellN c.formula &&
  decide (Pb.nA ≤ 2 ^ 62) &&
  budB Pb r (g + r.N) &&
  decide (Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW)

theorem checkStaticJ8F_eq (Pb : PubJ8 p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ8) (g : ℕ) :
    checkStaticJ8F Pb c m r g = checkStaticJ8 Pb c m r g := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp only [checkStaticJ8F, checkStaticJ8, injBF_eq]

end Static

/-- `nodupB` through the hash set. -/
def nodupBF {n : ℕ} (T : MemX.TabM n) : Bool := FastInj.injBF T.nodes

theorem nodupB_eq_F : @MemX.nodupB = @nodupBF := by
  funext n T
  haveI : NeZero Nock.Field.p := ⟨by have := Nock.Field.p_eq; omega⟩
  exact Bool.eq_iff_iff.mpr ((MemX.nodupB_iff T).trans (FastInj.injBF_iff T.nodes).symm)

attribute [csimp] nodupB_eq_F

end Nock.V1J8
