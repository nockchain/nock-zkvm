/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/IOJ9A.lean

* `reqsJ9_eqA`: S8's request lists `reqsJ9 … (qX9 …) extAC` are `RR49A.reqsA` at `gA := axOn` (any coins / publics).
  * **`ioA`**: outside `allJ8C (withLiftCA R L C)` (any data whose x / s / p readouts are the `RR49A` lists, rows
    `rowsB r`, id parameter `g + N + AX`), at an `AcceptsJ9A`-accepted trace: S8's `hout` (x, p), `houtS`, `hcount`
    (the budgets are `BudLenJ9A`'s, the caps `hcap` a parameter).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HbalJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.Out40J9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.BudLenJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.IOJ9A

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (liftP)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A (CW9 withLiftCA)
open Nock.NockVMROM.Thm54.VclL.Handle.Out40J9A (OutJ9A outJ9A_of_outside)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AcceptsJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.HbalJ9A (extAC provsAC extAC_eq provsAC_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.FibreJ8 (effP)

noncomputable section

section IO
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem reqsJ9_eqA (Pb : PubJ9A p) (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p))
    (chalV pv : ℕ → ZMod p) (bl : Bal) :
    TeleX9.reqsJ9 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalV) (pubVal := pv)
      (orbit := Pb.orbit) (P := qX9 δ b Pb tr chalV pv) (extAC δ b Pb χ M tr) bl =
      RR49A.reqsA δ b Pb.axOn Pb tr bl := by
  unfold TeleX9.reqsJ9 RR49A.reqsA
  rw [extAC_eq δ b Pb χ M tr bl]
  exact congrArg (fun l => (l ++ RR49A.extA b Pb.axOn Pb tr bl).map (BalanceQ.liftRec (L := 𝕂′)))
    (CompReqsX9.compReqsX9_eq_of9 Pb tr chalV pv bl)

/-- **S8's compute IO events and counts, from the bundle.** -/
theorem ioA {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} {r : RowsJ9A} {g P : ℕ}
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A (RR49A.rowsB r) P
      (g + r.N + r.AX))
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A (RR49A.rowsB r))
    (C : CW9 (K := K) (TrJ9A (ZMod p)) StJ9A (RR49A.rowsB r))
    (hRx : R.D.cxReqs tr χ = RR49A.reqsA δ b Pb.axOn Pb tr .x ∧
      R.D.cxProvs tr χ = liftP (RR49A.provsA b Pb.axOn Pb.spOn Pb tr .x))
    (hRs : R.D.svReqs tr χ = RR49A.reqsA δ b Pb.axOn Pb tr .s ∧
      R.D.svProvs tr χ = effP (liftP (RR49A.provsA b Pb.axOn Pb.spOn Pb tr .s)))
    (hLp : L.pReqs tr (toVSQ χ) = RR49A.reqsA δ b Pb.axOn Pb tr .p ∧
      L.pProvs tr (toVSQ χ) = liftP (RR49A.provsA b Pb.axOn Pb.spOn Pb tr .p))
    (hout : ∀ s ∈ allJ8C (withLiftCA R L C), ¬ s.mem tr χ)
    (hacc : AcceptsJ9A δ b Pb Rg c χ M tr r g) (hp : 20 < p)
    (hcap : 3 * (RR49A.rowsB r).N + (RR49A.rowsB r).W + (RR49A.rowsB r).rd < p ∧
      2 * (RR49A.rowsB r).N < p ∧ (RR49A.rowsB r).N + 2 * (RR49A.rowsB r).J + (g + r.N + r.AX) < p) :
    (∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (TeleX9.reqsJ9 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) (extAC δ b Pb χ M tr) bl)
        (liftP (provsAC δ b Pb χ M tr bl))) ∧
    (((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (TeleX9.reqsJ9 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) (extAC δ b Pb χ M tr) .s)
        (effP (liftP (provsAC δ b Pb χ M tr .s)))) ∧
    (∀ bl, (TeleX9.reqsJ9 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ9 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
        (P := qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ)) (extAC δ b Pb χ M tr) bl).length < p) := by
  have O := outJ9A_of_outside R L C b hout
  have hB := hacc.hbud
  have hsat := hacc.hsatX
  have hx := O.hout_x
  rw [show (withLiftCA R L C).D.cxReqs tr χ = _ from hRx.1, show (withLiftCA R L C).D.cxProvs tr χ = _ from hRx.2]
    at hx
  have hs := O.hout_s
  rw [show (withLiftCA R L C).D.svReqs tr χ = _ from hRs.1, show (withLiftCA R L C).D.svProvs tr χ = _ from hRs.2]
    at hs
  have hpp := O.hout_p
  rw [hLp.1, hLp.2] at hpp
  have hx' := hx (BudLenJ9A.reqsA_x_le δ b hp hB _ _ _ hsat) (BudLenJ9A.provsA_x_le δ b hB _ _)
  have hs' := hs (BudLenJ9A.reqsA_s_le δ b hp hB _ _ _ hsat) (BudLenJ9A.provsA_s_le δ b hB _ _)
  have hp' := hpp (BudLenJ9A.reqsA_p_le δ b hp hB _ _ _ hsat) (BudLenJ9A.provsA_p_le δ b hB _ _)
  have hc := BudLenJ9A.hcountA9 δ b hp hB Pb.axOn _ _ hsat hcap
  refine ⟨fun bl hbl => ?_, ?_, fun bl => ?_⟩
  · rw [reqsJ9_eqA, provsAC_eq]
    cases bl with
    | x => exact hx'
    | p => exact hp'
    | s => exact absurd rfl hbl
  · rw [reqsJ9_eqA, provsAC_eq]
    exact hs'
  · rw [reqsJ9_eqA]
    exact hc bl

end IO

end

end Nock.NockVMROM.Thm54.VclL.Handle.IOJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.IOJ9A
#print axioms reqsJ9_eqA
#print axioms ioA
end Axioms
