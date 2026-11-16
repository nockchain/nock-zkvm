/-
  Nock/NockVMROM/Thm54/VclL/Handle/WeightsJ8M.lean

  **FinalJ8's `hout.s` from the merged service summand.**
  New module, additive.

  * `outside_sv`: outside `allJ8 R`, outside the merged service summand;
  * **`hout_s_of_outside`**: if `R.svReqs / R.svProvs` at `(tr, χ)` are the `s` balance's lists (`reqsJ8 … ext.s`,
    `liftP (provs.s)`) and fit the merged budgets, the compute coins `coinsCV (chalVJ8 b χ)` are outside
    `IOFailureEventW` of them — FinalJ8's `hout.s`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8M

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8)

noncomputable section

section HoutS
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem hout_s_of_outside (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P)
    (b : Module.Basis (Fin 3) (ZMod p) K) {tr : Tr} {χ : Coins frameJ8 K}
    (h : ∀ s ∈ sumJ8 R .service, ¬ s.mem tr χ)
    (rs : List (Fin 8 → 𝕂′)) (ps : List ((Fin 8 → 𝕂′) × 𝕂′))
    (hr : R.svReqs tr χ = rs) (hp : R.svProvs tr χ = ps)
    (h1 : rs.length ≤ r.N + 2 * r.J) (h2 : ps.length ≤ r.calls + r.heads + r.blocks + r.J) :
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW rs ps := by
  have hs := h
  simp only [sumJ8, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at hs
  subst hr hp
  exact hout_of_specH b _ _ _ _ _ hs h1 h2

/-- The same, from outside the whole J-8 list. -/
theorem hout_s_of_outside_all (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P)
    (b : Module.Basis (Fin 3) (ZMod p) K) {tr : Tr} {χ : Coins frameJ8 K}
    (h : ∀ s ∈ allJ8 R, ¬ s.mem tr χ)
    (rs : List (Fin 8 → 𝕂′)) (ps : List ((Fin 8 → 𝕂′) × 𝕂′))
    (hr : R.svReqs tr χ = rs) (hp : R.svProvs tr χ = ps)
    (h1 : rs.length ≤ r.N + 2 * r.J) (h2 : ps.length ≤ r.calls + r.heads + r.blocks + r.J) :
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW rs ps :=
  hout_s_of_outside R b (outside_sumJ8 R h .service) rs ps hr hp h1 h2

end HoutS

end

end Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8M
