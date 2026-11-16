/-
  Nock/NockVMROM/Thm54/VclL/Handle/ServedAJ8.lean

  **`hservedA` from `hvalA0`.**

  The atom table's validity accumulator has NO external provider and NO external request; R1's `AcceptsJ8'` checks
  its terminal `pubsA 0/1 = 0` (`hvalA0`, Q2 S3).  So the atom table is the cell table's single-provider case at
  `reqs = []` (`Telescope.cell_validityServed` on the restricted cell chip):

  * **`atom_valid_out_of_outside`**: outside summand #3 (`atomValidity`), within its budgets, the validity pair
    `(γ′, ρ′)` is outside `IOFailureEventW` of the `avReqs / avProvs` readouts;
  * **`servedA_of_valid`**: at any atom vector carrying the validity coins (`ChalsOK … γ′ ρ′ 11`), the terminal
    `pubsA 0/1 = 0` and the pair outside the event of the atom table's own lists, `ValidityServed` holds;
  * **`hservedA_of_outside`**: the `LinkJ8` field `hservedA` from outside `allJ8C`, the readout of #3 at the
    atom table's lists (`rdAV`, the same class as `rdV`), its budget and `hvalA0`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesZJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ServedAJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (pair_notMem_of_io)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (atomChipHQ)

noncomputable section

/-! ## 1. Summand #3 -/

section Out
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P : ℕ}

/-- **Outside summand #3, within its budgets**: the validity pair is outside the atom table's IO event. -/
theorem atom_valid_out_of_outside (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ sumJ8 R .atomValidity, ¬ s.mem tr χ)
    (h1 : (R.avReqs tr χ).length ≤ 3 + 2 * r.A) (h2 : (R.avProvs tr χ).length ≤ r.A) :
    (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.avReqs tr χ) (R.avProvs tr χ) := by
  have hs := h
  simp only [sumJ8, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at hs
  exact pair_notMem_of_io _ _ _ St _ _ _ _ _ hs h1 h2

end Out

/-! ## 2. `ValidityServed` on the atom table -/

section Served
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
  (chalsA pubsA : ℕ → K)
  (QA : Fin (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "QR" => AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA

variable {δ b hnA nodesA orbitA chalsA pubsA QA} in
/-- **`ValidityServed` on the atom table from its zero terminal**: no external request, terminal `pubsA 0/1 = 0`,
the validity pair outside the event of the table's own lists. -/
theorem servedA_of_valid [CharP 𝕂′ p]
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (γ ρ : 𝕂′) (hok : ChalsOK δ chalsA γ ρ 11)
    (hval0 : pubsA 0 = 0 ∧ pubsA 1 = 0)
    (hout : (γ, ρ) ∉ IOFailureEventW (cellVInternal δ b hnA nodesA orbitA chalsA pubsA QR)
      (SVFrame.liftWts (cellVRecords δ b hnA nodesA orbitA chalsA pubsA QR)))
    (hcount : (cellVInternal δ b hnA nodesA orbitA chalsA pubsA QR).length < p) :
    ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA QR) := by
  rw [mem_IOFailureEventW_iff, not_or, not_or] at hout
  refine cell_validityServed δ b hnA nodesA orbitA chalsA pubsA QR
    (AtomChipHQ.atomChipHQ_restrict_cell_sat δ b hnA nodesA orbitA chalsA pubsA QA hsat)
    (AtomChipHQ.atomChipHQ_restrict_bind δ b hnA nodesA orbitA chalsA pubsA QA hbind) hinj hadj γ ρ hok
    (p := p) [] ?_ (by simp) ?_ ?_ (by simpa using hcount)
  · rw [hval0.1, hval0.2]; simp [Quad.mk_zero']
  · simpa using hout.1
  · simpa using hout.2.2

end Served

/-! ## 3. The `LinkJ8` field -/

section Link
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K}
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}
  {QA : Fin (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "QR" => AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA

/-- **`hservedA`** (the `LinkJ8` field): outside `allJ8C`, at the readout `rdAV` of summand #3 (the atom table's
internal consumes and its row provides), its budget, the verifier check `hvalA0` and `3 + 2A < p`. -/
theorem hservedA_of_outside [CharP 𝕂′ p] (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hok : ChalsOK δ chalsA (Quad.mk _ (χ c4) (χ c6)) (Quad.mk _ (χ c5) (χ c7)) 11)
    (hvalA0 : pubsA 0 = 0 ∧ pubsA 1 = 0)
    (rdAV : R.D.avReqs tr χ = cellVInternal δ b hnA nodesA orbitA chalsA pubsA QR ∧
      R.D.avProvs tr χ = SVFrame.liftWts (cellVRecords δ b hnA nodesA orbitA chalsA pubsA QR))
    (budAV : (R.D.avReqs tr χ).length ≤ 3 + 2 * r.A ∧ (R.D.avProvs tr χ).length ≤ r.A)
    (hA : 3 + 2 * r.A < p) :
    ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA QR) := by
  have h3 := outside_sumJ8_D R h .atomValidity (by decide) (by decide) (by decide)
  have hout := atom_valid_out_of_outside R.D h3 budAV.1 budAV.2
  rw [rdAV.1, rdAV.2] at hout
  have hcnt : (cellVInternal δ b hnA nodesA orbitA chalsA pubsA QR).length < p := by
    rw [← rdAV.1]; omega
  exact servedA_of_valid hsat hbind hinj hadj _ _ hok hvalA0 hout hcnt

end Link

end

end Nock.NockVMROM.Thm54.VclL.Handle.ServedAJ8
