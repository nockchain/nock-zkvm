/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8Static.lean

  **The verifier's STATIC checks of `AcceptsJ8''''` at the claim
  `c0 = *[[0 0] [0 1]] = [0 0]` with the empty registry and no J row.**

  * Claim checks: `hcellF0`, `hclA0` (no claim noun is an atom), `hclR0` (rank high limbs `0`), `hcen0` (the census
    of the registered formulas and the claim cells: leaves `≤ 2 ≤ fuelChip`, every leaf `< p`).
  * `hbud0`: `BudJ8` at `regs = ids = []`, `nJ = 0`, `nV = 0`-free (the atom-walk term enters as `2 * Pb.nV`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static

open Nock Nock.Noun Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (claimCells censusG rkC)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN)
open Nock.Jet.ChipJ8 (layoutJ8 tvKey axPosB PRow)
open Polynomial Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

/-! ## 1. The claim checks -/

theorem claimNoun_c0 (k : Fin 3) : claimNoun c0 k = if k = 1 then f0 else s0 := by
  fin_cases k <;> rfl

theorem hcellF0 : isCellN c0.formula = true := rfl

theorem isCell_c0 (k : Fin 3) : isCellN (claimNoun c0 k) = true := by
  rw [claimNoun_c0]; split_ifs <;> rfl

theorem hclA0 (p : ℕ) : ∀ k : Fin 3, ∀ v, claimNoun c0 k = .atom v → v < p := by
  intro k v h
  have := isCell_c0 k
  rw [h] at this
  exact absurd this (by simp [isCellN])

theorem internal_c0 (k : Fin 3) : (claimNoun c0 k).internal = 1 := by
  rw [claimNoun_c0]; split_ifs <;> rfl

theorem hclR0 (p : ℕ) (hp : 0 < p) : ∀ k : Fin 3, isCellN (claimNoun c0 k) = true →
    (claimNoun c0 k).internal / 2 ^ 62 < p := by
  intro k _
  rw [internal_c0]; simpa using hp

theorem claimCells_c0 : claimCells c0 = [0, 1, 2] := by
  unfold claimCells
  simp [List.finRange, List.filter, isCell_c0]

theorem claimMap_c0 : (claimCells c0).map (claimNoun c0) = [s0, f0, s0] := by
  rw [claimCells_c0]; rfl

section Pub
variable {p : ℕ} [Fact p.Prime]

theorem censusG_c0 (Pb : PubJ8 p) (hreg : Pb.regs = []) : censusG Pb c0 = [s0, f0, s0] := by
  unfold censusG; rw [hreg, claimMap_c0]; rfl

theorem hcen0 (Pb : PubJ8 p) (hreg : Pb.regs = []) (hp : 2 ≤ p) :
    ∀ x ∈ censusG Pb c0, x.leaves ≤ VclL.fuelChip ∧ ∀ v ∈ x.leafList, v < p := by
  rw [censusG_c0 Pb hreg]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  have hf : (VclL.fuelChip : ℕ) = 2 ^ 110 := rfl
  rcases hx with rfl | rfl | rfl <;> refine ⟨by rw [hf]; decide, ?_⟩ <;>
    simp [s0, f0, Noun.leafList] <;> omega

/-! ## 2. The J chip absent and the registry checks at `regs = ids = []` -/

theorem layout_nil (Rt : ℕ → Nock.Jet.Autogen.Tpl) : layoutJ8 Rt [] [] = [] := by
  simp [layoutJ8, Nock.Jet.ChipJ8.blocks]

theorem hlay0 (Pb : PubJ8 p) (hreg : Pb.regs = []) (hids : Pb.ids = []) (hJ0 : Pb.nJ = 0) :
    List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids := by
  rw [hreg, hids, layout_nil]
  exact List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, hJ0])

theorem hsmall0 (Pb : PubJ8 p) (hreg : Pb.regs = []) (hids : Pb.ids = []) :
    ∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p := by
  rw [hreg, hids, layout_nil]; simp

theorem huniq0 (Pb : PubJ8 p) (hreg : Pb.regs = []) (hids : Pb.ids = []) :
    ((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup := by
  rw [hreg, hids, layout_nil]; simp

variable {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]

theorem jchip_absent (δ : ZMod p) (b : Module.Basis (Fin 3) (ZMod p) K) {hJ nJ : ℕ}
    (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (chalsJ pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (Nock.Jet.ChipJ8.jetChipJ8 δ b nodesJ orbitJ chalsJ pubsJ lay).rap.w → (ZMod p)[X])
    (h0 : nJ = 0) (hp : pubsJ 0 = 0 ∧ pubsJ 1 = 0 ∧ pubsJ 2 = 0 ∧ pubsJ 3 = 0) :
    JGenJ8.JChipOK δ b nodesJ orbitJ chalsJ pubsJ lay PJ :=
  Or.inr ⟨h0, hp⟩

theorem regs_vacuous {P : ℕ → Prop} (Pb : PubJ8 p) (hreg : Pb.regs = []) : ∀ i ∈ Pb.regs, P i := by
  rw [hreg]; simp

theorem hnd0 (Pb : PubJ8 p) (hreg : Pb.regs = []) : Pb.regs.Nodup := by rw [hreg]; simp

/-! ## 3. The public budget -/

theorem jCount_nil {n : ℕ} (es : List (Nock.Jet.ChipJ8.Kd × List Nock.Jet.ChipJ8.KE)) (lay : Fin n → PRow)
    (h0 : n = 0) : RealIOJ8.jCount es lay = 0 := by
  subst h0; simp [RealIOJ8.jCount]

theorem hbud0 (Pb : PubJ8 p) (r : RowsJ8) (g : ℕ) (hreg : Pb.regs = []) (hJ0 : Pb.nJ = 0)
    (h1 : 3 * Pb.n + Pb.nW ≤ 3 * r.N + r.W + r.rd) (h2 : Pb.nC ≤ r.D) (h3 : Pb.n ≤ r.N) (h4 : Pb.nW ≤ r.W)
    (h5 : 2 * Pb.n ≤ r.N + 2 * r.J + g) (h6 : Pb.nA + 2 * Pb.nV ≤ r.calls + r.heads + r.blocks + r.J) :
    RealIOJ8.BudJ8 Pb r g where
  x1 := by rw [jCount_nil _ _ hJ0]; simpa using h1
  x2 := h2
  p1 := h3
  p2 := h4
  s1 := by rw [jCount_nil _ _ hJ0, jCount_nil _ _ hJ0, hreg]; simpa using h5
  s2 := by rw [jCount_nil _ _ hJ0, jCount_nil _ _ hJ0]; simpa using h6

end Pub

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static
