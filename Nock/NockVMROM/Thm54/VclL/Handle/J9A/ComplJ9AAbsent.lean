/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AAbsent.lean

Absent chips still carry one dummy row each
  (`nX = nS = 1`: `hnX hnS : 0 < ·`), charged to the budget by `rowsA` (`N + 1`, `AX = SP = 1`).

  * `pubA` / `msgA` / `trA` / `rowsA`: the J-9 A record of a J-8 one (absent chips).
  * `acceptsA_of_V`: `AcceptsJ9V → AcceptsJ9A` at the lifted record (only `RowsLe31` and `2^63 < p` added).
  * `stA_of_st`: `StJ8 → StJ9A` at the lifted traces.
  * **`complJ9A_closed_absent`**: the exact `complJ9B_closed` shape at `AcceptsJ9A`, with `axOn = spOn = false`.

  Scope (U, argued, not kernel-checked): J-9 B's `hax` (formula axes `< p` on `s0`/`s9`/`s10` rows) and `hwalk`
  (read depths `≤ 61`) exclude every big (kind-2) and every field (`≥ 2^62`) axis, so on J-9 B's hypotheses the axis
  and split chips are never needed; the present regime needs a J-9 A generator.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AComp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsent

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crC crM crW crJ crA)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8 ProgAxOK ProgOp5OK RowsLe31)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BOf
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (BudJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V (AcceptsJ9V)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AComp (emb9)

noncomputable section

/-! ## 1. The J-9 A record of a J-8 one (absent chips) -/

section Lift
variable {p : ℕ} [Fact p.Prime]

/-- The public layout with both new chips ABSENT (`axOn = spOn = false`) on one dummy row each. -/
def pubA (Pb : PubJ8 p) : PubJ9A p :=
  { toPubJ8 := Pb, hX := Pb.h, nX := 1, hnX := Nat.one_pos, nodesX := fun _ => Pb.nodes ⟨0, Pb.hn⟩,
    orbitX := Pb.orbit, hS := Pb.h, nS := 1, hnS := Nat.one_pos, nodesS := fun _ => Pb.nodes ⟨0, Pb.hn⟩,
    orbitS := Pb.orbit, axOn := false, spOn := false }

/-- The message with zero axis / split publics. -/
def msgA {K : Type} [Field K] [Algebra (ZMod p) K] {δ : ZMod p} (M : MsgJ8' p K δ) : MsgJ9A' p K δ :=
  { toMsgJ8' := M, pubsX := fun _ => 0, pubsS := fun _ => 0 }

/-- The traces: the compute trace embedded in the twin (new columns zero), the new chips zero. -/
def trA {F : Type} [Field F] (tr : TrJ8 F) : TrJ9A F :=
  { C := emb9 tr.C, M := tr.M, W := tr.W, J := tr.J, A := tr.A, V := tr.V, X := fun _ => 0, S := fun _ => 0 }

/-- The rows: one more compute row (the dummy axis row is charged to `N`, `BudJ9A.p1`), `AX = SP = 1`. -/
def rowsA (r : RowsJ8) : RowsJ9A := { toRowsJ8 := { r with N := r.N + 1 }, AX := 1, SP := 1 }

theorem trA_toJ8 {F : Type} [Field F] (tr : TrJ8 F) : (trA tr).toJ8 = tr := by
  cases tr
  simp only [TrJ9A.toJ8, trA]
  congr 1
  funext j
  exact ComplJ9AComp.emb9_oldCol _ j

/-- The J-8 budget at `N + 1`. -/
theorem budJ8_succ (Pb : PubJ8 p) (r : RowsJ8) (g : ℕ) (h : BudJ8 Pb r (g + r.N)) :
    BudJ8 Pb { r with N := r.N + 1 } (g + (r.N + 1)) := by
  obtain ⟨x1, x2, p1, p2, s1, s2⟩ := h
  exact ⟨by simp only; omega, x2, by simp only; omega, p2, by simp only; omega, s2⟩

/-- The J-9 A budget of the lifted record. -/
theorem budA (Pb : PubJ8 p) (r : RowsJ8) (g : ℕ) (h : BudJ8 Pb r (g + r.N)) :
    BudJ9A (pubA Pb) (rowsA r) (g + (rowsA r).N) := by
  obtain ⟨x1, x2, p1, p2, s1, s2⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [pubA, rowsA] <;> omega

/-- Staging of the embedded compute trace: `emb9` reads J-8 column `j` at RAP column `j` (`j < 69`, round 0) or
`j + 14` (round 1), and is `0` on the round-0 block `69..82`. -/
theorem staged_emb9 {K : Type} (Q : Coins frameJ8 K → Fin 123 → (ZMod p)[X])
    (hQ : StagedCols frameJ8 crC Q) : StagedCols frameJ8 crC9 (fun χ => emb9 (Q χ)) := by
  intro j χ χ' hχ
  simp only [emb9]
  split_ifs with h1 h2
  · refine hQ _ χ χ' fun i hi => hχ i ?_
    simp [crC, h1] at hi
  · rfl
  · refine hQ _ χ χ' fun i hi => hχ i ?_
    have h3 : ¬ ((j : ℕ) - 14 < 69) := by omega
    simpa [crC, crC9, h3, h2] using hi

theorem stA_of_st {K : Type} (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q) :
    StJ9A (fun χ => trA (Q χ)) := by
  obtain ⟨hC, hM, hW, hJ, hA, hV⟩ := hQ
  exact ⟨staged_emb9 (fun χ => (Q χ).C) hC, hM, hW, hJ, hA, hV, stagedCols_const _ _ _, stagedCols_const _ _ _⟩

end Lift

/-! ## 2. Acceptance transfer -/

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

theorem add_mk_zero {L : Type} [Field L] (d : L) (x y : Quad d) (a b c e : L) (ha : a = 0) (hb : b = 0)
    (hc : c = 0) (he : e = 0) (h : x = y) : x + Quad.mk d a b = y + Quad.mk d c e := by
  subst ha hb hc he h; rfl

/-- **`AcceptsJ9V → AcceptsJ9A`** at the lifted record (absent chips). -/
theorem acceptsA_of_V {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsJ9V δ b Pb Rg c χ M tr r g) (hle : RowsLe31 Pb) (hp63 : 2 ^ 63 < p) :
    AcceptsJ9A δ b (pubA Pb) Rg c χ (msgA M) (trA tr) (rowsA r) g := by
  have h' : AcceptsJ9V δ b (pubA Pb).toPubJ8 Rg c χ (msgA M).toMsgJ8' (trA tr).toJ8 (rowsA r).toRowsJ8 g := by
    rw [trA_toJ8]
    exact { h with hbud := budJ8_succ Pb r g h.hbud }
  obtain ⟨hn, _, _, _, hnA, _⟩ := hle
  refine AcceptsJ9A.of_V δ b h' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ComplJ9AComp.sat9_of_sat8 _ _ _ _ _ _ _ _ h.hsatX
  · show M.ρ 4 + Quad.mk (algebraMap (ZMod p) K δ) (0 : K) 0 = _
    rw [Quad.mk_zero', add_zero]
    exact h.hGp
  · exact add_mk_zero _ _ _ _ _ _ _ rfl rfl rfl rfl h.hGS
  · show Pb.nA + 1 < 2 ^ 57; omega
  · exact budA Pb r g h.hbud
  · exact ⟨h.hbudV.1, h.hbudV.2.1, h.hbudV.2.2.1, h.hbudV.2.2.2, le_refl 1, le_refl 1⟩
  · exact Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · show 1 + Pb.n < p ∧ 2 * 1 < p
    constructor <;> omega

end Accept

/-! ## 3. Completeness in the absent regime -/

section Rec
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen

open Classical in
/-- **`complJ9A_closed_absent`: J-9 A completeness at Goldilocks on J-9 B's hypotheses (absent regime).**  Exactly
`complJ9B_closed`'s binders.  At the J-9 B honest record `B := BRun9`, lifted to J-9 A with the axis and split chips
ABSENT (`pubA`, `msgA`, `trA`, `rowsA`): honest acceptance by `AcceptsJ9A` at every good coin, `Pr[¬Good] ≤ ε_c`
(the same `ε_c` as J-9 B: absent chips add no honest bad event), staging `StJ9A`, the claim holds, and at
`|K| = cK` the figure `ε_c < 2^-120` with an accepting coin; and both chips are absent (`axOn = spOn = false`). -/
theorem complJ9A_closed_absent (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hleaf : ComplJ8Walk.RootsLeafOK (DD).roots)
    (hwalk : ComplJ8Walk.WalkDepthOK (DD).reads)
    (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hregAx : ∀ id ∈ ComplJ8Jet.CalledIds t, ∀ i, (Rt id).ax i < p)
    (h31 : Rows31 (DD)) :
    let B := BRun9 δ b Rt hgen hpG h31
    (∀ χ, B.Good χ → AcceptsJ9A δ b (pubA B.Pb) Rg.R (cJ s f r) χ (msgA (B.M χ)) (trA (B.tr χ)) (rowsA B.rows) B.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) ≤ B.epsC) ∧
    StJ9A (fun χ => trA (B.tr χ)) ∧ Nock.Jet.HoldsN (cJ s f r) ∧
    (Fintype.card K = VclL.Events.cK →
      B.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A δ b (pubA B.Pb) Rg.R (cJ s f r) χ (msgA (B.M χ)) (trA (B.tr χ)) (rowsA B.rows) B.g) ∧
    (pubA B.Pb).axOn = false ∧ (pubA B.Pb).spOn = false := by
  intro B
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hle : RowsLe31 B.Pb := rowsLe31_of δ b Rt hgen _ _ _ (AV9 δ b Rt hgen hpG h31)
    (famsAll9 δ b Rt hgen hpG h31 (famsA9 δ b (j9DataOf p Rg Rt hgen) (DD) (dvd9 Rt hgen hpG h31)
      (acs9_pos Rt hgen))) h31
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    complJ9B_closed δ b Rt hgen hpG hax hop5 hleaf hwalk hwalkA hRt hregAx h31
  refine ⟨fun χ hχ => acceptsA_of_V δ b (h1 χ hχ) hle hp63, h2, stA_of_st _ h3, h4, fun hcK => ?_, rfl, rfl⟩
  obtain ⟨he, χ, hχ⟩ := h5 hcK
  exact ⟨he, χ, acceptsA_of_V δ b hχ hle hp63⟩

end Rec

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsent

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsent
#print axioms acceptsA_of_V
#print axioms stA_of_st
#print axioms complJ9A_closed_absent
end Axioms
