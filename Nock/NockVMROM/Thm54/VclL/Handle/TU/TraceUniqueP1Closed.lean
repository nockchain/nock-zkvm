/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/TraceUniqueP1Closed.lean

 **Closed forms of (B) `canon_eq_final` and (C) `trace_unique_prob_final`.**

 * §1 **The honest record's rows cannot be used.** `(BC …).rows = canonRows Pb extraRows` keeps `Λ`, `leaves`,
 `maxlen` from `extraRows = 0`, so `hk : 2·fuelChip ≤ rows.leaves`, `hqM`, `hmax` and `RowsLe rows cornerC`
 (`Λ = fuelChip`) are all FALSE there (`BC_rows_bad`): (B)/(C) at `(BC …).rows` are vacuous. The verifier
 parameters are therefore restated at `rowsP1 Pb` (the canonical layout's table sizes, the census corner's `Λ`,
 `leaves`, `maxlen`) and budget `g = 0`. `AcceptsJ8V` reads the rows only through `hbud` / `hbudV`
 (`acceptsCanonP1_rows`), so the canonical triple is still accepted there (`canon_accepts_rowsP1`).
 * §2 every row/event parameter of (A) at `rowsP1`, `g = 0`, `R0d`, `L0d`, `skel = []` (`params_P1`).
 * §3 `canon_eq_closed'` / `trace_unique_prob_closed'` (with the cover `hcovC` as a hypothesis); the figure
 `fig_P1`: `2·ε + ε_c < 2^-119` (`epsJ8X_lt_155_census32` at `rowsP1`, `complJ8_P1`'s `ε_c < 2^-120`).
 * §4 **`hcovC_P1`**: the canonical compute path requests cover `RdP1` (`pKey_row`, the entry-level form of
 `ComplJ8OfBalG.pRow_row`; `reads_eqG`; `polyX_eval`/`trX_base` at the row nodes; `hdlP` serials).
 * §5 **`canon_eq_closed`**, **`trace_unique_prob_closed`**, **`trace_unique_prob_119`** (`< 2^-119` at
 `|K| = cK`): hypotheses `hpG`, `P1FragC c`, `P1SizeOK p c`, the run `h`, and the coin/event facts only.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 pubVJ8 chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX qW qM encJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5 (R0d L0d)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1 (dataA)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1 (reqsPW)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1 (szOfClaim P1SizeOK noPathReads RdP1 runP1 runP1_gen DC Rt0)
open Nock.Edit.GenX (SkelX)
open Nock.Atoms (lenL)

noncomputable section

/-! ## 1. The verifier rows `rowsP1`; the honest record's rows are unusable -/

section Rows
variable {p : ℕ} [Fact p.Prime]

/-- **The verifier rows on the P1 fragment**: the layout's table sizes (`J = rd = calls = inc = 0`, `heads = mb =
nA`, `blocks = 2·nV`, as `canonRows`) and the census corner's `Λ = fuelChip`, `leaves = 2·fuelChip`,
`maxlen = 2^31`. -/
def rowsP1 (Pb : PubJ8 p) : RowsJ8 where
  N := Pb.n
  D := Pb.nC
  W := Pb.nW
  Λ := fuelChip
  A := Pb.nA
  AW := Pb.nV
  J := 0
  mb := Pb.nA
  inc := 0
  calls := 0
  heads := Pb.nA
  blocks := 2 * Pb.nV
  rd := 0
  leaves := 2 * fuelChip
  maxlen := 2 ^ 31

theorem jCount_canon (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim)
    (es : List (Nock.Jet.ChipJ8.Kd × List Nock.Jet.ChipJ8.KE)) :
    RealIOJ8.jCount es (canonPb hpG sz c).lay = 0 := rfl

/-- **The budget at `rowsP1`, `g = 0`** on the canonical layout. -/
theorem bud_P1 (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim) :
    RealIOJ8.BudJ8 (canonPb hpG sz c) (rowsP1 (canonPb hpG sz c)) (0 + (rowsP1 (canonPb hpG sz c)).N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [jCount_canon, rowsP1, (canonPb_consts hpG sz c).1, (canonPb_consts hpG sz c).2.1,
      (canonPb_consts hpG sz c).2.2.1, (canonPb_consts hpG sz c).2.2.2.2.1, List.length_nil] <;> omega

theorem budV_P1 (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim) :
    (canonPb hpG sz c).regs.length ≤ 0 ∧ (canonPb hpG sz c).nA ≤ (rowsP1 (canonPb hpG sz c)).mb ∧
      (canonPb hpG sz c).nA ≤ (rowsP1 (canonPb hpG sz c)).A ∧
      (canonPb hpG sz c).nV ≤ (rowsP1 (canonPb hpG sz c)).AW :=
  ⟨by rw [(canonPb_consts hpG sz c).2.2.2.2.1]; rfl, le_rfl, le_rfl, le_rfl⟩

end Rows

section Lift
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K) [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **The rows enter `AcceptsCanonP1` only through the budgets**: acceptance at `(r, g)` gives acceptance at any
`(r', g')` satisfying `hbud` / `hbudV` there. -/
theorem acceptsCanonP1_rows {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    {ax : AuxP1 (ZMod p)} {r r' : RowsJ8} {g g' : ℕ}
    (h : AcceptsCanonP1 δ b hpG sz Pb Rg c χ M tr ax r g) (hb : RealIOJ8.BudJ8 Pb r' (g' + r'.N))
    (hv : Pb.regs.length ≤ g' ∧ Pb.nA ≤ r'.mb ∧ Pb.nA ≤ r'.A ∧ Pb.nV ≤ r'.AW) :
    AcceptsCanonP1 δ b hpG sz Pb Rg c χ M tr ax r' g' :=
  ⟨⟨⟨{ h.1.1.1 with hbud := hb, hbudV := hv }, h.1.1.2⟩, h.1.2⟩, h.2⟩

end Lift

section Bad
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **Why (B)/(C) at `(BC …).rows` are vacuous**: the honest record's rows have `leaves = maxlen = Λ = 0`, so `hk`,
`hqM` (at `x = 0`) and `RowsLe … cornerC` (its `Λ = fuelChip` conjunct) all fail. -/
theorem BC_rows_bad (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} {t : NTree SkelX}
    (h : runP1 c = some (t, c.result)) (hok : P1SizeOK p c) :
    ¬ (2 * fuelChip ≤ (BC δ b hpG h hok (K := K)).rows.leaves) ∧
    ¬ (∀ x < ringChar (ZMod p), lenL x ≤ (BC δ b hpG h hok (K := K)).rows.maxlen) ∧
    ¬ WeightsJ8.RowsLe (BC δ b hpG h hok (K := K)).rows EncInjJ8.cornerC := by
  have hl : (BC δ b hpG h hok (K := K)).rows.leaves = 0 := rfl
  have hm : (BC δ b hpG h hok (K := K)).rows.maxlen = 0 := rfl
  have hΛ : (BC δ b hpG h hok (K := K)).rows.Λ = 0 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hl]; simp [fuelChip]
  · intro H
    have := H 0 (Fact.out : (ringChar (ZMod p)).Prime).pos
    rw [hm] at this
    have h1 := Nock.Atoms.one_le_lenL 0
    omega
  · intro H
    have := H.2.2.2.1
    rw [hΛ] at this
    simp [EncInjJ8.cornerC, WeightsJ8.corner31, fuelChip] at this

end Bad

/-! ## 2. The parameters of (A) at `rowsP1` -/

section Params
variable {p : ℕ} [Fact p.Prime]
attribute [local instance] ClaimSizesP1.fact_rc
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (sizesJ8)

/-- The three table sizes of the canonical layout are `≤ 2^31` (`Rows31`). -/
theorem sizes31 {c : P8PublicClaim} {t : NTree SkelX} (h : runP1 c = some (t, c.result)) (hok : P1SizeOK p c) :
    (szOfClaim p c).n ≤ 2 ^ 31 ∧ (szOfClaim p c).nC ≤ 2 ^ 31 ∧ (szOfClaim p c).nW ≤ 2 ^ 31 := by
  have h31 := ((ClaimSizesP1.P1SizeOK_of p h).mp hok).1
  obtain ⟨hfit, he⟩ := ClaimSizesP1.szOfClaim_eq_szOf p h hok
  rw [he]
  refine ⟨h31 _ ?_, h31 _ ?_, h31 _ ?_⟩ <;> simp [sizesJ8, CanonGenP1.szOf]

theorem hnM_P1 (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (hok : P1SizeOK p c) : (layPb (canonPb hpG (szOfClaim p) c) [] (by simp)).nM ≤ 2 ^ 31 :=
  (sizes31 h hok).2.1

theorem hreg_P1 (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim) :
    (censusG (canonPb hpG sz c) c).length ≤ 2 ^ 31 := by
  have : (censusG (canonPb hpG sz c) c).length = (claimCells c).length := by
    simp [censusG, (canonPb_consts hpG sz c).2.2.2.2.1]
  rw [this]
  have : (claimCells c).length ≤ 3 :=
    (List.length_filter_le _ _).trans (by simp)
  omega

theorem hL_P1 (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim) :
    LayLe (layPb (canonPb hpG sz c) [] (by simp)) (rowsP1 (canonPb hpG sz c)) :=
  LinkJ8NV.layLe_ofG _ le_rfl le_rfl le_rfl le_rfl le_rfl

theorem hr_P1 (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (hok : P1SizeOK p c) : WeightsJ8.RowsLe (rowsP1 (canonPb hpG (szOfClaim p) c)) EncInjJ8.cornerC := by
  obtain ⟨h1, h2, h3⟩ := sizes31 h hok
  have hA := (canonPb_consts hpG (szOfClaim p) c).2.1
  have hV := (canonPb_consts hpG (szOfClaim p) c).2.2.1
  refine ⟨h1, h2, h3, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, le_rfl⟩ <;>
    simp only [rowsP1, hA, hV, EncInjJ8.cornerC, WeightsJ8.corner31] <;> norm_num

theorem hqM_P1 (hpG : p = Nock.Atoms.p) (Pb : PubJ8 p) :
    ∀ x < ringChar (ZMod p), lenL x ≤ (rowsP1 Pb).maxlen := by
  intro x hx
  rw [ZMod.ringChar_zmod_n, hpG] at hx
  show lenL x ≤ 2 ^ 31
  unfold lenL
  rw [ite_eq_left_iff.mpr (fun h => absurd hx h)]
  norm_num

theorem hmax_P1 (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (c : P8PublicClaim) :
    (canonPb hpG sz c).nA + 2 ≤ (rowsP1 (canonPb hpG sz c)).maxlen := by
  rw [(canonPb_consts hpG sz c).2.1]; show 1 + 2 ≤ 2 ^ 31; norm_num

theorem hk_P1 (Pb : PubJ8 p) : 2 * fuelChip ≤ (rowsP1 Pb).leaves := le_rfl

end Params

/-! ## 3. (B) `canon_eq_closed`, (C) `trace_unique_prob_closed` -/

section Closed
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The event data on the P1 fragment**: `dataA` at the canonical layout, `rowsP1`, `g = 0`, `R0d`, `L0d`,
`skel = []` (the data of `LinkJ8A.probJ8V_absent`). -/
abbrev dataP1 (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (hok : P1SizeOK p c) :=
  dataA δ b (g := 0) (canonPb hpG (szOfClaim p) c) c
    (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (Tr := TrJ8 (ZMod p)) (St := StJ8)
      (r := rowsP1 (canonPb hpG (szOfClaim p) c)) (P := 2 ^ 66))
    (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (Tr := TrJ8 (ZMod p)) (St := StJ8)
      (r := rowsP1 (canonPb hpG (szOfClaim p) c)))
    [] (by simp) (hL_P1 hpG (szOfClaim p) c) rfl (hnM_P1 hpG h hok) (hreg_P1 hpG (szOfClaim p) c)

/-- **Completeness at `rowsP1`**: at a good coin of the honest record the canonical triple is accepted by
`AcceptsCanonP1` at `rowsP1`, `g = 0`. -/
theorem canon_accepts_rowsP1 (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} (hc : P1FragC c) (hok : P1SizeOK p c)
    {t : NTree SkelX} (h : runP1 c = some (t, c.result)) {χ : Coins frameJ8 K} (hχ : (BC δ b hpG h hok).Good χ) :
    AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
      (msgC δ b hpG h hok χ) (trC δ b hpG h hok χ) (axC δ b hpG h χ) (rowsP1 (canonPb hpG (szOfClaim p) c)) 0 :=
  acceptsCanonP1_rows δ b (canon_accepts_P1 δ b hpG hc hok h hχ) (bud_P1 hpG _ c) (budV_P1 hpG _ c)

/-- **(B) `canon_eq_closed`**: on a P1 claim with the size premise, at the canonical layout, the empty registry,
the verifier rows `rowsP1` and budget `0`: a tuple accepted by `AcceptsCanonP1` at a coin `χ` that is good for the
honest record and outside the absent-data events `allJ8X (dataP1 …)` at the tuple's trace and the canonical trace
IS the canonical triple, provided the canonical cover `hcovC`. -/
theorem canon_eq_closed' [CharP K p] [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} (hc : P1FragC c)
    (hok : P1SizeOK p c) {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (hacc : AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
      M tr ax (rowsP1 (canonPb hpG (szOfClaim p) c)) 0)
    (hχ : (BC δ b hpG h hok).Good χ)
    (hg : ∀ s ∈ allJ8X (dataP1 δ b hpG h hok), ¬ s.mem tr χ)
    (hgC : ∀ s ∈ allJ8X (dataP1 δ b hpG h hok), ¬ s.mem (trC δ b hpG h hok χ) χ)
    (hcovC : ReqCoverP1 p c (reqsPW δ b (canonPb hpG (szOfClaim p) c) c χ (msgC δ b hpG h hok χ).m
      (msgC δ b hpG h hok χ).ρ (msgC δ b hpG h hok χ).ρS (trC δ b hpG h hok χ))) :
    (tr, ax, M) = canonOfP1 δ b hpG h hok χ :=
  trace_unique_good_final δ b hpG Nock.Jet.VerifiedRegistry.empty.faithful hc hok _ _ [] (by simp)
    (hL_P1 hpG (szOfClaim p) c) rfl (hnM_P1 hpG h hok) (hreg_P1 hpG (szOfClaim p) c) (hr_P1 hpG h hok)
    (Nat.zero_le _) (hmax_P1 hpG _ c) (hqM_P1 hpG _) (hk_P1 _) hacc (canon_accepts_rowsP1 δ b hpG hc hok h hχ)
    hg hgC hcovC

/-- **The figure**: `2·ε(allJ8X (dataP1 …)) + ε_c < 2^-119` at `|K| = cK`. -/
theorem fig_P1 (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} (hc : P1FragC c) (hok : P1SizeOK p c)
    {t : NTree SkelX} (h : runP1 c = some (t, c.result)) (hcK : Fintype.card K = VclL.Events.cK) :
    2 * epsilonOf (allJ8X (dataP1 δ b hpG h hok)) + (BC δ b hpG h hok).epsC < 1 / (2 : ℚ) ^ 119 := by
  have hc' : P1FragC ⟨c.subject, c.formula, c.result⟩ := by cases c; exact hc
  have hr := hr_P1 hpG h hok
  have hN : 0 + (rowsP1 (canonPb hpG (szOfClaim p) c)).N ≤ 2 ^ 32 := by
    have := hr.1; simp only [EncInjJ8.cornerC, WeightsJ8.corner31] at this; omega
  have e1 := RepriceJ8.epsJ8X_lt_155_census32 (dataP1 δ b hpG h hok) hcK hr le_rfl hN
  have e2 := ((CanonCompleteP1.complJ8_P1 δ b (Rt := Rt0) hpG (runP1_gen h) hc' (hR31 h hok)
    ((ClaimSizesP1.P1SizeOK_of p h).mp hok).2 (K := K)).2.2.2.2 hcK).1
  have e2' : (BC δ b hpG h hok).epsC < 1 / 2 ^ 120 := e2
  calc 2 * epsilonOf (allJ8X (dataP1 δ b hpG h hok)) + (BC δ b hpG h hok).epsC
      < 2 * (1 / (2 : ℚ) ^ 155) + 1 / 2 ^ 120 := by linarith
    _ ≤ 1 / (2 : ℚ) ^ 119 := by norm_num

open Classical in
/-- **(C) `trace_unique_prob_closed'`** (with the canonical cover as a hypothesis): for any staged prover strategy
`Q`, `Pr_χ[AcceptsCanonP1 (Q χ) at rowsP1, 0 ∧ Q χ ≠ canonOf χ] ≤ 2·ε + ε_c`, and `< 2^-119` at `|K| = cK`. -/
theorem trace_unique_prob_closed' [CharP K p] [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {c : P8PublicClaim}
    (hc : P1FragC c) (hok : P1SizeOK p c) {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (hcovC : ∀ χ : Coins frameJ8 K, ReqCoverP1 p c (reqsPW δ b (canonPb hpG (szOfClaim p) c) c χ
      (msgC δ b hpG h hok χ).m (msgC δ b hpG h hok χ).ρ (msgC δ b hpG h hok χ).ρS (trC δ b hpG h hok χ)))
    (Q : Coins frameJ8 K → TripP1 p K δ) (hQ : StJ8 fun χ => (Q χ).1) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
          (Q χ).2.2 (Q χ).1 (Q χ).2.1 (rowsP1 (canonPb hpG (szOfClaim p) c)) 0 ∧
        Q χ ≠ canonOfP1 δ b hpG h hok χ).card : ℚ) / Fintype.card (Coins frameJ8 K) ≤
      2 * epsilonOf (allJ8X (dataP1 δ b hpG h hok)) + (BC δ b hpG h hok).epsC := by
  have hc' : P1FragC ⟨c.subject, c.formula, c.result⟩ := by cases c; exact hc
  obtain ⟨hfit, hsz⟩ := ClaimSizesP1.szOfClaim_eq p h hok
  set L := allJ8X (dataP1 δ b hpG h hok) with hLd
  set E1 := unionEvent L (fun χ => (Q χ).1)
  set E2 := unionEvent L (fun χ => trC δ b hpG h hok χ)
  set E3 := Finset.univ.filter fun χ : Coins frameJ8 K => ¬ (BC δ b hpG h hok).Good χ
  have hsub : (Finset.univ.filter fun χ : Coins frameJ8 K =>
        AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
          (Q χ).2.2 (Q χ).1 (Q χ).2.1 (rowsP1 (canonPb hpG (szOfClaim p) c)) 0 ∧
        Q χ ≠ canonOfP1 δ b hpG h hok χ) ⊆ E1 ∪ E2 ∪ E3 := by
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    by_contra hno
    simp only [Finset.mem_union, E1, E2, E3, unionEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      not_or, not_exists, not_and, not_not] at hno
    obtain ⟨⟨h1, h2⟩, h3⟩ := hno
    exact hχ.2 (canon_eq_closed' δ b hpG hc hok h hχ.1 h3 (fun s hs' => h1 s hs') (fun s hs' => h2 s hs')
      (hcovC χ))
  have hcard := Finset.card_le_card hsub
  have hu := (Finset.card_union_le (E1 ∪ E2) E3).trans (Nat.add_le_add_right (Finset.card_union_le E1 E2) _)
  have hpos : (0 : ℚ) < Fintype.card (Coins frameJ8 K) := by exact_mod_cast Fintype.card_pos
  have b1 := union_prob_le L (fun χ => (Q χ).1) hQ
  have b2 := union_prob_le L (fun χ => trC δ b hpG h hok χ) (trC_staged δ b hpG hc hok h)
  have b3 := (CanonSideP1.canon_complete' δ b (Rt := Rt0) hpG (runP1_gen h) hc' (hR31 h hok)
    ((ClaimSizesP1.P1SizeOK_of p h).mp hok).2 (szOfClaim p) hsz (K := K)).2
  calc _ ≤ ((E1.card + E2.card + E3.card : ℕ) : ℚ) / Fintype.card (Coins frameJ8 K) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard.trans hu) hpos.le
    _ = (E1.card : ℚ) / Fintype.card (Coins frameJ8 K) + (E2.card : ℚ) / Fintype.card (Coins frameJ8 K) +
        (E3.card : ℚ) / Fintype.card (Coins frameJ8 K) := by push_cast; ring
    _ ≤ epsilonOf L + epsilonOf L + (BC δ b hpG h hok).epsC := add_le_add (add_le_add b1 b2) b3
    _ = _ := by ring

end Closed

/-! ## 4. `hcovC`: the canonical compute path requests cover the honest reads -/

section Recs
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (consQX pairRecsB)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (keyX keyXN pair_mem_consQX)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]

/-- An active slot entry's record is consumed. -/
theorem ent_mem_consQX {e : Env (ZMod p)} {S : SlotX ℚ} (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) {x : EntX ℚ}
    (hx : x ∈ S.ents) (hb : x.bal = .p) (ha : evalQX x.act e = 1) : x.rcd ∈ consQX e .p := by
  unfold consQX
  refine List.mem_flatMap.mpr ⟨S, hS, List.mem_append_left _ (List.mem_map.mpr ⟨x, ?_, rfl⟩)⟩
  exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hx, by simp [hb]⟩, by simp [ha]⟩

theorem key_walkRecX (e : Env (ZMod p)) (root : Hd) (axis : ℕ) (ch : Hd) :
    keyX (K := K) 5 (walkRecX root axis ch) e 0 = algebraMap (ZMod p) K (e.trace root.v) ∧
    keyX (K := K) 5 (walkRecX root axis ch) e 1 = algebraMap (ZMod p) K (e.trace axis) := by
  simp [keyX, keyXN, walkRecX, recOf, ChipH.walkRec, RE.ev]

/-- The four `.p` consume sites of a compute row, at the column level (the records of `pRow`). -/
theorem pRec_s0 (e : Env (ZMod p)) (h : e.trace 0 * (1 - e.trace 19) = 1) :
    ∃ y ∈ consQX e .p, keyX (K := K) 5 y e 0 = algebraMap (ZMod p) K (e.trace 26) ∧
      keyX (K := K) 5 y e 1 = algebraMap (ZMod p) K (e.trace 38) := by
  refine ⟨_, ent_mem_consQX (S := slot1X) (by simp [ChipHX.slotsX])
    (x := ⟨[0], notC z1X, walkRecX xS xFt.v xE, .p⟩) (by simp only [slot1X]; simp) rfl ?_,
    key_walkRecX e _ _ _⟩
  simpa [EntX.act, evalQX, selS, notC, cc, CoeffExpr.sumList, z1X] using h

theorem pRec_s9 (e : Env (ZMod p)) (h : e.trace 9 * (1 - e.trace 19) = 1) :
    ∃ y ∈ consQX e .p, keyX (K := K) 5 y e 0 = algebraMap (ZMod p) K (e.trace 32) ∧
      keyX (K := K) 5 y e 1 = algebraMap (ZMod p) K (e.trace 40) := by
  refine ⟨_, ent_mem_consQX (S := slot2X) (by simp [ChipHX.slotsX])
    (x := ⟨[9], notC z1X, walkRecX xSf1 xFth.v xM, .p⟩) (by simp only [slot2X]; simp) rfl ?_,
    key_walkRecX e _ _ _⟩
  simpa [EntX.act, evalQX, selS, notC, cc, CoeffExpr.sumList, z1X] using h

theorem pRec_s10 (e : Env (ZMod p)) (h : e.trace 11 * (1 - e.trace 19) = 1) :
    ∃ y ∈ consQX e .p, keyX (K := K) 5 y e 0 = algebraMap (ZMod p) K (e.trace 30) ∧
      keyX (K := K) 5 y e 1 = algebraMap (ZMod p) K (e.trace 20) := by
  refine ⟨_, ent_mem_consQX (S := slot3X) (by simp [ChipHX.slotsX])
    (x := ⟨[sS10], notC z1X, walkRecX xE vX xSf1, .p⟩) (by simp only [slot3X]; simp) rfl ?_,
    key_walkRecX e _ _ _⟩
  simpa [EntX.act, evalQX, selS, notC, cc, CoeffExpr.sumList, z1X, sS10] using h

theorem pRec_pair (e : Env (ZMod p)) (h : e.trace 24 = 1) :
    (∃ y ∈ consQX e .p, keyX (K := K) 5 y e 0 = algebraMap (ZMod p) K (e.trace 32) ∧
      keyX (K := K) 5 y e 1 = algebraMap (ZMod p) K (e.trace 48)) ∧
    (∃ y ∈ consQX e .p, keyX (K := K) 5 y e 0 = algebraMap (ZMod p) K (e.trace 34) ∧
      keyX (K := K) 5 y e 1 = algebraMap (ZMod p) K (e.trace 48)) := by
  obtain ⟨h1, h2⟩ := pair_mem_consQX e (S := slot2X) (by simp [ChipHX.slotsX]) rfl h
  exact ⟨⟨_, h1, key_walkRecX e _ _ _⟩, ⟨_, h2, key_walkRecX e _ _ _⟩⟩

end Recs

section Row
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (consQX)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (keyX)
open Nock.Edit.GenX (consEntriesX RowNX)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]

/-- **Every walk entry of an honest compute row is the key of a `.p` request of that row** (entry-level form of
`ComplJ8OfBalG.pRow_row`): at an environment whose round-0 columns are the row's `colX`, for each consumed walk
entry `(root, axis, child)` some consumed `.p` record has key coordinates `((H root).2, axis)`. -/
theorem pKey_row (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (rr : RowNX) (fl ll : ZMod p)
    (hok : HonestCompX.RowOKX p rr) (hH : HonestCompX.HdlOK p H) (e : Env (ZMod p))
    (he : ∀ c < 69, e.trace c = HonestCompX.colX H pd rr fl ll c) :
    ∀ x ∈ consEntriesX rr, ∃ y ∈ consQX e .p,
      keyX (K := K) 5 y e 0 = (((H x.1).2 : ℕ) : K) ∧ keyX (K := K) 5 y e 1 = ((x.2.1 : ℕ) : K) := by
  have hva : ∀ a, a < p → HonestCompX.hv H (.atom a) = ((a : ℕ) : ZMod p) := fun a ha => by
    show (((H (.atom a)).2 : ℕ) : ZMod p) = _
    rw [hH.small a ha]
  have hvn : ∀ n : Noun, algebraMap (ZMod p) K (HonestCompX.hv H n) = (((H n).2 : ℕ) : K) := fun n => by
    simp [HonestCompX.hv]
  have c0 := HonestCompX.colX_st H pd rr fl ll 0 (by decide)
  have c9 := HonestCompX.colX_st H pd rr fl ll 9 (by decide)
  have c11 := HonestCompX.colX_st H pd rr fl ll 11 (by decide)
  intro x hx
  unfold HonestCompX.RowOKX at hok
  simp only [consEntriesX, List.mem_append] at hx
  rcases hx with (((hx | hx) | hx) | hx) | hx <;> split_ifs at hx with hc
  all_goals first | exact absurd hx List.not_mem_nil | skip
  · -- s0
    rw [List.mem_singleton] at hx; subst hx
    rw [hc.1] at hok
    obtain ⟨-, -, ax, hax, hft, -⟩ := hok
    have hf : e.trace 0 * (1 - e.trace 19) = 1 := by
      rw [he 0 (by norm_num), he 19 (by norm_num), c0, HonestCompX.cx19]
      simp [hc.1, HonestCompX.cZ1, RowDecodeVSX.stIdx, hc.2]
    obtain ⟨y, hy, k0, k1⟩ := pRec_s0 (K := K) e hf
    refine ⟨y, hy, ?_, ?_⟩
    · rw [k0, he 26 (by norm_num), HonestCompX.cxS_v, hvn]
    · rw [k1, he 38 (by norm_num), HonestCompX.cxFt_v, hft, hva ax hax]
      simp [atomVal]
  · -- s9
    rw [List.mem_singleton] at hx; subst hx
    rw [hc.1] at hok
    obtain ⟨-, -, -, -, ⟨ax, hax, hft, -⟩, -⟩ := hok
    have hf : e.trace 9 * (1 - e.trace 19) = 1 := by
      rw [he 9 (by norm_num), he 19 (by norm_num), c9, HonestCompX.cx19]
      simp [hc.1, HonestCompX.cZ1, RowDecodeVSX.stIdx, hc.2]
    obtain ⟨y, hy, k0, k1⟩ := pRec_s9 (K := K) e hf
    refine ⟨y, hy, ?_, ?_⟩
    · rw [k0, he 32 (by norm_num), HonestCompX.cxSf1_v, hvn]
    · rw [k1, he 40 (by norm_num), HonestCompX.cxFth_v, hft, hva ax hax]
      simp [atomVal]
  · -- s5
    rw [hc.1] at hok
    obtain ⟨-, -, -, -, -, -, -, -, hm, hP⟩ := hok
    have hm1 : rr.m ≠ Noun.atom 1 := by
      rw [hm]; intro h1
      have := two_le_axisOfPath hc.2.2
      simp only [Noun.atom.injEq] at h1
      omega
    have hf : e.trace 24 = 1 := by
      rw [he 24 (by norm_num), HonestCompX.cx24]
      simp [HonestCompX.cPr, hc.1, hc.2.1, hm1]
    obtain ⟨⟨y1, hy1, k10, k11⟩, ⟨y2, hy2, k20, k21⟩⟩ := pRec_pair (K := K) e hf
    have hv48 : algebraMap (ZMod p) K (e.trace 48) = ((atomVal rr.m : ℕ) : K) := by
      rw [he 48 (by norm_num), HonestCompX.cxM_v, hm, hva _ hP]; simp [atomVal]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨y1, hy1, by rw [k10, he 32 (by norm_num), HonestCompX.cxSf1_v, hvn], by rw [k11, hv48]⟩
    · exact ⟨y2, hy2, by rw [k20, he 34 (by norm_num), HonestCompX.cxSf2_v, hvn], by rw [k21, hv48]⟩
  · -- s10
    rw [List.mem_singleton] at hx; subst hx
    rw [hc.1] at hok
    obtain ⟨-, -, -, -, ⟨ax, hax, hft, -⟩, -⟩ := hok
    have hf : e.trace 11 * (1 - e.trace 19) = 1 := by
      rw [he 11 (by norm_num), he 19 (by norm_num), c11, HonestCompX.cx19]
      simp [hc.1, HonestCompX.cZ1, RowDecodeVSX.stIdx, hc.2]
    obtain ⟨y, hy, k0, k1⟩ := pRec_s10 (K := K) e hf
    refine ⟨y, hy, ?_, ?_⟩
    · rw [k0, he 30 (by norm_num), HonestCompX.cxE_v, hvn]
    · rw [k1, he 20 (by norm_num), HonestCompX.cx20]
      simp only [HonestCompX.cV, hc.1]
      rw [hft, hva ax hax]
      simp [atomVal]
  · -- s10L
    rw [hc] at hok
    obtain ⟨-, a, -, -, ha1, -, -, hm, -⟩ := hok
    have hx' : a ^^^ 1 < p := by rw [Nock.Edit.xor_one_eq]; split <;> omega
    have hf : e.trace 24 = 1 := by
      rw [he 24 (by norm_num), HonestCompX.cx24]
      simp [HonestCompX.cPr, hc]
    obtain ⟨⟨y1, hy1, k10, k11⟩, ⟨y2, hy2, k20, k21⟩⟩ := pRec_pair (K := K) e hf
    have hv48 : algebraMap (ZMod p) K (e.trace 48) = ((atomVal rr.m : ℕ) : K) := by
      rw [he 48 (by norm_num), HonestCompX.cxM_v, hm, hva _ hx']; simp [atomVal]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨y1, hy1, by rw [k10, he 32 (by norm_num), HonestCompX.cxSf1_v, hvn], by rw [k11, hv48]⟩
    · exact ⟨y2, hy2, by rw [k20, he 34 (by norm_num), HonestCompX.cxSf2_v, hvn], by rw [k21, hv48]⟩

end Row

section Cover
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (consQX)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (keyX compReqsX)
open Nock.Edit.GenX (consEntriesX RowNX rowOfSkelX)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX (polyX polyX_eval trX_base baseT flX llX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (powN)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1 (trCanon)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1 (oP1)

/-- **`hcovC`, closed**: at every coin, every honest read `(cells.idxOf root, axis) ∈ RdP1 p c` is the pair of
the first two key coordinates of a compute path request (`.p`) of the canonical trace. Route: `RdP1`'s reads are
the run's path reads (`pathKind`, `reads_eqG`: the rows' walk entries); the canonical compute columns at row node
`j` are the honest row's `colX` (`polyX_eval`, `trX_base`); `pKey_row` reads the request off the row; the root key
`(H root).2` is the root's cell serial (`hdlP`, `genIdxOf_eq`). -/
theorem hcovC_P1 (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} (hc : P1FragC c) (hok : P1SizeOK p c)
    {t : NTree SkelX} (h : runP1 c = some (t, c.result)) (χ : Coins frameJ8 K) :
    ReqCoverP1 p c (reqsPW δ b (canonPb hpG (szOfClaim p) c) c χ (msgC δ b hpG h hok χ).m
      (msgC δ b hpG h hok χ).ρ (msgC δ b hpG h hok χ).ρS (trC δ b hpG h hok χ)) := by
  have hc' : P1FragC ⟨c.subject, c.formula, c.result⟩ := by cases c; exact hc
  obtain ⟨hfit, hsz⟩ := ClaimSizesP1.szOfClaim_eq p h hok
  have hgen := runP1_gen h
  have hR := hR31 h hok
  have R := CanonRunP1.canon_run_all (Rt := Rt0) hpG hgen hc' hR ((ClaimSizesP1.P1SizeOK_of p h).mp hok).2
  have hn : (canonPb hpG (szOfClaim p) c).n = (bfsForest [t]).length := by
    show (szOfClaim p c).n = _; rw [hsz]; rfl
  have hnC : (szOfClaim p c).nC = (DC p h).cells.length := by rw [hsz]; rfl
  have hnW : (szOfClaim p c).nW = (GenWalk.walkRows (DC p h).cells (DC p h).reads).length := by rw [hsz]; rfl
  have hht : ComplJ8Of.htJ8 (DC p h) = (szOfClaim p c).ht :=
    CanonCompleteP1.htJ8_p1 _ R.jrows R.acs1 R.preads _ hn hnC hnW
  have ho : HEq (oP1 hpG hgen hR (Rt := Rt0)) (canonPb hpG (szOfClaim p) c).orbit :=
    CanonCompleteP1.orbitG_heq hpG hht _ _ (SizesP1.one_le_ht _) (SizesP1.ht_le_32 _)
  have etr : trC δ b hpG h hok χ = trCanon δ b (DC p h) (CanonGenP1.j8DataCanon_ok p _ Rt0 hgen).cells_pos
      (CanonGenP1.j8DataCanon_ok p _ Rt0 hgen).acs_pos (canonPb hpG (szOfClaim p) c).orbit χ :=
    CanonCompleteP1.trCanon_congr δ b _ _ _ hht _ _ ho χ
  have hleN : (bfsForest [t]).length ≤ 2 ^ (szOfClaim p c).ht := by
    rw [← hn]; exact le_trans (le_max_left _ _) (szOfClaim p c).fit_ht
  have hinj := CanonOrbP1.powN_inj (canonPb hpG (szOfClaim p) c).orbit hleN
  have hH : HonestCompX.HdlOK p (DC p h).H := ComplJ8Data.hdlOK_hdlP p (DC p h).cells (DC p h).acs
  have hsm := ComplJ8.smallX_of_binders R.hax R.hop5
  -- the read
  intro s hs
  rw [ClaimSizesP1.RdP1_of p h] at hs
  unfold ClaimSizesP1.RdOf at hs
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
  have hy1 := (GenWalk.mem_pathKind.mp hy).1
  have hy2 := (J8Gen.reads_eqG Rt0 hgen CanonGenP1.ord8Canon).mem_iff.mp hy1
  obtain ⟨u, hu, hx⟩ := List.mem_flatMap.mp hy2
  obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, hjW, rfl⟩ := List.getElem_of_mem hu
  have hjn : j < (canonPb hpG (szOfClaim p) c).n := by rw [hn]; exact hjW
  have hin : InTree t ((bfsForest [t])[j]'hjW) :=
    Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton (List.getElem_mem hjW)
  have hokj := HonestRowX.rowOKX_of_genX hgen hin (hsm _ hin)
  -- the canonical compute environment at row `j`
  rw [etr]
  unfold reqsPW compReqsX
  set E := TeleC.envsN (canonPb hpG (szOfClaim p) c).hn (canonPb hpG (szOfClaim p) c).nodes (chalVJ8 b χ)
    (pubVJ8 δ b c (msgC δ b hpG h hok χ).m (msgC δ b hpG h hok χ).ρ (msgC δ b hpG h hok χ).ρS χ)
    (canonPb hpG (szOfClaim p) c).orbit
    (qX δ b (canonPb hpG (szOfClaim p) c) (trCanon δ b (DC p h) (CanonGenP1.j8DataCanon_ok p _ Rt0 hgen).cells_pos
      (CanonGenP1.j8DataCanon_ok p _ Rt0 hgen).acs_pos (canonPb hpG (szOfClaim p) c).orbit χ) (chalVJ8 b χ)
      (pubVJ8 δ b c (msgC δ b hpG h hok χ).m (msgC δ b hpG h hok χ).ρ (msgC δ b hpG h hok χ).ρS χ)) j with hE
  have he : ∀ c' < 69, E.trace c' = HonestCompX.colX (DC p h).H (DC p h).pd
      (rowOfSkelX ((bfsForest [t])[j]'hjW).label) (flX j) (llX (bfsForest [t]) j) c' := by
    intro c' hc'
    have h123 : c' < 123 := by omega
    have key : ∀ (chalV pubVal : ℕ → ZMod p) (ln cnt acc : ℕ → K),
        (polyX b δ (DC p h).H (DC p h).pd (bfsForest [t]) chalV pubVal ln cnt acc
          (powN (canonPb hpG (szOfClaim p) c).orbit (bfsForest [t]).length) 123 ⟨c', h123⟩).eval
          (powN (canonPb hpG (szOfClaim p) c).orbit (bfsForest [t]).length ⟨j, hjW⟩) =
        baseT (DC p h).H (DC p h).pd (bfsForest [t]) j c' := fun chalV pubVal ln cnt acc =>
      (polyX_eval b δ _ _ _ chalV pubVal ln cnt acc _ hinj ⟨c', h123⟩ ⟨j, hjW⟩).trans
        (trX_base b δ _ _ _ chalV pubVal ln cnt acc j c' hc')
    rw [hE, TeleC.envsN, dif_pos hjn, TeleC.rEF]
    simp only [Reify.envOfTrace]
    split_ifs with hw
    · refine (key _ _ _ _ _).trans ?_
      unfold baseT
      rw [CanonSideP1.rowAtWX_eq _ j hjW]
    · exact absurd h123 hw
  obtain ⟨yr, hyr, k0, k1⟩ := pKey_row (K := K) (DC p h).H (DC p h).pd _ _ _ hokj hH E he x hxm
  refine ⟨_, List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hjn, List.mem_map.mpr ⟨yr, hyr, rfl⟩⟩, ?_, k1⟩
  -- the root key is the root's cell serial
  refine k0.trans ?_
  have hrowm : rowOfSkelX ((bfsForest [t])[j]'hjW).label ∈ (DC p h).rows.toList := by
    simp only [DC, CanonGenP1.j8DataCanon, J8Gen.j8DataGen, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hjW)
  obtain ⟨h2, hsl⟩ := Nock.Edit.GenX.consEntriesX_sound _ (Nock.Edit.GenX.inTree_rowSem hgen hin) x hxm
  have hroot := Nock.Edit.GenX.consEntriesX_root _ x hxm
  rcases J8Gen.handle_noun_casesG p _ Rt0 hgen CanonGenP1.ord8Canon hrowm hroot with
    ⟨⟨a, c2, hac⟩, hmem⟩ | ⟨v, ev, _⟩ | ⟨v, ev, _⟩
  · have hidx : ((DC p h).H x.1).2 = (DC p h).cells.idxOf x.1 := by
      show (ComplJ8Data.hdlP p (DC p h).cells (DC p h).acs x.1).2 = _
      rw [hac]
      simp only [ComplJ8Data.hdlP]
      rw [← hac, ComplJ8OfBal.genIdxOf_eq _ _ hmem]
    rw [hidx]
  · rw [ev, ComplJ8OfBalG.slot_atom_two h2] at hsl; cases hsl
  · rw [ev, ComplJ8OfBalG.slot_atom_two h2] at hsl; cases hsl

end Cover

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **(B) `canon_eq_closed`: every accepted transcript is the canonical one.** On a P1 claim (`P1FragC`) with the
size premise (`P1SizeOK`), at the canonical layout `canonPb hpG (szOfClaim p) c`, the empty registry, the verifier
rows `rowsP1` and budget `0`: a tuple accepted by `AcceptsCanonP1` at a coin `χ` that is good for the honest record
(`hχ`) and outside the absent-data events `allJ8X (dataP1 …)` at the tuple's trace (`hg`) and at the canonical
trace (`hgC`) IS the canonical triple. No other hypothesis. -/
theorem canon_eq_closed [CharP K p] [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} (hc : P1FragC c)
    (hok : P1SizeOK p c) {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (hacc : AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
      M tr ax (rowsP1 (canonPb hpG (szOfClaim p) c)) 0)
    (hχ : (BC δ b hpG h hok).Good χ)
    (hg : ∀ s ∈ allJ8X (dataP1 δ b hpG h hok), ¬ s.mem tr χ)
    (hgC : ∀ s ∈ allJ8X (dataP1 δ b hpG h hok), ¬ s.mem (trC δ b hpG h hok χ) χ) :
    (tr, ax, M) = canonOfP1 δ b hpG h hok χ :=
  canon_eq_closed' δ b hpG hc hok h hacc hχ hg hgC (hcovC_P1 δ b hpG hc hok h χ)

open Classical in
/-- **`trace_unique_prob_closed`:** for any staged prover strategy `Q`,
`Pr_χ[AcceptsCanonP1 (Q χ) at rowsP1, 0 ∧ Q χ ≠ canonOf χ] ≤ 2·ε(allJ8X (dataP1 …)) + ε_c`. -/
theorem trace_unique_prob_closed [CharP K p] [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {c : P8PublicClaim}
    (hc : P1FragC c) (hok : P1SizeOK p c) {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (Q : Coins frameJ8 K → TripP1 p K δ) (hQ : StJ8 fun χ => (Q χ).1) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
          (Q χ).2.2 (Q χ).1 (Q χ).2.1 (rowsP1 (canonPb hpG (szOfClaim p) c)) 0 ∧
        Q χ ≠ canonOfP1 δ b hpG h hok χ).card : ℚ) / Fintype.card (Coins frameJ8 K) ≤
      2 * epsilonOf (allJ8X (dataP1 δ b hpG h hok)) + (BC δ b hpG h hok).epsC :=
  trace_unique_prob_closed' δ b hpG hc hok h (hcovC_P1 δ b hpG hc hok h) Q hQ

open Classical in
/-- **Trace uniqueness on P1, with the figure.** For a claim `c` in the P1 fragment (`P1FragC`: formula ops among
`0, 7, 10` and cons, atoms `< p`, depth `≤ 60`, run defined) with the size premise `P1SizeOK p c`, at `|K| = cK` (the
Goldilocks cubic extension) and for every staged prover strategy `Q` (`StJ8`):
`Pr_χ[AcceptsCanonP1 … (Q χ) ∧ Q χ ≠ canonOfP1 … χ] < 2^-119`, where the verifier runs at the canonical layout
`canonPb`, rows `rowsP1`, budget `0` and the empty registry, and `canonOfP1 χ` is the honest generator's transcript. -/
theorem trace_unique_prob_119 [CharP K p] [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {c : P8PublicClaim}
    (hc : P1FragC c) (hok : P1SizeOK p c) {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (hcK : Fintype.card K = VclL.Events.cK)
    (Q : Coins frameJ8 K → TripP1 p K δ) (hQ : StJ8 fun χ => (Q χ).1) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
          (Q χ).2.2 (Q χ).1 (Q χ).2.1 (rowsP1 (canonPb hpG (szOfClaim p) c)) 0 ∧
        Q χ ≠ canonOfP1 δ b hpG h hok χ).card : ℚ) / Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 119 :=
  lt_of_le_of_lt (trace_unique_prob_closed δ b hpG hc hok h Q hQ) (fig_P1 δ b hpG hc hok h hcK)

open Classical in
/-- **Split form:** `Pr_χ[AcceptsCanonP1 (Q χ) ∧ Q χ ≠ canonOf χ] ≤ 2·ε(allJ8X (dataP1 …)) +
Pr_χ[¬ Good χ]`, with, at `|K| = cK`, the soundness term `2·ε < 2^-154` (`epsJ8X_lt_155_census32`) and the honest
failure term `Pr[¬ Good] ≤ ε_c < 2^-120` (`complJ8_P1`) as separate conjuncts. The factor `2` is the event mass
at `Q`'s trace plus the event mass at the canonical trace (`hgC` of `canon_eq_closed`); no lemma puts the canonical
trace outside `allJ8X (dataP1 …)` at a `Good` coin. -/
theorem trace_unique_prob_split [CharP K p] [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {c : P8PublicClaim}
    (hc : P1FragC c) (hok : P1SizeOK p c) {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (hcK : Fintype.card K = VclL.Events.cK)
    (Q : Coins frameJ8 K → TripP1 p K δ) (hQ : StJ8 fun χ => (Q χ).1) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
          (Q χ).2.2 (Q χ).1 (Q χ).2.1 (rowsP1 (canonPb hpG (szOfClaim p) c)) 0 ∧
        Q χ ≠ canonOfP1 δ b hpG h hok χ).card : ℚ) / Fintype.card (Coins frameJ8 K) ≤
      2 * epsilonOf (allJ8X (dataP1 δ b hpG h hok)) +
        ((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ (BC δ b hpG h hok).Good χ).card : ℚ) /
          Fintype.card (Coins frameJ8 K) ∧
    2 * epsilonOf (allJ8X (dataP1 δ b hpG h hok)) < 1 / (2 : ℚ) ^ 154 ∧
    ((Finset.univ.filter fun χ : Coins frameJ8 K => ¬ (BC δ b hpG h hok).Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 120 := by
  have hc' : P1FragC ⟨c.subject, c.formula, c.result⟩ := by cases c; exact hc
  obtain ⟨hfit, hsz⟩ := ClaimSizesP1.szOfClaim_eq p h hok
  set L := allJ8X (dataP1 δ b hpG h hok) with hLd
  set E1 := unionEvent L (fun χ => (Q χ).1)
  set E2 := unionEvent L (fun χ => trC δ b hpG h hok χ)
  set E3 := Finset.univ.filter fun χ : Coins frameJ8 K => ¬ (BC δ b hpG h hok).Good χ
  have hsub : (Finset.univ.filter fun χ : Coins frameJ8 K =>
        AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
          (Q χ).2.2 (Q χ).1 (Q χ).2.1 (rowsP1 (canonPb hpG (szOfClaim p) c)) 0 ∧
        Q χ ≠ canonOfP1 δ b hpG h hok χ) ⊆ E1 ∪ E2 ∪ E3 := by
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    by_contra hno
    simp only [Finset.mem_union, E1, E2, E3, unionEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      not_or, not_exists, not_and, not_not] at hno
    obtain ⟨⟨h1, h2⟩, h3⟩ := hno
    exact hχ.2 (canon_eq_closed δ b hpG hc hok h hχ.1 h3 (fun s hs' => h1 s hs') (fun s hs' => h2 s hs'))
  have hcard := Finset.card_le_card hsub
  have hu := (Finset.card_union_le (E1 ∪ E2) E3).trans (Nat.add_le_add_right (Finset.card_union_le E1 E2) _)
  have hpos : (0 : ℚ) < Fintype.card (Coins frameJ8 K) := by exact_mod_cast Fintype.card_pos
  have b1 := union_prob_le L (fun χ => (Q χ).1) hQ
  have b2 := union_prob_le L (fun χ => trC δ b hpG h hok χ) (trC_staged δ b hpG hc hok h)
  have b3 := (CanonSideP1.canon_complete' δ b (Rt := Rt0) hpG (runP1_gen h) hc' (hR31 h hok)
    ((ClaimSizesP1.P1SizeOK_of p h).mp hok).2 (szOfClaim p) hsz (K := K)).2
  have hr := hr_P1 hpG h hok
  have hN : 0 + (rowsP1 (canonPb hpG (szOfClaim p) c)).N ≤ 2 ^ 32 := by
    have := hr.1; simp only [EncInjJ8.cornerC, WeightsJ8.corner31] at this; omega
  have e1 := RepriceJ8.epsJ8X_lt_155_census32 (dataP1 δ b hpG h hok) hcK hr le_rfl hN
  have e2 := ((CanonCompleteP1.complJ8_P1 δ b (Rt := Rt0) hpG (runP1_gen h) hc' (hR31 h hok)
    ((ClaimSizesP1.P1SizeOK_of p h).mp hok).2 (K := K)).2.2.2.2 hcK).1
  have e2' : (BC δ b hpG h hok).epsC < 1 / 2 ^ 120 := e2
  refine ⟨?_, ?_, lt_of_le_of_lt b3 e2'⟩
  · calc _ ≤ ((E1.card + E2.card + E3.card : ℕ) : ℚ) / Fintype.card (Coins frameJ8 K) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hcard.trans hu) hpos.le
      _ = (E1.card : ℚ) / Fintype.card (Coins frameJ8 K) + (E2.card : ℚ) / Fintype.card (Coins frameJ8 K) +
          (E3.card : ℚ) / Fintype.card (Coins frameJ8 K) := by push_cast; ring
      _ ≤ epsilonOf L + epsilonOf L + (E3.card : ℚ) / Fintype.card (Coins frameJ8 K) :=
          add_le_add (add_le_add b1 b2) le_rfl
      _ = _ := by ring
  · calc 2 * epsilonOf L < 2 * (1 / (2 : ℚ) ^ 155) := by linarith
      _ = 1 / (2 : ℚ) ^ 154 := by norm_num

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.acceptsCanonP1_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.BC_rows_bad
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.canon_accepts_rowsP1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.canon_eq_closed'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.fig_P1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.trace_unique_prob_closed'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.pKey_row
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.hcovC_P1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.canon_eq_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.trace_unique_prob_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.trace_unique_prob_119
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1Closed.trace_unique_prob_split
