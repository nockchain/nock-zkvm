/-
  Nock/NockVMROM/Thm54/VclL/Handle/TwinGatesH.lean

  Additive.

  Both twins carry the same LogUp shape in `𝕂`: an inverse gate `inv · den − 1`, an accumulator
  `acc(0) = term(0)`, `acc(i+1) = acc(i) + term(i+1)`, terminal `acc(last) = pub`.
  * `rlcH_eval`, `denKey_eval`: the denominator of a record is `ρ + Σ γ^k · lift(key_k)`;
  * `cellH_gates_honest`: the 4 `CellH.gates` of `cellChipH` (term `mh · inv`) at the honest fill:
    inverses `den⁻¹`, inclusive prefix sums, the total as public;
  * `walkH_gates_honest`: the 9 `WalkHC.gates` of `walkChipH` (export consume `xInv`, provide terms
    `mL · inv_L + mR · inv_R`);
  * `den_bad_card`: the honest bad event (a record denominator vanishes at the pole coin `ρ`) has at
    most one `ρ` per record, so at most `1 · (cell rows) + 3 · (walk rows)` poles in all
    (`twin_den_bad_few`): a completeness summand, NOT a hypothesis;
  * `cellH_gates_wrong_pub`: NC, a terminal off by one fails the cell terminal gate.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkRecH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestMh

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

noncomputable section

section Gates
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- `rlcH m l` evaluates to `Σ_k γ^(m+k) · lift(l_k)`. -/
theorem rlcH_eval (eK : Env K) (eF : Env F) (m : ℕ) (l : List (CoeffExpr F)) :
    (CellH.rlcH m l).eval eK eF =
      ((l.zipIdx m).map (fun p : CoeffExpr F × ℕ => eK.chal CellH.hGam ^ p.2 * algebraMap F K (p.1.eval eF))).sum := by
  induction l generalizing m with
  | nil => simp [CellH.rlcH, MixedExpr.eval]
  | cons g r ih =>
    simp only [CellH.rlcH, MixedExpr.eval, List.zipIdx_cons, List.map_cons, List.sum_cons]
    rw [ih]

theorem denKey_eval (eK : Env K) (eF : Env F) (l : List (CoeffExpr F)) :
    (CellH.denKey l).eval eK eF =
      eK.chal CellH.hRho + ((l.zipIdx 0).map
        (fun p : CoeffExpr F × ℕ => eK.chal CellH.hGam ^ p.2 * algebraMap F K (p.1.eval eF))).sum := by
  simp only [CellH.denKey, MixedExpr.eval]
  rw [rlcH_eval]

/-- **The four cell-twin handle gates at the honest fill.**  Row `i < N` of an honest cell twin trace:
the inverse is `den⁻¹` (non-zero), the accumulator holds the inclusive prefix sum of `mh · inv`, the
public is the total. -/
theorem cellH_gates_honest (eK : Env K) (eF : Env F) (N i : ℕ) (hi : i < N)
    (m : ℕ → F) (d : ℕ → K) (hd0 : d i ≠ 0)
    (hF : eF.trace Cell.isF = if i = 0 then 1 else 0)
    (hL : eF.trace Cell.isL = if i + 1 = N then 1 else 0)
    (hm : eF.trace CellH.mh = m i) (hmn : i + 1 < N → eF.traceNext CellH.mh = m (i + 1))
    (hden : (CellH.denKey (CellH.keyH (F := F))).eval eK eF = d i)
    (hinv : eK.trace CellH.invH = (d i)⁻¹)
    (hinvn : i + 1 < N → eK.traceNext CellH.invH = (d (i + 1))⁻¹)
    (hacc : eK.trace CellH.accH = ∑ j ∈ Finset.range (i + 1), algebraMap F K (m j) * (d j)⁻¹)
    (haccn : i + 1 < N → eK.traceNext CellH.accH =
      ∑ j ∈ Finset.range (i + 2), algebraMap F K (m j) * (d j)⁻¹)
    (hpub : eK.pub CellH.pubH = ∑ j ∈ Finset.range N, algebraMap F K (m j) * (d j)⁻¹) :
    ∀ g ∈ (CellH.gates (F := F)), g.eval eK eF = 0 := by
  intro g hg
  simp only [CellH.gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · simp only [MixedExpr.eval, hden, hinv]
    rw [inv_mul_cancel₀ hd0]; simp
  · simp only [MixedExpr.eval, CoeffExpr.eval, hF, hm, hacc, hinv]
    by_cases h0 : i = 0
    · subst h0; simp
    · simp [h0]
  · simp only [MixedExpr.eval, CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · simp [hl]
    · have hlt : i + 1 < N := by omega
      simp only [hl, if_false, sub_zero, one_mul, mul_one, hmn hlt, hinvn hlt, haccn hlt, hacc]
      have : ∑ j ∈ Finset.range (i + 2), algebraMap F K (m j) * (d j)⁻¹ =
          ∑ j ∈ Finset.range (i + 1), algebraMap F K (m j) * (d j)⁻¹ +
            algebraMap F K (m (i + 1)) * (d (i + 1))⁻¹ := Finset.sum_range_succ _ _
      rw [this]; simp
  · simp only [MixedExpr.eval, CoeffExpr.eval, hL, hacc, hpub]
    by_cases hl : i + 1 = N
    · subst hl; simp [Finset.sum_range_succ]
    · simp [hl]

/-- NC: a terminal off by one fails the cell terminal gate on the last row. -/
theorem cellH_gates_wrong_pub (eK : Env K) (eF : Env F) (N i : ℕ) (hlast : i + 1 = N)
    (m : ℕ → F) (d : ℕ → K)
    (hL : eF.trace Cell.isL = 1)
    (hacc : eK.trace CellH.accH = ∑ j ∈ Finset.range N, algebraMap F K (m j) * (d j)⁻¹)
    (hpub : eK.pub CellH.pubH = ∑ j ∈ Finset.range N, algebraMap F K (m j) * (d j)⁻¹ + 1) :
    ∃ g ∈ (CellH.gates (F := F)), g.eval eK eF ≠ 0 := by
  refine ⟨.Scale (cv Cell.isL) ((MixedExpr.Var VarKind.traceCur CellH.accH).Sub
    (MixedExpr.Var VarKind.publicVal CellH.pubH)), by simp [CellH.gates], ?_⟩
  simp [MixedExpr.eval, CoeffExpr.eval, hL, hacc, hpub]

/-- **The nine walk-twin handle gates at the honest fill.**  Row `i < N`: the three inverses are the
(non-zero) `den⁻¹` of the consumed export record and of the two provided handle records; the two
accumulators hold inclusive prefix sums of `xInv` and of `mL · invL + mR · invR`; the publics are the
totals. -/
theorem walkH_gates_honest (eK : Env K) (eF : Env F) (N i : ℕ) (hi : i < N)
    (mL mR : ℕ → F) (xd pdL pdR : ℕ → K) (hx0 : xd i ≠ 0) (hL0 : pdL i ≠ 0) (hR0 : pdR i ≠ 0)
    (hF : eF.trace WChip.isF = if i = 0 then 1 else 0)
    (hL : eF.trace WChip.isL = if i + 1 = N then 1 else 0)
    (hmL : eF.trace WChip.mL = mL i) (hmR : eF.trace WChip.mR = mR i)
    (hmLn : i + 1 < N → eF.traceNext WChip.mL = mL (i + 1))
    (hmRn : i + 1 < N → eF.traceNext WChip.mR = mR (i + 1))
    (hdx : (CellH.denKey (WalkHC.xKeyH (F := F))).eval eK eF = xd i)
    (hdL : (CellH.denKey (WalkHC.recLH (F := F))).eval eK eF = pdL i)
    (hdR : (CellH.denKey (WalkHC.recRH (F := F))).eval eK eF = pdR i)
    (hxi : eK.trace WalkHC.hxInv = (xd i)⁻¹)
    (hxin : i + 1 < N → eK.traceNext WalkHC.hxInv = (xd (i + 1))⁻¹)
    (hpL : eK.trace WalkHC.hpInvL = (pdL i)⁻¹) (hpR : eK.trace WalkHC.hpInvR = (pdR i)⁻¹)
    (hpLn : i + 1 < N → eK.traceNext WalkHC.hpInvL = (pdL (i + 1))⁻¹)
    (hpRn : i + 1 < N → eK.traceNext WalkHC.hpInvR = (pdR (i + 1))⁻¹)
    (hxa : eK.trace WalkHC.hxAcc = ∑ j ∈ Finset.range (i + 1), (xd j)⁻¹)
    (hxan : i + 1 < N → eK.traceNext WalkHC.hxAcc = ∑ j ∈ Finset.range (i + 2), (xd j)⁻¹)
    (hpa : eK.trace WalkHC.hpAcc = ∑ j ∈ Finset.range (i + 1),
      (algebraMap F K (mL j) * (pdL j)⁻¹ + algebraMap F K (mR j) * (pdR j)⁻¹))
    (hpan : i + 1 < N → eK.traceNext WalkHC.hpAcc = ∑ j ∈ Finset.range (i + 2),
      (algebraMap F K (mL j) * (pdL j)⁻¹ + algebraMap F K (mR j) * (pdR j)⁻¹))
    (hpx : eK.pub WalkHC.pubX = ∑ j ∈ Finset.range N, (xd j)⁻¹)
    (hpp : eK.pub WalkHC.pubP = ∑ j ∈ Finset.range N,
      (algebraMap F K (mL j) * (pdL j)⁻¹ + algebraMap F K (mR j) * (pdR j)⁻¹)) :
    ∀ g ∈ (WalkHC.gates (F := F)), g.eval eK eF = 0 := by
  intro g hg
  simp only [WalkHC.gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [MixedExpr.eval, hdx, hxi]; rw [inv_mul_cancel₀ hx0]; simp
  · simp only [MixedExpr.eval, hdL, hpL]; rw [inv_mul_cancel₀ hL0]; simp
  · simp only [MixedExpr.eval, hdR, hpR]; rw [inv_mul_cancel₀ hR0]; simp
  · simp only [MixedExpr.eval, CoeffExpr.eval, hF, hxa, hxi]
    by_cases h0 : i = 0
    · subst h0; simp
    · simp [h0]
  · simp only [MixedExpr.eval, CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · simp [hl]
    · have hlt : i + 1 < N := by omega
      simp only [hl, if_false, sub_zero, hxan hlt, hxin hlt, hxa]
      rw [Finset.sum_range_succ _ (i + 1)]; simp
  · simp only [MixedExpr.eval, CoeffExpr.eval, hL, hxa, hpx]
    by_cases hl : i + 1 = N
    · subst hl; simp [Finset.sum_range_succ]
    · simp [hl]
  · simp only [WalkHC.pTermH, if_true, MixedExpr.eval, CoeffExpr.eval, hF, hpa, hmL, hmR, hpL, hpR]
    by_cases h0 : i = 0
    · subst h0; simp
    · simp [h0]
  · simp only [WalkHC.pTermH, Bool.false_eq_true, if_false, MixedExpr.eval, CoeffExpr.eval, hL]
    by_cases hl : i + 1 = N
    · simp [hl]
    · have hlt : i + 1 < N := by omega
      simp only [hl, if_false, sub_zero, if_neg Bool.false_ne_true, hmLn hlt, hmRn hlt, hpLn hlt,
        hpRn hlt, hpan hlt, hpa]
      rw [Finset.sum_range_succ _ (i + 1)]; simp
  · simp only [MixedExpr.eval, CoeffExpr.eval, hL, hpa, hpp]
    by_cases hl : i + 1 = N
    · subst hl; simp [Finset.sum_range_succ]
    · simp [hl]

end Gates

/-! ## The honest bad event: a record denominator vanishes at the pole coin -/

section Bad
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- **At most one pole per record.**  For a list `r` of record RLC values (at fixed `γ`), the coins `ρ` with
`ρ + x = 0` for some `x ∈ r` number at most `|r|`.  With `r` the RLCs of the `cells` provided/consumed export
records and the `3 · walkrows` walk records, this prices the only event outside which every twin inverse
exists (`cellH_gates_honest`, `walkH_gates_honest` need `den ≠ 0`): a completeness summand, not a
hypothesis. -/
theorem den_bad_card (r : List K) :
    (Finset.univ.filter fun ρ : K => ∃ x ∈ r, ρ + x = 0).card ≤ r.length := by
  have hsub : (Finset.univ.filter fun ρ : K => ∃ x ∈ r, ρ + x = 0) ⊆ r.toFinset.image (fun x => -x) := by
    intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    obtain ⟨x, hx, h⟩ := hρ
    exact Finset.mem_image.mpr ⟨x, List.mem_toFinset.mpr hx, by rw [eq_neg_of_add_eq_zero_left h]⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (List.toFinset_card_le r))

theorem den_ne_zero_of_not_bad (r : List K) {ρ x : K} (hx : x ∈ r)
    (hρ : ρ ∉ (Finset.univ.filter fun ρ : K => ∃ x ∈ r, ρ + x = 0)) : ρ + x ≠ 0 := by
  intro h
  exact hρ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x, hx, h⟩)

end Bad

/-! ## The cell twin's terminal is the consumed total -/

section CellTerminal
open Nock.NockVMROM.Thm54.TraceGen
variable {F L R : Type} [Field F] [Field L] [Algebra F L] [DecidableEq F] [Field R]

/-- **The cell twin's honest public is the compute side's consumed export total.**  The inclusive sum
`Σ_j mh_j · den_j⁻¹` over the closure rows (the terms `cellH_gates_honest` accumulates, with `mh = mhH`
and `den = recDen ρ γ (expKey _ _)`, the denominator `ρ + RLC_γ` of the row's export key) equals
`Σ 1/den` over the records the compute rows consume.  Through `export_total_link_inv`. -/
theorem cell_terminal_is_consumed (rows : List (GenComputeRow R))
    (hsem : ∀ g ∈ rows, (rowOfSkel g.skel).Sem)
    (hlen : (demandH rows).cells.length < ringChar F) (ρ γ : L) :
    ∑ j ∈ Finset.range (demandH rows).cells.length,
      algebraMap F L ((mhH (F := F) rows ((demandH rows).cells.getD j (.atom 0)) : ℕ) : F) *
        (recDen ρ γ (expKey (F := F) (demandH rows).cells ((demandH rows).cells.getD j (.atom 0))))⁻¹ =
    ((consumedH (F := F) rows).map fun k => (recDen ρ γ k)⁻¹).sum := by
  rw [export_total_link_inv rows hsem hlen ρ γ]
  rw [← sum_range_getD (demandH rows).cells (.atom 0)
    (fun n => (mhH (F := F) rows n : L) * (recDen ρ γ (expKey (F := F) (demandH rows).cells n))⁻¹)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

end CellTerminal

end

end Nock.NockVMROM.Thm54.VclL.Handle
