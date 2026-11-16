/-
  Nock/Jet/ChipJ8THonestRAP.lean

The honest trace is built in closed form from a list of J-3b rows `rows : Fin n → CRow (ZMod p)`
  (the public layout is `layJ rows`, the rows' `pre` parts), following HC3's pattern (base columns, then
  the slot inverses, then prefix sums):
  * base columns `0..28`: the layout (`jetPre`, so the 18 verifier-fixed columns are bound by
    construction) and the witness columns `18..28` of the row;
  * `𝕂′` roles (`𝕂`-roles `0..13`, columns `29..70`, Re / Im as `Quad.re / Quad.im`): the four tagged
    slot inverses `sT es r = Σ_{κ ∈ keysOf es r} den(κ)⁻¹` at the J tagged coins `coinsJ` (a slot holds
    at most one key, so this is `den⁻¹` or `0`), the export-read inverse `sX` at `coinsJX`, and the two
    accumulators as INCLUSIVE prefix sums of the row terms `termJ r` (`= Σ cons den⁻¹ − mv · Σ prov
    den⁻¹ − m · Σ jet den⁻¹`, `RapJetJ8.termT_eq`'s right side) and `sX r`.

  **`jetChipJ8_honest_sat`**: `RAP.SatisfiesWithPreprocessing (jetChipJ8 …) (polyJ …)` from
  * J-3b's base gates on every row (`hgate`);
  * no tagged / export key denominator vanishes at the coins (`hpT`, `hpX`: the honest coins lie outside
    the pole events);
  * the publics: `(pub₀, pub₁) = Σ_i termJ (rows i)` (the J terminal) and `(pub₂, pub₃) = Σ_i sX (rows i)`
    (the export sum);
  * the orbit facts `hinj`, `hadj`, `0 < n`.
  The closed form of the J terminal under the `mv` fix and the verifier-side registry pins is
  `ChipJ8THonestBal.termJ_sum_of_mv`.
-/
import Nock.Jet.RapJetJ8
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.Jet.ChipJ8T.HonestRAP

open Nock Nock.Noun Nock.Jet Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8
open Nock.Framework Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The slot gate at the honest inverse -/

section Slot
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- A `𝕂′` equation with value `0` has both `𝕂`-gates `0`. -/
theorem gates_of_ev' (e : QE F) (eK : Env K) (eF : Env F) (h : e.ev δ eK eF = 0) :
    ∀ g ∈ e.gates, g.eval eK eF = 0 := by
  rw [QE.ev, Quad.mk_eq_zero_iff] at h
  intro g hg
  simp only [QE.gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact h.1
  · exact h.2

/-- **The slot lemma, honest direction** (converse of `RapJetJ8.slot_val`): under one-hot selectors,
with the inverse role set to `Σ_{keys} den⁻¹` and no vanishing denominator, the slot gate holds and
`Σ sel · inv = Σ_{keys} den⁻¹`. -/
theorem slot_honest (eK : Env K) (eF : Env F) (r : CRow F) (g ρ : QE F) (inv m : ℕ)
    (es : List (Kd × List KE)) (c : IOCoins 𝕂′)
    (hc : (⟨g.ev δ eK eF, ρ.ev δ eK eF⟩ : IOCoins 𝕂′) = c)
    (hsel : ∀ k : Kd, eF.trace k.sel = if k = r.pre.kd then 1 else 0)
    (hnd : (es.map Prod.fst).Nodup)
    (hes : ∀ e ∈ es, e.2.length ≤ m ∧ ∀ x ∈ e.2, x.expr.eval eF = KE.ev (colOf r) x)
    (hne : ∀ κ ∈ keysOf es r, compress c (liftRec (L := 𝕂′) (keyK (K := K) m κ)) ≠ 0)
    (hinv : Quad.mk _ (eK.trace inv) (eK.trace (inv + 1)) =
      ((keysOf es r).map fun κ => (compress c (liftRec (L := 𝕂′) (keyK (K := K) m κ)))⁻¹).sum) :
    (slotGate δ g ρ inv es).ev δ eK eF = 0 ∧
    liftQ δ ((ChipJ8.selSum cv es).eval eF) * Quad.mk _ (eK.trace inv) (eK.trace (inv + 1)) =
      ((keysOf es r).map fun κ => (compress c (liftRec (L := 𝕂′) (keyK (K := K) m κ)))⁻¹).sum := by
  set D : List F → 𝕂′ := fun κ => compress c (liftRec (L := 𝕂′) (keyK (K := K) m κ)) with hD
  have hden : ∀ e ∈ es, (denJ δ g ρ e.2).ev δ eK eF = D (e.2.map (KE.ev (colOf r))) := fun e he => by
    rw [denJ_val δ eK eF g ρ (colOf r) m e.2 (hes e he).1 (hes e he).2, hc]
  have hsel' : ∀ k, (fun k : Kd => eF.trace k.sel) k = if k = r.pre.kd then 1 else 0 := hsel
  have hsum : (ChipJ8.selSum (cv (F := F)) es).eval eF =
      ((es.filter fun e => e.1 == r.pre.kd).length : F) := by
    rw [ChipJ8.selSum, CoeffExpr.eval_sumList]
    exact sel_count r.pre.kd _ hsel' es
  have hg2 : (es.map fun e => (QE.scale (cv e.1.sel) (denJ δ g ρ e.2)).ev δ eK eF) =
      es.map fun e => liftQ δ (eF.trace e.1.sel) * D (e.2.map (KE.ev (colOf r))) := by
    refine List.map_congr_left fun e he => ?_
    rw [ev_scale, hden e he]; rfl
  have hk : keysOf es r =
      (es.filter fun e => e.1 == r.pre.kd).map fun e => e.2.map (KE.ev (colOf r)) := rfl
  have hval : (slotGate δ g ρ inv es).ev δ eK eF =
      Quad.mk _ (eK.trace inv) (eK.trace (inv + 1)) *
        ((es.filter fun e => e.1 == r.pre.kd).map fun e => D (e.2.map (KE.ev (colOf r)))).sum
        - liftQ δ (((es.filter fun e => e.1 == r.pre.kd).length : F)) := by
    unfold slotGate
    rw [ev_sub, ev_mul, ev_var, sumQE_ev, ev_base, hsum, List.map_map, Function.comp_def, hg2,
      sum_sel_filter δ r.pre.kd _ hsel' (fun e => D (e.2.map (KE.ev (colOf r)))) es]
  rw [hval, hsum]
  rw [hk] at hinv hne ⊢
  rcases filter_le_one r.pre.kd es hnd with h0 | ⟨e, he, -, h1⟩
  · rw [h0] at hinv ⊢
    simp only [List.map_nil, List.sum_nil] at hinv
    simp [hinv, liftQ]
  · rw [h1] at hinv hne ⊢
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.length_singleton, Nat.cast_one] at hinv hne ⊢
    have hne' := hne _ (List.mem_singleton_self _)
    have h1' : liftQ (K := K) δ (1 : F) = 1 := by simp [liftQ]
    rw [h1', hinv, inv_mul_cancel₀ hne', one_mul]
    exact ⟨sub_self _, rfl⟩

end Slot

/-! ## 2. The honest `𝕂′` values -/

section Values
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (chals : ℕ → K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- A tagged slot's honest inverse: `Σ_{κ ∈ keysOf es r} den(κ)⁻¹` at the J tagged coins. -/
def sT (es : List (Kd × List KE)) (r : CRow (ZMod p)) : 𝕂′ := ((keysOf es r).map (dJ δ chals)).sum

/-- The export slot's honest inverse at the J export coins. -/
def sX (r : CRow (ZMod p)) : 𝕂′ := ((keysOf entsX r).map (dJX δ chals)).sum

/-- **The tagged accumulator's row term**: consumes `+1`, in-chip provides `−mv`, the service
provide `−m`. -/
def termJ (r : CRow (ZMod p)) : 𝕂′ :=
  sT δ chals ents0T r + sT δ chals ents1T r - liftQ δ r.w.mv * sT δ chals ents2T r
    - liftQ δ r.w.m * sT δ chals ents3 r

theorem termJ_eq (r : CRow (ZMod p)) :
    termJ δ chals r = ((consKT r).map (dJ δ chals)).sum
      - liftQ δ r.w.mv * ((provKT r).map (dJ δ chals)).sum
      - liftQ δ r.w.m * ((keysOf ents3 r).map (dJ δ chals)).sum := by
  simp only [termJ, sT, consKT, provKT, List.map_append, List.sum_append]

end Values

/-! ## 3. The honest trace -/

section Trace
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K) (chals : ℕ → K)
  {n : ℕ} (rows : Fin n → CRow (ZMod p))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The public layout of the rows. -/
def layJ : Fin n → PRow := fun i => (rows i).pre

def tN (i : ℕ) : 𝕂′ := if h : i < n then termJ δ chals (rows ⟨i, h⟩) else 0
def xN (i : ℕ) : 𝕂′ := if h : i < n then sX δ chals (rows ⟨i, h⟩) else 0

/-- **The tagged accumulator**: the inclusive prefix sum of the row terms. -/
def accT (i : ℕ) : 𝕂′ := ∑ j ∈ Finset.range (i + 1), tN δ chals rows j
/-- **The export accumulator**: the inclusive prefix sum of the export-read terms. -/
def accX (i : ℕ) : 𝕂′ := ∑ j ∈ Finset.range (i + 1), xN δ chals rows j

/-- The seven `𝕂′` columns (`inv0 inv1 inv2 inv3 invX accT accX`) of row `i`. -/
def qv (s : ℕ) (i : Fin n) : 𝕂′ :=
  match s with
  | 0 => sT δ chals ents0T (rows i)
  | 1 => sT δ chals ents1T (rows i)
  | 2 => sT δ chals ents2T (rows i)
  | 3 => sT δ chals ents3 (rows i)
  | 4 => sX δ chals (rows i)
  | 5 => accT δ chals rows i
  | 6 => accX δ chals rows i
  | _ => 0

/-- `𝕂`-role `r` of row `i`: Re / Im of `𝕂′` column `r / 2`. -/
def roleV (r : ℕ) (i : Fin n) : K :=
  if r % 2 = 0 then Quad.re _ (qv δ chals rows (r / 2) i) else Quad.im _ (qv δ chals rows (r / 2) i)

/-- **The honest column function**: layout (`< 18`), witness (`18..28`), `𝕂`-role limbs (`29..70`). -/
def colJ (c : ℕ) (i : Fin n) : ZMod p :=
  if c < 18 then jetPre (layJ rows) c i
  else if c < 29 then colOf (rows i) c
  else coordN b (roleV δ chals rows ((c - 29) / 3) i) (c - 29)

/-- **The honest trace polynomials** (Lagrange interpolation over the row nodes). -/
def polyJ (nodes : Fin n → ZMod p) (w : ℕ) : Fin w → (ZMod p)[X] := fun c =>
  Lagrange.interpolate Finset.univ nodes (fun i => colJ δ b chals rows c i)

theorem tN_fin (i : Fin n) : tN δ chals rows i = termJ δ chals (rows i) := by
  simp [tN, i.isLt]

theorem xN_fin (i : Fin n) : xN δ chals rows i = sX δ chals (rows i) := by
  simp [xN, i.isLt]

theorem accT_zero : accT δ chals rows 0 = tN δ chals rows 0 := by simp [accT]
theorem accX_zero : accX δ chals rows 0 = xN δ chals rows 0 := by simp [accX]

theorem accT_succ (j : ℕ) : accT δ chals rows (j + 1) = accT δ chals rows j + tN δ chals rows (j + 1) := by
  simp only [accT]; rw [Finset.sum_range_succ]

theorem accX_succ (j : ℕ) : accX δ chals rows (j + 1) = accX δ chals rows j + xN δ chals rows (j + 1) := by
  simp only [accX]; rw [Finset.sum_range_succ]

theorem accT_last (hn : 0 < n) : accT δ chals rows (n - 1) = ∑ i, termJ δ chals (rows i) := by
  simp only [accT, show n - 1 + 1 = n by omega]
  rw [← Fin.sum_univ_eq_sum_range (tN δ chals rows) n]
  exact Finset.sum_congr rfl fun i _ => tN_fin δ chals rows i

theorem accX_last (hn : 0 < n) : accX δ chals rows (n - 1) = ∑ i, sX δ chals (rows i) := by
  simp only [accX, show n - 1 + 1 = n by omega]
  rw [← Fin.sum_univ_eq_sum_range (xN δ chals rows) n]
  exact Finset.sum_congr rfl fun i _ => xN_fin δ chals rows i

theorem colJ_pre {c : ℕ} (hc : c < 18) (i : Fin n) : colJ δ b chals rows c i = jetPre (layJ rows) c i := by
  simp [colJ, hc]

theorem colJ_base {c : ℕ} (hc : c < 29) (h11 : c ≠ 11) (h12 : c ≠ 12) (i : Fin n) :
    colJ δ b chals rows c i = colOf (rows i) c := by
  by_cases h18 : c < 18
  · rw [colJ_pre δ b chals rows h18]
    interval_cases c <;> simp_all [colOf, jetPre, preCol, layJ] <;> rfl
  · simp [colJ, h18, hc]

theorem colJ_role {r : ℕ} (hr : r < 14) (k : Fin 3) (i : Fin n) :
    colJ δ b chals rows (29 + 3 * r + k) i = coord b (roleV δ chals rows r i) k := by
  have hk := k.isLt
  simp only [colJ, if_neg (show ¬ (29 + 3 * r + (k : ℕ) < 18) by omega),
    if_neg (show ¬ (29 + 3 * r + (k : ℕ) < 29) by omega),
    show (29 + 3 * r + (k : ℕ) - 29) / 3 = r by omega]
  unfold coordN
  congr 1
  exact Fin.ext (by simp; omega)

theorem roleV_pair (s : ℕ) (i : Fin n) :
    Quad.mk _ (roleV δ chals rows (2 * s) i) (roleV δ chals rows (2 * s + 1) i) = qv δ chals rows s i := by
  simp only [roleV, show (2 * s) % 2 = 0 by omega, show (2 * s + 1) % 2 = 1 by omega,
    show (2 * s) / 2 = s by omega, show (2 * s + 1) / 2 = s by omega, if_true, one_ne_zero, if_false]
  exact Quad.mk_re_im _ _

end Trace

/-! ## 4. The row environments of the honest trace -/

/-- The honest trace at the chip's width. -/
abbrev polyJC {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
    [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)
    {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
    (rows : Fin n → CRow (ZMod p)) :
    Fin (jetChipJ8 δ b nodes orbit chals pubs (layJ rows)).rap.w → (ZMod p)[X] :=
  polyJ δ b chals rows nodes _

section Env
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)
  {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (rows : Fin n → CRow (ZMod p))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "PJ" => polyJC δ b nodes orbit chals pubs rows
local notation "EF" => jEF b nodes orbit chals pubs PJ
local notation "EK" => jEK δ b nodes orbit chals pubs PJ

theorem EF_trace (hinj : Function.Injective nodes) (i : Fin n) {c : ℕ} (hc : c < 71) :
    (EF i).trace c = colJ δ b chals rows c i := by
  have hw : (jetChipJ8 δ b nodes orbit chals pubs (layJ rows)).rap.w = 71 :=
    jetChipJ8_width δ b nodes orbit chals pubs (layJ rows)
  show (Reify.envOfTrace PJ orbit.ω (nodes i) (slotVal b 29 chals) (slotVal b 29 pubs)).trace c = _
  rw [envOfTrace_trace _ _ _ _ _ (show c < (jetChipJ8 δ b nodes orbit chals pubs (layJ rows)).rap.w by
    rw [hw]; exact hc)]
  exact Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

theorem EK_trace (hinj : Function.Injective nodes) (i : Fin n) {r : ℕ} (hr : r < 14) :
    (EK i).trace r = roleV δ chals rows r i := by
  show (gatherEnv b ((jetTemplateJ8T δ).col0 3) (EF i)).trace r = _
  have hv : ∀ k : Fin 3, (EF i).trace (29 + 3 * r + k) = coord b (roleV δ chals rows r i) k := fun k => by
    have := k.isLt
    rw [EF_trace δ b nodes orbit chals pubs rows hinj i (by omega), colJ_role δ b chals rows hr k i]
  simp only [gatherEnv, ChipTemplate.col0, jetTemplateJ8T_baseCols, hv, coord]
  exact b.sum_repr _

theorem qK (hinj : Function.Injective nodes) (i : Fin n) (s : ℕ) (hs : s < 7) :
    Quad.mk _ ((EK i).trace (2 * s)) ((EK i).trace (2 * s + 1)) = qv δ chals rows s i := by
  rw [EK_trace δ b nodes orbit chals pubs rows hinj i (by omega),
    EK_trace δ b nodes orbit chals pubs rows hinj i (by omega)]
  exact roleV_pair δ chals rows s i

theorem EF_first (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace 11 = if (i : ℕ) = 0 then 1 else 0 := by
  rw [EF_trace δ b nodes orbit chals pubs rows hinj i (by norm_num), colJ_pre δ b chals rows (by norm_num)]
  simp [jetPre]

theorem EF_last (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace 12 = if (i : ℕ) = n - 1 then 1 else 0 := by
  rw [EF_trace δ b nodes orbit chals pubs rows hinj i (by norm_num), colJ_pre δ b chals rows (by norm_num)]
  simp [jetPre]

theorem EF_sel (hinj : Function.Injective nodes) (i : Fin n) (k : Kd) :
    (EF i).trace k.sel = if k = (rows i).pre.kd then 1 else 0 := by
  have h0 : k.sel < 11 := by cases k <;> decide
  rw [EF_trace δ b nodes orbit chals pubs rows hinj i (by omega), colJ_pre δ b chals rows (by omega)]
  have h11 : k.sel ≠ 11 := by omega
  have h12 : k.sel ≠ 12 := by omega
  simp only [jetPre, if_neg h11, if_neg h12, preCol, if_pos h0, layJ]
  have key : ∀ k kd : Kd, ((if kd.sel = k.sel then (1 : ZMod p) else 0) = if k = kd then 1 else 0) := by
    intro k kd; cases k <;> cases kd <;> simp [Kd.sel]
  convert key k (rows i).pre.kd using 2 <;> rfl

theorem EF_col (hinj : Function.Injective nodes) (i : Fin n) {c : ℕ} (hc : c < 29) (h11 : c ≠ 11)
    (h12 : c ≠ 12) : (EF i).trace c = colOf (rows i) c := by
  rw [EF_trace δ b nodes orbit chals pubs rows hinj i (by omega), colJ_base δ b chals rows hc h11 h12]

theorem hes_honest (hinj : Function.Injective nodes) (i : Fin n) {m : ℕ} {es : List (Kd × List KE)}
    (hok : colsOK m es = true) :
    ∀ e ∈ es, e.2.length ≤ m ∧ ∀ x ∈ e.2, x.expr.eval (EF i) = KE.ev (colOf (rows i)) x := by
  intro e he
  have h1 := List.all_eq_true.mp hok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨h1.1, fun x hx => ?_⟩
  have h2 := List.all_eq_true.mp h1.2 x hx
  cases x with
  | col j =>
    simp only [decide_eq_true_eq] at h2
    simp only [KE.expr, KE.ev, cv, CoeffExpr.eval]
    exact EF_col δ b nodes orbit chals pubs rows hinj i h2.1 h2.2.1 h2.2.2
  | k c => simp [KE.expr, KE.ev, CoeffExpr.eval]

/-- J-3b's base gates on the honest row environment. -/
theorem base_honest (hinj : Function.Injective nodes) (i : Fin n)
    (hgate : ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (envOf (rows i)) = 0) :
    ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (EF i) = 0 := by
  have c := fun j (hj : j < 29) (h11 : j ≠ 11) (h12 : j ≠ 12) =>
    EF_col δ b nodes orbit chals pubs rows hinj i hj h11 h12
  have e2 := c 2 (by norm_num) (by norm_num) (by norm_num)
  have e3 := c 3 (by norm_num) (by norm_num) (by norm_num)
  have e4 := c 4 (by norm_num) (by norm_num) (by norm_num)
  have e5 := c 5 (by norm_num) (by norm_num) (by norm_num)
  have e6 := c 6 (by norm_num) (by norm_num) (by norm_num)
  have e7 := c 7 (by norm_num) (by norm_num) (by norm_num)
  have e16 := c 16 (by norm_num) (by norm_num) (by norm_num)
  have e20 := c 20 (by norm_num) (by norm_num) (by norm_num)
  have e21 := c 21 (by norm_num) (by norm_num) (by norm_num)
  have e22 := c 22 (by norm_num) (by norm_num) (by norm_num)
  have e23 := c 23 (by norm_num) (by norm_num) (by norm_num)
  intro g hg
  have := hgate g hg
  simp only [baseGatesJ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
  · simp only [CoeffExpr.eval, envOf, cv, Kd.sel, Col.val, Col.n1, Col.v1, Col.v2, Col.kN] at this ⊢
    simp only [e2, e3, e4, e5, e6, e7, e16, e20, e21, e22, e23]
    exact this

/-- A tagged slot of row `i` at the honest inverse. -/
theorem slotRowT (hinj : Function.Injective nodes) (i : Fin n) (inv : ℕ) (es : List (Kd × List KE))
    (hnd : (es.map Prod.fst).Nodup) (hok : colsOK 8 es = true)
    (hne : ∀ κ ∈ keysOf es (rows i), compress (coinsJ δ chals) (liftRec (keyK (K := K) 8 κ)) ≠ 0)
    (hinv : Quad.mk _ ((EK i).trace inv) ((EK i).trace (inv + 1)) = sT δ chals es (rows i)) :
    (slotGate δ gamT rhoT inv es).ev δ (EK i) (EF i) = 0 ∧
    liftQ δ ((ChipJ8.selSum cv es).eval (EF i)) * Quad.mk _ ((EK i).trace inv) ((EK i).trace (inv + 1)) =
      sT δ chals es (rows i) :=
  slot_honest δ (EK i) (EF i) (rows i) gamT rhoT inv 8 es (coinsJ δ chals) (coinsJ_ev i)
    (EF_sel δ b nodes orbit chals pubs rows hinj i) hnd
    (hes_honest δ b nodes orbit chals pubs rows hinj i hok) hne hinv

/-- The export slot of row `i` at the honest inverse. -/
theorem slotRowX (hinj : Function.Injective nodes) (i : Fin n)
    (hne : ∀ κ ∈ keysOf entsX (rows i), compress (coinsJX δ chals) (liftRec (keyK (K := K) 5 κ)) ≠ 0) :
    (slotGate δ gamX rhoX Col.invX entsX).ev δ (EK i) (EF i) = 0 ∧
    liftQ δ ((ChipJ8.selSum cv entsX).eval (EF i)) *
        Quad.mk _ ((EK i).trace Col.invX) ((EK i).trace (Col.invX + 1)) = sX δ chals (rows i) :=
  slot_honest δ (EK i) (EF i) (rows i) gamX rhoX Col.invX 5 entsX (coinsJX δ chals) (coinsJX_ev i)
    (EF_sel δ b nodes orbit chals pubs rows hinj i) kinds_nodup.2.2.2.2
    (hes_honest δ b nodes orbit chals pubs rows hinj i colsOK_all.2.2.2.2) hne
    (qK δ b nodes orbit chals pubs rows hinj i 4 (by norm_num))

/-- The four tagged slots of row `i`, and the row's tagged-accumulator term in closed form. -/
theorem rowT (hinj : Function.Injective nodes) (i : Fin n)
    (hpT : ∀ κ ∈ consKT (rows i) ++ provKT (rows i) ++ keysOf ents3 (rows i),
      compress (coinsJ δ chals) (liftRec (keyK (K := K) 8 κ)) ≠ 0) :
    (∀ e ∈ [slotGate δ gamT rhoT Col.inv0 ents0T, slotGate δ gamT rhoT Col.inv1 ents1T,
      slotGate δ gamT rhoT Col.inv2 ents2T, slotGate δ gamT rhoT Col.inv3 ents3],
        e.ev δ (EK i) (EF i) = 0) ∧
    (contribT cv QE.var).ev δ (EK i) (EF i) = termJ δ chals (rows i) := by
  have hm : ∀ κ, κ ∈ keysOf ents0T (rows i) ∨ κ ∈ keysOf ents1T (rows i) ∨ κ ∈ keysOf ents2T (rows i) ∨
      κ ∈ keysOf ents3 (rows i) → compress (coinsJ δ chals) (liftRec (keyK (K := K) 8 κ)) ≠ 0 := by
    intro κ hκ
    refine hpT κ ?_
    simp only [consKT, provKT, List.mem_append]
    tauto
  obtain ⟨g0, s0⟩ := slotRowT δ b nodes orbit chals pubs rows hinj i Col.inv0 ents0T kinds_nodup.1
    colsOK_all.1 (fun κ h => hm κ (Or.inl h)) (qK δ b nodes orbit chals pubs rows hinj i 0 (by norm_num))
  obtain ⟨g1, s1⟩ := slotRowT δ b nodes orbit chals pubs rows hinj i Col.inv1 ents1T kinds_nodup.2.1
    colsOK_all.2.1 (fun κ h => hm κ (Or.inr (Or.inl h))) (qK δ b nodes orbit chals pubs rows hinj i 1 (by norm_num))
  obtain ⟨g2, s2⟩ := slotRowT δ b nodes orbit chals pubs rows hinj i Col.inv2 ents2T kinds_nodup.2.2.1
    colsOK_all.2.2.1 (fun κ h => hm κ (Or.inr (Or.inr (Or.inl h))))
    (qK δ b nodes orbit chals pubs rows hinj i 2 (by norm_num))
  obtain ⟨g3, s3⟩ := slotRowT δ b nodes orbit chals pubs rows hinj i Col.inv3 ents3 kinds_nodup.2.2.2.1
    colsOK_all.2.2.2.1 (fun κ h => hm κ (Or.inr (Or.inr (Or.inr h))))
    (qK δ b nodes orbit chals pubs rows hinj i 3 (by norm_num))
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact g0
    · exact g1
    · exact g2
    · exact g3
  · rw [show ChipJ8.selSum (cv (F := ZMod p)) ents0T = ChipJ8.selSum cv ents0 from selSum_entsT _ _] at s0
    rw [show ChipJ8.selSum (cv (F := ZMod p)) ents1T = ChipJ8.selSum cv ents1 from selSum_entsT _ _] at s1
    rw [show ChipJ8.selSum (cv (F := ZMod p)) ents2T = ChipJ8.selSum cv ents2 from selSum_entsT _ _] at s2
    have h3 : (ChipJ8.selSum (cv (F := ZMod p)) ents3).eval (EF i) = (EF i).trace (Kd.sel .call) := by
      simp [ChipJ8.selSum, CoeffExpr.sumList, ents3, CoeffExpr.eval]
    rw [h3] at s3
    have hmv : (EF i).trace 19 = (rows i).w.mv :=
      EF_col δ b nodes orbit chals pubs rows hinj i (by norm_num) (by norm_num) (by norm_num)
    have hmm : (EF i).trace 18 = (rows i).w.m :=
      EF_col δ b nodes orbit chals pubs rows hinj i (by norm_num) (by norm_num) (by norm_num)
    rw [termJ, ← s0, ← s1, ← s2, ← s3, ← hmv, ← hmm]
    simp only [contribT, sumQE, List.foldr, ev_add, ev_scale, ev_var, ev_zero, CoeffExpr.eval, cv, Col.mv,
      Col.m, liftQ, map_neg, map_mul]
    ring

theorem rowX (hinj : Function.Injective nodes) (i : Fin n)
    (hpX : ∀ κ ∈ keysOf entsX (rows i), compress (coinsJX δ chals) (liftRec (keyK (K := K) 5 κ)) ≠ 0) :
    (contribX cv QE.var).ev δ (EK i) (EF i) = sX δ chals (rows i) := by
  rw [← (slotRowX δ b nodes orbit chals pubs rows hinj i hpX).2]
  simp only [contribX, ev_scale, ev_var]

end Env

/-! ## 5. Honest acceptance -/

section Main
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)
  {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (rows : Fin n → CRow (ZMod p))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "PJ" => polyJC δ b nodes orbit chals pubs rows
local notation "EF" => jEF b nodes orbit chals pubs PJ
local notation "EK" => jEK δ b nodes orbit chals pubs PJ

/-- The six accumulator `𝕂′` equations at row `i` of the honest trace. -/
theorem acc_honest (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpT : ∀ i, ∀ κ ∈ consKT (rows i) ++ provKT (rows i) ++ keysOf ents3 (rows i),
      compress (coinsJ δ chals) (liftRec (keyK (K := K) 8 κ)) ≠ 0)
    (hpX : ∀ i, ∀ κ ∈ keysOf entsX (rows i), compress (coinsJX δ chals) (liftRec (keyK (K := K) 5 κ)) ≠ 0)
    (hp01 : Quad.mk _ (pubs 0) (pubs 1) = ∑ i, termJ δ chals (rows i))
    (hp23 : Quad.mk _ (pubs 2) (pubs 3) = ∑ i, sX δ chals (rows i)) (i : Fin n) :
    ∀ e ∈ (accGates : List (QE (ZMod p))), e.ev δ (EK i) (EF i) = 0 := by
  have hF := EF_first δ b nodes orbit chals pubs rows hinj i
  have hL := EF_last δ b nodes orbit chals pubs rows hinj i
  have hT : Quad.mk _ ((EK i).trace 10) ((EK i).trace 11) = accT δ chals rows i :=
    qK δ b nodes orbit chals pubs rows hinj i 5 (by norm_num)
  have hX : Quad.mk _ ((EK i).trace 12) ((EK i).trace 13) = accX δ chals rows i :=
    qK δ b nodes orbit chals pubs rows hinj i 6 (by norm_num)
  have hcT := (rowT δ b nodes orbit chals pubs rows hinj i (hpT i)).2
  have hcX := rowX δ b nodes orbit chals pubs rows hinj i (hpX i)
  have hpub : ∀ j, (EK i).pub j = pubs j := fun j =>
    TeleH.gather_pub_T b (jetTemplateJ8T δ) 29 (jetTemplateJ8T_baseCols δ) (EF i) pubs rfl j
  intro e he
  simp only [accGates, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · -- tagged init
    rw [ev_scale, ev_sub, ev_var]
    simp only [cv, CoeffExpr.eval, Col.isFirst, Col.accT]
    rw [hF, hT, hcT]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0, ← tN_fin δ chals rows i, h0, accT_zero, sub_self, mul_zero]
    · rw [if_neg h0]; simp [liftQ]
  · -- tagged step
    rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var]
    simp only [notE, cv, CoeffExpr.eval, Col.isLast, Col.accT]
    rw [hL]
    by_cases hl : (i : ℕ) = n - 1
    · rw [if_pos hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by omega
      rw [contribT_next δ _ _ _ _ (next_F hadj i hi) (next_K hadj i hi),
        next_K hadj i hi 10, next_K hadj i hi 11,
        (rowT δ b nodes orbit chals pubs rows hinj ⟨(i : ℕ) + 1, hi⟩ (hpT _)).2,
        qK δ b nodes orbit chals pubs rows hinj ⟨(i : ℕ) + 1, hi⟩ 5 (by norm_num), hT, if_neg hl]
      show _ * (accT δ chals rows ((i : ℕ) + 1) - _ - _) = 0
      rw [← tN_fin δ chals rows ⟨(i : ℕ) + 1, hi⟩, accT_succ]
      simp
  · -- tagged terminal
    rw [ev_scale, ev_sub, ev_var, ev_pub, hpub, hpub]
    simp only [cv, CoeffExpr.eval, Col.isLast, Col.accT]
    rw [hL, hT]
    by_cases hl : (i : ℕ) = n - 1
    · rw [if_pos hl, hl, accT_last δ chals rows hn, show (0 : ℕ) + 1 = 1 from rfl, hp01, sub_self, mul_zero]
    · rw [if_neg hl]; simp [liftQ]
  · -- export init
    rw [ev_scale, ev_sub, ev_var]
    simp only [cv, CoeffExpr.eval, Col.isFirst, Col.accX]
    rw [hF, hX, hcX]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0, ← xN_fin δ chals rows i, h0, accX_zero, sub_self, mul_zero]
    · rw [if_neg h0]; simp [liftQ]
  · -- export step
    rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var]
    simp only [notE, cv, CoeffExpr.eval, Col.isLast, Col.accX]
    rw [hL]
    by_cases hl : (i : ℕ) = n - 1
    · rw [if_pos hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by omega
      rw [contribX_next δ _ _ _ _ (next_F hadj i hi) (next_K hadj i hi),
        next_K hadj i hi 12, next_K hadj i hi 13,
        rowX δ b nodes orbit chals pubs rows hinj ⟨(i : ℕ) + 1, hi⟩ (hpX _),
        qK δ b nodes orbit chals pubs rows hinj ⟨(i : ℕ) + 1, hi⟩ 6 (by norm_num), hX, if_neg hl]
      show _ * (accX δ chals rows ((i : ℕ) + 1) - _ - _) = 0
      rw [← xN_fin δ chals rows ⟨(i : ℕ) + 1, hi⟩, accX_succ]
      simp
  · -- export terminal
    rw [ev_scale, ev_sub, ev_var, ev_pub, hpub, hpub]
    simp only [cv, CoeffExpr.eval, Col.isLast, Col.accX]
    rw [hL, hX]
    by_cases hl : (i : ℕ) = n - 1
    · rw [if_pos hl, hl, accX_last δ chals rows hn, show (2 : ℕ) + 1 = 3 from rfl, hp23, sub_self, mul_zero]
    · rw [if_neg hl]; simp [liftQ]

/-- **RAP-level honest acceptance of the tag-last J chip** (`jetChipJ8 = expandChip jetTemplateJ8T`):
the honest trace `polyJ` of a row list satisfies the chip and binds its 18 verifier-fixed columns, from
J-3b's base gates on every row, no vanishing tagged / export denominator at the coins, and the four
publics: `(pub₀, pub₁)` = the J terminal `Σ termJ`, `(pub₂, pub₃)` = the export sum `Σ sX`. -/
theorem jetChipJ8_honest_sat (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hgate : ∀ i, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (envOf (rows i)) = 0)
    (hpT : ∀ i, ∀ κ ∈ consKT (rows i) ++ provKT (rows i) ++ keysOf ents3 (rows i),
      compress (coinsJ δ chals) (liftRec (keyK (K := K) 8 κ)) ≠ 0)
    (hpX : ∀ i, ∀ κ ∈ keysOf entsX (rows i), compress (coinsJX δ chals) (liftRec (keyK (K := K) 5 κ)) ≠ 0)
    (hp01 : Quad.mk _ (pubs 0) (pubs 1) = ∑ i, termJ δ chals (rows i))
    (hp23 : Quad.mk _ (pubs 2) (pubs 3) = ∑ i, sX δ chals (rows i)) :
    RAP.SatisfiesWithPreprocessing (jetChipJ8 δ b nodes orbit chals pubs (layJ rows)) PJ := by
  refine ⟨(expandChip_satisfies_iff_language (jetTemplateJ8T δ) b _ _ orbit _ _).mpr ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    refine ⟨base_honest δ b nodes orbit chals pubs rows hinj i (hgate i), ?_, ?_, ?_⟩
    · intro g hg; simp [jetTemplateJ8T] at hg
    · intro g hg; simp [jetTemplateJ8T] at hg
    · intro g hg
      obtain ⟨e, he, hg⟩ := List.mem_flatMap.mp hg
      refine gates_of_ev' δ e _ _ ?_ g hg
      rcases List.mem_append.mp he with hs | ha
      · simp only [slotGatesT, List.mem_cons, List.not_mem_nil, or_false] at hs
        have hT := (rowT δ b nodes orbit chals pubs rows hinj i (hpT i)).1
        rcases hs with rfl | rfl | rfl | rfl | rfl
        · exact hT _ (by simp)
        · exact hT _ (by simp)
        · exact hT _ (by simp)
        · exact hT _ (by simp)
        · exact (slotRowX δ b nodes orbit chals pubs rows hinj i (hpX i)).1
      · exact acc_honest δ b nodes orbit chals pubs rows hinj hn hadj hpT hpX hp01 hp23 i e ha
  · intro j
    show Lagrange.interpolate Finset.univ nodes (fun i => colJ δ b chals rows (j : ℕ) i) =
      Lagrange.interpolate Finset.univ nodes (fun i => jetPre (layJ rows) (j : ℕ) i)
    congr 1
    funext i
    exact colJ_pre δ b chals rows j.isLt i

end Main

end

end Nock.Jet.ChipJ8T.HonestRAP
