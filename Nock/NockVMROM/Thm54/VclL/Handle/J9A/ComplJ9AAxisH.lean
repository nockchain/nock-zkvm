/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AAxisH.lean

  Pattern: `Nock/Jet/ChipJ8THonestRAP.lean` (standalone `expandChip`
  with `𝕂′` inverses and inclusive prefix-sum accumulators).

  Data: base-column values `col : ℕ → Fin n → F` (columns `2..21`; columns `0 / 1` are the first / last row
  masks, supplied by `fullCol`), the chip's `δ`, basis `b`, orbit, coins `chals`, publics `pubs`.
  The honest `𝕂′` roles (round 2, after the 22 base columns), at the handle coins `κ`:
  * `invL = (den limbKey)⁻¹`, `invP = (den pathKey)⁻¹`, `invT = (den tagKey)⁻¹` (`dKey`, with the key read off
    the base columns `col`);
  * `accS` = INCLUSIVE prefix sum of `sRow = invL − mu·invT` (`sTerm`);
  * `accP` = INCLUSIVE prefix sum of `pRow = (1 − z1a)·invP` (`pTerm`).

  `axisChipJ9_honest_sat` : the honest trace `polyAx` satisfies the chip and binds its two preprocessing
  columns, from
  * `hgate`: every base gate of `AxisChipJ9.baseGates` vanishes at row `i`'s base environment `envC`
    whose next-row values are row `i+1`'s when `i+1 < n`, and — for the LAST row — at EVERY next-row valuation
    (the hypothesis is quantified over all `nxt` whose premise `∀ hi : i+1 < n, nxt = row i+1` is vacuous at the
    last row; it is exactly as strong as the chip's own row-gate semantics requires there);
  * `hden`: no key denominator vanishes at the handle coins (completeness bad events);
  * `hpS`, `hpP`: the two terminal publics are the full sums;
  * the orbit facts `hinj`, `hadj`.
  `polyAx_reads` / `axLimbReqs_honest` / `axPathReqs_honest` / `axTagProvs_honest`: the honest trace reads back
  `col` (as `EF_trace`), so the record lists are those of the base columns.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.AxisTeleJ9
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AxisTeleJ9
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Generic pieces -/

section Gen
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

/-- A `𝕂′` equation with value `0` has both `𝕂`-gates `0`. -/
theorem gates_of_ev' (e : QE F) (eK : Env K) (eF : Env F) (h : e.ev δ eK eF = 0) :
    ∀ g ∈ e.gates, g.eval eK eF = 0 := by
  rw [QE.ev, Quad.mk_eq_zero_iff] at h
  intro g hg
  simp only [QE.gates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact h.1
  · exact h.2

end Gen

section KeyShape
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The padded key vector reads only base columns `< 22` (and constants). -/
theorem keyVecL_congr (m : ℕ) (key : List (CoeffExpr F)) (e e' : Env F)
    (hk : ∀ g ∈ key, (∃ j, j < 22 ∧ g = cv j) ∨ ∃ c, g = CoeffExpr.const c)
    (ht : ∀ j < 22, e.trace j = e'.trace j) :
    AxisChipJ9.keyVecL (K := K) m key e = AxisChipJ9.keyVecL (K := K) m key e' := by
  funext c
  simp only [AxisChipJ9.keyVecL]
  congr 1
  by_cases hc : (c : ℕ) < key.length
  · rw [List.getD_eq_getElem _ _ hc]
    rcases hk _ (List.getElem_mem hc) with ⟨j, hj, hg⟩ | ⟨x, hg⟩
    · rw [hg]; simp only [cv, CoeffExpr.eval]; exact ht j hj
    · rw [hg]; rfl
  · rw [List.getD_eq_default _ _ (not_lt.mp hc)]
    rfl

theorem limbKey_shape : ∀ g ∈ (AxisChipJ9.limbKey : List (CoeffExpr F)),
    (∃ j, j < 22 ∧ g = cv j) ∨ ∃ c, g = CoeffExpr.const c := by
  intro g hg
  simp only [AxisChipJ9.limbKey, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    first | exact Or.inl ⟨_, by decide, rfl⟩ | exact Or.inr ⟨_, rfl⟩

theorem pathKey_shape : ∀ g ∈ (AxisChipJ9.pathKey : List (CoeffExpr F)),
    (∃ j, j < 22 ∧ g = cv j) ∨ ∃ c, g = CoeffExpr.const c := by
  intro g hg
  simp only [AxisChipJ9.pathKey, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    first | exact Or.inl ⟨_, by decide, rfl⟩ | exact Or.inr ⟨_, rfl⟩

theorem tagKey_shape : ∀ g ∈ (AxisChipJ9.tagKey : List (CoeffExpr F)),
    (∃ j, j < 22 ∧ g = cv j) ∨ ∃ c, g = CoeffExpr.const c := by
  intro g hg
  simp only [AxisChipJ9.tagKey, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact Or.inl ⟨_, by decide, rfl⟩ | exact Or.inr ⟨_, rfl⟩

/-- Every axis base gate reads only base columns `< 22` (current and next). -/
theorem baseGates_below_all :
    (AxisChipJ9.baseGates (F := F)).all (colsBelow 22) = true := by
  simp [AxisChipJ9.baseGates, AxisChipJ9.baseAG, AxisChipJ9.AG.gate, AxisChipJ9.g1, AxisChipJ9.g2,
    AxisChipJ9.g3, AxisChipJ9.g4, AxisChipJ9.g5, AxisChipJ9.g6, AxisChipJ9.g6c, AxisChipJ9.g6p,
    AxisChipJ9.gHeadCl, AxisChipJ9.g6b, AxisChipJ9.g7, AxisChipJ9.g8, AxisChipJ9.selG8,
    AxisChipJ9.CopyG.gate, AxisChipJ9.SelG.gate, AxisChipJ9.Op.expr, colsBelow, cv, nv, notE, boolE,
    AxisChipJ9.isFT, AxisChipJ9.isLT, AxisChipJ9.head, AxisChipJ9.cl, AxisChipJ9.z1a, AxisChipJ9.route0,
    AxisChipJ9.R, AxisChipJ9.pw, AxisChipJ9.l, AxisChipJ9.axK, AxisChipJ9.axS, AxisChipJ9.hrv,
    AxisChipJ9.hink, AxisChipJ9.hinv, AxisChipJ9.houtk, AxisChipJ9.houtv, AxisChipJ9.v, AxisChipJ9.invg4,
    AxisChipJ9.r0h, AxisChipJ9.ftk, AxisChipJ9.ftv, AxisChipJ9.mu]

theorem baseGates_below : ∀ g ∈ (AxisChipJ9.baseGates : List (CoeffExpr F)), colsBelow 22 g = true := by
  intro g hg; exact List.all_eq_true.mp baseGates_below_all g hg

end KeyShape

/-! ## 2. The honest values -/

section Values
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) (chals : ℕ → K) {n : ℕ}
  (hn : 0 < n) (col : ℕ → Fin n → F)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- **The intended base environment of row `i`**: the current row is `fullCol` (masks at `0 / 1`, `col`
elsewhere), the next row is the supplied `nxt`; coins and publics are free (no base gate reads them). -/
def envC (i : Fin n) (nxt : ℕ → F) : Env F where
  trace := fun j => fullCol hn col j i
  traceNext := nxt
  chal := fun _ => 0
  pub := fun _ => 0

/-- A key denominator at the handle coins `κ`, with the key read off the base columns. -/
def dKey (key : List (CoeffExpr F)) (i : Fin n) : 𝕂′ :=
  compress (κ δ chals)
    (liftRec (K := K) (L := 𝕂′) (AxisChipJ9.keyVecL (K := K) 8 key (envC hn col i (fun _ => 0))))

/-- The service row term `invL − mu·invT`. -/
def sRow (i : Fin n) : 𝕂′ :=
  (dKey δ chals hn col AxisChipJ9.limbKey i)⁻¹ -
    liftQ δ (col AxisChipJ9.mu i) * (dKey δ chals hn col AxisChipJ9.tagKey i)⁻¹

/-- The path row term `(1 − z1a)·invP`. -/
def pRow (i : Fin n) : 𝕂′ :=
  liftQ δ (1 - col AxisChipJ9.z1a i) * (dKey δ chals hn col AxisChipJ9.pathKey i)⁻¹

def sN (i : ℕ) : 𝕂′ := if h : i < n then sRow δ chals hn col ⟨i, h⟩ else 0
def pN (i : ℕ) : 𝕂′ := if h : i < n then pRow δ chals hn col ⟨i, h⟩ else 0

/-- **The service accumulator**: the inclusive prefix sum of `sRow`. -/
def accSN (i : ℕ) : 𝕂′ := ∑ j ∈ Finset.range (i + 1), sN δ chals hn col j
/-- **The path accumulator**: the inclusive prefix sum of `pRow`. -/
def accPN (i : ℕ) : 𝕂′ := ∑ j ∈ Finset.range (i + 1), pN δ chals hn col j

/-- The five `𝕂′` columns (`invL invP invT accS accP`) of row `i`. -/
def qv (s : ℕ) (i : Fin n) : 𝕂′ :=
  match s with
  | 0 => (dKey δ chals hn col AxisChipJ9.limbKey i)⁻¹
  | 1 => (dKey δ chals hn col AxisChipJ9.pathKey i)⁻¹
  | 2 => (dKey δ chals hn col AxisChipJ9.tagKey i)⁻¹
  | 3 => accSN δ chals hn col i
  | 4 => accPN δ chals hn col i
  | _ => 0

/-- `𝕂`-role `r` of row `i`: Re / Im of `𝕂′` column `r / 2`. -/
def roleV (r : ℕ) (i : Fin n) : K :=
  if r % 2 = 0 then Quad.re _ (qv δ chals hn col (r / 2) i) else Quad.im _ (qv δ chals hn col (r / 2) i)

/-- **The honest column function**: base columns `< 22` from `col`, `𝕂`-role limbs `22..51`. -/
def colAx (c : ℕ) (i : Fin n) : F :=
  if c < 22 then col c i else coordN b (roleV δ chals hn col ((c - 22) / 3) i) (c - 22)

theorem sN_fin (i : Fin n) : sN δ chals hn col i = sRow δ chals hn col i := by simp [sN, i.isLt]
theorem pN_fin (i : Fin n) : pN δ chals hn col i = pRow δ chals hn col i := by simp [pN, i.isLt]

theorem accSN_zero : accSN δ chals hn col 0 = sN δ chals hn col 0 := by simp [accSN]
theorem accPN_zero : accPN δ chals hn col 0 = pN δ chals hn col 0 := by simp [accPN]

theorem accSN_succ (j : ℕ) : accSN δ chals hn col (j + 1) = accSN δ chals hn col j + sN δ chals hn col (j + 1) := by
  simp only [accSN]; rw [Finset.sum_range_succ]
theorem accPN_succ (j : ℕ) : accPN δ chals hn col (j + 1) = accPN δ chals hn col j + pN δ chals hn col (j + 1) := by
  simp only [accPN]; rw [Finset.sum_range_succ]

theorem accSN_last : accSN δ chals hn col (n - 1) = ∑ i, sRow δ chals hn col i := by
  simp only [accSN, show n - 1 + 1 = n by omega]
  rw [← Fin.sum_univ_eq_sum_range (sN δ chals hn col) n]
  exact Finset.sum_congr rfl fun i _ => sN_fin δ chals hn col i

theorem accPN_last : accPN δ chals hn col (n - 1) = ∑ i, pRow δ chals hn col i := by
  simp only [accPN, show n - 1 + 1 = n by omega]
  rw [← Fin.sum_univ_eq_sum_range (pN δ chals hn col) n]
  exact Finset.sum_congr rfl fun i _ => pN_fin δ chals hn col i

theorem roleV_pair (s : ℕ) (i : Fin n) :
    Quad.mk _ (roleV δ chals hn col (2 * s) i) (roleV δ chals hn col (2 * s + 1) i) = qv δ chals hn col s i := by
  simp only [roleV, show (2 * s) % 2 = 0 by omega, show (2 * s + 1) % 2 = 1 by omega,
    show (2 * s) / 2 = s by omega, show (2 * s + 1) / 2 = s by omega, if_true, one_ne_zero, if_false]
  exact Quad.mk_re_im _ _

end Values

/-! ## 3. The honest trace and its row environments -/

section Trace
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (col : ℕ → Fin n → F)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- **The honest axis trace polynomials** (Lagrange interpolation of `colAx` over the row nodes, masks at
columns `0 / 1`). -/
def polyAx : Fin (axisChipJ9 δ b hn nodes orbit chals pubs).rap.w → F[X] :=
  honestQ hn nodes (colAx δ b chals hn col) _

local notation "PA" => polyAx δ b hn nodes orbit chals pubs col
local notation "EF" => axEF b nodes orbit chals pubs PA
local notation "EK" => axEK δ b nodes orbit chals pubs PA

theorem EF_full (hinj : Function.Injective nodes) (i : Fin n) {c : ℕ} (hc : c < 52) :
    (EF i).trace c = fullCol hn (colAx δ b chals hn col) c i := by
  have hw : (axisChipJ9 δ b hn nodes orbit chals pubs).rap.w = 52 := width_eq δ b hn nodes orbit chals pubs
  exact env_trace hn nodes hinj _ _ _ _ i (by rw [hw]; exact hc)

/-- Base columns `< 22` (the two masks and `col`). -/
theorem EF_lt22 (hinj : Function.Injective nodes) (i : Fin n) {c : ℕ} (hc : c < 22) :
    (EF i).trace c = fullCol hn col c i := by
  rw [EF_full δ b hn nodes orbit chals pubs col hinj i (by omega)]
  by_cases h0 : c = 0
  · simp [fullCol, h0]
  · by_cases h1 : c = 1
    · simp [fullCol, h1]
    · simp [fullCol, colAx, h0, h1, hc]

/-- **The honest trace reads back `col`** on the columns `2..21`. -/
theorem polyAx_reads (hinj : Function.Injective nodes) (i : Fin n) {c : ℕ} (h2 : 2 ≤ c) (h22 : c < 22) :
    (EF i).trace c = col c i := by
  rw [EF_lt22 δ b hn nodes orbit chals pubs col hinj i h22]
  simp [fullCol, show c ≠ 0 by omega, show c ≠ 1 by omega]

theorem EF_isFT (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace isFT = if (i : ℕ) = 0 then 1 else 0 := by
  rw [EF_lt22 δ b hn nodes orbit chals pubs col hinj i (by decide)]
  simp [fullCol, isFT]

theorem EF_isLT (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace isLT = if (i : ℕ) = n - 1 then 1 else 0 := by
  rw [EF_lt22 δ b hn nodes orbit chals pubs col hinj i (by decide)]
  simp only [fullCol, isLT, show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true]
  by_cases hi : (i : ℕ) = n - 1
  · rw [if_pos (Fin.ext hi), if_pos hi]
  · rw [if_neg (fun h => hi (congrArg Fin.val h)), if_neg hi]

theorem EK_trace (hinj : Function.Injective nodes) (i : Fin n) {r : ℕ} (hr : r < 10) :
    (EK i).trace r = roleV δ chals hn col r i := by
  show (gatherEnv b ((axisTemplateJ9 δ).col0 3) (EF i)).trace r = _
  have hv : ∀ k : Fin 3, (EF i).trace (22 + 3 * r + k) = coord b (roleV δ chals hn col r i) k := fun k => by
    have hk := k.isLt
    rw [EF_full δ b hn nodes orbit chals pubs col hinj i (by omega)]
    have h22 : ¬ (22 + 3 * r + (k : ℕ) < 22) := by omega
    have hmod : (22 + 3 * r + (k : ℕ) - 22) / 3 = r := by omega
    simp only [fullCol, colAx, if_neg h22, if_neg (show 22 + 3 * r + (k : ℕ) ≠ 0 by omega),
      if_neg (show 22 + 3 * r + (k : ℕ) ≠ 1 by omega), hmod]
    unfold coordN
    congr 1
    exact Fin.ext (by simp; omega)
  simp only [gatherEnv, ChipTemplate.col0, axisTemplateJ9_baseCols, hv, coord]
  exact b.sum_repr _

theorem qK (hinj : Function.Injective nodes) (i : Fin n) (s : ℕ) (hs : s < 5) :
    Quad.mk _ ((EK i).trace (2 * s)) ((EK i).trace (2 * s + 1)) = qv δ chals hn col s i := by
  rw [EK_trace δ b hn nodes orbit chals pubs col hinj i (by omega),
    EK_trace δ b hn nodes orbit chals pubs col hinj i (by omega)]
  exact roleV_pair δ chals hn col s i

theorem qIL (hinj : Function.Injective nodes) (i : Fin n) :
    Quad.mk _ ((EK i).trace invL) ((EK i).trace (invL + 1)) = (dKey δ chals hn col AxisChipJ9.limbKey i)⁻¹ :=
  qK δ b hn nodes orbit chals pubs col hinj i 0 (by norm_num)

theorem qIP (hinj : Function.Injective nodes) (i : Fin n) :
    Quad.mk _ ((EK i).trace invP) ((EK i).trace (invP + 1)) = (dKey δ chals hn col AxisChipJ9.pathKey i)⁻¹ :=
  qK δ b hn nodes orbit chals pubs col hinj i 1 (by norm_num)

theorem qIT (hinj : Function.Injective nodes) (i : Fin n) :
    Quad.mk _ ((EK i).trace invT) ((EK i).trace (invT + 1)) = (dKey δ chals hn col AxisChipJ9.tagKey i)⁻¹ :=
  qK δ b hn nodes orbit chals pubs col hinj i 2 (by norm_num)

theorem qAS (hinj : Function.Injective nodes) (i : Fin n) :
    Quad.mk _ ((EK i).trace accS) ((EK i).trace (accS + 1)) = accSN δ chals hn col i :=
  qK δ b hn nodes orbit chals pubs col hinj i 3 (by norm_num)

theorem qAP (hinj : Function.Injective nodes) (i : Fin n) :
    Quad.mk _ ((EK i).trace accP) ((EK i).trace (accP + 1)) = accPN δ chals hn col i :=
  qK δ b hn nodes orbit chals pubs col hinj i 4 (by norm_num)

/-- A key denominator of row `i` at the honest trace is `dKey`. -/
theorem den_honest (hinj : Function.Injective nodes) (key : List (CoeffExpr F))
    (hk : ∀ g ∈ key, (∃ j, j < 22 ∧ g = cv j) ∨ ∃ c, g = CoeffExpr.const c) (hl : key.length ≤ 8)
    (i : Fin n) :
    (HQ.denKeyQ δ key).ev δ (EK i) (EF i) = dKey δ chals hn col key i := by
  show axDen δ b nodes orbit chals pubs PA key i = _
  rw [axDen_eq δ b hn nodes orbit chals pubs PA key 8 hl i]
  unfold dKey
  rw [keyVecL_congr (K := K) 8 key (EF i) (envC hn col i (fun _ => 0)) hk
    (fun j hj => EF_lt22 δ b hn nodes orbit chals pubs col hinj i hj)]

/-- **The base gates at the honest row environment.** -/
theorem base_honest (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hgate : ∀ (i : Fin n) (nxt : ℕ → F),
      (∀ hi : (i : ℕ) + 1 < n, ∀ j, nxt j = fullCol hn col j ⟨(i : ℕ) + 1, hi⟩) →
      ∀ g ∈ (AxisChipJ9.baseGates : List (CoeffExpr F)), g.eval (envC hn col i nxt) = 0)
    (i : Fin n) : ∀ g ∈ (AxisChipJ9.baseGates : List (CoeffExpr F)), g.eval (EF i) = 0 := by
  intro g hg
  have hb := baseGates_below g hg
  by_cases hi : (i : ℕ) + 1 < n
  · have key := hgate i (fun j => fullCol hn col j ⟨(i : ℕ) + 1, hi⟩) (fun _ _ => rfl) g hg
    rw [colsBelow_eval hb (e' := envC hn col i (fun j => fullCol hn col j ⟨(i : ℕ) + 1, hi⟩))
      (fun j hj => EF_lt22 δ b hn nodes orbit chals pubs col hinj i hj)
      (fun j hj => by
        rw [axEF_next δ b hn nodes orbit chals pubs PA hadj i hi j]
        exact EF_lt22 δ b hn nodes orbit chals pubs col hinj ⟨(i : ℕ) + 1, hi⟩ hj)]
    exact key
  · have key := hgate i (fun j => (EF i).traceNext j) (fun h' => absurd h' hi) g hg
    rw [colsBelow_eval hb (e' := envC hn col i (fun j => (EF i).traceNext j))
      (fun j hj => EF_lt22 δ b hn nodes orbit chals pubs col hinj i hj) (fun j hj => rfl)]
    exact key

/-! ### The row terms -/

theorem sTerm_cur (hinj : Function.Injective nodes) (j : Fin n) :
    (sTerm (F := F) true).ev δ (EK j) (EF j) = sRow δ chals hn col j := by
  show (QE.sub (QE.var invL) (QE.scale (cv mu) (QE.var invT))).ev δ (EK j) (EF j) = _
  rw [ev_sub, ev_var, ev_scale, ev_var, qIL δ b hn nodes orbit chals pubs col hinj j,
    qIT δ b hn nodes orbit chals pubs col hinj j]
  simp only [cv, CoeffExpr.eval]
  rw [polyAx_reads δ b hn nodes orbit chals pubs col hinj j (by decide) (by decide)]
  rfl

theorem sTerm_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (sTerm (F := F) false).ev δ (EK i) (EF i) = sRow δ chals hn col ⟨(i : ℕ) + 1, hi⟩ := by
  show (QE.sub (QE.next invL) (QE.scale (nv mu) (QE.next invT))).ev δ (EK i) (EF i) = _
  rw [ev_sub, ev_next, ev_scale, ev_next]
  simp only [nv, CoeffExpr.eval]
  rw [axEF_next δ b hn nodes orbit chals pubs PA hadj i hi mu,
    axEK_next δ b hn nodes orbit chals pubs PA hadj i hi invL,
    axEK_next δ b hn nodes orbit chals pubs PA hadj i hi (invL + 1),
    axEK_next δ b hn nodes orbit chals pubs PA hadj i hi invT,
    axEK_next δ b hn nodes orbit chals pubs PA hadj i hi (invT + 1),
    qIL δ b hn nodes orbit chals pubs col hinj ⟨(i : ℕ) + 1, hi⟩,
    qIT δ b hn nodes orbit chals pubs col hinj ⟨(i : ℕ) + 1, hi⟩,
    polyAx_reads δ b hn nodes orbit chals pubs col hinj ⟨(i : ℕ) + 1, hi⟩ (by decide) (by decide)]
  rfl

theorem pTerm_cur (hinj : Function.Injective nodes) (j : Fin n) :
    (pTerm (F := F) true).ev δ (EK j) (EF j) = pRow δ chals hn col j := by
  show (QE.scale (notE (cv z1a)) (QE.var invP)).ev δ (EK j) (EF j) = _
  rw [ev_scale, ev_var, qIP δ b hn nodes orbit chals pubs col hinj j]
  simp only [notE, cv, CoeffExpr.eval]
  rw [polyAx_reads δ b hn nodes orbit chals pubs col hinj j (by decide) (by decide)]
  rfl

theorem pTerm_next (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (pTerm (F := F) false).ev δ (EK i) (EF i) = pRow δ chals hn col ⟨(i : ℕ) + 1, hi⟩ := by
  show (QE.scale (notE (nv z1a)) (QE.next invP)).ev δ (EK i) (EF i) = _
  rw [ev_scale, ev_next]
  simp only [notE, nv, CoeffExpr.eval]
  rw [axEF_next δ b hn nodes orbit chals pubs PA hadj i hi z1a,
    axEK_next δ b hn nodes orbit chals pubs PA hadj i hi invP,
    axEK_next δ b hn nodes orbit chals pubs PA hadj i hi (invP + 1),
    qIP δ b hn nodes orbit chals pubs col hinj ⟨(i : ℕ) + 1, hi⟩,
    polyAx_reads δ b hn nodes orbit chals pubs col hinj ⟨(i : ℕ) + 1, hi⟩ (by decide) (by decide)]
  rfl

/-! ### The `𝕂′` equations at row `i` of the honest trace -/

theorem axQ_honest (hinj : Function.Injective nodes) (hn' : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hden : ∀ i : Fin n, dKey δ chals hn col AxisChipJ9.limbKey i ≠ 0 ∧
      dKey δ chals hn col AxisChipJ9.pathKey i ≠ 0 ∧ dKey δ chals hn col AxisChipJ9.tagKey i ≠ 0)
    (hpS : Quad.mk _ (pubs pubAXs) (pubs (pubAXs + 1)) =
      ∑ i, ((dKey δ chals hn col AxisChipJ9.limbKey i)⁻¹ -
        liftQ δ (col AxisChipJ9.mu i) * (dKey δ chals hn col AxisChipJ9.tagKey i)⁻¹))
    (hpP : Quad.mk _ (pubs pubAXp) (pubs (pubAXp + 1)) =
      ∑ i, liftQ δ (1 - col AxisChipJ9.z1a i) * (dKey δ chals hn col AxisChipJ9.pathKey i)⁻¹)
    (i : Fin n) :
    ∀ e ∈ axQ δ, e.ev δ (EK i) (EF i) = 0 := by
  have hF := EF_isFT δ b hn nodes orbit chals pubs col hinj i
  have hL := EF_isLT δ b hn nodes orbit chals pubs col hinj i
  have hpubS : ∀ idx, (EK i).pub idx = pubs idx := axEK_pub δ b hn nodes orbit chals pubs PA i
  have hpS' : Quad.mk _ (pubs pubAXs) (pubs (pubAXs + 1)) = ∑ j, sRow δ chals hn col j := hpS
  have hpP' : Quad.mk _ (pubs pubAXp) (pubs (pubAXp + 1)) = ∑ j, pRow δ chals hn col j := hpP
  intro e he
  simp only [axQ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- invL
    rw [ev_sub, ev_mul, ev_var, ev_one, qIL δ b hn nodes orbit chals pubs col hinj i,
      den_honest δ b hn nodes orbit chals pubs col hinj _ limbKey_shape (by simp [AxisChipJ9.limbKey]) i,
      inv_mul_cancel₀ (hden i).1, sub_self]
  · -- invP
    rw [ev_sub, ev_mul, ev_var, ev_one, qIP δ b hn nodes orbit chals pubs col hinj i,
      den_honest δ b hn nodes orbit chals pubs col hinj _ pathKey_shape (by simp [AxisChipJ9.pathKey]) i,
      inv_mul_cancel₀ (hden i).2.1, sub_self]
  · -- invT
    rw [ev_sub, ev_mul, ev_var, ev_one, qIT δ b hn nodes orbit chals pubs col hinj i,
      den_honest δ b hn nodes orbit chals pubs col hinj _ tagKey_shape (by simp [AxisChipJ9.tagKey]) i,
      inv_mul_cancel₀ (hden i).2.2, sub_self]
  · -- accS init
    rw [ev_scale, ev_sub, ev_var, sTerm_cur δ b hn nodes orbit chals pubs col hinj i,
      qAS δ b hn nodes orbit chals pubs col hinj i]
    simp only [cv, CoeffExpr.eval]
    rw [hF]
    by_cases h0 : (i : ℕ) = 0
    · have e1 : accSN δ chals hn col (i : ℕ) = sRow δ chals hn col i := by
        rw [h0, accSN_zero, ← h0, sN_fin]
      rw [if_pos h0, e1, sub_self, mul_zero]
    · rw [if_neg h0]; simp [liftQ]
  · -- accS step
    rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var]
    simp only [notE, cv, CoeffExpr.eval]
    rw [hL]
    by_cases hl : (i : ℕ) = n - 1
    · rw [if_pos hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by omega
      rw [sTerm_next δ b hn nodes orbit chals pubs col hinj hadj i hi,
        axEK_next δ b hn nodes orbit chals pubs PA hadj i hi accS,
        axEK_next δ b hn nodes orbit chals pubs PA hadj i hi (accS + 1),
        qAS δ b hn nodes orbit chals pubs col hinj ⟨(i : ℕ) + 1, hi⟩,
        qAS δ b hn nodes orbit chals pubs col hinj i, if_neg hl]
      have h1 : sN δ chals hn col ((i : ℕ) + 1) = sRow δ chals hn col ⟨(i : ℕ) + 1, hi⟩ :=
        sN_fin δ chals hn col ⟨(i : ℕ) + 1, hi⟩
      have h2 : accSN δ chals hn col ((i : ℕ) + 1) - accSN δ chals hn col (i : ℕ) -
          sRow δ chals hn col ⟨(i : ℕ) + 1, hi⟩ = 0 := by
        rw [accSN_succ, h1]; ring
      have h3 : accSN δ chals hn col (⟨(i : ℕ) + 1, hi⟩ : Fin n) =
          accSN δ chals hn col ((i : ℕ) + 1) := rfl
      rw [h3, h2, mul_zero]
  · -- accS terminal
    rw [ev_scale, ev_sub, ev_var, ev_pub, hpubS, hpubS, qAS δ b hn nodes orbit chals pubs col hinj i]
    simp only [cv, CoeffExpr.eval]
    rw [hL]
    by_cases hl : (i : ℕ) = n - 1
    · have e1 : accSN δ chals hn col (i : ℕ) = ∑ j, sRow δ chals hn col j := by
        rw [hl]; exact accSN_last δ chals hn col
      rw [if_pos hl, e1, hpS', sub_self, mul_zero]
    · rw [if_neg hl]; simp [liftQ]
  · -- accP init
    rw [ev_scale, ev_sub, ev_var, pTerm_cur δ b hn nodes orbit chals pubs col hinj i,
      qAP δ b hn nodes orbit chals pubs col hinj i]
    simp only [cv, CoeffExpr.eval]
    rw [hF]
    by_cases h0 : (i : ℕ) = 0
    · have e1 : accPN δ chals hn col (i : ℕ) = pRow δ chals hn col i := by
        rw [h0, accPN_zero, ← h0, pN_fin]
      rw [if_pos h0, e1, sub_self, mul_zero]
    · rw [if_neg h0]; simp [liftQ]
  · -- accP step
    rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var]
    simp only [notE, cv, CoeffExpr.eval]
    rw [hL]
    by_cases hl : (i : ℕ) = n - 1
    · rw [if_pos hl]; simp [liftQ]
    · have hi : (i : ℕ) + 1 < n := by omega
      rw [pTerm_next δ b hn nodes orbit chals pubs col hinj hadj i hi,
        axEK_next δ b hn nodes orbit chals pubs PA hadj i hi accP,
        axEK_next δ b hn nodes orbit chals pubs PA hadj i hi (accP + 1),
        qAP δ b hn nodes orbit chals pubs col hinj ⟨(i : ℕ) + 1, hi⟩,
        qAP δ b hn nodes orbit chals pubs col hinj i, if_neg hl]
      have h1 : pN δ chals hn col ((i : ℕ) + 1) = pRow δ chals hn col ⟨(i : ℕ) + 1, hi⟩ :=
        pN_fin δ chals hn col ⟨(i : ℕ) + 1, hi⟩
      have h2 : accPN δ chals hn col ((i : ℕ) + 1) - accPN δ chals hn col (i : ℕ) -
          pRow δ chals hn col ⟨(i : ℕ) + 1, hi⟩ = 0 := by
        rw [accPN_succ, h1]; ring
      have h3 : accPN δ chals hn col (⟨(i : ℕ) + 1, hi⟩ : Fin n) =
          accPN δ chals hn col ((i : ℕ) + 1) := rfl
      rw [h3, h2, mul_zero]
  · -- accP terminal
    rw [ev_scale, ev_sub, ev_var, ev_pub, hpubS, hpubS, qAP δ b hn nodes orbit chals pubs col hinj i]
    simp only [cv, CoeffExpr.eval]
    rw [hL]
    by_cases hl : (i : ℕ) = n - 1
    · have e1 : accPN δ chals hn col (i : ℕ) = ∑ j, pRow δ chals hn col j := by
        rw [hl]; exact accPN_last δ chals hn col
      rw [if_pos hl, e1, hpP', sub_self, mul_zero]
    · rw [if_neg hl]; simp [liftQ]

/-! ## 4. Honest acceptance -/

/-- **RAP-level honest acceptance of the axis chip `axisChipJ9`, generic in the base columns**: the honest
trace `polyAx` of base columns `col` satisfies the chip and binds its two preprocessing columns, from the base
gates on every row (`hgate`, with every next-row valuation at the last row), no vanishing key denominator at
the handle coins (`hden`), the two terminal publics, and the orbit facts. -/
theorem axisChipJ9_honest_sat (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hgate : ∀ (i : Fin n) (nxt : ℕ → F),
      (∀ hi : (i : ℕ) + 1 < n, ∀ j, nxt j = fullCol hn col j ⟨(i : ℕ) + 1, hi⟩) →
      ∀ g ∈ (AxisChipJ9.baseGates : List (CoeffExpr F)), g.eval (envC hn col i nxt) = 0)
    (hden : ∀ i : Fin n, dKey δ chals hn col AxisChipJ9.limbKey i ≠ 0 ∧
      dKey δ chals hn col AxisChipJ9.pathKey i ≠ 0 ∧ dKey δ chals hn col AxisChipJ9.tagKey i ≠ 0)
    (hpS : Quad.mk _ (pubs pubAXs) (pubs (pubAXs + 1)) =
      ∑ i, ((dKey δ chals hn col AxisChipJ9.limbKey i)⁻¹ -
        liftQ δ (col AxisChipJ9.mu i) * (dKey δ chals hn col AxisChipJ9.tagKey i)⁻¹))
    (hpP : Quad.mk _ (pubs pubAXp) (pubs (pubAXp + 1)) =
      ∑ i, liftQ δ (1 - col AxisChipJ9.z1a i) * (dKey δ chals hn col AxisChipJ9.pathKey i)⁻¹) :
    (axisChipJ9 δ b hn nodes orbit chals pubs).rap.Satisfies (polyAx δ b hn nodes orbit chals pubs col) ∧
      (axisChipJ9 δ b hn nodes orbit chals pubs).BindsPreprocessing (polyAx δ b hn nodes orbit chals pubs col) := by
  refine ⟨(expandChip_satisfies_iff_language (axisTemplateJ9 δ) b _ _ orbit _ _).mpr ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    refine ⟨base_honest δ b hn nodes orbit chals pubs col hinj hadj hgate i, ?_, ?_, ?_⟩
    · intro g hg; simp [axisTemplateJ9] at hg
    · intro g hg; simp [axisTemplateJ9] at hg
    · intro g hg
      have hg' : g ∈ (axQ δ).flatMap QE.gates := hg
      obtain ⟨e, he, hg''⟩ := List.mem_flatMap.mp hg'
      exact gates_of_ev' δ e _ _ (axQ_honest δ b hn nodes orbit chals pubs col hinj hn hadj hden hpS hpP i e he)
        g hg''
  · intro j
    obtain ⟨j, hj⟩ := j
    have hj2 : j < 2 := hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact honestQ_zero hn nodes _ _
    · exact honestQ_one hn nodes _ _

end Trace

/-! ## 5. The honest record lists -/

section Lists
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n)
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (col : ℕ → Fin n → F)

local notation "PA" => polyAx δ b hn nodes orbit chals pubs col
local notation "EF" => axEF b nodes orbit chals pubs PA

/-- **The honest limb consumes** are the keys read off `col`. -/
theorem axLimbReqs_honest (hinj : Function.Injective nodes) :
    axLimbReqs b nodes orbit chals pubs PA =
      (List.finRange n).map fun i => AxisChipJ9.keyVecL (K := K) 8 AxisChipJ9.limbKey
        (envC hn col i (fun _ => 0)) := by
  unfold axLimbReqs
  refine List.map_congr_left fun i _ => ?_
  exact keyVecL_congr (K := K) 8 _ _ _ limbKey_shape
    (fun j hj => EF_lt22 δ b hn nodes orbit chals pubs col hinj i hj)

/-- **The honest path consumes** (rows with `1 − z1a ≠ 0`). -/
theorem axPathReqs_honest (hinj : Function.Injective nodes) :
    axPathReqs b nodes orbit chals pubs PA =
      (List.finRange n).flatMap fun i =>
        if 1 - col AxisChipJ9.z1a i = 0 then [] else
          [AxisChipJ9.keyVecL (K := K) 5 AxisChipJ9.pathKey (envC hn col i (fun _ => 0))] := by
  unfold axPathReqs
  refine List.flatMap_congr fun i _ => ?_
  rw [polyAx_reads δ b hn nodes orbit chals pubs col hinj i (by decide) (by decide),
    keyVecL_congr (K := K) 5 _ (EF i) (envC hn col i (fun _ => 0)) pathKey_shape
      (fun j hj => EF_lt22 δ b hn nodes orbit chals pubs col hinj i hj)]

/-- **The honest `TAG_ax` providers** (rows with `mu ≠ 0`, weight `mu`). -/
theorem axTagProvs_honest (hinj : Function.Injective nodes) :
    axTagProvs b nodes orbit chals pubs PA =
      (List.finRange n).flatMap fun i =>
        if col AxisChipJ9.mu i = 0 then [] else
          [(AxisChipJ9.keyVecL (K := K) 8 AxisChipJ9.tagKey (envC hn col i (fun _ => 0)),
            algebraMap F K (col AxisChipJ9.mu i))] := by
  unfold axTagProvs
  refine List.flatMap_congr fun i _ => ?_
  rw [polyAx_reads δ b hn nodes orbit chals pubs col hinj i (by decide) (by decide),
    keyVecL_congr (K := K) 8 _ (EF i) (envC hn col i (fun _ => 0)) tagKey_shape
      (fun j hj => EF_lt22 δ b hn nodes orbit chals pubs col hinj i hj)]

end Lists

end

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH
#print axioms axisChipJ9_honest_sat
#print axioms axLimbReqs_honest
#print axioms axPathReqs_honest
#print axioms axTagProvs_honest
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisH
