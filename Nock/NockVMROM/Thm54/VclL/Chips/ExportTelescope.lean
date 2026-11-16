/-
  Nock/NockVMROM/Thm54/VclL/Chips/ExportTelescope.lean

  **The export accumulator at the side slot ⇒
  weighted IO facts ⇒ `EdgeExported`.**

  * `cell_export_telescope`: `Σ_i (mxᵢ·inv₀ᵢ + mx1ᵢ·inv₁ᵢ) = ρ_X + y` (cell public slots `2 / 3`);
    `path_export_telescope`: `Σ_j invⱼ = y` (path public slots `0 / 1`), `y` the path chip's export
    terminal sent after the coins.
  * `cellExportFacts` — the frame's weighted `IOFacts` at `m = 11`: providers `cellXRecords` (two per
    cell row), internal = every path row's consumed key `pathXInternal`, terminal `ρ_X + Σ internal`.
  * `path_edges_exported` — every path row's edge `(p, l, r, side, natOf cellIdx)` is `EdgeExported`
    by the cell table (from `finiteIO_lookup_sound_weighted` over `reqs ++ internal`), and the row's
    `side` equals the providing record's side slot.
  * §4  `pathProviderFacts` — the path accumulator's own `IOFacts` at `m = 8`: providers =
    the record (`last`) rows `(pRec, m)`, terminal `ρ_P` (path slots `2 / 3`), no internal consumer.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.Telescope

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.PathModel
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The cell side -/

section CellX
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])

/-- The export row term `mx·inv₀ + mx1·inv₁`. -/
abbrev xT (i : Fin n) : Quad (algebraMap F K δF) :=
  liftQ δF (cellB δF b hn nodes orbit chals pubs Q Cell.mx i) * cellQ δF b hn nodes orbit chals pubs Q Cell.xProvInv i
    + liftQ δF (cellB δF b hn nodes orbit chals pubs Q Cell.mx1 i) * cellQ δF b hn nodes orbit chals pubs Q Cell.xProvInv1 i

theorem xTerm_cur (i : Fin n) :
    (Cell.xTerm true : QE F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
      (cellEnvF b nodes orbit chals pubs Q i) = xT δF b hn nodes orbit chals pubs Q i := by
  simp only [Cell.xTerm, if_true, ev_add, ev_scale, CoeffExpr.eval, cv]

theorem xTerm_next
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (Cell.xTerm false : QE F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
      (cellEnvF b nodes orbit chals pubs Q i) = xT δF b hn nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩ := by
  simp only [Cell.xTerm, Bool.false_eq_true, if_false, ev_add, ev_scale, CoeffExpr.eval, nv,
    cell_ev_next δF b hn nodes orbit chals pubs Q hadj i hi,
    cell_traceNext δF b hn nodes orbit chals pubs Q hadj i hi]

/-- **The cell export telescope**: `Σ_i xTᵢ` is the public at slots `2 / 3`. -/
theorem cell_export_telescope (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i : Fin n, xT δF b hn nodes orbit chals pubs Q i = Quad.mk _ (pubs 2) (pubs 3) := by
  have hmem : ∀ e, e ∈ Cell.qEqs δF → ∀ i, e.ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
      (cellEnvF b nodes orbit chals pubs Q i) = 0 := fun e he i =>
    (cell_gates δF b hn nodes orbit chals pubs Q hsat i).2 e he
  set acc : ℕ → Quad (algebraMap F K δF) := fun k =>
    if hk : k < n then cellQ δF b hn nodes orbit chals pubs Q Cell.xAcc ⟨k, hk⟩ else 0 with hacc
  set term : ℕ → Quad (algebraMap F K δF) := fun k =>
    if hk : k < n then xT δF b hn nodes orbit chals pubs Q ⟨k, hk⟩ else 0 with hterm
  have h0 : acc 0 = term 0 := by
    simp only [hacc, hterm, dif_pos hn]
    have g := hmem (QE.scale (cv Cell.isF)
      (QE.sub (QE.var Cell.xAcc) (Cell.xTerm true))) (by simp [Cell.qEqs]) ⟨0, hn⟩
    rw [ev_scale, ev_sub, xTerm_cur] at g
    have hf : (CoeffExpr.eval (cv Cell.isF) (cellEnvF b nodes orbit chals pubs Q ⟨0, hn⟩) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]
      exact (cell_isF δF b hn nodes orbit chals pubs Q hbind hinj ⟨0, hn⟩).trans (if_pos rfl)
    rw [hf, liftQ, map_one, map_one, one_mul] at g
    exact sub_eq_zero.mp g
  have hs : ∀ i, i + 1 < n → acc (i + 1) = acc i + term (i + 1) := by
    intro i hi
    simp only [hacc, hterm, dif_pos hi, dif_pos (show i < n by omega)]
    have g := hmem (QE.scale (notE (cv Cell.isL))
      (QE.sub (QE.sub (QE.next Cell.xAcc) (QE.var Cell.xAcc)) (Cell.xTerm false))) (by simp [Cell.qEqs])
      ⟨i, by omega⟩
    rw [ev_scale, ev_sub, ev_sub, xTerm_next δF b hn nodes orbit chals pubs Q hadj ⟨i, by omega⟩ hi,
      cell_ev_next δF b hn nodes orbit chals pubs Q hadj ⟨i, by omega⟩ hi] at g
    have hl : (CoeffExpr.eval (notE (cv Cell.isL)) (cellEnvF b nodes orbit chals pubs Q ⟨i, by omega⟩) : F) = 1 := by
      simp only [CoeffExpr.eval, cv, notE]
      have hL := cell_isL δF b hn nodes orbit chals pubs Q hbind hinj ⟨i, by omega⟩
      simp only [cellB] at hL
      rw [hL, if_neg]
      · simp
      · intro h; have := congrArg Fin.val h; simp at this; omega
    rw [hl, liftQ, map_one, map_one, one_mul] at g
    linear_combination g
  have hT : acc (n - 1) = Quad.mk _ (pubs 2) (pubs 3) := by
    simp only [hacc, dif_pos (show n - 1 < n by omega)]
    have g := hmem (QE.scale (cv Cell.isL)
      (QE.sub (QE.var Cell.xAcc) (QE.pub 2))) (by simp [Cell.qEqs]) ⟨n - 1, by omega⟩
    rw [ev_scale, ev_sub, ev_pub] at g
    have hl : (CoeffExpr.eval (cv Cell.isL) (cellEnvF b nodes orbit chals pubs Q ⟨n - 1, by omega⟩) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]
      exact (cell_isL δF b hn nodes orbit chals pubs Q hbind hinj ⟨n - 1, by omega⟩).trans (if_pos rfl)
    rw [hl, liftQ, map_one, map_one, one_mul,
      gather_pub_cell δF b pubs _ rfl, gather_pub_cell δF b pubs _ rfl] at g
    exact sub_eq_zero.mp g
  have := telescope n hn acc term _ h0 hs hT
  rw [Finset.sum_range] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hterm, dif_pos i.isLt]

/-- The two export provider inverses of row `i`. -/
theorem cell_xinv_facts (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (cellDen δF b hn nodes orbit chals pubs Q (Cell.xKeyS 0) i ≠ 0 ∧
      cellQ δF b hn nodes orbit chals pubs Q Cell.xProvInv i = (cellDen δF b hn nodes orbit chals pubs Q (Cell.xKeyS 0) i)⁻¹) ∧
    (cellDen δF b hn nodes orbit chals pubs Q (Cell.xKeyS 1) i ≠ 0 ∧
      cellQ δF b hn nodes orbit chals pubs Q Cell.xProvInv1 i = (cellDen δF b hn nodes orbit chals pubs Q (Cell.xKeyS 1) i)⁻¹) := by
  have hm := (cell_gates δF b hn nodes orbit chals pubs Q hsat i).2
  have g0 := hm (QE.sub (QE.mul δF (QE.var Cell.xProvInv) (den δF (Cell.xKeyS 0))) QE.one) (by simp [Cell.qEqs])
  have g1 := hm (QE.sub (QE.mul δF (QE.var Cell.xProvInv1) (den δF (Cell.xKeyS 1))) QE.one) (by simp [Cell.qEqs])
  rw [ev_sub, ev_mul, ev_one] at g0 g1
  exact ⟨prov_inv δF g0, prov_inv δF g1⟩

/-- The export providers: two records `(xKeyS s, mx_s)` per cell row. -/
def cellXRecords : List ((Fin 11 → Quad (algebraMap F K δF)) × F) :=
  (List.finRange n).flatMap fun i =>
    [(cellKey δF b hn nodes orbit chals pubs Q 11 (Cell.xKeyS 0) i, cellB δF b hn nodes orbit chals pubs Q Cell.mx i),
     (cellKey δF b hn nodes orbit chals pubs Q 11 (Cell.xKeyS 1) i, cellB δF b hn nodes orbit chals pubs Q Cell.mx1 i)]

theorem cell_export_sum (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) :
    ((cellXRecords δF b hn nodes orbit chals pubs Q).map fun r =>
        algebraMap F (Quad (algebraMap F K δF)) r.2 * (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r.1)⁻¹).sum =
      Quad.mk _ (pubs 2) (pubs 3) := by
  rw [← cell_export_telescope δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  simp only [cellXRecords, map_flatMap_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Function.comp_def, sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨-, h0⟩, ⟨-, h1⟩⟩ := cell_xinv_facts δF b hn nodes orbit chals pubs Q hsat i
  rw [cell_compress (m := 11) γ ρ hok (Cell.xKeyS 0) rfl le_rfl,
    cell_compress (m := 11) γ ρ hok (Cell.xKeyS 1) rfl le_rfl]
  simp only [xT, h0, h1, liftQ, IsScalarTower.algebraMap_apply F K (Quad (algebraMap F K δF))]

end CellX

/-! ## 2. The path side -/

section PathX
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (pathChip δF b hn nodes orbit chals pubs).rap.w → F[X])

abbrev pathQ (r j : ℕ) : Quad (algebraMap F K δF) :=
  (QE.var r : QE F).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q j) (pathEnvF b hn nodes orbit chals pubs Q j)

abbrev pathKey (m : ℕ) (es : List (QE F)) (j : ℕ) : Fin m → Quad (algebraMap F K δF) :=
  keyVec δF m es (pathEnvK δF b hn nodes orbit chals pubs Q j) (pathEnvF b hn nodes orbit chals pubs Q j)

theorem path_w : (pathChip δF b hn nodes orbit chals pubs).rap.w = 112 :=
  (pathChip_fingerprint δF b hn nodes orbit chals pubs).1

theorem path_isF (hbind : (pathChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (j : ℕ) (hj : j < n) :
    (pathEnvF b hn nodes orbit chals pubs Q j).trace Path.isF = if j = 0 then 1 else 0 := by
  rw [pathEnvF_eq b hn nodes orbit chals pubs Q j hj, show Path.isF = 0 from rfl,
    envOfTrace_trace Q _ _ _ _ (show 0 < _ by rw [path_w]; omega)]
  exact (pathChip_masks δF b hn nodes orbit chals pubs Q hbind hinj ⟨j, hj⟩).1

theorem path_isL (hbind : (pathChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (j : ℕ) (hj : j < n) :
    (pathEnvF b hn nodes orbit chals pubs Q j).trace Path.isL = if j = n - 1 then 1 else 0 := by
  rw [pathEnvF_eq b hn nodes orbit chals pubs Q j hj, show Path.isL = 1 from rfl,
    envOfTrace_trace Q _ _ _ _ (show 1 < _ by rw [path_w]; omega),
    (pathChip_masks δF b hn nodes orbit chals pubs Q hbind hinj ⟨j, hj⟩).2]
  by_cases hjn : j = n - 1
  · rw [if_pos (Fin.ext hjn), if_pos hjn]
  · rw [if_neg (fun h => hjn (congrArg Fin.val h)), if_neg hjn]

/-- **The path export-consumption telescope**: `Σ_j invⱼ = y` (path public slots `0 / 1`). -/
theorem path_export_telescope (hsat : (pathChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (pathChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ j ∈ Finset.range n, pathQ δF b hn nodes orbit chals pubs Q Path.xConsInv j =
      Quad.mk _ (pubs 0) (pubs 1) := by
  have hmem : ∀ e, e ∈ Path.qEqs δF → ∀ j, j < n → e.ev δF (pathEnvK δF b hn nodes orbit chals pubs Q j)
      (pathEnvF b hn nodes orbit chals pubs Q j) = 0 := fun e he j hj =>
    (path_gates δF b hn nodes orbit chals pubs Q hsat j hj).2 e he
  refine telescope n hn (pathQ δF b hn nodes orbit chals pubs Q Path.xAcc) _ _ ?_ ?_ ?_
  · have g := hmem (QE.scale (cv Path.isF) (QE.sub (QE.var Path.xAcc) (QE.var Path.xConsInv)))
      (by simp [Path.qEqs]) 0 hn
    rw [ev_scale, ev_sub] at g
    have hf : (CoeffExpr.eval (cv Path.isF) (pathEnvF b hn nodes orbit chals pubs Q 0) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]; rw [path_isF δF b hn nodes orbit chals pubs Q hbind hinj 0 hn]; simp
    rw [hf, liftQ, map_one, map_one, one_mul] at g
    exact sub_eq_zero.mp g
  · intro i hi
    have g := hmem (QE.scale (notE (cv Path.isL))
      (QE.sub (QE.sub (QE.next Path.xAcc) (QE.var Path.xAcc)) (QE.next Path.xConsInv)))
      (by simp [Path.qEqs]) i (by omega)
    rw [ev_scale, ev_sub, ev_sub, path_ev_next δF b hn nodes orbit chals pubs Q hadj i hi,
      path_ev_next δF b hn nodes orbit chals pubs Q hadj i hi] at g
    have hl : (CoeffExpr.eval (notE (cv Path.isL)) (pathEnvF b hn nodes orbit chals pubs Q i) : F) = 1 := by
      simp only [CoeffExpr.eval, cv, notE]
      rw [path_isL δF b hn nodes orbit chals pubs Q hbind hinj i (by omega), if_neg (by omega)]; simp
    rw [hl, liftQ, map_one, map_one, one_mul] at g
    linear_combination g
  · have g := hmem (QE.scale (cv Path.isL) (QE.sub (QE.var Path.xAcc) (QE.pub 0)))
      (by simp [Path.qEqs]) (n - 1) (by omega)
    rw [ev_scale, ev_sub, ev_pub] at g
    have hl : (CoeffExpr.eval (cv Path.isL) (pathEnvF b hn nodes orbit chals pubs Q (n - 1)) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]
      rw [path_isL δF b hn nodes orbit chals pubs Q hbind hinj (n - 1) (by omega), if_pos rfl]
    have hp : (pathEnvK δF b hn nodes orbit chals pubs Q (n - 1)).pub = pubs := by
      funext k; unfold pathEnvK; rw [pathEnvF_eq b hn nodes orbit chals pubs Q (n - 1) (by omega)]
      exact gather_pub_path δF b pubs _ rfl k
    rw [hl, liftQ, map_one, map_one, one_mul, hp] at g
    exact sub_eq_zero.mp g

theorem path_chal (j : ℕ) (hj : j < n) : (pathEnvK δF b hn nodes orbit chals pubs Q j).chal = chals := by
  funext k; unfold pathEnvK; rw [pathEnvF_eq b hn nodes orbit chals pubs Q j hj]
  exact gather_chal_path δF b chals _ rfl k

/-- The path export-consumer inverse: `inv·den(p, l, r, cellIdx, side) = 1`. -/
theorem path_xinv (hsat : (pathChip δF b hn nodes orbit chals pubs).rap.Satisfies Q) (j : ℕ) (hj : j < n) :
    (den δF Path.xKey).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q j) (pathEnvF b hn nodes orbit chals pubs Q j) ≠ 0 ∧
      pathQ δF b hn nodes orbit chals pubs Q Path.xConsInv j =
        ((den δF Path.xKey).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q j) (pathEnvF b hn nodes orbit chals pubs Q j))⁻¹ := by
  have g := (path_gates δF b hn nodes orbit chals pubs Q hsat j hj).2
    (QE.sub (QE.mul δF (QE.var Path.xConsInv) (den δF Path.xKey)) QE.one) (by simp [Path.qEqs])
  rw [ev_sub, ev_mul, ev_one] at g
  exact prov_inv δF g

/-- Every path row's consumed export key. -/
def pathXInternal : List (Fin 11 → Quad (algebraMap F K δF)) :=
  (List.range n).map fun j => pathKey δF b hn nodes orbit chals pubs Q 11 Path.xKey j

theorem path_compress (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) (j : ℕ) (hj : j < n) :
    FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (pathKey δF b hn nodes orbit chals pubs Q 11 Path.xKey j) =
      (den δF Path.xKey).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q j) (pathEnvF b hn nodes orbit chals pubs Q j) := by
  rw [den_ev_compress' δF Path.xKey (m := 11) rfl _ _ γ ρ
    (by rw [path_chal δF b hn nodes orbit chals pubs Q j hj]; exact hok)]

theorem path_internal_sum (hsat : (pathChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (pathChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) :
    ((pathXInternal δF b hn nodes orbit chals pubs Q).map fun r =>
      (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r)⁻¹).sum = Quad.mk _ (pubs 0) (pubs 1) := by
  rw [← path_export_telescope δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj, pathXInternal,
    List.map_map, list_range_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [Function.comp_apply, path_compress δF b hn nodes orbit chals pubs Q γ ρ hok j hj',
    (path_xinv δF b hn nodes orbit chals pubs Q hsat j hj').2]

end PathX

/-! ## 3. Both tables: the export IO facts and `EdgeExported` -/

section Both
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → F)
  (orbitC : StrictOrbitDomain F 3 hC) {hP nP : ℕ} (hnP : 0 < nP) (nodesP : Fin nP → F)
  (orbitP : StrictOrbitDomain F 3 hP) (chals pubsC pubsP : ℕ → K)
  (QC : Fin (cellChip δF b hnC nodesC orbitC chals pubsC).rap.w → F[X])
  (QP : Fin (pathChip δF b hnP nodesP orbitP chals pubsP).rap.w → F[X])

/-- **The export accumulator's weighted IO facts** (the frame's `IOFacts` at `m = 11`): providers
`cellXRecords`, internal = every path row's consumed key, terminal `ρ_X + Σ internal`, given the cell
terminal `ρ_X + y` (slots `2 / 3`) and the path terminal `y` (slots `0 / 1`). -/
def cellExportFacts
    (hsatC : (cellChip δF b hnC nodesC orbitC chals pubsC).rap.Satisfies QC)
    (hbindC : (cellChip δF b hnC nodesC orbitC chals pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hsatP : (pathChip δF b hnP nodesP orbitP chals pubsP).rap.Satisfies QP)
    (hbindP : (pathChip δF b hnP nodesP orbitP chals pubsP).BindsPreprocessing QP)
    (hinjP : Function.Injective nodesP)
    (hadjP : ∀ (i : Fin nP) (hi : (i : ℕ) + 1 < nP), nodesP ⟨(i : ℕ) + 1, hi⟩ = nodesP i * orbitP.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) (ρX : Quad (algebraMap F K δF))
    (hpub : Quad.mk _ (pubsC 2) (pubsC 3) = ρX + Quad.mk _ (pubsP 0) (pubsP 1)) :
    SVFrame.IOFacts F (FiniteIO.compress (m := 11) ⟨γ, ρ⟩)
      (ρX + ((pathXInternal δF b hnP nodesP orbitP chals pubsP QP).map fun r =>
          (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r)⁻¹).sum) where
  records := cellXRecords δF b hnC nodesC orbitC chals pubsC QC
  sum_eq := by
    rw [cell_export_sum δF b hnC nodesC orbitC chals pubsC QC hsatC hbindC hinjC hadjC γ ρ hok, hpub,
      path_internal_sum δF b hnP nodesP orbitP chals pubsP QP hsatP hbindP hinjP hadjP γ ρ hok]
  ne_zero := by
    intro r hr
    obtain ⟨i, -, hri⟩ := List.mem_flatMap.mp hr
    obtain ⟨⟨h0, -⟩, ⟨h1, -⟩⟩ := cell_xinv_facts δF b hnC nodesC orbitC chals pubsC QC hsatC i
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hri
    rcases hri with rfl | rfl
    · rw [cell_compress (m := 11) γ ρ hok (Cell.xKeyS 0) rfl le_rfl]; exact h0
    · rw [cell_compress (m := 11) γ ρ hok (Cell.xKeyS 1) rfl le_rfl]; exact h1

/-- **Decoding a matched export key**: a path row's consumed key equal to a cell row's side-`s`
record names that row's `(p, l, r)`, its serial, and the side. -/
theorem xKey_decode (j : ℕ) (i : Fin nC) (s : F)
    (hk : pathKey δF b hnP nodesP orbitP chals pubsP QP 11 Path.xKey j =
      cellKey δF b hnC nodesC orbitC chals pubsC QC 11 (Cell.xKeyS s) i) :
    (pathRows δF b hnP nodesP orbitP chals pubsP QP j).p =
        (cellRowOf δF (cellEnvK δF b nodesC orbitC chals pubsC QC i) (cellEnvF b nodesC orbitC chals pubsC QC i)).p ∧
      (pathRows δF b hnP nodesP orbitP chals pubsP QP j).l =
        (cellRowOf δF (cellEnvK δF b nodesC orbitC chals pubsC QC i) (cellEnvF b nodesC orbitC chals pubsC QC i)).l ∧
      (pathRows δF b hnP nodesP orbitP chals pubsP QP j).r =
        (cellRowOf δF (cellEnvK δF b nodesC orbitC chals pubsC QC i) (cellEnvF b nodesC orbitC chals pubsC QC i)).r ∧
      (pathRows δF b hnP nodesP orbitP chals pubsP QP j).cellIdx = cellB δF b hnC nodesC orbitC chals pubsC QC Cell.idx i ∧
      (pathRows δF b hnP nodesP orbitP chals pubsP QP j).side = s := by
  have e : ∀ c : Fin 11, _ := fun c => congrFun hk c
  have e0 := e ⟨0, by decide⟩; have e1 := e ⟨1, by decide⟩; have e2 := e ⟨2, by decide⟩
  have e3 := e ⟨3, by decide⟩; have e4 := e ⟨4, by decide⟩; have e5 := e ⟨5, by decide⟩
  have e6 := e ⟨6, by decide⟩; have e7 := e ⟨7, by decide⟩; have e8 := e ⟨8, by decide⟩
  have e9 := e ⟨9, by decide⟩; have e10 := e ⟨10, by decide⟩
  simp only [pathKey, cellKey, keyVec, Path.xKey, Cell.xKeyS, Cell.xKey, QFP.var, QFP.entries,
    List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
    at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [ev_base, ev_base, liftQ, liftQ] at e9 e10
  refine ⟨?_, ?_, ?_, (algebraMap F K).injective ((algebraMap K (Quad (algebraMap F K δF))).injective e9), ?_⟩
  · simp only [pathRows, pathRowOf, cellRowOf, QFP.ev, QFP.var, e0, e1, e2]
  · simp only [pathRows, pathRowOf, cellRowOf, QFP.ev, QFP.var, e3, e4, e5]
  · simp only [pathRows, pathRowOf, cellRowOf, QFP.ev, QFP.var, e6, e7, e8]
  · have := (algebraMap F K).injective ((algebraMap K (Quad (algebraMap F K δF))).injective e10)
    show (pathEnvF b hnP nodesP orbitP chals pubsP QP j).trace Path.side = s
    simpa [CoeffExpr.eval, cst] using this

variable [Fintype K] [DecidableEq (Quad (algebraMap F K δF))]

/-- **`EdgeExported` for every path row** from the export lookup: the compute side's export
requests `reqs` sum to `ρ_X`; outside the weighted IO event at `reqs ++ internal` (internal = the
path rows' consumed keys) with the consumer count below the characteristic, every path row's edge
`(p, l, r, side, natOf cellIdx)` is a cell-table row's `(p, l, r, idx)`, and the row's `side` is the
providing record's side slot. -/
theorem path_edges_exported
    (hsatC : (cellChip δF b hnC nodesC orbitC chals pubsC).rap.Satisfies QC)
    (hbindC : (cellChip δF b hnC nodesC orbitC chals pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hsatP : (pathChip δF b hnP nodesP orbitP chals pubsP).rap.Satisfies QP)
    (hbindP : (pathChip δF b hnP nodesP orbitP chals pubsP).BindsPreprocessing QP)
    (hinjP : Function.Injective nodesP)
    (hadjP : ∀ (i : Fin nP) (hi : (i : ℕ) + 1 < nP), nodesP ⟨(i : ℕ) + 1, hi⟩ = nodesP i * orbitP.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) (ρX : Quad (algebraMap F K δF))
    (hpub : Quad.mk _ (pubsC 2) (pubsC 3) = ρX + Quad.mk _ (pubsP 0) (pubsP 1))
    {p : ℕ} [CharP (Quad (algebraMap F K δF)) p] (reqs : List (Fin 11 → Quad (algebraMap F K δF)))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r)⁻¹).sum = ρX)
    (hne : ∀ r ∈ reqs, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r ≠ 0)
    (hγ : γ ∉ FiniteIO.IORLCCollisionEvent (FiniteIO.recordsW (reqs ++ pathXInternal δF b hnP nodesP orbitP chals pubsP QP)
      (SVFrame.liftWts (cellXRecords δF b hnC nodesC orbitC chals pubsC QC))))
    (hpole : ρ ∉ FiniteIO.IOLogDerivEventW (reqs ++ pathXInternal δF b hnP nodesP orbitP chals pubsP QP)
      (SVFrame.liftWts (cellXRecords δF b hnC nodesC orbitC chals pubsC QC)) γ)
    (hcount : (reqs ++ pathXInternal δF b hnP nodesP orbitP chals pubsP QP).length < p) :
    ∀ j < nP, EdgeExported (cellTableOf δF b nodesC orbitC chals pubsC QC)
      ⟨(pathRows δF b hnP nodesP orbitP chals pubsP QP j).p, (pathRows δF b hnP nodesP orbitP chals pubsP QP j).l,
        (pathRows δF b hnP nodesP orbitP chals pubsP QP j).r, (pathRows δF b hnP nodesP orbitP chals pubsP QP j).sideB,
        natOf (pathRows δF b hnP nodesP orbitP chals pubsP QP j).cellIdx⟩ := by
  set M := cellExportFacts δF b hnC nodesC orbitC hnP nodesP orbitP chals pubsC pubsP QC QP hsatC hbindC hinjC hadjC
    hsatP hbindP hinjP hadjP γ ρ hok ρX hpub with hM
  have hlook := FiniteIO.finiteIO_lookup_sound_weighted (p := p)
    (reqs ++ pathXInternal δF b hnP nodesP orbitP chals pubsP QP) (SVFrame.liftWts M.records) ⟨γ, ρ⟩
    (by
      intro r hr
      rcases List.mem_append.mp hr with h | h
      · exact hne r h
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
        have hj' := List.mem_range.mp hj
        rw [path_compress δF b hnP nodesP orbitP chals pubsP QP γ ρ hok j hj']
        exact (path_xinv δF b hnP nodesP orbitP chals pubsP QP hsatP j hj').1)
    (by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact M.ne_zero r hr)
    (by
      rw [List.map_append, List.sum_append, hsum]
      have := M.sum_eq
      simp only [SVFrame.liftWts, List.map_map, Function.comp_def]
      exact this.symm)
    hcount hγ hpole
  intro j hj
  have hr := hlook _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
  rw [SVFrame.liftWts_fst] at hr
  obtain ⟨q, hq, hqr⟩ := List.mem_map.mp hr
  obtain ⟨i, -, hqi⟩ := List.mem_flatMap.mp hq
  have hmem : cellRowOf δF (cellEnvK δF b nodesC orbitC chals pubsC QC i) (cellEnvF b nodesC orbitC chals pubsC QC i) ∈
      cellTableOf δF b nodesC orbitC chals pubsC QC := List.mem_ofFn.mpr ⟨i, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hqi
  rcases hqi with rfl | rfl
  · obtain ⟨hp, hl, hr', hidx, -⟩ := xKey_decode δF b hnC nodesC orbitC hnP nodesP orbitP chals pubsC pubsP QC QP
      j i 0 hqr.symm
    exact ⟨_, hmem, by rw [hidx]; rfl, hp.symm, hl.symm, hr'.symm⟩
  · obtain ⟨hp, hl, hr', hidx, -⟩ := xKey_decode δF b hnC nodesC orbitC hnP nodesP orbitP chals pubsC pubsP QC QP
      j i 1 hqr.symm
    exact ⟨_, hmem, by rw [hidx]; rfl, hp.symm, hl.symm, hr'.symm⟩

end Both

/-! ## 4. The path accumulator's own provider facts -/

section PathP
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (pathChip δF b hn nodes orbit chals pubs).rap.w → F[X])

abbrev pathB (c j : ℕ) : F := (pathEnvF b hn nodes orbit chals pubs Q j).trace c

/-- The path provider row term `m·inv`. -/
abbrev pT (j : ℕ) : Quad (algebraMap F K δF) :=
  liftQ δF (pathB δF b hn nodes orbit chals pubs Q Path.m j) * pathQ δF b hn nodes orbit chals pubs Q Path.pProvInv j

/-- **The path accumulator telescope**: `Σ_j m_j·inv_j = ρ_P` (path public slots `2 / 3`). -/
theorem path_provider_telescope (hsat : (pathChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (pathChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ j ∈ Finset.range n, pT δF b hn nodes orbit chals pubs Q j = Quad.mk _ (pubs 2) (pubs 3) := by
  have hmem : ∀ e, e ∈ Path.qEqs δF → ∀ j, j < n → e.ev δF (pathEnvK δF b hn nodes orbit chals pubs Q j)
      (pathEnvF b hn nodes orbit chals pubs Q j) = 0 := fun e he j hj =>
    (path_gates δF b hn nodes orbit chals pubs Q hsat j hj).2 e he
  refine telescope n hn (pathQ δF b hn nodes orbit chals pubs Q Path.pAcc) _ _ ?_ ?_ ?_
  · have g := hmem (QE.scale (cv Path.isF) (QE.sub (QE.var Path.pAcc) (QE.scale (cv Path.m) (QE.var Path.pProvInv))))
      (by simp [Path.qEqs]) 0 hn
    rw [ev_scale, ev_sub, ev_scale] at g
    have hf : (CoeffExpr.eval (cv Path.isF) (pathEnvF b hn nodes orbit chals pubs Q 0) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]; rw [path_isF δF b hn nodes orbit chals pubs Q hbind hinj 0 hn]; simp
    rw [hf, liftQ, map_one, map_one, one_mul] at g
    exact sub_eq_zero.mp g
  · intro i hi
    have g := hmem (QE.scale (notE (cv Path.isL))
      (QE.sub (QE.sub (QE.next Path.pAcc) (QE.var Path.pAcc)) (QE.scale (nv Path.m) (QE.next Path.pProvInv))))
      (by simp [Path.qEqs]) i (by omega)
    rw [ev_scale, ev_sub, ev_sub, ev_scale, path_ev_next δF b hn nodes orbit chals pubs Q hadj i hi,
      path_ev_next δF b hn nodes orbit chals pubs Q hadj i hi] at g
    have hl : (CoeffExpr.eval (notE (cv Path.isL)) (pathEnvF b hn nodes orbit chals pubs Q i) : F) = 1 := by
      simp only [CoeffExpr.eval, cv, notE]
      rw [path_isL δF b hn nodes orbit chals pubs Q hbind hinj i (by omega), if_neg (by omega)]; simp
    have hm : (CoeffExpr.eval (nv Path.m) (pathEnvF b hn nodes orbit chals pubs Q i) : F) =
        pathB δF b hn nodes orbit chals pubs Q Path.m (i + 1) := by
      simp only [CoeffExpr.eval, nv]; exact path_traceNext δF b hn nodes orbit chals pubs Q hadj i hi _
    rw [hl, hm, liftQ, map_one, map_one, one_mul] at g
    linear_combination g
  · have g := hmem (QE.scale (cv Path.isL) (QE.sub (QE.var Path.pAcc) (QE.pub 2)))
      (by simp [Path.qEqs]) (n - 1) (by omega)
    rw [ev_scale, ev_sub, ev_pub] at g
    have hl : (CoeffExpr.eval (cv Path.isL) (pathEnvF b hn nodes orbit chals pubs Q (n - 1)) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]
      rw [path_isL δF b hn nodes orbit chals pubs Q hbind hinj (n - 1) (by omega), if_pos rfl]
    have hp : (pathEnvK δF b hn nodes orbit chals pubs Q (n - 1)).pub = pubs := by
      funext k; unfold pathEnvK; rw [pathEnvF_eq b hn nodes orbit chals pubs Q (n - 1) (by omega)]
      exact gather_pub_path δF b pubs _ rfl k
    rw [hl, liftQ, map_one, map_one, one_mul, hp] at g
    exact sub_eq_zero.mp g

/-- Row `j`'s provider facts: `last ∈ {0, 1}`; `last = 0 ⇒ m = 0`; `last = 1 ⇒ inv = den(pRec)⁻¹ ≠ 0`. -/
theorem path_pinv (hsat : (pathChip δF b hn nodes orbit chals pubs).rap.Satisfies Q) (j : ℕ) (hj : j < n) :
    (pathB δF b hn nodes orbit chals pubs Q Path.last j = 0 ∨ pathB δF b hn nodes orbit chals pubs Q Path.last j = 1) ∧
    (pathB δF b hn nodes orbit chals pubs Q Path.last j = 0 → pathB δF b hn nodes orbit chals pubs Q Path.m j = 0) ∧
    (pathB δF b hn nodes orbit chals pubs Q Path.last j = 1 →
      (den δF Path.pRec).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q j) (pathEnvF b hn nodes orbit chals pubs Q j) ≠ 0 ∧
      pathQ δF b hn nodes orbit chals pubs Q Path.pProvInv j =
        ((den δF Path.pRec).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q j) (pathEnvF b hn nodes orbit chals pubs Q j))⁻¹) := by
  obtain ⟨hb, hm⟩ := path_gates δF b hn nodes orbit chals pubs Q hsat j hj
  refine ⟨bool_of_gate _ Path.last (by simp [Path.baseGates]) hb, fun h0 => ?_, fun h1 => ?_⟩
  · have g := hb (.mul (notE (cv Path.last)) (cv Path.m)) (by simp [Path.baseGates])
    simp only [CoeffExpr.eval, cv, notE] at g
    rw [show (pathEnvF b hn nodes orbit chals pubs Q j).trace Path.last = 0 from h0, sub_zero, one_mul] at g
    exact g
  · have g := hm (QE.scale (cv Path.last) (QE.sub (QE.mul δF (QE.var Path.pProvInv) (den δF Path.pRec)) QE.one))
      (by simp [Path.qEqs])
    rw [ev_scale, ev_sub, ev_mul, ev_one] at g
    simp only [CoeffExpr.eval, cv] at g
    rw [show (pathEnvF b hn nodes orbit chals pubs Q j).trace Path.last = 1 from h1, liftQ, map_one, map_one,
      one_mul] at g
    exact prov_inv δF g

theorem list_filter_sum {M : Type*} [AddCommMonoid M] (l : List ℕ) (P : ℕ → Prop) [DecidablePred P]
    (g : ℕ → M) : ((l.filter fun j => decide (P j)).map g).sum = (l.map fun j => if P j then g j else 0).sum := by
  induction l with
  | nil => simp
  | cons a t ih => by_cases h : P a <;> simp [List.filter_cons, h, ih]

/-- The path providers: one `(pRec, m)` per record (`last`) row. -/
def pathPRecords : List ((Fin 8 → Quad (algebraMap F K δF)) × F) :=
  ((List.range n).filter fun j => pathB δF b hn nodes orbit chals pubs Q Path.last j = 1).map fun j =>
    (pathKey δF b hn nodes orbit chals pubs Q 8 Path.pRec j, pathB δF b hn nodes orbit chals pubs Q Path.m j)

theorem path_compress8 (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) (j : ℕ) (hj : j < n) :
    FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (pathKey δF b hn nodes orbit chals pubs Q 8 Path.pRec j) =
      (den δF Path.pRec).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q j) (pathEnvF b hn nodes orbit chals pubs Q j) := by
  rw [den_ev_compress' δF Path.pRec (m := 8) rfl _ _ γ ρ
    (by rw [path_chal δF b hn nodes orbit chals pubs Q j hj]; exact chalsOK_mono δF (by norm_num) hok)]

/-- **The path accumulator's weighted IO facts** (the frame's `IOFacts` at `m = 8`, no internal
consumer): providers = the record rows `(pRec, m)`, terminal `ρ_P` (slots `2 / 3`). -/
def pathProviderFacts (hsat : (pathChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (pathChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) :
    SVFrame.IOFacts F (FiniteIO.compress (m := 8) ⟨γ, ρ⟩) (Quad.mk _ (pubs 2) (pubs 3)) where
  records := pathPRecords δF b hn nodes orbit chals pubs Q
  sum_eq := by
    rw [← path_provider_telescope δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj, pathPRecords,
      List.map_map, list_filter_sum, list_range_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn := Finset.mem_range.mp hj
    obtain ⟨hbool, hm0, hinv⟩ := path_pinv δF b hn nodes orbit chals pubs Q hsat j hjn
    simp only [Function.comp_apply]
    split_ifs with hl
    · rw [path_compress8 δF b hn nodes orbit chals pubs Q γ ρ hok j hjn]
      simp only [pT, (hinv hl).2, liftQ, IsScalarTower.algebraMap_apply F K (Quad (algebraMap F K δF))]
    · rw [pT, hm0 (hbool.resolve_right hl)]; simp [liftQ]
  ne_zero := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hjr, hjl⟩ := List.mem_filter.mp hj
    have hjn := List.mem_range.mp hjr
    rw [path_compress8 δF b hn nodes orbit chals pubs Q γ ρ hok j hjn]
    exact ((path_pinv δF b hn nodes orbit chals pubs Q hsat j hjn).2.2 (by simpa using hjl)).1

end PathP

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
