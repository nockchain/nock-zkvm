/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/RoundsCellP1.lean

 **Trace uniqueness on the P1 fragment: the cell table's rounds 1 and 2.**

 Two traces `Q`, `Q'` of the wire-key cell chip `cellChipHQKW`, at one coin vector and possibly different
 public vectors, with equal round-0 columns (the first `134`), have equal round-1 and round-2 columns, and equal
 terminal publics `0 .. 5`.

 * §1 generic pieces: a `𝕂′` accumulator `a (i+1) − a i = t (i+1)` started at the first row is determined by its
 terms (`acc_rows_eq`); a denominator reads only the entries' values (`den_congr`); provider and consumer
 inverse columns are determined by an equal denominator (`prov_roles`, `cons_roles`).
 * §2 the wire chip's row facts: the gates of `Cell.qEqs` and the base gates hold in the gathered environments
 (`cellW_rowLocal`), the restriction to the `225`-column cell chip reads the same columns (`hqk_trace_shift`,
 `cellEnvK_trace_eq`).
 * §3 round 1: the fingerprint roles `p l r` (`𝕂`-roles `0 .. 17`) are equal, by `cell_fps_eq` on the accepted
 tables of the restrictions (`cell_round1_eq`).
 * §4 round 2: the six inverse roles, the validity and export accumulators and the handle-export inverse and
 accumulator (`cell_round2_eq`); the terminal publics (`cell_pubs_eq`).
 * §5 the columns: `cell_cols_eq` states it on every column of `tr.M` at every row node.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsP1

/-! ## 1. Generic pieces -/

theorem mem_fst_zipIdx {α : Type} : ∀ (l : List α) (k : ℕ) (ei : α × ℕ), ei ∈ l.zipIdx k → ei.1 ∈ l
  | [], k, ei, h => by simp at h
  | a :: t, k, ei, h => by
    simp only [List.zipIdx_cons, List.mem_cons] at h
    rcases h with h | h
    · simp [h]
    · exact List.mem_cons_of_mem _ (mem_fst_zipIdx t _ _ h)

section Generic
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **A `𝕂′` accumulator is determined by its terms.** Two families of row environments carry an accumulator
column pair `accC, accC + 1` with the init gate `isF·(acc − t)`, the step gate `(1 − isL)·(acc′ − acc − t′)`, equal
terms and the same first / last masks; then the accumulators agree on every row. -/
theorem acc_rows_eq {n : ℕ} (hn : 0 < n) (accC : ℕ) (tC tN : QE F)
    (eK eK' : Fin n → Env K) (eF eF' : Fin n → Env F)
    (hFi : ∀ i : Fin n, (eF i).trace Cell.isF = if (i : ℕ) = 0 then 1 else 0)
    (hLa : ∀ i : Fin n, (eF i).trace Cell.isL = if (i : ℕ) = n - 1 then 1 else 0)
    (hFi' : ∀ i : Fin n, (eF' i).trace Cell.isF = if (i : ℕ) = 0 then 1 else 0)
    (hLa' : ∀ i : Fin n, (eF' i).trace Cell.isL = if (i : ℕ) = n - 1 then 1 else 0)
    (g0 : ∀ i : Fin n, (QE.scale (cv Cell.isF) (QE.sub (QE.var accC) tC)).ev δF (eK i) (eF i) = 0)
    (g0' : ∀ i : Fin n, (QE.scale (cv Cell.isF) (QE.sub (QE.var accC) tC)).ev δF (eK' i) (eF' i) = 0)
    (gs : ∀ i : Fin n, (QE.scale (notE (cv Cell.isL))
      (QE.sub (QE.sub (QE.next accC) (QE.var accC)) tN)).ev δF (eK i) (eF i) = 0)
    (gs' : ∀ i : Fin n, (QE.scale (notE (cv Cell.isL))
      (QE.sub (QE.sub (QE.next accC) (QE.var accC)) tN)).ev δF (eK' i) (eF' i) = 0)
    (hsh : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      tN.ev δF (eK i) (eF i) = tC.ev δF (eK ⟨(i : ℕ) + 1, hi⟩) (eF ⟨(i : ℕ) + 1, hi⟩))
    (hsh' : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
      tN.ev δF (eK' i) (eF' i) = tC.ev δF (eK' ⟨(i : ℕ) + 1, hi⟩) (eF' ⟨(i : ℕ) + 1, hi⟩))
    (hnx : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ),
      (eK i).traceNext r = (eK ⟨(i : ℕ) + 1, hi⟩).trace r)
    (hnx' : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ),
      (eK' i).traceNext r = (eK' ⟨(i : ℕ) + 1, hi⟩).trace r)
    (hT : ∀ i : Fin n, tC.ev δF (eK i) (eF i) = tC.ev δF (eK' i) (eF' i)) :
    ∀ i : Fin n, (eK i).trace accC = (eK' i).trace accC ∧ (eK i).trace (accC + 1) = (eK' i).trace (accC + 1) := by
  classical
  let A : (Fin n → Env K) → ℕ → Quad (algebraMap F K δF) := fun e j =>
    if h : j < n then Quad.mk _ ((e ⟨j, h⟩).trace accC) ((e ⟨j, h⟩).trace (accC + 1)) else 0
  let S : (Fin n → Env K) → (Fin n → Env F) → ℕ → Quad (algebraMap F K δF) := fun e f j =>
    if h : j < n then tC.ev δF (e ⟨j, h⟩) (f ⟨j, h⟩) else 0
  have hone : ∀ (e : Fin n → Env K) (f : Fin n → Env F),
      (∀ i : Fin n, (f i).trace Cell.isF = if (i : ℕ) = 0 then 1 else 0) →
      (∀ i : Fin n, (f i).trace Cell.isL = if (i : ℕ) = n - 1 then 1 else 0) →
      (∀ i : Fin n, (QE.scale (cv Cell.isF) (QE.sub (QE.var accC) tC)).ev δF (e i) (f i) = 0) →
      (∀ i : Fin n, (QE.scale (notE (cv Cell.isL))
        (QE.sub (QE.sub (QE.next accC) (QE.var accC)) tN)).ev δF (e i) (f i) = 0) →
      (∀ (i : Fin n) (hi : (i : ℕ) + 1 < n),
        tN.ev δF (e i) (f i) = tC.ev δF (e ⟨(i : ℕ) + 1, hi⟩) (f ⟨(i : ℕ) + 1, hi⟩)) →
      (∀ (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ), (e i).traceNext r = (e ⟨(i : ℕ) + 1, hi⟩).trace r) →
      A e 0 = S e f 0 ∧ ∀ i, i + 1 < n → A e (i + 1) - A e i = S e f (i + 1) := by
    intro e f hF hL g0 gs hsh hnx
    refine ⟨?_, ?_⟩
    · simp only [A, S, dif_pos hn]
      have g := g0 ⟨0, hn⟩
      rw [ev_scale, ev_sub, ev_var] at g
      have hf : (cv Cell.isF : CoeffExpr F).eval (f ⟨0, hn⟩) = 1 := by
        simp only [CoeffExpr.eval, cv]; rw [hF ⟨0, hn⟩]; simp
      rw [hf, liftQ, map_one, map_one, one_mul] at g
      exact sub_eq_zero.mp g
    · intro i hi
      have hi0 : i < n := by omega
      simp only [A, S, dif_pos hi, dif_pos hi0]
      have g := gs ⟨i, hi0⟩
      rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var] at g
      have hl : (notE (cv Cell.isL) : CoeffExpr F).eval (f ⟨i, hi0⟩) = 1 := by
        simp only [CoeffExpr.eval, cv, notE]
        rw [hL ⟨i, hi0⟩, if_neg (by simp; omega)]; simp
      rw [hl, liftQ, map_one, map_one, one_mul, hsh ⟨i, hi0⟩ hi] at g
      simp only [hnx ⟨i, hi0⟩ hi] at g
      linear_combination g
  obtain ⟨h0, hs⟩ := hone eK eF hFi hLa g0 gs hsh hnx
  obtain ⟨h0', hs'⟩ := hone eK' eF' hFi' hLa' g0' gs' hsh' hnx'
  have key := acc_unique n (A eK) (A eK') (S eK eF) (S eK' eF') h0 h0'
    (fun i hi => by simp only [S, dif_pos hi]; exact hT ⟨i, hi⟩) hs hs'
  intro i
  have := key i i.isLt
  simp only [A, dif_pos i.isLt, Quad.mk_eq_mk_iff] at this
  exact this

/-- **A denominator reads only the entries' values and the coins.** -/
theorem den_congr {eK eK' : Env K} {eF eF' : Env F} (es : List (QE F)) (hch : eK.chal = eK'.chal)
    (h : ∀ e ∈ es, e.ev δF eK eF = e.ev δF eK' eF') :
    (den δF es).ev δF eK eF = (den δF es).ev δF eK' eF' := by
  rw [ev_den, ev_den, ev_rlc, ev_rlc]
  have h1 : (rQ : QE F).ev δF eK eF = (rQ : QE F).ev δF eK' eF' := by
    simp only [rQ, ev_chal, hch]
  rw [h1]
  congr 1
  congr 1
  refine List.map_congr_left fun ei hei => ?_
  rw [ev_gpow, ev_gpow, hch, h ei.1 (mem_fst_zipIdx _ _ _ hei)]

/-- **A provider inverse role pair is determined by an equal denominator** (`inv·den = 1`). -/
theorem prov_roles {eK eK' : Env K} {eF eF' : Env F} (r : ℕ) (d : QE F)
    (g : (QE.sub (QE.mul δF (QE.var r) d) QE.one).ev δF eK eF = 0)
    (g' : (QE.sub (QE.mul δF (QE.var r) d) QE.one).ev δF eK' eF' = 0)
    (hd : d.ev δF eK eF = d.ev δF eK' eF') :
    eK.trace r = eK'.trace r ∧ eK.trace (r + 1) = eK'.trace (r + 1) := by
  rw [ev_sub, ev_mul, ev_one, ev_var] at g g'
  have := (prov_inv δF g).2.trans (hd ▸ (prov_inv δF g').2.symm)
  simpa only [Quad.mk_eq_mk_iff] using this

/-- **A consumer inverse role pair is determined by an equal denominator and an equal weight**
(`inv·den = w`, `(1 − w)·inv = 0`, `w ∈ {0, 1}`). -/
theorem cons_roles {eK eK' : Env K} {eF eF' : Env F} (r : ℕ) (d : QE F) (w : ℕ)
    (hw : eF.trace w = 0 ∨ eF.trace w = 1) (hw' : eF'.trace w = 0 ∨ eF'.trace w = 1)
    (hww : eF.trace w = eF'.trace w)
    (g : (QE.sub (QE.mul δF (QE.var r) d) (QE.base (cv w))).ev δF eK eF = 0)
    (g' : (QE.sub (QE.mul δF (QE.var r) d) (QE.base (cv w))).ev δF eK' eF' = 0)
    (z : (QE.scale (notE (cv w)) (QE.var r)).ev δF eK eF = 0)
    (z' : (QE.scale (notE (cv w)) (QE.var r)).ev δF eK' eF' = 0)
    (hd : d.ev δF eK eF = d.ev δF eK' eF') :
    eK.trace r = eK'.trace r ∧ eK.trace (r + 1) = eK'.trace (r + 1) := by
  rw [ev_sub, ev_mul, ev_base] at g g'
  rw [ev_scale] at z z'
  simp only [CoeffExpr.eval, cv, notE] at g g' z z'
  rw [ev_var] at g g' z z'
  have a := (cons_inv δF hw g z).2
  have a' := (cons_inv δF hw' g' z').2
  rw [← hww, ← hd] at a'
  have := a.trans a'.symm
  simpa only [Quad.mk_eq_mk_iff] using this

end Generic

/-! ## 2. The wire chip's row facts -/

section Wire
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals : ℕ → K)

/-- **The wire chip's row gates** at every row node: the base gates, the `𝕂′` equations of the cell table, and
the four handle-export gates. -/
theorem cellW_rowLocal (pubs : ℕ → K) {Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]}
    (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (∀ g ∈ Cell.baseGates (F := F), g.eval (hqkEF b nodes orbit chals pubs Q i) = 0) ∧
    (∀ e ∈ Cell.qEqs δF, e.ev δF (wEK δF b nodes orbit chals pubs Q i) (hqkEF b nodes orbit chals pubs Q i) = 0) ∧
    (∀ e ∈ gatesQ δF, e.ev δF (wEK δF b nodes orbit chals pubs Q i) (hqkEF b nodes orbit chals pubs Q i) = 0) := by
  have hl := (expandChip_satisfies_iff_language (cellTemplateHQKW δF) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  refine ⟨fun g hg => hl.1 g (List.mem_append_left _ hg), fun e he => ?_, fun e he => ?_⟩
  · exact ev_eq_zero_of_gates δF _ _ e fun g hg =>
      hl.2.2.2 g (List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hg⟩))
  · exact ev_eq_zero_of_gates δF _ _ e fun g hg =>
      hl.2.2.2 g (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩))

/-- The first / last masks of the wire chip at a row. -/
theorem cellW_masks (pubs : ℕ → K) {Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]}
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (hqkEF b nodes orbit chals pubs Q i).trace Cell.isF = (if (i : ℕ) = 0 then 1 else 0) ∧
      (hqkEF b nodes orbit chals pubs Q i).trace Cell.isL = (if (i : ℕ) = n - 1 then 1 else 0) :=
  cellHQKW_masks δF b hn nodes orbit chals pubs Q hbind hinj i

/-- The restriction to the `225`-column cell chip reads, at the extension columns, the wire chip's columns shifted
by `5`. -/
theorem hqk_trace_shift (pubs : ℕ → K) (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]) (i : Fin n) {c : ℕ} (hc : c < 96) :
    (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i).trace (129 + c) =
      (hqkEF b nodes orbit chals pubs Q i).trace (134 + c) := by
  have hw : (cellChip δF b hn nodes orbit chals pubs).rap.w = 225 :=
    (cellChip_fingerprint δF b hn nodes orbit chals pubs).1
  have h0 : 129 + c < (cellChip δF b hn nodes orbit chals pubs).rap.w := by rw [hw]; omega
  have h1 : 134 + c < (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w := by
    rw [cellChipHQKW_width]; omega
  simp only [cellEnvF, Reify.envOfTrace, dif_pos h0, dif_pos h1, restrictHQKWCell, restrictQ]
  congr 2
  apply Fin.ext
  simp only [shiftCol]
  split_ifs <;> omega

/-- **The restricted chip's `𝕂` roles are the wire chip's** (roles `0 .. 31`). -/
theorem cellEnvK_trace_eq (pubs : ℕ → K) (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]) (i : Fin n) {r : ℕ} (hr : r < 32) :
    (cellEnvK δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i).trace r =
      (wEK δF b nodes orbit chals pubs Q i).trace r := by
  simp only [cellEnvK, wEK, gatherEnv, ChipTemplate.col0, cellTemplate_baseCols, cellTemplateHQKW_baseCols]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := k.isLt
  have := hqk_trace_shift δF b hn nodes orbit chals pubs Q i (c := 3 * r + k) (by omega)
  rw [show 129 + 3 * r + (k : ℕ) = 129 + (3 * r + k) by ring, show 134 + 3 * r + (k : ℕ) = 134 + (3 * r + k) by ring,
    this]


/-- The first / last masks as the nat-indexed forms used by the accumulators. -/
theorem keyVec5_keyHK_congr {e e' : Env F} (h : ∀ j < 134, e.trace j = e'.trace j) :
    (ServeH.keyVec5 (K := K) (keyHK (F := F)) e) = ServeH.keyVec5 (keyHK (F := F)) e' := by
  have h1 := h Cell.idx (by decide)
  have h2 := h Cell.wL (by decide)
  have h3 := h CellTwinK.kbL (by decide)
  have h4 := h Cell.idL (by decide)
  have h5 := h Cell.aL (by decide)
  have h6 := h Cell.wR (by decide)
  have h7 := h CellTwinK.kbR (by decide)
  have h8 := h Cell.idR (by decide)
  have h9 := h Cell.aR (by decide)
  funext c
  simp only [ServeH.keyVec5]
  congr 1
  fin_cases c <;>
    simp [keyHK, CellH.valE, CoeffExpr.eval, cv, notE, h1, h2, h3, h4, h5, h6, h7, h8, h9]

end Wire

/-! ## 3. Equal denominators from equal round-1 roles -/

section Keys
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  {eK eK' : Env K} {eF eF' : Env F}

theorem var_cong (hK : ∀ r < 18, eK.trace r = eK'.trace r) (r : ℕ) (hr : r + 1 < 18) :
    (QE.var r : QE F).ev δF eK eF = (QE.var r : QE F).ev δF eK' eF' := by
  rw [ev_var, ev_var, hK r (by omega), hK (r + 1) hr]

theorem base_cv_cong (hF : ∀ j < 134, eF.trace j = eF'.trace j) (j : ℕ) (hj : j < 134) :
    (QE.base (cv j) : QE F).ev δF eK eF = (QE.base (cv j) : QE F).ev δF eK' eF' := by
  rw [ev_base, ev_base]; simp only [CoeffExpr.eval, cv]; rw [hF j hj]

theorem base_cst_cong (c : F) :
    (QE.base (cst c) : QE F).ev δF eK eF = (QE.base (cst c) : QE F).ev δF eK' eF' := by
  rw [ev_base, ev_base]; rfl

theorem mk2_cv_cong (hF : ∀ j < 134, eF.trace j = eF'.trace j) (j j' : ℕ) (hj : j < 134) (hj' : j' < 134) :
    (QE.mk2 (cv j) (cv j') : QE F).ev δF eK eF = (QE.mk2 (cv j) (cv j') : QE F).ev δF eK' eF' := by
  rw [ev_mk2, ev_mk2]; simp only [CoeffExpr.eval, cv]; rw [hF j hj, hF j' hj']

/-- **The five denominators of the cell table read round-1 roles `0 .. 17` and round-0 columns only.** -/
theorem keys_cong (hK : ∀ r < 18, eK.trace r = eK'.trace r) (hF : ∀ j < 134, eF.trace j = eF'.trace j) :
    (∀ e ∈ (Cell.vKeyP : List (QE F)), e.ev δF eK eF = e.ev δF eK' eF') ∧
    (∀ e ∈ (Cell.vKeyL : List (QE F)), e.ev δF eK eF = e.ev δF eK' eF') ∧
    (∀ e ∈ (Cell.vKeyR : List (QE F)), e.ev δF eK eF = e.ev δF eK' eF') ∧
    (∀ e ∈ (Cell.xKeyS (0 : F)), e.ev δF eK eF = e.ev δF eK' eF') ∧
    (∀ e ∈ (Cell.xKeyS (1 : F)), e.ev δF eK eF = e.ev δF eK' eF') := by
  have V : ∀ r, r + 1 < 18 → (QE.var r : QE F).ev δF eK eF = (QE.var r : QE F).ev δF eK' eF' :=
    fun r hr => var_cong δF hK r hr
  have B : ∀ j, j < 134 → (QE.base (cv j) : QE F).ev δF eK eF = (QE.base (cv j) : QE F).ev δF eK' eF' :=
    fun j hj => base_cv_cong δF hF j hj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [Cell.vKeyP, QFP.entries, QFP.var, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact mk2_cv_cong δF hF _ _ (by decide) (by decide)
    · exact B _ (by decide)
  · intro e he
    simp only [Cell.vKeyL, QFP.entries, QFP.var, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact mk2_cv_cong δF hF _ _ (by decide) (by decide)
    · exact B _ (by decide)
  · intro e he
    simp only [Cell.vKeyR, QFP.entries, QFP.var, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact mk2_cv_cong δF hF _ _ (by decide) (by decide)
    · exact B _ (by decide)
  · intro e he
    simp only [Cell.xKeyS, Cell.xKey, QFP.entries, QFP.var, List.cons_append, List.nil_append, List.append_assoc,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact B _ (by decide)
    · exact base_cst_cong δF _
  · intro e he
    simp only [Cell.xKeyS, Cell.xKey, QFP.entries, QFP.var, List.cons_append, List.nil_append, List.append_assoc,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact B _ (by decide)
    · exact base_cst_cong δF _

/-- The roles of a `QFP` at equal values are equal. -/
theorem qfp_roles {r : ℕ}
    (h : (QFP.var r : QFP F).ev δF eK eF = (QFP.var r : QFP F).ev δF eK' eF') :
    ∀ k < 6, eK.trace (r + k) = eK'.trace (r + k) := by
  rw [QFP.ev_var, QFP.ev_var] at h
  injection h with h1 h2 h3
  rw [ev_var, ev_var, Quad.mk_eq_mk_iff] at h1 h2 h3
  intro k hk
  interval_cases k
  · simpa using h1.1
  · simpa using h1.2
  · simpa using h2.1
  · simpa [add_assoc] using h2.2
  · simpa using h3.1
  · simpa [add_assoc] using h3.2

end Keys


/-! ## 4. Rounds 1 and 2 of the wire chip -/

section Round
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs pubs' : ℕ → K)

/-- **Round 1.** Two traces of the wire chip (one coin vector, public vectors `pubs`, `pubs'`) with equal
round-0 columns and `ValidityServed` tables have equal fingerprint roles `p l r` (`𝕂`-roles `0 .. 17`):
`cell_fps_eq` on the accepted tables of the restrictions to the `225`-column chip. -/
theorem cell_round1_eq (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    {Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]}
    {Q' : Fin (cellChipHQKW δF b hn nodes orbit chals pubs').rap.w → F[X]}
    (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hsat' : (cellChipHQKW δF b hn nodes orbit chals pubs').rap.Satisfies Q')
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hbind' : (cellChipHQKW δF b hn nodes orbit chals pubs').BindsPreprocessing Q')
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (hserved : ValidityServed (cellTableOf δF b nodes orbit chals pubs
      (restrictHQKWCell δF b hn nodes orbit chals pubs Q)))
    (hserved' : ValidityServed (cellTableOf δF b nodes orbit chals pubs'
      (restrictHQKWCell δF b hn nodes orbit chals pubs' Q')))
    (h0 : ∀ (i : Fin n) (j : ℕ), j < 134 →
      (hqkEF b nodes orbit chals pubs Q i).trace j = (hqkEF b nodes orbit chals pubs' Q' i).trace j) :
    ∀ (i : Fin n), ∀ r < 18,
      (wEK δF b nodes orbit chals pubs Q i).trace r = (wEK δF b nodes orbit chals pubs' Q' i).trace r := by
  have hsat0 := cellChipHQKW_restrict_cell_sat δF b hn nodes orbit chals pubs Q hsat
  have hbind0 := cellChipHQKW_restrict_bind δF b hn nodes orbit chals pubs Q hbind
  have hsat0' := cellChipHQKW_restrict_cell_sat δF b hn nodes orbit chals pubs' Q' hsat'
  have hbind0' := cellChipHQKW_restrict_bind δF b hn nodes orbit chals pubs' Q' hbind'
  have hA := cellTable_accepts δF b hn nodes orbit chals pubs _ hsat0 hF hq hz hbind0 hinj hadj hnp hserved []
  have hA' := cellTable_accepts δF b hn nodes orbit chals pubs' _ hsat0' hF hq hz hbind0' hinj hadj hnp
    hserved' []
  have hbi : ∀ i : Fin n,
      cellB0Of (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i) =
        cellB0Of (cellEnvF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i) := by
    intro i
    rw [← cellB0Of_hqkw δF b hn nodes orbit chals pubs Q i, ← cellB0Of_hqkw δF b hn nodes orbit chals pubs' Q' i]
    exact cellB0Of_congr (fun j hj => h0 i j (by omega))
  have hb0 : (cellTableOf δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q)).map
      (·.b0) = (cellTableOf δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q')).map
      (·.b0) := by
    unfold cellTableOf
    rw [List.map_ofFn, List.map_ofFn]
    congr 1
    funext i
    exact hbi i
  intro i r hr
  have hc : cellRowOf δF (cellEnvK δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i) ∈
      cellTableOf δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hc' : cellRowOf δF (cellEnvK δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i)
      (cellEnvF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i) ∈
      cellTableOf δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  obtain ⟨hp, hl, hrr⟩ := cell_fps_eq hq hz hA hA' hb0 hc hc' (hbi i)
  have hpp : (QFP.var Cell.pR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i) =
      (QFP.var Cell.pR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i)
      (cellEnvF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i) := hp
  have hll : (QFP.var Cell.lR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i) =
      (QFP.var Cell.lR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i)
      (cellEnvF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i) := hl
  have hrr' : (QFP.var Cell.rR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q) i) =
      (QFP.var Cell.rR : QFP F).ev δF
      (cellEnvK δF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i)
      (cellEnvF b nodes orbit chals pubs' (restrictHQKWCell δF b hn nodes orbit chals pubs' Q') i) := hrr
  rw [← cellEnvK_trace_eq δF b hn nodes orbit chals pubs Q i (by omega),
    ← cellEnvK_trace_eq δF b hn nodes orbit chals pubs' Q' i (by omega)]
  rcases (by omega : r < 6 ∨ (6 ≤ r ∧ r < 12) ∨ 12 ≤ r) with h | h | h
  · have := qfp_roles δF hpp r (by show r < 6; omega)
    simpa [Cell.pR] using this
  · have := qfp_roles δF hll (r - 6) (by omega)
    simpa [Cell.lR, show 6 + (r - 6) = r by omega] using this
  · have := qfp_roles δF hrr' (r - 12) (by omega)
    simpa [Cell.rR, show 12 + (r - 12) = r by omega] using this


/-- **Round 2.** With equal round-0 columns and equal round-1 roles, every round-2 role is equal: the six inverse
pairs (`inv·den = 1`, or `inv·den = w` with `(1 − w)·inv = 0`), the validity accumulator (roles `26, 27`), the
export accumulator (`28, 29`) and the handle-export accumulator (`34, 35`), by induction from the first row. -/
theorem cell_round2_eq
    {Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]}
    {Q' : Fin (cellChipHQKW δF b hn nodes orbit chals pubs').rap.w → F[X]}
    (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hsat' : (cellChipHQKW δF b hn nodes orbit chals pubs').rap.Satisfies Q')
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hbind' : (cellChipHQKW δF b hn nodes orbit chals pubs').BindsPreprocessing Q')
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (h0 : ∀ (i : Fin n) (j : ℕ), j < 134 →
      (hqkEF b nodes orbit chals pubs Q i).trace j = (hqkEF b nodes orbit chals pubs' Q' i).trace j)
    (h1 : ∀ (i : Fin n), ∀ r < 18,
      (wEK δF b nodes orbit chals pubs Q i).trace r = (wEK δF b nodes orbit chals pubs' Q' i).trace r) :
    ∀ (i : Fin n), ∀ r < 36,
      (wEK δF b nodes orbit chals pubs Q i).trace r = (wEK δF b nodes orbit chals pubs' Q' i).trace r := by
  have hch : ∀ i : Fin n, (wEK δF b nodes orbit chals pubs Q i).chal = (wEK δF b nodes orbit chals pubs' Q' i).chal :=
    fun i => funext fun j => (wEK_chal δF b hn nodes orbit chals pubs Q i j).trans
      (wEK_chal δF b hn nodes orbit chals pubs' Q' i j).symm
  have hbool : ∀ (i : Fin n) (w : ℕ), boolE (cv w) ∈ Cell.baseGates (F := F) →
      ((hqkEF b nodes orbit chals pubs Q i).trace w = 0 ∨ (hqkEF b nodes orbit chals pubs Q i).trace w = 1) := by
    intro i w hw
    have g := (cellW_rowLocal δF b hn nodes orbit chals pubs hsat i).1 _ hw
    simp only [CoeffExpr.eval, cv, boolE] at g
    exact bool_val g
  have hbool' : ∀ (i : Fin n) (w : ℕ), boolE (cv w) ∈ Cell.baseGates (F := F) →
      ((hqkEF b nodes orbit chals pubs' Q' i).trace w = 0 ∨ (hqkEF b nodes orbit chals pubs' Q' i).trace w = 1) := by
    intro i w hw
    have g := (cellW_rowLocal δF b hn nodes orbit chals pubs' hsat' i).1 _ hw
    simp only [CoeffExpr.eval, cv, boolE] at g
    exact bool_val g
  -- the inverse roles
  have hinv : ∀ (i : Fin n), ∀ r, ((18 ≤ r ∧ r < 26) ∨ (30 ≤ r ∧ r < 34)) →
      (wEK δF b nodes orbit chals pubs Q i).trace r = (wEK δF b nodes orbit chals pubs' Q' i).trace r := by
    intro i
    obtain ⟨-, q, hq4⟩ := cellW_rowLocal δF b hn nodes orbit chals pubs hsat i
    obtain ⟨-, q', hq4'⟩ := cellW_rowLocal δF b hn nodes orbit chals pubs' hsat' i
    obtain ⟨kP, kL, kR, kX, kX1⟩ := keys_cong δF (eF := hqkEF b nodes orbit chals pubs Q i)
      (eF' := hqkEF b nodes orbit chals pubs' Q' i) (h1 i) (h0 i)
    have dP := den_congr δF Cell.vKeyP (hch i) kP
    have dL := den_congr δF Cell.vKeyL (hch i) kL
    have dR := den_congr δF Cell.vKeyR (hch i) kR
    have dX := den_congr δF (Cell.xKeyS (0 : F)) (hch i) kX
    have dX1 := den_congr δF (Cell.xKeyS (1 : F)) (hch i) kX1
    have rP := prov_roles δF Cell.vProvInv _ (q _ (by simp [Cell.qEqs])) (q' _ (by simp [Cell.qEqs])) dP
    have rX := prov_roles δF Cell.xProvInv _ (q _ (by simp [Cell.qEqs])) (q' _ (by simp [Cell.qEqs])) dX
    have rX1 := prov_roles δF Cell.xProvInv1 _ (q _ (by simp [Cell.qEqs])) (q' _ (by simp [Cell.qEqs])) dX1
    have wL := h0 i Cell.wL (by decide)
    have wR := h0 i Cell.wR (by decide)
    have rL := cons_roles δF Cell.consLInv _ Cell.wL (hbool i _ (by simp [Cell.baseGates]))
      (hbool' i _ (by simp [Cell.baseGates])) wL (q _ (by simp [Cell.qEqs])) (q' _ (by simp [Cell.qEqs]))
      (q _ (by simp [Cell.qEqs])) (q' _ (by simp [Cell.qEqs])) dL
    have rR := cons_roles δF Cell.consRInv _ Cell.wR (hbool i _ (by simp [Cell.baseGates]))
      (hbool' i _ (by simp [Cell.baseGates])) wR (q _ (by simp [Cell.qEqs])) (q' _ (by simp [Cell.qEqs]))
      (q _ (by simp [Cell.qEqs])) (q' _ (by simp [Cell.qEqs])) dR
    -- the handle-export inverse
    have hkv := keyVec5_keyHK_congr (K := K) (h0 i)
    have dH : wDenQ δF b nodes orbit chals pubs Q i = wDenQ δF b nodes orbit chals pubs' Q' i := by
      rw [wDenQ_eq, wDenQ_eq, hkv]
    have gH := hq4 (QE.sub (QE.mul δF (QE.var CellHQ.invHQ) (HQ.denKeyQ δF keyHK)) QE.one) (by simp [gatesQ])
    have gH' := hq4' (QE.sub (QE.mul δF (QE.var CellHQ.invHQ) (HQ.denKeyQ δF keyHK)) QE.one) (by simp [gatesQ])
    have rH := prov_roles δF CellHQ.invHQ _ gH gH' dH
    intro r hr
    have e1 : Cell.vProvInv = 18 := rfl
    have e2 : Cell.consLInv = 20 := rfl
    have e3 : Cell.consRInv = 22 := rfl
    have e4 : Cell.xProvInv = 24 := rfl
    have e5 : Cell.xProvInv1 = 30 := rfl
    have e6 : CellHQ.invHQ = 32 := rfl
    rw [e1] at rP; rw [e2] at rL; rw [e3] at rR; rw [e4] at rX; rw [e5] at rX1; rw [e6] at rH
    rcases (by omega : r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 25 ∨ r = 30 ∨ r = 31 ∨
      r = 32 ∨ r = 33) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [rP.1, rP.2, rL.1, rL.2, rR.1, rR.2, rX.1, rX.2, rX1.1, rX1.2, rH.1, rH.2]
  have hvT : ∀ i : Fin n, (Cell.vTerm true : QE F).ev δF (wEK δF b nodes orbit chals pubs Q i)
      (hqkEF b nodes orbit chals pubs Q i) =
      (Cell.vTerm true : QE F).ev δF (wEK δF b nodes orbit chals pubs' Q' i) (hqkEF b nodes orbit chals pubs' Q' i) := by
    intro i
    simp only [Cell.vTerm, if_true, ev_sub, ev_scale, ev_var, CoeffExpr.eval, cv]
    simp only [h0 i Cell.mv (by decide), hinv i Cell.vProvInv (by decide), hinv i (Cell.vProvInv + 1) (by decide),
      hinv i Cell.consLInv (by decide), hinv i (Cell.consLInv + 1) (by decide),
      hinv i Cell.consRInv (by decide), hinv i (Cell.consRInv + 1) (by decide)]
  have hxT : ∀ i : Fin n, (Cell.xTerm true : QE F).ev δF (wEK δF b nodes orbit chals pubs Q i)
      (hqkEF b nodes orbit chals pubs Q i) =
      (Cell.xTerm true : QE F).ev δF (wEK δF b nodes orbit chals pubs' Q' i) (hqkEF b nodes orbit chals pubs' Q' i) := by
    intro i
    simp only [Cell.xTerm, if_true, ev_add, ev_scale, ev_var, CoeffExpr.eval, cv]
    simp only [h0 i Cell.mx (by decide), h0 i Cell.mx1 (by decide), hinv i Cell.xProvInv (by decide),
      hinv i (Cell.xProvInv + 1) (by decide), hinv i Cell.xProvInv1 (by decide),
      hinv i (Cell.xProvInv1 + 1) (by decide)]
  have hhT : ∀ i : Fin n, (QE.scale (cv CellH.mh) (QE.var CellHQ.invHQ) : QE F).ev δF
      (wEK δF b nodes orbit chals pubs Q i) (hqkEF b nodes orbit chals pubs Q i) =
      (QE.scale (cv CellH.mh) (QE.var CellHQ.invHQ) : QE F).ev δF (wEK δF b nodes orbit chals pubs' Q' i)
        (hqkEF b nodes orbit chals pubs' Q' i) := by
    intro i
    simp only [ev_scale, ev_var, CoeffExpr.eval, cv]
    simp only [h0 i CellH.mh (by decide), hinv i CellHQ.invHQ (by decide), hinv i (CellHQ.invHQ + 1) (by decide)]
  have accV := acc_rows_eq δF hn Cell.vAcc (Cell.vTerm true) (Cell.vTerm false)
    (fun i => wEK δF b nodes orbit chals pubs Q i) (fun i => wEK δF b nodes orbit chals pubs' Q' i)
    (fun i => hqkEF b nodes orbit chals pubs Q i) (fun i => hqkEF b nodes orbit chals pubs' Q' i)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs hbind hinj i).1)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs hbind hinj i).2)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs' hbind' hinj i).1)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs' hbind' hinj i).2)
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs hsat i).2.1 _ (by simp [Cell.qEqs]))
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs' hsat' i).2.1 _ (by simp [Cell.qEqs]))
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs hsat i).2.1 _ (by simp [Cell.qEqs]))
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs' hsat' i).2.1 _ (by simp [Cell.qEqs]))
    (fun i hi => by
      simp only [Cell.vTerm, Bool.false_eq_true, if_false, if_true, ev_sub, ev_scale, ev_next, ev_var,
        CoeffExpr.eval, nv, cv, wEK_next δF b hn nodes orbit chals pubs Q hadj i hi,
        wEF_next δF b hn nodes orbit chals pubs Q hadj i hi])
    (fun i hi => by
      simp only [Cell.vTerm, Bool.false_eq_true, if_false, if_true, ev_sub, ev_scale, ev_next, ev_var,
        CoeffExpr.eval, nv, cv, wEK_next δF b hn nodes orbit chals pubs' Q' hadj i hi,
        wEF_next δF b hn nodes orbit chals pubs' Q' hadj i hi])
    (fun i hi r => wEK_next δF b hn nodes orbit chals pubs Q hadj i hi r)
    (fun i hi r => wEK_next δF b hn nodes orbit chals pubs' Q' hadj i hi r) hvT
  have accX := acc_rows_eq δF hn Cell.xAcc (Cell.xTerm true) (Cell.xTerm false)
    (fun i => wEK δF b nodes orbit chals pubs Q i) (fun i => wEK δF b nodes orbit chals pubs' Q' i)
    (fun i => hqkEF b nodes orbit chals pubs Q i) (fun i => hqkEF b nodes orbit chals pubs' Q' i)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs hbind hinj i).1)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs hbind hinj i).2)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs' hbind' hinj i).1)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs' hbind' hinj i).2)
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs hsat i).2.1 _ (by simp [Cell.qEqs]))
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs' hsat' i).2.1 _ (by simp [Cell.qEqs]))
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs hsat i).2.1 _ (by simp [Cell.qEqs]))
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs' hsat' i).2.1 _ (by simp [Cell.qEqs]))
    (fun i hi => by
      simp only [Cell.xTerm, Bool.false_eq_true, if_false, if_true, ev_add, ev_scale, ev_next, ev_var,
        CoeffExpr.eval, nv, cv, wEK_next δF b hn nodes orbit chals pubs Q hadj i hi,
        wEF_next δF b hn nodes orbit chals pubs Q hadj i hi])
    (fun i hi => by
      simp only [Cell.xTerm, Bool.false_eq_true, if_false, if_true, ev_add, ev_scale, ev_next, ev_var,
        CoeffExpr.eval, nv, cv, wEK_next δF b hn nodes orbit chals pubs' Q' hadj i hi,
        wEF_next δF b hn nodes orbit chals pubs' Q' hadj i hi])
    (fun i hi r => wEK_next δF b hn nodes orbit chals pubs Q hadj i hi r)
    (fun i hi r => wEK_next δF b hn nodes orbit chals pubs' Q' hadj i hi r) hxT
  have accH := acc_rows_eq δF hn CellHQ.accHQ (QE.scale (cv CellH.mh) (QE.var CellHQ.invHQ))
    (QE.scale (nv CellH.mh) (QE.next CellHQ.invHQ))
    (fun i => wEK δF b nodes orbit chals pubs Q i) (fun i => wEK δF b nodes orbit chals pubs' Q' i)
    (fun i => hqkEF b nodes orbit chals pubs Q i) (fun i => hqkEF b nodes orbit chals pubs' Q' i)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs hbind hinj i).1)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs hbind hinj i).2)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs' hbind' hinj i).1)
    (fun i => (cellW_masks δF b hn nodes orbit chals pubs' hbind' hinj i).2)
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs hsat i).2.2 _ (by simp [gatesQ, CellHQ.gatesQ]))
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs' hsat' i).2.2 _ (by simp [gatesQ, CellHQ.gatesQ]))
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs hsat i).2.2 _ (by simp [gatesQ, CellHQ.gatesQ]))
    (fun i => (cellW_rowLocal δF b hn nodes orbit chals pubs' hsat' i).2.2 _ (by simp [gatesQ, CellHQ.gatesQ]))
    (fun i hi => by
      simp only [ev_scale, ev_next, ev_var, CoeffExpr.eval, nv, cv,
        wEK_next δF b hn nodes orbit chals pubs Q hadj i hi, wEF_next δF b hn nodes orbit chals pubs Q hadj i hi])
    (fun i hi => by
      simp only [ev_scale, ev_next, ev_var, CoeffExpr.eval, nv, cv,
        wEK_next δF b hn nodes orbit chals pubs' Q' hadj i hi, wEF_next δF b hn nodes orbit chals pubs' Q' hadj i hi])
    (fun i hi r => wEK_next δF b hn nodes orbit chals pubs Q hadj i hi r)
    (fun i hi r => wEK_next δF b hn nodes orbit chals pubs' Q' hadj i hi r) hhT
  intro i r hr
  by_cases a : r < 18
  · exact h1 i r a
  by_cases c : (18 ≤ r ∧ r < 26) ∨ (30 ≤ r ∧ r < 34)
  · exact hinv i r c
  rcases (by omega : r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 34 ∨ r = 35) with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [(accV i).1, (accV i).2, (accX i).1, (accX i).2, (accH i).1, (accH i).2]


/-- **The terminal publics.** With equal accumulator roles, the publics `0 .. 5` (the validity terminal at `0, 1`,
the export terminal at `2, 3`, the handle-export terminal at `4, 5`) are equal: the terminal gates `isL·(acc − pub)`
at the last row. -/
theorem cell_pubs_eq
    {Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]}
    {Q' : Fin (cellChipHQKW δF b hn nodes orbit chals pubs').rap.w → F[X]}
    (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hsat' : (cellChipHQKW δF b hn nodes orbit chals pubs').rap.Satisfies Q')
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hbind' : (cellChipHQKW δF b hn nodes orbit chals pubs').BindsPreprocessing Q')
    (hinj : Function.Injective nodes)
    (hr : ∀ (i : Fin n), ∀ r < 36,
      (wEK δF b nodes orbit chals pubs Q i).trace r = (wEK δF b nodes orbit chals pubs' Q' i).trace r) :
    ∀ j < 6, pubs j = pubs' j := by
  let ℓ : Fin n := ⟨n - 1, by omega⟩
  have hL : (hqkEF b nodes orbit chals pubs Q ℓ).trace Cell.isL = 1 := by
    rw [(cellW_masks δF b hn nodes orbit chals pubs hbind hinj ℓ).2]; simp [ℓ]
  have hL' : (hqkEF b nodes orbit chals pubs' Q' ℓ).trace Cell.isL = 1 := by
    rw [(cellW_masks δF b hn nodes orbit chals pubs' hbind' hinj ℓ).2]; simp [ℓ]
  have key : ∀ (accC pj : ℕ), accC + 1 < 36 →
      (QE.scale (cv Cell.isL) (QE.sub (QE.var accC) (QE.pub pj)) : QE F) ∈ Cell.qEqs δF ∨
        (QE.scale (cv Cell.isL) (QE.sub (QE.var accC) (QE.pub pj)) : QE F) ∈ gatesQ δF →
      pubs pj = pubs' pj ∧ pubs (pj + 1) = pubs' (pj + 1) := by
    intro accC pj hacc hm
    have g : (QE.scale (cv Cell.isL) (QE.sub (QE.var accC) (QE.pub pj)) : QE F).ev δF
        (wEK δF b nodes orbit chals pubs Q ℓ) (hqkEF b nodes orbit chals pubs Q ℓ) = 0 := by
      rcases hm with hm | hm
      · exact (cellW_rowLocal δF b hn nodes orbit chals pubs hsat ℓ).2.1 _ hm
      · exact (cellW_rowLocal δF b hn nodes orbit chals pubs hsat ℓ).2.2 _ hm
    have g' : (QE.scale (cv Cell.isL) (QE.sub (QE.var accC) (QE.pub pj)) : QE F).ev δF
        (wEK δF b nodes orbit chals pubs' Q' ℓ) (hqkEF b nodes orbit chals pubs' Q' ℓ) = 0 := by
      rcases hm with hm | hm
      · exact (cellW_rowLocal δF b hn nodes orbit chals pubs' hsat' ℓ).2.1 _ hm
      · exact (cellW_rowLocal δF b hn nodes orbit chals pubs' hsat' ℓ).2.2 _ hm
    obtain ⟨a1, a2⟩ := terminal_pub δF _ _ Cell.isL accC pj hL g
    obtain ⟨b1, b2⟩ := terminal_pub δF _ _ Cell.isL accC pj hL' g'
    rw [wEK_pub] at a1 a2 b1 b2
    exact ⟨a1.trans ((hr ℓ accC (by omega)).trans b1.symm),
      a2.trans ((hr ℓ (accC + 1) hacc).trans b2.symm)⟩
  have kV := key Cell.vAcc 0 (by decide) (Or.inl (cell_vterm_mem δF))
  have kX := key Cell.xAcc 2 (by decide) (Or.inl (cell_xterm_mem δF))
  have kH := key CellHQ.accHQ CellHQ.pubHQ (by decide) (Or.inr (by simp [gatesQ, CellHQ.gatesQ]))
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [kV.1, kV.2, kX.1, kX.2, kH.1, kH.2]

/-- **Every column.** Equal round-0 columns, equal round-1 and round-2 roles give equal base columns (`3` per
`𝕂`-role). -/
theorem cell_cols_eq_of_roles
    {Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]}
    {Q' : Fin (cellChipHQKW δF b hn nodes orbit chals pubs').rap.w → F[X]}
    (h0 : ∀ (i : Fin n) (j : ℕ), j < 134 →
      (hqkEF b nodes orbit chals pubs Q i).trace j = (hqkEF b nodes orbit chals pubs' Q' i).trace j)
    (hr : ∀ (i : Fin n), ∀ r < 36,
      (wEK δF b nodes orbit chals pubs Q i).trace r = (wEK δF b nodes orbit chals pubs' Q' i).trace r) :
    ∀ (i : Fin n) (j : ℕ), j < 242 →
      (hqkEF b nodes orbit chals pubs Q i).trace j = (hqkEF b nodes orbit chals pubs' Q' i).trace j := by
  intro i j hj
  by_cases h134 : j < 134
  · exact h0 i j h134
  have hk : (j - 134) % 3 < 3 := Nat.mod_lt _ (by omega)
  have := trace_cols_eq_of_gather b ((cellTemplateHQKW δF).col0 3)
    (hqkEF b nodes orbit chals pubs Q i) (hqkEF b nodes orbit chals pubs' Q' i) ((j - 134) / 3)
    (hr i ((j - 134) / 3) (by omega)) ⟨(j - 134) % 3, hk⟩
  simpa [ChipTemplate.col0, cellTemplateHQKW_baseCols, show 134 + 3 * ((j - 134) / 3) + (j - 134) % 3 = j by omega]
    using this

/-- **Rounds 1 and 2 of the cell table are determined by round 0** (and the coins), on every column at every row
node, and the publics `0 .. 5` are determined with them. Hypotheses: the chip is satisfied and binds its masks, the
two tables are `ValidityServed`, the seed is nonzero. -/
theorem cell_rows_eq (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    {Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → F[X]}
    {Q' : Fin (cellChipHQKW δF b hn nodes orbit chals pubs').rap.w → F[X]}
    (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hsat' : (cellChipHQKW δF b hn nodes orbit chals pubs').rap.Satisfies Q')
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hbind' : (cellChipHQKW δF b hn nodes orbit chals pubs').BindsPreprocessing Q')
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (hserved : ValidityServed (cellTableOf δF b nodes orbit chals pubs
      (restrictHQKWCell δF b hn nodes orbit chals pubs Q)))
    (hserved' : ValidityServed (cellTableOf δF b nodes orbit chals pubs'
      (restrictHQKWCell δF b hn nodes orbit chals pubs' Q')))
    (h0 : ∀ (i : Fin n) (j : ℕ) (hj : j < 134),
      (Q ⟨j, by rw [cellChipHQKW_width]; omega⟩).eval (nodes i) =
        (Q' ⟨j, by rw [cellChipHQKW_width]; omega⟩).eval (nodes i)) :
    (∀ (i : Fin n) (j : ℕ) (hj : j < 242),
      (Q ⟨j, by rw [cellChipHQKW_width]; exact hj⟩).eval (nodes i) =
        (Q' ⟨j, by rw [cellChipHQKW_width]; exact hj⟩).eval (nodes i)) ∧ ∀ j < 6, pubs j = pubs' j := by
  have h0' : ∀ (i : Fin n) (j : ℕ), j < 134 →
      (hqkEF b nodes orbit chals pubs Q i).trace j = (hqkEF b nodes orbit chals pubs' Q' i).trace j := by
    intro i j hj
    simp only [Reify.envOfTrace, dif_pos (show j < (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w by
      rw [cellChipHQKW_width]; omega), dif_pos (show j < (cellChipHQKW δF b hn nodes orbit chals pubs').rap.w by
      rw [cellChipHQKW_width]; omega)]
    exact h0 i j hj
  have r1 := cell_round1_eq δF b hn nodes orbit chals pubs pubs' hF hq hz hsat hsat' hbind hbind' hinj hadj hnp
    hserved hserved' h0'
  have r2 := cell_round2_eq δF b hn nodes orbit chals pubs pubs' hsat hsat' hbind hbind' hinj hadj h0' r1
  refine ⟨fun i j hj => ?_, cell_pubs_eq δF b hn nodes orbit chals pubs pubs' hsat hsat' hbind hbind' hinj r2⟩
  have := cell_cols_eq_of_roles δF b hn nodes orbit chals pubs pubs' h0' r2 i j hj
  simpa [Reify.envOfTrace, dif_pos (show j < (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w by
      rw [cellChipHQKW_width]; omega), dif_pos (show j < (cellChipHQKW δF b hn nodes orbit chals pubs').rap.w by
      rw [cellChipHQKW_width]; omega)] using this

end Round

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1.acc_rows_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1.cell_round1_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1.cell_round2_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1.cell_pubs_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1.cell_rows_eq
