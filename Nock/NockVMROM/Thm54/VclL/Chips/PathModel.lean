/-
  Nock/NockVMROM/Thm54/VclL/Chips/PathModel.lean

  * Abstract row model: `PathRow` (side / first / last / len / acc / rootIdx / cellIdx in `𝔽`,
    root / p / l / r in `FP 𝕂′`), the row-local gate consequences `PathLocal` and the step
    consequences `PathStep`; `chain_invariant` (induction along a chain: root, `len = k + 1`,
    `acc = axisFold sides`, `rootIdx = cellIdx` of the start, `chainEnd` links the edges);
    `chain_start` (every row lies in a chain: row `0` is `first`, a row after a `last` row is
    `first`); `chain_record` (V1's certificate at the record row pins `k + 1 ≤ 62` through
    `len_le_62_of_chip`, so `acc` is exactly the natural axis fold, `< 2^63 < p`).
  * The chip: `pathRowOf` / `pathRows` read the row model off a trace; `pathLocal_of_chip`,
    `pathStep_of_chip` (row adjacency `Checks.hadjM`, the `isLast` mask); the chip's `bitSum`
    is `len_le_62_of_chip`'s `Finset.range` sum (`eval_bitSum`, `RowModel.lean`);
    **`path_records_of_chip`**: every record row (`last = 1`) closes a chain with those facts.
  Premises (all verifier-side, none read the trace): adjacency, node injectivity, `n + 1 < p`
  (from `Checks.hcons`), `2^63 < p`, `PrimeFieldElems F`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.RowModel
import Nock.NockVMROM.Thm54.P8Core.VclL.Chain

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Chips.PathModel

open Nock.NockVMROM.Thm54.VclL
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

section Abstract
variable {F : Type} [Field F] {Kfp : Type} [Field Kfp] [DecidableEq Kfp]

/-- **Per-row path-chip data** (the row model of one path-chip row). -/
structure PathRow (F Kfp : Type) where
  side : F
  first : F
  last : F
  len : F
  acc : F
  rootIdx : F
  cellIdx : F
  root : FP Kfp
  p : FP Kfp
  l : FP Kfp
  r : FP Kfp

variable [DecidableEq F]

theorem chainEnd_append_single (cur : FP Kfp) (es : List (Edge Kfp)) (e : Edge Kfp) :
    chainEnd cur (es ++ [e]) =
      (chainEnd cur es).bind fun c => if e.p = c then some (childOf e) else none := by
  induction es generalizing cur with
  | nil => simp [chainEnd]
  | cons a t ih =>
    simp only [List.cons_append, chainEnd]
    split_ifs
    · exact ih _
    · rfl

/-- The side bit of a row. -/
def PathRow.sideB (x : PathRow F Kfp) : Bool := decide (x.side = 1)

/-- The edge a row consumes (`cellIdx` read later through `natOf`). -/
def PathRow.child (x : PathRow F Kfp) : FP Kfp := if x.sideB then x.r else x.l

/-- **The row-local path gates, as equations** (current row `x`, next row `y` when not last). -/
structure PathLocal (x : PathRow F Kfp) : Prop where
  side_bool : x.side = 0 ∨ x.side = 1
  first_bool : x.first = 0 ∨ x.first = 1
  last_bool : x.last = 0 ∨ x.last = 1
  len_first : x.first * (x.len - 1) = 0
  acc_first : x.first * (x.acc - 2 - x.side) = 0
  rootIdx_first : x.first * (x.rootIdx - x.cellIdx) = 0
  root_first : x.first = 1 → x.root = x.p

structure PathStep (x y : PathRow F Kfp) : Prop where
  first_next : x.last = 0 → y.first = 0
  first_after_last : x.last = 1 → y.first = 1
  len_step : x.last = 0 → y.len = x.len + 1
  acc_step : x.last = 0 → y.acc = 2 * x.acc + y.side
  rootIdx_step : x.last = 0 → y.rootIdx = x.rootIdx
  root_step : x.last = 0 → y.root = x.root
  p_step : x.last = 0 → y.p = x.child

/-- The side bits of rows `s.. s + k`. -/
def sides (rows : ℕ → PathRow F Kfp) (s k : ℕ) : List Bool :=
  (List.range (k + 1)).map fun j => (rows (s + j)).sideB

/-- The edges of rows `s.. s + k`. -/
def edges (rows : ℕ → PathRow F Kfp) (cidx : F → ℕ) (s k : ℕ) : List (Edge Kfp) :=
  (List.range (k + 1)).map fun j =>
    ⟨(rows (s + j)).p, (rows (s + j)).l, (rows (s + j)).r, (rows (s + j)).sideB,
      cidx (rows (s + j)).cellIdx⟩

theorem side_val (x : PathRow F Kfp) (h : x.side = 0 ∨ x.side = 1) :
    x.side = if x.sideB then 1 else 0 := by
  unfold PathRow.sideB
  rcases h with h | h <;> simp [h]

/-- **The chain invariant**: along a chain started at row `s` (a `first` row) and not yet ended
before row `s + k`, row `s + k` carries the chain's root, length `k + 1`, the axis fold of the
sides so far, the root's serial, and the edges `s.. s + k` link from `p s` to row `s + k`'s child. -/
theorem chain_invariant (rows : ℕ → PathRow F Kfp) (cidx : F → ℕ) (n s : ℕ)
    (hloc : ∀ i < n, PathLocal (rows i)) (hstep : ∀ i, i + 1 < n → PathStep (rows i) (rows (i + 1)))
    (hfirst : (rows s).first = 1) :
    ∀ k, s + k < n → (∀ j < k, (rows (s + j)).last = 0) →
      (rows (s + k)).root = (rows s).p ∧
      (rows (s + k)).len = ((k + 1 : ℕ) : F) ∧
      (rows (s + k)).acc = ((axisFold (sides rows s k) : ℕ) : F) ∧
      (rows (s + k)).rootIdx = (rows s).cellIdx ∧
      chainEnd (rows s).p (edges rows cidx s k) = some (rows (s + k)).child := by
  intro k
  induction k with
  | zero =>
    intro hsn _
    have hl := hloc s (by omega)
    refine ⟨hl.root_first hfirst, ?_, ?_, ?_, ?_⟩
    · have := hl.len_first; rw [hfirst, one_mul] at this; simpa using sub_eq_zero.mp this
    · have := hl.acc_first; rw [hfirst, one_mul] at this
      rw [sub_sub, sub_eq_zero] at this
      have h0 : sides rows s 0 = [] ++ [(rows s).sideB] := by simp [sides]
      rw [Nat.add_zero, this, h0, axisFold_append, side_val _ hl.side_bool]
      simp only [axisFold, List.foldl_nil]
      split_ifs <;> push_cast <;> (try ring)
    · have := hl.rootIdx_first; rw [hfirst, one_mul] at this; simpa using sub_eq_zero.mp this
    · simp [edges, chainEnd]; rfl
  | succ k ih =>
    intro hsn hlast
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (by omega) (fun j hj => hlast j (by omega))
    have hk : (rows (s + k)).last = 0 := hlast k (by omega)
    have hs := hstep (s + k) (by omega)
    have e : s + (k + 1) = s + k + 1 := by omega
    rw [e]
    refine ⟨by rw [hs.root_step hk, h1], by rw [hs.len_step hk, h2]; push_cast; ring, ?_,
      by rw [hs.rootIdx_step hk, h4], ?_⟩
    · rw [hs.acc_step hk, h3]
      have hsd := side_val _ (hloc (s + k + 1) (by omega)).side_bool
      have : sides rows s (k + 1) = sides rows s k ++ [(rows (s + k + 1)).sideB] := by
        simp only [sides, List.range_succ, List.map_append, List.map_cons, List.map_nil]
        rw [e]
      rw [this, axisFold_append, hsd]
      split_ifs <;> push_cast <;> (try ring)
    · have hed : edges rows cidx s (k + 1) = edges rows cidx s k ++
          [⟨(rows (s + k + 1)).p, (rows (s + k + 1)).l, (rows (s + k + 1)).r,
            (rows (s + k + 1)).sideB, cidx (rows (s + k + 1)).cellIdx⟩] := by
        simp only [edges, List.range_succ, List.map_append, List.map_cons, List.map_nil]
        rw [e]
      rw [hed, chainEnd_append_single, h5, Option.bind_some, ← hs.p_step hk, if_pos rfl]
      rfl

theorem sides_length (rows : ℕ → PathRow F Kfp) (s k : ℕ) : (sides rows s k).length = k + 1 := by
  simp [sides]

/-- **The path record of a chain** (rows `s.. s + k`, `first` at `s`, `last` first reached at
`s + k`): the length certificate pins `k + 1 ≤ 62` (V1's `certBits`, `len_le_62_of_chip`, given
`k + 2 < p`); then `acc` is exactly the natural axis fold (`< 2^63 < p`), the record's root is the
first row's parent, its serial the first row's `cellIdx`, and the edges link to the record's child. -/
theorem chain_record (hF : GeneratedField.PrimeFieldElems F) (hp63 : 2 ^ 63 < ringChar F)
    (rows : ℕ → PathRow F Kfp) (cidx : F → ℕ) (n s k : ℕ)
    (hloc : ∀ i < n, PathLocal (rows i)) (hstep : ∀ i, i + 1 < n → PathStep (rows i) (rows (i + 1)))
    (hfirst : (rows s).first = 1) (hsk : s + k < n) (hnolast : ∀ j < k, (rows (s + j)).last = 0)
    (bits : ℕ → F) (hb : ∀ i < 6, bits i * (bits i - 1) = 0)
    (hcert : (rows (s + k)).len + ∑ i ∈ Finset.range 6, (2 : F) ^ i * bits i - 62 = 0)
    (hkp : k + 2 < ringChar F) :
    k + 1 ≤ 62 ∧
      Chips.ChipRAP.natOf (rows (s + k)).acc = axisFold (sides rows s k) ∧
      (rows (s + k)).root = (rows s).p ∧
      (rows (s + k)).rootIdx = (rows s).cellIdx ∧
      chainEnd (rows s).p (edges rows cidx s k) = some (rows (s + k)).child := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := chain_invariant rows cidx n s hloc hstep hfirst k hsk hnolast
  have hk : k + 1 ≤ 62 := by
    rw [h2] at hcert
    exact CertBound.len_le_62_of_chip (p := ringChar F) bits hb (by omega) hcert
  refine ⟨hk, ?_, h1, h4, h5⟩
  rw [h3]
  apply Chips.ChipRAP.natOf_natCast hF
  have := axisFold_lt (sides rows s k)
  rw [sides_length] at this
  have h2k : 2 ^ (k + 1 + 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Every row lies in a chain**: from row `e` back to the nearest `first` row `s`, no row in
`[s, e)` is `last` (row `0` is `first`; a row after a `last` row is `first`). -/
theorem chain_start (rows : ℕ → PathRow F Kfp) (n : ℕ)
    (hloc : ∀ i < n, PathLocal (rows i)) (hstep : ∀ i, i + 1 < n → PathStep (rows i) (rows (i + 1)))
    (h0 : (rows 0).first = 1) :
    ∀ e < n, ∃ s k, e = s + k ∧ (rows s).first = 1 ∧ ∀ j < k, (rows (s + j)).last = 0 := by
  intro e
  induction e with
  | zero => intro _; exact ⟨0, 0, rfl, h0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ e ih =>
    intro hen
    rcases (hloc (e + 1) hen).first_bool with hf | hf
    · obtain ⟨s, k, rfl, hs, hk⟩ := ih (by omega)
      have hl : (rows (s + k)).last = 0 := by
        rcases (hloc (s + k) (by omega)).last_bool with h | h
        · exact h
        · have := (hstep (s + k) hen).first_after_last h; rw [hf] at this; exact absurd this zero_ne_one
      refine ⟨s, k + 1, by omega, hs, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hk j hj
      · exact hl
    · exact ⟨e + 1, 0, rfl, hf, fun j hj => absurd hj (Nat.not_lt_zero _)⟩

end Abstract

/-! ## The path chip's rows -/

section Chip
noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- The row model of one path-chip row at its two environments. -/
def pathRowOf (eK : Env K) (eF : Env F) : PathRow F (Quad (algebraMap F K δF)) where
  side := eF.trace Path.side
  first := eF.trace Path.first
  last := eF.trace Path.last
  len := eF.trace Path.len
  acc := eF.trace Path.acc
  rootIdx := eF.trace Path.rootIdx
  cellIdx := eF.trace Path.cellIdx
  root := (QFP.var Path.rootR).ev δF eK eF
  p := (QFP.var Path.pR).ev δF eK eF
  l := (QFP.var Path.lR).ev δF eK eF
  r := (QFP.var Path.rR).ev δF eK eF

/-- Row `i`'s base environment on the path chip (rows past `n` read row `0`; never used). -/
def pathEnvF {w : ℕ} (Q : Fin w → F[X]) (i : ℕ) : Env F :=
  Reify.envOfTrace Q orbit.ω (if hi : i < n then nodes ⟨i, hi⟩ else nodes ⟨0, hn⟩)
    (slotVal b 16 chals) (slotVal b 16 pubs)

def pathEnvK {w : ℕ} (Q : Fin w → F[X]) (i : ℕ) : Env K :=
  gatherEnv b ((pathTemplate δF).col0 3) (pathEnvF b hn nodes orbit chals pubs Q i)

/-- The path table read off a trace, as a row function. -/
def pathRows {w : ℕ} (Q : Fin w → F[X]) (i : ℕ) : PathRow F (Quad (algebraMap F K δF)) :=
  pathRowOf δF (pathEnvK δF b hn nodes orbit chals pubs Q i) (pathEnvF b hn nodes orbit chals pubs Q i)

/-- A `QFP` whose three entries' `𝕂′` values are `0` is the zero fingerprint, entrywise. -/
theorem qfp_entries_zero (x : QFP F) (eK : Env K) (eF : Env F)
    (h : ∀ e ∈ x.entries, e.ev δF eK eF = 0) :
    x.size.ev δF eK eF = 0 ∧ x.dyck.ev δF eK eF = 0 ∧ x.leaf.ev δF eK eF = 0 :=
  ⟨h _ (by simp [QFP.entries]), h _ (by simp [QFP.entries]), h _ (by simp [QFP.entries])⟩

/-- The chip's child expression `l + side·(r − l)` at a boolean side is `PathRow.child`. -/
theorem child_ev (eK : Env K) (eF : Env F) (hs : eF.trace Path.side = 0 ∨ eF.trace Path.side = 1) :
    (Path.child (F := F)).ev δF eK eF = (pathRowOf δF eK eF).child := by
  unfold PathRow.child PathRow.sideB
  rcases hs with h0 | h1
  · have : ¬ (pathRowOf δF eK eF).side = 1 := by
      show ¬ eF.trace Path.side = 1; rw [h0]; exact zero_ne_one
    rw [if_neg (by simpa using this)]
    simp only [Path.child, QFP.ev, QFP.add, QFP.scale, QFP.sub, ev_add, ev_scale, ev_sub, CoeffExpr.eval,
      cv, h0, liftQ, map_zero, zero_mul, add_zero]
    rfl
  · have : (pathRowOf δF eK eF).side = 1 := h1
    rw [if_pos (by simpa using this)]
    simp only [Path.child, QFP.ev, QFP.add, QFP.scale, QFP.sub, ev_add, ev_scale, ev_sub, CoeffExpr.eval,
      cv, h1, liftQ, map_one, one_mul, add_sub_cancel]
    rfl

theorem pathEnvF_eq {w : ℕ} (Q : Fin w → F[X]) (i : ℕ) (hi : i < n) :
    pathEnvF b hn nodes orbit chals pubs Q i =
      Reify.envOfTrace Q orbit.ω (nodes ⟨i, hi⟩) (slotVal b 16 chals) (slotVal b 16 pubs) := by
  simp [pathEnvF, hi]

theorem memA (e : QE F)
    (he : e ∈ (QFP.scale (cv Path.first) (QFP.sub (QFP.var Path.rootR) (QFP.var Path.pR))).entries) :
    e ∈ Path.qEqs δF := by
  unfold Path.qEqs; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he))

theorem memB (e : QE F)
    (he : e ∈ (QFP.scale (notE (cv Path.last))
      (QFP.sub (QFP.next Path.rootR) (QFP.var Path.rootR))).entries) :
    e ∈ Path.qEqs δF := by
  unfold Path.qEqs; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ he))

theorem memC (e : QE F)
    (he : e ∈ (QFP.scale (notE (cv Path.last)) (QFP.sub (QFP.next Path.pR) Path.child)).entries) :
    e ∈ Path.qEqs δF := by
  unfold Path.qEqs; exact List.mem_append_left _ (List.mem_append_right _ he)

/-- A `QFP` equation `g·(x − y)` with `g = 1` gives `x = y`. -/
theorem fp_of_scaled (g : CoeffExpr F) (x y : QFP F) (eK : Env K) (eF : Env F) (hg : g.eval eF = 1)
    (h : ∀ e ∈ (QFP.scale g (QFP.sub x y)).entries, e.ev δF eK eF = 0) :
    x.ev δF eK eF = y.ev δF eK eF := by
  obtain ⟨h1, h2, h3⟩ := qfp_entries_zero δF _ eK eF h
  simp only [QFP.scale, QFP.sub, ev_scale, ev_sub, hg, liftQ, map_one, one_mul] at h1 h2 h3
  simp only [QFP.ev]
  rw [sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3]

theorem bool_of_gate (eF : Env F) (j : ℕ) (hj : (boolE (cv j) : CoeffExpr F) ∈ Path.baseGates)
    (hb : ∀ g ∈ Path.baseGates (F := F), g.eval eF = 0) : eF.trace j = 0 ∨ eF.trace j = 1 :=
  bool_val (by simpa [CoeffExpr.eval, cv, boolE] using hb _ hj)

variable (Q : Fin (pathChip δF b hn nodes orbit chals pubs).rap.w → F[X])
  (hsat : (pathChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
include hsat

/-- Row `i`'s gates on the path chip, in the row environments. -/
theorem path_gates (i : ℕ) (hi : i < n) :
    (∀ g ∈ Path.baseGates (F := F), g.eval (pathEnvF b hn nodes orbit chals pubs Q i) = 0) ∧
      (∀ e ∈ Path.qEqs δF, e.ev δF (pathEnvK δF b hn nodes orbit chals pubs Q i)
        (pathEnvF b hn nodes orbit chals pubs Q i) = 0) := by
  have hl := pathChip_rowLocal δF b hn nodes orbit chals pubs Q hsat ⟨i, hi⟩
  unfold pathEnvK
  rw [pathEnvF_eq b hn nodes orbit chals pubs Q i hi]
  exact ⟨hl.1, fun e he => ev_eq_zero_of_gates δF _ _ e fun g hg =>
    hl.2 g (List.mem_flatMap.mpr ⟨e, he, hg⟩)⟩

/-- **`PathLocal` at every row** of an accepted path chip. -/
theorem pathLocal_of_chip (i : ℕ) (hi : i < n) :
    PathLocal (pathRows δF b hn nodes orbit chals pubs Q i) := by
  obtain ⟨hb, hm⟩ := path_gates δF b hn nodes orbit chals pubs Q hsat i hi
  refine ⟨bool_of_gate _ Path.side (by simp [Path.baseGates]) hb,
    bool_of_gate _ Path.first (by simp [Path.baseGates]) hb,
    bool_of_gate _ Path.last (by simp [Path.baseGates]) hb, ?_, ?_, ?_, ?_⟩
  · exact hb (.mul (cv Path.first) (.sub (cv Path.len) (.const 1)))
      (by simp [Path.baseGates])
  · exact hb (.mul (cv Path.first) (.sub (.sub (cv Path.acc) (.const 2))
      (cv Path.side))) (by simp [Path.baseGates])
  · exact hb (.mul (cv Path.first) (.sub (cv Path.rootIdx) (cv Path.cellIdx)))
      (by simp [Path.baseGates])
  · intro h1
    exact fp_of_scaled δF (cv Path.first) _ _ _ _ h1 fun e he => hm e (memA δF e he)

variable (hbind : (pathChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
  (hinj : Function.Injective nodes)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
include hbind hinj hadj

omit hsat hbind hinj in
theorem path_traceNext (i : ℕ) (hi : i + 1 < n) (j : ℕ) :
    (pathEnvF b hn nodes orbit chals pubs Q i).traceNext j =
      (pathEnvF b hn nodes orbit chals pubs Q (i + 1)).trace j := by
  rw [pathEnvF_eq b hn nodes orbit chals pubs Q i (by omega),
    pathEnvF_eq b hn nodes orbit chals pubs Q (i + 1) hi]
  exact traceNext_eq nodes orbit Q _ _ hadj ⟨i, by omega⟩ hi j

omit hsat hbind hinj in
theorem path_ev_next (i : ℕ) (hi : i + 1 < n) (r : ℕ) :
    (QE.next r : QE F).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q i)
        (pathEnvF b hn nodes orbit chals pubs Q i) =
      (QE.var r : QE F).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q (i + 1))
        (pathEnvF b hn nodes orbit chals pubs Q (i + 1)) := by
  simp only [ev_next, ev_var, pathEnvK, gatherEnv, ChipTemplate.col0,
    path_traceNext δF b hn nodes orbit chals pubs Q hadj i hi]

omit hsat hbind hinj in
theorem path_qfp_next (i : ℕ) (hi : i + 1 < n) (r : ℕ) :
    (QFP.next r : QFP F).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q i)
        (pathEnvF b hn nodes orbit chals pubs Q i) =
      (QFP.var r : QFP F).ev δF (pathEnvK δF b hn nodes orbit chals pubs Q (i + 1))
        (pathEnvF b hn nodes orbit chals pubs Q (i + 1)) := by
  simp only [QFP.ev, QFP.next, QFP.var, path_ev_next δF b hn nodes orbit chals pubs Q hadj i hi]

/-- **`PathStep` between consecutive rows** of an accepted path chip (row adjacency, the
`isLast` mask is `0` before the last row). -/
theorem pathStep_of_chip (i : ℕ) (hi : i + 1 < n) :
    PathStep (pathRows δF b hn nodes orbit chals pubs Q i)
      (pathRows δF b hn nodes orbit chals pubs Q (i + 1)) := by
  obtain ⟨hb, hm⟩ := path_gates δF b hn nodes orbit chals pubs Q hsat i (by omega)
  have hw : (pathChip δF b hn nodes orbit chals pubs).rap.w = 112 :=
    (pathChip_fingerprint δF b hn nodes orbit chals pubs).1
  have hisL : (pathEnvF b hn nodes orbit chals pubs Q i).trace Path.isL = 0 := by
    rw [pathEnvF_eq b hn nodes orbit chals pubs Q i (by omega), show Path.isL = 1 from rfl,
      envOfTrace_trace Q _ _ _ _ (show 1 < _ by rw [hw]; omega),
      (pathChip_masks δF b hn nodes orbit chals pubs Q hbind hinj ⟨i, by omega⟩).2]
    rw [if_neg]
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hnx := path_traceNext δF b hn nodes orbit chals pubs Q hadj i hi
  have g1 := hb (.mul (notE (cv Path.isL)) (.sub (nv Path.first) (cv Path.last))) (by simp [Path.baseGates])
  have g2 := hb (.mul (notE (cv Path.last)) (.sub (.sub (nv Path.len) (cv Path.len)) (.const 1)))
    (by simp [Path.baseGates])
  have g3 := hb (.mul (notE (cv Path.last)) (.sub (.sub (nv Path.acc) (.mul (.const 2) (cv Path.acc)))
    (nv Path.side))) (by simp [Path.baseGates])
  have g4 := hb (.mul (notE (cv Path.last)) (.sub (nv Path.rootIdx) (cv Path.rootIdx)))
    (by simp [Path.baseGates])
  simp only [CoeffExpr.eval, cv, nv, notE, hisL, hnx, sub_zero, one_mul] at g1 g2 g3 g4
  have hsd := bool_of_gate _ Path.side (by simp [Path.baseGates]) hb
  set x := pathEnvF b hn nodes orbit chals pubs Q i with hx
  set y := pathEnvF b hn nodes orbit chals pubs Q (i + 1) with hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; change y.trace Path.first = 0; rw [sub_eq_zero.mp g1]; exact h
  · intro h; change y.trace Path.first = 1; rw [sub_eq_zero.mp g1]; exact h
  · intro h; change x.trace Path.last = 0 at h
    rw [h, sub_zero, one_mul] at g2; change y.trace Path.len = x.trace Path.len + 1
    linear_combination g2
  · intro h; change x.trace Path.last = 0 at h
    rw [h, sub_zero, one_mul] at g3; change y.trace Path.acc = 2 * x.trace Path.acc + y.trace Path.side
    linear_combination g3
  · intro h; change x.trace Path.last = 0 at h
    rw [h, sub_zero, one_mul] at g4; change y.trace Path.rootIdx = x.trace Path.rootIdx
    linear_combination g4
  · intro h
    have := fp_of_scaled δF (notE (cv Path.last)) _ _ _ _ (by simp [CoeffExpr.eval, cv, notE]; exact h)
      fun e he => hm e (memB δF e he)
    rw [path_qfp_next δF b hn nodes orbit chals pubs Q hadj i hi] at this
    exact this
  · intro h
    have := fp_of_scaled δF (notE (cv Path.last)) _ _ _ _ (by simp [CoeffExpr.eval, cv, notE]; exact h)
      fun e he => hm e (memC δF e he)
    rw [path_qfp_next δF b hn nodes orbit chals pubs Q hadj i hi, child_ev δF _ _ hsd] at this
    exact this

/-- **Step (2): every record row of an accepted path chip closes a chain** — for a row `e` with
`last = 1` there is a chain start `s` (`e = s + k`) such that `k + 1 ≤ 62` (V1's certificate), the
row's `acc` is exactly the natural axis fold of the chain's sides, its `root` is the start row's
parent `p`, its `rootIdx` the start row's `cellIdx`, and the chain's edges link `p s` to the row's
child.  Premises: adjacency and node injectivity (`Checks.hadjM`, `memNodes_injective`), `n + 1 < p`
(from `Checks.hcons`), `2^63 < p`, `PrimeFieldElems F`. -/
theorem path_records_of_chip (hF : GeneratedField.PrimeFieldElems F) (hp63 : 2 ^ 63 < ringChar F)
    (hnp : n + 1 < ringChar F) (cidx : F → ℕ) (e : ℕ) (he : e < n)
    (hlast : (pathRows δF b hn nodes orbit chals pubs Q e).last = 1) :
    ∃ s k, e = s + k ∧ k + 1 ≤ 62 ∧
      natOf (pathRows δF b hn nodes orbit chals pubs Q e).acc =
        axisFold (sides (pathRows δF b hn nodes orbit chals pubs Q) s k) ∧
      (pathRows δF b hn nodes orbit chals pubs Q e).root = (pathRows δF b hn nodes orbit chals pubs Q s).p ∧
      (pathRows δF b hn nodes orbit chals pubs Q e).rootIdx =
        (pathRows δF b hn nodes orbit chals pubs Q s).cellIdx ∧
      chainEnd (pathRows δF b hn nodes orbit chals pubs Q s).p
        (edges (pathRows δF b hn nodes orbit chals pubs Q) cidx s k) =
        some (pathRows δF b hn nodes orbit chals pubs Q e).child := by
  set rows := pathRows δF b hn nodes orbit chals pubs Q with hrows
  have hloc : ∀ i < n, PathLocal (rows i) := fun i hi =>
    pathLocal_of_chip δF b hn nodes orbit chals pubs Q hsat i hi
  have hstep : ∀ i, i + 1 < n → PathStep (rows i) (rows (i + 1)) := fun i hi =>
    pathStep_of_chip δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj i hi
  have hw : (pathChip δF b hn nodes orbit chals pubs).rap.w = 112 :=
    (pathChip_fingerprint δF b hn nodes orbit chals pubs).1
  have h0 : (rows 0).first = 1 := by
    obtain ⟨hb, -⟩ := path_gates δF b hn nodes orbit chals pubs Q hsat 0 hn
    have g := hb (.mul (cv Path.isF) (.sub (cv Path.first) (.const 1))) (by simp [Path.baseGates])
    have hisF : (pathEnvF b hn nodes orbit chals pubs Q 0).trace Path.isF = 1 := by
      rw [pathEnvF_eq b hn nodes orbit chals pubs Q 0 hn, show Path.isF = 0 from rfl,
        envOfTrace_trace Q _ _ _ _ (show 0 < _ by rw [hw]; omega),
        (pathChip_masks δF b hn nodes orbit chals pubs Q hbind hinj ⟨0, hn⟩).1]
      simp
    simp only [CoeffExpr.eval, hisF, one_mul] at g
    exact sub_eq_zero.mp g
  obtain ⟨s, k, rfl, hs, hk⟩ := chain_start rows n hloc hstep h0 e he
  -- the certificate at the record row
  obtain ⟨hb, -⟩ := path_gates δF b hn nodes orbit chals pubs Q hsat (s + k) he
  have gc := hb (.mul (cv Path.last) (.sub (.add (cv Path.len) (bitSum Path.bit0 6)) (.const 62)))
    (by simp [Path.baseGates])
  have hl1 : (pathEnvF b hn nodes orbit chals pubs Q (s + k)).trace Path.last = 1 := hlast
  simp only [CoeffExpr.eval, hl1, one_mul, eval_bitSum] at gc
  have hbits : ∀ i < 6, (pathEnvF b hn nodes orbit chals pubs Q (s + k)).trace (Path.bit0 + i) *
      ((pathEnvF b hn nodes orbit chals pubs Q (s + k)).trace (Path.bit0 + i) - 1) = 0 := by
    intro i hi
    have := hb (boolE (cv (Path.bit0 + i)))
      (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    simpa [CoeffExpr.eval, cv, boolE] using this
  obtain ⟨hk62, hacc, hroot, hidx, hend⟩ := chain_record hF hp63 rows cidx n s k hloc hstep hs he hk
    (fun i => (pathEnvF b hn nodes orbit chals pubs Q (s + k)).trace (Path.bit0 + i)) hbits
    gc (by omega)
  exact ⟨s, k, rfl, hk62, hacc, hroot, hidx, hend⟩

end
end Chip


end Nock.NockVMROM.Thm54.VclL.Chips.PathModel
