/-
  Nock/NockVMROM/Thm54/VclL/Chips/RowModel.lean

  The row model of a cell-table row is read off the row's two environments (base `eF`, gathered
  `𝕂` `eK`): every base column through `natOf` (the natural `< p` a `PrimeFieldElems` field element
  names), the boolean weights as `Bool`, the three fingerprints `p l r` as `𝕂′` values
  (`QFP.ev`, `QEval.lean`).  Then (`cellRow_gates`):
  * cons — the `z`-cleared `𝕂′` cons gates and `z ≠ 0` give `p = FP.cons z l r`;
  * the rank limbs — the bit decompositions spell `lo < 2^62`, `hi < 2^48` (`bits_sum_nat`,
    `2^63 < p`); the two limb gates read in `ZMod p` (`CharP.natCast_eq_natCast`); carry boolean;
  * the atom gates — a zero-weight child is `atomFP z (aX)` with limbs `0`.
  **What the gates do NOT give per row: the child limbs' ranges `loL hiL loR hiR < 2^62 / 2^48`**
  (no range gate on them, by design: the validity key `(fp, lo + hi√δ, idx)` carries them to a
  providing row, whose own bits range them).  So `RowOK` follows from the per-row gates AND
  `ValidityServed` (`rowOK_of_gates`), not from the gates alone.  `cellTable_accepts`: the chip, adjacency, node injectivity, `n < p` ⇒ `SerialOK` and every
  `RowOK`, i.e. `Table.TableAccepts` given `ValidityServed` (step (3) discharges that).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.QEval
import Nock.NockVMROM.Thm54.VclL.Chips.CertBound
import Nock.NockVMROM.Thm54.P8Core.VclL.Table
import Nock.NockVMROM.Thm54.GeneratedField

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
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Base-field values as naturals -/

section Nat
variable {F : Type} [Field F]

/-- The natural `< p` naming a field element (`0` if none; `PrimeFieldElems` says one exists). -/
def natOf (x : F) : ℕ :=
  open Classical in if h : ∃ n : ℕ, n < ringChar F ∧ (n : F) = x then Classical.choose h else 0

theorem natOf_spec (hF : GeneratedField.PrimeFieldElems F) (x : F) :
    natOf x < ringChar F ∧ (natOf x : F) = x := by
  have h := hF x
  unfold natOf
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem natOf_cast (hF : GeneratedField.PrimeFieldElems F) (x : F) : (natOf x : F) = x :=
  (natOf_spec hF x).2

theorem natOf_lt (hF : GeneratedField.PrimeFieldElems F) (x : F) : natOf x < ringChar F :=
  (natOf_spec hF x).1

/-- Naturals below `p` are cast injectively. -/
theorem natCast_inj_lt {a c : ℕ} (ha : a < ringChar F) (hc : c < ringChar F)
    (h : (a : F) = (c : F)) : a = c := by
  rw [CharP.natCast_eq_natCast F (ringChar F)] at h
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at h

theorem natOf_natCast (hF : GeneratedField.PrimeFieldElems F) {k : ℕ} (hk : k < ringChar F) :
    natOf (k : F) = k :=
  natCast_inj_lt (natOf_lt hF _) hk (natOf_cast hF _)

theorem natOf_zero (hF : GeneratedField.PrimeFieldElems F) (hp : 0 < ringChar F) :
    natOf (0 : F) = 0 := by
  simpa using natOf_natCast hF (k := 0) hp

theorem natOf_inj (hF : GeneratedField.PrimeFieldElems F) {x y : F} (h : natOf x = natOf y) :
    x = y := by
  rw [← natOf_cast hF x, ← natOf_cast hF y, h]

/-- A field equation between naturals is a `ZMod p` equation. -/
theorem zmod_of_field {a c : ℕ} (h : (a : F) = (c : F)) : (a : ZMod (ringChar F)) = (c : ZMod (ringChar F)) := by
  rw [CharP.natCast_eq_natCast F (ringChar F)] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

/-- A boolean field value is `0` or `1`. -/
theorem bool_val {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := CertBound.bool_cases h

/-- `List.range` sums are `Finset.range` sums. -/
theorem list_range_sum {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- **The chip's `bitSum` is the certificate sum** (`len_le_62_of_chip`'s `Finset.range` form). -/
theorem eval_bitSum (base m : ℕ) (env : Env F) :
    (bitSum (F := F) base m).eval env = ∑ i ∈ Finset.range m, (2 : F) ^ i * env.trace (base + i) := by
  rw [bitSum, CoeffExpr.eval_sumList, list_range_sum]
  rfl

/-- Boolean bits under a field-valued `bitSum` name a natural below `2^m` (and below `p`). -/
theorem bitSum_nat (hF : GeneratedField.PrimeFieldElems F) (base m : ℕ) (env : Env F)
    (hb : ∀ i < m, env.trace (base + i) * (env.trace (base + i) - 1) = 0)
    (hm : 2 ^ m ≤ ringChar F) :
    natOf ((bitSum (F := F) base m).eval env) < 2 ^ m := by
  obtain ⟨s, hs, hsum⟩ := CertBound.bits_sum_nat (fun i => env.trace (base + i)) m hb
  rw [eval_bitSum, ← hsum, natOf_natCast hF (by omega)]
  exact hs

end Nat

/-! ## 2. The row model of one cell-table row -/

section Row
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] (δF : F)

/-- The round-0 part of a cell row, read from the base environment. -/
def cellB0Of (eF : Env F) : CellRowB0 (ringChar F) where
  idx := natOf (eF.trace Cell.idx)
  idL := natOf (eF.trace Cell.idL)
  idR := natOf (eF.trace Cell.idR)
  wL := decide (eF.trace Cell.wL = 1)
  wR := decide (eF.trace Cell.wR = 1)
  aL := (natOf (eF.trace Cell.aL) : ZMod (ringChar F))
  aR := (natOf (eF.trace Cell.aR) : ZMod (ringChar F))
  lo := natOf (eF.trace Cell.lo)
  hi := natOf (eF.trace Cell.hi)
  loL := natOf (eF.trace Cell.loL)
  hiL := natOf (eF.trace Cell.hiL)
  loR := natOf (eF.trace Cell.loR)
  hiR := natOf (eF.trace Cell.hiR)
  carry := natOf (eF.trace Cell.carry)
  mv := natOf (eF.trace Cell.mv)
  mx := natOf (eF.trace Cell.mx)

/-- **The cell row** at the two environments: B0 through `natOf`, fingerprints as `𝕂′` values. -/
def cellRowOf (eK : Env K) (eF : Env F) : CellRow (ringChar F) (Quad (algebraMap F K δF)) :=
  ⟨cellB0Of eF, (QFP.var Cell.pR).ev δF eK eF, (QFP.var Cell.lR).ev δF eK eF,
    (QFP.var Cell.rR).ev δF eK eF⟩

/-- The seed `z′` at an environment. -/
abbrev zOf (eK : Env K) (eF : Env F) : Quad (algebraMap F K δF) := (zQ : QE F).ev δF eK eF

/-- **The row predicate minus the child-limb ranges** (what one row's gates give). -/
structure RowGates {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp] (z : Kfp)
    (c : CellRow q Kfp) : Prop where
  cons : c.p = FP.cons z c.l c.r
  lo_lt : c.b0.lo < 2 ^ 62
  hi_lt : c.b0.hi < 2 ^ 48
  carry_le : c.b0.carry ≤ 1
  limbLo : ((c.b0.lo : ZMod q) + (c.b0.carry : ZMod q) * 2 ^ 62 =
      (c.b0.loL : ZMod q) + (c.b0.loR : ZMod q) + 1)
  limbHi : ((c.b0.hi : ZMod q) = (c.b0.hiL : ZMod q) + (c.b0.hiR : ZMod q) + (c.b0.carry : ZMod q))
  atomL : c.b0.wL = false →
    c.l = FP.atomFP z (algebraMap (ZMod q) Kfp c.b0.aL) ∧ c.b0.loL = 0 ∧ c.b0.hiL = 0
  atomR : c.b0.wR = false →
    c.r = FP.atomFP z (algebraMap (ZMod q) Kfp c.b0.aR) ∧ c.b0.loR = 0 ∧ c.b0.hiR = 0

variable [Fact (¬ IsSquare (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))]

/-- `algebraMap (ZMod p) 𝕂′` of a `natOf` value is the lift of the field element. -/
theorem algebraMap_natOf (hF : GeneratedField.PrimeFieldElems F) (x : F) :
    algebraMap (ZMod (ringChar F)) (Quad (algebraMap F K δF)) (natOf x : ZMod (ringChar F)) =
      liftQ δF x := by
  rw [map_natCast, liftQ, ← map_natCast (algebraMap K _), ← map_natCast (algebraMap F K),
    natOf_cast hF]

/-- One atom side: a zero-weight child is `atomFP z a` with zero limbs. -/
theorem atom_side (hF : GeneratedField.PrimeFieldElems F) (hp : 0 < ringChar F)
    (eK : Env K) (eF : Env F) (w a xr lo hi : ℕ) (hw0 : eF.trace w = 0)
    (hs : (QE.scale (notE (cv w)) (QE.sub (QFP.var xr).size zQ) : QE F).ev δF eK eF = 0)
    (hd : (QE.scale (notE (cv w)) (QFP.var xr).dyck : QE F).ev δF eK eF = 0)
    (hl : (QE.scale (notE (cv w)) (QE.sub (QFP.var xr).leaf (QE.base (cv a))) : QE F).ev δF eK eF = 0)
    (hlo : (CoeffExpr.mul (notE (cv w)) (cv lo) : CoeffExpr F).eval eF = 0)
    (hhi : (CoeffExpr.mul (notE (cv w)) (cv hi) : CoeffExpr F).eval eF = 0) :
    (QFP.var xr).ev δF eK eF = FP.atomFP (zOf δF eK eF)
        (algebraMap (ZMod (ringChar F)) _ (natOf (eF.trace a) : ZMod (ringChar F))) ∧
      natOf (eF.trace lo) = 0 ∧ natOf (eF.trace hi) = 0 := by
  simp only [ev_scale, ev_sub, ev_base, CoeffExpr.eval, cv, notE, hw0, sub_zero, liftQ, map_one,
    one_mul] at hs hd hl
  simp only [CoeffExpr.eval, hw0, sub_zero, one_mul] at hlo hhi
  refine ⟨?_, by rw [hlo, natOf_zero hF hp], by rw [hhi, natOf_zero hF hp]⟩
  rw [algebraMap_natOf δF hF]
  ext
  · exact sub_eq_zero.mp hs
  · exact hd
  · exact sub_eq_zero.mp hl

theorem bit_bool_mem (i : ℕ) (hi : i < 110) :
    (boolE (cv (Cell.bit0 + i)) : CoeffExpr F) ∈ Cell.baseGates :=
  List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem consEq_mem (e : QE F) (he : e ∈ Cell.consEqs δF) : e ∈ Cell.qEqs δF := by
  unfold Cell.qEqs; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl he))

/-- **One cell row's gates ⇒ `RowGates`** (everything of `Table.RowOK` but the child-limb ranges). -/
theorem cellRow_gates (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (eK : Env K) (eF : Env F)
    (hb : ∀ g ∈ Cell.baseGates (F := F), g.eval eF = 0)
    (hm : ∀ e ∈ Cell.qEqs δF, e.ev δF eK eF = 0)
    (hz : zOf δF eK eF ≠ 0) :
    RowGates (zOf δF eK eF) (cellRowOf δF eK eF) := by
  have hp : 0 < ringChar F := by omega
  -- booleanity
  have hbool : ∀ j, (boolE (cv j) : CoeffExpr F) ∈ Cell.baseGates → eF.trace j = 0 ∨ eF.trace j = 1 :=
    fun j hj => bool_val (by simpa [CoeffExpr.eval, cv, boolE] using hb _ hj)
  have hw01 : ∀ j, (boolE (cv j) : CoeffExpr F) ∈ Cell.baseGates →
      decide (eF.trace j = 1) = false → eF.trace j = 0 := by
    intro j hj hd
    rcases hbool j hj with h | h
    · exact h
    · simp [h] at hd
  have gb : ∀ g ∈ Cell.baseGates (F := F), g.eval eF = 0 := hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cons
    have h1 := hm _ (consEq_mem δF _ (List.mem_cons_self ..))
    have h2 := hm _ (consEq_mem δF _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have h3 := hm _ (consEq_mem δF _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
    simp only [ev_sub, ev_mul, ev_add] at h1 h2 h3
    show (QFP.var Cell.pR).ev δF eK eF = FP.cons (zOf δF eK eF) ((QFP.var Cell.lR).ev δF eK eF)
      ((QFP.var Cell.rR).ev δF eK eF)
    ext
    · exact sub_eq_zero.mp h1
    · simp only [FP.cons, QFP.ev, zOf]
      have h3' := sub_eq_zero.mp h3
      field_simp
      linear_combination h3'
    · exact sub_eq_zero.mp h2
  · -- lo < 2^62
    have hg := gb _ (show (.sub (cv Cell.lo) (bitSum Cell.bit0 62) : CoeffExpr F) ∈ Cell.baseGates by
      simp [Cell.baseGates])
    simp only [CoeffExpr.eval] at hg
    show natOf (eF.trace Cell.lo) < 2 ^ 62
    rw [sub_eq_zero.mp hg]
    refine bitSum_nat hF _ _ _ (fun i hi => ?_) (by omega)
    simpa [CoeffExpr.eval, cv, boolE] using gb _ (bit_bool_mem i (by omega))
  · -- hi < 2^48
    have hg := gb _ (show (.sub (cv Cell.hi) (bitSum (Cell.bit0 + 62) 48) : CoeffExpr F) ∈
        Cell.baseGates by simp [Cell.baseGates])
    simp only [CoeffExpr.eval] at hg
    show natOf (eF.trace Cell.hi) < 2 ^ 48
    rw [sub_eq_zero.mp hg]
    refine bitSum_nat hF _ _ _ (fun i hi => ?_) (by omega)
    have := gb _ (bit_bool_mem (62 + i) (by omega))
    simpa [CoeffExpr.eval, cv, boolE, Nat.add_assoc] using this
  · -- carry ≤ 1
    show natOf (eF.trace Cell.carry) ≤ 1
    rcases hbool Cell.carry (by simp [Cell.baseGates]) with h | h
    · rw [h, natOf_zero hF hp]; omega
    · rw [h, show (1 : F) = ((1 : ℕ) : F) by simp, natOf_natCast hF (by omega)]
  · -- limbLo
    have hg := gb _ (show (.sub (.add (cv Cell.lo) (.mul (.const ((2 : F) ^ 62)) (cv Cell.carry)))
        (.add (.add (cv Cell.loL) (cv Cell.loR)) (.const 1)) : CoeffExpr F) ∈ Cell.baseGates by
      simp [Cell.baseGates])
    simp only [CoeffExpr.eval] at hg
    have e : ((natOf (eF.trace Cell.lo) + natOf (eF.trace Cell.carry) * 2 ^ 62 : ℕ) : F) =
        ((natOf (eF.trace Cell.loL) + natOf (eF.trace Cell.loR) + 1 : ℕ) : F) := by
      push_cast; rw [natOf_cast hF, natOf_cast hF, natOf_cast hF, natOf_cast hF]
      linear_combination hg
    have := zmod_of_field e
    push_cast at this
    show ((natOf (eF.trace Cell.lo) : ℕ) : ZMod (ringChar F)) + (natOf (eF.trace Cell.carry) : ZMod _) * 2 ^ 62 =
      (natOf (eF.trace Cell.loL) : ZMod _) + (natOf (eF.trace Cell.loR) : ZMod _) + 1
    norm_num at this ⊢
    exact this
  · -- limbHi
    have hg := gb _ (show (.sub (cv Cell.hi) (.add (.add (cv Cell.hiL) (cv Cell.hiR)) (cv Cell.carry)) :
        CoeffExpr F) ∈ Cell.baseGates by simp [Cell.baseGates])
    simp only [CoeffExpr.eval] at hg
    have e : ((natOf (eF.trace Cell.hi) : ℕ) : F) =
        ((natOf (eF.trace Cell.hiL) + natOf (eF.trace Cell.hiR) + natOf (eF.trace Cell.carry) : ℕ) : F) := by
      push_cast; rw [natOf_cast hF, natOf_cast hF, natOf_cast hF, natOf_cast hF]
      linear_combination hg
    have := zmod_of_field e
    push_cast at this ⊢
    exact this
  · -- atom L
    intro hw
    have hw0 := hw01 Cell.wL (by simp [Cell.baseGates]) hw
    have hA : ∀ e ∈ Cell.atomEqs (F := F) Cell.wL Cell.aL Cell.lR, e.ev δF eK eF = 0 := by
      intro e he; apply hm; unfold Cell.qEqs; simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he))
    exact atom_side δF hF hp eK eF Cell.wL Cell.aL Cell.lR Cell.loL Cell.hiL hw0
      (hA _ (List.mem_cons_self ..)) (hA _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (hA _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (gb _ (by simp [Cell.baseGates])) (gb _ (by simp [Cell.baseGates]))
  · -- atom R
    intro hw
    have hw0 := hw01 Cell.wR (by simp [Cell.baseGates]) hw
    have hA : ∀ e ∈ Cell.atomEqs (F := F) Cell.wR Cell.aR Cell.rR, e.ev δF eK eF = 0 := by
      intro e he; apply hm; unfold Cell.qEqs; simp only [List.mem_append]
      exact Or.inl (Or.inr he)
    exact atom_side δF hF hp eK eF Cell.wR Cell.aR Cell.rR Cell.loR Cell.hiR hw0
      (hA _ (List.mem_cons_self ..)) (hA _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (hA _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (gb _ (by simp [Cell.baseGates])) (gb _ (by simp [Cell.baseGates]))

/-- **`RowOK` from the row gates and the validity lookup's existence form**: the child limbs of a
weighted child are a providing row's limbs (`ValidityServed`), ranged by that row's own bits; a
zero-weight child's are `0`. -/
theorem rowOK_of_gates {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp] {z : Kfp}
    {t : List (CellRow q Kfp)} (hg : ∀ c ∈ t, RowGates z c) (hs : ValidityServed t) :
    ∀ c ∈ t, RowOK z c := by
  intro c hc
  have g := hg c hc
  have hL : c.b0.loL < 2 ^ 62 ∧ c.b0.hiL < 2 ^ 48 := by
    cases hw : c.b0.wL with
    | false => obtain ⟨-, h1, h2⟩ := g.atomL hw; rw [h1, h2]; omega
    | true =>
      obtain ⟨c', hc', -, hhi, hlo, -⟩ := (hs c hc).1 hw
      rw [hhi, hlo]; exact ⟨(hg c' hc').lo_lt, (hg c' hc').hi_lt⟩
  have hR : c.b0.loR < 2 ^ 62 ∧ c.b0.hiR < 2 ^ 48 := by
    cases hw : c.b0.wR with
    | false => obtain ⟨-, h1, h2⟩ := g.atomR hw; rw [h1, h2]; omega
    | true =>
      obtain ⟨c', hc', -, hhi, hlo, -⟩ := (hs c hc).2 hw
      rw [hhi, hlo]; exact ⟨(hg c' hc').lo_lt, (hg c' hc').hi_lt⟩
  exact ⟨g.cons, g.lo_lt, hL.1, hR.1, g.hi_lt, hL.2, hR.2, g.carry_le, g.limbLo, g.limbHi,
    g.atomL, g.atomR⟩

end Row

/-! ## 3. The accepted cell table -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- Row `i`'s base environment on the cell table. -/
abbrev cellEnvF {w : ℕ} (Q : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 129 chals) (slotVal b 129 pubs)

/-- Row `i`'s gathered `𝕂` environment. -/
abbrev cellEnvK {w : ℕ} (Q : Fin w → F[X]) (i : Fin n) : Env K :=
  gatherEnv b ((cellTemplate δF).col0 3) (cellEnvF b nodes orbit chals pubs Q i)

/-- **The cell table read off a trace**: one `CellRow` per row node. -/
def cellTableOf {w : ℕ} (Q : Fin w → F[X]) : List (CellRow (ringChar F) (Quad (algebraMap F K δF))) :=
  List.ofFn fun i : Fin n =>
    cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i)

/-- The seed the chip's cons / atom gates read: `z′ = χ₂ + χ₃√δ`. -/
theorem cell_zOf {w : ℕ} (Q : Fin w → F[X]) (i : Fin n) :
    zOf δF (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i) =
      Quad.mk _ (chals 2) (chals 3) := by
  simp only [zOf, zQ, ev_chal]
  rw [gather_chal_cell δF b chals _ rfl, gather_chal_cell δF b chals _ rfl]

variable (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])
  (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
include hsat

/-- Every row of an accepted cell table meets `RowGates` at the seed `z′`. -/
theorem cellTable_rowGates (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0) :
    ∀ c ∈ cellTableOf δF b nodes orbit chals pubs Q,
      RowGates (Quad.mk (algebraMap F K δF) (chals 2) (chals 3)) c := by
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  have hl := cellChip_rowLocal δF b hn nodes orbit chals pubs Q hsat i
  have hz' := cell_zOf δF b nodes orbit chals pubs Q i
  rw [← hz']
  refine cellRow_gates δF hF hq _ _ hl.1 (fun e he => ev_eq_zero_of_gates δF _ _ e fun g hg =>
    hl.2 g (List.mem_flatMap.mpr ⟨e, he, hg⟩)) (by rw [hz']; exact hz)

/-- **`SerialOK`** on the table read off an accepted trace (`cellChip_serial`, `n < p`). -/
theorem cellTable_serial (hF : GeneratedField.PrimeFieldElems F)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F) :
    SerialOK ((cellTableOf δF b nodes orbit chals pubs Q).map (·.b0)) := by
  have hser := cellChip_serial δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj
  have hw : (cellChip δF b hn nodes orbit chals pubs).rap.w = 225 :=
    (cellChip_fingerprint δF b hn nodes orbit chals pubs).1
  unfold SerialOK cellTableOf
  simp only [List.map_ofFn, List.length_ofFn]
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_range]
  show natOf ((cellEnvF b nodes orbit chals pubs Q ⟨k, by simpa using h1⟩).trace Cell.idx) = k
  rw [show Cell.idx = 2 from rfl, envOfTrace_trace Q _ _ _ _ (show 2 < _ by rw [hw]; omega)]
  rw [hser ⟨k, by simpa using h1⟩, natOf_natCast hF (by simp at h1; omega)]

/-- **The cell table accepts** (`Table.TableAccepts`) on any accepted trace, given the validity
lookup's existence form (step (3) discharges it from the accumulator). -/
theorem cellTable_accepts (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (hserved : ValidityServed (cellTableOf δF b nodes orbit chals pubs Q))
    (vl : List (VKey (Quad (algebraMap F K δF)))) :
    TableAccepts (Quad.mk (algebraMap F K δF) (chals 2) (chals 3))
      (cellTableOf δF b nodes orbit chals pubs Q) vl :=
  ⟨cellTable_serial δF b hn nodes orbit chals pubs Q hsat hF hbind hinj hadj hnp,
    rowOK_of_gates (cellTable_rowGates δF b hn nodes orbit chals pubs Q hsat hF hq hz) hserved,
    hserved⟩

end Chip


end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
