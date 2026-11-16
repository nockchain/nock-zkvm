/-
  Nock/NockVMROM/Thm54/VclL/Handle/ProvideH.lean

* **Read-set congruence** (`colsBelow`, `mixBelow`, `colsBelow_eval`, `mixBelow_eval`) and the
    generic **restriction** `expandChip_restrict`: if a twin template keeps an original template's
    base and mixed gates, adds base columns after the original's and `𝕂`-roles after the original's,
    and the original gates read only the original's columns, then a twin-accepted trace restricted
    to the original's columns (`restrictQ`) is original-accepted.  So every theorem about the
    original chip applies to the twin unchanged — nothing is re-proved.
  * **`cellTemplateH`** = `cellTemplate` + the B0 multiplicity `mh` (column `129`) + two `𝕂`-roles
    (`32` provide inverse, `33` accumulator) + four `𝕂` gates: the provide inverse
    `invH·(ρ + Σ_k γ^k·key_k) − 1` and the accumulator's init / step / terminal.  The provided key is
    `keyH = (idx, wL, wL·idL + (1 − wL)·aL, wR, wR·idR + (1 − wR)·aR)` — the existing columns at
    degree `2`, **no new data column** (VS handle `(kind, serial-or-atom)` of each child, in the
    order of `ChipH.cellRec`).  Coins: `𝕂` leaves `hGam = 33`, `hRho = 34` (the frame wiring of
    these slots is UNCONFIRMED, as for `ChipH`).  **MEASURED `w = 232` (`cellChipH_width`).**
  * **`exportH_genuine`** (the chip form of P4-1's `exportRec_grounded`): on a twin-accepted trace,
    every row's provided record, read off the twin's key expressions, is `exportRec` of the row's
    round-0 data, and `denH (1, idx) = cell (denH hL) (denH hR)`, from `row_genuine` (T1, rank μ) and
    the restriction; the serial names one row (`denH_serial_meaning`, `serial_functional`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.Ground

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Read sets and congruence -/

section Congr
variable {F : Type} [Field F]

/-- A base expression reads only trace columns `< B` (current or next row); no coin, no public. -/
def colsBelow (B : ℕ) : CoeffExpr F → Bool
  | .const _ => true
  | .var .traceCur i => decide (i < B)
  | .var .traceNext i => decide (i < B)
  | .var .challenge _ => false
  | .var .publicVal _ => false
  | .add a b => colsBelow B a && colsBelow B b
  | .sub a b => colsBelow B a && colsBelow B b
  | .mul a b => colsBelow B a && colsBelow B b
  | .neg a => colsBelow B a
  | .pow a _ => colsBelow B a

/-- A mixed expression reads only `𝕂`-roles `< R` and base columns `< B` (coins and publics free). -/
def mixBelow (R B : ℕ) : MixedExpr F → Bool
  | .Var .traceCur i => decide (i < R)
  | .Var .traceNext i => decide (i < R)
  | .Var .challenge _ => true
  | .Var .publicVal _ => true
  | .Lift g => colsBelow B g
  | .Scale g u => colsBelow B g && mixBelow R B u
  | .Const _ => true
  | .Add x y => mixBelow R B x && mixBelow R B y
  | .Sub x y => mixBelow R B x && mixBelow R B y
  | .Neg x => mixBelow R B x
  | .Mul x y => mixBelow R B x && mixBelow R B y
  | .Pow x _ => mixBelow R B x

theorem colsBelow_eval {B : ℕ} {g : CoeffExpr F} (hg : colsBelow B g = true) {e e' : Env F}
    (ht : ∀ j < B, e.trace j = e'.trace j) (hn : ∀ j < B, e.traceNext j = e'.traceNext j) :
    g.eval e = g.eval e' := by
  induction g with
  | const c => rfl
  | var k i =>
    cases k <;> simp only [colsBelow, decide_eq_true_eq, Bool.false_eq_true] at hg <;>
      simp only [CoeffExpr.eval]
    · exact ht i hg
    · exact hn i hg
  | add a b iha ihb =>
    simp only [colsBelow, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | sub a b iha ihb =>
    simp only [colsBelow, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | mul a b iha ihb =>
    simp only [colsBelow, Bool.and_eq_true] at hg
    simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | neg a iha =>
    simp only [colsBelow] at hg
    simp only [CoeffExpr.eval, iha hg]
  | pow a m iha =>
    simp only [colsBelow] at hg
    simp only [CoeffExpr.eval, iha hg]

variable {K : Type} [Field K] [Algebra F K]

theorem mixBelow_eval {R B : ℕ} {g : MixedExpr F} (hg : mixBelow R B g = true) {eK eK' : Env K}
    {eF eF' : Env F} (hKt : ∀ i < R, eK.trace i = eK'.trace i)
    (hKn : ∀ i < R, eK.traceNext i = eK'.traceNext i) (hKc : eK.chal = eK'.chal)
    (hKp : eK.pub = eK'.pub) (hFt : ∀ j < B, eF.trace j = eF'.trace j)
    (hFn : ∀ j < B, eF.traceNext j = eF'.traceNext j) :
    g.eval eK eF = g.eval eK' eF' := by
  induction g with
  | Var k i =>
    cases k <;> simp only [mixBelow, decide_eq_true_eq] at hg <;> simp only [MixedExpr.eval]
    · exact hKt i hg
    · exact hKn i hg
    · rw [hKc]
    · rw [hKp]
  | Lift g =>
    simp only [mixBelow] at hg
    simp only [MixedExpr.eval, colsBelow_eval hg hFt hFn]
  | Scale g u ih =>
    simp only [mixBelow, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, colsBelow_eval hg.1 hFt hFn, ih hg.2]
  | Const c => rfl
  | Add x y ihx ihy =>
    simp only [mixBelow, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Sub x y ihx ihy =>
    simp only [mixBelow, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Neg x ih =>
    simp only [mixBelow] at hg
    simp only [MixedExpr.eval, ih hg]
  | Mul x y ihx ihy =>
    simp only [mixBelow, Bool.and_eq_true] at hg
    simp only [MixedExpr.eval, ihx hg.1, ihy hg.2]
  | Pow x m ih =>
    simp only [mixBelow] at hg
    simp only [MixedExpr.eval, ih hg]

end Congr

/-! ## 2. The restriction: a twin that only ADDS columns and gates accepts what the original does -/

section Restrict
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Original column `j` sits at twin column `j` (base, `j < B`) or `j + (B' − B)` (`𝕂` limbs). -/
def shiftCol (B B' j : ℕ) : ℕ := if j < B then j else j + (B' - B)

/-- **The restriction of a twin trace** to the original's columns. -/
def restrictQ {w w' : ℕ} (B B' : ℕ) (hw : ∀ j < w, shiftCol B B' j < w') (Q : Fin w' → F[X]) :
    Fin w → F[X] := fun j => Q ⟨shiftCol B B' j, hw j j.isLt⟩

theorem envOfTrace_restrict_trace {w w' : ℕ} (B B' : ℕ) (hw : ∀ j < w, shiftCol B B' j < w')
    (Q : Fin w' → F[X]) (ω x : F) (cv pv cv' pv' : ℕ → F) {j : ℕ} (hj : j < w) :
    (Reify.envOfTrace (restrictQ B B' hw Q) ω x cv pv).trace j =
      (Reify.envOfTrace Q ω x cv' pv').trace (shiftCol B B' j) := by
  simp [Reify.envOfTrace, hj, hw j hj, restrictQ]

theorem envOfTrace_restrict_traceNext {w w' : ℕ} (B B' : ℕ) (hw : ∀ j < w, shiftCol B B' j < w')
    (Q : Fin w' → F[X]) (ω x : F) (cv pv cv' pv' : ℕ → F) {j : ℕ} (hj : j < w) :
    (Reify.envOfTrace (restrictQ B B' hw Q) ω x cv pv).traceNext j =
      (Reify.envOfTrace Q ω x cv' pv').traceNext (shiftCol B B' j) := by
  simp [Reify.envOfTrace, hj, hw j hj, restrictQ]

variable (b : Basis (Fin 3) F K) {h : ℕ} (orbit : StrictOrbitDomain F 3 h) (H : Finset F)
  (chals pubs : ℕ → K)

/-- The original's width bound is enough for the shift. -/
theorem shift_lt (T T' : ChipTemplate F) (B B' : ℕ) (hBe : T.baseCols = B) (hB'e : T'.baseCols = B')
    (hB : B ≤ B') (hR : T.extCols ≤ T'.extCols) :
    ∀ j < T.width 3, shiftCol B B' j < T'.width 3 := by
  intro j hj
  subst hBe hB'e
  unfold shiftCol ChipTemplate.width at *
  split_ifs <;> omega

/-- **The restriction theorem.**  Let `T'` keep `T`'s base gates and mixed gates (each reading
only `T`'s base columns and `𝕂`-roles), with `T` carrying no other gate kind.  Then the
restriction of a `T'`-accepted trace is `T`-accepted. -/
theorem expandChip_restrict (T T' : ChipTemplate F) (B B' : ℕ) (hBe : T.baseCols = B)
    (hB'e : T'.baseCols = B') (hB : B ≤ B') (hR : T.extCols ≤ T'.extCols)
    (hbase : ∀ g ∈ T.baseTransition, g ∈ T'.baseTransition ∧ colsBelow B g = true)
    (hmix : ∀ g ∈ T.mixedTransition,
      g ∈ T'.mixedTransition ∧ mixBelow T.extCols B g = true)
    (hEq : T.equalityChecks = []) (hExt : T.extTransition ++ T.extDeg1 ++ T.extDeg3 = [])
    (Q : Fin (expandChip T' b (slotVal b B' chals) (slotVal b B' pubs) orbit H).w → F[X])
    (hsat : (expandChip T' b (slotVal b B' chals) (slotVal b B' pubs) orbit H).Satisfies Q) :
    (expandChip T b (slotVal b B chals) (slotVal b B pubs) orbit H).Satisfies
      (restrictQ B B' (shift_lt T T' B B' hBe hB'e hB hR) Q) := by
  subst hBe hB'e
  rw [expandChip_satisfies_iff_language] at hsat ⊢
  intro x hx
  obtain ⟨hb', -, -, hm'⟩ := hsat x hx
  set e0 := Reify.envOfTrace (restrictQ T.baseCols T'.baseCols (shift_lt T T' _ _ rfl rfl hB hR) Q) orbit.ω x
    (slotVal b T.baseCols chals) (slotVal b T.baseCols pubs)
  set e1 := Reify.envOfTrace Q orbit.ω x (slotVal b T'.baseCols chals) (slotVal b T'.baseCols pubs)
  have hw0 : (expandChip T b (slotVal b T.baseCols chals) (slotVal b T.baseCols pubs) orbit H).w = T.baseCols + T.extCols * 3 :=
    rfl
  have ht : ∀ j < T.baseCols, e0.trace j = e1.trace j := by
    intro j hj
    have := envOfTrace_restrict_trace T.baseCols T'.baseCols (shift_lt T T' _ _ rfl rfl hB hR) Q orbit.ω x (slotVal b T.baseCols chals)
      (slotVal b T.baseCols pubs) (slotVal b T'.baseCols chals) (slotVal b T'.baseCols pubs) (j := j)
      (by show j < T.width 3; unfold ChipTemplate.width; omega)
    rw [this]; simp only [shiftCol, if_pos hj]; rfl
  have hn : ∀ j < T.baseCols, e0.traceNext j = e1.traceNext j := by
    intro j hj
    have := envOfTrace_restrict_traceNext T.baseCols T'.baseCols (shift_lt T T' _ _ rfl rfl hB hR) Q orbit.ω x
      (slotVal b T.baseCols chals) (slotVal b T.baseCols pubs) (slotVal b T'.baseCols chals) (slotVal b T'.baseCols pubs) (j := j)
      (by show j < T.width 3; unfold ChipTemplate.width; omega)
    rw [this]; simp only [shiftCol, if_pos hj]; rfl
  have hlimb : ∀ i < T.extCols, ∀ k : Fin 3,
      e0.trace (T.col0 3 .traceCur i + k) = e1.trace (T'.col0 3 .traceCur i + k) ∧
      e0.traceNext (T.col0 3 .traceNext i + k) = e1.traceNext (T'.col0 3 .traceNext i + k) := by
    intro i hi k
    have hk := k.isLt
    have hlt : T.col0 3 .traceCur i + k < T.width 3 := by
      unfold ChipTemplate.col0 ChipTemplate.width; nlinarith
    have hsh : shiftCol T.baseCols T'.baseCols (T.col0 3 .traceCur i + k) = T'.col0 3 .traceCur i + k := by
      unfold shiftCol ChipTemplate.col0
      rw [if_neg (by omega)]; omega
    constructor
    · exact (envOfTrace_restrict_trace T.baseCols T'.baseCols (shift_lt T T' _ _ rfl rfl hB hR) Q orbit.ω x _ _
        (slotVal b T'.baseCols chals) (slotVal b T'.baseCols pubs) hlt).trans (by rw [hsh]; try rfl)
    · have hsh' : shiftCol T.baseCols T'.baseCols (T.col0 3 .traceNext i + k) = T'.col0 3 .traceNext i + k := hsh
      have hlt' : T.col0 3 .traceNext i + k < T.width 3 := hlt
      exact (envOfTrace_restrict_traceNext T.baseCols T'.baseCols (shift_lt T T' _ _ rfl rfl hB hR) Q orbit.ω x _ _
        (slotVal b T'.baseCols chals) (slotVal b T'.baseCols pubs) hlt').trans (by rw [hsh']; try rfl)
  refine ⟨fun g hg => ?_, by simp [hEq], by simp [hExt], fun g hg => ?_⟩
  · show g.eval e0 = 0
    rw [colsBelow_eval (hbase g hg).2 ht hn]
    exact hb' g (hbase g hg).1
  · show g.eval (gatherEnv b (T.col0 3) e0) e0 = 0
    rw [mixBelow_eval (hmix g hg).2 (eK' := gatherEnv b (T'.col0 3) e1) (eF' := e1) ?_ ?_ ?_ ?_ ht hn]
    · exact hm' g (hmix g hg).1
    · intro i hi
      simp only [gatherEnv]
      exact Finset.sum_congr rfl fun k _ => by rw [(hlimb i hi k).1]
    · intro i hi
      simp only [gatherEnv]
      exact Finset.sum_congr rfl fun k _ => by rw [(hlimb i hi k).2]
    · funext i
      simp only [gatherEnv, ChipTemplate.col0]
      show ∑ k : Fin 3, slotVal b T.baseCols chals (T.baseCols + 3 * i + k) • b k =
        ∑ k : Fin 3, slotVal b T'.baseCols chals (T'.baseCols + 3 * i + k) • b k
      rw [sum_slotVal, sum_slotVal]
    · funext i
      simp only [gatherEnv, ChipTemplate.col0]
      show ∑ k : Fin 3, slotVal b T.baseCols pubs (T.baseCols + 3 * i + k) • b k =
        ∑ k : Fin 3, slotVal b T'.baseCols pubs (T'.baseCols + 3 * i + k) • b k
      rw [sum_slotVal, sum_slotVal]

end Restrict

/-! ## 3. The cell twin `cellTemplateH` -/

namespace CellH

section Gates
variable {F : Type} [Field F]

/-- The handle-export multiplicity (round 0, base column `129`, after `mx1`). -/
def mh : ℕ := 129
/-- `𝕂`-roles: the handle-export provide inverse and accumulator (after the `32` existing roles). -/
def invH : ℕ := 32
def accH : ℕ := 33
/-- `𝕂` coin leaves of the handle LogUp (`γ`, `ρ`; UNCONFIRMED frame wiring) and its terminal. -/
def hGam : ℕ := 33
def hRho : ℕ := 34
def pubH : ℕ := 4

/-- A child's handle value `w·id + (1 − w)·a`: the serial if weighted, the atom value otherwise. -/
def valE (w i a : ℕ) : CoeffExpr F := .add (.mul (cv w) (cv i)) (.mul (notE (cv w)) (cv a))

/-- **The provided handle-export key** `(idx, hL.kind, hL.val, hR.kind, hR.val)` (`ChipH.cellRec`'s
order), from the existing columns. -/
def keyH : List (CoeffExpr F) :=
  [cv Cell.idx, cv Cell.wL, valE Cell.wL Cell.idL Cell.aL, cv Cell.wR, valE Cell.wR Cell.idR Cell.aR]

/-- `Σ_k γ^k · lift(key_k)` (the record form `ChipH.rlcKey` consumes). -/
def rlcH : ℕ → List (CoeffExpr F) → MixedExpr F
  | _, [] => .Const 0
  | m, g :: r => .Add (.Mul (.Pow (.Var .challenge hGam) m) (.Lift g)) (rlcH (m + 1) r)

def denKey (l : List (CoeffExpr F)) : MixedExpr F := .Add (.Var .challenge hRho) (rlcH 0 l)

/-- **The four handle-export gates** (`𝕂`): provide inverse, accumulator init / step / terminal. -/
def gates : List (MixedExpr F) :=
  [ .Sub (.Mul (.Var .traceCur invH) (denKey keyH)) (.Const 1),
    .Scale (cv Cell.isF) (.Sub (.Var .traceCur accH) (.Scale (cv mh) (.Var .traceCur invH))),
    .Scale (notE (cv Cell.isL)) (.Sub (.Sub (.Var .traceNext accH) (.Var .traceCur accH))
      (.Scale (nv mh) (.Var .traceNext invH))),
    .Scale (cv Cell.isL) (.Sub (.Var .traceCur accH) (.Var .publicVal pubH)) ]

theorem gates_deg_all : (gates (F := F)).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [gates, denKey, rlcH, keyH, valE, MixedExpr.degree, CoeffExpr.degree]

theorem gates_deg : ∀ g ∈ gates (F := F), g.degree ≤ 4 := by
  intro g hg
  simpa using List.all_eq_true.mp gates_deg_all g hg

theorem mixed_deg (δF : F) : ∀ g ∈ Cell.mixedGates δF ++ gates (F := F), g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact cellMixed_deg δF g hg
  · exact gates_deg g hg

end Gates

end CellH

section Template
variable {F : Type} [Field F]

/-- **The cell twin template**: base `130` (`+ mh`), `𝕂`-roles `0 / 18 / 16` (`+ invH accH`). -/
def cellTemplateH (δF : F) : ChipTemplate F where
  rounds := 3
  rounds_pos := by decide
  baseColsOf := ![130, 0, 0]
  extColsOf := ![0, 18, 16]
  baseTransition := Cell.baseGates
  extTransition := []
  mixedTransition := Cell.mixedGates δF ++ CellH.gates
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := cellBase_deg
  extTransition_deg := by simp
  mixedTransition_deg := CellH.mixed_deg δF
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

theorem cellTemplateH_baseCols (δF : F) : (cellTemplateH δF).baseCols = 130 := by
  show (∑ r : Fin 3, (![130, 0, 0] : Fin 3 → ℕ) r) = 130
  decide
theorem cellTemplateH_extCols (δF : F) : (cellTemplateH δF).extCols = 34 := by
  show (∑ r : Fin 3, (![0, 18, 16] : Fin 3 → ℕ) r) = 34
  decide



theorem colsBelow_sumList (B : ℕ) (l : List ℕ) (f : ℕ → CoeffExpr F)
    (h : ∀ i ∈ l, colsBelow B (f i) = true) : colsBelow B (CoeffExpr.sumList l f) = true := by
  induction l with
  | nil => simp [CoeffExpr.sumList, colsBelow]
  | cons a t ih =>
    simp only [CoeffExpr.sumList, List.foldr_cons, colsBelow, Bool.and_eq_true] at ih ⊢
    exact ⟨h a (by simp), ih fun i hi => h i (by simp [hi])⟩

theorem colsBelow_bitSum (B base m : ℕ) (hm : base + m ≤ B) :
    colsBelow B (bitSum (F := F) base m) = true := by
  unfold bitSum
  refine colsBelow_sumList B _ _ fun i hi => ?_
  simp only [List.mem_range] at hi
  simp [colsBelow]; omega

theorem cellBase_below : ∀ g ∈ Cell.baseGates (F := F), colsBelow 129 g = true := by
  intro g hg
  simp only [Cell.baseGates, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hg
  rcases hg with (h | h | h | h | h | h | h | h | h | h | h | h | h) | ⟨i, hi, rfl⟩
  all_goals first
    | (subst h; simp [colsBelow, Cell.isF, Cell.isL, Cell.idx, Cell.lo, Cell.hi, Cell.carry, Cell.loL,
        Cell.loR, Cell.hiL, Cell.hiR, Cell.wL, Cell.wR]; done)
    | (subst h; simp only [colsBelow, Bool.and_eq_true, decide_eq_true_eq]
       refine ⟨by simp [Cell.lo, Cell.hi], colsBelow_bitSum 129 _ _ (by simp [Cell.bit0])⟩)
    | (simp [colsBelow, Cell.bit0]; exact decide_eq_true (by omega))

theorem cellMixed_below (δF : F) : ∀ g ∈ Cell.mixedGates δF, mixBelow 32 129 g = true := by
  have hall : (Cell.mixedGates δF).all (mixBelow 32 129) = true := by
    simp [Cell.mixedGates, Cell.qEqs, Cell.consEqs, Cell.atomEqs, Cell.vKeyP, Cell.vKeyL,
      Cell.vKeyR, Cell.xKey, Cell.xKeyS, Cell.vTerm, Cell.xTerm, QE.gates, QE.var, QE.next, QE.chal,
      QE.pub, QE.base, QE.mk2, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, QE.rlc, QE.gpow,
      QFP.var, QFP.next, QFP.entries, QFP.sub, QFP.add, QFP.scale, QFP.gates, den, zQ, rQ,
      mixBelow, colsBelow, List.zipIdx, Cell.pR, Cell.lR, Cell.rR, Cell.vProvInv, Cell.consLInv,
      Cell.consRInv, Cell.xProvInv, Cell.xProvInv1, Cell.vAcc, Cell.xAcc, Cell.isF, Cell.isL,
      Cell.idx, Cell.idL, Cell.idR, Cell.wL, Cell.wR, Cell.aL, Cell.aR, Cell.lo, Cell.hi, Cell.loL,
      Cell.hiL, Cell.loR, Cell.hiR, Cell.mv, Cell.mx, Cell.mx1]
  intro g hg
  exact List.all_eq_true.mp hall g hg

end Template

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The cell twin chip** (`expandChip` of `cellTemplateH`, masks at `0`, `1`). -/
def cellChipH (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) : FixedPreprocessingRAP F where
  rap := expandChip (cellTemplateH δF) b (slotVal b 130 chals) (slotVal b 130 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 130 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

variable (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- **The cell twin's width, MEASURED: `232`** (`225 + mh + 2 𝕂`-roles). -/
theorem cellChipH_width : (cellChipH δF b hn nodes orbit chals pubs).rap.w = 232 := by
  show (cellTemplateH δF).baseCols + (cellTemplateH δF).extCols * 3 = 232
  rw [cellTemplateH_baseCols, cellTemplateH_extCols]

theorem cellChipH_s : (cellChipH δF b hn nodes orbit chals pubs).rap.s = 255 + 4 * 3 := by
  rw [show (cellChipH δF b hn nodes orbit chals pubs).rap =
      expandChip (cellTemplateH δF) b _ _ orbit _ from rfl, expandChip_s]
  simp only [cellTemplateH, cellBase_length, List.length_append, cellMixed_length, CellH.gates,
    List.length_cons, List.length_nil]

theorem cellH_shift : ∀ j < (cellTemplate δF).width 3,
    shiftCol 129 130 j < (cellTemplateH δF).width 3 :=
  shift_lt _ _ 129 130 (cellTemplate_baseCols δF) (cellTemplateH_baseCols δF) (by omega)
    (by rw [cellTemplate_extCols, cellTemplateH_extCols]; omega)

/-- **The restriction of a twin trace to the original cell chip's `225` columns.** -/
def restrictCell (Q : Fin (cellChipH δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X] :=
  restrictQ 129 130 (cellH_shift δF) Q

variable (Q : Fin (cellChipH δF b hn nodes orbit chals pubs).rap.w → F[X])

/-- **Twin acceptance ⇒ original acceptance** of the restriction. -/
theorem cellChipH_restrict_sat (hsat : (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies
      (restrictCell δF b hn nodes orbit chals pubs Q) := by
  have hB : (cellTemplate δF).baseCols = 129 := cellTemplate_baseCols δF
  have hR : (cellTemplate δF).extCols = 32 := cellTemplate_extCols δF
  exact expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (cellTemplate δF)
    (cellTemplateH δF) 129 130 hB (cellTemplateH_baseCols δF) (by omega)
    (by rw [hR, cellTemplateH_extCols]; omega)
    (fun g hg => ⟨hg, cellBase_below g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [hR]; exact cellMixed_below δF g hg⟩)
    rfl rfl Q hsat

/-- The preprocessing transfers (columns `0`, `1` are not shifted). -/
theorem cellChipH_restrict_bind
    (hbind : (cellChipH δF b hn nodes orbit chals pubs).BindsPreprocessing Q) :
    (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing
      (restrictCell δF b hn nodes orbit chals pubs Q) := by
  intro j
  have hj := hbind j
  fin_cases j
  · exact hj
  · exact hj

end Chip

/-! ## 4. The provided record and its genuineness -/

section Genuine
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))] [Fact (ringChar F).Prime]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

/-- A handle as two field entries `(kind, value)`. -/
def hF2 (x : VHandle) : List F := [if x.1 then 1 else 0, (x.2 : F)]

/-- An export record `(idx, hL, hR)` as the five field entries the twin provides. -/
def recF (r : ℕ × VHandle × VHandle) : List F := (r.1 : F) :: (hF2 r.2.1 ++ hF2 r.2.2)

/-- Row `i`'s base environment on the twin. -/
abbrev cellEnvFH {w : ℕ} (Q : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 130 chals) (slotVal b 130 pubs)

/-- **The provided key IS the row's handle-export record** (any base env whose `wL`, `wR` are
boolean): `keyH` evaluates to `recF (exportRec (cellB0Of eF))`. -/
theorem keyH_eval (hF : GeneratedField.PrimeFieldElems F) (eF : Env F)
    (hwL : eF.trace Cell.wL = 0 ∨ eF.trace Cell.wL = 1)
    (hwR : eF.trace Cell.wR = 0 ∨ eF.trace Cell.wR = 1) :
    CellH.keyH.map (fun g : CoeffExpr F => g.eval eF) = recF (exportRec (cellB0Of eF)) := by
  have hval : ∀ x : F, (((natOf x : ZMod (ringChar F)).val : ℕ) : F) = x := by
    intro x
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (natOf_lt hF x), natOf_cast hF x]
  have hside : ∀ (w i a : ℕ), (eF.trace w = 0 ∨ eF.trace w = 1) →
      [eF.trace w, (CellH.valE w i a).eval eF] =
        hF2 ((decide (eF.trace w = 1)),
          if decide (eF.trace w = 1) then natOf (eF.trace i)
          else (natOf (eF.trace a) : ZMod (ringChar F)).val) := by
    intro w i a hw
    rcases hw with h0 | h1
    · have : ¬ (eF.trace w = 1) := by rw [h0]; exact zero_ne_one
      simp [hF2, CellH.valE, CoeffExpr.eval, h0, this, Nat.mod_eq_of_lt (natOf_lt hF _), natOf_cast hF]
    · simp [hF2, CellH.valE, CoeffExpr.eval, h1, natOf_cast hF]
  have eL : hF2 (F := F) (hL (cellB0Of eF)) =
      [eF.trace Cell.wL, (CellH.valE Cell.wL Cell.idL Cell.aL).eval eF] :=
    (hside Cell.wL Cell.idL Cell.aL hwL).symm
  have eR : hF2 (F := F) (hR (cellB0Of eF)) =
      [eF.trace Cell.wR, (CellH.valE Cell.wR Cell.idR Cell.aR).eval eF] :=
    (hside Cell.wR Cell.idR Cell.aR hwR).symm
  show [eF.trace Cell.idx, eF.trace Cell.wL, (CellH.valE Cell.wL Cell.idL Cell.aL).eval eF,
      eF.trace Cell.wR, (CellH.valE Cell.wR Cell.idR Cell.aR).eval eF] =
    ((cellB0Of eF).idx : F) :: (hF2 (hL (cellB0Of eF)) ++ hF2 (hR (cellB0Of eF)))
  rw [eL, eR]
  show _ = (natOf (eF.trace Cell.idx) : F) :: _
  rw [natOf_cast hF]
  rfl

variable (Q : Fin (cellChipH δF b hn nodes orbit chals pubs).rap.w → F[X])

/-- The twin's row environment agrees with the restriction's on the original base columns. -/
theorem cellEnvFH_trace (i : Fin n) {j : ℕ} (hj : j < 129) :
    (cellEnvFH b nodes orbit chals pubs Q i).trace j =
      (cellEnvF b nodes orbit chals pubs (restrictCell δF b hn nodes orbit chals pubs Q) i).trace j := by
  have hw : (cellChip δF b hn nodes orbit chals pubs).rap.w = 225 :=
    (cellChip_fingerprint δF b hn nodes orbit chals pubs).1
  have h0 : j < (cellChip δF b hn nodes orbit chals pubs).rap.w := by rw [hw]; omega
  have h1 : j < (cellChipH δF b hn nodes orbit chals pubs).rap.w := by
    rw [cellChipH_width]; omega
  simp only [cellEnvF, Reify.envOfTrace, dif_pos h0, dif_pos h1, restrictCell, restrictQ]
  congr 2
  apply Fin.ext
  simp [shiftCol, hj]

/-- `cellB0Of` reads only base columns `< 129`, so the twin and the restriction give one row. -/
theorem cellB0Of_twin (i : Fin n) :
    cellB0Of (cellEnvFH b nodes orbit chals pubs Q i) =
      cellB0Of (cellEnvF b nodes orbit chals pubs (restrictCell δF b hn nodes orbit chals pubs Q) i) := by
  simp only [cellB0Of, cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idx < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idL < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idR < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.wL < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.wR < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.aL < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.aR < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.lo < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hi < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.loL < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hiL < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.loR < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hiR < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.carry < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.mv < 129),
    cellEnvFH_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.mx < 129)]

/-- **`exportH_genuine`** (the chip form of P4-1's `exportRec_grounded`).  On a trace accepted by
the twin `cellChipH` (with the validity lookup's existence form for the restricted table, as
`cellTable_accepts` takes it), at every row `i` the handle-export record the twin PROVIDES — the
evaluation of `keyH` — is `recF (exportRec c)` for the row's round-0 data `c`, the serial names
exactly one row, and `denH (1, c.idx) = cell (denH hL) (denH hR)` on the table read off the trace. -/
theorem exportH_genuine (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    (hsat : (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChipH δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (hserved : ValidityServed
      (cellTableOf δF b nodes orbit chals pubs (restrictCell δF b hn nodes orbit chals pubs Q)))
    (i : Fin n) :
    let tb := (cellTableOf δF b nodes orbit chals pubs
      (restrictCell δF b hn nodes orbit chals pubs Q)).map (·.b0)
    let c := cellB0Of (cellEnvFH b nodes orbit chals pubs Q i)
    CellH.keyH.map (fun g : CoeffExpr F => g.eval (cellEnvFH b nodes orbit chals pubs Q i)) =
        recF (exportRec c) ∧
      c ∈ tb ∧ (∀ c' ∈ tb, c'.idx = c.idx → c' = c) ∧
      ∃ L R, denH tb (true, c.idx) = some (.cell L R) ∧ denH tb (hL c) = some L ∧
        denH tb (hR c) = some R := by
  intro tb c
  set Q0 := restrictCell δF b hn nodes orbit chals pubs Q
  have hsat0 := cellChipH_restrict_sat δF b hn nodes orbit chals pubs Q hsat
  have hbind0 := cellChipH_restrict_bind δF b hn nodes orbit chals pubs Q hbind
  have hacc := cellTable_accepts δF b hn nodes orbit chals pubs Q0 hsat0 hF hq hz hbind0 hinj hadj
    hnp hserved []
  -- booleanity of `wL`, `wR` at the twin row (the twin keeps the original base gates)
  have hbase := ((expandChip_satisfies_iff_language _ b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)).1
  have hbool : ∀ w, boolE (cv w) ∈ Cell.baseGates (F := F) →
      (cellEnvFH b nodes orbit chals pubs Q i).trace w = 0 ∨
        (cellEnvFH b nodes orbit chals pubs Q i).trace w = 1 := by
    intro w hw
    have g := hbase _ hw
    simp only [CoeffExpr.eval, cv] at g
    exact bool_val g
  have hwL := hbool Cell.wL (by simp [Cell.baseGates])
  have hwR := hbool Cell.wR (by simp [Cell.baseGates])
  have hc : cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q0 i)
      (cellEnvF b nodes orbit chals pubs Q0 i) ∈ cellTableOf δF b nodes orbit chals pubs Q0 :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hcb : c = (cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q0 i)
      (cellEnvF b nodes orbit chals pubs Q0 i)).b0 :=
    cellB0Of_twin δF b hn nodes orbit chals pubs Q i
  have hctb : c ∈ tb := by rw [hcb]; exact List.mem_map_of_mem hc
  refine ⟨keyH_eval hF _ hwL hwR, hctb, fun c' hc' he =>
    ((denH_serial_meaning hacc.serial c.idx (.atom 0)).2 c' hc' c hctb he rfl), ?_⟩
  rw [hcb]
  exact exportRec_grounded hq hz hacc hc

end Genuine

end

end Nock.NockVMROM.Thm54.VclL.Handle
