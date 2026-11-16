import Nock.NockVMROM.Thm54.Unhosted309Chip

/-!
# Host-insensitivity of the untouched compute sources

**  Instrument + receipts; nothing existing is edited.**

The un-hosted 309 trace differs from the deployed canonical trace only at the eight former
walk-host `𝕂`-roles (`6, 7, 9, 10, 18, 19, 27, 28`), and on a row of state `s` only at the two
host roles of `s` (`3·overlayANat s`, `3·overlayANat s + 1`).

* `specSel σ e` substitutes a partial constant valuation `σ` (the one-hot state selectors);
* `simp0` folds constants (multiplication by `0` kills a subterm);
* `readsE` lists the variables of the folded expression;
* `eval_eq_of_insensitive`: if the folded expression avoids a set `D`, two environments that
  match `σ` and agree off `D` evaluate the source equally.
-/

namespace Nock.NockVMROM.Thm54
namespace Unhosted309

open Nock
open Nock.Reified
open Nock.ComputeTable
open OptimizedComputeSubstitution
open OptimizedComputeGateBasis
open OptimizedComputeCorrectedFinal

set_option maxRecDepth 300000

/-! ## 1. Partial constant valuations -/

/-- A partial integer valuation of variables. -/
abbrev Valuation := VarKind → ℕ → Option ℤ

/-- Replace each valued variable by its constant. -/
def specSel (σ : Valuation) (e : Expr) : Expr :=
  e.subst fun k i => match σ k i with | some v => .Const v | none => .Var k i

/-- The value of a variable in an environment. -/
def varVal {K : Type*} (E : Env K) : VarKind → ℕ → K
  | .traceCur, i => E.trace i
  | .traceNext, i => E.traceNext i
  | .challenge, i => E.chal i
  | .publicVal, i => E.pub i

/-- `E` matches `σ`. -/
def Matches {K : Type*} [Field K] (σ : Valuation) (E : Env K) : Prop :=
  ∀ k i v, σ k i = some v → varVal E k i = (v : K)

theorem specSel_eval {K : Type*} [Field K] (σ : Valuation) (E : Env K) (h : Matches σ E)
    (e : Expr) : (specSel σ e).eval E = e.eval E := by
  unfold specSel
  rw [Expr.eval_subst]
  congr 1
  have hv : ∀ k i, (match σ k i with | some v => Expr.Const v | none => Expr.Var k i).eval E =
      varVal E k i := by
    intro k i
    cases hσ : σ k i with
    | none => cases k <;> rfl
    | some v => simp [Expr.eval, h k i v hσ]
  cases E
  simp only [Env.ofSubst, Env.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i
  · exact hv .traceCur i
  · exact hv .traceNext i
  · exact hv .challenge i
  · exact hv .publicVal i

/-! ## 2. Constant folding -/

def mkAdd : Expr → Expr → Expr
  | .Const x, .Const y => .Const (x + y)
  | .Const 0, b => b
  | a, .Const 0 => a
  | a, b => .Add a b

def mkSub : Expr → Expr → Expr
  | .Const x, .Const y => .Const (x - y)
  | a, .Const 0 => a
  | a, b => .Sub a b

def mkMul : Expr → Expr → Expr
  | .Const 0, _ => .Const 0
  | _, .Const 0 => .Const 0
  | .Const x, .Const y => .Const (x * y)
  | a, b => .Mul a b

def mkNeg : Expr → Expr
  | .Const x => .Const (-x)
  | a => .Neg a

def mkPow : Expr → ℕ → Expr
  | .Const x, n => .Const (x ^ n)
  | a, n => .Pow a n

def simp0 : Expr → Expr
  | .Add a b => mkAdd (simp0 a) (simp0 b)
  | .Sub a b => mkSub (simp0 a) (simp0 b)
  | .Mul a b => mkMul (simp0 a) (simp0 b)
  | .Neg a => mkNeg (simp0 a)
  | .Pow a n => mkPow (simp0 a) n
  | e => e

section Fold
variable {K : Type*} [Field K] (E : Env K)

theorem mkAdd_eval (a b : Expr) : (mkAdd a b).eval E = a.eval E + b.eval E := by
  unfold mkAdd; split <;> simp_all [Expr.eval]

theorem mkSub_eval (a b : Expr) : (mkSub a b).eval E = a.eval E - b.eval E := by
  unfold mkSub; split <;> simp_all [Expr.eval]

theorem mkMul_eval (a b : Expr) : (mkMul a b).eval E = a.eval E * b.eval E := by
  unfold mkMul; split <;> simp_all [Expr.eval]

theorem mkNeg_eval (a : Expr) : (mkNeg a).eval E = -a.eval E := by
  unfold mkNeg; split <;> simp_all [Expr.eval]

theorem mkPow_eval (a : Expr) (n : ℕ) : (mkPow a n).eval E = (a.eval E) ^ n := by
  unfold mkPow; split <;> simp_all [Expr.eval]

theorem simp0_eval : ∀ e : Expr, (simp0 e).eval E = e.eval E
  | .Add a b => by simp [simp0, mkAdd_eval, Expr.eval, simp0_eval a, simp0_eval b]
  | .Sub a b => by simp [simp0, mkSub_eval, Expr.eval, simp0_eval a, simp0_eval b]
  | .Mul a b => by simp [simp0, mkMul_eval, Expr.eval, simp0_eval a, simp0_eval b]
  | .Neg a => by simp [simp0, mkNeg_eval, Expr.eval, simp0_eval a]
  | .Pow a n => by simp [simp0, mkPow_eval, Expr.eval, simp0_eval a]
  | .Var _ _ => rfl
  | .Const _ => rfl

end Fold

/-! ## 3. Reads and the congruence -/

def readsE : Expr → List (VarKind × ℕ)
  | .Var k j => [(k, j)]
  | .Const _ => []
  | .Add a b | .Sub a b | .Mul a b => readsE a ++ readsE b
  | .Neg a | .Pow a _ => readsE a

theorem eval_congr_reads {K : Type*} [Field K] {E₁ E₂ : Env K} :
    ∀ e : Expr, (∀ p ∈ readsE e, varVal E₁ p.1 p.2 = varVal E₂ p.1 p.2) → e.eval E₁ = e.eval E₂
  | .Var k j, h => by have := h (k, j) (by simp [readsE]); cases k <;> exact this
  | .Const _, _ => rfl
  | .Add a b, h => by
      simp only [readsE, List.mem_append] at h
      simp only [Expr.eval, eval_congr_reads a (fun p hp => h p (Or.inl hp)),
        eval_congr_reads b (fun p hp => h p (Or.inr hp))]
  | .Sub a b, h => by
      simp only [readsE, List.mem_append] at h
      simp only [Expr.eval, eval_congr_reads a (fun p hp => h p (Or.inl hp)),
        eval_congr_reads b (fun p hp => h p (Or.inr hp))]
  | .Mul a b, h => by
      simp only [readsE, List.mem_append] at h
      simp only [Expr.eval, eval_congr_reads a (fun p hp => h p (Or.inl hp)),
        eval_congr_reads b (fun p hp => h p (Or.inr hp))]
  | .Neg a, h => by simp only [Expr.eval, eval_congr_reads a h]
  | .Pow a _, h => by simp only [Expr.eval, eval_congr_reads a h]

/-- **The insensitivity check**: the folded, specialised source reads no variable in `D`. -/
def Insensitive (σ : Valuation) (D : VarKind → ℕ → Bool) (e : Expr) : Bool :=
  (readsE (simp0 (specSel σ e))).all fun p => !D p.1 p.2

/-- **Soundness of the check.** -/
theorem eval_eq_of_insensitive {K : Type*} [Field K] (σ : Valuation) (D : VarKind → ℕ → Bool)
    (e : Expr) (hins : Insensitive σ D e = true) {E₁ E₂ : Env K}
    (h₁ : Matches σ E₁) (h₂ : Matches σ E₂)
    (hagree : ∀ k i, D k i = false → varVal E₁ k i = varVal E₂ k i) :
    e.eval E₁ = e.eval E₂ := by
  rw [← specSel_eval σ E₁ h₁, ← specSel_eval σ E₂ h₂, ← simp0_eval E₁, ← simp0_eval E₂]
  apply eval_congr_reads
  intro p hp
  have := List.all_eq_true.mp hins p hp
  exact hagree p.1 p.2 (by simpa using this)

/-! ## 4. The valuations and difference sets used for the un-hosted trace -/

/-- State by selector column (`opCol`). -/
def stOfIdx : Fin 11 → State
  | 0 => .s0 | 1 => .s1 | 2 => .s2 | 3 => .s3 | 4 => .s4 | 5 => .s5 | 6 => .s6 | 7 => .s7
  | 8 => .s8 | 9 => .s9 | 10 => .cons

theorem opCol_stOfIdx (s : Fin 11) : Nock.Reified.opCol (stOfIdx s) = s := by
  fin_cases s <;> rfl

/-- The current-row selectors one-hot at state index `s`. -/
def curSel (s : Fin 11) : Valuation
  | .traceCur, j => if j < 11 then some (if j = (s : ℕ) then 1 else 0) else none
  | _, _ => none

/-- The two host `𝕂`-roles of a state (walk `count`/`acc` in the deployed encoding). -/
def hostRolesOf (st : State) : List ℕ := [3 * overlayANat st, 3 * overlayANat st + 1]

/-- The eight former walk-host `𝕂`-roles. -/
def hostKRoles : List ℕ := [6, 7, 9, 10, 18, 19, 27, 28]

/-- Residual roles `58`/`59` (source indices `71`/`72`). -/
def residualRoles : List ℕ := [58, 59]

/-- **The difference set at a row of state `s`** (source indices): current host roles of `s`, all
eight host roles on the successor row (covering the terminal row), the residual roles on both
rows, and the walk columns. -/
def diffAt (s : Fin 11) : VarKind → ℕ → Bool
  | .traceCur, j => decide (13 ≤ j ∧ j < 76 ∧ (j - 13 ∈ hostRolesOf (stOfIdx s) ∨
      j - 13 ∈ residualRoles)) || decide (303 ≤ j)
  | .traceNext, j => decide (13 ≤ j ∧ j < 76 ∧ (j - 13 ∈ hostKRoles ∨ j - 13 ∈ residualRoles))
      || decide (303 ≤ j)
  | _, _ => false

/-- The deployed core source at a position. -/
def coreSrc (i : Fin 82) : Expr := finalExtTransitionGates.get ⟨i, by simp⟩

/-- **Receipt: every untouched core source is host-insensitive at every state.**  The 78 core
positions other than `74..77` read the former host cells only under a selector that vanishes
on a row of the hosting state. -/
theorem untouched_core_insensitive :
    ∀ s : Fin 11, ∀ i : Fin 82, i.val ≠ 74 → i.val ≠ 75 → i.val ≠ 76 → i.val ≠ 77 →
      Insensitive (curSel s) (diffAt s) (coreSrc i) = true := by
  decide +kernel

/-- **Control: the four walk positions are host-sensitive at every state** — the un-hosting
touches exactly `walkCountStep`, `walkAccStep`, `walkQueueNonEmpty`, `walkQueueTiling`. -/
theorem retargeted_core_sensitive :
    ((List.finRange 82).filter fun i =>
      (List.finRange 11).any fun s => !Insensitive (curSel s) (diffAt s) (coreSrc i)).map
        Fin.val = [74, 75, 76, 77] := by
  decide +kernel

/-! ## 5. Further valuations and receipts used by the canonical transfer -/

/-- The empty valuation. -/
def noSel : Valuation := fun _ _ => none

/-- The successor-row selectors one-hot at state index `s`. -/
def nextSel (s : Fin 11) : Valuation
  | .traceNext, j => if j < 11 then some (if j = (s : ℕ) then 1 else 0) else none
  | _, _ => none

/-- First-row valuation: the current selectors and the public initial-state masks
(`initialMask`, publics `20..30`), both one-hot at `s`. -/
def firstSel (s : Fin 11) : Valuation
  | .traceCur, j => if j < 11 then some (if j = (s : ℕ) then 1 else 0) else none
  | .publicVal, j => if 20 ≤ j ∧ j < 31 then some (if j = 20 + (s : ℕ) then 1 else 0) else none
  | _, _ => none

/-- Difference set at a nonterminal row whose successor has state index `s'`: every host role on
the current row, the host roles of `s'` on the successor row, the residual roles, the walk
columns. -/
def diffNext (s' : Fin 11) : VarKind → ℕ → Bool
  | .traceCur, j => decide (13 ≤ j ∧ j < 76 ∧ (j - 13 ∈ hostKRoles ∨ j - 13 ∈ residualRoles))
      || decide (303 ≤ j)
  | .traceNext, j => decide (13 ≤ j ∧ j < 76 ∧ (j - 13 ∈ hostRolesOf (stOfIdx s') ∨
      j - 13 ∈ residualRoles)) || decide (303 ≤ j)
  | _, _ => false

/-- **Receipt**: the successor-row in-gate label, child sum and count multiplier read the host
cells only under a successor selector that vanishes on the hosting state. -/
theorem next_labels_insensitive :
    ∀ s' : Fin 11,
      Insensitive (nextSel s') (diffNext s') (ComputeWalkLabel.labelRLC ComputeWalkLabel.nextReader) = true ∧
      Insensitive (nextSel s') (diffNext s')
        (ComputeWalkLabel.childSumCC ComputeWalkLabel.nextReader) = true ∧
      Insensitive noSel (diffNext s') (ComputeWalkLabel.selectorCM ComputeWalkLabel.nextReader) = true := by
  decide +kernel

/-- **Receipt**: the first-row in-gate label, child sum and count multiplier (public masks). -/
theorem first_labels_insensitive :
    ∀ s : Fin 11,
      Insensitive (firstSel s) (diffAt s) (ComputeWalkLabel.labelRLC ComputeWalkLabel.firstReader) = true ∧
      Insensitive (firstSel s) (diffAt s)
        (ComputeWalkLabel.childSumCC ComputeWalkLabel.firstReader) = true ∧
      Insensitive noSel (diffAt s) (ComputeWalkLabel.selectorCM ComputeWalkLabel.firstReader) = true := by
  decide +kernel

/-- **Receipt**: the untouched endpoint and anchored-step sources. -/
theorem untouched_endpoint_insensitive :
    ∀ s : Fin 11, ∀ e ∈ [finalAccAfterStep, OptimizedComputeFinalTypedLowering.finalMaskedWalkLn1,
        finalAccInit, finalAccTerminal, finalLnInit],
      Insensitive (curSel s) (diffAt s) e = true := by
  decide +kernel

/-- **Receipt**: the line, walk-inverse and last-mask reads of the queue gates. -/
theorem queue_reads_insensitive :
    ∀ s : Fin 11, ∀ e ∈ [finalWalkLine .traceCur, walkInv .traceCur, Expr.Var .traceCur 12,
        Expr.Var .traceCur 11, finalWalkLine .traceNext],
      Insensitive noSel (diffAt s) e = true := by
  decide +kernel

end Unhosted309
end Nock.NockVMROM.Thm54
