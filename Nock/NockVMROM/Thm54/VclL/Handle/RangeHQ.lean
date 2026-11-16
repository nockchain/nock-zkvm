/-
  Nock/NockVMROM/Thm54/VclL/Handle/RangeHQ.lean

  Additive.

  Every column / role a gate reads lies inside the chip:

  * **cell twin** (`cellTemplateHQ`, width `130 + 36·3 = 238`): every base gate reads base columns
    `< 130`, every mixed gate reads `𝕂`-roles `< 36` and base columns `< 130` (`cellHQ_range`);
  * **walk twin** (`walkTemplateHQ`, width `25 + 47·3 = 166`): base `< 25`, roles `< 47`
    (`walkHQ_range`), for every `kroots`;
  * **compute twin** (`computeChipVCLHQ`, width `85`, `𝕂`-variables at three consecutive columns,
    `col0Id`): on the gate TEMPLATES at `F = ℚ`, `δ = 7` (kernel `decide`), every base column read is
    `< 85`, every `𝕂`-variable `i` has `i + 2 < 85` (`computeHQ_range`), and every challenge / public
    limb read is below the vector lengths `18 / 27` of `chalVHQ` / `pubVHQ` (`computeHQ_coins_range`).
    The chip's gates are these templates mapped to `F` (`mapC` / `mapM`, column-preserving) and compiled
    by `mixedCompile b col0Id` (`𝕂`-variable `i` ↦ columns `i.. i+2`).
  * **positive controls**: the replica of the old cell gate (role `36`) fails `mixBelow 36 130`
    (`cell_old_gate_flagged`); a `𝕂′` slot read at `𝕂`-variable `83` fails the compute check
    (`compute_range_flags`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.MemHQ
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

/-! ## 1. Monotonicity of the instruments -/

section Mono
variable {F : Type} [Field F]

theorem colsBelow_mono {B B' : ℕ} (hB : B ≤ B') : ∀ g : CoeffExpr F, colsBelow B g = true →
    colsBelow B' g = true
  | .const _, _ => rfl
  | .var .traceCur i, h => by simp [colsBelow] at h ⊢; omega
  | .var .traceNext i, h => by simp [colsBelow] at h ⊢; omega
  | .var .challenge _, h => h
  | .var .publicVal _, h => h
  | .add a b, h => by
      simp only [colsBelow, Bool.and_eq_true] at h ⊢
      exact ⟨colsBelow_mono hB a h.1, colsBelow_mono hB b h.2⟩
  | .sub a b, h => by
      simp only [colsBelow, Bool.and_eq_true] at h ⊢
      exact ⟨colsBelow_mono hB a h.1, colsBelow_mono hB b h.2⟩
  | .mul a b, h => by
      simp only [colsBelow, Bool.and_eq_true] at h ⊢
      exact ⟨colsBelow_mono hB a h.1, colsBelow_mono hB b h.2⟩
  | .neg a, h => by simp only [colsBelow] at h ⊢; exact colsBelow_mono hB a h
  | .pow a _, h => by simp only [colsBelow] at h ⊢; exact colsBelow_mono hB a h

theorem mixBelow_mono {R R' B B' : ℕ} (hR : R ≤ R') (hB : B ≤ B') : ∀ g : MixedExpr F,
    mixBelow R B g = true → mixBelow R' B' g = true
  | .Var .traceCur i, h => by simp [mixBelow] at h ⊢; omega
  | .Var .traceNext i, h => by simp [mixBelow] at h ⊢; omega
  | .Var .challenge _, h => h
  | .Var .publicVal _, h => h
  | .Lift g, h => colsBelow_mono hB g h
  | .Scale g u, h => by
      simp only [mixBelow, Bool.and_eq_true] at h ⊢
      exact ⟨colsBelow_mono hB g h.1, mixBelow_mono hR hB u h.2⟩
  | .Const _, h => h
  | .Add x y, h => by
      simp only [mixBelow, Bool.and_eq_true] at h ⊢
      exact ⟨mixBelow_mono hR hB x h.1, mixBelow_mono hR hB y h.2⟩
  | .Sub x y, h => by
      simp only [mixBelow, Bool.and_eq_true] at h ⊢
      exact ⟨mixBelow_mono hR hB x h.1, mixBelow_mono hR hB y h.2⟩
  | .Neg x, h => by simp only [mixBelow] at h ⊢; exact mixBelow_mono hR hB x h
  | .Mul x y, h => by
      simp only [mixBelow, Bool.and_eq_true] at h ⊢
      exact ⟨mixBelow_mono hR hB x h.1, mixBelow_mono hR hB y h.2⟩
  | .Pow x _, h => by simp only [mixBelow] at h ⊢; exact mixBelow_mono hR hB x h

end Mono

/-! ## 2. The memory twins -/

section Mem
variable {F : Type} [Field F]

theorem cellHQ_new_below (δF : F) : ∀ g ∈ CellHQ.gates δF, mixBelow 36 130 g = true := by
  have hall : (CellHQ.gates δF).all (mixBelow 36 130) = true := by
    simp [CellHQ.gates, CellHQ.gatesQ, CellHQ.invHQ, CellHQ.accHQ, CellHQ.pubHQ, HQ.denKeyQ, HQ.rlcQ,
      HQ.gpowQ, HQ.gamQ, HQ.rhoQ, CellH.keyH, CellH.valE, cv, nv, notE, QE.gates, QE.var, QE.next,
      QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, mixBelow, colsBelow,
      Cell.idx, Cell.wL, Cell.wR, Cell.idL, Cell.idR, Cell.aL, Cell.aR, Cell.isF, Cell.isL, CellH.mh]
  intro g hg
  exact List.all_eq_true.mp hall g hg

/-- **Cell twin range**: base reads `< 130`, `𝕂`-roles `< 36` (= `extCols`), so every read column is
`< 130 + 36·3 = 238`; no equality or extension-only gates. -/
theorem cellHQ_range (δF : F) :
    (∀ g ∈ (cellTemplateHQ δF).baseTransition, colsBelow (cellTemplateHQ δF).baseCols g = true) ∧
    (∀ g ∈ (cellTemplateHQ δF).mixedTransition,
      mixBelow (cellTemplateHQ δF).extCols (cellTemplateHQ δF).baseCols g = true) ∧
    (cellTemplateHQ δF).equalityChecks = [] ∧
    (cellTemplateHQ δF).extTransition ++ (cellTemplateHQ δF).extDeg1 ++ (cellTemplateHQ δF).extDeg3 = [] := by
  rw [cellTemplateHQ_baseCols, cellTemplateHQ_extCols]
  refine ⟨fun g hg => colsBelow_mono (by omega) g (cellBase_below g hg), fun g hg => ?_, rfl, rfl⟩
  rcases List.mem_append.mp hg with h | h
  · exact mixBelow_mono (by omega) (by omega) g (cellMixed_below δF g h)
  · exact cellHQ_new_below δF g h

theorem walkHQ_new_below (δF : F) : ∀ g ∈ WalkHQ.gates δF, mixBelow 47 25 g = true := by
  have hall : (WalkHQ.gates δF).all (mixBelow 47 25) = true := by
    simp [WalkHQ.gates, WalkHQ.gatesQ, WalkHQ.pTermQ, WalkHQ.hxInvQ, WalkHQ.hpInvLQ, WalkHQ.hpInvRQ,
      WalkHQ.hxAccQ, WalkHQ.hpAccQ, WalkHQ.pubXQ, WalkHQ.pubPQ, HQ.denKeyQ, HQ.rlcQ, HQ.gpowQ, HQ.gamQ,
      HQ.rhoQ, WalkHC.xKeyH, WalkHC.recLH, WalkHC.recRH, cv, nv, notE, QE.gates, QE.var, QE.next,
      QE.chal, QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, mixBelow, colsBelow,
      WChip.idx, WalkHC.kL, WalkHC.vL, WalkHC.kR, WalkHC.vR, WChip.ridx, WChip.pre, WChip.isF,
      WChip.isL, WChip.mL, WChip.mR]
  intro g hg
  exact List.all_eq_true.mp hall g hg

theorem walkHC_baseH_below : ∀ g ∈ (WalkHC.baseH : List (CoeffExpr F)), colsBelow 25 g = true := by
  intro g hg
  simp only [WalkHC.baseH, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp [colsBelow, WalkHC.kL, WalkHC.kR]

/-- **Walk twin range** (every `kroots`): base reads `< 25`, `𝕂`-roles `< 47`, so every read column is
`< 25 + 47·3 = 166`. -/
theorem walkHQ_range (δF : F) (kroots : ℕ) :
    (∀ g ∈ (walkTemplateHQ δF kroots).baseTransition,
      colsBelow (walkTemplateHQ δF kroots).baseCols g = true) ∧
    (∀ g ∈ (walkTemplateHQ δF kroots).mixedTransition,
      mixBelow (walkTemplateHQ δF kroots).extCols (walkTemplateHQ δF kroots).baseCols g = true) ∧
    (walkTemplateHQ δF kroots).equalityChecks = [] ∧
    (walkTemplateHQ δF kroots).extTransition ++ (walkTemplateHQ δF kroots).extDeg1 ++
      (walkTemplateHQ δF kroots).extDeg3 = [] := by
  rw [walkTemplateHQ_baseCols, walkTemplateHQ_extCols]
  refine ⟨fun g hg => ?_, fun g hg => ?_, rfl, rfl⟩
  · rcases List.mem_append.mp hg with h | h
    · exact colsBelow_mono (by omega) g (walkBase_below kroots g h)
    · exact walkHC_baseH_below g h
  · rcases List.mem_append.mp hg with h | h
    · exact mixBelow_mono (by omega) (by omega) g (walkMixed_below δF kroots g h)
    · exact walkHQ_new_below δF g h

theorem cell_old_gate_flagged (δF : F) :
    mixBelow 36 130 (QE.sub (QE.mul δF (QE.var 36) (HQ.denKeyQ δF CellH.keyH)) QE.one).re = false := by
  simp [QE.sub, QE.mul, QE.var, QE.one, mixBelow]

end Mem

/-! ## 3. The compute twin (templates at `F = ℚ`, `δ = 7`) -/

section Compute

/-- Indices of the leaves of kind `k` in a base expression. -/
def bReads (k : VarKind) : CoeffExpr ℚ → List ℕ
  | .const _ => []
  | .var k' i => if k' = k then [i] else []
  | .add a b => bReads k a ++ bReads k b
  | .sub a b => bReads k a ++ bReads k b
  | .mul a b => bReads k a ++ bReads k b
  | .neg a => bReads k a
  | .pow a _ => bReads k a

/-- Indices of the `𝕂`-leaves of kind `k` in a mixed expression (`𝕂`-variable `i` = columns
`i.. i+2` under `col0Id`). -/
def kReads (k : VarKind) : MixedExpr ℚ → List ℕ
  | .Var k' i => if k' = k then [i] else []
  | .Lift _ => []
  | .Scale _ u => kReads k u
  | .Const _ => []
  | .Add x y => kReads k x ++ kReads k y
  | .Sub x y => kReads k x ++ kReads k y
  | .Neg x => kReads k x
  | .Mul x y => kReads k x ++ kReads k y
  | .Pow x _ => kReads k x

/-- Indices of the base leaves of kind `k` under the `Lift` / `Scale` leaves of a mixed expression. -/
def lReads (k : VarKind) : MixedExpr ℚ → List ℕ
  | .Var _ _ => []
  | .Lift g => bReads k g
  | .Scale g u => bReads k g ++ lReads k u
  | .Const _ => []
  | .Add x y => lReads k x ++ lReads k y
  | .Sub x y => lReads k x ++ lReads k y
  | .Neg x => lReads k x
  | .Mul x y => lReads k x ++ lReads k y
  | .Pow x _ => lReads k x

/-- A mixed template expression is inside a chip of width `w` with challenge / public vectors of
lengths `nc / np`. -/
def mixIn (w nc np : ℕ) (g : MixedExpr ℚ) : Bool :=
  (kReads .traceCur g ++ kReads .traceNext g).all (fun i => decide (i + 2 < w)) &&
  (lReads .traceCur g ++ lReads .traceNext g).all (fun i => decide (i < w)) &&
  (kReads .challenge g).all (fun i => decide (i + 2 < nc)) &&
  (lReads .challenge g).all (fun i => decide (i < nc)) &&
  (kReads .publicVal g).all (fun i => decide (i + 2 < np)) &&
  (lReads .publicVal g).all (fun i => decide (i < np))

def baseIn (w nc np : ℕ) (g : CoeffExpr ℚ) : Bool :=
  (bReads .traceCur g ++ bReads .traceNext g).all (fun i => decide (i < w)) &&
  (bReads .challenge g).all (fun i => decide (i < nc)) &&
  (bReads .publicVal g).all (fun i => decide (i < np))

/-- **Compute twin range** (templates): base gates, the `𝕂′` slot pairs (both halves) and the walk gates
read columns `< 85`, challenge limbs `< 18`, public limbs `< 27`. -/
theorem computeHQ_range :
    ((ChipHQ.baseGatesHQ (F := ℚ)).all (baseIn ChipHQ.widthHQ 18 27) &&
      (ChipHQ.slotPairs (F := ℚ) 7).all (fun q => mixIn ChipHQ.widthHQ 18 27 q.1 && mixIn ChipHQ.widthHQ 18 27 q.2) &&
      (ChipH.walkGates (F := ℚ)).all (mixIn ChipHQ.widthHQ 18 27)) = true := by
  decide +kernel

/-- **Positive control**: a `𝕂′` slot read at `𝕂`-variable `83` (columns `83..85`) is flagged. -/
theorem compute_range_flags :
    mixIn ChipHQ.widthHQ 18 27 (MixedExpr.Mul (.Var .traceCur 83) (.Const 1)) = false := by
  decide +kernel

end Compute

end Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
