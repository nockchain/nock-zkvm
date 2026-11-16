/-
  Nock/NockVMROM/Thm54/VclL/Handle/FrameJ8.lean

  **The frame `frameJ8` and the summand list.**

  * `frameJ8` (SPEC §5.1, O1 "coins shared by class"): `frameVSQ`'s seventeen coins verbatim, then the
    limb coin `y = y₁ + y₂√δ` (`18 / 19`, two `𝕂`-coins sampled after round 0, the stage of `z`).  No
    β.  No new coin pair for any new balance: the atom table's external provide is the cell validity
    balance (`γ′ρ′`), the service balance is handle-class (`γH′ρH′`), the atom walk's labels use
    `αW γW` at `y`, the atom table's internal validity / export balances use `γ′ρ′` / `γH′ρH′`
    (`classJ8`, a total map from summands to coin indices, checked to land inside `frameJ8`).
  * `SummandJ8` / `weightJ8` (SPEC §5.2): the ten summands with their weights as rationals in the
    row counts, `|𝕂|` and `|𝕂′|`.  `boundJ8` = their sum.  No figure is claimed here.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

/-! ## 1. The frame -/

/-- **`frameJ8`**: `frameVSQ`'s 17 coins, then `y₁ y₂` (the limb coin), sampled after round 0. -/
def frameJ8 : CoinFrame where
  n := 19
  sampledAfter := fun i => ![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] i

def cY1 : Fin frameJ8.n := ⟨17, by decide⟩
def cY2 : Fin frameJ8.n := ⟨18, by decide⟩

theorem lt_frameJ8 (i : Fin frameVSQ.n) : (i : ℕ) < frameJ8.n := by
  have := i.isLt; change (i : ℕ) < 17 at this; change (i : ℕ) < 19; omega

/-- The first seventeen coins. -/
def toVSQ {K : Type} (χ : Coins frameJ8 K) : Coins frameVSQ K := fun i => χ ⟨i, lt_frameJ8 i⟩

/-- `frameVSQ`'s round map is `frameJ8`'s on the first seventeen coins (summand #1 lifts). -/
theorem toVSQ_sampled (i : Fin frameVSQ.n) :
    frameVSQ.sampledAfter i = frameJ8.sampledAfter ⟨i, lt_frameJ8 i⟩ := by
  fin_cases i <;> rfl

/-- `y` is sampled after round 0, with `z = (χ₂, χ₃)`. -/
theorem frameJ8_y_round0 :
    frameJ8.sampledAfter cY1 = 0 ∧ frameJ8.sampledAfter cY2 = 0 ∧
      frameJ8.sampledAfter ⟨2, by decide⟩ = 0 ∧ frameJ8.sampledAfter ⟨3, by decide⟩ = 0 := by decide

/-- `frameJ8` adds exactly two coins and no round. -/
theorem frameJ8_n : frameJ8.n = frameVSQ.n + 2 := rfl

/-! ## 2. Summands, coin classes, weights -/

inductive SummandJ8
  | fortieth          -- #1 all `sumCVSQ`/`sumMVSQ`/`jointVSQ`, lifted through `toVSQ`
  | cellValidity2     -- #2 cell validity IO with two providers
  | atomValidity      -- #3 atom-table validity IO (internal, at `y`)
  | atomExport        -- #4 atom-table export IO (incl. the separate old-export accumulator)
  | cellExport3       -- #5 cell export IO with the third consumer (J `rd` rows)
  | service           -- #6 the tagged service balance (3 providers)
  | jInChip           -- #7 J in-chip IO (registry + node values)
  | atomCensus        -- #8 atom-table T1/T2 census + Dyck-root events at `y`
  | atomWalk          -- #9 the second `walkEvent` (atom walk, labels at `y`)
  | bivariateCensus
  deriving DecidableEq, Fintype

/-- **O1, coins shared by class**: the coin indices each summand's event reads.  `γ′ρ′` =
`4,5,6,7`; `γH′ρH′` = `11,12,15,16`; `αW γW` = `13,14`; `z` = `2,3`; `y` = `17,18`. -/
def classJ8 : SummandJ8 → List ℕ
  | .fortieth => List.range 17
  | .cellValidity2 => [4, 5, 6, 7]
  | .atomValidity => [4, 5, 6, 7, 17, 18]
  | .atomExport => [11, 12, 15, 16, 17, 18]
  | .cellExport3 => [11, 12, 15, 16]
  | .service => [11, 12, 15, 16]
  | .jInChip => [11, 12, 15, 16]
  | .atomCensus => [17, 18]
  | .atomWalk => [13, 14, 17, 18]
  | .bivariateCensus => [2, 3, 17, 18]

/-- Every class lands inside `frameJ8`, and no summand reads a coin outside `frameVSQ ++ [y₁, y₂]`. -/
theorem classJ8_in_frame : ∀ s : SummandJ8, ∀ i ∈ classJ8 s, i < frameJ8.n := by
  intro s i hi; cases s <;> simp [classJ8] at hi <;> (show i < 19; omega)

/-- The new summands read no coin beyond `y`: everything outside `{17, 18}` is a `frameVSQ` coin. -/
theorem classJ8_new_coins_only_y :
    ∀ s : SummandJ8, ∀ i ∈ classJ8 s, i < 17 ∨ i = 17 ∨ i = 18 := by
  intro s i hi; cases s <;> simp [classJ8] at hi <;> omega

/-- Row counts entering the J-8 weights. -/
structure RowsJ8 where
  N : ℕ        -- compute rows
  D : ℕ        -- cell rows
  W : ℕ        -- cell-walk rows
  Λ : ℕ        -- leaf bound
  A : ℕ        -- atom rows
  AW : ℕ       -- atom-walk rows
  J : ℕ        -- J rows
  mb : ℕ       -- atom-root provides
  inc : ℕ      -- inc rows
  calls : ℕ    -- J call rows
  heads : ℕ    -- chain heads
  blocks : ℕ   -- atom-walk blocks
  rd : ℕ       -- J read rows
  leaves : ℕ
  maxlen : ℕ

/-- **SPEC §5.2's weights (U: shapes, not yet proved bounds)**, `c = |𝕂|`, `c′ = |𝕂′|`. -/
def weightJ8 (c c' : ℕ) (r : RowsJ8) : SummandJ8 → ℚ
  | .fortieth => boundVCLHQ'' c c' r.N r.D r.W r.Λ
  | .cellValidity2 => (ioFailureUnionBound 5 (r.D + r.mb) r.D c' : ℚ) / c ^ 4
  | .atomValidity => (ioFailureUnionBound 5 r.A r.A c' : ℚ) / c ^ 4
  | .atomExport => (ioFailureUnionBound 5 (r.A + r.inc + r.AW) r.A c' : ℚ) / c ^ 4
  | .cellExport3 => (ioFailureUnionBound 5 (3 * r.N + r.W + r.rd) r.D c' : ℚ) / c ^ 4
  | .service => (ioFailureUnionBound 8 (r.N + r.calls) (r.heads + r.AW + r.blocks) c' : ℚ) / c ^ 4
  | .jInChip => (ioFailureUnionBound 8 (3 * r.J) (3 * r.J) c' : ℚ) / c ^ 4
  | .atomCensus => ((r.A * (2 * fuelChip - 1) + 1 : ℕ) : ℚ) / c ^ 2
  | .atomWalk => ((15 * r.AW : ℕ) : ℚ) / c
  | .bivariateCensus => ((r.leaves + r.maxlen : ℕ) : ℚ) / c'

/-- **`boundJ8`**: the sum of the ten weights (U as a bound; a definition here). -/
def boundJ8 (c c' : ℕ) (r : RowsJ8) : ℚ := ∑ s : SummandJ8, weightJ8 c c' r s

theorem weightJ8_fortieth (c c' : ℕ) (r : RowsJ8) :
    weightJ8 c c' r .fortieth = boundVCLHQ'' c c' r.N r.D r.W r.Λ := rfl

/-- Ten summands. -/
theorem summandJ8_card : Fintype.card SummandJ8 = 10 := rfl

end Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
