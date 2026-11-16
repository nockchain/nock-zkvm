/-
  Nock/RedTeam/Batch608Thm54PreseedGateBodiesReview.lean

  Notes only; not a pass.

  * Gate bodies, symbol by symbol (`haltSel = bcur 1`, `atomCol = 180`,
    `haltAtomMixed = Scale (bcur 1) (Sub (Var traceCur 2) (Lift (bcur 180)))`, coordinate `k` on
    physical `12 + k`).
  * `bcur 1` is the `halt` selector on BOTH sides: honest codec `stateIndex.halt = 1`
    (`OptimizedMemoryCodec.stateSelector`), hostile decode `memoryStateOf =.halt → trace 1 = 1`,
    and the paper `𝕂` gates' own `selScale` uses `bcur 1` for `f.halt`.
  * Role `2` is `pt.noun.leaf`: `memoryPtNoun` is `⟨trace 0, trace 1, trace 2⟩` and `FP` is
    `(size, dyck, leaf)`; honest `enc z (atom k) = (z, 0, k)`.
  * Deployed: the gate holds on every row of every trace accepted at `P.memoryChipAt c`.
  * Round (check 2): `Batch601.atom_column_in_round_zero` is round-BLIND — the same statement
    holds for every column `< 181`, including the `pt.noun.size` columns `6..8` that hold the seed
    `z` on honest `halt` rows; `Batch580.memoryPaperRound` puts column `180` in round `1`, not `0`
    (the draft letter cites that table for round `0`).
-/
import Nock.RedTeam.Batch601Thm54PreseedAtomMemoryGate
import Nock.RedTeam.Batch580Thm54PreseedChronology
import Nock.RedTeam.Batch578Thm54AdaptiveAtomForgery
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch608

open Nock
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP

noncomputable section

/-! ## Check 1 — gate bodies, symbol by symbol -/

section Bodies

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem atomCol_is_180 : atomCol = 180 := rfl

theorem haltSel_is_base_col_one :
    haltSel (F := F) = CoordinateCompiler.CoeffExpr.var .traceCur 1 := rfl

theorem haltAtomMixed_body :
    haltAtomMixed (F := F) =
      .Scale (CoordinateCompiler.CoeffExpr.var .traceCur 1)
        (.Sub (.Var .traceCur 2) (.Lift (CoordinateCompiler.CoeffExpr.var .traceCur 180))) := rfl

/-- `K`-role `2` sits on physical columns `12, 13, 14` of the deployed layout. -/
theorem role_two_physical (k : ℕ) : memoryCol0 .traceCur 2 + k = 12 + k := rfl

/-- The paper's own selector-summed `𝕂` gates scale the `halt` block by the same `bcur 1`. -/
theorem selScale_halt_selector (f : MemoryTable.MState → Expr) :
    selScale (F := F) f =
      .Add (.Scale (bcur 0) (MixedExpr.ofExpr (f .decompose)))
        (.Add (.Scale (bcur 1) (MixedExpr.ofExpr (f .halt)))
          (.Add (.Scale (bcur 2) (MixedExpr.ofExpr (f .read_root)))
            (.Scale (bcur 3) (MixedExpr.ofExpr (f .verify_child))))) := rfl

end Bodies

/-- Honest codec: base column `1` is `1` exactly on `halt` rows. -/
theorem honest_selector_one_iff_halt {F : Type} [Field F] [DecidableEq F] (s : MemoryTable.MState) :
    OptimizedMemoryCodec.stateSelector (F := F) s 1 =
      if s = MemoryTable.MState.halt then 1 else 0 := by
  cases s <;> simp [OptimizedMemoryCodec.stateSelector, OptimizedMemoryCodec.stateIndex]

/-- Hostile decode: a row decoded as `halt` has base column `1` equal to `1`. -/
theorem decoded_halt_selector {F : Type} [Field F] [DecidableEq F] (env : Env F)
    (h : StrategyOfTraces.memoryStateOf env = MemoryTable.MState.halt) : env.trace 1 = 1 := by
  unfold StrategyOfTraces.memoryStateOf at h
  split_ifs at h with h0 h1 <;> first | exact h1 | cases h

/-- Hostile decode: a row whose base column `1` is not `1` is never decoded as `halt`
(the "selector zero" forgery is a non-`halt` row). -/
theorem selector_ne_one_not_halt {F : Type} [Field F] [DecidableEq F] (env : Env F)
    (h : env.trace 1 ≠ 1) :
    StrategyOfTraces.memoryStateOf env ≠ MemoryTable.MState.halt := fun hh => h (decoded_halt_selector env hh)

/-- Role `2` is the leaf: `memoryPtNoun` reads `𝕂` columns `0, 1, 2` as `(size, dyck, leaf)`. -/
theorem ptNoun_leaf_is_role_two {K : Type} [Field K] (eK : Env K) :
    (StrategyOfTraces.memoryPtNoun eK).leaf = eK.trace 2 ∧
      (StrategyOfTraces.memoryPtNoun eK).size = eK.trace 0 ∧
      (StrategyOfTraces.memoryPtNoun eK).dyck = eK.trace 1 := ⟨rfl, rfl, rfl⟩

/-- Honest `halt` noun: `enc z (atom k) = (z, 0, k)`, so leaf `= k` and size `= z`. -/
theorem honest_atom_fp {K : Type} [Field K] (z : K) (k : ℕ) :
    (GlobalCarryRecognizer.enc z (Noun.atom k)).leaf = (k : K) ∧
      (GlobalCarryRecognizer.enc z (Noun.atom k)).size = z ∧
      (GlobalCarryRecognizer.enc z (Noun.atom k)).dyck = 0 := by
  rw [GlobalCarryRecognizer.enc_atom]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Check 1 — the gate is in the deployed `memoryChipAt c` -/

section Deployed

open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- On every trace accepted at the deployed `P.memoryChipAt c`, every row satisfies
`bcur 1 · (role-2 leaf − algebraMap (col 180)) = 0`. -/
theorem deployed_gate_holds
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → Polynomial F)
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    algebraMap F K ((memoryBaseEnvAt P c (honestQm P c Qm) i).trace 1) *
        ((memorySourceEnvAt P c (honestQm P c Qm) i).trace 2 -
          algebraMap F K ((memoryBaseEnvAt P c (honestQm P c Qm) i).trace 180)) = 0 := by
  have hgate := mixed_at_family P c Qm hsat i haltAtomMixed
    (MemoryHaltAtomDecode.haltAtomMixed_mem (F := F) (K := K) P.optimized.basis)
  rwa [haltAtomMixed_eval] at hgate

/-- The deployed chip's width is `204` at every challenge tuple. -/
theorem deployed_width (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F) : (P.memoryChipAt c).rap.w = 205 :=
  (finalMemoryRAP_fingerprint _ _ _ _ _ _ _).1

end Deployed

/-! ## Check 2 — the round statement is column-blind -/

section Round

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **`atom_column_in_round_zero`'s shape holds for EVERY source column.**  The memory source
chip has `k = 1`, so `wRAP 0` is the whole source width and every column `j < 181` is "round 0" —
including the `pt.noun.size` columns `6, 7, 8`, which carry the seed `z` on every honest `halt`
row (`honest_atom_fp`), and the walk / IO accumulator columns that read `α, γ, λ`.  The statement
therefore cannot separate a pre-`z` column from a post-`z` one. -/
theorem every_source_column_is_round_zero {h : ℕ} (b : Module.Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h) (H : Finset F)
    (j : ℕ) (hj : j < 182) :
    (sourceMemoryRAP b chalVal pubVal orbit H).k = 1 ∧
      j < (sourceMemoryRAP b chalVal pubVal orbit H).wRAP
        ⟨0, (memorySourceTemplate b).rounds_pos⟩ := by
  obtain ⟨hk, hw, -, -⟩ := Batch601.atom_column_in_round_zero b chalVal pubVal orbit H
  exact ⟨hk, hw ▸ hj⟩

/-- In particular the `size` columns (honest value `z` on `halt` rows) pass the same test. -/
theorem seed_valued_size_columns_round_zero {h : ℕ} (b : Module.Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h) (H : Finset F) :
    ∀ k : Fin 3, memoryCol0 .traceCur 0 + (k : ℕ) <
      (sourceMemoryRAP b chalVal pubVal orbit H).wRAP ⟨0, (memorySourceTemplate b).rounds_pos⟩ :=
  fun k => (every_source_column_is_round_zero b chalVal pubVal orbit H _
    (by have := k.isLt; simp only [memoryCol0]; omega)).2

end Round

/-- Satisfaction ignores `k` / `wRAP` (OX's `Batch578.rap_satisfies_ignores_rounds`): no
soundness statement about the chip can see a round assignment. -/
theorem satisfaction_round_blind {F : Type} [Field F] [DecidableEq F]
    (R : RAP F) (k' : ℕ) (w' : Fin k' → ℕ) (hw : R.w = ∑ i, w' i) (P : Fin R.w → Polynomial F) :
    R.Satisfies P ↔ ({R with k := k', wRAP := w', w_eq := hw} : RAP F).Satisfies P :=
  Batch578.rap_satisfies_ignores_rounds R k' w' hw P

/-- That table
(`Batch580.memoryPaperRound`, still typed `Fin 200`) puts column `180` in round `1` (the
post-`z` extension payload); only columns `< 13` are round `0`. -/
theorem memoryPaperRound_atom_col_is_one :
    Batch580.memoryPaperRound ⟨180, by decide⟩ = 1 := by
  simp [Batch580.memoryPaperRound]

end

end Nock.RedTeam.Batch608

#print axioms Nock.RedTeam.Batch608.haltAtomMixed_body
#print axioms Nock.RedTeam.Batch608.honest_selector_one_iff_halt
#print axioms Nock.RedTeam.Batch608.decoded_halt_selector
#print axioms Nock.RedTeam.Batch608.honest_atom_fp
#print axioms Nock.RedTeam.Batch608.deployed_gate_holds
#print axioms Nock.RedTeam.Batch608.deployed_width
#print axioms Nock.RedTeam.Batch608.every_source_column_is_round_zero
#print axioms Nock.RedTeam.Batch608.seed_valued_size_columns_round_zero
#print axioms Nock.RedTeam.Batch608.memoryPaperRound_atom_col_is_one
