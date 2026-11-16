/-
  Nock/RedTeam/Batch613Thm54PreseedAuditGate.lean

  Notes only; not a pass.  Imports production modules only.

  * Honest fill: on `op9HaltPub (encC z) a` the leaf is `algebraMap (a : F)`, so the gate body
    evaluates to `0` with `atom := honestAtomOf`; derived here from `enc_atom`, not from
    `GenMemAtomFill`'s lemma.
  * Also: `memoryStateOf =.halt` is the ONLY decode outcome on which the gate bites — on a row
    with base column `1 = 0` the gate is `0` for every leaf and every atom (the selector, not the
    decoder, is the gate's domain; a non-Boolean selector would be caught by the paper's
    Boolean gates, not by this one).
-/
import Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
import Nock.NockVMROM.Thm54.TraceGen.Op9Gen
import Nock.NockVMROM.Thm54.TraceGen.GenMemAtomFill
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch613

open Nock
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
open Nock.NockVMROM.Thm54.TraceGen
open Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open scoped Polynomial

noncomputable section

section Body
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Check 1(a): the body against raw constructors. -/
theorem body :
    haltAtomMixed (F := F) =
      MixedExpr.Scale (CoeffExpr.var .traceCur 1)
        (MixedExpr.Sub (MixedExpr.Var .traceCur 2)
          (MixedExpr.Lift (CoeffExpr.var .traceCur 180))) := rfl

/-- Check 1(b): the three compiled coordinate gates, against raw constructors
(`memoryCol0 _ 2 = 12`). -/
theorem coord_body (b : Module.Basis (Fin 3) F K) (k : Fin 3) :
    haltAtomGateCoord b k =
      CoeffExpr.mul (CoeffExpr.var .traceCur 1)
        (CoeffExpr.sub (CoeffExpr.var .traceCur (12 + (k : ℕ)))
          (CoeffExpr.mul (CoeffExpr.const (coord b (1 : K) k)) (CoeffExpr.var .traceCur 180))) := by
  simp only [haltAtomGateCoord, haltAtomMixed, haltSel, atomCol, bcur, mixedCompile, memoryCol0]

/-- Check 1(c): at a `FormRBasis` (`coord b 1 = (1,0,0)`) the three gates read
`sel·(leaf₀ − atom)`, `sel·leaf₁`, `sel·leaf₂` on physical columns `1, 12, 13, 14, 180`. -/
theorem coord_eval (b : Module.Basis (Fin 3) F K) (hb : OptimizedComputeFinalTrace.FormRBasis b)
    (env : Env F) :
    (haltAtomGateCoord b 0).eval env = env.trace 1 * (env.trace 12 - env.trace 180) ∧
      (haltAtomGateCoord b 1).eval env = env.trace 1 * env.trace 13 ∧
      (haltAtomGateCoord b 2).eval env = env.trace 1 * env.trace 14 := by
  obtain ⟨h0, h1, h2⟩ := hb
  refine ⟨?_, ?_, ?_⟩ <;> simp [coord_body, CoeffExpr.eval, h0, h1, h2]

/-- Check 1(d): deployed — the gate is the last element of the template's mixed list, after the
untouched `paperKGates`. -/
theorem deployed_last (b : Module.Basis (Fin 3) F K) :
    (memorySourceTemplate b).mixedTransition =
      paperKGates (F := F) (K := K) ++ [haltAtomMixed] := rfl

theorem deployed_length (b : Module.Basis (Fin 3) F K) :
    (memorySourceTemplate b).mixedTransition.length = 50 := by
  rw [deployed_last, List.length_append, paperKGates_length]; rfl

theorem deployed_mem (b : Module.Basis (Fin 3) F K) :
    haltAtomMixed (F := F) ∈ (memorySourceTemplate (K := K) b).mixedTransition := by
  rw [deployed_last]; simp

/-- The gate's domain is the selector column, not the decoder: with base column `1 = 0` it is
`0` whatever the leaf or the atom. -/
theorem off_halt_vacuous (eK : Env K) (eF : Env F) (h : eF.trace 1 = 0) :
    (haltAtomMixed (F := F)).eval eK eF = 0 := by
  rw [haltAtomMixed_eval, h, map_zero, zero_mul]

/-- With base column `1 = 1` the gate is exactly `leaf = algebraMap atom`. -/
theorem on_halt_iff (eK : Env K) (eF : Env F) (h : eF.trace 1 = 1) :
    (haltAtomMixed (F := F)).eval eK eF = 0 ↔ eK.trace 2 = algebraMap F K (eF.trace 180) := by
  rw [haltAtomMixed_eval, h, map_one, one_mul, sub_eq_zero]

end Body

/-! ## Check 3 — honest fill, derived from `enc_atom` -/
section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- A generated `halt` row's leaf is the lifted base atom (the paper: `enc z (atom a) =
(z, 0, a)`). -/
theorem gen_halt_leaf (z : K) (a : ℕ) :
    (op9HaltPub (encC z) a).pt.noun.leaf = algebraMap F K ((a : ℕ) : F) := by
  show (encC z (.atom a)).leaf = _
  rw [encC_eq, GlobalCarryRecognizer.enc_atom, map_natCast]
  rfl

/-- The honest atom column value is `(a : F)`, read off the leaf (no `z`, no `λ`). -/
theorem gen_honest_atom (z : K) (a : ℕ) :
    OptimizedMemoryCanonicalTrace.honestAtomOf (F := F) (K := K) (op9HaltPub (encC z) a) =
      ((a : ℕ) : F) := by
  have hex : (op9HaltPub (encC z) a).st = .halt ∧
      ∃ b : F, algebraMap F K b = (op9HaltPub (encC z) a).pt.noun.leaf :=
    ⟨rfl, ⟨((a : ℕ) : F), (gen_halt_leaf (F := F) z a).symm⟩⟩
  apply (algebraMap F K).injective
  rw [OptimizedMemoryCanonicalTrace.honestAtomOf_spec (F := F) _ hex, gen_halt_leaf (F := F)]

/-- The gate body at an honest `halt` row: selector `1`, role `2 = leaf`, column `180 = (a : F)`. -/
theorem gen_gate_zero (z : K) (a : ℕ) (eK : Env K) (eF : Env F)
    (hsel : eF.trace 1 = 1)
    (hleaf : eK.trace 2 = (op9HaltPub (encC z) a).pt.noun.leaf)
    (hatom : eF.trace 180 =
      OptimizedMemoryCanonicalTrace.honestAtomOf (F := F) (K := K) (op9HaltPub (encC z) a)) :
    (haltAtomMixed (F := F)).eval eK eF = 0 := by
  rw [on_halt_iff _ _ hsel, hleaf, hatom, gen_honest_atom (F := F), gen_halt_leaf (F := F)]

/-- Every `halt` row of the generated BFS forest is some `E (atom a)` (independent restatement
of the generator's `AllH` conclusion, consumed as a black box). -/
theorem gen_forest_halt_rows_are_atoms (z α lmb : K) (t : Nock.Walk.NTree (GenComputeRow K)) :
    ∀ n ∈ bfsForest (genMemForestFromTree (encC z) z α lmb t),
      n.label.row.2.2.st = MemoryTable.MState.halt →
        ∃ a : ℕ, n.label.row.2.2.pt.noun.leaf = algebraMap F K ((a : ℕ) : F) := by
  intro n hn hst
  obtain ⟨a, ha⟩ := genMemForestFromTree_bfs_halt (encC z) z α lmb t n hn hst
  refine ⟨a, ?_⟩
  rw [ha, encC_eq, GlobalCarryRecognizer.enc_atom, map_natCast]
  rfl

end Honest

/-! ## Check 4 — decode, re-derived from `mixed_at_family` -/
section Decode
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)

/-- `memoryStateOf env =.halt` forces base column `1 = 1`. -/
theorem halt_decode_forces_selector (env : Env F) (h : memoryStateOf env = .halt) :
    env.trace 1 = 1 := by
  unfold memoryStateOf at h
  split_ifs at h with h0 h1 h2
  exact h1

include hsat in
/-- On every accepted trace, a row the decoder reads as `halt` has `leaf = algebraMap (col 180)`.
Independent of `MemoryHaltAtomDecode.decodeMemPub_halt_leaf_eq_atom`. -/
theorem accepted_halt_leaf (i : Fin P.optimized.family.problem.cfg.memRows)
    (hst : memoryStateOf (memoryBaseEnvAt P c (honestQm P c Qm) i) = .halt) :
    (memorySourceEnvAt P c (honestQm P c Qm) i).trace 2 =
      algebraMap F K ((memoryBaseEnvAt P c (honestQm P c Qm) i).trace 180) := by
  have hg := mixed_at_family P c Qm hsat i haltAtomMixed
    (by simp [mixedTransitionGates])
  exact (on_halt_iff _ _ (halt_decode_forces_selector _ hst)).1 hg

include hsat in
/-- Same statement at the decoder's objects: `decodeMemPub` reads `st` via `memoryStateOf` and
`pt.noun` via `memoryPtNoun`, so the decoded `halt` leaf is the committed atom. -/
theorem decoded_halt_leaf (i : Fin P.optimized.family.problem.cfg.memRows)
    (hst : (decodeMemPub P (honestQm P c Qm) c i).st = .halt) :
    (decodeMemPub P (honestQm P c Qm) c i).pt.noun.leaf =
      algebraMap F K (memoryAtomAt P c (honestQm P c Qm) i) := by
  have hst' : memoryStateOf (memoryBaseEnvAt P c (honestQm P c Qm) i) = .halt := by
    simpa [decodeMemPub] using hst
  have := accepted_halt_leaf P c Qm hsat i hst'
  simpa [decodeMemPub, memoryPtNoun, memoryAtomAt, atomCol] using this

end Decode

#print axioms Nock.RedTeam.Batch613.decoded_halt_leaf
#print axioms Nock.RedTeam.Batch613.gen_gate_zero
#print axioms Nock.RedTeam.Batch613.coord_eval

end

end Nock.RedTeam.Batch613
