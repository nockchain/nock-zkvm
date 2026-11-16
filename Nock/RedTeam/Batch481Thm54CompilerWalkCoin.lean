/-
  Nock/RedTeam/Batch481Thm54CompilerWalkCoin.lean

  **The compiled walk was identically
  zero.**

  At `α = 0` the walk columns are `ln ≡ count ≡ acc ≡ 0`, so
  either queue gate is unsatisfiable on every table with `h ≥ 2`
  (`Batch478::alpha_zero_gate_unsat`).  That is a completeness break at the
  compiler's own triple.

  The compiler now chooses `compilerWalkCoin packageOrbit` — the RAP orbit
  generator injected into `K`.  `hprogCap` / `hcap` give `rows ≤ 2^hOrb < 3 · 2^hOrb`, so
  `Batch478::honest_ratio_gate`'s `h ≤ orderOf α` holds by construction.
  The COMPUTE walk coin and the walk
  `γ` stay `compilerWalkCoin packageOrbit`, as below.)

  `perfect_at_compiler_triple` is re-stated (it never mentioned the walk-coin
  value; the honest-chip identity is `computeChipAt_honest_of_chalVal`).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.RedTeam.Batch361Thm54Completeness
import Nock.RedTeam.Batch478Thm54QueueGateRatioForm
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch481

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.StrictExtension

/-! ## F1 — the compiled walk was identically zero -/

/-- **F1.**  At the OG merge the compiler's walk coins were the zero tuple. -/
def findingF1 : String :=
  "compiler walk coins were 0 0 0 (fun _ => 0) 0 at GenNockCompilesBounded.lean:447,:639 (280ba79)"

theorem findingF1_nonempty : findingF1 ≠ "" := by decide

/-- The zero walk coin makes the ratio gate unsatisfiable for `h ≥ 2`
(`Batch478::alpha_zero_gate_unsat`).  Adopting the gate without changing the
compiler coin would break `perfect_at_compiler_triple`. -/
theorem f1_zero_coin_unsat {K : Type*} [Field K] {h : ℕ} (hh : 2 ≤ h) :
    ∀ walk_inv : ℕ → K,
      ¬ (∀ i, 1 ≤ i → i < h → walk_inv i * ((0 : K) ^ i - (0 : K) ^ i) = 1) := by
  intro walk_inv hgate
  have h1 : 1 ≤ 1 := le_refl 1
  have hlt : 1 < h := Nat.lt_of_succ_le hh
  have := hgate 1 h1 hlt
  simp at this

/-- The new compiler walk coin is nonzero. -/
theorem compilerWalkCoin_ne_zero
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {hOrb : ℕ} (o : StrictOrbitDomain F 3 hOrb) :
    compilerWalkCoin (F := F) (K := K) o ≠ 0 :=
  TraceGen.compilerWalkCoin_ne_zero (F := F) (K := K) o

/-- Its order is `3 · 2^hOrb`, hence strictly above any `rows ≤ 2^hOrb`. -/
theorem compilerWalkCoin_order_gt_rows
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {hOrb : ℕ} (o : StrictOrbitDomain F 3 hOrb)
    {rows : ℕ} (hrows : rows ≤ 2 ^ hOrb) :
    rows < orderOf (compilerWalkCoin (F := F) (K := K) o) := by
  rw [compilerWalkCoin_order]
  have hpos : 0 < 2 ^ hOrb := pow_pos (by decide) _
  omega

/-- Completeness side condition of `Batch478::honest_ratio_gate` at the
compiler coin, for any table no taller than the orbit. -/
theorem honest_ratio_side_of_compiler
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {hOrb : ℕ} (o : StrictOrbitDomain F 3 hOrb)
    {h : ℕ} (hh : h ≤ 2 ^ hOrb) :
    h ≤ orderOf (compilerWalkCoin (F := F) (K := K) o) :=
  Nat.le_of_lt (compilerWalkCoin_order_gt_rows (F := F) (K := K) o hh)

/-! ## Perfect completeness at the compiler triple, restated -/

/-- Re-proof of `Batch361.perfect_at_compiler_triple`: the honest chip *is*
`computeChipAt honestTuple` once `chalVal` agrees.  The walk-coin change does
not appear in the hypotheses. -/
theorem perfect_at_compiler_triple
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (hchal :
      DeployedChipFamily.computeChalValOfTuple P.optimized.basis P.honestTuple =
        P.optimized.computeChallenge)
    (hst :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
        ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula)
    (hs :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).s =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.subject)
    (hf :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).f =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.formula)
    (he :
      (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).e =
        GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1)
          P.optimized.verifier.raw.claim.result) :
    P.computeChipAt P.honestTuple = P.computeChip :=
  Nock.RedTeam.Batch361.perfect_at_compiler_triple P hchal hst hs hf he

def nockCompiles_zmod_hypotheses_unmoved : String :=
  "nockCompiles_zmod binders unmoved: hrun hbound hs hf hΛp hp hK hF hwin hKszChar"
    ++ " (historical; repair (ii) 2026-10-21 retyped hwin to the pair, names unmoved)"

theorem nockCompiles_zmod_hypotheses_unmoved_nonempty :
    nockCompiles_zmod_hypotheses_unmoved ≠ "" := by decide

end Nock.RedTeam.Batch481

#print axioms Nock.RedTeam.Batch481.compilerWalkCoin_ne_zero
#print axioms Nock.RedTeam.Batch481.compilerWalkCoin_order_gt_rows
#print axioms Nock.RedTeam.Batch481.honest_ratio_side_of_compiler
#print axioms Nock.RedTeam.Batch481.perfect_at_compiler_triple
#print axioms Nock.RedTeam.Batch481.f1_zero_coin_unsat
