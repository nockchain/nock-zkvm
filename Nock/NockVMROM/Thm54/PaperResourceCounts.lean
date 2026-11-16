import Nock.Framework.Core
import Mathlib.Data.Nat.Log

/-!
# Theorem 5.4's resource list as affine functions of the extension degree `e`

`Def:RAP` makes the pair `(𝕂, e)` a *component of the RAP tuple*: the
structure `Nock.Framework.RAP` records it as the field `RAP.e` (`Nock/Framework/Core.lean:97`).
Theorem 5.4 then states **every** resource of both chips as an affine
function of that same `e`, never as a bare numeral:

* compute chip `RAP_NockComp-IO`
  - one commitment to at most `N + (9·e + 1)·L` elements in `𝔽`
  - two rounds of interaction, providing three random elements in `𝕂`
  - `62·e + 13` columns
  - `15 + 24·e` gates of degree at most `4`
  - `2·e` gates of degree `1`
  - `e` gates of degree `3`
  - two equality checks
  - `N` total rows
* memory chip `RAP_NockMem-IO`
  - one commitment to at most `M` elements in `𝔽`
  - one round of interaction, providing a random element in `𝕂`
  - `61·e + 13` columns in `𝔽`
  - `24·e + 16` gates of degree at most `4`
  - `2·e` gates of degree `1`
  - `2·e` gates of degree `3`
  - four equality checks
  - `M + 2L` total rows

This module carries those formulas as named definitions and records that the tree's deployed
constants — `199/98` compute and `196/104` memory — are **exactly** their `e = 3`
instantiations.  Nothing changes at `e = 3`; what changes is that the capstone's resource
conjuncts now name the paper's formula rather than its value at one degree.

Why this shape matters downstream: a `𝕂`-valued gate is committed by its `e` base-field
coordinates, so retyping a scalar gate to `𝕂` moves a `+1` to a `+e`.  Under numerals that reads
as a broken `104`; under this formulation it is a change of the coefficient in a formula the paper
already writes affinely.  `RAPPadding.lean:217-292` already carried the *core/residual* half of
this arithmetic parametrically; this module supplies the *final, paper-facing* half that
Theorem 5.4 literally states.
-/

namespace Nock.NockVMROM.Thm54
namespace Thm54Resources

/-! ## The deployed degree

The tree instantiates `𝕂` as a degree-`3` extension of `𝔽` throughout (`Basis (Fin 3) F K`),
so every constructed chip carries `RAP.e = 3`. -/

/-- The extension degree this tree deploys: `𝕂` is a cubic extension of `𝔽`. -/
def deployedExtensionDegree : ℕ := 3

/-- The maximal constraint degree, common to both chips. -/
def maxConstraintDegree : ℕ := 4

/-! ## Compute chip `RAP_NockComp-IO` -/

/-- Bound on the committed elements of `𝔽` for `N` opcodes and `L` memory records.  Affine in `e` through the `9·e + 1` factor. -/
def computeCommitmentBound (N L e : ℕ) : ℕ := N + (9 * e + 1) * L

/-- Rounds of interaction of the compute chip. -/
def computeCommittedRounds : ℕ := 2

/-- Random elements of `𝕂` the verifier supplies to the compute chip. -/
def computeRandomElements : ℕ := 3

/-- Extra form-R certificate columns at bit-length `n = Nat.size p`. -/
def rangeColumns (e n : ℕ) : ℕ :=
  (n - 1) + Nat.clog 2 n + ((Nat.clog 2 n + 2) / 3) * (1 + e)
    + ((Nat.clog 2 n + 2) / 3) + (n - 1) / 3
/-- Form R certificate gates at bit-length `n` and extension degree `e`. -/
def rangeGates (e n : ℕ) : ℕ :=
  (n - 1) + Nat.clog 2 n + (1 + e) * ((Nat.clog 2 n + 2) / 3)
    + ((Nat.clog 2 n + 2) / 3) + (n - 1) / 3 + 3

def computeColumns (e : ℕ) : ℕ := 63 * e + 13 + rangeColumns e 64 + 1

/-- Compute transition gates of degree at most `4`, **as the paper prices them**: `15 + 24·e`.  Kept under this name for the paper-comparison theorems; the deployed chip's
committed count is `computeTransitionGates` below. -/
def computeTransitionGatesPaper (e : ℕ) : ℕ := 24 * e + 15

/-- The 17 coin-folded non-IO families become the paper's selector-packed 78 `𝕂` gates; with the 7 IO/residual `𝕂` gates that were already
in the bucket this is `85·e` extension coordinates plus the 15 `𝔽` SV/mask gates.  The paper's
`15 + 24·e` is `computeTransitionGatesPaper`; it is **not** reproducible
coin-free (`ComputePaperPacking.paper_numeral_not_attainable_coin_free`).  Before this stage the
deployed chip met the paper numeral by folding. -/
def computeTransitionGates (e : ℕ) : ℕ := 85 * e + 15 + rangeGates e 64 + 1

/-- The paper states the terminal
constraint `requests = acc_prog(h₁)` at the paper and the seed implicitly, and does not
price either in `:1467-1469`; the tree commits both as `𝕂`-valued masked gates, `e` coordinates
each.  Before the
anchoring stage this was `2 * e`.

Before stage 2A this was `4 * e`.

Before this
stage the two errors were one coin-folded endpoint and this counter was `5 * e`. -/
def computeDegreeOneGates (e : ℕ) : ℕ := 6 * e + 1

/-- Compute degree-`3` endpoint gates: `e`. -/
def computeDegreeThreeGates (e : ℕ) : ℕ := e

/-- Compute equality checks: two.

**The `e` parameter is deliberately UNUSED and must not be "cleaned up".**

On the count itself: this is the **tree's** number — committed base-field gates.  the paper's
"Two equality checks" is a *different unit*, and the decisive evidence is `:990` with `:857`, not
`:594`: `:857` types the walk's final output `out_walk ∈ 𝕂`, and `:990` prices
`out_walk = 0` as "**One** equality check" **in the very list** where `:988` charges `2·e` for
degree-`1` gates and `:989` charges `e` for degree-`3` ones.  So in the paper a `𝕂`-valued
*terminal equality* costs one while a `𝕂`-valued *gate* costs `e` — the equality-check bucket is
counted per check, not per committed coordinate.  (`:594` is the weaker reason and was quoted
first for a day: its enumerate has exactly **two** items, `requests = responses` and
`out_mem = 0` at `:597`/`:598`, so it cannot account for `:1469`'s two *or* `:1489`'s four on its
own.)

**Stage 3e moved this counter `2 → 22`, and the unit is the point.**  The tree
counts *committed base-field gates*; the paper counts *verifier-side equalities on terminal
outputs*.  De-compressing the two eleven-term `challenge36` column pins into their twenty-two
individual equations (`OptimizedComputeFinal.finalEndpointEqualityChecks`) moves the tree's count
and cannot move the paper's, because the paper has no counterpart for those pins at all — they
are first/last-row column-vs-public pins, not terminal output equalities.
The two no longer agree at `e = 3`, which removes the coincidence rather than breaking a match. -/
def computeEqualityChecks (_e : ℕ) : ℕ := 22

/-- Everything the compute chip counts outside the transition bucket: the degree-`1` and
degree-`3` endpoint gates and the equality checks. -/
def computeEndpointConstraints (e : ℕ) : ℕ :=
  computeDegreeOneGates e + computeDegreeThreeGates e + computeEqualityChecks e

/-- The compute chip's total constraint count, i.e. the `Def:RAP` field `s`:
the four families of the paper summed. -/
def computeConstraints (e : ℕ) : ℕ :=
  computeTransitionGates e + computeEndpointConstraints e

/-- Compute rows: `N`. -/
def computeRows (N : ℕ) : ℕ := N

/-! ## Memory chip `RAP_NockMem-IO` -/

/-- Bound on the committed elements of `𝔽` for a forest with `M` nodes. -/
def memoryCommitmentBound (M : ℕ) : ℕ := M

/-- Rounds of interaction of the memory chip. -/
def memoryCommittedRounds : ℕ := 1

/-- Random elements of `𝕂` the verifier supplies to the memory chip. -/
def memoryRandomElements : ℕ := 1

def memoryColumns (e : ℕ) : ℕ := 64 * e + 13

/-- Memory transition gates of degree at most `4`, **as the paper prices them**: `24·e + 16`.  Kept under this name for the paper-comparison theorems
(`MemoryFactorizationScope`, `GateCorrespondenceMemory`, `EqualityCheckLedger`,
`MemoryPaperFactorization.count_comparison`); the deployed chip's committed count is
`memoryTransitionGates` below. -/
def memoryTransitionGatesPaper (e : ℕ) : ℕ := 24 * e + 16

/-- Until the ver-gate this was `49·e + 5`.  This is a **tree** count of committed base-field gates, disclosed — the `LO` precedent —
not a re-reading of `:1483`; the paper's own formula is
`memoryTransitionGatesPaper = 24·e + 16`. -/
def memoryTransitionGates (e : ℕ) : ℕ := 50 * e + 6

/-- Memory degree-`1` endpoint gates **as the paper prices them**: `2·e`.  Kept
under this name for the paper-comparison theorems; the deployed chip's committed count is
`memoryDegreeOneGates` below. -/
def memoryDegreeOneGatesPaper (e : ℕ) : ℕ := 2 * e

/-- Memory degree-`3` endpoint gates **as the paper prices them**: `2·e`. -/
def memoryDegreeThreeGatesPaper (e : ℕ) : ℕ := 2 * e

/-- Memory degree-`1` endpoint gates: **`0`**.  The paper's `2·e` is
`memoryDegreeOneGatesPaper`. -/
def memoryDegreeOneGates (_e : ℕ) : ℕ := 0

/-- The paper's `2·e` is `memoryDegreeThreeGatesPaper`. -/
def memoryDegreeThreeGates (_e : ℕ) : ℕ := 0

def memoryEqualityChecks (_e : ℕ) : ℕ := 0

/-- Everything the memory chip counts outside the transition bucket. -/
def memoryEndpointConstraints (e : ℕ) : ℕ :=
  memoryDegreeOneGates e + memoryDegreeThreeGates e + memoryEqualityChecks e

/-- The paper's `2·e + 2·e`
and "Four" (`:1489`) survive as `…Paper` / the documented unit split; the tree bills every
masked endpoint in `memoryTransitionGates = 49·e + 6`. -/
theorem memory_endpoint_total_unmoved_by_lu (e : ℕ) :
    memoryDegreeOneGates e = 0 ∧ memoryDegreeThreeGates e = 0 ∧
      memoryEqualityChecks e = 0 ∧ memoryEndpointConstraints e = 0 ∧
      memoryDegreeOneGatesPaper e = 2 * e ∧ memoryDegreeThreeGatesPaper e = 2 * e := by
  simp [memoryDegreeOneGates, memoryDegreeThreeGates, memoryEqualityChecks,
    memoryEndpointConstraints, memoryDegreeOneGatesPaper, memoryDegreeThreeGatesPaper]

/-- The memory chip's total constraint count, i.e. the `Def:RAP` field `s`.

**Licence for `32·e + 16`, stated rather than assumed.**  So `28·e + 20 → 32·e + 16` is **not** a re-reading of
`:1489` and is **not** presented as arithmetic about the paper: it is the tree's own committed-gate
total moving because the chip now commits twelve base-field equality gates where it committed
four.  `paper_matched_memory_buckets_unmoved` and `memory_equality_bucket_is_the_only_mover` are
the receipts.

`memory_transition_bucket_is_the_amem2_mover` is the receipt. -/
def memoryConstraints (e : ℕ) : ℕ :=
  memoryTransitionGates e + memoryEndpointConstraints e

/-- Memory rows: `M + 2L`. -/
def memoryRows (M L : ℕ) : ℕ := M + 2 * L

/-! ## The affine shape, in closed form -/

theorem clog2_64 : Nat.clog 2 64 = 6 := by
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.clog_pow _ _ (by norm_num)]

theorem rangeGates_64 (e : ℕ) : rangeGates e 64 = 97 + 2 * e := by
  simp [rangeGates, clog2_64]
  omega

theorem rangeColumns_3_64 : rangeColumns 3 64 = 100 := by
  simp [rangeColumns, clog2_64]

theorem computeConstraints_closed (e : ℕ) : computeConstraints e = 94 * e + 136 := by
  simp only [computeConstraints, computeTransitionGates, computeEndpointConstraints,
    computeDegreeOneGates, computeDegreeThreeGates, computeEqualityChecks, rangeGates_64]
  omega

theorem memoryConstraints_closed (e : ℕ) : memoryConstraints e = 50 * e + 6 := by
  simp [memoryConstraints, memoryTransitionGates, memoryEndpointConstraints,
    memoryDegreeOneGates, memoryDegreeThreeGates, memoryEqualityChecks]

/-- The transition bucket is recovered from the total by removing the endpoint bucket. -/
theorem computeTransitionGates_eq_sub (e : ℕ) :
    computeConstraints e - computeEndpointConstraints e = computeTransitionGates e := by
  simp [computeConstraints]

theorem memoryTransitionGates_eq_sub (e : ℕ) :
    memoryConstraints e - memoryEndpointConstraints e = memoryTransitionGates e := by
  simp [memoryConstraints]

/-! ## What the `𝔽 → 𝕂` retyping moved, and what it did not -/

/-- These
are the four the paper states; the retyping changed
none of them, at any `e`.  **Since A-mem-2 the transition bucket is a tree count** — the paper's
formula survives as `memoryTransitionGatesPaper`, and the deployed `memoryTransitionGates` is
`26·e + 11`, which exceeds it by `2·e − 5` (one at `e = 3`). -/
theorem paper_matched_memory_buckets_unmoved (e : ℕ) :
    memoryColumns e = 64 * e + 13 ∧
      memoryTransitionGatesPaper e = 24 * e + 16 ∧
      memoryTransitionGates e = 50 * e + 6 ∧
      memoryDegreeOneGatesPaper e = 2 * e ∧
      memoryDegreeThreeGatesPaper e = 2 * e ∧
      memoryDegreeOneGates e = 0 ∧ memoryDegreeThreeGates e = 0 ∧
      memoryEqualityChecks e = 0 := by
  simp [memoryColumns, memoryTransitionGatesPaper, memoryTransitionGates,
    memoryDegreeOneGatesPaper, memoryDegreeThreeGatesPaper, memoryDegreeOneGates,
    memoryDegreeThreeGates, memoryEqualityChecks]

/-- Stated over the paper's transition formula `memoryTransitionGatesPaper`
(the pre-A-mem-2 `memoryConstraints`).  The total went from `28·e + 20` to `32·e + 16`, a difference of exactly
`4·e − 4` — the retyping of four scalar checks into four `𝕂`-valued ones, each committed by its
`e` coordinates.  The two totals agree only at `e = 1`; in particular they differ at the deployed
`e = 3`, which is why the capstone's numeral moved `104 → 112` and why that move is disclosed
rather than presented as a restatement. -/
theorem memory_equality_bucket_is_the_only_mover (e : ℕ) :
    memoryTransitionGatesPaper e = 24 * e + 16 ∧
      memoryEndpointConstraints e = 0 ∧
      memoryEqualityChecks e = 0 ∧
      memoryTransitionGatesPaper 3 = 88 := by
  refine ⟨rfl, ?endp, rfl, by decide⟩
  simp [memoryEndpointConstraints, memoryDegreeOneGates, memoryDegreeThreeGates,
    memoryEqualityChecks]

/-- `memoryConstraints` went
`34·e + 11 → 45·e + 5`, `113 → 140` at `e = 3`, then `45·e + 5 → 47·e + 5`,
`140 → 146` at the nineteenth (root-mask) move.  The endpoint/equality buckets are empty. -/
theorem memory_transition_bucket_is_the_amem2_mover (e : ℕ) :
    memoryConstraints e = 50 * e + 6 ∧
      memoryEndpointConstraints e = 0 ∧
      memoryConstraints 3 = 156 ∧ memoryTransitionGatesPaper 3 = 88 := by
  refine ⟨memoryConstraints_closed e, ?endp, by decide, by decide⟩
  simp [memoryEndpointConstraints, memoryDegreeOneGates, memoryDegreeThreeGates,
    memoryEqualityChecks]

/-! ## The deployed instantiation `e = 3`

They are the reason re-pointing the capstone's resource conjuncts at
the parametric form changes nothing about what is proved. -/

theorem computeColumns_deployed : computeColumns deployedExtensionDegree = 303 := by
  simp [computeColumns, deployedExtensionDegree, rangeColumns_3_64]

theorem computeConstraints_deployed : computeConstraints deployedExtensionDegree = 418 := by
  simp [computeConstraints_closed, deployedExtensionDegree]

theorem computeTransitionGates_deployed :
    computeTransitionGates deployedExtensionDegree = 374 := by
  simp [computeTransitionGates, deployedExtensionDegree, rangeGates_64]

theorem computeTransitionGatesPaper_deployed :
    computeTransitionGatesPaper deployedExtensionDegree = 87 := by
  simp [computeTransitionGatesPaper, deployedExtensionDegree]

theorem computeEndpointConstraints_deployed :
    computeEndpointConstraints deployedExtensionDegree = 44 := by
  simp [computeEndpointConstraints, computeDegreeOneGates, computeDegreeThreeGates,
    computeEqualityChecks, deployedExtensionDegree]

theorem computeCommitmentBound_deployed (N L : ℕ) :
    computeCommitmentBound N L deployedExtensionDegree = N + 28 * L := by
  simp [computeCommitmentBound, deployedExtensionDegree]

theorem memoryColumns_deployed : memoryColumns deployedExtensionDegree = 205 := by
  simp [memoryColumns, deployedExtensionDegree]

theorem memoryConstraints_deployed : memoryConstraints deployedExtensionDegree = 156 := by
  simp [memoryConstraints_closed, deployedExtensionDegree]

theorem memoryTransitionGates_deployed :
    memoryTransitionGates deployedExtensionDegree = 156 := by
  simp [memoryTransitionGates, deployedExtensionDegree]

theorem memoryTransitionGatesPaper_deployed :
    memoryTransitionGatesPaper deployedExtensionDegree = 88 := by
  simp [memoryTransitionGatesPaper, deployedExtensionDegree]

theorem memoryEndpointConstraints_deployed :
    memoryEndpointConstraints deployedExtensionDegree = 0 := by
  simp [memoryEndpointConstraints, memoryDegreeOneGates, memoryDegreeThreeGates,
    memoryEqualityChecks]

/-! ## Equivalence of the parametric and numeric resource statements at `e = 3`

The capstone's `exact_resources` conjunct is re-pointed at the parametric right-hand sides. -/

theorem compute_resources_iff (e w s d k : ℕ) :
    (e = deployedExtensionDegree ∧ w = computeColumns e ∧ s = computeConstraints e ∧
        d = maxConstraintDegree ∧ k = computeCommittedRounds)
      ↔ (e = 3 ∧ w = 303 ∧ s = 418 ∧ d = 4 ∧ k = 2) := by
  constructor
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, computeColumns_deployed, computeConstraints_deployed, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨rfl, ?_, ?_, rfl, rfl⟩
    · exact computeColumns_deployed.symm
    · exact computeConstraints_deployed.symm

theorem memory_resources_iff (e w s d k : ℕ) :
    (e = deployedExtensionDegree ∧ w = memoryColumns e ∧ s = memoryConstraints e ∧
        d = maxConstraintDegree ∧ k = memoryCommittedRounds)
      ↔ (e = 3 ∧ w = 205 ∧ s = 156 ∧ d = 4 ∧ k = 1) := by
  constructor
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, memoryColumns_deployed, memoryConstraints_deployed, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨rfl, ?_, ?_, rfl, rfl⟩
    · exact memoryColumns_deployed.symm
    · exact memoryConstraints_deployed.symm

/-- At the deployed degree the parametric transition fingerprint is exactly the numeric
`s - 43 = 270` it replaces. -/
theorem compute_transition_fingerprint_iff (e s : ℕ) (he : e = deployedExtensionDegree) :
    (s - computeEndpointConstraints e = computeTransitionGates e) ↔ (s - 44 = 374) := by
  subst he
  rw [computeEndpointConstraints_deployed, computeTransitionGates_deployed]

theorem memory_transition_fingerprint_iff (e s : ℕ) (he : e = deployedExtensionDegree) :
    (s - memoryEndpointConstraints e = memoryTransitionGates e) ↔ (s - 0 = 156) := by
  subst he
  rw [memoryEndpointConstraints_deployed, memoryTransitionGates_deployed]

end Thm54Resources
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.Thm54Resources.computeConstraints_closed
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.memoryConstraints_closed
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.computeColumns_deployed
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.computeConstraints_deployed
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.memoryColumns_deployed
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.memoryConstraints_deployed
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.compute_resources_iff
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.memory_resources_iff
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.compute_transition_fingerprint_iff
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.paper_matched_memory_buckets_unmoved
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.memory_equality_bucket_is_the_only_mover
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.memory_transition_bucket_is_the_amem2_mover
#print axioms Nock.NockVMROM.Thm54.Thm54Resources.memory_transition_fingerprint_iff
