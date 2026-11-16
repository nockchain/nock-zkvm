/-
  Nock/NockVMROM/Thm54/TraceGen/GenNockCompilesBounded.lean

  **`hb` and `haxis` discharged: the two skeleton-level premises of the `∃ package` theorems are
  replaced by conditions on the program.**

  `nockCompiles_of_accepted` / `nockCompiles_of_rom` (`GenNockCompiles.lean`) and
  `GoodSeed.nockCompiles_of_rom_atRomSeed` (`GenGoodSeedExists.lean`) each carry

  * `hb    : (genSemanticSkeleton (bfsAssign (airReorder t)) …).BoundedBy q`, and
  * `haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t)) …)`,

  Both have `∀ program` suppliers that
  had never been wired into these theorems: `genComputeSkeleton_skeletonBounded`
  (`GenGenericBounded.lean::genComputeSkeleton_skeletonBounded`) and
  `genComputeSkeleton_axisRange` (`GenGenericAxisRange.lean::genComputeSkeleton_axisRange`).

  **What the suppliers cost, stated precisely.**  Each wants `1 < q` — which `hq : 11 < q` gives —
  together with three conditions on the *input*:

  * `hs : FieldEmbedding.BoundedBy q subject` and `hf : FieldEmbedding.BoundedBy q formula`
    — every atom of the program is `< q`;
  * `hG : FieldEmbedding.evalGBy q fuel subject formula = some result` — the run reaches the
    result without an `OP_4` increment touching `q`.

  So at the *acceptance* antecedent the trade is two premises for three, and
  `nockCompiles_of_accepted_bounded` says so honestly (§1 below).  At the *ROM* antecedent it is
  not: `hrom` and `hG` are the same run under two different restrictions, and `evalGRom`
  (`GenGuardedRom.lean::evalGRom`) carries both in one hypothesis, so §2 and §3 trade
  `{hrom, hb, haxis}` for `{hgrom, hs, hf}` — three for three, with the two skeleton-level
  conditions gone and only program-level ones left.

  They are decidable on the
  source text before anything is compiled. `hb` and `haxis` were neither.

-- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericAxisRange
import Nock.NockVMROM.Thm54.TraceGen.GenGenericMempos
import Nock.NockVMROM.Thm54.TraceGen.GenGenericSeedIrrel
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists
import Nock.NockVMROM.Thm54.TraceGen.GenGuardedRom
import Nock.NockVMROM.Thm54.TraceGen.GenCoinCounting
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

-- Form R `λ` of the generated memory rows (the configuration's `λ`; 28th λ-fix).
variable {lmb : K}

/-! ## 0. Compiler defaults for P6.1

The canonical challenge vector is the
one every live config already writes by hand
(`{ a, b, c, α, z, β := 0, γ := 0 }`, matching `memInputs z`). `StateTagChar` is
`NodeEncoding.stateTagChar_of_ringChar_gt_eleven` off `hq`/`hchar`.

`bas` / `packageOrbit` / `orbit` stay on `p61`–`p67`.  The carrier-pass
(`GenNockCompilesCarrier.lean::nockCompiles_p68`) inhabits them from
`hK : finrank F K = 3` and `hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1`
 — field restrictions §1 sanctions.

Its order is `3 · 2^hOrb` (`StrictOrbitDomain.order_ω`), which is `> rows` by
`hprogCap` / `hcap`, so `Batch478::honest_ratio_gate`'s `h ≤ orderOf α` holds
by construction. No new hypothesis on `nockCompiles_zmod`. -/

/-- **The compiler's challenge vector at the sampled `λ`.**  Compute coins `(α, z, a, b, c)`, the
memory pole/γ at `0` (exactly `memInputs z`), and Form R `λ := lmb` — the round's **sampled** `λ`
.  The
compiler chooses no `λ`: every theorem below is stated at an arbitrary `lmb`, and the carrier pass
(`GenNockCompilesCarrier.lean::nockCompiles_p68`) quantifies it in its conclusion.
-- -/
def compilerChallengeVector (α z a b c lmb : K) : ChallengeVector K where
  a := a
  b := b
  c := c
  α := α
  z := z
  β := 0
  γ := 0
  lam := lmb

@[simp] theorem compilerChallengeVector_computeInputs (α z a b c lmb : K) :
    (compilerChallengeVector α z a b c lmb).computeInputs = ⟨α, z, a, b, c⟩ :=
  rfl

@[simp] theorem compilerChallengeVector_memoryInputs (α z a b c lmb : K) :
    (compilerChallengeVector α z a b c lmb).memoryInputs = memInputs z :=
  rfl

@[simp] theorem compilerChallengeVector_lam (α z a b c lmb : K) :
    (compilerChallengeVector α z a b c lmb).lam = lmb :=
  rfl

/-- `StateTagChar` from the two characteristic binders the `∃ package` theorems already
carry (`hq : 11 < q`, `hchar : q = ringChar K`).  No new hypothesis.
-- -/
theorem compilerStateTagChar {q : ℕ} (hq : 11 < q) (hchar : q = ringChar K) :
    NodeEncoding.StateTagChar K :=
  NodeEncoding.stateTagChar_of_ringChar_gt_eleven (hchar ▸ hq)

/-- **The compiler's walk coin.**  The RAP orbit generator of
`packageOrbit` (`compilerStrictGenerator`, order `3 · 2^hOrb`),
injected into `K`. -/
def compilerWalkCoin {hOrb : ℕ} (o : StrictOrbitDomain F 3 hOrb) : K :=
  algebraMap F K o.ω

theorem compilerWalkCoin_order {hOrb : ℕ} (o : StrictOrbitDomain F 3 hOrb) :
    orderOf (compilerWalkCoin (F := F) (K := K) o) = 3 * 2 ^ hOrb :=
  (orderOf_injective (algebraMap F K).toMonoidHom
    (RingHom.injective (algebraMap F K)) o.ω).trans o.order_ω

/-- Queue-witness completeness: `rows ≤ 2^hOrb` is enough, because
`orderOf (compilerWalkCoin o) = 3 · 2^hOrb`.  Not a new `nockCompiles_zmod`
hypothesis — the compiler already chose this coin and this orbit.
-- -/
theorem compilerWalkOrder_of_le {hOrb rows : ℕ} (o : StrictOrbitDomain F 3 hOrb)
    (hle : rows ≤ 2 ^ hOrb) :
    2 ≤ rows → rows ≤ orderOf (compilerWalkCoin (F := F) (K := K) o) := fun _ =>
  hle.trans <| by
    rw [compilerWalkCoin_order]
    exact Nat.le_mul_of_pos_left (2 ^ hOrb) (by norm_num : 0 < 3)

theorem compilerWalkCoin_ne_zero {hOrb : ℕ} (o : StrictOrbitDomain F 3 hOrb) :
    compilerWalkCoin (F := F) (K := K) o ≠ 0 := by
  intro h0
  have hω : o.ω = 0 :=
    (map_eq_zero_iff (algebraMap F K) (RingHom.injective _)).mp h0
  have hpow : o.ω ^ (3 * 2 ^ hOrb) = 1 := by
    rw [← o.order_ω]; exact pow_orderOf_eq_one _
  rw [hω, zero_pow (Nat.pos_iff_ne_zero.mp
    (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _)))] at hpow
  exact zero_ne_one hpow

/-! ## 0b. Compiler capacity values for P6.2

`Ksz`, `B` and `n` are **numeric** compiler choices, computed from the program's own
row counts. Their comparison hypotheses (`hKsz`, `hKsz2`, `hB`, `hreqn`, `hrespn`)
become `le_max` / `le_rfl`. `orbit : OrbitDomain K` is **not** moved: it needs an
element of order `2^h` in `K`, the same inhabitation obstruction as `packageOrbit`
(P6.1 finding). `hmempos` is derived:
`genComputeSkeleton_hmempos` (`GenGenericMempos.lean`), from the always-on formula-open request
. -/

/-- Request-column accumulator of a compute tree. -/
abbrev programAcc (t : NTree (GenComputeRow K)) : ℕ :=
  accAt (airReorder t) (bfsRows (airReorder t)).length

/-- Memory-row count of the generated forest at Form R `λ = lmb`. -/
abbrev programMemRowsL (lmb z α : K) (t : NTree (GenComputeRow K)) : ℕ :=
  (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length

/-- Memory-root count (`genExactConfig.kMem`) at Form R `λ = lmb`. -/
abbrev programMemRootsL (lmb z α : K) (t : NTree (GenComputeRow K)) : ℕ :=
  (genMemoryForest z α lmb (memInputs z) t).length

/-- **λ-free memory-row count.**  `λ` is a row label: the count is the same at every `λ`
(`programMemRows_eq_L`), so it is read off at the dummy label `0`, exactly as the seed slot of
`hKszChar` is the dummy `(0 : K)` (`programMemRows_irrel`).  Not a choice of `λ`: no package,
configuration or row is built at this value. -/
abbrev programMemRows (z α : K) (t : NTree (GenComputeRow K)) : ℕ :=
  programMemRowsL 0 z α t

/-- λ-free memory-root count (see `programMemRows`). -/
abbrev programMemRoots (z α : K) (t : NTree (GenComputeRow K)) : ℕ :=
  programMemRootsL 0 z α t

/-- Compiler IO window: the request accumulator and twice the root count. -/
abbrev compilerKsz (acc mfLen : ℕ) : ℕ := max acc (2 * mfLen)

abbrev compilerKszOfL (lmb z α : K) (t : NTree (GenComputeRow K)) : ℕ :=
  compilerKsz (programAcc t) (programMemRootsL lmb z α t)

abbrev compilerKszOf (z α : K) (t : NTree (GenComputeRow K)) : ℕ :=
  compilerKsz (programAcc t) (programMemRoots z α t)

/-- Compiler IO record bound: the larger of the two record columns. -/
abbrev compilerN (acc memR : ℕ) : ℕ := max acc memR

abbrev compilerNOfL (lmb z α : K) (t : NTree (GenComputeRow K)) : ℕ :=
  compilerN (programAcc t) (programMemRowsL lmb z α t)

abbrev compilerNOf (z α : K) (t : NTree (GenComputeRow K)) : ℕ :=
  compilerN (programAcc t) (programMemRows z α t)

@[simp] theorem compilerKsz_acc (acc mfLen : ℕ) : acc ≤ compilerKsz acc mfLen :=
  le_max_left _ _

@[simp] theorem compilerKsz_two_mul (acc mfLen : ℕ) :
    2 * mfLen ≤ compilerKsz acc mfLen :=
  le_max_right _ _

@[simp] theorem compilerN_acc (acc memR : ℕ) : acc ≤ compilerN acc memR :=
  le_max_left _ _

@[simp] theorem compilerN_mem (acc memR : ℕ) : memR ≤ compilerN acc memR :=
  le_max_right _ _

/-- Memory-row count is independent of the NPR seed and of `λ` (both are labels). -/
theorem programMemRowsL_lam (lmb lmb' z z' α : K) (t : NTree (GenComputeRow K)) :
    programMemRowsL lmb z α t = programMemRowsL lmb' z' α t :=
  genMemoryForest_bfsForest_length_lam_irrel z z' α lmb lmb' (memInputs z) (memInputs z') t

/-- Memory-root count is independent of the NPR seed and of `λ`. -/
theorem programMemRootsL_lam (lmb lmb' z z' α : K) (t : NTree (GenComputeRow K)) :
    programMemRootsL lmb z α t = programMemRootsL lmb' z' α t :=
  genMemoryForest_length_lam_irrel z z' α lmb lmb' (memInputs z) (memInputs z') t

theorem programMemRowsL_irrel (lmb z z' α : K) (t : NTree (GenComputeRow K)) :
    programMemRowsL lmb z α t = programMemRowsL lmb z' α t :=
  programMemRowsL_lam lmb lmb z z' α t

theorem programMemRootsL_irrel (lmb z z' α : K) (t : NTree (GenComputeRow K)) :
    programMemRootsL lmb z α t = programMemRootsL lmb z' α t :=
  programMemRootsL_lam lmb lmb z z' α t

theorem compilerKszOfL_irrel (lmb z z' α : K) (t : NTree (GenComputeRow K)) :
    compilerKszOfL lmb z α t = compilerKszOfL lmb z' α t := by
  unfold compilerKszOfL
  rw [programMemRootsL_irrel lmb z z' α t]

theorem compilerNOfL_irrel (lmb z z' α : K) (t : NTree (GenComputeRow K)) :
    compilerNOfL lmb z α t = compilerNOfL lmb z' α t := by
  unfold compilerNOfL
  rw [programMemRowsL_irrel lmb z z' α t]

theorem programMemRows_irrel (z z' α : K) (t : NTree (GenComputeRow K)) :
    programMemRows z α t = programMemRows z' α t :=
  programMemRowsL_irrel 0 z z' α t

theorem programMemRoots_irrel (z z' α : K) (t : NTree (GenComputeRow K)) :
    programMemRoots z α t = programMemRoots z' α t :=
  programMemRootsL_irrel 0 z z' α t

theorem compilerKszOf_irrel (z z' α : K) (t : NTree (GenComputeRow K)) :
    compilerKszOf z α t = compilerKszOf z' α t :=
  compilerKszOfL_irrel 0 z z' α t

theorem compilerNOf_irrel (z z' α : K) (t : NTree (GenComputeRow K)) :
    compilerNOf z α t = compilerNOf z' α t :=
  compilerNOfL_irrel 0 z z' α t

/-- The λ-free counts are the counts at every sampled `λ`. -/
theorem programMemRows_eq_L (lmb z α : K) (t : NTree (GenComputeRow K)) :
    programMemRows z α t = programMemRowsL lmb z α t :=
  programMemRowsL_lam 0 lmb z z α t

theorem programMemRoots_eq_L (lmb z α : K) (t : NTree (GenComputeRow K)) :
    programMemRoots z α t = programMemRootsL lmb z α t :=
  programMemRootsL_lam 0 lmb z z α t

theorem compilerKszOf_eq_L (lmb z α : K) (t : NTree (GenComputeRow K)) :
    compilerKszOf z α t = compilerKszOfL lmb z α t := by
  unfold compilerKszOf compilerKszOfL
  rw [programMemRoots_eq_L lmb z α t]

theorem compilerNOf_eq_L (lmb z α : K) (t : NTree (GenComputeRow K)) :
    compilerNOf z α t = compilerNOfL lmb z α t := by
  unfold compilerNOf compilerNOfL
  rw [programMemRows_eq_L lmb z α t]

/-- Seed-free memory-forest shape (F-8).  Dummy seed `0` is a label;
`encC` does not change `recordTreeSize`. -- the paper -/
def programMemShape (α : K) (t : NTree (GenComputeRow K)) : ℕ :=
  programMemRows (0 : K) α t

theorem programMemShape_spec {lmb : K} (z α : K) (t : NTree (GenComputeRow K)) :
    programMemShape α t = programMemRowsL lmb z α t := by
  dsimp [programMemShape]
  exact programMemRowsL_lam 0 lmb 0 z α t

/-- **Repair (ii).**  At repair (ii) the memory walk
ran at the §1 timestamp coin `α` and this lemma discharged `hordM`; since S2
the chain runs the memory walk at its own coin `αW` and uses `memRowsL_le_orderOf_of_shapeW`.
This lemma (the `αW := α` instance) is kept.  At repair (ii):
`buildFullPackage`'s `hordM` needs `memRows ≤ orderOf α`.  From the memory half of §1's
`hwin` (weakest form, `programMemShape α t ≤ orderOf α`: distinct walk line numbers `α^i` over
the memory rows); exactly what `hordM` consumes. -/
theorem memRowsL_le_orderOf_of_shape {lmb z α : K} {t : NTree (GenComputeRow K)}
    (h : programMemShape α t ≤ orderOf α) :
    (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤ orderOf α := by
  change programMemRowsL lmb z α t ≤ orderOf α
  rw [← programMemShape_spec (lmb := lmb) z α t]
  omega

/-! ### S2 (W-gen): the memory walk at its own coin `αW` -/

section AlphaIrrel

open MemoryTable

theorem genRowMemForest_totalSize_alpha_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α₁ α₂ lmb₁ lmb₂ : K) (reqs : List MemRecordReq) :
    totalSize (genRowMemForest E z α₁ lmb₁ reqs) =
      totalSize (genRowMemForest E' z' α₂ lmb₂ reqs) := by
  match reqs with
  | [] => simp [genRowMemForest]
  | [r] =>
    rw [genRowMemForest_singleton_size, genRowMemForest_singleton_size]
  | [r1, r2] =>
    by_cases hc : r1.child = r2.root
    · exact (genRowMemForest_two_chain_size (lmb := lmb₁) E z α₁ r1 r2 hc).1.trans
        (genRowMemForest_two_chain_size (lmb := lmb₂) E' z' α₂ r1 r2 hc).1.symm
    · exact (genRowMemForest_two_indep_size (lmb := lmb₁) E z α₁ r1 r2 hc).1.trans
        (genRowMemForest_two_indep_size (lmb := lmb₂) E' z' α₂ r1 r2 hc).1.symm
  | [r1, r2, r3] =>
    simp [genRowMemForest_three_eq, totalSize_append]
    rw [genRowMemForest_totalSize_alpha_irrel E E' z z' α₁ α₂ lmb₁ lmb₂ [r1, r2]]
    simp [totalSize_cons, totalSize_nil, genAnnotatedRecordTree_size]
  | r1 :: r2 :: r3 :: r4 :: rest =>
    have hE := totalSize_map_annotated (lmb := lmb₁) E z α₁ (r1 :: r2 :: r3 :: r4 :: rest)
    have hE' := totalSize_map_annotated (lmb := lmb₂) E' z' α₂ (r1 :: r2 :: r3 :: r4 :: rest)
    simp [genRowMemForest] at hE hE' ⊢
    rw [hE, hE']

mutual
theorem genMemForestFromTree_totalSize_alpha_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α₁ α₂ lmb₁ lmb₂ : K) (t : NTree (GenComputeRow K)) :
    totalSize (genMemForestFromTree E z α₁ lmb₁ t) =
      totalSize (genMemForestFromTree E' z' α₂ lmb₂ t) := by
  cases t with
  | node g cs =>
    simp [genMemForestFromTree, totalSize_append]
    rw [genRowMemForest_totalSize_alpha_irrel E E' z z' α₁ α₂ lmb₁ lmb₂ (extractNodeReqs g),
      genMemForestFromList_totalSize_alpha_irrel E E' z z' α₁ α₂ lmb₁ lmb₂ cs]

theorem genMemForestFromList_totalSize_alpha_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α₁ α₂ lmb₁ lmb₂ : K) (ts : List (NTree (GenComputeRow K))) :
    totalSize (genMemForestFromList E z α₁ lmb₁ ts) =
      totalSize (genMemForestFromList E' z' α₂ lmb₂ ts) := by
  cases ts with
  | nil => simp [genMemForestFromList]
  | cons t rest =>
    simp [genMemForestFromList, totalSize_append]
    rw [genMemForestFromTree_totalSize_alpha_irrel E E' z z' α₁ α₂ lmb₁ lmb₂ t,
      genMemForestFromList_totalSize_alpha_irrel E E' z z' α₁ α₂ lmb₁ lmb₂ rest]
end

theorem genMemoryForest_bfsForest_length_alpha_irrel (z z' α₁ α₂ lmb₁ lmb₂ : K)
    (inp inp' : Inputs K) (t : NTree (GenComputeRow K)) :
    (bfsForest (genMemoryForest z α₁ lmb₁ inp t)).length =
      (bfsForest (genMemoryForest z' α₂ lmb₂ inp' t)).length := by
  rw [bfsForest_length, bfsForest_length]
  simp only [genMemoryForest, threadGenForest_totalSize]
  exact genMemForestFromTree_totalSize_alpha_irrel (encC z) (encC z') z z' α₁ α₂ lmb₁ lmb₂
    (bfsAssign (airReorder t))

/-- **S2.**  The memory-forest shape does
not depend on the timestamp coin: `programMemShape α t = programMemShape α' t`.  This is what lets
the signed `hwin.2 : programMemShape αW t ≤ orderOf αW` feed a package whose `memRows` is
`programMemShape α t` (built at the timestamp coin `α`).  Follows `GenGenericSeedIrrel`'s
`*_lam_irrel` block with the timestamp split into `α₁ α₂`. -/
theorem programMemShape_alpha_irrel (α α' : K) (t : NTree (GenComputeRow K)) :
    programMemShape α t = programMemShape α' t := by
  unfold programMemShape programMemRows programMemRowsL
  exact genMemoryForest_bfsForest_length_alpha_irrel 0 0 α α' 0 0 _ _ t

/-- **S2 (W-gen).**  What the chain's `hordM` consumes when the memory walk runs at the separate
coin `αW` (`mwa := αW`): the memory rows of the package built at the timestamp `α`, below
`orderOf αW`, from the signed memory half of `hwin` (`programMemShape αW t ≤ orderOf αW`;
distinct walk line numbers `αW^i` over the memory rows). -/
theorem memRowsL_le_orderOf_of_shapeW {lmb z α αW : K} {t : NTree (GenComputeRow K)}
    (h : programMemShape αW t ≤ orderOf αW) :
    (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤ orderOf αW := by
  change programMemRowsL lmb z α t ≤ orderOf αW
  rw [← programMemShape_spec (lmb := lmb) z α t, programMemShape_alpha_irrel α αW t]
  exact h

end AlphaIrrel

variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- The generated carrier's `rowsBound` hypothesis from the program-level row counts (H1.5b Part 2a;
the chain form of `genBuildableOfProgram_rowsBound_of_hrows`, which needs `programCompRows`). -/
theorem genBuildableOfProgram_rowsBound_of_program {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K}
    (hrows : 3 * (bfsRows (airReorder t)).length < ringChar K ∧ programMemShape α t < ringChar K) :
    3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K := by
  have hc : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows =
      (bfsRows (airReorder t)).length := genComputeRows_bfsForest_length z α t
  have hm : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows = programMemShape α t :=
    (programMemShape_spec (lmb := chal.lam) z α t).symm
  rw [hc, hm]
  exact hrows


/-! ## 1. The acceptance antecedent

`nockCompiles_of_accepted` with `hb` and `haxis` derived.  This form keeps the generator's tree `t`
free, so it has no run hypothesis to fold the guard into and the guarded run `hG` is a binder of
its own: the trade here is **two premises for three**.  What it buys is the *kind* of premise —
three measurements of the program in place of two measurements of the compiled skeleton. -/

/-- **`nockCompiles_of_accepted` with `hb` and `haxis` discharged.**  For every Nock program the
generator accepts whose atoms and whose guarded run fit `q`.
-- -/
theorem nockCompiles_of_accepted_bounded {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreqn : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ n)
    (hrespn : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (memoryExtensionFold : K)
    (hord : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf computeWalkAlpha)
    (hordM : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
        hchar
        (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
        hbad hout hKszChar hprogCap hmemCap hfirst))
    (hax : FormRAxisBound
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h)
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.sampled
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h)
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = chal.lam
        ∧ package.optimized.family.memoryWalkAlpha = memoryWalkAlpha :=
  nockCompiles_of_accepted z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
    hmempos hcomp hmem B hB hwin hKsz hKsz2
    (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h) hq hchar
    (genComputeSkeleton_axisRange (by omega) hs hf hG h (genMemoryForest z α chal.lam (memInputs z) t))
    hbad hout hKszChar hprogCap hmemCap hfirst hmore stc bas packageOrbit hcap n hreqn hrespn hcard
    computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
    hord hordM hrows hG hF hax hbasis hwidth

/-! ## 2. The ROM antecedent, where the trade is even

`evalGRom q` (`GenGuardedRom.lean::evalGRom`) is the ROM transition function with the crashing
increment, so a single hypothesis `hgrom` delivers both `hrom` (by `evalGRom_le_evalRom`) and `hG`
(by `evalGRom_le_evalGBy`).  Against `nockCompiles_of_rom` this removes `hb` and `haxis` and adds
`hs` and `hf`, with `hrom` retyped rather than duplicated. -/

/-- **`nockCompiles_of_rom` with `hb` and `haxis` discharged**, at the guarded ROM antecedent.

-/
theorem nockCompiles_of_grom {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hseed : SeedGood z (romTree (K := K) (evalGRom_le_evalRom hgrom)))
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
    (hcomp : (bfsForest [genComputeRows z α (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length + 3 < B)
    (hKsz : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem).kMem ≤ Ksz)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))) n
        →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hconf
      (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
        (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreqn : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ n)
    (hrespn : (bfsForest (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (memoryExtensionFold : K)
    (hord : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest z α chal.lam (memInputs z)
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest z α chal.lam (memInputs z)
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf computeWalkAlpha)
    (hordM : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest z α chal.lam (memInputs z)
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest z α chal.lam (memInputs z)
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest z α chal.lam (memInputs z)
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest z α chal.lam (memInputs z)
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2
        (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
          (evalGRom_le_evalGBy hgrom)
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
        hchar
        (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
          (genMemoryForest z α chal.lam (memInputs z)
            (romTree (K := K) (evalGRom_le_evalRom hgrom))))
        hbad hout hKszChar hprogCap hmemCap hfirst))
    (hax : FormRAxisBound
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α (romTree (K := K) (evalGRom_le_evalRom hgrom))) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α (romTree (K := K) (evalGRom_le_evalRom hgrom))) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.sampled
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α (romTree (K := K) (evalGRom_le_evalRom hgrom))) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α (romTree (K := K) (evalGRom_le_evalRom hgrom))) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (genMemoryForest z α chal.lam (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = chal.lam
        ∧ package.optimized.family.memoryWalkAlpha = memoryWalkAlpha :=
  nockCompiles_of_accepted_bounded z α hz htwo a b c chal hinp hmi Ksz orbit horb
    (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hs hf (evalGRom_le_evalGBy hgrom)
    hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hq hchar hfirst hbad hout
    hKszChar hprogCap hmemCap stc bas packageOrbit hcap n hreqn hrespn hcard
    computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
    hord hordM hrows hF hmore hax hbasis hwidth


/-! ## 2b. The same, at the tree a configuration actually holds

`nockCompiles_of_grom`'s premises are stated at `romTree hrom`, which is `Classical.choose`; every
configuration records its facts at the literal tree its generator returned. -/

/-- **`nockCompiles_of_grom` with its trace-level premises at the generator's own tree.**  The
guarded ROM antecedent of `nockCompiles_of_grom`, the premise shape of
`nockCompiles_of_accepted_bounded`.
-- -/
theorem nockCompiles_of_grom_atTree {q Λ : ℕ}
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hgrom : evalGRom q fuel subject formula = some result)
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreqn : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ n)
    (hrespn : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (memoryExtensionFold : K)
    (hord : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom) h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
            (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom) h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
            (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf computeWalkAlpha)
    (hordM : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom) h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
            (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom) h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
            (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom) h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
            (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom) h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
            (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
          (evalGRom_le_evalGBy hgrom) h) hq
        hchar
        (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
          (genMemoryForest z α chal.lam (memInputs z) t))
        hbad hout hKszChar hprogCap hmemCap hfirst))
    (hax : FormRAxisBound
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h)
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.sampled
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α chal Ksz orbit horb a b c t
            (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h)
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α chal.lam (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = chal.lam
        ∧ package.optimized.family.memoryWalkAlpha = memoryWalkAlpha := by
  have ht : romTree (K := K) (evalGRom_le_evalRom hgrom) = t := by
    have h1 := romTree_spec (K := K) (evalGRom_le_evalRom hgrom)
    rw [h] at h1
    exact (congrArg Prod.fst (Except.ok.inj h1)).symm
  subst ht
  exact nockCompiles_of_grom z α hz htwo a b c chal hinp hmi Ksz orbit horb hgrom hs hf
    hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hq hchar hfirst hbad hout
    hKszChar hprogCap hmemCap stc bas packageOrbit hcap n hreqn hrespn hcard
    computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
    hord hordM hrows hF hmore hax hbasis hwidth

/-! ## 2c. P6.1 at the generator's own tree

`chal`/`hinp`/`hmi`, `stc`, the three trailing walk coins and the two memory-fold coins
are filled with the compiler defaults of §0.  `bas` and `packageOrbit` stay: they are
not freely inhabited (see §0).  `hKsz2` is restated at `compilerChallengeVector` — the
same inequality, the challenge argument specialised, no new hypothesis.
The claim conjunct is the in-tree form of `claimedResult = result`. -/

/-- **`nockCompiles_of_grom_atTree` with the freely-choosable P6.1 binders moved into
the `∃`.**  Instantiable at a live configuration (Tier A / `DotConfig769`).
-- -/
theorem nockCompiles_of_grom_atTree_p61 {q Λ : ℕ}
    (z α αW lmb : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hgrom : evalGRom q fuel subject formula = some result)
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hmemOrd : (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤ orderOf αW)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) (compilerChallengeVector α z a b c lmb) Ksz orbit horb
      (genComputeRows z α t)
      (genMemoryForest z α lmb (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α lmb (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α lmb (memInputs z) t)))
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreqn : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ n)
    (hrespn : (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (hrows : 3 * (bfsRows (airReorder t)).length < ringChar K ∧
      programMemShape α t < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        (compilerChallengeVector α z a b c lmb) rfl rfl
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
          (evalGRom_le_evalGBy hgrom) h) hq
        hchar
        (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
          (genMemoryForest z α lmb (memInputs z) t))
        hbad hout hKszChar hprogCap hmemCap hfirst))
    (hax : FormRAxisBound
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α (compilerChallengeVector α z a b c lmb) Ksz orbit horb a b c t
            (genMemoryForest z α lmb (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) (compilerChallengeVector α z a b c lmb) Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α lmb (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard (compilerWalkCoin (F := F) (K := K) packageOrbit) αW (compilerWalkCoin (F := F) (K := K) packageOrbit) (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α (compilerChallengeVector α z a b c lmb) Ksz orbit horb a b c t
            (genMemoryForest z α lmb (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) (compilerChallengeVector α z a b c lmb) Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α lmb (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard (compilerWalkCoin (F := F) (K := K) packageOrbit) αW (compilerWalkCoin (F := F) (K := K) packageOrbit) (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb)
          rfl rfl Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h)
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore
        (fun hge => by
          change (bfsForest [genComputeRows z α t]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows z α t]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤
            orderOf αW
          exact hmemOrd)).optimized.sampled
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
          Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
          hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α (compilerChallengeVector α z a b c lmb) Ksz orbit horb a b c t
            (genMemoryForest z α lmb (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) (compilerChallengeVector α z a b c lmb) Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α lmb (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard (compilerWalkCoin (F := F) (K := K) packageOrbit) αW (compilerWalkCoin (F := F) (K := K) packageOrbit) (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
            hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F) z α (compilerChallengeVector α z a b c lmb) Ksz orbit horb a b c t
            (genMemoryForest z α lmb (memInputs z) t) hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) (compilerChallengeVector α z a b c lmb) Ksz orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α lmb (memInputs z) t) hmempos hcomp hmem n hrespn)
          hcard (compilerWalkCoin (F := F) (K := K) packageOrbit) αW (compilerWalkCoin (F := F) (K := K) packageOrbit) (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
              Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq
              hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (by
              change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
                  Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
                  (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
                  (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
                  hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb) rfl rfl
            Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c (compilerChallengeVector α z a b c lmb)
          rfl rfl Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf (evalGRom_le_evalGBy hgrom) h)
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h (genMemoryForest z α lmb (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore
        (fun hge => by
          change (bfsForest [genComputeRows z α t]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows z α t]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤
            orderOf αW
          exact hmemOrd)).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_of_grom_atTree (hrows := genBuildableOfProgram_rowsBound_of_program hrows) z α hz htwo a b c
    (compilerChallengeVector α z a b c lmb) rfl rfl
    Ksz orbit horb h hs hf hgrom hseed hcoins hΛ hconf hmempos hcomp hmem
    B hB hwin hKsz hKsz2 hq hchar hfirst hbad hout
    hKszChar hprogCap hmemCap (compilerStateTagChar hq hchar) bas packageOrbit hcap
    n hreqn hrespn hcard
    (compilerWalkCoin (F := F) (K := K) packageOrbit)
    αW
    (compilerWalkCoin (F := F) (K := K) packageOrbit)
    (fun _ => 0) 0
    (fun hge => by
      change (bfsForest [genComputeRows z α t]).length ≤
        orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
      exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
        change 2 ≤ (bfsForest [genComputeRows z α t]).length
        exact hge))
    (fun hge => by
      change (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤
        orderOf αW
      exact hmemOrd)
    hF hmore hax hbasis hwidth

/-! ## 2d. P6.2 at the generator's own tree

`Ksz`, `B` and `n` are `compilerKszOf`, `orderOf α` and `compilerNOf`.  The five
comparisons they fed become `le_max` / `le_rfl`.  `orbit` and the `2^h` comparisons
stay (orbit inhabitation).  `hmempos` is `genComputeSkeleton_hmempos`.
  `hwin` / `hKszChar` / `hcard` are the
same inequalities at the chosen values, not new hypotheses. -/

/-- **`nockCompiles_of_grom_atTree_p61` with `Ksz`, `B`, `n` chosen and their
comparisons derived.**  Instantiable at Tier A.
-- -/
theorem nockCompiles_of_grom_atTree_p62 {q Λ : ℕ}
    (z α αW lmb : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hgrom : evalGRom q fuel subject formula = some result)
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (hwin : programAcc t + 3 < orderOf α)
    (hmemOrd : programMemShape αW t ≤ orderOf αW)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α lmb (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α lmb (memInputs z) t)))
    (hKszChar : compilerKszOfL lmb z α t < ringChar K)
    (hprogCap : programAcc t + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemRowsL lmb z α t + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound (compilerNOfL lmb z α t) (compilerNOfL lmb z α t)
      (Fintype.card K) < Fintype.card (K × K))
    (hrows : 3 * (bfsRows (airReorder t)).length < ringChar K ∧
      programMemShape α t < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        (compilerChallengeVector α z a b c lmb) rfl rfl
        (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
        (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
        (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
        (by
          change 2 * (genExactConfig (F := F) (compilerChallengeVector α z a b c lmb)
              (compilerKszOfL lmb z α t) orbit horb (genComputeRows z α t)
              (genMemoryForest z α lmb (memInputs z) t)
              (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem).kMem ≤
            compilerKszOfL lmb z α t
          change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
          exact compilerKsz_two_mul _ _)
        (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
          (evalGRom_le_evalGBy hgrom) h) hq
        hchar
        (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
          (genMemoryForest z α lmb (memInputs z) t))
        hbad hout hKszChar hprogCap hmemCap hfirst))
    (hax : FormRAxisBound
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          (compilerChallengeVector α z a b c lmb) rfl rfl
          (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
          (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
          (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
          (by
            change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom) h) hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
            (genMemoryForest z α lmb (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
            (compilerChallengeVector α z a b c lmb) rfl rfl
            (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
            (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
            (by
              change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
              (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
              (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap (compilerNOfL lmb z α t)
          (genExactExecution_requestIO_le (F := F) z α
            (compilerChallengeVector α z a b c lmb) (compilerKszOfL lmb z α t) orbit horb a b c t
            (genMemoryForest z α lmb (memInputs z) t)
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem (compilerNOfL lmb z α t)
            (compilerN_acc (programAcc t) (programMemRowsL lmb z α t)))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α z a b c lmb) (compilerKszOfL lmb z α t) orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α lmb (memInputs z) t)
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem (compilerNOfL lmb z α t)
            (compilerN_mem (programAcc t) (programMemRowsL lmb z α t))) hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
              (compilerChallengeVector α z a b c lmb) rfl rfl
              (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
              (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
              (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
              (by
                change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
                (evalGRom_le_evalGBy hgrom) h) hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
                (genMemoryForest z α lmb (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (compilerN_mem _ _) hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
            (compilerChallengeVector α z a b c lmb) rfl rfl
            (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
            (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
            (by
              change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
              (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
              (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
            (compilerChallengeVector α z a b c lmb) rfl rfl
            (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
            (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
            (by
              change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
              (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
              (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
            (compilerChallengeVector α z a b c lmb) rfl rfl
            (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
            (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
            (by
              change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
              (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
              (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap (compilerNOfL lmb z α t)
          (genExactExecution_requestIO_le (F := F) z α
            (compilerChallengeVector α z a b c lmb) (compilerKszOfL lmb z α t) orbit horb a b c t
            (genMemoryForest z α lmb (memInputs z) t)
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem (compilerNOfL lmb z α t)
            (compilerN_acc (programAcc t) (programMemRowsL lmb z α t)))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α z a b c lmb) (compilerKszOfL lmb z α t) orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α lmb (memInputs z) t)
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem (compilerNOfL lmb z α t)
            (compilerN_mem (programAcc t) (programMemRowsL lmb z α t))) hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
              (compilerChallengeVector α z a b c lmb) rfl rfl
              (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
              (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
              (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
              (by
                change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
                (evalGRom_le_evalGBy hgrom) h) hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
                (genMemoryForest z α lmb (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (compilerN_mem _ _) hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
            (compilerChallengeVector α z a b c lmb) rfl rfl
            (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
            (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
            (by
              change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
              (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
              (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          (compilerChallengeVector α z a b c lmb) rfl rfl
          (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
          (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
          (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
          (by
            change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom) h) hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
            (genMemoryForest z α lmb (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore
        (fun hge => by
          change (bfsForest [genComputeRows z α t]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows z α t]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.sampled
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          (compilerChallengeVector α z a b c lmb) rfl rfl
          (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
          (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
          (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
          (by
            change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom) h) hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
            (genMemoryForest z α lmb (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
            (compilerChallengeVector α z a b c lmb) rfl rfl
            (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
            (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
            (by
              change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
              (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
              (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap (compilerNOfL lmb z α t)
          (genExactExecution_requestIO_le (F := F) z α
            (compilerChallengeVector α z a b c lmb) (compilerKszOfL lmb z α t) orbit horb a b c t
            (genMemoryForest z α lmb (memInputs z) t)
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem (compilerNOfL lmb z α t)
            (compilerN_acc (programAcc t) (programMemRowsL lmb z α t)))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α z a b c lmb) (compilerKszOfL lmb z α t) orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α lmb (memInputs z) t)
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem (compilerNOfL lmb z α t)
            (compilerN_mem (programAcc t) (programMemRowsL lmb z α t))) hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
              (compilerChallengeVector α z a b c lmb) rfl rfl
              (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
              (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
              (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
              (by
                change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
                (evalGRom_le_evalGBy hgrom) h) hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
                (genMemoryForest z α lmb (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (compilerN_mem _ _) hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
            (compilerChallengeVector α z a b c lmb) rfl rfl
            (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
            (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
            (by
              change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
              (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
              (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
            (compilerChallengeVector α z a b c lmb) rfl rfl
            (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
            (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
            (by
              change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
              (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
              (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
            (compilerChallengeVector α z a b c lmb) rfl rfl
            (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
            (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
            (by
              change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
              (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
              (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap (compilerNOfL lmb z α t)
          (genExactExecution_requestIO_le (F := F) z α
            (compilerChallengeVector α z a b c lmb) (compilerKszOfL lmb z α t) orbit horb a b c t
            (genMemoryForest z α lmb (memInputs z) t)
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem (compilerNOfL lmb z α t)
            (compilerN_acc (programAcc t) (programMemRowsL lmb z α t)))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α z a b c lmb) (compilerKszOfL lmb z α t) orbit horb a b c
            (genComputeRows z α t) (genMemoryForest z α lmb (memInputs z) t)
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem (compilerNOfL lmb z α t)
            (compilerN_mem (programAcc t) (programMemRowsL lmb z α t))) hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
              (compilerChallengeVector α z a b c lmb) rfl rfl
              (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
              (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
              (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
              (by
                change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
                (evalGRom_le_evalGBy hgrom) h) hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
                (genMemoryForest z α lmb (memInputs z) t))
              hbad hout hKszChar hprogCap hmemCap hfirst)
            (compilerN_mem _ _) hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
            (compilerChallengeVector α z a b c lmb) rfl rfl
            (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
            (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
            (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
            (by
              change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
              (evalGRom_le_evalGBy hgrom) h) hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
              (genMemoryForest z α lmb (memInputs z) t))
            hbad hout hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          (compilerChallengeVector α z a b c lmb) rfl rfl
          (compilerKszOfL lmb z α t) orbit horb h hseed hcoins hΛ hconf
          (genComputeSkeleton_hmempos z α (memInputs z) h) hcomp hmem
          (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
          (by
            change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf
            (evalGRom_le_evalGBy hgrom) h) hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom) h
            (genMemoryForest z α lmb (memInputs z) t))
          hbad hout hKszChar hprogCap hmemCap hfirst)
        hmore
        (fun hge => by
          change (bfsForest [genComputeRows z α t]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows z α t]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW := by
  let Ksz := compilerKszOfL lmb z α t
  let n := compilerNOfL lmb z α t
  let B := orderOf α
  have hmempos := genComputeSkeleton_hmempos (lmb := lmb) z α (memInputs z) h
  have hKsz2 :
      2 * (genExactConfig (F := F) (compilerChallengeVector α z a b c lmb) Ksz orbit horb
        (genComputeRows z α t) (genMemoryForest z α lmb (memInputs z) t)
        hmempos hcomp hmem).kMem ≤ Ksz := by
    change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
    exact compilerKsz_two_mul _ _
  exact nockCompiles_of_grom_atTree_p61 (hrows := hrows) z α αW lmb hz htwo a b c
    Ksz orbit horb h hs hf hgrom hseed hcoins hΛ hconf hmempos hcomp hmem
    B le_rfl hwin (memRowsL_le_orderOf_of_shapeW hmemOrd) (compilerKsz_acc _ _) hKsz2 hq hchar hfirst hbad hout
    hKszChar hprogCap hmemCap bas packageOrbit hcap
    n (compilerN_acc (programAcc t) (programMemRowsL lmb z α t)) (compilerN_mem (programAcc t) (programMemRowsL lmb z α t)) hcard hF hmore hax hbasis hwidth


namespace GoodSeed

/-! ## 3. And with the NPR seed chosen as well

No premise of that theorem is
relocated — `hb` and `haxis` are supplied, not restated. -/

/-- **`GoodSeed.nockCompiles_of_rom_atRomSeed` with `hb` and `haxis` discharged.**  The seed is the
compiler's own choice and the two skeleton-level premises are gone; what remains about the program
is `hgrom`, `hs`, `hf` and the arithmetic side conditions.
-- -/
theorem nockCompiles_of_grom_atRomSeed {q Λ : ℕ}
    (α : K) (htwo : (2 : K) ≠ 0) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hwinNouns : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hseedcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length < Fintype.card K)
    (chal : ChallengeVector K)
    (hinp : chal.computeInputs = ⟨α, (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard), a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hseed : SeedGood (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) (romTree (K := K) (evalGRom_le_evalRom hgrom)))
    (hcoins : ComputeCoinsGeneric (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α a b c
      (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hmempos : 0 < (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
    (hcomp : (bfsForest [genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length + 3 < B)
    (hKsz : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem).kMem ≤ Ksz)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))) n
        →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreqn : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ n)
    (hrespn : (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (computeWalkAlpha memoryWalkAlpha walkGamma : K)
    (memoryScalarChallenge : Fin 4 → F) (memoryExtensionFold : K)
    (hord : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c chal hinp hmi Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c chal hinp hmi Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf computeWalkAlpha)
    (hordM : 2 ≤
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c chal hinp hmi Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c chal hinp hmi Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c chal hinp hmi Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c chal hinp hmi Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
        (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
        (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
        htwo a b c chal hinp hmi Ksz orbit horb
        (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2
        (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
          (evalGRom_le_evalGBy hgrom)
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
        hq hchar
        (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
        (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
        (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
          hwinNouns hseedcard)
        hKszChar hprogCap hmemCap hfirst))
    (hax : FormRAxisBound
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c chal hinp hmi Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c chal hinp hmi Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            chal Ksz orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
                htwo a b c chal hinp hmi Ksz orbit horb
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
                hmempos hcomp hmem B hB hwin hKsz hKsz2
                (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                  (evalGRom_le_evalGBy hgrom)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
                hq hchar
                (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
                (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
                (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
                  hwinNouns hseedcard)
                hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c chal hinp hmi Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c chal hinp hmi Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c chal hinp hmi Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            chal Ksz orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
                htwo a b c chal hinp hmi Ksz orbit horb
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
                hmempos hcomp hmem B hB hwin hKsz hKsz2
                (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                  (evalGRom_le_evalGBy hgrom)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
                hq hchar
                (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
                (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
                (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
                  hwinNouns hseedcard)
                hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c chal hinp hmi Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c chal hinp hmi Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.sampled
      (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c chal hinp hmi Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c chal hinp hmi Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            chal Ksz orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
                htwo a b c chal hinp hmi Ksz orbit horb
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
                hmempos hcomp hmem B hB hwin hKsz hKsz2
                (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                  (evalGRom_le_evalGBy hgrom)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
                hq hchar
                (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
                (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
                (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
                  hwinNouns hseedcard)
                hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c chal hinp hmi Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c chal hinp hmi Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c chal hinp hmi Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          stc bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            chal Ksz orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F) chal Ksz orbit horb a b c
            (genComputeRows
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α chal.lam
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hrespn)
          hcard computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge
          memoryExtensionFold (interCard_of_unionBound _ (by
            change (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
                htwo a b c chal hinp hmi Ksz orbit horb
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
                hmempos hcomp hmem B hB hwin hKsz hKsz2
                (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                  (evalGRom_le_evalGBy hgrom)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
                hq hchar
                (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
                (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
                (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
                  hwinNouns hseedcard)
                hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤ n
            exact hrespn) hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c chal hinp hmi Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c chal hinp hmi Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds (lmb := chal.lam) hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        hmore hord hordM hrows).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = chal.lam :=
  nockCompiles_of_rom_atRomSeed α htwo a b c (evalGRom_le_evalRom hgrom) hΛ hconf
    hwinNouns hseedcard chal hinp hmi Ksz orbit horb hseed hcoins hmempos hcomp hmem
    B hB hwin hKsz hKsz2
    (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf (evalGRom_le_evalGBy hgrom)
      (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
    hq hchar
    (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
      (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
    hKszChar hprogCap hmemCap hfirst hmore stc bas packageOrbit hcap n hreqn hrespn hcard
    computeWalkAlpha memoryWalkAlpha walkGamma memoryScalarChallenge memoryExtensionFold
    hord hordM hrows (evalGRom_le_evalGBy hgrom) hF hax hbasis hwidth

/-! ## 4. P6.1 at the chosen seed

Same restatement as `nockCompiles_of_grom_atTree_p61`, on the current best-form theorem.
`chal`/`hinp`/`hmi` become `compilerChallengeVector` at `romSeed`; `stc` is
`compilerStateTagChar`; trailing walk coins are `compilerWalkCoin packageOrbit`
; memory-fold coins stay `0`.  `bas` and
`packageOrbit` stay (finding: not freely inhabited).  No new hypothesis.  The claim
conjunct is kept. -/

/-- **`nockCompiles_of_grom_atRomSeed` with the freely-choosable P6.1 binders moved into
the `∃`.**  This is the best-form restatement; non-vacuity is the at-tree form
(`nockCompiles_of_grom_atTree_p61`), because `romSeed` is `Classical.choose` (`P6.4`).
-- -/
theorem nockCompiles_p61 {q Λ : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hwinNouns : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hseedcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length < Fintype.card K)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hseed : SeedGood (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) (romTree (K := K) (evalGRom_le_evalRom hgrom)))
    (hcoins : ComputeCoinsGeneric (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α a b c
      (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hmempos : 0 < (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
    (hcomp : (bfsForest [genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length + 3 < B)
    (hmemOrd : (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ orderOf αW)
    (hKsz : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F)
      (compilerChallengeVector α (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
      Ksz orbit horb (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom))) hmempos hcomp hmem).kMem ≤ Ksz)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hfirst : ∀ n, InTree (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))) n
        →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hKszChar : Ksz < ringChar K)
    (hprogCap : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length + 1 ≤ 2 ^ orbit.h)
    (hmemCap : (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreqn : accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ n)
    (hrespn : (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
        (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
        (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
        htwo a b c
        (compilerChallengeVector α
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
        rfl rfl Ksz orbit horb
        (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2
        (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
          (evalGRom_le_evalGBy hgrom)
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
        hq hchar
        (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
        (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
        (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
          hwinNouns hseedcard)
        hKszChar hprogCap hmemCap hfirst) := by later_seed_zeros)
    (hax : FormRAxisBound
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            Ksz orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            Ksz orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hrespn)
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl Ksz orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap hfirst)
            (by
              change (bfsForest (genMemoryForest
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
                  (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            Ksz orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            Ksz orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hrespn)
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl Ksz orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap hfirst)
            (by
              change (bfsForest (genMemoryForest
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
                  (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        hmore
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact hmemOrd)).optimized.sampled
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            Ksz orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            Ksz orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hrespn)
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl Ksz orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap hfirst)
            (by
              change (bfsForest (genMemoryForest
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
                  (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap n
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            Ksz orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hreqn)
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            Ksz orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem n hrespn)
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl Ksz orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem B hB hwin hKsz hKsz2
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap hfirst)
            (by
              change (bfsForest (genMemoryForest
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
                  (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ n
              exact hrespn)
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl Ksz orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem B hB hwin hKsz hKsz2
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl Ksz orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem B hB hwin hKsz hKsz2
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        hmore
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact hmemOrd)).optimized.basis)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb :=
  nockCompiles_of_grom_atRomSeed (hrows := genBuildableOfProgram_rowsBound_of_program hrows) α htwo a b c hgrom hs hf hΛ hconf
    hwinNouns hseedcard
    (compilerChallengeVector α (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
    rfl rfl Ksz orbit horb hseed hcoins hmempos hcomp hmem
    B hB hwin hKsz hKsz2 hq hchar hfirst
    hKszChar hprogCap hmemCap (compilerStateTagChar hq hchar) bas packageOrbit hcap
    n hreqn hrespn hcard
    (compilerWalkCoin (F := F) (K := K) packageOrbit)
    αW
    (compilerWalkCoin (F := F) (K := K) packageOrbit)
    (fun _ => 0) 0
    (fun hge => by
      change (bfsForest [genComputeRows
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
        orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
      exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
        change 2 ≤ (bfsForest [genComputeRows
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
        exact hge))
    (fun hge => by
      change (bfsForest (genMemoryForest
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
          (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
          (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
        orderOf αW
      exact hmemOrd)
    hF hmore hax hbasis hwidth

/-! ## 5. P6.2 at the chosen seed

`Ksz`/`B`/`n` become `compilerKszOf` / `orderOf α` / `compilerNOf`.  Their five
comparisons (`hKsz`, `hKsz2`, `hB`, `hreqn`, `hrespn`) are `le_max` / `le_rfl`.
`orbit` and the `2^h` comparisons stay.  `hmempos` stays.  `hwin` / `hKszChar` /
`hcard` are restated at the chosen values — same inequalities, not new premises.
The claim conjunct is kept. -/

/-- **`nockCompiles_p61` with `Ksz`, `B`, `n` chosen and their comparisons derived.**
Best-form restatement; non-vacuity is the at-tree form (`nockCompiles_of_grom_atTree_p62`).
-- -/
theorem nockCompiles_p62 {q Λ : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0) (a b c : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hwinNouns : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hseedcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length < Fintype.card K)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hseed : SeedGood (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) (romTree (K := K) (evalGRom_le_evalRom hgrom)))
    (hcoins : ComputeCoinsGeneric (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α a b c
      (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hmempos : 0 < (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
    (hcomp : (bfsForest [genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hKszChar : compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemRowsL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound
      (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K))
    (hfirst : ∀ n, InTree (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))) n
        →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : BuildableAxisWitness.LaterSeedZeros
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
        (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
        (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
        htwo a b c
        (compilerChallengeVector α
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
        rfl rfl
        (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romTree (K := K) (evalGRom_le_evalRom hgrom)))
        orbit horb
        (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
        hmempos hcomp hmem (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
        (by
          change 2 * programMemRootsL lmb
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
            compilerKsz
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          exact compilerKsz_two_mul _ _)
        (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
          (evalGRom_le_evalGBy hgrom)
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
        hq hchar
        (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
        (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
        (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
          hwinNouns hseedcard)
        hKszChar hprogCap hmemCap hfirst) := by later_seed_zeros)
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F)
    (hax : FormRAxisBound
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap hfirst)
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap hfirst)
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        hmore
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.sampled
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap hfirst)
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst)
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap hfirst)
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap hfirst))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap hfirst)
        hmore
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.basis) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb := by
  let z := romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard
  let t := romTree (K := K) (evalGRom_le_evalRom hgrom)
  let Ksz := compilerKszOfL lmb z α t
  let n := compilerNOfL lmb z α t
  let B := orderOf α
  have hKsz2 :
      2 * (genExactConfig (F := F)
        (compilerChallengeVector α z a b c lmb) Ksz orbit horb
        (genComputeRows z α t) (genMemoryForest z α lmb (memInputs z) t)
        hmempos hcomp hmem).kMem ≤ Ksz := by
    change 2 * programMemRootsL lmb z α t ≤ compilerKsz (programAcc t) (programMemRootsL lmb z α t)
    exact compilerKsz_two_mul _ _
  exact nockCompiles_p61 (hrows := hrows) α αW lmb htwo a b c hgrom hs hf hΛ hconf hwinNouns hseedcard
    Ksz orbit horb hseed hcoins hmempos hcomp hmem
    B le_rfl hwin (memRowsL_le_orderOf_of_shapeW hmemOrd) (compilerKsz_acc _ _) hKsz2 hq hchar hfirst
    hKszChar hprogCap hmemCap bas packageOrbit hcap
    n (compilerN_acc (programAcc t) (programMemRowsL lmb z α t)) (compilerN_mem (programAcc t) (programMemRowsL lmb z α t)) hcard hF hmore
    hax hbasis hwidth

/-! ## 6. P6.3 — compute coins as a compiler choice

`hcoins` is `GS`'s counted event: good `(a,b,c)` exist as soon as the compute-row
count is below `|K|` (`exists_computeCoinsGeneric_airReorder`).  That inequality
is not a new premise — `hseedcard` plus `seedBudget_gt_rows` give it, and
`bfsForest_bfsAssign_length` matches the two row counts.

`hseed : SeedGood (romSeed …) _` is **not** discharged.  `romSeed` avoids
`{0} ∪ p8.badSeeds ∪ sizeWindowFailureSeeds` (`KM`); `SeedGood` is the complement
of a different set (`cons`-dyck / OP5-agree / OP3-size, `GenDyckBadSeed`).  Closing
it at `romSeed` needs a per-row shape bound and an enlarged choose, which is a
finding, not a new event in the soundness bound.  `a,b,c` move into the `∃` with
`hcoins`; `hseed` stays. -/

/-- `hseedcard`'s row count is the AIR-ordered BFS length. -/
theorem airReorder_rows_lt_card_of_seedBudget {Λ : ℕ} (hΛ : 1 ≤ Λ)
    (t : NTree (GenComputeRow K))
    (h : seedBudget Λ (bfsForest [bfsAssign (airReorder t)]).length < Fintype.card K) :
    (bfsForest [airReorder t]).length < Fintype.card K := by
  have := rows_lt_card_of_seedBudget (K := K) hΛ h
  rwa [bfsForest_bfsAssign_length] at this

/-- **`nockCompiles_p62` with `(a,b,c)` / `hcoins` chosen by the `GS` pigeonhole.**
`hseed` stays (finding).  Best-form restatement; non-vacuity is the at-tree witness
, because `romSeed` is `Classical.choose` (`P6.4`).
-- -/
theorem nockCompiles_p63 {q Λ : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hwinNouns : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hseedcard : seedBudget Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length < Fintype.card K)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hseed : SeedGood (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) (romTree (K := K) (evalGRom_le_evalRom hgrom)))
    (hmempos : 0 < (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
    (hcomp : (bfsForest [genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hKszChar : compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemRowsL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound
      (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K))
    (hfirst : ∀ (a b c : K), ∀ n, InTree (bfsAssign (airReorder (romTree (K := K)
        (evalGRom_le_evalRom hgrom)))) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : ∀ (a b c : K)
        (hcoins : ComputeCoinsGeneric
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α a b c
          (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      BuildableAxisWitness.LaterSeedZeros
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
          (by
            change 2 * programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c)))
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F)
    (hax : ∀ (a b c : K)
        (hcoins : ComputeCoinsGeneric
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α a b c
          (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      FormRAxisBound
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (hmore a b c hcoins)
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.sampled
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
              (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
            (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
          (romSeed_ne_zero hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hseed hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeed_notMem_badSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard)
          (romSeed_notMem_sizeWindowFailureSeeds hΛ (evalGRom_le_evalRom hgrom) hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (hmore a b c hcoins)
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.basis) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb := by
  let z := romSeed hΛ (evalGRom_le_evalRom hgrom) hconf α hwinNouns hseedcard
  let t := romTree (K := K) (evalGRom_le_evalRom hgrom)
  have hrowsCard : (bfsForest [airReorder t]).length < Fintype.card K :=
    airReorder_rows_lt_card_of_seedBudget hΛ t hseedcard
  obtain ⟨a, b, c, hcoins⟩ := exists_computeCoinsGeneric_airReorder z α t hrowsCard
  exact nockCompiles_p62 (hrows := hrows) α αW lmb htwo a b c hgrom hs hf hΛ hconf hwinNouns hseedcard
    orbit horb hseed hcoins hmempos hcomp hmem
    hwin hmemOrd hq hchar hKszChar hprogCap hmemCap bas packageOrbit hcap hcard
    (hfirst a b c) hF (hmore a b c hcoins) hbasis hwidth (hax a b c hcoins)

/-! ## 7. P6.4 — joint pigeonhole: `hseed` is `choose_spec`

The three `SeedGood` shapes are theorems of `genComputeSkeleton` plus
`hconf`/`hs`/`hf`/`hgrom` (`rowBad_card_le_of_generated`). The Dyck-bad
set therefore folds into the compiler choose (`romSeedVcomp`); `hseed`
is `romSeedVcomp_seedGood`. `hseedcard` is restated at the enlarged
`seedBudgetVcomp` — a compiler numeral, not a new soundness summand. `bas`/`packageOrbit`/`orbit`/`hcard` stay. -/

/-- `hseedcard` at the joint budget still gives `rows < |K|`. -/
theorem airReorder_rows_lt_card_of_seedBudgetVcomp {Λ : ℕ} (hΛ : 1 ≤ Λ)
    (t : NTree (GenComputeRow K))
    (h : seedBudgetVcomp Λ (bfsForest [bfsAssign (airReorder t)]).length
        < Fintype.card K) :
    (bfsForest [airReorder t]).length < Fintype.card K := by
  have := rows_lt_card_of_seedBudgetVcomp (K := K) hΛ h
  rwa [bfsForest_bfsAssign_length] at this


theorem nockCompiles_p64 {q Λ : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hwinNouns : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hmempos : 0 < (bfsForest (genMemoryForest
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
      (memInputs (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
      (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
    (hcomp : (bfsForest [genComputeRows
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
      (memInputs (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
      (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hKszChar : compilerKszOfL lmb
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemRowsL lmb
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound
      (compilerNOfL lmb
        (romSeedVcomp hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOfL lmb
        (romSeedVcomp hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K))
    (hfirst : ∀ (a b c : K), ∀ n, InTree (bfsAssign (airReorder (romTree (K := K)
        (evalGRom_le_evalRom hgrom)))) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : ∀ (a b c : K)
        (hcoins : ComputeCoinsGeneric
          (romSeedVcomp hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          α a b c
          (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      BuildableAxisWitness.LaterSeedZeros
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          α
          (romSeedVcomp_ne_zero hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            a b c lmb)
          rfl rfl
          (compilerKszOfL lmb
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
          (romSeedVcomp_seedGood hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          hcoins hΛ hconf
          (genComputeSkeleton_hmempos
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            α
            (memInputs (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hcomp hmem (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
          (by
            change 2 * (genExactConfig (F := F)
                (compilerChallengeVector α
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  a b c lmb)
                (compilerKszOfL lmb
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                orbit horb
                (genComputeRows
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (genMemoryForest
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  α lmb
                  (memInputs (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard))
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (genComputeSkeleton_hmempos
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  α
                  (memInputs (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard))
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
                hcomp hmem).kMem ≤
              compilerKszOfL lmb
                (romSeedVcomp hq hchar hs hf
                  (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                  hΛ hconf α hwinNouns hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom))
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf
                  (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                  hΛ hconf α hwinNouns hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c)))
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F)
    (hax : ∀ (a b c : K)
        (hcoins : ComputeCoinsGeneric
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α a b c
          (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      FormRAxisBound
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (hmore a b c hcoins)
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.sampled
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            hmempos hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
              hmempos hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            hmempos hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
          hmempos hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (hmore a b c hcoins)
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.basis) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW := by
  let hrom := evalGRom_le_evalRom hgrom
  let hG := evalGRom_le_evalGBy hgrom
  let z := romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwinNouns hseedcard
  let t := romTree (K := K) hrom
  have hz : z ≠ 0 := romSeedVcomp_ne_zero hq hchar hs hf hG hrom hΛ hconf α hwinNouns hseedcard
  have hseed : SeedGood z t :=
    romSeedVcomp_seedGood hq hchar hs hf hG hrom hΛ hconf α hwinNouns hseedcard
  have hbad := romSeedVcomp_notMem_badSeeds (lmb := lmb) hq hchar hs hf hG hrom hΛ hconf α hwinNouns hseedcard
  have hout :=
    romSeedVcomp_notMem_sizeWindowFailureSeeds (lmb := lmb) hq hchar hs hf hG hrom hΛ hconf α hwinNouns hseedcard
  have hrowsCard : (bfsForest [airReorder t]).length < Fintype.card K :=
    airReorder_rows_lt_card_of_seedBudgetVcomp hΛ t hseedcard
  obtain ⟨a, b, c, hcoins⟩ := exists_computeCoinsGeneric_airReorder z α t hrowsCard
  let _ := hmempos
  exact nockCompiles_of_grom_atTree_p62 (hrows := hrows) z α αW lmb hz htwo a b c
    orbit horb (romTree_spec (K := K) hrom) hs hf hgrom hseed hcoins
    hΛ hconf hcomp hmem
    hwin hmemOrd hq hchar (hfirst a b c) hbad hout
    hKszChar hprogCap hmemCap bas packageOrbit hcap hcard
    hF (hmore a b c hcoins) (hax a b c hcoins) hbasis hwidth

/-- **`nockCompiles_p64` with `hmempos` derived.**  Always-on `mem_record₁`
; `genMemoryForest_bfsForest_length_pos` is
seed-independent.  Instrument: explicit binders `24 → 23`.
-- -/
theorem nockCompiles_p65 {q Λ : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hwinNouns : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hcomp : (bfsForest [genComputeRows
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
      (memInputs (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
      (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hKszChar : compilerKszOfL lmb
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemRowsL lmb
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound
      (compilerNOfL lmb
        (romSeedVcomp hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOfL lmb
        (romSeedVcomp hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K))
    (hfirst : ∀ (a b c : K), ∀ n, InTree (bfsAssign (airReorder (romTree (K := K)
        (evalGRom_le_evalRom hgrom)))) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : ∀ (a b c : K)
        (hcoins : ComputeCoinsGeneric
          (romSeedVcomp hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          α a b c
          (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      BuildableAxisWitness.LaterSeedZeros
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          α
          (romSeedVcomp_ne_zero hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            a b c lmb)
          rfl rfl
          (compilerKszOfL lmb
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
          (romSeedVcomp_seedGood hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          hcoins hΛ hconf
          (genComputeSkeleton_hmempos
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            α
            (memInputs (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hcomp hmem (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
          (by
            change 2 * (genExactConfig (F := F)
                (compilerChallengeVector α
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  a b c lmb)
                (compilerKszOfL lmb
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                orbit horb
                (genComputeRows
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (genMemoryForest
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  α lmb
                  (memInputs (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard))
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (genComputeSkeleton_hmempos
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  α
                  (memInputs (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard))
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
                hcomp hmem).kMem ≤
              compilerKszOfL lmb
                (romSeedVcomp hq hchar hs hf
                  (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                  hΛ hconf α hwinNouns hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom))
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf
                  (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                  hΛ hconf α hwinNouns hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    hΛ hconf α hwinNouns hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c)))
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F)
    (hax : ∀ (a b c : K)
        (hcoins : ComputeCoinsGeneric
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α a b c
          (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      FormRAxisBound
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
          (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
              (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
              (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
          (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (hmore a b c hcoins)
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.sampled
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
          (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
              (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
              (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
                hwinNouns hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
              hwinNouns hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) hcoins hΛ hconf
          (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α
            hwinNouns hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (hmore a b c hcoins)
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.basis) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p64 (hrows := hrows) α αW lmb htwo hgrom hs hf hΛ hconf hwinNouns hseedcard hq hchar
    orbit horb
    (genMemoryForest_bfsForest_length_pos
      (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard)
      α
      (memInputs (romSeedVcomp hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ hconf α hwinNouns hseedcard))
      (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
    hcomp hmem hwin hmemOrd hKszChar hprogCap hmemCap bas packageOrbit hcap hcard
    hfirst hF hmore hbasis hwidth hax

/-- Compiler seed at the single §1 window.  Padding `1 ≤ Λ` and
`hwinNouns` are derived; not new binders. -- the paper -/
noncomputable def romSeedVcompOfWindow {q Λ : ℕ}
    (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) : K :=
  romSeedVcomp hq hchar hs hf hG hrom (one_le_of_hΛ_conf hΛ) hΛ α
    (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
      (romTree_spec (K := K) hrom) hΛ [])
    hseedcard

/-- **`nockCompiles_p65` with one window premise.**  `hΛ` is
`TraceConfined` — §1 `leafBound … ≤ Λ`.
Dummy `1 ≤ Λ` and `hwinNouns` are derived (`one_le_of_hΛ_conf`,
`sizeWindowNounsBoundedBy_of_traceConfined`).  Instrument: `23 → 21`.
-- -/
theorem nockCompiles_p66 {q Λ : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hcomp : (bfsForest [genComputeRows
      (romSeedVcompOfWindow hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest
      (romSeedVcompOfWindow hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α lmb
      (memInputs (romSeedVcompOfWindow hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard))
      (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤ 2 ^ orbit.h)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hKszChar : compilerKszOfL lmb
      (romSeedVcompOfWindow hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemRowsL lmb
      (romSeedVcompOfWindow hq hchar hs hf
        (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound
      (compilerNOfL lmb
        (romSeedVcompOfWindow hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOfL lmb
        (romSeedVcompOfWindow hq hchar hs hf
          (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard) α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K))
    (hfirst : ∀ (a b c : K), ∀ n, InTree (bfsAssign (airReorder (romTree (K := K)
        (evalGRom_le_evalRom hgrom)))) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : ∀ (a b c : K)
        (hcoins : ComputeCoinsGeneric
          (romSeedVcomp hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          α a b c
          (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      BuildableAxisWitness.LaterSeedZeros
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          α
          (romSeedVcomp_ne_zero hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            a b c lmb)
          rfl rfl
          (compilerKszOfL lmb
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
          (romSeedVcomp_seedGood hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          hcoins (one_le_of_hΛ_conf hΛ) hΛ
          (genComputeSkeleton_hmempos
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            α
            (memInputs (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard))
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hcomp hmem (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
          (by
            change 2 * (genExactConfig (F := F)
                (compilerChallengeVector α
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  a b c lmb)
                (compilerKszOfL lmb
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                orbit horb
                (genComputeRows
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (genMemoryForest
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  α lmb
                  (memInputs (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard))
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (genComputeSkeleton_hmempos
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  α
                  (memInputs (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard))
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
                hcomp hmem).kMem ≤
              compilerKszOfL lmb
                (romSeedVcomp hq hchar hs hf
                  (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                  (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom))
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf
                  (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                  (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c)))
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F)
    (hax : ∀ (a b c : K)
        (hcoins : ComputeCoinsGeneric
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α a b c
          (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      FormRAxisBound
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
          (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
              (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
              (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
                (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
              (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
              (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
              (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
              (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
                (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
              (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
          (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (hmore a b c hcoins)
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.sampled
      (buildFullPackage (hrows := genBuildableOfProgram_rowsBound_of_program hrows)
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
          (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
              (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
              (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
                (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
              (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (commitmentResidualOfZero
          (genDataOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
              (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (inputsOfCarrier_challenges
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
              (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c))
          (compilerStateTagChar hq hchar) bas packageOrbit hcap
          (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          (genExactExecution_requestIO_le (F := F)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (romTree (K := K) (evalGRom_le_evalRom hgrom))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_acc
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          (genExactExecution_responseIO_le (F := F)
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb a b c
            (genComputeRows (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem
            (compilerNOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))))
          hcard
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          αW
          (compilerWalkCoin (F := F) (K := K) packageOrbit)
          (fun _ => 0) 0
          (interCard_of_unionBound
            (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              htwo a b c
              (compilerChallengeVector α
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
              rfl rfl
              (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              orbit horb
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
              (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
              (compilerKsz_acc
                (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom))))
              (by
                change 2 * programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                  compilerKsz
                    (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                    (programMemRootsL lmb
                      (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                      (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                exact compilerKsz_two_mul _ _)
              (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
                (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
              hq hchar
              (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
                (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
              (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
                (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              hKszChar hprogCap hmemCap (hfirst a b c))
            (compilerN_mem
              (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            hcard)
          (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ)
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            htwo a b c
            (compilerChallengeVector α
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
            rfl rfl
            (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            orbit horb
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
            (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
            (compilerKsz_acc
              (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
              (programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))))
            (by
              change 2 * programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
                compilerKsz
                  (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                  (programMemRootsL lmb
                    (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                    (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              exact compilerKsz_two_mul _ _)
            (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
              (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
            hq hchar
            (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
            (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
              (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            hKszChar hprogCap hmemCap (hfirst a b c)))
        (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
          (romSeedVcomp_ne_zero hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) a b c lmb)
          rfl rfl
          (compilerKszOfL lmb (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
            (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) (romSeedVcomp_seedGood hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) hcoins (one_le_of_hΛ_conf hΛ) hΛ
          (genMemoryForest_bfsForest_length_pos (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))) hcomp hmem (orderOf α) le_rfl hwin
          (compilerKsz_acc
            (accAt (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))
              (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length)
            (programMemRootsL lmb
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))))
          (by
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          hKszChar hprogCap hmemCap (hfirst a b c))
        (hmore a b c hcoins)
        (fun hge => by
          change (bfsForest [genComputeRows
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
              (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length ≤
            orderOf (compilerWalkCoin (F := F) (K := K) packageOrbit)
          exact compilerWalkOrder_of_le packageOrbit (hcomp.trans hcap) (by
            change 2 ≤ (bfsForest [genComputeRows
                (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
                (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
            exact hge))
        (fun hge => by
          change (bfsForest (genMemoryForest
              (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α lmb
              (memInputs (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard))
              (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length ≤
            orderOf αW
          exact memRowsL_le_orderOf_of_shapeW hmemOrd)).optimized.basis) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW := by
  unfold romSeedVcompOfWindow at hcomp hmem hKszChar hmemCap hcard
  exact nockCompiles_p65 (hrows := hrows) α αW lmb htwo hgrom hs hf (one_le_of_hΛ_conf hΛ) hΛ
    (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
      (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
      ([] : List (NTree (GenMemoryRow K))))
    hseedcard hq hchar orbit horb hcomp hmem hwin hmemOrd hKszChar hprogCap hmemCap
    bas packageOrbit hcap hcard hfirst hF hmore hbasis hwidth hax

/-- **`nockCompiles_p66` with seed-free counts.**  Forest shape is
noun/axis (`recordTreeSize`); `encC z` only labels.  Binders `hmem`,
`hmemCap`, `hKszChar`, `hcard` are stated at dummy seed `0` and
transported by `programMemRows_irrel` / `compilerNOf_irrel` /
`compilerKszOf_irrel`.  `hcomp` is the AIR-ordered BFS length
(`genComputeRows_bfsForest_length`).  Count unchanged; kind improved.
-- -/
theorem nockCompiles_p67 {q Λ : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hcomp : (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length
      ≤ 2 ^ orbit.h)
    (hmem : programMemShape α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ 2 ^ orbit.h)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hKszChar : compilerKszOfL lmb 0 α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemShape α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound
      (compilerNOfL lmb 0 α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOfL lmb 0 α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K))
    (hfirst : ∀ (a b c : K), ∀ n, InTree (bfsAssign (airReorder (romTree (K := K)
        (evalGRom_le_evalRom hgrom)))) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hmore : ∀ (a b c : K)
        (hcoins : ComputeCoinsGeneric
          (romSeedVcomp hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          α a b c
          (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      BuildableAxisWitness.LaterSeedZeros
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
          (romSeedVcomp hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          α
          (romSeedVcomp_ne_zero hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          htwo a b c
          (compilerChallengeVector α
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            a b c lmb)
          rfl rfl
          (compilerKszOfL lmb
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
          orbit horb
          (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
          (romSeedVcomp_seedGood hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          hcoins (one_le_of_hΛ_conf hΛ) hΛ
          (genComputeSkeleton_hmempos
            (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
            α
            (memInputs (romSeedVcomp hq hchar hs hf
              (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard))
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          (by
            rw [genComputeRows_bfsForest_length (romSeedVcomp hq hchar hs hf
                (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                (one_le_of_hΛ_conf hΛ) hΛ α
                (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
                  ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              α (romTree (K := K) (evalGRom_le_evalRom hgrom))]
            exact hcomp)
          (by
            change programMemRowsL lmb (romSeedVcomp hq hchar hs hf
                (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                (one_le_of_hΛ_conf hΛ) hΛ α
                (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
                  ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ 2 ^ orbit.h
            rw [← programMemShape_spec]
            exact hmem) (orderOf α) le_rfl hwin (compilerKsz_acc _ _)
          (by
            change 2 * (genExactConfig (F := F)
                (compilerChallengeVector α
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  a b c lmb)
                (compilerKszOfL lmb
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                orbit horb
                (genComputeRows
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (genMemoryForest
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  α lmb
                  (memInputs (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard))
                  (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (genComputeSkeleton_hmempos
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  α
                  (memInputs (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard))
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
                (by
            rw [genComputeRows_bfsForest_length (romSeedVcomp hq hchar hs hf
                (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                (one_le_of_hΛ_conf hΛ) hΛ α
                (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
                  ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              α (romTree (K := K) (evalGRom_le_evalRom hgrom))]
            exact hcomp)
          (by
            change programMemRowsL lmb (romSeedVcomp hq hchar hs hf
                (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                (one_le_of_hΛ_conf hΛ) hΛ α
                (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
                  ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ 2 ^ orbit.h
            rw [← programMemShape_spec]
            exact hmem)).kMem ≤
              compilerKszOfL lmb
                (romSeedVcomp hq hchar hs hf
                  (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                  (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom))
            change 2 * programMemRootsL lmb
                (romSeedVcomp hq hchar hs hf
                  (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                  (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤
              compilerKsz
                (programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)))
                (programMemRootsL lmb
                  (romSeedVcomp hq hchar hs hf
                    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                    (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                  α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
            exact compilerKsz_two_mul _ _)
          (genComputeSkeleton_skeletonBounded _ α _ (by omega) hs hf
            (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)))
          hq hchar
          (genComputeSkeleton_axisRange (by omega) hs hf (evalGRom_le_evalGBy hgrom)
            (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) _)
          (romSeedVcomp_notMem_badSeeds hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          (romSeedVcomp_notMem_sizeWindowFailureSeeds hq hchar hs hf
            (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α
            (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
              (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
              ([] : List (NTree (GenMemoryRow K)))) hseedcard)
          (by
            rw [compilerKszOfL_irrel lmb
              (romSeedVcomp hq hchar hs hf
                (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                (one_le_of_hΛ_conf hΛ) hΛ α
                (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
                  (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
                  ([] : List (NTree (GenMemoryRow K)))) hseedcard)
              (0 : K) α (romTree (K := K) (evalGRom_le_evalRom hgrom))]
            exact hKszChar)
          hprogCap
          (by
            change programMemRowsL lmb
                (romSeedVcomp hq hchar hs hf
                  (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom)
                  (one_le_of_hΛ_conf hΛ) hΛ α
                  (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ)
                    (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ
                    ([] : List (NTree (GenMemoryRow K)))) hseedcard)
                α (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h
            rw [← programMemShape_spec]
            exact hmemCap)
          (hfirst a b c)))
    (hbasis : FormRBasis bas)
    (hwidth : FormRWidth F)
    (hax : ∀ (a b c : K)
        (hcoins : ComputeCoinsGeneric
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α a b c
          (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      GenFormRAxisLambda.RowsFormRAxisBound bas
        ((bfsRows (genComputeRows
          (romSeedVcomp hq hchar hs hf (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) (one_le_of_hΛ_conf hΛ) hΛ α (sizeWindowNounsBoundedBy_of_traceConfined (one_le_of_hΛ_conf hΛ) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom)) hΛ ([] : List (NTree (GenMemoryRow K)))) hseedcard) α
          (romTree (K := K) (evalGRom_le_evalRom hgrom)))).map
          (fun g => setRowCoins a b c g.row))) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW := by
  let z := romSeedVcompOfWindow hq hchar hs hf
    (evalGRom_le_evalGBy hgrom) (evalGRom_le_evalRom hgrom) hΛ α hseedcard
  let t := romTree (K := K) (evalGRom_le_evalRom hgrom)
  have hcomp' :
      (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h := by
    rw [genComputeRows_bfsForest_length]
    exact hcomp
  have hmem' :
      (bfsForest (genMemoryForest z α lmb (memInputs z) t)).length ≤ 2 ^ orbit.h := by
    change programMemRowsL lmb z α t ≤ 2 ^ orbit.h
    rw [← programMemShape_spec z α t]
    exact hmem
  have hKszChar' : compilerKszOfL lmb z α t < ringChar K := by
    rw [compilerKszOfL_irrel lmb z (0 : K) α t]
    exact hKszChar
  have hmemCap' : programMemRowsL lmb z α t + 1 ≤ 2 ^ orbit.h := by
    rw [← programMemShape_spec z α t]
    exact hmemCap
  have hcard' :
      RecordCarrier.honestIOBound (compilerNOfL lmb z α t) (compilerNOfL lmb z α t)
        (Fintype.card K) < Fintype.card (K × K) := by
    rw [compilerNOfL_irrel lmb z (0 : K) α t]
    exact hcard
  exact nockCompiles_p66 (hrows := hrows) α αW lmb htwo hgrom hs hf hΛ hseedcard hq hchar
    orbit horb
    hcomp' hmem'
    hwin hmemOrd hKszChar' hprogCap hmemCap'
    bas packageOrbit hcap hcard' hfirst hF hmore hbasis hwidth
    (fun a b c hcoins =>
      (GenFormRAxisLambda.buildFullPackage_formRAxisBound_iff _ _ _ _ _ _ _ _ _).mpr (by
        erw [GenFormRAxisLambda.genBuildableOfProgram_exec_computeRows]
        exact hax a b c hcoins))

end GoodSeed

end

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_accepted_bounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_grom
#print axioms Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_grom_atTree
#print axioms Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_grom_atTree_p61
#print axioms Nock.NockVMROM.Thm54.TraceGen.nockCompiles_of_grom_atTree_p62
#print axioms Nock.NockVMROM.Thm54.TraceGen.compilerChallengeVector
#print axioms Nock.NockVMROM.Thm54.TraceGen.compilerStateTagChar
#print axioms Nock.NockVMROM.Thm54.TraceGen.compilerKsz
#print axioms Nock.NockVMROM.Thm54.TraceGen.compilerN
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_of_grom_atRomSeed
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p61
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p62
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p63
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p64
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p65
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p66
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p67
#print axioms Nock.NockVMROM.Thm54.TraceGen.programMemRows_irrel
#print axioms Nock.NockVMROM.Thm54.TraceGen.compilerNOf_irrel
#print axioms Nock.NockVMROM.Thm54.TraceGen.compilerKszOf_irrel
#print axioms Nock.NockVMROM.Thm54.TraceGen.programMemShape_spec
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.airReorder_rows_lt_card_of_seedBudget
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.airReorder_rows_lt_card_of_seedBudgetVcomp
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.seedBudget_gt_rows
