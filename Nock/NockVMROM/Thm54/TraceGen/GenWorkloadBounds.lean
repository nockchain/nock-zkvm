/-
  Nock/NockVMROM/Thm54/TraceGen/GenWorkloadBounds.lean

  **Bounding the two challenge-indexed majorants of `workload`.**

  `GenFailureUnionCounting.exists_coin_outside_failureUnion` is conditional on

  where `workload` (`ProductionP8Containment.lean:548`) is explicit and linear in the compute-row
  count and `Λ`, but the two majorants are suprema over challenges:

  * `fixedTopologyWorkload T` (`:566`) `= TemplateMemoryWalkCounting.memoryWalkTopologyWorkload
    T.verifier.raw` `= ⨆_{(z,α)} topologyWorkload ((T.verifier.raw.afterAlphaM z hz α lmb).familyData.base)`,
    and `topologyWorkload R` (`RawTopologyRAP.lean:289`) `= R.cfg.compRows * 3 * 8 + R.cfg.memRows * 2 * 4`;
  * `fixedAxisWorkload T` (`:579`) `= ⨆_{z ≠ 0} templateAxisWorkload (committedTemplate T.verifier z hz)`,
    and `templateAxisWorkload E` (`TemplateAxisCounting.lean:387`)
    `= ∑_{i < kMem} (countsP (templateAxisTree (templateMemoryTreeAt E i))).natDegree`.

  The two behave completely differently, and this module says exactly how.

  ## §D — the topology majorant **collapses**

  `topologyWorkload` reads only `compRows`/`memRows`.  `ExactConfigTemplate.specialize`
  (`SemanticTimestampStrategy.lean:319`) copies both, so `α` cannot move them; and
  `BareSemanticSupport.binds` (`ProductionP8Containment.lean:46`) supplies, at *every* `(z, α)`, a
  `SemanticStrategy.BindsAt` whose `computeRows`/`memoryRows` fields are `List.Forall₂` alignments
  with the *one pre-`z` skeleton*.  `Forall₂` forces equal lengths, and
  `ExactExecution.computeRows_length` identifies that length with `cfg.compRows`.  So `compRows` and
  `memRows` are constant in `(z, α)` and equal to the skeleton's row counts, the `sup` collapses,
  and `fixedTopologyWorkload` has an **exact closed form in trace data**
  (`fixedTopologyWorkload_eq`).

  ## §E — the axis majorant does **not** collapse

  `templateAxisWorkload` is a sum of `natDegree`s of `countsP` polynomials whose exponents are the
  committed `MemoryRowTemplate.timestamp.recordExponent` **raw naturals** of the seed-fixed template
  `(T.raw.timestamp.afterSeed ⟨z, hz⟩).executionTemplate`.  `afterSeed` is an arbitrary function of
  the seed, and — decisively — `BindsAt` cannot pin those naturals: every row-level obligation it
  carries factors through `MemoryRowTemplate.specialize`, which reads the exponent only as
  `α ^ recordExponent` (`ForestExponentWindow.lean` §C, `wrapDataExponents`).  Adding `orderOf α` to
  every committed exponent therefore yields a *different* template with the *same* specialized
  execution and a *larger* workload.  So no bound on `fixedAxisWorkload` follows from trace data
  alone; the residual is exactly the paper's no-wrap canonicity condition on the commitment, whose intended content is the paper (each committed memory timestamp exponent
  *is* a compute-table line number) plus the paper (`N, L ∈ negl(K)`).

  What this module *does* prove about it is the reduction of the whole `sup`-of-sums-of-degrees to a
  **single scalar of the commitment**:

  * `natDegree_indP_countsP_le` — `indP`/`countsP` have `natDegree ≤ B` as soon as every
    `read`/`verify` exponent of the axis tree is `≤ B` (unconditional, generic in `K`);
  * `templateAxisWorkload_le` — hence `templateAxisWorkload E ≤ T.kMem * B`;
  * `templateAxisWorkload_le_maxTemplateRecordExponent` — **unconditionally**, with `B` the largest
    `recordExponent` of an actual BFS row of the committed template, via
    `ForestExponentWindow.memoryRow_of_alphaFreeRoot_exp`;
  * `fixedAxisWorkload_le` / `fixedAxisWorkload_le_maxTemplateRecordExponent` — the same at the
    production layer, with `kMem` replaced by the skeleton's memory-root count (§C, again from
    `binds`), under a seed-uniform exponent premise.

  The premise `CommittedExponentWindow T B` is stated, named, and **not** discharged here.  It is
  `GenericHonestPackage.ForestExponentOrder` with `< orderOf α` replaced by `≤ B` and quantified
  over all seeds; `ForestExponentWindow.lean` §B records that a Nat *bound* of this shape is a
  rename of that window and closes nothing by itself.  It is not a hypothesis of the form "the
  workload is small": it constrains one committed natural per memory row, and the conclusion is a
  quadratic-in-trace-data bound.  Supplying it needs the line-number identification
  (`ForestExponentWindow.forestExponentOrder_of_line_numbers`'s `hmemLine`) at every seed, which
  nothing in the tree provides for a general commitment.
-/
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ForestExponentWindow
import Nock.NockVMROM.Thm54.TraceGen.GenFailureUnionCounting
import Nock.NockVMROM.Thm54.TraceGen.GoldilocksTimestampBase
import Nock.Field

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.AxisBridge
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.SizeWindowCounting

noncomputable section

/-! ## §A. Degree of the axis polynomials from an exponent bound

`indP`/`countsP` (`AxisBatching.lean:127,134`) are built from `X ^ e` at `read`/`verify` nodes, a
`C a *` scaling and `±`.  None of those raises the degree above the largest exponent used, so a
bound on the tree's `readExps`/`verifyExps` bounds both polynomials' `natDegree`.  This is generic
in `K`: no `Fintype`, no characteristic hypothesis. -/

section AxisDegree

variable {K : Type} [Field K]

/-- Both axis polynomials of an `MTree` have degree at most any bound on its timestamp
exponents. -/
theorem natDegree_indP_countsP_le (B : ℕ) :
    ∀ t : MTree K,
      (∀ e ∈ readExps t, e ≤ B) → (∀ e ∈ verifyExps t, e ≤ B) →
        (indP t).natDegree ≤ B ∧ (countsP t).natDegree ≤ B := by
  intro t
  induction t with
  | halt =>
      intro _ _
      simp [indP, countsP]
  | decompose l r ihl ihr =>
      intro hread hverify
      have hrl : ∀ e ∈ readExps l, e ≤ B := fun e he =>
        hread e (by simp only [readExps, List.mem_append]; exact Or.inl he)
      have hrr : ∀ e ∈ readExps r, e ≤ B := fun e he =>
        hread e (by simp only [readExps, List.mem_append]; exact Or.inr he)
      have hvl : ∀ e ∈ verifyExps l, e ≤ B := fun e he =>
        hverify e (by simp only [verifyExps, List.mem_append]; exact Or.inl he)
      have hvr : ∀ e ∈ verifyExps r, e ≤ B := fun e he =>
        hverify e (by simp only [verifyExps, List.mem_append]; exact Or.inr he)
      obtain ⟨hil, hcl⟩ := ihl hrl hvl
      obtain ⟨hir, hcr⟩ := ihr hrr hvr
      refine ⟨?_, ?_⟩
      · have hind : indP (MTree.decompose l r) =
            Polynomial.C (1 : K) * (indP l + indP r) := rfl
        rw [hind, map_one, one_mul]
        exact (Polynomial.natDegree_add_le _ _).trans (max_le hil hir)
      · have hcnt : countsP (MTree.decompose l r) =
            countsP l + countsP r + Polynomial.C ((1 : K) - 1) * (indP l + indP r) +
              indP r := rfl
        rw [hcnt, sub_self, map_zero, zero_mul, add_zero]
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ hir)
        exact (Polynomial.natDegree_add_le _ _).trans (max_le hcl hcr)
  | read e c ih =>
      intro hread hverify
      have he : e ≤ B := hread e (by simp [readExps])
      have hrc : ∀ e' ∈ readExps c, e' ≤ B := fun e' he' =>
        hread e' (by simp only [readExps]; exact List.mem_cons_of_mem _ he')
      have hvc : ∀ e' ∈ verifyExps c, e' ≤ B := fun e' he' =>
        hverify e' (by simpa only [verifyExps] using he')
      obtain ⟨hic, hcc⟩ := ih hrc hvc
      have hxp : (Polynomial.X ^ e : Polynomial K).natDegree ≤ B := by
        rw [Polynomial.natDegree_X_pow]; exact he
      refine ⟨?_, ?_⟩
      · rw [indP_default_read]
        exact (Polynomial.natDegree_sub_le _ _).trans (max_le hic hxp)
      · rw [countsP_default_read]
        exact (Polynomial.natDegree_sub_le _ _).trans (max_le hcc hxp)
  | verify e a c ih =>
      intro hread hverify
      have he : e ≤ B := hverify e (by simp [verifyExps])
      have hrc : ∀ e' ∈ readExps c, e' ≤ B := fun e' he' =>
        hread e' (by simpa only [readExps] using he')
      have hvc : ∀ e' ∈ verifyExps c, e' ≤ B := fun e' he' =>
        hverify e' (by simp only [verifyExps]; exact List.mem_cons_of_mem _ he')
      obtain ⟨hic, hcc⟩ := ih hrc hvc
      have hxp : (Polynomial.X ^ e : Polynomial K).natDegree ≤ B := by
        rw [Polynomial.natDegree_X_pow]; exact he
      refine ⟨?_, ?_⟩
      · have hind : indP (MTree.verify e a c) =
            indP c + Polynomial.C (pwScale (1 : K)) * Polynomial.X ^ e := rfl
        rw [hind, pwScale_one, map_one, one_mul]
        exact (Polynomial.natDegree_add_le _ _).trans (max_le hic hxp)
      · have hcnt : countsP (MTree.verify e a c) =
            countsP c + Polynomial.C (pwScale (1 : K)) * Polynomial.X ^ e := rfl
        rw [hcnt, pwScale_one, map_one, one_mul]
        exact (Polynomial.natDegree_add_le _ _).trans (max_le hcc hxp)

end AxisDegree

/-! ## §B. The axis workload from an exponent bound -/

section TemplateAxis

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- One committed root polynomial's degree, from a bound on that root's timestamp exponents. -/
theorem templateAxisPolynomial_natDegree_le
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (B : ℕ) (i : Fin T.kMem)
    (hexp : ∀ e, (e ∈ readExps (alphaFreeRoot E i) ∨
        e ∈ verifyExps (alphaFreeRoot E i)) → e ≤ B) :
    (templateAxisPolynomial E i).natDegree ≤ B :=
  (TemplateAxisCounting.natDegree_indP_bin_countsP_bin_le B (alphaFreeRoot E i)
    (fun e he => hexp e (Or.inl he)) (fun e he => hexp e (Or.inr he))).2

/-- **The axis workload of one committed template, from one exponent bound.**  `kMem` roots, each
contributing degree at most `B`. -/
theorem templateAxisWorkload_le
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (B : ℕ)
    (hexp : ∀ (i : Fin T.kMem) e, (e ∈ readExps (alphaFreeRoot E i) ∨
        e ∈ verifyExps (alphaFreeRoot E i)) → e ≤ B) :
    templateAxisWorkload E ≤ T.kMem * B := by
  have hsum : templateAxisWorkload E =
      ∑ i : Fin T.kMem, (templateAxisPolynomial E i).natDegree := rfl
  rw [hsum]
  calc ∑ i : Fin T.kMem, (templateAxisPolynomial E i).natDegree
      ≤ ∑ _i : Fin T.kMem, B :=
        Finset.sum_le_sum fun i _ => templateAxisPolynomial_natDegree_le E B i (hexp i)
    _ = T.kMem * B := by simp

/-! ### The unconditional reduction to the largest committed exponent

Every exponent the α-free axis structure reads is the committed `recordExponent` of an actual BFS
row of the committed template.  So the whole axis workload is bounded by `kMem` times the largest
committed exponent, with no premise at all. -/

/-- The largest committed timestamp exponent of a committed execution template. -/
def maxTemplateRecordExponent
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : ℕ :=
  (E.memoryRows.map fun row => row.timestamp.recordExponent).foldr max 0

theorem le_foldr_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · exact le_trans (ih hx) (by simp)

/-- **Unconditional.**  The axis workload of a committed template is at most its memory-root count
times its largest committed timestamp exponent. -/
theorem templateAxisWorkload_le_maxTemplateRecordExponent
    [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    templateAxisWorkload E ≤ T.kMem * maxTemplateRecordExponent E := by
  refine templateAxisWorkload_le E _ ?_
  intro i e he
  obtain ⟨row, hrow, hev⟩ :=
    ForestExponentWindow.memoryRow_of_alphaFreeRoot_exp E i e he
  subst hev
  exact le_foldr_max (List.mem_map_of_mem hrow)

end TemplateAxis

/-! ## §C. `compRows`, `memRows` and `kMem` are skeleton data, constant in the challenges

`BareSemanticSupport.binds` gives a `BindsAt` at every `(z, α)`; its `Forall₂` fields force the
executed row lists to have the *skeleton's* lengths, and `ExactExecution`'s own length fields
identify those with the configured counts. -/

section Collapse

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- The specialized compute-row count is the skeleton's, at every challenge. -/
theorem specializedCfg_compRows (T : ProductionStrategy F K) (hb : T.BindsAll) (z : K) (hz : z ≠ 0) (α lmb : K) :
    (T.specializedCfg z hz α lmb).compRows =
      (SemanticStrategy.computeSkeletonRows T.skeleton).length := by
  have h := (hb z hz α lmb).computeRows.length_eq
  rw [ExactExecution.computeRows_length] at h
  exact h.symm

/-- The specialized memory-row count is the skeleton's, at every challenge. -/
theorem specializedCfg_memRows (T : ProductionStrategy F K) (hb : T.BindsAll) (z : K) (hz : z ≠ 0) (α lmb : K) :
    (T.specializedCfg z hz α lmb).memRows =
      (SemanticStrategy.memorySkeletonRows T.skeleton).length := by
  have h := (hb z hz α lmb).memoryRows.length_eq
  rw [ExactExecution.memoryRows_length] at h
  exact h.symm

/-- The specialized memory-root count is the skeleton's, at every challenge. -/
theorem specializedCfg_kMem (T : ProductionStrategy F K) (hb : T.BindsAll) (z : K) (hz : z ≠ 0) (α lmb : K) :
    (T.specializedCfg z hz α lmb).kMem = T.skeleton.memoryForest.length := by
  have h := (hb z hz α lmb).memoryForest.length_eq
  rw [(T.specializedExec z hz α lmb).memory_root_count] at h
  exact h.symm

/-- The same for the α-free committed configuration template: `specialize` copies `kMem`. -/
theorem committedTemplate_kMem (T : ProductionStrategy F K) (hb : T.BindsAll) (z : K) (hz : z ≠ 0) :
    (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem =
      T.skeleton.memoryForest.length :=
  specializedCfg_kMem T hb z hz 0 0

end Collapse

/-! ## §D. The topology majorant, exactly -/

section Topology

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- Every staged topology workload has the *same* value, given by skeleton row counts. -/
theorem topologyWorkload_base_eq (T : ProductionStrategy F K) (hb : T.BindsAll) (z : K) (hz : z ≠ 0) (α lmb : K) :
    topologyWorkload ((T.verifier.raw.afterAlphaM z hz α lmb).familyData.base) =
      24 * (SemanticStrategy.computeSkeletonRows T.skeleton).length +
        8 * (SemanticStrategy.memorySkeletonRows T.skeleton).length := by
  have hbase : ((T.verifier.raw.afterAlphaM z hz α lmb).familyData.base).cfg =
      T.specializedCfg z hz α lmb := rfl
  have hc := specializedCfg_compRows T hb z hz α lmb
  have hm := specializedCfg_memRows T hb z hz α lmb
  simp only [topologyWorkload, hbase, hc, hm]
  ring

/-- **The topology majorant collapses to an exact closed form in trace data.**  The `sup` over all
`(z, α)` is attained everywhere, so this is an equality, not a bound. -/
theorem fixedTopologyWorkload_eq (T : ProductionStrategy F K) (hb : T.BindsAll) :
    fixedTopologyWorkload T =
      24 * (SemanticStrategy.computeSkeletonRows T.skeleton).length +
        8 * (SemanticStrategy.memorySkeletonRows T.skeleton).length := by
  refine le_antisymm ?_ ?_
  · simp only [fixedTopologyWorkload, TemplateMemoryWalkCounting.memoryWalkTopologyWorkload]
    refine Finset.sup_le ?_
    intro za _
    by_cases hz : za.1 ≠ 0
    · rw [dif_pos hz]
      exact le_of_eq (topologyWorkload_base_eq T hb za.1 hz za.2.1 za.2.2)
    · rw [dif_neg hz]
      exact Nat.zero_le _
  · have hone : (1 : K) ≠ 0 := one_ne_zero
    have h := topologyWorkload_le_fixedTopologyWorkload T (1 : K) hone (0 : K) (0 : K)
    rwa [topologyWorkload_base_eq T hb (1 : K) hone (0 : K) (0 : K)] at h

end Topology

/-! ## §E. The axis majorant, under the named exponent window -/

section Axis

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **The residual premise, named.**  Every timestamp exponent read by the α-free axis structure of
every seed-committed template is at most `B`.

This is `GenericHonestPackage.ForestExponentOrder` with `< orderOf α` replaced by `≤ B`, quantified
over all nonzero seeds.  `ForestExponentWindow.lean` §B records that a Nat bound of this shape is a
rename of that window; the paper's intended content is the paper (the exponent *is* a
compute-table line number) plus the paper, enforced at the paper by the verifier's
no-wrap check. -/
def CommittedExponentWindow (T : ProductionStrategy F K) (B : ℕ) : Prop :=
  ∀ (z : K) (hz : z ≠ 0)
    (i : Fin (T.verifier.raw.timestamp.afterSeed ⟨z, hz⟩).configTemplate.kMem) (e : ℕ),
    (e ∈ readExps (alphaFreeRoot (committedTemplate T.verifier z hz) i) ∨
      e ∈ verifyExps (alphaFreeRoot (committedTemplate T.verifier z hz) i)) → e ≤ B

/-- Under the exponent window the axis majorant is bounded by skeleton data times `B`. -/
theorem fixedAxisWorkload_le (T : ProductionStrategy F K) (hb : T.BindsAll) (B : ℕ)
    (hwin : CommittedExponentWindow T B) :
    fixedAxisWorkload T ≤ T.skeleton.memoryForest.length * B := by
  simp only [fixedAxisWorkload]
  refine Finset.sup_le ?_
  intro z _
  by_cases hz : z ≠ 0
  · rw [dif_pos hz]
    have h := templateAxisWorkload_le (committedTemplate T.verifier z hz) B (hwin z hz)
    rwa [committedTemplate_kMem T hb z hz] at h
  · rw [dif_neg hz]
    exact Nat.zero_le _

/-- The same with the window taken at the row level: a bound on the largest committed timestamp
exponent of each seed's template.  This is the form the no-wrap check is about — one natural per
memory row — and it needs no statement about axis trees. -/
theorem fixedAxisWorkload_le_maxTemplateRecordExponent [FiniteDimensional F K]
    (T : ProductionStrategy F K) (hb : T.BindsAll) (B : ℕ)
    (hmax : ∀ (z : K) (hz : z ≠ 0),
      maxTemplateRecordExponent (committedTemplate T.verifier z hz) ≤ B) :
    fixedAxisWorkload T ≤ T.skeleton.memoryForest.length * B := by
  simp only [fixedAxisWorkload]
  refine Finset.sup_le ?_
  intro z _
  by_cases hz : z ≠ 0
  · rw [dif_pos hz]
    have h := templateAxisWorkload_le_maxTemplateRecordExponent
      (committedTemplate T.verifier z hz)
    rw [committedTemplate_kMem T hb z hz] at h
    exact h.trans (Nat.mul_le_mul_left _ (hmax z hz))
  · rw [dif_neg hz]
    exact Nat.zero_le _

end Axis

/-! ## §F. The composed explicit bound -/

section Compose

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- Gauss closed form for the size-window numerator, so the composed bound below is fully
explicit. -/
theorem sizeWindowRootBound_mul_two (Λ : ℕ) : sizeWindowRootBound Λ * 2 = Λ * (Λ + 1) := by
  induction Λ with
  | zero => simp [sizeWindowRootBound]
  | succ n ih =>
      have hstep : sizeWindowRootBound (n + 1) = sizeWindowRootBound n + (n + 1) := by
        simp only [sizeWindowRootBound]
        exact Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)) (fun k => k)
      rw [hstep, Nat.add_mul, ih]
      ring

/-- **The whole soundness numerator, explicit in trace data and one exponent bound.**  Everything on
the right is either a skeleton row/root count, `Λ`, or the exponent window bound `B`. -/
theorem workload_le_explicit (T : ProductionStrategy F K) (hb : T.BindsAll) (Λ B : ℕ)
    (hwin : CommittedExponentWindow T B) :
    workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) ≤
      1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) * (2 * Λ - 1) +
        (24 * (SemanticStrategy.computeSkeletonRows T.skeleton).length +
          8 * (SemanticStrategy.memorySkeletonRows T.skeleton).length) +
        T.skeleton.memoryForest.length * B +
        formRUniformWorkload T +
        reqPairWorkload T Λ +
        sizeWindowRootBound Λ := by
  simp only [workload, fixedTopologyWorkload_eq T hb]
  have := fixedAxisWorkload_le T hb B hwin
  omega

end Compose

/-! ## §G. The Goldilocks side condition

At `Nock.Field.K = GaloisField p 3` the side condition of
`GenFailureUnionCounting.exists_coin_outside_failureUnion` becomes a single explicit numeric
inequality on skeleton row counts, `Λ` and the exponent bound.

⚠ Everything in this section mentions `Nock.Field.K` and therefore depends on the blessed
`Nock.Field.goldilocks_prime` axiom.  Nothing above does. -/

section Goldilocks

variable {F : Type} [Field F] [Algebra F GK]

/-- As in `GenFailureUnionCounting`: Mathlib's `ringChar.charP` is low priority, so the instance
`ProductionStrategy`'s binder demands is installed locally.  `CharP` is a `Prop`, so this is the
same instance argument that module's own local copy supplies.  This adds no assumption. -/
local instance goldilocksWorkloadRingCharP : CharP GK (ringChar GK) := ringChar.charP _

/-- **The Goldilocks numerator bound.**  The soundness numerator is below `p^3` as soon as the
explicit inequality in skeleton row/root counts, `Λ` and the exponent window `B` holds. -/
theorem goldilocks_workload_lt_p_cubed
    (T : ProductionP8Containment.ProductionStrategy F GK) (hb : T.BindsAll) (Λ B : ℕ)
    (hwin : CommittedExponentWindow T B)
    (hlt :
      1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) * (2 * Λ - 1) +
        (24 * (SemanticStrategy.computeSkeletonRows T.skeleton).length +
          8 * (SemanticStrategy.memorySkeletonRows T.skeleton).length) +
        T.skeleton.memoryForest.length * B +
        ProductionP8Containment.formRUniformWorkload T +
        ProductionP8Containment.reqPairWorkload T Λ +
        sizeWindowRootBound Λ < Nock.Field.p ^ 3) :
    workload T Λ (fixedTopologyWorkload T) (fixedAxisWorkload T) < Nock.Field.p ^ 3 :=
  lt_of_le_of_lt (workload_le_explicit T hb Λ B hwin) hlt

/-- **Existence of a coin outside the five-class failure union, from trace data plus the exponent
window.**  This is `GenFailureUnionCounting.goldilocks_exists_coin_outside_failureUnion` with its
arithmetic side condition replaced by the explicit inequality above.  As there, this is existence
only: it says nothing about `T.Accepts`. -/
theorem goldilocks_exists_coin_outside_failureUnion_of_explicit
    (T : ProductionP8Containment.ProductionStrategy F GK) (hb : T.BindsAll) (Λ B : ℕ)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus GK T.skeleton Λ)
    (lmb : GK)
    (hwindowBound : SizeWindowNounsBoundedBy T.skeleton Λ)
    (hwin : CommittedExponentWindow T B)
    (hlt :
      1 + (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) * (2 * Λ - 1) +
        (24 * (SemanticStrategy.computeSkeletonRows T.skeleton).length +
          8 * (SemanticStrategy.memorySkeletonRows T.skeleton).length) +
        T.skeleton.memoryForest.length * B +
        ProductionP8Containment.formRUniformWorkload T +
        ProductionP8Containment.reqPairWorkload T Λ +
        sizeWindowRootBound Λ < Nock.Field.p ^ 3) :
    ∃ ω : JointCoins GK, ω ∉ ProductionP8Containment.FailureUnion T C lmb :=
  goldilocks_exists_coin_outside_failureUnion T Λ C lmb hwindowBound
    (goldilocks_workload_lt_p_cubed T hb Λ B hwin hlt)

end Goldilocks

end

end Nock.NockVMROM.Thm54.TraceGen

/-! ## Axiom receipts -/

-- [propext, Classical.choice, Quot.sound]
#print axioms Nock.NockVMROM.Thm54.TraceGen.natDegree_indP_countsP_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.templateAxisWorkload_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.templateAxisWorkload_le_maxTemplateRecordExponent
#print axioms Nock.NockVMROM.Thm54.TraceGen.fixedTopologyWorkload_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.fixedAxisWorkload_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.workload_le_explicit
-- [propext, Classical.choice, Quot.sound, Nock.Field.goldilocks_prime]
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocks_workload_lt_p_cubed
#print axioms Nock.NockVMROM.Thm54.TraceGen.goldilocks_exists_coin_outside_failureUnion_of_explicit
