import Nock.NockVMROM.Thm54.GoldilocksOrbit
import Nock.RedTeam.Batch70Thm54BuildableMilestones01
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Universal-constructor Milestone 2 domains and orbits

The paper frame is

The consumed release declaration remains
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.
-/

namespace Nock.RedTeam.Batch71

open scoped Classical Polynomial
open Module
open Nock Nock.Framework Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.GoldilocksOrbit

noncomputable section

/-! ## A. Goldilocks arithmetic and exact orders -/

/-- Exact arithmetic at the supported upper boundary. -/
theorem goldilocks_h32_arithmetic :
    Field.p - 1 = 2 ^ 32 * (2 ^ 32 - 1) ∧
      3 * 2 ^ 32 ∣ Field.p - 1 :=
  ⟨p_sub_one_factorization, three_mul_two_pow_dvd_p_sub_one 32 le_rfl⟩

/-- Height 33 is outside the fixed Goldilocks strict-orbit range. -/
theorem goldilocks_h33_divisibility_rejected :
    ¬(3 * 2 ^ 33 ∣ Field.p - 1) := by
  norm_num [Field.p]

/-- Both fixed generators have exact order at the supported upper boundary, rather than merely
orders dividing the required values. -/
theorem goldilocks_h32_exact_orders :
    orderOf (goldilocksStrictGenerator 32 (by norm_num)) = 3 * 2 ^ 32 ∧
      orderOf (goldilocksExecutionGenerator 32 (by norm_num)) = 2 ^ 32 :=
  ⟨goldilocksStrictGenerator_order 32 (by norm_num),
    goldilocksExecutionGenerator_order 32 (by norm_num)⟩

/-! ## B. Generic exact-order extraction edge cases -/

/-- Eta/type receipt for the generic exact-order extractor. -/
theorem generic_generator_signature
    (q m : ℕ) [Fact (Nat.Prime q)] (hm : m ∣ q - 1) :
    ∃ ω : ZMod q, orderOf ω = m :=
  exists_zmod_generator_of_dvd_sub_one q m hm

/-- The order-one edge case is inhabited. -/
theorem generic_generator_order_one :
    ∃ ω : ZMod 7, orderOf ω = 1 := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_zmod_generator_of_dvd_sub_one 7 1 (by norm_num)

/-- A nontrivial proper divisor is also realized with exact order. -/
theorem generic_generator_order_three :
    ∃ ω : ZMod 7, orderOf ω = 3 := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_zmod_generator_of_dvd_sub_one 7 3 (by norm_num)

/-- The apparent `m = 0` edge cannot satisfy the extractor's premises over a prime modulus. -/
theorem generic_generator_zero_order_premise_impossible
    (q : ℕ) [Fact (Nat.Prime q)] (hm : 0 ∣ q - 1) : False := by
  obtain ⟨k, hk⟩ := hm
  have hq : 1 < q := (Fact.out : Nat.Prime q).one_lt
  simp at hk
  omega

/-- Likewise, the prime typeclass excludes every `q ≤ 1` invocation. -/
theorem generic_generator_small_modulus_premise_impossible
    (q : ℕ) [Fact (Nat.Prime q)] (hq : q ≤ 1) : False :=
  (not_lt_of_ge hq) (Fact.out : Nat.Prime q).one_lt

/-- The varying-prime strict generator still delegates to the generic exact-order extractor. -/
theorem varying_strict_generator_refactor_preserved
    (e : ℕ) [NeZero e] (Ksz h : ℕ → ℕ) (kroots n : ℕ) :
    ∃ ω : StrictBaseField e Ksz h kroots n,
      orderOf ω = strictModulus e h n :=
  exists_strict_generator e Ksz h kroots n

/-! ## C. Prefix semantics and edge cases -/

section Prefix

variable {F : Type*} [Field F] {e h : ℕ}

/-- One receipt collects exact active cardinality, full-domain inclusion, transition cardinality,
terminal exclusion, and full-capacity injectivity. -/
theorem strict_prefix_semantics
    (D : StrictOrbitDomain F e h) (n : ℕ) (hn : 0 < n) (hcap : n ≤ 2 ^ h) :
    (strictRowDomain D n).card = n ∧
      strictRowDomain D n ⊆ strictFullDomain D ∧
      (strictTransitionDomain D n hn).card = n - 1 ∧
      strictTerminalPoint D n hn ∉ strictTransitionDomain D n hn ∧
      Function.Injective
        (fun i : Fin (2 ^ h) => strictOrbitPoint D i) := by
  exact
    ⟨strictRowDomain_card D hcap,
      strictRowDomain_mono D hcap,
      strictTransitionDomain_card D n hn hcap,
      strictTerminalPoint_not_mem_transitionDomain D n hn,
      strictOrbitPoint_injective D le_rfl⟩

/-- A singleton prefix has one active row, no transition rows, and its sole row is terminal. -/
theorem strict_singleton_edge
    (D : StrictOrbitDomain F e h) :
    (strictRowDomain D 1).card = 1 ∧
      strictTransitionDomain D 1 (by norm_num) = ∅ ∧
      strictTerminalPoint D 1 (by norm_num) ∉
        strictTransitionDomain D 1 (by norm_num) := by
  have hcap : 1 ≤ 2 ^ h := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  refine ⟨strictRowDomain_card D hcap, ?_, strictTerminalPoint_not_mem_transitionDomain D 1 _⟩
  apply Finset.card_eq_zero.mp
  simpa using strictTransitionDomain_card D 1 (by norm_num) hcap

/-- At full capacity, all `2^h` points remain distinct and the active domain is the full domain. -/
theorem strict_full_capacity_edge
    (D : StrictOrbitDomain F e h) :
    (strictFullDomain D).card = 2 ^ h ∧
      strictRowDomain D (2 ^ h) = strictFullDomain D ∧
      Function.Injective
        (fun i : Fin (2 ^ h) => strictOrbitPoint D i) :=
  ⟨strictFullDomain_card D, rfl, strictOrbitPoint_injective D le_rfl⟩

/-- The adjacency theorem reads the actual successor point and carries no cyclic final-row rule. -/
theorem strict_adjacency_receipt
    (D : StrictOrbitDomain F e h) {w : ℕ}
    (P : Fin w → F[X]) (chalVal pubVal : ℕ → F) (k i : ℕ) (hi : i < w) :
    (Reify.envOfTrace P D.ω (strictOrbitPoint D k) chalVal pubVal).traceNext i =
      (P ⟨i, hi⟩).eval (strictOrbitPoint D (k + 1)) :=
  strictOrbitPoint_gives_adjacency D P k chalVal pubVal i hi

end Prefix

/-! ## D. Physical-capacity enforcement -/

section Capacity

variable {F : Type*} [Field F] {e h : ℕ}

/-- The intended active-domain record rejects a compute row count one above physical capacity. -/
theorem compute_over_capacity_rejected
    (orbit : StrictOrbitDomain F e h) :
    ¬ MonolithicActiveDomains orbit (2 ^ h + 1) 0 0 := by
  intro D
  exact Nat.not_succ_le_self (2 ^ h) (by
    simpa [Nat.succ_eq_add_one] using D.computeCapacity)

/-- The intended active-domain record independently rejects an oversized memory row count. -/
theorem memory_over_capacity_rejected
    (orbit : StrictOrbitDomain F e h) :
    ¬ MonolithicActiveDomains orbit 0 (2 ^ h + 1) 0 := by
  intro D
  exact Nat.not_succ_le_self (2 ^ h) (by
    simpa [Nat.succ_eq_add_one] using D.memoryCapacity)

/-- The lower-level helper intentionally accepts an arbitrary prefix length.  It can therefore
form an H indexed by `2^h+1`; exact-cardinality export remains guarded by the separate `hcap`
premise of `expandChipOnStrictPrefix_H_card`. -/
theorem unconstrained_helper_forms_oversized_H
    {K : Type*} [Field K] [Algebra F K] [FiniteDimensional F K]
    (T : ChipTemplate F) (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) :
    (expandChipOnStrictPrefix T b chalVal pubVal orbit (2 ^ h + 1)).H =
        strictRowDomain orbit (2 ^ h + 1) ∧
      2 ^ h < 2 ^ h + 1 :=
  ⟨rfl, Nat.lt_succ_self _⟩

end Capacity

/-! ## E. Exact H threading -/

section Threading

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable {e h N M L : ℕ} {orbit : StrictOrbitDomain F e h}

/-- Compute H is definitionally the declared strict prefix. -/
theorem compute_H_defeq
    (D : MonolithicActiveDomains orbit N M L)
    (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F) :
    (expandChipOnComputeDomain D T b chalVal pubVal).H =
      strictRowDomain orbit N :=
  rfl

/-- Memory H is definitionally the declared `M+2L` strict prefix. -/
theorem memory_H_defeq
    (D : MonolithicActiveDomains orbit N M L)
    (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F) :
    (expandChipOnMemoryDomain D T b chalVal pubVal).H =
      strictRowDomain orbit (M + 2 * L) :=
  rfl

/-- A caller-selected compute H distinct from the declared prefix cannot equal the constructed H. -/
theorem compute_caller_H_substitution_rejected
    (D : MonolithicActiveDomains orbit N M L)
    (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (H' : Finset F) (hne : H' ≠ strictRowDomain orbit N) :
    H' ≠ (expandChipOnComputeDomain D T b chalVal pubVal).H := by
  simpa [compute_H_defeq D T b chalVal pubVal] using hne

/-- The same substitution attack is rejected for the memory constructor. -/
theorem memory_caller_H_substitution_rejected
    (D : MonolithicActiveDomains orbit N M L)
    (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (H' : Finset F) (hne : H' ≠ strictRowDomain orbit (M + 2 * L)) :
    H' ≠ (expandChipOnMemoryDomain D T b chalVal pubVal).H := by
  simpa [memory_H_defeq D T b chalVal pubVal] using hne

theorem active_H_cards_and_order
    (D : MonolithicActiveDomains orbit N M L)
    (T : ChipTemplate F) (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F) :
    (expandChipOnComputeDomain D T b chalVal pubVal).H.card = N ∧
      (expandChipOnMemoryDomain D T b chalVal pubVal).H.card = M + 2 * L ∧
      orderOf (expandChipOnComputeDomain D T b chalVal pubVal).ω =
        (expandChipOnComputeDomain D T b chalVal pubVal).e *
          2 ^ (expandChipOnComputeDomain D T b chalVal pubVal).h :=
  ⟨expandChipOnComputeDomain_H_card D T b chalVal pubVal,
    expandChipOnMemoryDomain_H_card D T b chalVal pubVal,
    orbit.order_ω⟩

end Threading

/-! ## F. Independent execution and RAP exponents -/

/-- Both independently selected exact orders survive construction of the pair. -/
theorem orbit_pair_preserves_separate_orders
    (hExec hRap : ℕ)
    (hExecPos : 1 ≤ hExec) (hExecLe : hExec ≤ 32)
    (hRapPos : 1 ≤ hRap) (hRapLe : hRap ≤ 32) :
    orderOf
        (goldilocksOrbitPair hExec hRap hExecPos hExecLe hRapPos hRapLe).execution.ω =
          2 ^ hExec ∧
      orderOf
        (goldilocksOrbitPair hExec hRap hExecPos hExecLe hRapPos hRapLe).strictRAP.ω =
          3 * 2 ^ hRap :=
  ⟨goldilocksExecutionGenerator_order hExec hExecLe,
    goldilocksStrictGenerator_order hRap hRapLe⟩

/-- A concrete pair with unequal exponents compiles; no shared-height premise can be inferred. -/
theorem unequal_orbit_exponents_nonvacuous :
    let P := goldilocksOrbitPair 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    P.execution.h = 1 ∧
      orderOf P.execution.ω = 2 ∧
      orderOf P.strictRAP.ω = 12 ∧
      P.execution.h ≠ 2 := by
  dsimp [goldilocksOrbitPair, goldilocksExecutionOrbit, goldilocksStrictOrbit]
  exact
    ⟨rfl,
      by simpa using goldilocksExecutionGenerator_order 1 (by norm_num),
      by simpa using goldilocksStrictGenerator_order 2 (by norm_num),
      by norm_num⟩

/-! ## G. Concrete non-vacuity and axiom scope -/

/-- Height 32 is substantively inhabited: the full strict prefix has `2^32` distinct points and
the execution generator has exact order `2^32`. -/
theorem height_32_nonvacuous :
    let strict := goldilocksStrictOrbit 32 (by norm_num) (by norm_num)
    let execution := goldilocksExecutionOrbit 32 (by norm_num) (by norm_num)
    (strictFullDomain strict).card = 2 ^ 32 ∧
      Function.Injective
        (fun i : Fin (2 ^ 32) => strictOrbitPoint strict i) ∧
      strictOrbitPoint strict (0 : Fin 2) ≠ strictOrbitPoint strict (1 : Fin 2) ∧
      orderOf execution.ω = 2 ^ 32 := by
  dsimp
  refine
    ⟨strictFullDomain_card _, strictOrbitPoint_injective _ le_rfl, ?_,
      goldilocksExecutionGenerator_order 32 (by norm_num)⟩
  intro h
  have hinj : Function.Injective
      (fun i : Fin 2 =>
        strictOrbitPoint (goldilocksStrictOrbit 32 (by norm_num) (by norm_num)) i) :=
    strictOrbitPoint_injective
      (goldilocksStrictOrbit 32 (by norm_num) (by norm_num))
      (n := 2) (by norm_num)
  have hij : (0 : Fin 2) = 1 := hinj h
  norm_num at hij

/-! ## H. Scope and consumed aliases -/

theorem milestone2_alias_scope_guard :
    @«Thm:NockVMROM» =
        @Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package ∧
      @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  Nock.RedTeam.Batch70.release_aliases_unchanged

/-- The universal builders remain uninhabited function types at this milestone. -/
theorem milestone2_constructor_scope_guard
    (F K : Type) [Field F] [Field K] [Algebra F K] :
    BuildableTopologyConstructor F K =
        ((E : BuildableNockExecution F K) → BuildableTopology E) ∧
      (∀ build : BuildableTopologyConstructor F K,
        BuildableTopologyTraceConstructor build =
          ((E : BuildableNockExecution F K) → BuildableTopologyTraces (build E))) :=
  Nock.RedTeam.Batch70.missing_constructor_types_are_functions F K

#print axioms Nock.NockVMROM.Thm54.StrictExtension.exists_zmod_generator_of_dvd_sub_one
#print axioms Nock.NockVMROM.Thm54.StrictExtension.exists_strict_generator
#print axioms Nock.NockVMROM.Thm54.StrictExtension.strictOrbitPoint_injective
#print axioms Nock.NockVMROM.Thm54.StrictExtension.strictRowDomain_card
#print axioms Nock.NockVMROM.Thm54.StrictExtension.strictTransitionDomain_card
#print axioms Nock.NockVMROM.Thm54.StrictExtension.expandChipOnStrictPrefix_H_card
#print axioms Nock.NockVMROM.Thm54.StrictExtension.expandChipOnStrictPrefix_order
#print axioms generic_generator_zero_order_premise_impossible
#print axioms strict_prefix_semantics
#print axioms unconstrained_helper_forms_oversized_H
#print axioms active_H_cards_and_order
#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.goldilocksStrictOrbit
#print axioms Nock.NockVMROM.Thm54.GoldilocksOrbit.goldilocksExecutionOrbit
#print axioms goldilocks_h33_divisibility_rejected
#print axioms unequal_orbit_exponents_nonvacuous
#print axioms height_32_nonvacuous
#print axioms milestone2_alias_scope_guard

end
end Nock.RedTeam.Batch71
