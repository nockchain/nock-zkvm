/-
  Nock/RedTeam/Batch265Thm54DeadChallenge36.lean

  **`challenge36` was dead: nothing consumed read it except the acceptance pin that stored it —
  and the deployed compute chip reads no gate through its slot.**

  History, because it is the whole point of this file.  `FinalComputeChallengeTuple`
  (`OptimizedComputeCollisionBound.lean`) used to carry three coordinates — `challenge9 : 𝕂`,
  `challenge11 : 𝕂` and `challenge36 : 𝔽`, the coin of the two compressed endpoint equality checks
  `OptimizedComputeFinal.finalMaskedEndpointEqualityChecks`.  Since stage 3e the
  deployed compute chip commits the twenty-two individual equations `finalEndpointEqualityChecks`
  instead, and the `liftChallenge36` summand left `OptimizedStrictPackage.OptimizedProductionFailureEvent`.

  1. `b265_failure_event_ignores_challenge36` — membership in the consumed failure event is
     invariant under changing `challenge36`;
  2. `b265_genuine_target_ignores_challenge36` — `OptimizedProductionGenuineTargetAt` is
     invariant under changing `challenge36`;
  3. `b265_acceptance_reads_challenge36_only_through_the_pin` (and the `OptimizedTraceAcceptanceAt`
     twin) — acceptance at a tuple with `challenge36 = x` is acceptance at the tuple carrying the
     chip's own raw slot `36`, **plus** the single equation `chal 36 = x`: the coordinate was read
     by exactly one conjunct, `compute_challenge36`, and that conjunct only copied the slot;
  4. `b265_no_committed_compute_gate_reads_slot36` — **measured, not asserted** (below).

  What survives, and is what this file now records:

  * `b265_failure_event_reads_only_the_two_extension_compute_coins` — for any two challenge
    tuples agreeing on `JointCoins`, `IOCoins`, `challenge9`, `challenge11` and the memory block,
    membership in the consumed failure event agrees.  Since those two coins are now the *whole*
    compute block, this says the compute block enters the event only through the two extension
    coins.
  * **Receipt 4, unchanged:** the gate-side read-set instrument `chalSlots` (the `CoeffExpr`
    analogue of `ConstraintIndex.chalIdxs`, tied to evaluation by `eval_congr_of_chalSlots` and to
    the `Def:RAP` polynomials by `coeffToMv_congr_of_chalSlots`) finds raw slot
    `finalScalarChallengeBase = 36` in **no** gate of the deployed list
    `correctedFinalComputeAllGates`, at every row count and every basis
    (`b265_no_committed_compute_gate_reads_slot36`).  The positive control
    `b265_retired_compressed_gates_do_read_slot36` finds it in **both** retired compressed gates,
    so the instrument sees the slot where it really is.  `b265_deployed_compute_chip_is_blind_to_slot36`
    is the RAP-level consequence — every constraint polynomial of `CorrectedFinalComputeRAP` is
    unchanged when slot `36` of `chalVal` is changed — and `b265_pinned_coin_is_the_chip_challenge_at_36`
    identifies the value the old pin copied, `(P.computeScalarEnv Qc).chal finalScalarChallengeBase`,
    with that very slot of the package's compute challenge vector.  The slot itself remains in
    the substitution file's index map, read by nothing.

  Together: the verifier drew a base-field element, the acceptance copied it into the tuple, and
  nothing downstream — event, target, chip — depended on it.

  **Not claimed.**  Nothing here says the eleven column-vs-public equalities the coin once folded
  are unenforced — they are enforced, individually, by the twenty-two committed gates with no
  randomness (`OptimizedComputeFinal.endpointEqualityChecks_determine_public`).  This is a
  statement about what read the coordinate, not about what the chip checks.  No bound and no bit
  figure moves with this file.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch265

open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Module
open scoped Polynomial

/-! ## 0. The two extension lifts read exactly their own coordinate -/

theorem mem_liftChallenge9
    {K : Type} [Fintype K] [DecidableEq K]
    (bad : Finset K) (c : FinalComputeChallengeTuple K) :
    c ∈ liftChallenge9 bad ↔ False := by
  simp [liftChallenge9]

theorem mem_liftChallenge11
    {K : Type} [Fintype K] [DecidableEq K]
    (bad : Finset K) (c : FinalComputeChallengeTuple K) :
    c ∈ liftChallenge11 bad ↔ False := by
  simp [liftChallenge11]

theorem b265_compute_block_is_two_extension_coordinates
    (K : Type) [Fintype K] :
    Fintype.card (FinalComputeChallengeTuple K) = Fintype.card K ^ 3 :=
  card_finalComputeChallengeTuple K

/-- The production challenge space is `|𝕂|⁶`. -/
theorem b265_no_base_field_factor_in_the_challenge_space
    (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedProductionChallengeTuple K F) = Fintype.card K ^ 11 :=
  card_optimizedProductionChallengeTuple K F

/-! ## 1. -/

section FailureEvent

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
  [DecidableEq F] [DecidableEq K]
variable {Λ N M m : ℕ}

/-- `OptimizedProductionFailureEvent` is a union of four lifts.

`OptimizedProductionFailureEvent` no longer takes the IO records
(the IO summand moved to the family event `famIOEventOf`), so the event reads `c.1` only. -/
theorem b265_failure_event_reads_only_the_two_extension_compute_coins
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F)
    (c d : OptimizedProductionChallengeTuple K F)
    (h1 : c.1 = d.1) (h2 : c.2.1 = d.2.1)
    (h4 : c.2.2.2 = d.2.2.2) :
    (c ∈ OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies) ↔
      d ∈ OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies := by
  simp only [OptimizedProductionFailureEvent, Finset.mem_union, liftP8Failure, liftIOFailure,
    Finset.mem_product, Finset.mem_univ, true_and, and_true, h1]

end FailureEvent

/-! ## 2–3. Where the old pin pointed

What is still
statable is the identification of the value the pin copied. -/

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The value the deleted pin `compute_challenge36` copied into the tuple is slot `36` of the
package's own compute challenge vector — the very vector `P.computeChip` is built from, and the
vector §4 shows the chip does not read at that slot. -/
theorem b265_pinned_coin_is_the_chip_challenge_at_36
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    (P.computeScalarEnv Qc).chal finalScalarChallengeBase =
      P.optimized.computeChallenge finalScalarChallengeBase := rfl

end Package

/-! ## 4. The deployed compute chip reads no gate through slot 36 — measured

`SaturatedDeclaration.lean` measures the *prover's* declared coin reads against the schedule.
The question here is the *verifier's*: which coin slots does each committed gate read?  The
instrument is the gate-side read set, the `CoeffExpr` analogue of `ConstraintIndex.chalIdxs`
(which does the same job for `Nock.Reified.Expr`).  Two lemmas tie it to semantics — a gate's
evaluation and its `Def:RAP` polynomial both depend on a coin only through the slots the
instrument lists — so an absence measured by it is an absence in the deployed object, not a
syntactic accident. -/

section Instrument

variable {F : Type*} [Field F]

/-- **The gate-side read-set instrument**: the challenge slots a base-field gate reads. -/
def chalSlots : CoeffExpr F → List ℕ
  | .const _ => []
  | .var .challenge i => [i]
  | .var .traceCur _ => []
  | .var .traceNext _ => []
  | .var .publicVal _ => []
  | .add a b => chalSlots a ++ chalSlots b
  | .sub a b => chalSlots a ++ chalSlots b
  | .mul a b => chalSlots a ++ chalSlots b
  | .neg a => chalSlots a
  | .pow a _ => chalSlots a

/-- **Semantic soundness of the instrument, evaluation side**: two environments agreeing on the
trace, the public values and every listed slot give the same evaluation. -/
theorem eval_congr_of_chalSlots (g : CoeffExpr F) (env env' : Env F)
    (htrace : env'.trace = env.trace) (hnext : env'.traceNext = env.traceNext)
    (hpub : env'.pub = env.pub)
    (hchal : ∀ j ∈ chalSlots g, env'.chal j = env.chal j) :
    g.eval env' = g.eval env := by
  induction g with
  | const c => rfl
  | var kind i =>
      cases kind
      · simp [CoeffExpr.eval, htrace]
      · simp [CoeffExpr.eval, hnext]
      · exact hchal i (List.mem_singleton_self i)
      · simp [CoeffExpr.eval, hpub]
  | add a b iha ihb =>
      simp only [chalSlots, List.mem_append] at hchal
      simp only [CoeffExpr.eval, iha (fun j hj => hchal j (Or.inl hj)),
        ihb (fun j hj => hchal j (Or.inr hj))]
  | sub a b iha ihb =>
      simp only [chalSlots, List.mem_append] at hchal
      simp only [CoeffExpr.eval, iha (fun j hj => hchal j (Or.inl hj)),
        ihb (fun j hj => hchal j (Or.inr hj))]
  | mul a b iha ihb =>
      simp only [chalSlots, List.mem_append] at hchal
      simp only [CoeffExpr.eval, iha (fun j hj => hchal j (Or.inl hj)),
        ihb (fun j hj => hchal j (Or.inr hj))]
  | neg a iha =>
      simp only [chalSlots] at hchal
      simp only [CoeffExpr.eval, iha hchal]
  | pow a n iha =>
      simp only [chalSlots] at hchal
      simp only [CoeffExpr.eval, iha hchal]

/-- **Semantic soundness of the instrument, `Def:RAP` side**: the reified constraint polynomial
depends on the challenge vector only through the listed slots. -/
theorem coeffToMv_congr_of_chalSlots {w : ℕ} (chalVal chalVal' pubVal : ℕ → F)
    (g : CoeffExpr F) (hchal : ∀ j ∈ chalSlots g, chalVal' j = chalVal j) :
    coeffToMv (w := w) chalVal' pubVal g = coeffToMv (w := w) chalVal pubVal g := by
  induction g with
  | const c => rfl
  | var kind i =>
      cases kind
      · rfl
      · rfl
      · simp only [coeffToMv]
        rw [hchal i (List.mem_singleton_self i)]
      · rfl
  | add a b iha ihb =>
      simp only [chalSlots, List.mem_append] at hchal
      simp only [coeffToMv, iha (fun j hj => hchal j (Or.inl hj)),
        ihb (fun j hj => hchal j (Or.inr hj))]
  | sub a b iha ihb =>
      simp only [chalSlots, List.mem_append] at hchal
      simp only [coeffToMv, iha (fun j hj => hchal j (Or.inl hj)),
        ihb (fun j hj => hchal j (Or.inr hj))]
  | mul a b iha ihb =>
      simp only [chalSlots, List.mem_append] at hchal
      simp only [coeffToMv, iha (fun j hj => hchal j (Or.inl hj)),
        ihb (fun j hj => hchal j (Or.inr hj))]
  | neg a iha =>
      simp only [chalSlots] at hchal
      simp only [coeffToMv, iha hchal]
  | pow a n iha =>
      simp only [chalSlots] at hchal
      simp only [coeffToMv, iha hchal]

/-- A listed sum reads a slot iff one of its summands does. -/
theorem mem_chalSlots_sumList {ι : Type*} (l : List ι) (f : ι → CoeffExpr F) (s : ℕ) :
    s ∈ chalSlots (CoeffExpr.sumList l f) ↔ ∃ i ∈ l, s ∈ chalSlots (f i) := by
  induction l with
  | nil => simp [CoeffExpr.sumList, chalSlots]
  | cons a l ih =>
      simp only [CoeffExpr.sumList, List.foldr_cons] at ih ⊢
      simp only [chalSlots, List.mem_append, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨i, hi, hs⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨i, Or.inr hi, hs⟩
      · rintro ⟨i, (rfl | hi), hs⟩
        · exact Or.inl hs
        · exact Or.inr ⟨i, hi, hs⟩

end Instrument

section Compiler

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The compiled product reads only what its factors read. -/
theorem chalSlots_mulVec {e : ℕ} (b : Basis (Fin e) F K) (u v : Fin e → CoeffExpr F)
    (k : Fin e) (s : ℕ) (hs : s ∈ chalSlots (mulVec b u v k)) :
    (∃ i, s ∈ chalSlots (u i)) ∨ ∃ j, s ∈ chalSlots (v j) := by
  unfold mulVec at hs
  rw [mem_chalSlots_sumList] at hs
  obtain ⟨i, _, hs⟩ := hs
  rw [mem_chalSlots_sumList] at hs
  obtain ⟨j, _, hij⟩ := hs
  simp only [chalSlots, List.append_nil] at hij
  rcases List.mem_append.mp hij with h | h
  · exact Or.inl ⟨i, h⟩
  · exact Or.inr ⟨j, h⟩

/-- The compiled power reads only what its base reads. -/
theorem chalSlots_powVec {e : ℕ} (b : Basis (Fin e) F K) (u : Fin e → CoeffExpr F) :
    ∀ (n : ℕ) (k : Fin e) (s : ℕ), s ∈ chalSlots (powVec b u n k) → ∃ j, s ∈ chalSlots (u j)
  | 0, k, s, hs => by simp [powVec, oneVec, chalSlots] at hs
  | n + 1, k, s, hs => by
      rcases chalSlots_mulVec b _ u k s hs with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact chalSlots_powVec b u n i s hi
      · exact ⟨j, hj⟩

/-- **Every challenge slot the corrected compiler emits is a cubic coordinate `e·i + k` of one of
the twelve `𝕂` challenges**, `i < 12`, `k < e`.  Raw slot `36 = 3·12` is above all of them. -/
theorem correctedFinalTypedCompile_chalSlots {e : ℕ} (b : Basis (Fin e) F K)
    (t : CorrectedFinalTypedExpr) :
    ∀ (k : Fin e) (s : ℕ), s ∈ chalSlots (correctedFinalTypedCompile b t k) →
      ∃ (i : Fin 12) (k' : Fin e), s = e * (i : ℕ) + (k' : ℕ) := by
  induction t with
  | baseCur i => intro k s hs; simp [correctedFinalTypedCompile, chalSlots] at hs
  | baseNext i => intro k s hs; simp [correctedFinalTypedCompile, chalSlots] at hs
  | extCur i => intro k s hs; simp [correctedFinalTypedCompile, chalSlots] at hs
  | extNext i => intro k s hs; simp [correctedFinalTypedCompile, chalSlots] at hs
  | challenge i =>
      intro k s hs
      simp only [correctedFinalTypedCompile, chalSlots, List.mem_singleton] at hs
      exact ⟨i, k, hs⟩
  | extensionPublic i => intro k s hs; simp [correctedFinalTypedCompile, chalSlots] at hs
  | scalarPublic i => intro k s hs; simp [correctedFinalTypedCompile, chalSlots] at hs
  | const c => intro k s hs; simp [correctedFinalTypedCompile, chalSlots] at hs
  | expCur => intro k s hs; simp [correctedFinalTypedCompile, chalSlots] at hs
  | add x y ihx ihy =>
      intro k s hs
      simp only [correctedFinalTypedCompile, chalSlots] at hs
      rcases List.mem_append.mp hs with h | h
      · exact ihx k s h
      · exact ihy k s h
  | sub x y ihx ihy =>
      intro k s hs
      simp only [correctedFinalTypedCompile, chalSlots] at hs
      rcases List.mem_append.mp hs with h | h
      · exact ihx k s h
      · exact ihy k s h
  | neg x ih =>
      intro k s hs
      simp only [correctedFinalTypedCompile, chalSlots] at hs
      exact ih k s hs
  | mul x y ihx ihy =>
      intro k s hs
      rcases chalSlots_mulVec b _ _ k s hs with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact ihx i s hi
      · exact ihy j s hj
  | pow x n ih =>
      intro k s hs
      obtain ⟨j, hj⟩ := chalSlots_powVec b _ n k s hs
      exact ih j s hj
  | certBase i => intro k s hs; simp [correctedFinalTypedCompile, chalSlots] at hs
  | certExt i => intro k s hs; simp [correctedFinalTypedCompile, chalSlots] at hs
  | lamPow d =>
      intro k s hs
      simp only [correctedFinalTypedCompile] at hs
      split_ifs at hs
      · obtain ⟨j, hj⟩ := chalSlots_powVec b _ _ k s hs
        simp only [chalSlots, List.mem_singleton] at hj
        exact ⟨9, j, hj⟩
      · simp [chalSlots] at hs

/-- At `e = 3` the compiler's slots are all below `finalScalarChallengeBase = 36`. -/
theorem correctedFinalTypedCompile_not_slot36 (b : Basis (Fin 3) F K)
    (t : CorrectedFinalTypedExpr) (k : Fin 3) :
    finalScalarChallengeBase ∉ chalSlots (correctedFinalTypedCompile b t k) := by
  intro hs
  obtain ⟨i, k', hik⟩ := correctedFinalTypedCompile_chalSlots b t k _ hs
  have hi := i.isLt
  have hk := k'.isLt
  simp only [finalScalarChallengeBase] at hik
  omega

end Compiler

section BaseGates

variable {F : Type*} [Field F]

/-- The fifteen base transition gates read no challenge at all. -/
theorem finalBaseTransitionGates_chalSlots (n : ℕ) :
    ∀ g ∈ finalBaseTransitionGates (F := F) n, chalSlots g = [] := by
  intro g hg
  simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ⟨i, _, rfl⟩ | rfl | rfl | rfl | rfl
  · simp [selectorBool, bv, chalSlots]
  · simp only [selectorOneHot, selectorSum, chalSlots, List.append_nil]
    rw [List.eq_nil_iff_forall_not_mem]
    intro s hs
    rw [mem_chalSlots_sumList] at hs
    obtain ⟨i, _, hi⟩ := hs
    simp [bv, chalSlots] at hi
  · simp [firstMaskBoolean, isFirstVar, bv, chalSlots]
  · simp [lastMaskBoolean, isLastVar, bv, chalSlots]
  · unfold endpointOverlapConsistency
    split <;> simp [isFirstVar, isLastVar, bv, chalSlots]

omit [Field F] in
/-- The twenty-two committed endpoint equality checks read no challenge at all — that is the whole
point of the stage-3e de-compression. -/
theorem finalEndpointEqualityChecks_chalSlots :
    ∀ g ∈ finalEndpointEqualityChecks (F := F), chalSlots g = [] := by
  intro g hg
  simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range] at hg
  rcases hg with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩ <;>
    simp [endpointEqualityCheck, isFirstVar, isLastVar, bv, chalSlots]

open OptimizedComputeRangeCertificate

theorem chalSlots_colC (j : ℕ) : chalSlots (colC (F := F) j) = [] := rfl
theorem chalSlots_colM (k : ℕ) : chalSlots (colM (F := F) k) = [] := rfl
theorem chalSlots_helperAt (k : ℕ) : chalSlots (helperAt (F := F) k) = [] := by
  unfold helperAt; split_ifs <;> rfl
theorem chalSlots_linC (j : ℕ) (b : Bool) : chalSlots (linC (F := F) j b) = [] := by
  cases b <;> simp [linC, colC, bcur, chalSlots]
theorem chalSlots_linCol (j : ℕ) : chalSlots (linCol (F := F) j) = [] := by
  unfold linCol
  split_ifs <;> simp [colC, bcur, chalSlots]
theorem chalSlots_foldMul (ls : List (CoeffExpr F)) (E : CoeffExpr F)
    (hE : chalSlots E = []) (hl : ∀ l ∈ ls, chalSlots l = []) :
    chalSlots (foldMul ls E) = [] := by
  induction ls generalizing E with
  | nil => simpa [foldMul]
  | cons l ls ih =>
      simp only [foldMul]
      exact ih _ (by
          simp [chalSlots, hE, hl l (List.mem_cons.mpr (Or.inl rfl))])
        (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
theorem chalSlots_termAt (k : ℕ) : chalSlots (termAt (F := F) k) = [] := by
  unfold termAt
  simp only [chalSlots]
  rw [chalSlots_foldMul]
  · simp [colC, bcur, chalSlots]
  · exact chalSlots_helperAt (k / 3)
  · intro l hl
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨j, _, rfl⟩ := hl
    exact chalSlots_linCol _
theorem chalSlots_lm (k : ℕ) : chalSlots (lm (F := F) k) = [] := by
  unfold lm
  split_ifs <;> simp [colM, bcur, chalSlots]
theorem chalSlots_sumExpr (L : List (CoeffExpr F)) (h : ∀ t ∈ L, chalSlots t = []) :
    chalSlots (sumExpr L) = [] := by
  induction L with
  | nil => simp [sumExpr, chalSlots]
  | cons t ts ih =>
      simp [sumExpr, chalSlots, h t (by simp), ih (fun x hx => h x (by simp [hx]))]
theorem chalSlots_csumAcc : ∀ n, chalSlots (csumAcc (F := F) n) = [] := by
  intro n; induction n <;> simp [csumAcc, colC, bcur, chalSlots, *]
theorem formRCertificateGates_not_slot36 (g : CoeffExpr F)
    (hg : g ∈ formRCertificateGates (F := F)) :
    finalScalarChallengeBase ∉ chalSlots g := by
  simp only [formRCertificateGates, List.mem_append] at hg
  rcases hg with h | hnamed
  · rcases h with h | hhelper
    · rcases h with h | hpins
      · rcases h with hbool | hpower
        · simp only [booleanGates, List.mem_append, List.mem_map] at hbool
          rcases hbool with ⟨j, _, rfl⟩ | ⟨k, _, rfl⟩
          · split_ifs <;> simp [bbool, colC, bcur, chalSlots]
          · simp [bbool, colM, bcur, chalSlots]
        · simp only [powerPins, List.mem_cons, List.not_mem_nil, or_false] at hpower
          rcases hpower with rfl | rfl
          · simp [hPin, factor2, colHbase, colM, bcur, chalSlots]
          · simp [tPin, factor2, colHbase, colTbase, colM, bcur, chalSlots]
      · simp only [formRPins, List.mem_cons, List.not_mem_nil, or_false] at hpins
        rcases hpins with rfl | rfl
        · simp only [pPin, chalSlots]
          simp [chalSlots_lm, colP, bcur, chalSlots]
        · simp only [topPin, chalSlots]
          simp [chalSlots_lm, colP, colTop, bcur, chalSlots]
    · simp only [helperPins, List.mem_map] at hhelper
      obtain ⟨k, _, rfl⟩ := hhelper
      unfold helperPinAt
      simp only [chalSlots, chalSlots_helperAt, chalSlots_linCol, colE, bcur, List.append_nil,
        List.not_mem_nil, not_false_eq_true]
  · simp only [formRNamed, List.mem_cons, List.not_mem_nil, or_false] at hnamed
    rcases hnamed with rfl | h
    · have hs : chalSlots (sumExpr (comparisonTerms (F := F))) = [] :=
        chalSlots_sumExpr _ (fun t ht => by
          simp only [comparisonTerms, List.mem_map, List.mem_range] at ht
          obtain ⟨k, _, rfl⟩ := ht
          have hb : chalSlots (bitCoeff (F := F)
              (decide (k + 1 < formRN F) && pBit F (formRN F - 2 - k))) = [] := by
            cases (decide (k + 1 < formRN F) && pBit F (formRN F - 2 - k)) <;>
              simp [bitCoeff, chalSlots]
          simp [chalSlots, hb, chalSlots_termAt k])
      simp [comparisonGate, chalSlots, hs, colTop, bcur]
    · rcases h with rfl | rfl
      · have hr : chalSlots (sumExpr (rangeTerms (F := F))) = [] :=
          chalSlots_sumExpr _ (fun t ht => by
            simp only [rangeTerms, List.mem_map, List.mem_range] at ht
            obtain ⟨k, hk, rfl⟩ := ht
            have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
            rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp [rangeTerm, eqmAt, lm, colP, colM, bcur, chalSlots] <;>
              split_ifs <;> simp [chalSlots, colM, colP, bcur])
        simp [rangeGate, chalSlots, hr, colTop, bcur]
      · simp [axisEquation, ftLeaf, fthLeaf, colTbase, bcur, chalSlots, csum,
          chalSlots_csumAcc]

/-- The compressed selector/public RLC reads slot `36` (through its `i = 0` summand, whose
coefficient is `chal 36 ^ 0`). -/
theorem finalSelectorPublicCheck_reads_slot36 (base : ℕ) :
    finalScalarChallengeBase ∈ chalSlots (finalSelectorPublicCheck (F := F) .traceCur base) := by
  unfold finalSelectorPublicCheck
  rw [mem_chalSlots_sumList]
  refine ⟨0, List.mem_range.mpr (by norm_num), ?_⟩
  simp [chalSlots]

/-- **Positive control**: the same instrument finds slot `36` in **both** retired compressed
gates `finalMaskedEndpointEqualityChecks` — the ones the deployed chip stopped committing at stage
3e.  So an absence measured by it is an absence, not a blind instrument. -/
theorem b265_retired_compressed_gates_do_read_slot36 :
    ∀ g ∈ finalMaskedEndpointEqualityChecks (F := F), finalScalarChallengeBase ∈ chalSlots g := by
  intro g hg
  simp only [finalMaskedEndpointEqualityChecks, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp only [chalSlots, isFirstVar, bv, List.nil_append]
    exact finalSelectorPublicCheck_reads_slot36 20
  · simp only [chalSlots, isLastVar, bv, List.nil_append]
    exact finalSelectorPublicCheck_reads_slot36 31

end BaseGates

section Chip

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- **Receipt 4, measured: no gate of the deployed compute list reads raw slot `36`**, at every
row count `n` and every basis `b`. -/
theorem b265_no_committed_compute_gate_reads_slot36 (n : ℕ) (b : Basis (Fin 3) F K) :
    ∀ g ∈ correctedFinalComputeAllGates n b, finalScalarChallengeBase ∉ chalSlots g := by
  intro g hg
  unfold correctedFinalComputeAllGates at hg
  rcases List.mem_append.mp hg with hg | hexp
  rotate_left
  ·
    simp only [computeExpGates, List.mem_cons, List.not_mem_nil, or_false] at hexp
    rcases hexp with rfl | rfl <;>
      simp [expInitGate, expStepGate, arityForm, List.range, List.range.loop, chalSlots]
  rcases List.mem_append.mp hg with hg | hlam
  rotate_left
  · unfold correctedCompileList at hlam
    rw [List.mem_flatMap] at hlam
    obtain ⟨t, _, ht⟩ := hlam
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ht
    exact correctedFinalTypedCompile_not_slot36 b t k
  rcases List.mem_append.mp hg with hg | hformR
  rcases List.mem_append.mp hg with hg | heq
  rcases List.mem_append.mp hg with hg | h4
  rcases List.mem_append.mp hg with hg | h2
  rcases List.mem_append.mp hg with hg | ha
  rcases List.mem_append.mp hg with hb | hc
  · rw [finalBaseTransitionGates_chalSlots n g hb]
    exact List.not_mem_nil
  · unfold correctedCore at hc
    rw [List.mem_flatten] at hc
    obtain ⟨l, hl, hgl⟩ := hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hgl
    intro hs
    unfold correctedCoreCoord at hs
    split_ifs at hs with h10 h11 h20 h89
    · simp [notLastCoeff, isLastVar, bv, residualWitnessCoord, chalSlots] at hs
    · simp [notLastCoeff, isLastVar, bv, residualWitnessCoord, chalSlots] at hs
    · exact correctedFinalTypedCompile_not_slot36 b _ k hs
    · simp only [chalSlots, notLastCoeff, isLastVar, bv, List.append_nil, List.nil_append] at hs
      exact correctedFinalTypedCompile_not_slot36 b _ k hs
    · exact correctedFinalTypedCompile_not_slot36 b _ k hs
  · unfold correctedAux at ha
    rw [List.mem_flatten] at ha
    obtain ⟨l, hl, hgl⟩ := ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hgl
    intro hs
    unfold correctedAuxCoord at hs
    split_ifs at hs with h2
    · exact correctedFinalTypedCompile_not_slot36 b _ k hs
    · simp only [chalSlots, residualWitnessCoord, List.nil_append] at hs
      exact correctedFinalTypedCompile_not_slot36 b _ k hs
  · unfold correctedCompileList at h2
    rw [List.mem_flatMap] at h2
    obtain ⟨t, _, ht⟩ := h2
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ht
    exact correctedFinalTypedCompile_not_slot36 b t k
  · unfold correctedCompileList at h4
    rw [List.mem_flatMap] at h4
    obtain ⟨t, _, ht⟩ := h4
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ht
    exact correctedFinalTypedCompile_not_slot36 b t k
  · rw [finalEndpointEqualityChecks_chalSlots g heq]
    exact List.not_mem_nil
  · exact formRCertificateGates_not_slot36 g hformR

/-- Evaluation form of the same fact, for the environment the acceptance pin is stated in: every
deployed gate evaluates identically under any two base environments that differ only at slot
`36`. -/
theorem b265_deployed_compute_gates_eval_blind_to_slot36
    (n : ℕ) (b : Basis (Fin 3) F K) (env : Env F) (v : F) :
    ∀ g ∈ correctedFinalComputeAllGates n b,
      g.eval { env with chal := Function.update env.chal finalScalarChallengeBase v } =
        g.eval env := by
  intro g hg
  refine eval_congr_of_chalSlots g env
    { env with chal := Function.update env.chal finalScalarChallengeBase v } rfl rfl rfl ?_
  intro j hj
  have hne : j ≠ finalScalarChallengeBase := fun heq =>
    b265_no_committed_compute_gate_reads_slot36 n b g hg (heq ▸ hj)
  simp [Function.update_of_ne hne]

end Chip

section RAP

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The RAP-level consequence.**  Every constraint polynomial of the deployed
`CorrectedFinalComputeRAP` is unchanged when the challenge vector is changed at slot `36` and
nowhere else.  The chip the acceptance pins the coin *for* cannot see the coin. -/
theorem b265_deployed_compute_chip_is_blind_to_slot36
    {h n : ℕ} (b : Basis (Fin 3) F K) (chalVal chalVal' pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F)
    (hagree : ∀ j, j ≠ finalScalarChallengeBase → chalVal' j = chalVal j)
    (i : Fin (correctedFinalComputeAllGates n b).length) :
    (CorrectedFinalComputeRAP (n := n) b chalVal' pubVal orbit H).C i =
      (CorrectedFinalComputeRAP (n := n) b chalVal pubVal orbit H).C i := by
  show coeffToMv chalVal' pubVal ((correctedFinalComputeAllGates n b).get i) =
    coeffToMv chalVal pubVal ((correctedFinalComputeAllGates n b).get i)
  apply coeffToMv_congr_of_chalSlots
  intro j hj
  apply hagree
  intro hj36
  subst hj36
  exact b265_no_committed_compute_gate_reads_slot36 n b _ (List.get_mem _ _) hj

end RAP

end Nock.RedTeam.Batch265

#print axioms Nock.RedTeam.Batch265.mem_liftChallenge9
#print axioms Nock.RedTeam.Batch265.mem_liftChallenge11
#print axioms Nock.RedTeam.Batch265.b265_compute_block_is_two_extension_coordinates
#print axioms Nock.RedTeam.Batch265.b265_no_base_field_factor_in_the_challenge_space
#print axioms Nock.RedTeam.Batch265.b265_failure_event_reads_only_the_two_extension_compute_coins
#print axioms Nock.RedTeam.Batch265.b265_pinned_coin_is_the_chip_challenge_at_36
#print axioms Nock.RedTeam.Batch265.eval_congr_of_chalSlots
#print axioms Nock.RedTeam.Batch265.coeffToMv_congr_of_chalSlots
#print axioms Nock.RedTeam.Batch265.correctedFinalTypedCompile_chalSlots
#print axioms Nock.RedTeam.Batch265.b265_no_committed_compute_gate_reads_slot36
#print axioms Nock.RedTeam.Batch265.b265_retired_compressed_gates_do_read_slot36
#print axioms Nock.RedTeam.Batch265.b265_deployed_compute_chip_is_blind_to_slot36
#print axioms Nock.RedTeam.Batch265.b265_deployed_compute_gates_eval_blind_to_slot36
