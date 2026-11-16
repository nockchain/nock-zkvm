import Nock.AIRPacked
import Nock.NockVMROM.Thm54.OptimizedComputeCoreInventory
import Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
import Nock.NockVMROM.Thm54.ComputeWalkLabel

/-!
# Concrete repaired optimized-compute extension gate basis

The production extension list `finalExtTransitionGates` commits the
paper's selector-packed non-IO basis plus the four sampled-IO expressions, with **no** `challenge9` fold.
The seventeen `finalRlcFold`s remain as `finalNonIOTransitionGates` for the exactness theorems
in `ComputePaperPacking` (stage 1); they are not in the deployed chip.

Until this stage the production final
family used the disjoint compiler challenge 9. Exactness of those folds is stated under the
explicit collision-free premise; a compiled cancellation example shows why that premise may not
be erased.  The packed basis needs no such premise (`deployed_of_paperPacking`).
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeGateBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Nock
open Nock.Reified
open Nock.ComputeTable
open OptimizedComputeSubstitution
open OptimizedComputeFiniteIOGates

/-- Challenge used only to compress finite optimized gate families. -/
def foldChallenge : Expr := .Var .challenge 8

def finalFoldChallenge : Expr := .Var .challenge compilerChallengeBase

/-- Horner-style random linear combination of a finite expression family. -/
def rlcFold : List Expr → Expr
  | [] => .Const 0
  | e :: es => .Add e (.Mul foldChallenge (rlcFold es))

def finalRlcFold : List Expr → Expr
  | [] => .Const 0
  | e :: es => .Add e (.Mul finalFoldChallenge (finalRlcFold es))

@[simp] theorem rlcFold_eval_nil {K : Type*} [Field K] (env : Env K) :
    (rlcFold []).eval env = 0 := by
  simp [rlcFold, Expr.eval]

theorem rlcFold_eval_of_all_zero {K : Type*} [Field K]
    (env : Env K) (es : List Expr)
    (h : ∀ e ∈ es, e.eval env = 0) :
    (rlcFold es).eval env = 0 := by
  induction es with
  | nil => simp [rlcFold, Expr.eval]
  | cons e es ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [rlcFold, Expr.eval, h.1, ih h.2]

theorem finalRlcFold_eval_of_all_zero {K : Type*} [Field K]
    (env : Env K) (es : List Expr)
    (h : ∀ e ∈ es, e.eval env = 0) :
    (finalRlcFold es).eval env = 0 := by
  induction es with
  | nil => simp [finalRlcFold, Expr.eval]
  | cons e es ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [finalRlcFold, Expr.eval, h.1, ih h.2]

/-- Exact bad-event exclusion for one finite RLC family. -/
def CollisionFree {K : Type*} [Field K] (env : Env K) (es : List Expr) : Prop :=
  (rlcFold es).eval env = 0 → ∀ e ∈ es, e.eval env = 0

/-- Production challenge-9 exclusion for one concrete family. -/
def FinalCollisionFree {K : Type*} [Field K] (env : Env K) (es : List Expr) : Prop :=
  (finalRlcFold es).eval env = 0 → ∀ e ∈ es, e.eval env = 0

/-- Exact production collision event: the fold vanishes although at least one source does not. -/
def FinalCollisionEvent {K : Type*} [Field K] (env : Env K) (es : List Expr) : Prop :=
  (finalRlcFold es).eval env = 0 ∧ ∃ e ∈ es, e.eval env ≠ 0

theorem not_finalCollisionFree_iff_event {K : Type*} [Field K]
    (env : Env K) (es : List Expr) :
    ¬ FinalCollisionFree env es ↔ FinalCollisionEvent env es := by
  simp [FinalCollisionFree, FinalCollisionEvent]

theorem finalRlcFold_zero_iff {K : Type*} [Field K]
    (env : Env K) (es : List Expr) (hfree : FinalCollisionFree env es) :
    (finalRlcFold es).eval env = 0 ↔ ∀ e ∈ es, e.eval env = 0 :=
  ⟨hfree, finalRlcFold_eval_of_all_zero env es⟩

theorem rlcFold_zero_iff {K : Type*} [Field K]
    (env : Env K) (es : List Expr) (hfree : CollisionFree env es) :
    (rlcFold es).eval env = 0 ↔ ∀ e ∈ es, e.eval env = 0 :=
  ⟨hfree, rlcFold_eval_of_all_zero env es⟩

/-- RLC compression does not increase trace degree because `foldChallenge` has degree zero. -/
theorem rlcFold_degree_le (es : List Expr) (d : ℕ)
    (h : ∀ e ∈ es, e.degree ≤ d) :
    (rlcFold es).degree ≤ d := by
  induction es with
  | nil => simp [rlcFold, Expr.degree]
  | cons e es ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp only [rlcFold, Expr.degree, foldChallenge, zero_add]
      exact max_le h.1 (ih h.2)

/-- Cancellation is real without the explicit RLC premise. -/
def cancellationEnv : Env ℚ where
  trace := fun _ => 0
  traceNext := fun _ => 0
  chal := fun i => if i = 8 then 1 else 0
  pub := fun _ => 0

theorem cancellation_counterexample :
    (rlcFold [.Const 1, .Const (-1)]).eval cancellationEnv = 0 ∧
      ¬ (∀ e ∈ ([.Const 1, .Const (-1)] : List Expr),
        e.eval cancellationEnv = 0) := by
  constructor
  · norm_num [rlcFold, foldChallenge, cancellationEnv, Expr.eval]
  · simp [Expr.eval]

/-! ## Source-family partition -/

/-- Exact slices of the repaired per-state source list. -/
def stateBlock : State → List Expr
  | .s0 => refoldedPerStateGates.take 46
  | .s1 => (refoldedPerStateGates.drop 46).take 47
  | .s2 => (refoldedPerStateGates.drop 93).take 41
  | .s3 => (refoldedPerStateGates.drop 134).take 47
  | .s4 => (refoldedPerStateGates.drop 181).take 46
  | .s5 => (refoldedPerStateGates.drop 227).take 48
  | .s6 => (refoldedPerStateGates.drop 275).take 50
  | .s7 => (refoldedPerStateGates.drop 325).take 44
  | .s8 => (refoldedPerStateGates.drop 369).take 45
  | .s9 => (refoldedPerStateGates.drop 414).take 43
  | .cons => (refoldedPerStateGates.drop 457).take 42

/-- Selector sum activating the four nonlinear equations participating in the combined gate. -/
def combinedSelectorExpr : Expr :=
  .Add (.Add (.Add (tc 3) (tc 5)) (tc 8)) (tc 10)

/-- Selector-activated transcription of the paper's displayed four-way nonlinear fold.  This is `Σ op_s * (g_s - 1) = 0`, so inactive opcodes contribute
zero.  The OP8 term retains the corrected subject-size factor. -/
def combinedSourceExpr : Expr :=
  .Sub
    (.Add
      (.Add
        (.Add
          (.Mul (tc 3)
            (.Add (.Mul (tc 92) (.Sub (chl 1) Nock.Reified.cSf1e.size))
              Nock.Reified.cE.leaf))
          (.Mul (tc 5)
            (.Mul (tc 92)
              (.Add
                (.Add
                  (.Add (.Mul (chl 2)
                    (.Sub Nock.Reified.cSf1e.size Nock.Reified.cSf2e.size))
                    (.Mul (chl 3)
                      (.Sub Nock.Reified.cSf1e.dyck Nock.Reified.cSf2e.dyck)))
                  (.Mul (chl 4)
                    (.Sub Nock.Reified.cSf1e.leaf Nock.Reified.cSf2e.leaf)))
                (.Sub (.Const 1) Nock.Reified.cE.leaf)))))
        (.Mul (tc 8)
          (.Mul (.Mul Nock.Reified.cSf2e.size Nock.Reified.cS.size) (tc 92))))
      (.Mul (tc 10)
        (.Mul (.Mul Nock.Reified.cSf1e.size Nock.Reified.cSf2e.size) (tc 92))))
    combinedSelectorExpr

def optimizedCombinedGate : Expr := combinedSourceExpr.subst computeSubst

theorem optimizedCombinedGate_degree : optimizedCombinedGate.degree = 4 := by
  decide

/-- The twenty concrete non-IO source families before the repaired three pair-folds. -/
def sourceFamilies20 : List (List Expr) :=
  [[sv4Expr.subst computeSubst],
   [sv5Expr.subst computeSubst],
   [sv6Expr.subst computeSubst],
   (formulaExprs.map (fun e => e.subst computeSubst)) ++ [optimizedCombinedGate],
   [zZinvExpr.subst computeSubst],
   [Trans.lnChainExpr.subst computeSubst],
   [Trans.walkLnStep.subst walkSubst],
   [Trans.walkCountStep.subst walkSubst],
   [Trans.walkAccStep.subst walkSubst],
   stateBlock .s0, stateBlock .s1, stateBlock .s2, stateBlock .s3,
   stateBlock .s4, stateBlock .s5, stateBlock .s6, stateBlock .s7,
   stateBlock .s8, stateBlock .s9, stateBlock .cons]

@[simp] theorem sourceFamilies20_length : sourceFamilies20.length = 20 := rfl

/-- Exactly three compatible opcode-family pairs are combined: OP0/OP1, OP2/OP3, OP4/OP5. -/
def nonIOSourceFamilies17With (walkS : VarKind → ℕ → Expr) : List (List Expr) :=
  [(stateBlock .s0 ++ stateBlock .s1),
   (stateBlock .s2 ++ stateBlock .s3),
   (stateBlock .s4 ++ stateBlock .s5),
   [sv4Expr.subst computeSubst],
   [sv5Expr.subst computeSubst],
   [sv6Expr.subst computeSubst],
   (formulaExprs.map (fun e => e.subst computeSubst)) ++ [optimizedCombinedGate],
   [zZinvExpr.subst computeSubst],
   [Trans.lnChainExpr.subst computeSubst],
   [Trans.walkLnStep.subst walkS],
   [Trans.walkCountStep.subst walkS],
   [Trans.walkAccStep.subst walkS],
   stateBlock .s6, stateBlock .s7, stateBlock .s8, stateBlock .s9,
   stateBlock .cons]

def nonIOSourceFamilies17 : List (List Expr) :=
  nonIOSourceFamilies17With walkSubst

/-- Production source families against the direct final 13/62 layout. -/
def finalNonIOSourceFamilies17 : List (List Expr) :=
  nonIOSourceFamilies17With ComputeWalkLabel.finalWalkSubstInGate

@[simp] theorem nonIOSourceFamilies17_length :
    nonIOSourceFamilies17.length = 17 := rfl

set_option maxRecDepth 20000 in
theorem nonIOSourceFamilies17_nonempty :
    ∀ es ∈ nonIOSourceFamilies17, es ≠ [] := by
  decide

/-- Complete source coverage is unchanged by the three pair-folds. -/
theorem nonIO_source_coverage (e : Expr) :
    e ∈ nonIOSourceFamilies17.flatten ↔ e ∈ sourceFamilies20.flatten := by
  simp [nonIOSourceFamilies17, nonIOSourceFamilies17With, sourceFamilies20]
  aesop

theorem complete_nonIO_source_partition :
    sourceFamilies20.flatten.length = 511 ∧
      nonIOSourceFamilies17.flatten.length = 511 ∧
      sourceFamilies20.flatten.Nodup ∧
      nonIOSourceFamilies17.flatten.Nodup ∧
      optimizedCombinedGate ∈ sourceFamilies20.flatten := by
  set_option maxRecDepth 100000 in
  decide

/-- The seventeen concrete non-IO extension gates. -/
def nonIOTransitionGates : List Expr :=
  nonIOSourceFamilies17.map rlcFold

def finalNonIOTransitionGates : List Expr :=
  finalNonIOSourceFamilies17.map finalRlcFold

/-- Collision exclusion for all seventeen production folds on one exact row environment. -/
def FinalComputeCollisionFree {K : Type*} [Field K] (env : Env K) : Prop :=
  ∀ es ∈ finalNonIOSourceFamilies17, FinalCollisionFree env es

/-- Union of the exact seventeen production collision events on the same row environment. -/
def FinalComputeCollisionEvent {K : Type*} [Field K] (env : Env K) : Prop :=
  ∃ es ∈ finalNonIOSourceFamilies17, FinalCollisionEvent env es

/-- Exact univariate workload of the seventeen production folds: a family of length `m` contributes
at most `m-1` roots when its constituent vector is nonzero. -/
def finalComputeRLCWorkload : ℕ :=
  (finalNonIOSourceFamilies17.map fun es => es.length - 1).sum

theorem finalComputeRLCWorkload_exact :
    finalComputeRLCWorkload = 494 := by
  set_option maxRecDepth 100000 in
  decide

theorem not_finalComputeCollisionFree_iff_event {K : Type*} [Field K]
    (env : Env K) :
    ¬ FinalComputeCollisionFree env ↔ FinalComputeCollisionEvent env := by
  constructor
  · intro h
    simp only [FinalComputeCollisionFree, not_forall] at h
    obtain ⟨es, hes, hbad⟩ := h
    exact ⟨es, hes, (not_finalCollisionFree_iff_event env es).1 hbad⟩
  · rintro ⟨es, hes, hbad⟩ hfree
    exact ((not_finalCollisionFree_iff_event env es).2 hbad) (hfree es hes)

/-- Honest source equations imply every production fold without any collision hypothesis. -/
theorem finalNonIOTransitionGates_complete {K : Type*} [Field K]
    (env : Env K)
    (hsource : ∀ e ∈ finalNonIOSourceFamilies17.flatten, e.eval env = 0) :
    ∀ g ∈ finalNonIOTransitionGates, g.eval env = 0 := by
  intro g hg
  obtain ⟨es, hes, rfl⟩ := List.mem_map.mp hg
  apply finalRlcFold_eval_of_all_zero
  intro e he
  exact hsource e (List.mem_flatten.mpr ⟨es, hes, he⟩)

/-- Production fold soundness under the exact same-row challenge-9 exclusion. -/
theorem finalNonIOTransitionGates_sound {K : Type*} [Field K]
    (env : Env K) (hfree : FinalComputeCollisionFree env)
    (hgates : ∀ g ∈ finalNonIOTransitionGates, g.eval env = 0) :
    ∀ e ∈ finalNonIOSourceFamilies17.flatten, e.eval env = 0 := by
  intro e he
  obtain ⟨es, hes, heEs⟩ := List.mem_flatten.mp he
  have hfold : (finalRlcFold es).eval env = 0 := by
    apply hgates
    exact List.mem_map.mpr ⟨es, hes, rfl⟩
  exact hfree es hes hfold e heEs

@[simp] theorem nonIOTransitionGates_length :
    nonIOTransitionGates.length = 17 := by
  simp [nonIOTransitionGates]

/-- Exact family-fold semantics under the explicit finite collision exclusions. -/
theorem nonIOTransitionGates_eval_iff {K : Type*} [Field K]
    (env : Env K)
    (hfree : ∀ es ∈ nonIOSourceFamilies17, CollisionFree env es) :
    (∀ g ∈ nonIOTransitionGates, g.eval env = 0) ↔
      ∀ e ∈ sourceFamilies20.flatten, e.eval env = 0 := by
  constructor
  · intro hg e he
    have he' : e ∈ nonIOSourceFamilies17.flatten :=
      (nonIO_source_coverage e).2 he
    obtain ⟨es, hes, heEs⟩ := List.mem_flatten.mp he'
    have hfold : (rlcFold es).eval env = 0 := by
      apply hg
      exact List.mem_map.mpr ⟨es, hes, rfl⟩
    have hall := (rlcFold_zero_iff env es (hfree es hes)).1 hfold
    exact hall e heEs
  · intro hall g hg
    obtain ⟨es, hes, rfl⟩ := List.mem_map.mp hg
    apply rlcFold_eval_of_all_zero env es
    intro e he
    apply hall e
    apply (nonIO_source_coverage e).1
    exact List.mem_flatten.mpr ⟨es, hes, he⟩

/-! ## Repaired 17+4 extension allocation -/

/-- Named finite IDs for all twenty-one optimized extension transition gates. -/
abbrev ExtGateId := Fin 21

def allExtGateIds : List ExtGateId := List.ofFn id

theorem allExtGateIds_nodup : allExtGateIds.Nodup := by
  rw [allExtGateIds, List.nodup_ofFn]
  exact Function.injective_id

@[simp] theorem allExtGateIds_length : allExtGateIds.length = 21 := by
  simp [allExtGateIds]

def extTransitionGates : List Expr :=
  nonIOTransitionGates ++ legacySampledIOTransitionGates

/-- Production sampled gates with their two challenges shifted past the walk namespace. -/
def finalSampledIOTransitionGates : List Expr :=
  optimizedSampledIOTransitionGates.map (fun e => e.subst finalSampledNamespace)

/-! The 17 `finalRlcFold`s are replaced in `finalExtTransitionGates` by the paper's selector-packed
basis.  Construction is the stage-1 object `ComputePaperPacking.paperPackingNonIOGates`, moved
here so the deployed list can read it without an import cycle. -/

/-- The 66 packed classes substituted verbatim.  Two of them — the OP3 and OP5 output-bit
booleanities — reach trace degree `5`; `refoldLeafBool` repairs them. -/
def packedTableOptimizedRaw : List Expr :=
  allPacked.map (fun e => e.subst computeSubst)

/-- The tree's existing degree repair, in map form: the two degree-5 bodies are replaced by the
direct fixed-role refolds `op3ELeafBoolRefold` / `op5ELeafBoolRefold` (degree `3`). -/
def refoldLeafBool (e : Expr) : Expr :=
  if e = op3ELeafBool.subst computeSubst then op3ELeafBoolRefold
  else if e = op5ELeafBool.subst computeSubst then op5ELeafBoolRefold
  else e

/-- **The paper's selector-packed equality/nonlinear/memory classes in the optimized layout**.  66 `𝕂`-valued gates, no fold coin. -/
def packedTableOptimized : List Expr :=
  packedTableOptimizedRaw.map refoldLeafBool

/-- Always-on `𝕂` prefix: SV4–SV6 and `f = cons(f_h, f_t)` (`:1848`).
It is **not** committed here; honest rows still set
`exactFinalChallenge 5 = z⁻¹` (`OptimizedComputeSameExecution.exactFinalChallenge`). -/
def alwaysOnOptimized : List Expr :=
  [sv4Expr.subst computeSubst, sv5Expr.subst computeSubst, sv6Expr.subst computeSubst] ++
    formulaExprs.map (fun e => e.subst computeSubst)

/-- Cross-row singletons: `ln_prev(i+1) = ln(i)` and the three walk
recurrences (`:835`, `:840`, `:848-850`). -/
def crossRowSingletons : List Expr :=
  [Trans.lnChainExpr.subst computeSubst,
   Trans.walkLnStep.subst ComputeWalkLabel.finalWalkSubstInGate,
   Trans.walkCountStep.subst ComputeWalkLabel.finalWalkSubstInGate,
   Trans.walkAccStep.subst ComputeWalkLabel.finalWalkSubstInGate]

/-- Ratio-form queue gates: `count` is overlay coordinate 0,
`ln` the dedicated walk line, `walk_inv` extension role 62.  `notLast` / `isLast` are the
fixed preprocessing columns 11/12.  Compute `count` is an overlay reconstruction (degree 2),
so the masked non-empty gate is degree 4 (budget); the abstract form is degree 3 when
`count` is a column. -/
def walkQueueNonEmpty : Expr :=
  .Mul (.Sub (.Const 1) (.Var .traceCur 12))
    (.Sub
      (.Mul (walkInv .traceCur)
        (.Sub (overlayCoord .traceCur 0) (finalWalkLine .traceCur)))
      (.Const 1))

def walkQueueTiling : Expr :=
  .Mul (.Var .traceCur 12)
    (.Sub (overlayCoord .traceCur 0) (finalWalkLine .traceCur))

def queueWitnessGates : List Expr := [walkQueueNonEmpty, walkQueueTiling]

/-- **The coin-free non-IO transition gate set.**  78 `𝕂`-valued gates: 66 packed classes, 6
always-on, 4 cross-row, 2 queue-witness.  No challenge `9`. -/
def paperPackingNonIOGates : List Expr :=
  packedTableOptimized ++ alwaysOnOptimized ++ crossRowSingletons ++ queueWitnessGates

/-- Row-local (no successor) subset: 66 packed classes + 6 always-on.  The four
cross-row singletons are excluded; they are last-row-masked or residual. -/
def paperPackingRowLocal : List Expr :=
  packedTableOptimized ++ alwaysOnOptimized

theorem paperPackingRowLocal_length : paperPackingRowLocal.length = 72 := by
  decide

theorem paperPacking_eq_rowLocal_append :
    paperPackingNonIOGates =
      paperPackingRowLocal ++ crossRowSingletons ++ queueWitnessGates := rfl

theorem paperPackingNonIOGates_length : paperPackingNonIOGates.length = 78 := by
  decide

def legacyFinalSampledIOTransitionGates : List Expr :=
  legacySampledIOTransitionGates.map (fun e => e.subst finalSampledNamespace)

/-- Kept for the pre-correction compiler (`OptimizedComputeFinal`); production reads
`finalExtTransitionGates` (the packed 81). -/
def historicalFinalExtTransitionGates : List Expr :=
  finalNonIOTransitionGates ++ legacyFinalSampledIOTransitionGates

@[simp] theorem historicalFinalExtTransitionGates_length :
    historicalFinalExtTransitionGates.length = 21 := by
  simp [historicalFinalExtTransitionGates, finalNonIOTransitionGates,
    finalNonIOSourceFamilies17, nonIOSourceFamilies17With,
    legacyFinalSampledIOTransitionGates]

def finalExtTransitionGates : List Expr :=
  paperPackingNonIOGates ++ finalSampledIOTransitionGates

@[simp] theorem finalExtTransitionGates_length :
    finalExtTransitionGates.length = 82 := by
  simp [finalExtTransitionGates, paperPackingNonIOGates_length,
    finalSampledIOTransitionGates]

@[simp] theorem extTransitionGates_length :
    extTransitionGates.length = 21 := by
  simp [extTransitionGates]

/-- Total ID-to-gate map. -/
def extGate (id : ExtGateId) : Expr :=
  extTransitionGates.get ⟨id, by simpa using id.isLt⟩

theorem extGate_mem (id : ExtGateId) :
    extGate id ∈ extTransitionGates :=
  List.get_mem _ _

/-- Every concrete extension gate is named by exactly one finite position. -/
theorem extGate_coverage (g : Expr) :
    g ∈ extTransitionGates ↔ ∃ id : ExtGateId, extGate id = g := by
  constructor
  · intro hg
    obtain ⟨n, hn⟩ := List.get_of_mem hg
    exact ⟨⟨n, by simpa using n.isLt⟩, hn⟩
  · rintro ⟨id, rfl⟩
    exact extGate_mem id

theorem extTransitionGates_nonzero :
    ∀ g ∈ extTransitionGates, g ≠ (.Const 0 : Expr) := by
  intro g hg
  simp only [extTransitionGates, List.mem_append] at hg
  rcases hg with hg | hg
  · obtain ⟨es, hes, rfl⟩ := List.mem_map.mp hg
    have hne := nonIOSourceFamilies17_nonempty es hes
    cases es with
    | nil => contradiction
    | cons e es => simp [rlcFold]
  · change g ∈ [legacySampledDenomPin .traceCur 0, legacySampledDenomPin .traceCur 1,
      legacySampledDenomPin .traceCur 2, optimizedFoldedProgStep3] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · unfold optimizedFoldedProgStep3
      change Expr.Sub _ _ ≠ .Const 0
      intro h
      cases h

set_option maxRecDepth 20000 in
theorem nonIOTransitionGates_degree :
    ∀ g ∈ nonIOTransitionGates, g.degree ≤ 4 := by
  decide

theorem extTransitionGates_degree :
    ∀ g ∈ extTransitionGates, g.degree ≤ 4 := by
  intro g hg
  simp only [extTransitionGates, List.mem_append] at hg
  rcases hg with hg | hg
  · exact nonIOTransitionGates_degree g hg
  · exact legacySampledIOTransitionGates_degree g hg

#print axioms cancellation_counterexample
#print axioms nonIO_source_coverage
#print axioms nonIOTransitionGates_eval_iff
#print axioms not_finalComputeCollisionFree_iff_event
#print axioms finalNonIOTransitionGates_complete
#print axioms finalNonIOTransitionGates_sound
#print axioms extGate_coverage
#print axioms allExtGateIds_nodup
#print axioms extTransitionGates_nonzero
#print axioms extTransitionGates_degree

end OptimizedComputeGateBasis
end Nock.NockVMROM.Thm54
