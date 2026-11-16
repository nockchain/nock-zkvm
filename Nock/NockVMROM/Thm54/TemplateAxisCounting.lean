import Nock.NockVMROM.Thm54.TemplateRawJointSoundness

/-!
# Axis counting for the template-specialized carrier

The polynomial used here is formed from the memory-tree template fixed after the nonzero NPR
seed, before `alphaM`.  Its exponents are the template's natural timestamp exponents and its
coefficients are the template's committed axes.  In particular it is not formed by freezing an
`alphaM`-specialized execution.
-/

open scoped BigOperators Classical Polynomial

namespace Nock.NockVMROM.Thm54.TemplateAxisCounting

open Nock Nock.Walk
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open SemanticTimestampStrategy
open TemplateRawJointSoundness

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]

/-- The statically indexed memory root in the pre-`alphaM` execution template. -/
def templateMemoryTreeAt
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) :
    NTree (MemoryRowTemplate (K := K)) :=
  E.memoryForest.get (Fin.cast E.memory_root_count.symm i)

/-- The fixed axis tree read directly from a pre-`alphaM` memory template. -/
def templateAxisTree : NTree (MemoryRowTemplate (K := K)) → MTree K
  | .node row children =>
      match row.timestamp.state, children with
      | .halt, _ => .halt
      | .decompose, [l, r] => .decompose (templateAxisTree l) (templateAxisTree r)
      | .read_root, [c] => .read row.timestamp.recordExponent (templateAxisTree c)
      | .verify_child, [c] =>
          .verify row.timestamp.recordExponent row.placeholder.2.2.mem.axis
            (templateAxisTree c)
      | _, _ => .halt
termination_by t => sizeOf t
decreasing_by
  all_goals (simp only [wfParam] at *; simp_wf; omega)

/-- The same template tree with the exponent oracle used by the specialized exact carrier.
This auxiliary tree is allowed to depend on `α`; only its diagonal evaluation is used. -/
def recoveredAxisTree (α : K) : NTree (MemoryRowTemplate (K := K)) → MTree K
  | .node row children =>
      match row.timestamp.state, children with
      | .halt, _ => .halt
      | .decompose, [l, r] => .decompose (recoveredAxisTree α l) (recoveredAxisTree α r)
      | .read_root, [c] =>
          .read (timestampExp α (α ^ row.timestamp.recordExponent))
            (recoveredAxisTree α c)
      | .verify_child, [c] =>
          .verify (timestampExp α (α ^ row.timestamp.recordExponent))
            row.placeholder.2.2.mem.axis (recoveredAxisTree α c)
      | _, _ => .halt
termination_by t => sizeOf t
decreasing_by
  all_goals (simp only [wfParam] at *; simp_wf; omega)

/-- The univariate polynomial fixed before `alphaM`, one polynomial per memory root.

It is the 2-adic `countsP_bin` of the a-bearing template tree: the same polynomial
`ProductionP8Containment.RootAxisBoundaryAt` checks, so the priced guarded event and the
acceptance check are one polynomial.  The Form R `countsP` at defaults is kept as `templateAxisPolynomialFormR` for the
exec-level `AxisSoundness` route only. -/
def templateAxisPolynomial
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) : K[X] :=
  countsP_bin (templateAxisTree (templateMemoryTreeAt E i))

/-- Form R `countsP` (at defaults) of the template tree: the polynomial of the exec-level
`AxisSoundness.axisRootFailureAlphas` route (`specializedGuardedRootAlphas`, `seedAxisPairs`). -/
def templateAxisPolynomialFormR
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem) : K[X] :=
  countsP (templateAxisTree (templateMemoryTreeAt E i))

@[simp] theorem specialize_memory_state
    (row : MemoryRowTemplate (K := K)) (α : K) :
    (row.specializeA α).1 = row.timestamp.state :=
  rfl

theorem specialize_memory_ts_of_active
    (row : MemoryRowTemplate (K := K)) (α : K)
    (hactive : memoryMemRecKind row.timestamp.state = .active) :
    (row.specializeA α).2.2.mem.ts = α ^ row.timestamp.recordExponent := by
  simp [MemoryRowTemplate.specializeA, specializeMemRec, hactive]

theorem specialize_memory_axis_of_active
    (row : MemoryRowTemplate (K := K)) (α : K)
    (hactive : memoryMemRecKind row.timestamp.state = .active) :
    (row.specializeA α).2.2.mem.axis = row.placeholder.2.2.mem.axis := by
  simp [MemoryRowTemplate.specializeA, specializeMemRec, hactive]

/-- Simultaneous diagonal evaluation lemma for indicator and count polynomials.  It does not
assume exponent injectivity: `timestampExp_spec` is enough because both sides are evaluated at
the same `α`. -/
theorem recoveredAxisTree_eval (α : K)
    (t : NTree (MemoryRowTemplate (K := K))) :
    (indP (recoveredAxisTree α t)).eval α = (indP (templateAxisTree t)).eval α ∧
    (countsP (recoveredAxisTree α t)).eval α =
      (countsP (templateAxisTree t)).eval α := by
  let P := fun t : NTree (MemoryRowTemplate (K := K)) =>
    (indP (recoveredAxisTree α t)).eval α = (indP (templateAxisTree t)).eval α ∧
    (countsP (recoveredAxisTree α t)).eval α =
      (countsP (templateAxisTree t)).eval α
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P]
    cases hs : row.timestamp.state with
      | decompose =>
          rcases children with _ | ⟨l, rest⟩
          · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
          · rcases rest with _ | ⟨r, tail⟩
            · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
            · rcases tail with _ | ⟨x, xs⟩
              · have hl := ih l (by simp)
                have hr := ih r (by simp)
                simp only [P] at hl hr
                simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP,
                  hl.1, hl.2, hr.1, hr.2]
              · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
      | halt =>
          simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
      | read_root =>
          rcases children with _ | ⟨c, rest⟩
          · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
          · rcases rest with _ | ⟨x, xs⟩
            · have hc := ih c (by simp)
              simp only [P] at hc
              have hpow := timestampExp_spec (show TimestampClosedAt α
                (α ^ row.timestamp.recordExponent) from
                  ⟨row.timestamp.recordExponent, rfl⟩)
              simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP,
                hc.1, hc.2, ← hpow]
            · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
      | verify_child =>
          rcases children with _ | ⟨c, rest⟩
          · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
          · rcases rest with _ | ⟨x, xs⟩
            · have hc := ih c (by simp)
              simp only [P] at hc
              have hpow := timestampExp_spec (show TimestampClosedAt α
                (α ^ row.timestamp.recordExponent) from
                  ⟨row.timestamp.recordExponent, rfl⟩)
              simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP,
                hc.1, hc.2, ← hpow]
            · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- 2-adic twin of `recoveredAxisTree_eval`: diagonal evaluation of `indP_bin`/`countsP_bin`. -/
theorem recoveredAxisTree_eval_bin (α : K)
    (t : NTree (MemoryRowTemplate (K := K))) :
    (indP_bin (recoveredAxisTree α t)).eval α = (indP_bin (templateAxisTree t)).eval α ∧
    (countsP_bin (recoveredAxisTree α t)).eval α =
      (countsP_bin (templateAxisTree t)).eval α := by
  let P := fun t : NTree (MemoryRowTemplate (K := K)) =>
    (indP_bin (recoveredAxisTree α t)).eval α = (indP_bin (templateAxisTree t)).eval α ∧
    (countsP_bin (recoveredAxisTree α t)).eval α =
      (countsP_bin (templateAxisTree t)).eval α
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P]
    cases hs : row.timestamp.state with
      | decompose =>
          rcases children with _ | ⟨l, rest⟩
          · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
          · rcases rest with _ | ⟨r, tail⟩
            · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
            · rcases tail with _ | ⟨x, xs⟩
              · have hl := ih l (by simp)
                have hr := ih r (by simp)
                simp only [P] at hl hr
                simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin,
                  hl.1, hl.2, hr.1, hr.2]
              · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
      | halt =>
          simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
      | read_root =>
          rcases children with _ | ⟨c, rest⟩
          · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
          · rcases rest with _ | ⟨x, xs⟩
            · have hc := ih c (by simp)
              simp only [P] at hc
              have hpow := timestampExp_spec (show TimestampClosedAt α
                (α ^ row.timestamp.recordExponent) from
                  ⟨row.timestamp.recordExponent, rfl⟩)
              simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin,
                hc.1, hc.2, ← hpow]
            · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
      | verify_child =>
          rcases children with _ | ⟨c, rest⟩
          · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
          · rcases rest with _ | ⟨x, xs⟩
            · have hc := ih c (by simp)
              simp only [P] at hc
              have hpow := timestampExp_spec (show TimestampClosedAt α
                (α ^ row.timestamp.recordExponent) from
                  ⟨row.timestamp.recordExponent, rfl⟩)
              simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin,
                hc.1, hc.2, ← hpow]
            · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- Specializing a template and then reading it through `ofNTree` gives the recovered tree above. -/
theorem ofNTree_specialize_toMTree (α : K)
    (t : NTree (MemoryRowTemplate (K := K))) :
    (ofNTree (timestampExpAt α)
      (mapNTree (fun row => row.specializeA α) t)).toMTree =
        recoveredAxisTree α t := by
  let P := fun t : NTree (MemoryRowTemplate (K := K)) =>
    (ofNTree (timestampExpAt α)
      (mapNTree (fun row => row.specializeA α) t)).toMTree =
        recoveredAxisTree α t
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P]
    cases hs : row.timestamp.state with
      | decompose =>
          rcases children with _ | ⟨l, rest⟩
          · rw [mapNTree]
            simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
              timestampExpAt, specialize_memory_state, hs]
          · rcases rest with _ | ⟨r, tail⟩
            · rw [mapNTree]
              simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
                timestampExpAt, specialize_memory_state, hs]
            · rcases tail with _ | ⟨x, xs⟩
              · have hl := ih l (by simp)
                have hr := ih r (by simp)
                simp only [P] at hl hr
                rw [mapNTree]
                simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
                  timestampExpAt, specialize_memory_state, hs, hl, hr]
              · rw [mapNTree]
                simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
                  timestampExpAt, specialize_memory_state, hs]
      | halt =>
          rw [mapNTree]
          simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
            timestampExpAt, specialize_memory_state, hs]
      | read_root =>
          rcases children with _ | ⟨c, rest⟩
          · rw [mapNTree]
            simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
              timestampExpAt, specialize_memory_state, hs]
          · rcases rest with _ | ⟨x, xs⟩
            · have hc := ih c (by simp)
              simp only [P] at hc
              rw [mapNTree]
              have hactive : memoryMemRecKind row.timestamp.state = .active := by
                simp [hs, memoryMemRecKind]
              simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
                timestampExpAt, specialize_memory_state, hs,
                specialize_memory_ts_of_active row α hactive, hc]
            · rw [mapNTree]
              simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
                timestampExpAt, specialize_memory_state, hs]
      | verify_child =>
          rcases children with _ | ⟨c, rest⟩
          · rw [mapNTree]
            simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
              timestampExpAt, specialize_memory_state, hs]
          · rcases rest with _ | ⟨x, xs⟩
            · have hc := ih c (by simp)
              simp only [P] at hc
              rw [mapNTree]
              have hactive : memoryMemRecKind row.timestamp.state = .active := by
                simp [hs, memoryMemRecKind]
              simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
                timestampExpAt, specialize_memory_state, hs,
                specialize_memory_ts_of_active row α hactive,
                specialize_memory_axis_of_active row α hactive, hc]
            · rw [mapNTree]
              simp [ofNTree, MemWalk.toMTree, recoveredAxisTree,
                timestampExpAt, specialize_memory_state, hs]
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- Static root selection commutes with specialization. -/
theorem specialize_memoryTreeAt
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (α : K) {lmb : K} (i : Fin T.kMem) :
    (E.specialize α lmb).memoryTreeAt i =
      mapNTree (fun row => row.specialize α lmb) (templateMemoryTreeAt E i) := by
  simp [ExactExecution.memoryTreeAt, ExactExecutionTemplate.specialize,
    templateMemoryTreeAt]
  try rfl

/-- Static root selection commutes with the a-bearing specialization. -/
theorem specializeA_memoryTreeAt
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (α : K) {lmb : K} (i : Fin T.kMem) :
    (E.specializeA α lmb).memoryTreeAt i =
      mapNTree (fun row => row.specializeA α) (templateMemoryTreeAt E i) := by
  simp [ExactExecution.memoryTreeAt, ExactExecutionTemplate.specializeA,
    templateMemoryTreeAt]
  try rfl

/-- The specialized `countsP` root condition (on the a-bearing view `specializeA`; the executed
rows carry `(T, C')`) is exactly evaluation of the fixed template polynomial at `alphaM`. -/
theorem specialized_countsP_eval
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (α : K) {lmb : K} (i : Fin T.kMem) :
    (countsP (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)).eval α =
      (templateAxisPolynomialFormR E i).eval α := by
  simp only [exactAxisTree, ExactConfigTemplate.specialize_alpha]
  rw [specializeA_memoryTreeAt E α i, ofNTree_specialize_toMTree]
  exact (recoveredAxisTree_eval α (templateMemoryTreeAt E i)).2

/-- The specialized 2-adic `countsP_bin` root condition is evaluation of the template
polynomial at the sampled `alphaM`. -/
theorem specialized_countsP_bin_eval
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (α : K) {lmb : K} (i : Fin T.kMem) :
    (countsP_bin (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)).eval α =
      (countsP_bin (templateAxisTree (templateMemoryTreeAt E i))).eval α := by
  simp only [exactAxisTree, ExactConfigTemplate.specialize_alpha]
  rw [specializeA_memoryTreeAt E α i, ofNTree_specialize_toMTree]
  exact (recoveredAxisTree_eval_bin α (templateMemoryTreeAt E i)).2

/-! ## Polynomial exponent reindexing -/

/-- Additive reindexing of polynomial exponents.  Colliding target exponents are summed by
`Finsupp.mapDomain`; no injectivity assumption on `f` is made. -/
def reindexPolynomial (f : ℕ → ℕ) (P : K[X]) : K[X] :=
  ⟨P.toFinsupp.mapDomain f⟩

@[simp] theorem reindexPolynomial_zero (f : ℕ → ℕ) :
    reindexPolynomial (K := K) f 0 = 0 := by
  apply Polynomial.toFinsupp_injective
  simp only [reindexPolynomial, Polynomial.toFinsupp_zero]
  exact AddMonoidAlgebra.mapDomain_zero f

theorem reindexPolynomial_add (f : ℕ → ℕ) (P Q : K[X]) :
    reindexPolynomial f (P + Q) =
      reindexPolynomial f P + reindexPolynomial f Q := by
  apply Polynomial.toFinsupp_injective
  simp only [reindexPolynomial, Polynomial.toFinsupp_add]
  exact AddMonoidAlgebra.mapDomain_add f _ _

theorem reindexPolynomial_sub (f : ℕ → ℕ) (P Q : K[X]) :
    reindexPolynomial f (P - Q) =
      reindexPolynomial f P - reindexPolynomial f Q := by
  apply Polynomial.toFinsupp_injective
  simp only [reindexPolynomial, Polynomial.toFinsupp_sub]
  refine eq_sub_of_add_eq ?_
  rw [← AddMonoidAlgebra.mapDomain_add, sub_add_cancel]

theorem reindexPolynomial_C_mul (f : ℕ → ℕ) (a : K) (P : K[X]) :
    reindexPolynomial f (Polynomial.C a * P) =
      Polynomial.C a * reindexPolynomial f P := by
  rw [← Polynomial.smul_eq_C_mul, ← Polynomial.smul_eq_C_mul]
  apply Polynomial.toFinsupp_injective
  simp only [reindexPolynomial, Polynomial.toFinsupp_smul]
  ext n
  simp [AddMonoidAlgebra.mapDomain, Finsupp.mapDomain_smul]

theorem reindexPolynomial_X_pow (f : ℕ → ℕ) (e : ℕ) :
    reindexPolynomial (K := K) f (Polynomial.X ^ e) = Polynomial.X ^ f e := by
  apply Polynomial.toFinsupp_injective
  simp [reindexPolynomial, Polynomial.X_pow_eq_monomial, Finsupp.mapDomain_single]

/-- The exponent selected by the specialized carrier for a template timestamp exponent. -/
def recoveredExponent (α : K) (e : ℕ) : ℕ :=
  timestampExp α (α ^ e)

/-- Recovered indicator/count polynomials are exactly additive exponent reindexings of the fixed
template polynomials. -/
theorem recoveredAxisTree_reindex (α : K)
    (t : NTree (MemoryRowTemplate (K := K))) :
    reindexPolynomial (recoveredExponent α) (indP (templateAxisTree t)) =
        indP (recoveredAxisTree α t) ∧
      reindexPolynomial (recoveredExponent α) (countsP (templateAxisTree t)) =
        countsP (recoveredAxisTree α t) := by
  let P := fun t : NTree (MemoryRowTemplate (K := K)) =>
    reindexPolynomial (recoveredExponent α) (indP (templateAxisTree t)) =
        indP (recoveredAxisTree α t) ∧
      reindexPolynomial (recoveredExponent α) (countsP (templateAxisTree t)) =
        countsP (recoveredAxisTree α t)
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P]
    cases hs : row.timestamp.state with
    | decompose =>
        rcases children with _ | ⟨l, rest⟩
        · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
        · rcases rest with _ | ⟨r, tail⟩
          · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
          · rcases tail with _ | ⟨x, xs⟩
            · have hl := ih l (by simp)
              have hr := ih r (by simp)
              simp only [P] at hl hr
              simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP,
                reindexPolynomial_add, reindexPolynomial_sub,
                reindexPolynomial_C_mul, hl.1, hl.2, hr.1, hr.2]
            · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
    | halt =>
        simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
    | read_root =>
        rcases children with _ | ⟨c, rest⟩
        · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP,
              recoveredExponent, reindexPolynomial_sub, reindexPolynomial_C_mul,
              reindexPolynomial_X_pow, pwScale, hc.1, hc.2]
          · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
    | verify_child =>
        rcases children with _ | ⟨c, rest⟩
        · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP,
              recoveredExponent, reindexPolynomial_add, reindexPolynomial_C_mul,
              reindexPolynomial_X_pow, hc.1, hc.2]
          · simp [templateAxisTree, recoveredAxisTree, hs, indP, countsP]
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- Zero template count polynomials remain zero after every specialization-time exponent
recovery, even when powers collide. -/
theorem recovered_countsP_eq_zero_of_template_eq_zero
    (α : K) (t : NTree (MemoryRowTemplate (K := K)))
    (hzero : countsP (templateAxisTree t) = 0) :
    countsP (recoveredAxisTree α t) = 0 := by
  rw [← (recoveredAxisTree_reindex α t).2, hzero, reindexPolynomial_zero]

/-- 2-adic twin of `recoveredAxisTree_reindex`. -/
theorem recoveredAxisTree_reindex_bin (α : K)
    (t : NTree (MemoryRowTemplate (K := K))) :
    reindexPolynomial (recoveredExponent α) (indP_bin (templateAxisTree t)) =
        indP_bin (recoveredAxisTree α t) ∧
      reindexPolynomial (recoveredExponent α) (countsP_bin (templateAxisTree t)) =
        countsP_bin (recoveredAxisTree α t) := by
  let P := fun t : NTree (MemoryRowTemplate (K := K)) =>
    reindexPolynomial (recoveredExponent α) (indP_bin (templateAxisTree t)) =
        indP_bin (recoveredAxisTree α t) ∧
      reindexPolynomial (recoveredExponent α) (countsP_bin (templateAxisTree t)) =
        countsP_bin (recoveredAxisTree α t)
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro row children ih
    simp only [P]
    cases hs : row.timestamp.state with
    | decompose =>
        rcases children with _ | ⟨l, rest⟩
        · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
        · rcases rest with _ | ⟨r, tail⟩
          · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
          · rcases tail with _ | ⟨x, xs⟩
            · have hl := ih l (by simp)
              have hr := ih r (by simp)
              simp only [P] at hl hr
              simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin,
                reindexPolynomial_add, reindexPolynomial_sub,
                reindexPolynomial_C_mul, hl.1, hl.2, hr.1, hr.2]
            · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
    | halt =>
        simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
    | read_root =>
        rcases children with _ | ⟨c, rest⟩
        · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin,
              recoveredExponent, reindexPolynomial_sub,
              reindexPolynomial_X_pow, hc.1, hc.2]
          · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
    | verify_child =>
        rcases children with _ | ⟨c, rest⟩
        · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
        · rcases rest with _ | ⟨x, xs⟩
          · have hc := ih c (by simp)
            simp only [P] at hc
            simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin,
              recoveredExponent, reindexPolynomial_add, reindexPolynomial_C_mul,
              reindexPolynomial_X_pow, hc.1, hc.2]
          · simp [templateAxisTree, recoveredAxisTree, hs, indP_bin, countsP_bin]
  · intro c hc
    simp at hc
  · intro head tail ihHead ihTail c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- The a-bearing specialized 2-adic polynomials are exponent reindexings of the fixed template
ones (`specializeA` keeps the template's `a`; the identity of `ofNTree_specialize_toMTree`). -/
theorem specializeA_axis_bin_eq_reindex
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (α : K) {lmb : K} (i : Fin T.kMem) :
    indP_bin (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) =
        reindexPolynomial (recoveredExponent α)
          (indP_bin (templateAxisTree (templateMemoryTreeAt E i))) ∧
      countsP_bin (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) =
        reindexPolynomial (recoveredExponent α) (templateAxisPolynomial E i) := by
  have ht : exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i =
      recoveredAxisTree α (templateMemoryTreeAt E i) := by
    simp only [exactAxisTree, ExactConfigTemplate.specialize_alpha]
    rw [specializeA_memoryTreeAt E α i, ofNTree_specialize_toMTree]
  rw [ht]
  exact ⟨(recoveredAxisTree_reindex_bin α _).1.symm, (recoveredAxisTree_reindex_bin α _).2.symm⟩

/-- 2-adic twin of `recovered_countsP_eq_zero_of_template_eq_zero`. -/
theorem recovered_countsP_bin_eq_zero_of_template_eq_zero
    (α : K) (t : NTree (MemoryRowTemplate (K := K)))
    (hzero : countsP_bin (templateAxisTree t) = 0) :
    countsP_bin (recoveredAxisTree α t) = 0 := by
  rw [← (recoveredAxisTree_reindex_bin α t).2, hzero, reindexPolynomial_zero]

omit [Fintype K] [DecidableEq K] in
/-- Both 2-adic axis polynomials of an `MTree` have degree at most any bound on its timestamp
exponents (twin of `TraceGen.natDegree_indP_countsP_le`; generic in `K`). -/
theorem natDegree_indP_bin_countsP_bin_le (B : ℕ) :
    ∀ t : MTree K,
      (∀ e ∈ readExps t, e ≤ B) → (∀ e ∈ verifyExps t, e ≤ B) →
        (indP_bin t).natDegree ≤ B ∧ (countsP_bin t).natDegree ≤ B := by
  intro t
  induction t with
  | halt =>
      intro _ _
      simp [indP_bin, countsP_bin]
  | decompose l r ihl ihr =>
      intro hread hverify
      obtain ⟨hil, hcl⟩ := ihl (fun e he => hread e (by simp [readExps, he]))
        (fun e he => hverify e (by simp [verifyExps, he]))
      obtain ⟨hir, hcr⟩ := ihr (fun e he => hread e (by simp [readExps, he]))
        (fun e he => hverify e (by simp [verifyExps, he]))
      refine ⟨?_, ?_⟩
      · exact (Polynomial.natDegree_add_le _ _).trans (max_le hil hir)
      · change (Polynomial.C ((2 : K)⁻¹) *
            (countsP_bin l + countsP_bin r - indP_bin r)).natDegree ≤ B
        refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ hir)
        exact (Polynomial.natDegree_add_le _ _).trans (max_le hcl hcr)
  | read e c ih =>
      intro hread hverify
      have he : e ≤ B := hread e (by simp [readExps])
      obtain ⟨hic, hcc⟩ := ih (fun e' he' => hread e' (by simp [readExps, he']))
        (fun e' he' => hverify e' (by simpa [verifyExps] using he'))
      have hxp : (Polynomial.X ^ e : Polynomial K).natDegree ≤ B := by
        rw [Polynomial.natDegree_X_pow]; exact he
      exact ⟨(Polynomial.natDegree_sub_le _ _).trans (max_le hic hxp),
        (Polynomial.natDegree_sub_le _ _).trans (max_le hcc hxp)⟩
  | verify e a c ih =>
      intro hread hverify
      have he : e ≤ B := hverify e (by simp [verifyExps])
      obtain ⟨hic, hcc⟩ := ih (fun e' he' => hread e' (by simpa [readExps] using he'))
        (fun e' he' => hverify e' (by simp [verifyExps, he']))
      have hxp : (Polynomial.X ^ e : Polynomial K).natDegree ≤ B := by
        rw [Polynomial.natDegree_X_pow]; exact he
      have hcxp : (Polynomial.C a * Polynomial.X ^ e : Polynomial K).natDegree ≤ B :=
        (Polynomial.natDegree_C_mul_le _ _).trans hxp
      exact ⟨(Polynomial.natDegree_add_le _ _).trans (max_le hic hxp),
        (Polynomial.natDegree_add_le _ _).trans (max_le hcc hcxp)⟩


/-- The α-free aggregate `intermediate` **request** exponent multiset of the committed template
forest.  This is the seed-time shadow of `forestReadTimestamps`; the paper's `intermediate` is one
variable global to the whole traversal over a forest that already contains every
mutated `OP2`/`OP7`/`OP8`/`OP9` subject. -/
def templateForestReadExps
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : List ℕ :=
  (List.finRange T.kMem).flatMap fun i =>
    readExps (templateAxisTree (templateMemoryTreeAt E i))


/-- The α-free aggregate `intermediate` **response** exponent multiset of the committed template
forest. -/
def templateForestVerifyExps
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : List ℕ :=
  (List.finRange T.kMem).flatMap fun i =>
    verifyExps (templateAxisTree (templateMemoryTreeAt E i))

/-- Degree workload fixed with the execution template (2-adic `countsP_bin` degrees: the
polynomial `RootAxisBoundaryAt` checks). -/
def templateAxisWorkload
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : ℕ :=
  ∑ i : Fin T.kMem, (templateAxisPolynomial E i).natDegree

/-- Form R degree workload of the exec-level `AxisSoundness` route. -/
def templateAxisWorkloadFormR
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : ℕ :=
  ∑ i : Fin T.kMem, (templateAxisPolynomialFormR E i).natDegree

/-- The exact axis-soundness witness which makes one root polynomial countable. -/
def TemplateAxisBadWitness (t : MTree K) : Prop :=
  ∃ e : ℕ, Nested e t ∧ readCount e t = 1 ∧ verifyCount e t = 1 ∧
    vaxis e t ≠ Relaxis e t

/-- A Relaxis mismatch on the 2-adic substrate forces `countsP_bin ≠ 0`.
    Form R `countsP` is the live event polynomial (`axisRootFailureAlphas`). -/
theorem templateAxisPolynomial_ne_zero_of_bad
    (h2 : (2 : K) ≠ 0) (t : MTree K) (W : TemplateAxisBadWitness t) :
    countsP_bin t ≠ 0 := by
  obtain ⟨e, hn, hr, hv, hwrong⟩ := W
  intro hzero
  exact hwrong (axis_batching_sound h2 t hzero e hn hr hv)

/-- Structural axis data needed for counting.  In contrast to `ExactAxisRefinement`, this has no
`root_accepts` field and therefore imposes no boundary equation at rejected challenges.

The current connector leaves exactly three honest residuals: ancestry, per-root read-timestamp
nodup, and the one global `intermediate` matching.  `timestamp_closed` is omitted because the
counting proof uses the template specialization equation directly and never consumes it. -/
structure ExactAxisStructuralRefinement
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop where
  ancestry : ExactMemoryAncestry cfg exec
  read_timestamps_nodup :
    ∀ i, ((readExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Nodup

  /-- The `L_mIO` matching of the one `intermediate` accumulator, applied **once** to the aggregate
  request/response multiset of the whole memory forest.  the paper stores `intermediate`
  "externally to the node labels … a variable `global' to the traversal", constrains it exactly as
  `RAP_mem-IO`/`RAP_comp-IO` do (so its content is the `Thm:IO_result` matching), and checks its
  initial and final values against zero *globally*; `App:Memconstraints` writes that accumulator as
  one row recurrence over the whole memory table.  Since the paper feeds
  every mutated `OP2`/`OP7`/`OP8`/`OP9` subject into the same forest, a seeded atom subject is a
  legitimately record-free root whose `axis_counts`/`axis_indicator` are zero
; the `[K]` index range therefore
  belongs to the aggregate multiset, not to each root. -/
  intermediate_matching :
    IO.LmIO cfg.Ksz (forestReadTimestamps cfg exec) (forestVerifyTimestamps cfg exec)

namespace ExactAxisStructuralRefinement

theorem readExps_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisStructuralRefinement cfg exec) (i : Fin cfg.kMem) :
    (readExps (exactAxisTree cfg exec i)).Nodup :=
  Nock.AxisBridge.readExps_nodup_of_ts cfg.challenges.α _
    (R.read_timestamps_nodup i)


/-- Unique response of the one global matching: `L_mIO`'s `unique_requests` conjunct makes the
aggregate `intermediate` response multiset repeat-free across the whole forest. -/
theorem forestVerifyTimestamps_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisStructuralRefinement cfg exec) :
    (forestVerifyTimestamps cfg exec).Nodup :=
  ((IO.LmIO_iff _ _ _).1 R.intermediate_matching).2.2.1

/-- Per-root verify-timestamp uniqueness is a *localization* of the one global condition, via
`readTimestamps_sublist_forest`/`verifyTimestamps_sublist_forest`.  Nothing per-root is assumed. -/
theorem verifyTimestamps_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisStructuralRefinement cfg exec) (i : Fin cfg.kMem) :
    ((verifyExps (exactAxisTree cfg exec i)).map
      (fun e => cfg.challenges.α ^ e)).Nodup :=
  (verifyTimestamps_sublist_forest cfg exec i).nodup R.forestVerifyTimestamps_nodup


/-- The paper's global terminal check, in the shape `Thm:IO_result` gives it.  Once the aggregate
request multiset is itself repeat-free — the global `z^i` uniqueness of the paper — the
one `intermediate` accumulator closes exactly: every timestamp added at a `read_root` row of the
forest is removed at a `verify_child` row of the forest and conversely, so its final value is zero
whenever its initial value is. -/
theorem intermediate_closes
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisStructuralRefinement cfg exec)
    (hglobal : (forestReadTimestamps cfg exec).Nodup) :
    (forestReadTimestamps cfg exec).Perm (forestVerifyTimestamps cfg exec) :=
  (IO.cor_uni_req_uni_resp cfg.Ksz _ _ hglobal R.intermediate_matching).2.2

theorem verifyExps_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisStructuralRefinement cfg exec) (i : Fin cfg.kMem) :
    (verifyExps (exactAxisTree cfg exec i)).Nodup :=
  Nock.AxisBridge.verifyExps_nodup_of_ts cfg.challenges.α _
    (R.verifyTimestamps_nodup i)

/-- Existing honest reconstruction discharges ancestry.  The only remaining structural inputs
are per-root read-timestamp nodup and intermediate LIO matching. -/
def ofHonestReconstruction
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {subjects : Fin cfg.kMem → Noun}
    (hhonest : ExactMemoryHonestReconstruction cfg exec subjects)
    (hread :
      ∀ i, ((readExps (exactAxisTree cfg exec i)).map
        (fun e => cfg.challenges.α ^ e)).Nodup)
    (hmatch :
      IO.LmIO cfg.Ksz (forestReadTimestamps cfg exec)
        (forestVerifyTimestamps cfg exec)) :
    ExactAxisStructuralRefinement cfg exec where
  ancestry := exactMemoryAncestry_of_honestReconstruction hhonest
  read_timestamps_nodup := hread
  intermediate_matching := hmatch

end ExactAxisStructuralRefinement

/-- Compatibility adapter.  Production counting consumes only the structural result. -/
def ExactAxisRefinement.toStructural
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (R : ExactAxisRefinement cfg exec) :
    ExactAxisStructuralRefinement cfg exec where
  ancestry := R.ancestry
  read_timestamps_nodup := R.read_timestamps_nodup
  intermediate_matching := R.intermediate_matching

/-- Turn the weak discrepancy stored by `axisRootFailureAlphas` into the complete specialized
axis-soundness witness supplied by structural refinement, then identify the recovered tree. -/
theorem recovered_badWitness_of_specialized_bad
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (α : K) {lmb : K}
    (R : ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb))
    (i : Fin T.kMem)
    (hbad : ∃ e : ℕ,
      e ∈ readExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ∧
      e ∈ verifyExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ∧
      vaxis e (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ≠
        Relaxis e (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)) :
    TemplateAxisBadWitness
      (recoveredAxisTree α (templateMemoryTreeAt E i)) := by
  obtain ⟨e, hre, hve, hwrong⟩ := hbad
  let t := exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i
  have hread : (readExps t).Nodup := R.readExps_nodup i
  have hverify : (verifyExps t).Nodup := R.verifyExps_nodup i
  have hru : ∀ q, readCount q t ≤ 1 :=
    fun q => Nock.AxisBridge.readCount_le_one q t hread
  have hvu : ∀ q, verifyCount q t ≤ 1 :=
    fun q => Nock.AxisBridge.verifyCount_le_one q t hverify
  have hn : Nested e t :=
    Nock.AxisBridge.nested_of_readVerifyNested t (R.ancestry i) e hru hvu
  have hr : readCount e t = 1 :=
    Nock.AxisBridge.readCount_eq_one_of_mem e t hread hre
  have hv : verifyCount e t = 1 :=
    Nock.AxisBridge.verifyCount_eq_one_of_mem e t hverify hve
  have ht :
      t = recoveredAxisTree α (templateMemoryTreeAt E i) := by
    simp only [t, exactAxisTree, ExactConfigTemplate.specialize_alpha]
    rw [specializeA_memoryTreeAt E α i, ofNTree_specialize_toMTree]
  rw [← ht]
  exact ⟨e, hn, hr, hv, hwrong⟩

/-- The reindex theorem makes the bridge's nonzeroness direction explicit: a complete bad
recovered witness rules out an identically-zero 2-adic count polynomial. -/
theorem templateAxisPolynomial_ne_zero_of_recovered_bad
    (h2 : (2 : K) ≠ 0) (α : K)
    (t : NTree (MemoryRowTemplate (K := K)))
    (W : TemplateAxisBadWitness (recoveredAxisTree α t)) :
    countsP_bin (recoveredAxisTree α t) ≠ 0 := by
  obtain ⟨e, hn, hr, hv, hwrong⟩ := W
  intro hzero
  exact hwrong (axis_batching_sound h2 _ hzero e hn hr hv)

/-- Template-level nonzeroness: a complete bad witness on the recovered (a-bearing specialized)
tree forces the fixed template polynomial `templateAxisPolynomial = countsP_bin` to be nonzero,
through the 2-adic reindex (exponent collisions only sum coefficients). -/
theorem templateAxisPolynomial_ne_zero_of_specialized_bad
    (h2 : (2 : K) ≠ 0)
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (α : K) {lmb : K}
    (R : ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb))
    (i : Fin T.kMem)
    (hbad : ∃ e : ℕ,
      e ∈ readExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ∧
      e ∈ verifyExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ∧
      vaxis e (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ≠
        Relaxis e (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)) :
    templateAxisPolynomial E i ≠ 0 := by
  intro hzero
  exact templateAxisPolynomial_ne_zero_of_recovered_bad h2 α (templateMemoryTreeAt E i)
    (recovered_badWitness_of_specialized_bad E α R i hbad)
    (recovered_countsP_bin_eq_zero_of_template_eq_zero α _ hzero)

/-- Actual guarded event for one fixed seed-time template root.  The witness is stated on the
specialized exact tree; only the root equation is transported to the one fixed template
polynomial. -/
def specializedGuardedRootAlphas
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (lmb : K)
    (i : Fin T.kMem) : Finset K :=
  Finset.univ.filter fun α =>
    (∃ e : ℕ,
      e ∈ readExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ∧
      e ∈ verifyExps (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ∧
      vaxis e (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i) ≠
        Relaxis e (exactAxisTree (T.specialize α lmb) (E.specializeA α lmb) i)) ∧
    templateAxisPolynomialFormR E i ≠ 0 ∧
    (templateAxisPolynomialFormR E i).eval α = 0

def specializedGuardedRootUnion
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (lmb : K) : Finset K :=
  (Finset.univ : Finset (Fin T.kMem)).biUnion (specializedGuardedRootAlphas E lmb)

theorem specializedGuardedRootAlphas_card_le
    (h2 : (2 : K) ≠ 0)
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (lmb : K)
    (hrefine :
      ∀ α : K, ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb))
    (i : Fin T.kMem) :
    (specializedGuardedRootAlphas E lmb i).card ≤
      (templateAxisPolynomialFormR E i).natDegree := by
  by_cases hempty : specializedGuardedRootAlphas E lmb i = ∅
  · simp [hempty]
  · have hnonempty : (specializedGuardedRootAlphas E lmb i).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨α₀, hα₀⟩ := hnonempty
    have hα₀' := (Finset.mem_filter.mp hα₀).2
    have hne : templateAxisPolynomialFormR E i ≠ 0 := hα₀'.2.1
    have hsubset :
        specializedGuardedRootAlphas E lmb i ⊆
          Finset.univ.filter fun α : K => (templateAxisPolynomialFormR E i).IsRoot α := by
      intro α hα
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ α, (Finset.mem_filter.mp hα).2.2.2⟩
    exact (Finset.card_le_card hsubset).trans (Nock.Walk.card_roots_le _ hne)

theorem specializedGuardedRootUnion_card_le
    (h2 : (2 : K) ≠ 0)
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (lmb : K)
    (hrefine :
      ∀ α : K, ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb)) :
    (specializedGuardedRootUnion E lmb).card ≤ templateAxisWorkloadFormR E := by
  calc
    (specializedGuardedRootUnion E lmb).card
        ≤ ∑ i : Fin T.kMem, (specializedGuardedRootAlphas E lmb i).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ i : Fin T.kMem, (templateAxisPolynomialFormR E i).natDegree :=
      Finset.sum_le_sum fun i _ =>
        specializedGuardedRootAlphas_card_le h2 E lmb hrefine i
    _ = templateAxisWorkloadFormR E := rfl

/-- Bad sampled `alphaM` values at one fixed nonzero NPR seed. -/
def seedSpecializedAxisAlphas
    (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K) (z : K) (hz : z ≠ 0) :
    Finset K :=
  Finset.univ.filter fun α =>
    α ∈ axisBadAlphas
      (specializedProblem T.timestamp z hz α lmb).cfg
      (specializedExecA T.timestamp z hz α lmb)

theorem seedSpecializedAxisAlphas_subset_templateRoots
    (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K) (z : K) (hz : z ≠ 0) :
    seedSpecializedAxisAlphas T lmb z hz ⊆
      specializedGuardedRootUnion
        (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate lmb := by
  intro α hα
  simp only [seedSpecializedAxisAlphas, Finset.mem_filter, Finset.mem_univ,
    true_and] at hα
  rw [mem_axisBadAlphas_iff] at hα
  obtain ⟨i, hi⟩ := hα
  have hi' := (mem_axisRootFailureAlphas_iff _ _ i α).1 hi
  simp only [specializedGuardedRootUnion, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  refine ⟨i, ?_⟩
  simp only [specializedGuardedRootAlphas, Finset.mem_filter, Finset.mem_univ,
    true_and]
  refine ⟨?_, ?_, ?_⟩
  · simpa [specializedProblem, specializedExecA] using hi'.1
  · intro h0
    have hrec := recovered_countsP_eq_zero_of_template_eq_zero α
      (templateMemoryTreeAt (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate i) h0
    apply hi'.2.1
    convert hrec using 1
    simp only [exactAxisTree, specializedProblem, specializedExecA,
      ExactConfigTemplate.specialize_alpha]
    erw [specializeA_memoryTreeAt, ofNTree_specialize_toMTree]
  · rw [← specialized_countsP_eval
      (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate α (lmb := lmb) i]
    simpa [specializedProblem, specializedExecA] using hi'.2.2

theorem seedSpecializedAxisAlphas_card_le
    (h2 : (2 : K) ≠ 0)
    (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K) (z : K) (hz : z ≠ 0)
    (hrefine :
      ∀ α : K, ExactAxisStructuralRefinement
        (specializedProblem T.timestamp z hz α lmb).cfg
        (specializedExecA T.timestamp z hz α lmb)) :
    (seedSpecializedAxisAlphas T lmb z hz).card ≤
      templateAxisWorkloadFormR
        (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate :=
  (Finset.card_le_card
      (seedSpecializedAxisAlphas_subset_templateRoots T lmb z hz)).trans
    (specializedGuardedRootUnion_card_le h2 _ lmb
      (fun α => by simpa [specializedProblem, specializedExecA] using hrefine α))

/-- Embed one `alphaM` fiber at a fixed NPR seed. -/
def seedAlphaEmbedding (z : K) : K ↪ (K × K) where
  toFun α := (α, z)
  inj' := by
    intro α β h
    exact congrArg Prod.fst h

/-- Union of all nonzero-seed `(alphaM,z)` bad fibers. -/
def seedAxisPairs (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K) : Finset (K × K) :=
  (Finset.univ : Finset K).biUnion fun z =>
    if hz : z ≠ 0 then
      (seedSpecializedAxisAlphas T lmb z hz).map (seedAlphaEmbedding z)
    else ∅

@[simp] theorem mem_seedAxisPairs_iff
    (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K) (a z : K) :
    (a, z) ∈ seedAxisPairs T lmb ↔
      ∃ hz : z ≠ 0, a ∈ seedSpecializedAxisAlphas T lmb z hz := by
  simp only [seedAxisPairs, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z', h⟩
    split at h
    · rename_i hz'
      simp only [Finset.mem_map] at h
      obtain ⟨a', ha', hp⟩ := h
      have hzEq : z' = z := congrArg Prod.snd hp
      subst z'
      have haEq : a' = a := congrArg Prod.fst hp
      subst a'
      exact ⟨hz', ha'⟩
    · simp at h
  · rintro ⟨hz, ha⟩
    refine ⟨z, ?_⟩
    simp [hz, seedAlphaEmbedding]
    exact ⟨a, ha, rfl⟩

theorem seedAxisPairs_card_le
    (h2 : (2 : K) ≠ 0)
    (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K) (workload : ℕ)
    (hrefine :
      ∀ (z : K) (hz : z ≠ 0) (α : K),
        ExactAxisStructuralRefinement
          (specializedProblem T.timestamp z hz α lmb).cfg
          (specializedExecA T.timestamp z hz α lmb))
    (hwork :
      ∀ (z : K) (hz : z ≠ 0),
        templateAxisWorkloadFormR
          (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate ≤ workload) :
    (seedAxisPairs T lmb).card ≤ workload * Fintype.card K := by
  calc
    (seedAxisPairs T lmb).card
        ≤ ∑ z : K,
            (if hz : z ≠ 0 then
              (seedSpecializedAxisAlphas T lmb z hz).map (seedAlphaEmbedding z)
            else ∅).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _z : K, workload := by
      apply Finset.sum_le_sum
      intro z _
      split
      · rename_i hz
        simpa using
          (seedSpecializedAxisAlphas_card_le h2 T lmb z hz
            (hrefine z hz)).trans
            (hwork z hz)
      · simp
    _ = workload * Fintype.card K := by
      simp [Nat.mul_comm]

/-- The exact specialized event is a product with the two unrestricted later coordinates
`(alphaC,gamma)`. -/
theorem specializedAxisFailureEvent_eq_product
    (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K) :
    specializedAxisFailureEvent T lmb =
      (Finset.univ : Finset (K × K)) ×ˢ seedAxisPairs T lmb := by
  ext ω
  rcases ω with ⟨cg, ⟨a, z⟩⟩
  rw [mem_specializedAxisFailureEvent_iff]
  simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_seedAxisPairs_iff]
  constructor
  · rintro ⟨hz, hbad⟩
    change z ≠ 0 at hz
    change a ∈ axisBadAlphas
      (specializedProblem T.timestamp z hz a lmb).cfg
      (specializedExecA T.timestamp z hz a lmb) at hbad
    refine ⟨hz, ?_⟩
    exact (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hbad⟩)
  · rintro ⟨hz, hbad⟩
    change z ≠ 0 at hz
    change a ∈ seedSpecializedAxisAlphas T lmb z hz at hbad
    refine ⟨hz, ?_⟩
    change a ∈ axisBadAlphas
      (specializedProblem T.timestamp z hz a lmb).cfg
      (specializedExecA T.timestamp z hz a lmb)
    exact (Finset.mem_filter.mp hbad).2

/-- Uniform template-polynomial counting closes the exact specialized axis residual.  The proof
is a cardinality argument in the common joint space and uses no independence premise. -/
theorem specializedAxisFailureEvent_card_le
    (h2 : (2 : K) ≠ 0)
    (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K) (workload : ℕ)
    (hrefine :
      ∀ (z : K) (hz : z ≠ 0) (α : K),
        ExactAxisStructuralRefinement
          (specializedProblem T.timestamp z hz α lmb).cfg
          (specializedExecA T.timestamp z hz α lmb))
    (hwork :
      ∀ (z : K) (hz : z ≠ 0),
        templateAxisWorkloadFormR
          (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate ≤ workload) :
    (specializedAxisFailureEvent T lmb).card ≤
      workload * Fintype.card K ^ 3 := by
  rw [specializedAxisFailureEvent_eq_product]
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_prod]
  have hpairs := seedAxisPairs_card_le h2 T lmb workload hrefine hwork
  calc
    Fintype.card K * Fintype.card K * (seedAxisPairs T lmb).card
        ≤ Fintype.card K * Fintype.card K *
            (workload * Fintype.card K) :=
      Nat.mul_le_mul_left _ hpairs
    _ = workload * Fintype.card K ^ 3 := by ring

/-- Requested instantiation of
`TemplateRawJointSoundness.SpecializedAxisCountingResidual`. -/
theorem specializedAxisCountingResidual
    (h2 : (2 : K) ≠ 0)
    (T : TemplateRawJointSoundness.Strategy F K p) (lmb : K) (workload : ℕ)
    (hrefine :
      ∀ (z : K) (hz : z ≠ 0) (α : K),
        ExactAxisStructuralRefinement
          (specializedProblem T.timestamp z hz α lmb).cfg
          (specializedExecA T.timestamp z hz α lmb))
    (hwork :
      ∀ (z : K) (hz : z ≠ 0),
        templateAxisWorkloadFormR
          (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate ≤ workload) :
    SpecializedAxisCountingResidual T lmb workload :=
  specializedAxisFailureEvent_card_le h2 T lmb workload hrefine hwork



/-- Honest one-step read/verify tree: committed axis `1` is the true relative axis. -/
def honestReadVerifyAxisTree (e : ℕ) : MTree K :=
  .read e (.verify e 1 .halt)

/-- Honest roots may, and in this basic case do, have an identically-zero count polynomial. -/
@[simp] theorem honestReadVerifyAxisTree_countsP (e : ℕ) :
    countsP (honestReadVerifyAxisTree (K := K) e) = 0 := by
  simp [honestReadVerifyAxisTree, countsP]

/-- Completeness regression: the honest zero polynomial carries no guarded bad witness, so it
contributes no root event. -/
theorem honestReadVerifyAxisTree_no_bad
    (h2 : (2 : K) ≠ 0) (e : ℕ) :
    ¬ TemplateAxisBadWitness (honestReadVerifyAxisTree (K := K) e) := by
  intro W
  obtain ⟨e', hn, hr, hv, hwrong⟩ := W
  exact hwrong (axis_batching_sound h2 _ (by simp [honestReadVerifyAxisTree, countsP_bin])
    e' hn hr hv)

/-- At `α = 1`, all template exponents collide under the recovered timestamp oracle. -/
theorem recoveredExponent_one_collision (e₁ e₂ : ℕ) :
    recoveredExponent (1 : K) e₁ = recoveredExponent (1 : K) e₂ := by
  simp [recoveredExponent]

/-- Collision regression: even at the maximally colliding challenge `α = 1`, an identically-zero
template polynomial stays zero on the recovered tree. -/
theorem exponentCollision_preserves_zero
    (t : NTree (MemoryRowTemplate (K := K)))
    (hzero : countsP (templateAxisTree t) = 0) :
    countsP (recoveredAxisTree 1 t) = 0 :=
  recovered_countsP_eq_zero_of_template_eq_zero 1 t hzero

/-- A toy acceptance schedule which accepts only one challenge. -/
def acceptsOnlyAt (chosen α : K) : Prop :=
  α = chosen

/-- Rejection regression: counting is applicable with a structural refinement even when every
challenge except one is rejected.  No root-boundary premise is supplied. -/
theorem sparseAcceptance_counting_regression
    (h2 : (2 : K) ≠ 0)
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (chosen lmb : K)
    (hrefine :
      ∀ α : K, ExactAxisStructuralRefinement (T.specialize α lmb) (E.specializeA α lmb))
    (i : Fin T.kMem) :
    (∀ α : K, α ≠ chosen → ¬ acceptsOnlyAt chosen α) ∧
      (specializedGuardedRootAlphas E lmb i).card ≤
        (templateAxisPolynomialFormR E i).natDegree := by
  refine ⟨?_, specializedGuardedRootAlphas_card_le h2 E lmb hrefine i⟩
  intro α hne haccept
  exact hne haccept

/-- The guarded counting route is deliberately unavailable in characteristic two. -/
theorem characteristicTwo_rejects_axisCounting
    {L : Type} [Field L] [CharP L 2] :
    ¬ (2 : L) ≠ 0 := by
  intro h2
  exact h2 (CharP.cast_eq_zero L 2)

end

end Nock.NockVMROM.Thm54.TemplateAxisCounting

#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.recoveredAxisTree_eval
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.recoveredAxisTree_eval_bin
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.specialized_countsP_eval
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.specialized_countsP_bin_eval
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.recoveredAxisTree_reindex
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.recovered_countsP_eq_zero_of_template_eq_zero
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.templateAxisPolynomial_ne_zero_of_bad
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisRefinement.toStructural
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement.ofHonestReconstruction
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.specializedGuardedRootUnion_card_le
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.seedAxisPairs_card_le
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.specializedAxisFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.specializedAxisCountingResidual
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.honestReadVerifyAxisTree_no_bad
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.recoveredExponent_one_collision
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.exponentCollision_preserves_zero
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.sparseAcceptance_counting_regression
#print axioms Nock.NockVMROM.Thm54.TemplateAxisCounting.characteristicTwo_rejects_axisCounting
