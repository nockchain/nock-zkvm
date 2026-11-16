import Nock.Counts
import Nock.NockVMROM.Thm54.ProductionRawVerifier
import Nock.Walk

/-!
They deliberately do not encode
absence claims as propositions.

* The paper's NockVMROM theorem is at the paper.  The raw IO message commits multiplicity and
  the two accumulators; the verifier constructs the IO trace by applying `ioProgRowEnv` and
  `ioMemRowEnv`, whose column `1` is `SetEq.frac`.
* `RAP.β` is the shifted-orbit base `OrbitDomain.βcoset`.  The LogUp pole challenge is the separate
  field `ExactConfig.challenges.β`; no universal inequality between those fields is claimed.
* The current IO row domains contain `records + 1` points.  The compute and memory table domains
  contain their respective BFS row counts.  Thus these exact receipts do not supply the paper's
  still-required memory-side `M + 2L` row-accounting bridge; the compute-side paper
  count is `N` rows.
* The walk AIR reflects the line/count/accumulator recurrence, but the semantic
  theorem also takes `hfo` and `hFcommit`.  Binding those semantic hypotheses to the accepted table
  and walk traces is the residual cross-table obligation.
-/

namespace Nock.RedTeam.Batch18

open Classical
open Nock Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Walk
open Nock.Reified Nock.NockVMROM.Thm54
open scoped Polynomial

noncomputable section

/-! ## A. Verifier-reconstructed IO fractions -/

/-- The exported IO AIRs have no challenge columns.  Their exact trace widths and three-gate
interfaces are the concrete shape used by the raw verifier. -/
theorem b18_io_air_shape :
    Trans.ioProgAIR.numChallenges = 0 ∧
      Trans.ioProgAIR.constraints.length = 3 ∧
      Trans.ioProgAIR.numTraceCols = 2 ∧
      Trans.ioMemAIR.numChallenges = 0 ∧
      Trans.ioMemAIR.constraints.length = 3 ∧
      Trans.ioMemAIR.numTraceCols = 3 := by
  exact ⟨Trans.ioProgAIR_numChallenges, Trans.ioProgAIR_num_constraints,
    Trans.ioProgAIR_numTraceCols, Trans.ioMemAIR_numChallenges,
    Trans.ioMemAIR_num_constraints, Trans.ioMemAIR_numTraceCols⟩

section Raw

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ}
variable {R : RawPlusIOSegmentedFamily F K}

/-- At every active program-IO node, verifier-reconstructed trace column `1` evaluates to the
fraction generated from the authoritative derived request record. -/
theorem b18_computeIOTrace_column_one_is_frac
    (M : RawMessage R p)
    (hcap : R.exec.derivedRequestIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (i : Fin (R.exec.derivedRequestIO.length + 1)) :
    (M.computeIOTrace
        (⟨1, by rw [Trans.ioProgAIR_numTraceCols]; decide⟩ :
          Fin Trans.ioProgAIR.numTraceCols)).eval
        (algebraMap K (IOField K) (R.cfg.orbit.orbitPoint i)) =
      SetEq.frac (SetEq.RLC (IO.listExt R.exec.derivedRequestIO (i : ℕ))) := by
  have h :=
    encodeEnvTrace_eval_at_node
      (rows := fun q : Fin (R.exec.derivedRequestIO.length + 1) =>
        Trans.ioProgRowEnv
          (fun j => SetEq.RLC (IO.listExt R.exec.derivedRequestIO j))
          M.io.progAcc R.requests q)
      (nodes := fun q : Fin (R.exec.derivedRequestIO.length + 1) =>
        algebraMap K (IOField K) (R.cfg.orbit.orbitPoint q))
      ((algebraMap K (IOField K)).injective.comp
        (R.cfg.orbit.orbitPoint_injective hcap))
      i (⟨1, by rw [Trans.ioProgAIR_numTraceCols]; decide⟩ :
        Fin Trans.ioProgAIR.numTraceCols)
  simpa [RawMessage.computeIOTrace, Trans.ioProgRowEnv] using h

variable [CharP K p]

/-- The memory-IO trace has the same verifier-generated fraction in column `1`; only multiplicity
and the accumulator are prover data. -/
theorem b18_memoryIOTrace_column_one_is_frac
    (M : RawMessage R p)
    (hcap : R.exec.derivedResponseIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (i : Fin (R.exec.derivedResponseIO.length + 1)) :
    (M.memoryIOTrace
        (⟨1, by rw [Trans.ioMemAIR_numTraceCols]; decide⟩ :
          Fin Trans.ioMemAIR.numTraceCols)).eval
        (algebraMap K (IOField K) (R.cfg.orbit.orbitPoint i)) =
      SetEq.frac (SetEq.RLC (IO.listExt R.exec.derivedResponseIO (i : ℕ))) := by
  have h :=
    encodeEnvTrace_eval_at_node
      (rows := fun q : Fin (R.exec.derivedResponseIO.length + 1) =>
        Trans.ioMemRowEnv
          (fun j => SetEq.RLC (IO.listExt R.exec.derivedResponseIO j))
          (IO.castμ (𝔽 := K) M.io.multiplicity)
          M.io.memAcc R.responses R.outMem q)
      (nodes := fun q : Fin (R.exec.derivedResponseIO.length + 1) =>
        algebraMap K (IOField K) (R.cfg.orbit.orbitPoint q))
      ((algebraMap K (IOField K)).injective.comp
        (R.cfg.orbit.orbitPoint_injective hcap))
      i (⟨1, by rw [Trans.ioMemAIR_numTraceCols]; decide⟩ :
        Fin Trans.ioMemAIR.numTraceCols)
  simpa [RawMessage.memoryIOTrace, Trans.ioMemRowEnv] using h

/-- Actual raw-verifier soundness boundary: verifier gates plus all six segmented RAP families,
the characteristic bound, and the two IO capacities imply the exact multiset-IO language. -/
theorem b18_raw_six_rap_acceptance_implies_LIO
    {claim : P8PublicClaim} {ω : JointCoins K}
    (M : RawMessage R p) (hKp : R.cfg.Ksz < p)
    (hProgCap : R.exec.derivedRequestIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (hMemCap : R.exec.derivedResponseIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (h : M.Accepts claim ω) :
    IO.LIO R.cfg.Ksz R.exec.derivedRequestIO R.exec.derivedResponseIO :=
  M.lio_of_accepts hKp hProgCap hMemCap h

/-! ## B. Orbit shift versus LogUp challenge -/

/-- In the actual raw memory-table family, `RAP.β` and its nonzero certificate are inherited from
the orbit coset, while challenge slot `1` is the separate LogUp pole challenge
`cfg.challenges.β`.  This is a structural identity, not a claim that the two field values differ. -/
theorem b18_memory_table_rap_beta_roles (R : RawPlusIOSegmentedFamily F K)
    (kind : ConstraintKind) :
    (R.memoryTableRAP kind).β = R.cfg.orbit.βcoset ∧
      (R.memoryTableRAP kind).β_ne_zero = R.cfg.orbit.βcoset_ne_zero ∧
      R.memoryTableParams.chalVal 1 = R.cfg.challenges.β := by
  refine ⟨rfl, ?_, rfl⟩
  exact Subsingleton.elim _ _

/-! ## C. Exact current row domains -/

/-- Definitional domain receipt: table rows use the two BFS prefixes, whereas each IO row domain is
the algebraic lift of a `records + 1` orbit prefix. -/
theorem b18_raw_row_domain_definitions (R : RawPlusIOSegmentedFamily F K) :
    R.computeTableParams.domain .row = R.cfg.orbit.rowDomain R.cfg.compRows ∧
      R.memoryTableParams.domain .row = R.cfg.orbit.rowDomain R.cfg.memRows ∧
      R.progIOParams.domain .row =
        PlusIOSegmentedFamily.liftFinsetToIO
          (R.cfg.orbit.rowDomain (R.exec.derivedRequestIO.length + 1)) ∧
      R.memIOParams.domain .row =
        PlusIOSegmentedFamily.liftFinsetToIO
          (R.cfg.orbit.rowDomain (R.exec.derivedResponseIO.length + 1)) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Current raw-family row domains preserve the two capacity hypotheses exactly: table domains
have the BFS row counts, while IO domains have one accumulator row per record plus the initial
row.  No `M + 2L` equality is asserted here. -/
theorem b18_raw_row_domain_cardinalities (R : RawPlusIOSegmentedFamily F K)
    (hProgCap : R.exec.derivedRequestIO.length + 1 ≤ 2 ^ R.cfg.orbit.h)
    (hMemCap : R.exec.derivedResponseIO.length + 1 ≤ 2 ^ R.cfg.orbit.h) :
    (R.computeTableParams.domain .row).card = R.cfg.compRows ∧
      (R.memoryTableParams.domain .row).card = R.cfg.memRows ∧
      (R.progIOParams.domain .row).card = R.exec.derivedRequestIO.length + 1 ∧
      (R.memIOParams.domain .row).card = R.exec.derivedResponseIO.length + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [RawPlusIOSegmentedFamily.computeTableParams,
      SegmentedRAPParams.ofComputeConfig, ExactConfig.computeDomain] using
      R.cfg.orbit.rowDomain_card R.cfg.compRows_le
  · simpa [RawPlusIOSegmentedFamily.memoryTableParams,
      SegmentedRAPParams.ofMemoryConfig, ExactConfig.memoryDomain] using
      R.cfg.orbit.rowDomain_card R.cfg.memRows_le
  · rw [RawPlusIOSegmentedFamily.progIOParams]
    simp only [PlusIOSegmentedFamily.liftFinsetToIO,
      PlusIOSegmentedFamily.ioBaseDomain]
    rw [Finset.card_image_of_injective _ (algebraMap K (IOField K)).injective]
    exact R.cfg.orbit.rowDomain_card hProgCap
  · rw [RawPlusIOSegmentedFamily.memIOParams]
    simp only [PlusIOSegmentedFamily.liftFinsetToIO,
      PlusIOSegmentedFamily.ioBaseDomain]
    rw [Finset.card_image_of_injective _ (algebraMap K (IOField K)).injective]
    exact R.cfg.orbit.rowDomain_card hMemCap

end Raw

/-! ## D. Walk AIR shape and semantic theorem interface -/

/-- The exported walk AIR has exactly six trace columns, one challenge, and seven constraints
implementing the paper's line-indexed recurrence. -/
theorem b18_walk_air_shape :
    Trans.walkAIR.numTraceCols = 6 ∧
      Trans.walkAIR.numChallenges = 1 ∧
      Trans.walkAIR.constraints.length = 7 :=
  ⟨Trans.walkAIR_numTraceCols, Trans.walkAIR_numChallenges, Trans.walkAIR_num_constraints⟩

/-- Exact `Walk_IOP_final_prob` interface receipt.  In particular, `hfo` and `hFcommit` remain
explicit semantic hypotheses; the seven-gate `walkAIR` shape alone does not instantiate them. -/
theorem b18_walk_final_prob_requires_semantic_bindings
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {node_size n : ℕ} {S DT : Type*}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (enc : (S × DT) → (Fin node_size → K))
    (hEnc : Function.Injective enc) (lbl : ℕ → S × DT)
    (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n =>
        if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((Finset.univ.filter (fun q : K × K =>
        (∃ ln count acc : ℕ → K,
          WalkSat (fun i => rlc q.2 (enc (lbl i)))
            (fun i l => rlc q.2 (enc (clab i l))) fo
            ln count acc q.1 (rlc q.2 (enc (lbl 1)) * q.1) q.1 h ∧ acc h = 0)
        ∧ ¬ ReconGoal St lbl h)).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) :=
  Walk_IOP_final_prob St enc hEnc lbl clab fo hSf hvalid harity hfo hFcommit

end

end Nock.RedTeam.Batch18

#print axioms Nock.RedTeam.Batch18.b18_io_air_shape
#print axioms Nock.RedTeam.Batch18.b18_computeIOTrace_column_one_is_frac
#print axioms Nock.RedTeam.Batch18.b18_memoryIOTrace_column_one_is_frac
#print axioms Nock.RedTeam.Batch18.b18_raw_six_rap_acceptance_implies_LIO
#print axioms Nock.RedTeam.Batch18.b18_memory_table_rap_beta_roles
#print axioms Nock.RedTeam.Batch18.b18_raw_row_domain_definitions
#print axioms Nock.RedTeam.Batch18.b18_raw_row_domain_cardinalities
#print axioms Nock.RedTeam.Batch18.b18_walk_air_shape
#print axioms Nock.RedTeam.Batch18.b18_walk_final_prob_requires_semantic_bindings
