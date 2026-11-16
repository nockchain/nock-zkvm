import Nock.Framework.Core
import Nock.IO

/-!
Memory-execution separation in the framework: the structures `MES` (uniquely memory-execution separable), `CanonicalRAP` (two sub-RAPs sharing IO) and `OpcodeMemOneHot` (opcode and memory one-hot tables) with their operation counts, and the corresponding classes `UniqueMemoryExecutionSeparable`, `OpcodeMemoryOneHot` and `HasCanonicalRAP`.
-/

namespace Nock.Framework

open scoped Polynomial

/-! ## `Def:MES` — uniquely memory-execution separable -/

/-- **`Def:MES`.**  A language `L_Lang = {x | ∃ T, LangVM(x,T) = 0}` recognised by
    a verifier `LangVM` is *uniquely memory-execution separable* over `MEM` if there exist
    bijections `x ↦ (x_prog, x_mem)` and `T ↦ (T_prog, T_mem)` and verifiers
    `LangVMComputation`, `LangVMMemory` such that `x ∈ LangVM` iff there is a decomposition whose
    two sub-verifiers accept AND whose shared IO records lie in `L_mIO^MEM`.
    Acceptance `= 0` is modeled as the corresponding `Prop` holding. -/
structure MES (X Tw : Type*) (M : MEF) [DecidableEq M.Rec] where
  /-- Program half of `x`. -/
  Xprog : Type*
  /-- Memory half of `x`. -/
  Xmem : Type*
  /-- Program half of the trace `T`. -/
  Tprog : Type*
  /-- Memory half of the trace `T`. -/
  Tmem : Type*
  /-- Compute-table IO variable. -/
  IOprog : Type*
  /-- Memory-table IO variable. -/
  IOmem : Type*
  /-- The recognising verifier `LangVM(x,T)`. -/
  LangVM : X → Tw → Prop
  /-- The compute verifier `LangVMComputation(x_prog, T_prog, IO_prog)`. -/
  LangVMComputation : Xprog → Tprog → IOprog → Prop
  /-- The memory verifier `LangVMMemory(x_mem, T_mem, IO_mem)`. -/
  LangVMMemory : Xmem → Tmem → IOmem → Prop
  /-- The statement bijection `x ↦ x* = (x_prog, x_mem)`. -/
  splitX : X ≃ Xprog × Xmem
  /-- The trace bijection `T ↦ T* = (T_prog, T_mem)`. -/
  splitT : Tw ≃ Tprog × Tmem
  /-- `K` bound of the `L_mIO^{MEM,K}` language. -/
  K : ℕ
  /-- The IO variables are *semantically equivalent to an array pair of memory records*
      (`(requests, responses)`, the paper). -/
  ioRecords : IOprog → IOmem → List M.Rec × List M.Rec
  /-- **The separation equivalence.** -/
  correct : ∀ x : X,
    (∃ T, LangVM x T) ↔
      ∃ (T : Tw) (ioP : IOprog) (ioM : IOmem),
        LangVMComputation (splitX x).1 (splitT T).1 ioP
        ∧ LangVMMemory (splitX x).2 (splitT T).2 ioM
        ∧ Nock.IO.LmIO K (ioRecords ioP ioM).1 (ioRecords ioP ioM).2

/-! ## `Def:Canonical_RAP` — two sub-RAPs sharing IO -/

/-- **`Def:Canonical_RAP`.**  A uniquely memory-execution separable language has a
    *canonical RAP arithmetization* if there are common RAP parameters (`𝔽, e, h, d, (ω,β)`) and
    two sub-RAPs `RAP_prog`, `RAP_mem` (with `w_prog, w_mem ⊆ w_RAP`) such that
    `LangVMComputation(W_prog, IO_prog) = 0 ⟺ (W_prog, IO_prog)` satisfies `RAP_prog`,
    and likewise for memory.  `encodeProg/encodeMem` realise `(W, IO)` as a trace. -/
structure CanonicalRAP {X Tw : Type*} {M : MEF} [DecidableEq M.Rec] (mes : MES X Tw M)
    (F : Type*) [CommRing F] where
  /-- `RAP_prog`. -/
  Rprog : RAP F
  /-- `RAP_mem`. -/
  Rmem : RAP F
  /-- Common extension degree `e`. -/
  common_e : Rprog.e = Rmem.e
  /-- Common length exponent `h`. -/
  common_h : Rprog.h = Rmem.h
  /-- Common max degree `d`. -/
  common_d : Rprog.d = Rmem.d
  /-- Common `ω`. -/
  common_ω : Rprog.ω = Rmem.ω
  /-- Common `β`. -/
  common_β : Rprog.β = Rmem.β
  /-- Trace encoding of the compute witness+IO. -/
  encodeProg : mes.Xprog → mes.Tprog → mes.IOprog → (Fin Rprog.w → F[X])
  /-- Trace encoding of the memory witness+IO. -/
  encodeMem : mes.Xmem → mes.Tmem → mes.IOmem → (Fin Rmem.w → F[X])
  /-- **Compute equivalence.** -/
  compute_iff : ∀ xp tp iop,
    mes.LangVMComputation xp tp iop ↔ Rprog.Satisfies (encodeProg xp tp iop)
  /-- **Memory equivalence.** -/
  memory_iff : ∀ xm tm iom,
    mes.LangVMMemory xm tm iom ↔ Rmem.Satisfies (encodeMem xm tm iom)

/-! ## `Def:one-hot` — opcode and memory one-hot -/

/-- **`Def:one-hot`.**  A uniquely memory-execution separable language with a
    canonical RAP is *opcode and memory one-hot* of size `N_OP` and arity `M_OP` if there is a set
    of `N_OP` opcodes and a memory-requesting subset `OP_IO`, with the five semantic conditions:
      1. one opcode per compute row;
      2. one memory record per memory row;
      3. each opcode reads `≤ M_OP` records;
      4. only `OP_IO` opcodes request records;
      5. IO records resolved in-place.
    The selectors `xprog i j ∈ {0,1}` sit over field `F`; `opIO`, `regs` and the layout predicates
    capture 2–5 abstractly. -/
structure OpcodeMemOneHot (F : Type*) [CommRing F] where
  /-- `N_OP`: number of opcodes. -/
  NOP : ℕ
  /-- `M_OP`: memory arity. -/
  MOP : ℕ
  /-- `N_mem`: number of `𝔽`-elements needed to represent one memory record, `MEM ⊆ 𝔽^{N_mem}`. -/
  Nmem : ℕ
  /-- `h₁`: number of compute rows. -/
  h1 : ℕ
  /-- `h₂`: number of memory rows. -/
  h2 : ℕ
  /-- The opcode selector table `x_prog(i,j)`. -/
  xprog : Fin h1 → Fin NOP → F
  /-- `IO_comp(i,k) = IO_prog(i,k) ∈ MEM ⊆ 𝔽^{N_mem}`, the `k`-th memory record segment requested
      in compute row `i`. -/
  IOprog : Fin h1 → Fin MOP → (Fin Nmem → F)
  /-- `x_mem(r) ∈ MEM ⊆ 𝔽^{N_mem}`, the memory record verified in row `r` of `RAP_mem`. -/
  xmem : Fin h2 → (Fin Nmem → F)
  /-- The memory-requesting opcode subset `OP_IO ⊆ OP`, as a `Finset` of columns. -/
  opIO : Finset (Fin NOP)
  /-- `regs : OP_IO → [M_IO]`, the number of records requested per requesting opcode. -/
  regs : Fin NOP → ℕ
  /-- `h_R ≤ h₂`: the number of IO records resolved in the memory table. -/
  hR : ℕ
  /-- `IO_mem(r) ∈ MEM ⊆ 𝔽^{N_mem}`, the `r`-th IO record verified in the memory table. -/
  IOmem : Fin hR → (Fin Nmem → F)
  /-- **(1a) Booleanity:** every selector is `0` or `1`. -/
  boolean : ∀ i j, xprog i j * (1 - xprog i j) = 0
  /-- **(1c) One-hot:** exactly one opcode active per row. -/
  oneHot : ∀ i : Fin h1, (∑ j, xprog i j) = 1
  /-- **(3) Memory arity bound:** each requesting opcode reads `≤ M_OP` records. -/
  regs_le : ∀ j ∈ opIO, regs j ≤ MOP
  /-- **(4b) Zero IO row when no `OP_IO` opcode is active:**
      `∑_{j ∈ OP_IO} x_prog(i,j) = 0 ⇒ IO_prog(i,·) = 𝟎^{M_OP × N_mem}`. -/
  io_zero : ∀ i : Fin h1, (∑ j ∈ opIO, xprog i j) = 0 →
    ∀ (k : Fin MOP) (c : Fin Nmem), IOprog i k c = 0
  /-- **(4b) Zero-padding beyond the requested records:**
      `j ∈ OP_IO, x_prog(i,j) = 1 ⇒ ∀ k ∈ [M_OP]∖[regs(j)], IO_prog(i,k) = 𝟎^{N_mem}` — with the
      paper's `regs(i)` read as `regs(j)` for the (unique, one-hot) active opcode `j` of row `i`, and
      `[M_OP]∖[regs(j)]` the `0`-indexed columns `k` with `regs(j) ≤ k`. -/
  regs_zero_pad : ∀ (i : Fin h1) (j : Fin NOP), j ∈ opIO → xprog i j = 1 →
    ∀ (k : Fin MOP), regs j ≤ (k : ℕ) → ∀ c : Fin Nmem, IOprog i k c = 0
  /-- **(5) `h_R ≤ h₂`.** -/
  hR_le : hR ≤ h2
  /-- **(5) IO records resolved in-place:** `IO_mem ⊆ x_mem`, i.e. every verified IO
      record appears among the memory-table records. -/
  io_mem_subset : ∀ r : Fin hR, ∃ s : Fin h2, IOmem r = xmem s

/-- **`req_ops`.**  The total number of memory-requesting opcode activations of
    `(x_prog, IO_prog)`: `req_ops(x_prog) = ∑_{i=1}^{h₁} ∑_{j ∈ OP_IO} x_prog(i,j)`. -/
def reqOps {F : Type*} [CommRing F] (O : OpcodeMemOneHot F) : F :=
  ∑ i : Fin O.h1, ∑ j ∈ O.opIO, O.xprog i j

/-- **`mem_ops`.**  The total number of non-zero memory record requests:
    `mem_ops(IO_prog) = ∑_{i=1}^{h₁} ∑_{j=1}^{M_OP} 𝟏[IO_prog(i,j) ≠ 𝟎^{N_mem}]`, with `𝟏[·]` the
    indicator.  (`noncomputable`: the `≠ 𝟎` test uses classical decidability.) -/
noncomputable def memOps {F : Type*} [CommRing F] (O : OpcodeMemOneHot F) : ℕ := by
  classical
  exact ∑ i : Fin O.h1, ∑ j : Fin O.MOP, if O.IOprog i j = 0 then 0 else 1

/-! ## `Def:MES` as a class (S1) — `UniqueMemoryExecutionSeparable` -/

/-- **`UniqueMemoryExecutionSeparable ι M`.**  The class form of
    `MES`, keyed by a `VMSystem` tag `ι` and a memory-encoding family `M`.  A language is uniquely
    memory-execution separable over `M` if its statements/witnesses split into program/memory
    halves and membership is **exactly** the conjunction of a compute-side and memory-side
    acceptance whose shared IO records lie in `L_mIO^M`.  The `correct` biconditional is the paper
    separation equivalence; the Nock instance discharges it from the concrete recognizer definition
    (no `hcorrect` hypothesis is carried). -/
class UniqueMemoryExecutionSeparable (ι : Type u) [VMSystem ι] (M : MEF) where
  /-- Program-half statement type. -/
  ProgStatement : Type*
  /-- Memory-half statement type. -/
  MemStatement : Type*
  /-- Program-half witness type. -/
  ProgWitness : Type*
  /-- Memory-half witness type. -/
  MemWitness : Type*
  /-- Program IO type. -/
  ProgIO : Type*
  /-- Memory IO type. -/
  MemIO : Type*
  /-- Statement decomposition `x ↦ (x_prog, x_mem)`. -/
  splitStatement : VMSystem.Statement ι ≃ ProgStatement × MemStatement
  /-- Witness/trace decomposition `T ↦ (T_prog, T_mem)`. -/
  splitWitness : VMSystem.Witness ι ≃ ProgWitness × MemWitness
  /-- Compute sub-verifier `LangVMComputation(x_prog, T_prog, IO_prog)`. -/
  computeAccepts : ProgStatement → ProgWitness → ProgIO → Prop
  /-- Memory sub-verifier `LangVMMemory(x_mem, T_mem, IO_mem)`. -/
  memoryAccepts : MemStatement → MemWitness → MemIO → Prop
  /-- The IO variables as a `(requests, responses)` record-list pair. -/
  ioRecords : ProgIO → MemIO → List M.Rec × List M.Rec
  /-- `L_mIO^{M,K}` bound. -/
  K : ℕ
  /-- **The separation equivalence.** -/
  correct : ∀ x : VMSystem.Statement ι,
    Language ι x ↔
      ∃ (w : VMSystem.Witness ι) (ioP : ProgIO) (ioM : MemIO),
        computeAccepts (splitStatement x).1 (splitWitness w).1 ioP ∧
        memoryAccepts (splitStatement x).2 (splitWitness w).2 ioM ∧
        IO.LmIO K (ioRecords ioP ioM).1 (ioRecords ioP ioM).2

/-! ## `Def:one-hot` as a class (S3) — `OpcodeMemoryOneHot` -/

/-- **`OpcodeMemoryOneHot ι M F NOP MOP`.**  Opcode one-hot of
    size `NOP` and (memory-record) arity `MOP`.  A compute row selects
    **exactly one action** among `NOP` *numeric ROM opcodes* (`numericSelector`) **and** a separately
    typed *structural* action (`structuralSelector`, e.g. Nock `cons`) — their combined sum is `1`
    (never a bare `NOP`-column sum that would be false on structural rows).  `record_pos` records that
    every row opens `≥ 1` memory record (so `OP_IO = OP`), which is exactly why the paper's cond-4b
    `io_zero` antecedent is unsatisfiable — vacuous **by design**, not a proved non-trivial
    constraint.  `record_arity_le` is cond-3 (arity `≤ MOP`). -/
class OpcodeMemoryOneHot (ι : Type u) [VMSystem ι] (M : MEF) (F : Type*) [CommRing F]
    (NOP MOP : ℕ) [UniqueMemoryExecutionSeparable ι M] where
  /-- A compute-row descriptor (carries the opcode state). -/
  Row : Type
  /-- Selector of numeric ROM opcode `op` at a row. -/
  numericSelector : Row → Fin NOP → F
  /-- Selector of the single structural action (`cons`) at a row. -/
  structuralSelector : Row → F
  /-- Memory records opened by a row's opcode. -/
  recordCount : Row → ℕ
  /-- (1a) Numeric selectors are boolean. -/
  numeric_boolean : ∀ (row : Row) (op : Fin NOP),
    numericSelector row op * (1 - numericSelector row op) = 0
  /-- (1a) The structural selector is boolean. -/
  structural_boolean : ∀ row : Row, structuralSelector row * (1 - structuralSelector row) = 0
  /-- (1c) Exactly one action per compute row across the `NOP` numeric opcodes and
      the structural action. -/
  exactly_one_action_per_compute_row : ∀ row : Row,
    (∑ op, numericSelector row op) + structuralSelector row = 1
  /-- (3) Request arity: each row opens at most `MOP` memory records. -/
  record_arity_le : ∀ row : Row, recordCount row ≤ MOP
  /-- (4b vacuity) Every row opens `≥ 1` record (`OP_IO = OP`), so the cond-4b `io_zero`
      antecedent (`∑_{OP_IO} = 0`) never fires — vacuous by design. -/
  record_pos : ∀ row : Row, 1 ≤ recordCount row

/-! ## `Def:Canonical_RAP` as a class (S2) — `HasCanonicalRAP` -/

/-- **`Def:Canonical_RAP` as a class.**  The compute/memory chips have canonical
    reified RAP arithmetizations `Rprog`/`Rmem`, and their satisfiability corresponds exactly to
    algorithmic table acceptance: `progAccepts p ↔ progSatisfiable p` (and memory).  `ProgProblem`
    bundles a well-formed trace-family (the disclosed WF — injective evaluation nodes, shared
    challenges, per-row `WF`, `z ≠ 0` — lives inside `ProgProblem`, so the iff is unconditional over
    it).  The `w_RAP` shared-column embedding is not asserted here.

    **Deliberately standalone:** unlike `CanonicalRAP` (the `MES`-indexed structure), this class does
    NOT require `[UniqueMemoryExecutionSeparable ι M]`.  It states the two per-chip RAP↔acceptance
    correspondences directly, so a `VMSystem` tag `ι` with a memory-encoding family `M` can carry the
    canonical-RAP data without first exhibiting the full S1 separation. -/
class HasCanonicalRAP (ι : Type u) [VMSystem ι] (M : MEF) (F : Type*) [CommRing F] where
  Rprog : RAP F
  Rmem : RAP F
  ProgProblem : Type*
  MemProblem : Type*
  progAccepts : ProgProblem → Prop
  progSatisfiable : ProgProblem → Prop
  memAccepts : MemProblem → Prop
  memSatisfiable : MemProblem → Prop
  compute_iff : ∀ p, progAccepts p ↔ progSatisfiable p
  memory_iff : ∀ p, memAccepts p ↔ memSatisfiable p

end Nock.Framework
