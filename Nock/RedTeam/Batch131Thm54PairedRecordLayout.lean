import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.NockVMROM.Thm54.DistinctCensusExecution
import Nock.RedTeam.Batch130Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame, read from the body before the appendix:

* the paper — `read_root` removes a memory record from the `IO` column, checks its root
  against the parent label, and **adds the record to the global accumulator `intermediate`**.
* the paper — `verify_child` **removes an element from `intermediate`** and checks it
  against the parent node.
* the paper — "the `IO` and `intermediate` multisets are also checked to be zero, so every
  timestamp needs to be removed from the `IO` multiset, added to `intermediate`, and then removed
  again"; and "indexing the respective memory records through their unique timestamps".
* `Lem:ldse_mse` the paper — for multilinear `aᵢ(Y)`, `bᵢ(Y)` over `𝔽` with
  `char p > n`, `∏(X + aᵢ(Y)) = ∏(X + bᵢ(Y))` in `𝔽[X,Y]` **iff**
  `Σ 1/(X + aᵢ(Y)) = Σ 1/(X + bᵢ(Y))` in `𝔽(X,Y)`.
* `lem:set_inclusion` the paper — `S ⊆ T` iff there are `𝔽_p` multiplicities `mᵢ` with
  `Σ 1/(X + aᵢ(Y)) = Σ mᵢ/(X + bᵢ(Y))` in `𝔽(X,Y)`; if `S = T` the `mᵢ` may be taken nonzero, and
  conversely with `b` injective and every `mᵢ ≠ 0` one gets `S = T`.
* `Lem:MEM_2`(2) the paper — `L_IO ≡ L_uSE`: set equality plus distinct responses **is**
  the permutation.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: **FINDING (scoped)**.  Two of its supporting claims do not survive:

1. **Attack B.**  `logup_mass_does_not_determine_record_perm` is exhibited at `(β, γ) = (0, 1)`.
   `beta_zero_is_the_degenerate_pole` shows `β = 0` is exactly the point where the LogUp pole
   loses its offset (`pole = RLC^γ`, the paper reads `RLC^γ(·) − β`), and
   `ao109_witness_agrees_only_at_beta_zero` scans **all 97** offsets and finds the exhibited pair
   agrees at that one degenerate point and nowhere else.  The witness is therefore a single-point
   coincidence, not a separation in the protocol's regime.  The *claim* it supports does survive:
   `logup_mass_nondegenerate_counterexample` repairs it at `β = 3` with all four poles nonzero.
   And `nondegenerate_witness_dies_at_beta_zero` plus
   `ao109_witness_dies_at_beta_three` show each witness is killed by a *different* offset — the
   paper's `F(X, Y)` quantification is what removes them, exactly as `Lem:ldse_mse` states.

2. **Attack A / G.**  That is not the paper's mechanism and is
   not the cheapest carrier.  `pairedRecordLayout_iff_intermediate_LIO` shows
   `PairedRecordLayout` **is** the paper's `L_IO` membership of the `(IO, intermediate)` column
   pair — the verbatim right-hand side of `Thm:IO_result` that the paper names — and
   `IO.io_result_LIO` already carries that right-hand side as an **iff** against the `F(X, Y)`
   accumulator.  So the paper's LDSE-to-MSE route is present, formalized, and applicable; what is
   missing is its *input*.  `memory_rows_pin_the_challenge` compiles exactly why that input is
   absent: `MemoryRowAccepted` pins every memory row's `Inputs` to `E.cfg.challenges.memoryInputs`,
   so `E` carries the accumulator at one scalar offset and no `F(X, Y)` identity.
   Separately, `addedRemovedAgain_of_timestamp_key` exhibits a strictly cheaper carrier
   decomposition than a record `Perm` partition — timestamp support plus a scalar key condition on
   the record columns, which is the paper's own "indexing the respective memory records through
   their unique timestamps".

This artifact inhabits nothing:
it does not inhabit `PairedRecordLayout`, `AddedRemovedAgain`, `timestampClosed`, or
`ForestExponentOrder`, and it makes no carrier change.  The NMR axis is not re-litigated.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Nock.RedTeam.Batch131

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.AxisBridge
open Nock.AxisBatching
open Nock.NockVMROM.Thm54.RowLayout

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A.

The *scope* is visible in the types: the accumulator and the mass identity
live at `E.cfg.challenges.memoryInputs`, one scalar `(z, β, γ)` tuple. -/

/-- Independent re-derivation: the ordered `intermediate` accumulator with both global zero
boundaries, from `E` alone. -/
theorem interChain_independent (E : BuildableNockExecution F K) :
    MemoryTable.InterChain E.cfg.challenges.memoryInputs 0 0
      (GenericHonestData.memoryPubRows E.exec) :=
  GenericHonestData.execution_interChain E

/-- Independent re-derivation: the record-level LogUp mass identity, from `E` alone, **at
`E.cfg.challenges.memoryInputs`**. -/
theorem logup_mass_balanced_independent (E : BuildableNockExecution F K) :
    ((List.filter (fun p => decide (p.st = MemoryTable.MState.read_root))
        (GenericHonestData.memoryPubRows E.exec)).map
        (fun p => (MemoryTable.pole E.cfg.challenges.memoryInputs p.mem p.cprime)⁻¹)).sum
      = ((List.filter (fun p => decide (p.st = MemoryTable.MState.verify_child))
          (GenericHonestData.memoryPubRows E.exec)).map
          (fun p => (MemoryTable.pole E.cfg.challenges.memoryInputs p.mem p.cprime)⁻¹)).sum :=
  GenericHonestData.execution_logup_mass_balanced E

/-- **The compiled reason the paper's `F(X, Y)` input is not on `E`.**  Row acceptance pins every
memory row's RAP `Inputs` to the configuration's own `(z, β, γ)`.  So `E` exhibits the
`intermediate` accumulator at exactly one scalar offset; there is no family over offsets on `E`,
hence no `Lem:ldse_mse` antecedent. -/
theorem memory_rows_pin_the_challenge (E : BuildableNockExecution F K) :
    ∀ row ∈ E.exec.memoryRows, row.2.1 = E.cfg.challenges.memoryInputs := fun row hrow =>
  ((ExactExecution.memoryRowsAccepted_iff E.exec).1
    E.chained.semantic.2.1 row hrow).2.1

/-! ## B. Attack E — the two "already held" facts are genuinely already held -/

/-- Under honest `ver`, `exec.rawResponses` **is** `addedRecordList` (by-ver IO
recovers the by-state intermediate list). -/
theorem rawResponses_is_addedRecordList_independent {cfg : ExactConfig F K}
    (exec : ExactExecution cfg)
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    exec.rawResponses = RowLayout.addedRecordList exec :=
  RowLayout.rawResponses_eq_addedRecordList exec hhon

/-- `requestNodup` and `recordCountBalance` are pre-existing fields of the fourteen-field carrier:
the eta receipt names them and nothing was added. -/
theorem execution_eta_still_fourteen_fields_batch131 (E : BuildableNockExecution F K) :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } :=
  E.eta_with_memoryTrace

/-- The **encoded** added record list is `Nodup` on `E` under honest `ver`. -/
theorem encoded_addedRecordList_nodup (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    ((RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r (E.exec.cprimeOf r))).Nodup
        := by
  have hnd := (GenericHonestData.execution_lio_of_requestNodup E).2.1
  rwa [ExactExecution.derivedResponseIO_eq_map_encRecC E.exec hC,
    GenericHonestData.rawResponses_eq_addedRecordList _ hhon] at hnd

/-- Independent re-derivation of the equal-length fact from `E.recordCountBalance`. -/
theorem consumed_length_eq_added_length_independent (E : BuildableNockExecution F K) :
    (RowLayout.consumedRecordList E.exec).length
      = (RowLayout.addedRecordList E.exec).length :=
  GenericHonestData.consumed_length_eq_added_length E

/-! ## C. Attack A — `PairedRecordLayout` IS the paper's `Thm:IO_result` right-hand side on the
`(IO, intermediate)` column pair

the paper says the `intermediate` treatment "is equivalent to Theorem `Thm:IO_result`,
noting simply that in this case the `IO` and `intermediate` columns function as the two memory
record columns that are matched within the same table".  `IO.LIO` is record-type generic
(`Nock/IO.lean:60`), so that object can be written directly at the `MemRec` level, and its
permutation component is `PairedRecordLayout` verbatim. -/

/-- **The paper's object closes the premise.**  `L_IO` on the `(intermediate, IO)` record columns
gives `PairedRecordLayout` on its permutation component alone. -/
theorem pairedRecordLayout_of_intermediate_LIO (E : BuildableNockExecution F K)
    (h : IO.LIO E.cfg.Ksz (RowLayout.consumedRecordList E.exec)
          (RowLayout.addedRecordList E.exec)) :
    RowLayout.PairedRecordLayout E.exec :=
  h.2.2

/-- **And it is exactly the premise**, given only what `E` already carries: the `[K]` index range
plus `addedRecordList_nodup`.  So the named premise is not weaker or stronger than the paper's
`Thm:IO_result` right-hand side on this column pair — it is that object. -/
theorem pairedRecordLayout_iff_intermediate_LIO (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hrange : IO.InRange E.cfg.Ksz (RowLayout.addedRecordList E.exec).length) :
    IO.LIO E.cfg.Ksz (RowLayout.consumedRecordList E.exec)
        (RowLayout.addedRecordList E.exec)
      ↔ RowLayout.PairedRecordLayout E.exec :=
  ⟨fun h => h.2.2,
    fun h => ⟨hrange, GenericHonestData.addedRecordList_nodup E hhon hC, h⟩⟩

/-- **The paper's LDSE-to-MSE route is present and applicable.**  `IO.io_result_LIO` is
`Thm:IO_result` as an *iff* between the `F(X, Y)` `RAP_prog-IO`/`RAP_mem-IO` accumulator
satisfaction (`ProgIOSat`/`MemIOSat` over `RatFunc (RatFunc K)`) and `L_IO`.  Instantiated on the
encoded `(intermediate, IO)` record columns it is available with `hrespnd` **already discharged**
by `encoded_addedRecordList_nodup`.  Nothing here is a `RootTrace` partition. -/
theorem paper_io_result_route_available_on_intermediate_columns
    (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hKreq : IO.InRange E.cfg.Ksz
      ((RowLayout.consumedRecordList E.exec).map (fun r => NockVM.encRecC r
          (E.exec.cprimeOf r))).length)
    (hKresp : ((RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r
        (E.exec.cprimeOf r))).length
      ≤ E.cfg.Ksz)
    (hreqnd : ((RowLayout.consumedRecordList E.exec).map (fun r => NockVM.encRecC r
        (E.exec.cprimeOf r))).Nodup) :
    (∃ (m : Fin ((RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r
        (E.exec.cprimeOf r))).length →
          ZMod (ringChar K))
        (accP accM : ℕ → RatFunc (RatFunc K))
        (requests responses out_mem : RatFunc (RatFunc K)),
        (∀ j, m j ≠ 0)
        ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt
            ((RowLayout.consumedRecordList E.exec).map (fun r => NockVM.encRecC r
                (E.exec.cprimeOf r))) i)) accP requests
            ((RowLayout.consumedRecordList E.exec).map (fun r => NockVM.encRecC r
                (E.exec.cprimeOf r))).length
        ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt
            ((RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r
                (E.exec.cprimeOf r))) i)) (IO.castμ m)
            accM responses out_mem
            ((RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r
                (E.exec.cprimeOf r))).length
        ∧ requests = responses ∧ out_mem = 0)
      ↔ IO.LIO E.cfg.Ksz
          ((RowLayout.consumedRecordList E.exec).map (fun r => NockVM.encRecC r
              (E.exec.cprimeOf r)))
          ((RowLayout.addedRecordList E.exec).map (fun r => NockVM.encRecC r (E.exec.cprimeOf r)))
              :=
  IO.io_result_LIO E.cfg.Ksz E.Ksz_lt_ringChar _ _ hKreq hKresp hreqnd
    (encoded_addedRecordList_nodup E hhon hC)

/-! ## D. Attack G — a strictly cheaper carrier shape than a verify-side record partition

the paper and the paper say the records are *indexed through their unique timestamps*.
Decomposed that way, the residual splits into a support fact and a scalar key fact on the record
columns — no `Perm` partition on `RootTrace` is needed. -/

/-- Every record added to `intermediate` has its timestamp removed again. -/
def TimestampSupportedAdded {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  ∀ s ∈ RowLayout.addedRecordList exec,
    ∃ r ∈ RowLayout.consumedRecordList exec, r.ts = s.ts

/-- The timestamp is a key across the two columns: a removed record that shares an added record's
timestamp *is* that record.  Four scalar equalities, not a permutation. -/
def TimestampKeyedColumns {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  ∀ s ∈ RowLayout.addedRecordList exec,
    ∀ r ∈ RowLayout.consumedRecordList exec, r.ts = s.ts → r = s

/-- **The cheaper decomposition closes the residual.** -/
theorem addedRemovedAgain_of_timestamp_key {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (hsupp : TimestampSupportedAdded exec) (hkey : TimestampKeyedColumns exec) :
    GenericHonestData.AddedRemovedAgain exec := by
  intro s hs
  obtain ⟨r, hr, hts⟩ := hsupp s hs
  have : r = s := hkey s hs r hr hts
  exact this ▸ hr

/-- The same decomposition reaches the named premise. -/
theorem pairedRecordLayout_of_timestamp_key (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hsupp : TimestampSupportedAdded E.exec) (hkey : TimestampKeyedColumns E.exec) :
    RowLayout.PairedRecordLayout E.exec :=
  GenericHonestData.pairedRecordLayout_of_addedRemovedAgain E hhon hC
    (addedRemovedAgain_of_timestamp_key hsupp hkey)

/-- `E.memoryTrace` derives the paper's one
global `intermediate` matching **at the timestamp level** — `L_mIO` between the forest's
`read_root` and `verify_child` `z^i` multisets — unconditionally.  It is at the reconstructed-tree
layer (`exactAxisTree`), not the row layer, so it does not by itself reach the record lists; but it
is a real derived object on `E` and belongs in the inventory. -/
theorem execution_intermediate_timestamp_matching (E : BuildableNockExecution F K) :
    IO.LmIO E.cfg.Ksz (forestReadTimestamps E.cfg E.execA)
      (forestVerifyTimestamps E.cfg E.execA) :=
  E.memoryTrace.intermediateMatching

/-! ## E. Attack F — the `MTree` shadow, labelled as a shadow

`AxisBatching.MTree.verify` carries an exponent and an axis and nothing else, so no `MemRec`
reaches `exactAxisTree`.  Per the frame-lock rule this is recorded as an `MTree`-level fact and is
**not** treated as decisive about the paper-level object; the decisive layer statements are §A and
§C above. -/

/-- Type-level receipt: the `verify` constructor's payload is `(ℕ, K)`. -/
def mtree_verify_payload_is_exponent_and_axis : ℕ → K → MTree K → MTree K :=
  MTree.verify

/-! ## F.

`addedRemovedAgain_iff_pairedRecordLayout` is re-obtained, and then the reduction's reliance on
the already-held facts is witnessed: with the inclusion and equal lengths but a **repeat** in the
added list, the two lists are *not* a permutation.  So the forward direction is not trivial and
`addedRecordList_nodup` is load-bearing. -/

theorem addedRemovedAgain_iff_pairedRecordLayout_independent
    (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    GenericHonestData.AddedRemovedAgain E.exec
      ↔ RowLayout.PairedRecordLayout E.exec :=
  GenericHonestData.addedRemovedAgain_iff_pairedRecordLayout E hhon hC

/-! ## G. The concrete fixture-field section: Attack B and the non-vacuity witnesses -/

namespace Concrete

abbrev F97 := ZMod 97

local instance prime97b131 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- A record whose only nonzero component is its timestamp, written with explicit fingerprints so
no `Zero` instance has to be unfolded. -/
def tsRec (t : F97) : ComputeTable.MemRec F97 :=
  ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 0, t⟩

/-- LogUp challenges with `γ = 1` and a **variable** pole offset `β` (the paper:
`RLC^γ(·) − β`). -/
def chal (β : F97) : MemoryTable.Inputs F97 := ⟨0, β, 1⟩

theorem pole_tsRec (β t : F97) :
    MemoryTable.pole (chal β) (tsRec t) = t - β := by
  simp [MemoryTable.pole, MemoryTable.recRLC, tsRec, chal]

/-- **`β = 0` is the degenerate point of the pole construction.**  There the LogUp pole loses its
offset entirely and is just the RLC, so the accumulator's only challenge-dependent ingredient at
`γ = 1` has been switched off. -/
theorem beta_zero_is_the_degenerate_pole (r : ComputeTable.MemRec F97) :
    MemoryTable.pole (chal 0) r = MemoryTable.recRLC 1 r := by
  simp [MemoryTable.pole, chal]

/-! ### The four modular inverses the two witnesses need -/

theorem inv_1 : (1 : F97)⁻¹ = 1 := inv_one
theorem inv_2 : (2 : F97)⁻¹ = 49 := inv_eq_of_mul_eq_one_right (by decide)
theorem inv_4 : (4 : F97)⁻¹ = 73 := inv_eq_of_mul_eq_one_right (by decide)
theorem inv_5 : (5 : F97)⁻¹ = 39 := inv_eq_of_mul_eq_one_right (by decide)
theorem inv_92 : (92 : F97)⁻¹ = 58 := inv_eq_of_mul_eq_one_right (by decide)
theorem inv_93 : (93 : F97)⁻¹ = 24 := inv_eq_of_mul_eq_one_right (by decide)
theorem inv_95 : (95 : F97)⁻¹ = 48 := inv_eq_of_mul_eq_one_right (by decide)
theorem inv_96 : (96 : F97)⁻¹ = 96 := inv_eq_of_mul_eq_one_right (by decide)


theorem ao109_mass_left_at_beta_three :
    ((([1, 96] : List F97).map tsRec).map
      (fun r => (MemoryTable.pole (chal 3) r)⁻¹)).sum = 72 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pole_tsRec]
  rw [show ((1 : F97) - 3) = 95 by decide, show ((96 : F97) - 3) = 93 by decide,
    inv_95, inv_93]
  decide

theorem ao109_mass_right_at_beta_three :
    ((([2, 95] : List F97).map tsRec).map
      (fun r => (MemoryTable.pole (chal 3) r)⁻¹)).sum = 57 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pole_tsRec]
  rw [show ((2 : F97) - 3) = 96 by decide, show ((95 : F97) - 3) = 92 by decide,
    inv_96, inv_92]
  decide

/-- Its two lists have *different*
LogUp mass at `β = 3`.  Together with `beta_zero_is_the_degenerate_pole`, the exhibited
counterexample is a one-point coincidence at the degenerate `β = 0`, not a separation in the
protocol's regime — it is exactly the small-probability event the paper's `F(X, Y)` identity quantifies away. -/
theorem ao109_witness_dies_at_beta_three :
    ((([1, 96] : List F97).map tsRec).map
        (fun r => (MemoryTable.pole (chal 3) r)⁻¹)).sum
      ≠ ((([2, 95] : List F97).map tsRec).map
        (fun r => (MemoryTable.pole (chal 3) r)⁻¹)).sum := by
  rw [ao109_mass_left_at_beta_three, ao109_mass_right_at_beta_three]
  decide

/-! ### Attack B.2 — the repaired, non-degenerate witness

Here is the replacement at `β = 3`, where the pole keeps its offset
and none of the four poles vanishes. -/

theorem poles_nonzero_at_beta_three :
    MemoryTable.pole (chal 3) (tsRec 1) ≠ 0
      ∧ MemoryTable.pole (chal 3) (tsRec 5) ≠ 0
      ∧ MemoryTable.pole (chal 3) (tsRec 2) ≠ 0
      ∧ MemoryTable.pole (chal 3) (tsRec 4) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pole_tsRec] <;> decide

theorem repaired_mass_left_at_beta_three :
    ((([1, 5] : List F97).map tsRec).map
      (fun r => (MemoryTable.pole (chal 3) r)⁻¹)).sum = 0 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pole_tsRec]
  rw [show ((1 : F97) - 3) = 95 by decide, show ((5 : F97) - 3) = 2 by decide,
    inv_95, inv_2]
  decide

theorem repaired_mass_right_at_beta_three :
    ((([2, 4] : List F97).map tsRec).map
      (fun r => (MemoryTable.pole (chal 3) r)⁻¹)).sum = 0 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pole_tsRec]
  rw [show ((2 : F97) - 3) = 96 by decide, show ((4 : F97) - 3) = 1 by decide,
    inv_96, inv_1]
  decide

/-- **Repaired compiled negative.**  At the real fixture field, at the *non-degenerate* offset
`β = 3` with `γ = 1` and every pole nonzero, two repeat-free two-record lists of equal length have
equal `pole⁻¹` mass and are not a `List.Perm`.  So "equal LogUp mass at one sampled challenge is
not the record matching" stands — but it needed this witness, not the `β = 0` one. -/
theorem logup_mass_nondegenerate_counterexample :
    ((([1, 5] : List F97).map tsRec).map
        (fun r => (MemoryTable.pole (chal 3) r)⁻¹)).sum
      = ((([2, 4] : List F97).map tsRec).map
        (fun r => (MemoryTable.pole (chal 3) r)⁻¹)).sum
    ∧ (([1, 5] : List F97).map tsRec).Nodup
    ∧ (([2, 4] : List F97).map tsRec).Nodup
    ∧ (([2, 4] : List F97).map tsRec).length
        = (([1, 5] : List F97).map tsRec).length
    ∧ ¬ (([2, 4] : List F97).map tsRec).Perm (([1, 5] : List F97).map tsRec) := by
  refine ⟨by rw [repaired_mass_left_at_beta_three,
    repaired_mass_right_at_beta_three], ?_, ?_, rfl, ?_⟩
  · simp only [List.map_cons, List.map_nil, tsRec, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil, and_true, or_false,
      ComputeTable.MemRec.mk.injEq, true_and]
    decide
  · simp only [List.map_cons, List.map_nil, tsRec, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil, and_true, or_false,
      ComputeTable.MemRec.mk.injEq, true_and]
    decide
  · intro hp
    have hmem : tsRec 2 ∈ (([1, 5] : List F97).map tsRec) :=
      hp.mem_iff.mp (by simp)
    simp only [List.map_cons, List.map_nil, tsRec, List.mem_cons, List.not_mem_nil,
      or_false, ComputeTable.MemRec.mk.injEq, true_and] at hmem
    revert hmem
    decide

theorem repaired_mass_left_at_beta_zero :
    ((([1, 5] : List F97).map tsRec).map
      (fun r => (MemoryTable.pole (chal 0) r)⁻¹)).sum = 40 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pole_tsRec]
  rw [show ((1 : F97) - 0) = 1 by decide, show ((5 : F97) - 0) = 5 by decide,
    inv_1, inv_5]
  decide

theorem repaired_mass_right_at_beta_zero :
    ((([2, 4] : List F97).map tsRec).map
      (fun r => (MemoryTable.pole (chal 0) r)⁻¹)).sum = 25 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pole_tsRec]
  rw [show ((2 : F97) - 0) = 2 by decide, show ((4 : F97) - 0) = 4 by decide,
    inv_2, inv_4]
  decide

/-- **Neither witness survives challenge quantification, and they die at *different* offsets.**
That is the paper's mechanism in miniature: `Lem:ldse_mse` is an
identity in the formal variable, so a coincidence at one instantiation is not the matching. -/
theorem repaired_witness_dies_at_beta_zero :
    ((([1, 5] : List F97).map tsRec).map
        (fun r => (MemoryTable.pole (chal 0) r)⁻¹)).sum
      ≠ ((([2, 4] : List F97).map tsRec).map
        (fun r => (MemoryTable.pole (chal 0) r)⁻¹)).sum := by
  rw [repaired_mass_left_at_beta_zero, repaired_mass_right_at_beta_zero]
  decide

/-! ### The all-offset scan, in the paper's cleared `L_MSE` form

the paper writes the multiset argument multiplicatively; clearing the two denominators turns
"equal `pole⁻¹` mass" for a pair of two-record lists into the polynomial condition below, which
needs no inverses and can therefore be scanned over the whole fixture field.  Both scans return a
**single** offset, which is the quantitative form of the Attack-B finding. -/

/-- The cleared form of "the two two-record lists have equal LogUp mass
at offset `β`": `(p_a + p_b)·p_c·p_d = (p_c + p_d)·p_a·p_b`. -/
def crossedMSE (β a b c d : F97) : F97 :=
  ((a - β) + (b - β)) * ((c - β) * (d - β))
    - ((c - β) + (d - β)) * ((a - β) * (b - β))

theorem ao109_crossedMSE_vanishes_only_at_beta_zero :
    ∀ β : F97, crossedMSE β 1 96 2 95 = 0 ↔ β = 0 := by decide

/-- The repaired pair meets it at exactly **one** offset too, and a different one. -/
theorem repaired_crossedMSE_vanishes_only_at_beta_three :
    ∀ β : F97, crossedMSE β 1 5 2 4 = 0 ↔ β = 3 := by decide

/-! ### Attack D — the reduction's hypotheses are essential (non-vacuity witnesses) -/

/-- **`AddedRemovedAgain`'s shape is satisfiable and refutable**, so the equivalence is not
vacuous on either side: a reordering satisfies the inclusion, a changed record refutes it. -/
theorem addedRemovedAgain_shape_satisfiable_and_refutable :
    (∀ r ∈ ([tsRec 1, tsRec 2] : List (ComputeTable.MemRec F97)),
        r ∈ ([tsRec 2, tsRec 1] : List (ComputeTable.MemRec F97)))
    ∧ ¬ (∀ r ∈ ([tsRec 1, tsRec 2] : List (ComputeTable.MemRec F97)),
        r ∈ ([tsRec 2, tsRec 3] : List (ComputeTable.MemRec F97))) := by
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    tauto
  · intro h
    have hmem := h (tsRec 1) (by simp)
    simp only [tsRec, List.mem_cons, List.not_mem_nil, or_false,
      ComputeTable.MemRec.mk.injEq, true_and] at hmem
    revert hmem
    decide

/-- Inclusion plus equal
lengths, but with a repeat on the added side, does *not* give a permutation.  So the forward
direction of the equivalence genuinely consumes the already-held `Nodup`, and the reduction is not
a trivial restatement. -/
theorem reduction_needs_added_nodup :
    (∀ r ∈ ([tsRec 1, tsRec 1] : List (ComputeTable.MemRec F97)),
        r ∈ ([tsRec 1, tsRec 2] : List (ComputeTable.MemRec F97)))
    ∧ ([tsRec 1, tsRec 2] : List (ComputeTable.MemRec F97)).length
        = ([tsRec 1, tsRec 1] : List (ComputeTable.MemRec F97)).length
    ∧ ¬ ([tsRec 1, tsRec 1] : List (ComputeTable.MemRec F97)).Nodup
    ∧ ¬ ([tsRec 1, tsRec 2] : List (ComputeTable.MemRec F97)).Perm
          [tsRec 1, tsRec 1] := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    tauto
  · simp only [tsRec, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, and_true, or_false]
    tauto
  · intro hp
    have hmem : tsRec 2 ∈ ([tsRec 1, tsRec 1] : List (ComputeTable.MemRec F97)) :=
      hp.mem_iff.mp (by simp)
    simp only [tsRec, List.mem_cons, List.not_mem_nil, or_false,
      ComputeTable.MemRec.mk.injEq, true_and] at hmem
    revert hmem
    decide

/-- **Attack G non-vacuity.**  The two halves of the cheaper decomposition are independent:
timestamp support without the key condition does not give the inclusion. -/
theorem timestamp_support_alone_is_not_the_inclusion :
    (∃ r ∈ ([tsRec 1, tsRec 2] : List (ComputeTable.MemRec F97)),
        r.ts = (tsRec 1 : ComputeTable.MemRec F97).ts)
    ∧ (⟨⟨1, 0, 0⟩, ⟨0, 0, 0⟩, 0, 1⟩ : ComputeTable.MemRec F97).ts
        = (tsRec 1 : ComputeTable.MemRec F97).ts
    ∧ (⟨⟨1, 0, 0⟩, ⟨0, 0, 0⟩, 0, 1⟩ : ComputeTable.MemRec F97) ≠ tsRec 1 := by
  refine ⟨⟨tsRec 1, by simp, rfl⟩, rfl, ?_⟩
  simp only [tsRec, ne_eq, ComputeTable.MemRec.mk.injEq, ComputeTable.FP.mk.injEq]
  intro h
  revert h
  decide

end Concrete

/-! ## H. -/

variable [Fintype F] [DecidableEq F]

/-- `ResidualPremises` still four named fields. -/
theorem residualPremises_eta_still_four_batch131
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch130.residualPremises_eta_still_four_batch130 P

/-- Census extras still five named fields. -/
theorem censusRecordPremises_eta_still_five_batch131
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch130.censusRecordPremises_eta_still_five_batch130 C

/-- `MemoryRecordPremises` still two fields, and `timestampClosed` is still named. -/
theorem memoryRecordPremises_still_two_batch131
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  GenericHonestData.memoryRecordPremises_still_two_after_logup_inventory M

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen_batch131
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  Batch130.consumed_capstone_and_alias_remain_frozen_batch130 P hax hbasis hwidth

inductive ReviewedField131
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | exact_resources
  | row_budgets
  | shared_forest_axis
  deriving DecidableEq

def substantiveFields131 : List ReviewedField131 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets, .shared_forest_axis]

def typeSummaryFields131 : List ReviewedField131 := [.structural]

def residualFields131 : List ReviewedField131 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- Independent `11+1+2` re-check.  Not a reinterpretation: the same fourteen-field partition of
the released capstone statement at F97 that `Batch91.exact_eleven_one_two_partition` fixes. -/
theorem independent_exact_eleven_one_two_accounting_batch131 :
    substantiveFields131.length = 11 ∧
      typeSummaryFields131.length = 1 ∧
      residualFields131 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields131.length = 2 ∧
      (substantiveFields131 ++ typeSummaryFields131 ++ residualFields131).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-- The released builder still takes `hzero`; the fibre is still `∀ a g` under the named window. -/
theorem released_builder_still_takes_hzero_batch131
    {E : BuildableNockExecution F K}
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧
      E.cfg.memRows < ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  Batch130.released_builder_still_takes_hzero_batch130 I hprl hmore hord hordM hrows hhon R hzero hgenF hF


#print axioms interChain_independent
#print axioms logup_mass_balanced_independent
#print axioms memory_rows_pin_the_challenge
#print axioms rawResponses_is_addedRecordList_independent
#print axioms execution_eta_still_fourteen_fields_batch131
#print axioms encoded_addedRecordList_nodup
#print axioms consumed_length_eq_added_length_independent
#print axioms pairedRecordLayout_of_intermediate_LIO
#print axioms pairedRecordLayout_iff_intermediate_LIO
#print axioms paper_io_result_route_available_on_intermediate_columns
#print axioms addedRemovedAgain_of_timestamp_key
#print axioms pairedRecordLayout_of_timestamp_key
#print axioms execution_intermediate_timestamp_matching
#print axioms addedRemovedAgain_iff_pairedRecordLayout_independent
#print axioms Concrete.pole_tsRec
#print axioms Concrete.beta_zero_is_the_degenerate_pole
#print axioms Concrete.ao109_mass_left_at_beta_three
#print axioms Concrete.ao109_mass_right_at_beta_three
#print axioms Concrete.ao109_witness_dies_at_beta_three
#print axioms Concrete.poles_nonzero_at_beta_three
#print axioms Concrete.repaired_mass_left_at_beta_three
#print axioms Concrete.repaired_mass_right_at_beta_three
#print axioms Concrete.logup_mass_nondegenerate_counterexample
#print axioms Concrete.repaired_mass_left_at_beta_zero
#print axioms Concrete.repaired_mass_right_at_beta_zero
#print axioms Concrete.repaired_witness_dies_at_beta_zero
#print axioms Concrete.ao109_crossedMSE_vanishes_only_at_beta_zero
#print axioms Concrete.repaired_crossedMSE_vanishes_only_at_beta_three
#print axioms Concrete.addedRemovedAgain_shape_satisfiable_and_refutable
#print axioms Concrete.reduction_needs_added_nodup
#print axioms Concrete.timestamp_support_alone_is_not_the_inclusion
#print axioms residualPremises_eta_still_four_batch131
#print axioms censusRecordPremises_eta_still_five_batch131
#print axioms memoryRecordPremises_still_two_batch131
#print axioms consumed_capstone_and_alias_remain_frozen_batch131
#print axioms independent_exact_eleven_one_two_accounting_batch131
#print axioms released_builder_still_takes_hzero_batch131

end

end Nock.RedTeam.Batch131
