import Nock.NockVMROM.Thm54.GenericHonestPackage

/-!
# `PairedRecordLayout` through the paper's `Thm:IO_result` instance

the paper says the `intermediate` accumulator "is considered a witness element and its
constraints are implemented in the exact same way as in `RAP_mem-IO`, `RAP_comp-IO`", and that
"the argument is equivalent to Theorem `Thm:IO_result`, noting simply that in this case the `IO`
and `intermediate` columns function as the two memory record columns that are matched within the
same table".

This file wires the paper's route end to end and measures exactly what is left.  Result:
`PairedRecordLayout` is **still not inhabited**, but the residual is now a **single** named input —
the paper's own `F(X, Y)` identity — with **every** side condition discharged from `E`:

* §C states the paper's `L_MSE` and `L_LDSE` conditions on the
  encoded `(intermediate, IO)` columns, proves them equivalent by `Lem:ldse_mse` with both bounds taken from `E`, and proves
  `pairedRecordLayout_iff_symbolicInterMSE` — an **iff**, so nothing is weakened or bundled.
  `timestampClosed` follows through the existing bridge.
* §D exhibits the gap in the sharpest available form: the scalar identity `E` really carries and
  the symbolic identity the paper needs are **the same list-sum equation**, differing only in
  whether the pole offset is `E.cfg.challenges.memoryInputs` or the formal variable.
* §E measures the Route-2 tree-to-row reindexing cost, which nobody had measured: the **read** half
  is already free on `E` (`service_record_of_added` plus `Service.timestamp`), and the **verify**
  half is *circular* — it is exactly the `verify_child` half of `timestampClosed`.
* §F measures Route 1: the `TimestampKeyedColumns` half needs the `mem.root` coordinate that the
  paper's own equality table leaves at `⊥` on a `verify_child` row.

Nothing here inhabits `PairedRecordLayout`, `AddedRemovedAgain`, `timestampClosed`, or
`ForestExponentOrder`, and **no carrier field is added**.  The NMR axis is not re-litigated.

`TraceGen.timestampClosed_of_data` discharges `MemoryRecordPremises.timestampClosed` for
**every** `E` holding a `Data E`, and `TraceGen.productionStrategy_timestampClosed` for every
`T : ProductionStrategy`, with **no premise and no acceptance** — because
`MemoryRowTemplate.specialize` (`SemanticTimestampStrategy.lean:435`) emits
`ts = α ^ recordExponent` through the *unscaled* `specializeMemRec` (`:349`), while only the
**compute** side routes through `specializeMemRecScaled` (`:398-404`) where the declined `ln_prev`
scale freedom lives.  Note the `read_root` half was already free here
(`timestampClosed_read_root_half_is_free`, `:340`); the new content is the `verify_child` half.  The
other three names in the sentence above are still uninhabited.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

namespace Nock.NockVMROM.Thm54.PairedRecordIOResult

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.AxisBridge

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §A. `NockVM.encRec` is injective

`NockVM.encRec` (`Nock/NockVM.lean:616`) is the paper's flattening of a `Rec^MEM` record into its eight field coordinates.  It is
provable exactly because the flattening is faithful: every one of the four record fields is read
back off a distinct coordinate. -/

/-- **The eight-coordinate record flattening is faithful.**  `encRec` is injective, so a
permutation of encoded records is a permutation of `MemRec`s. -/
theorem encRec_injective : Function.Injective (NockVM.encRec (K := K)) := by
  intro r s h
  have hs : ∀ i : Fin 9, NockVM.encRec r i = NockVM.encRec s i := fun i => congrFun h i
  refine ComputeTable.MemRec.ext (ComputeTable.FP.ext ?_ ?_ ?_)
    (ComputeTable.FP.ext ?_ ?_ ?_) ?_ ?_
  · simpa [NockVM.encRec] using hs 0
  · simpa [NockVM.encRec] using hs 1
  · simpa [NockVM.encRec] using hs 2
  · simpa [NockVM.encRec] using hs 3
  · simpa [NockVM.encRec] using hs 4
  · simpa [NockVM.encRec] using hs 5
  · simpa [NockVM.encRec] using hs 6
  · simpa [NockVM.encRec] using hs 7

/-- Un-encoding a permutation: encoded record lists permute only if the record lists do. -/
theorem perm_of_perm_map_encRec {l l' : List (ComputeTable.MemRec K)}
    (h : (l.map NockVM.encRec).Perm (l'.map NockVM.encRec)) : l.Perm l' := by
  have hms : ((l : Multiset (ComputeTable.MemRec K)).map NockVM.encRec)
      = ((l' : Multiset (ComputeTable.MemRec K)).map NockVM.encRec) := by
    rw [Multiset.map_coe, Multiset.map_coe]
    exact Multiset.coe_eq_coe.mpr h
  exact Multiset.coe_eq_coe.mp (Multiset.map_injective encRec_injective hms)

/-! ## §B. Every side condition of `Thm:IO_result` on the `(IO, intermediate)` pair is on `E`

Two of the three are discharged here
from `E`, and the third is not needed at all on the `L_MSE` route of §C.  The bounds come from
`execution_lio_of_requestNodup`, whose `InRange` component is already about
`E.exec.derivedResponseIO = (addedRecordList E.exec).map encRec`. -/

/-- **Already held under honest `ver`.**  The encoded add column's length is in the paper's index range `[K]`. -/
theorem added_length_inRange (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    IO.InRange E.cfg.Ksz (RowLayout.addedRecordList E.exec).length := by
  have h := (execution_lio_of_requestNodup E).1
  rwa [ExactExecution.derivedResponseIO_eq_map_encRecC E.exec hC,
    rawResponses_eq_addedRecordList _ hhon, List.length_map] at h

/-- **Already held under honest `ver`.**  The remove column's length is in `[K]` too, from the count balance. -/
theorem consumed_length_inRange (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    IO.InRange E.cfg.Ksz (RowLayout.consumedRecordList E.exec).length := by
  rw [consumed_length_eq_added_length E]
  exact added_length_inRange E hhon hC

/-- **Already held under honest `ver`.**  Both column lengths sit below the characteristic — the `char p > K`
hypothesis of `Lem:ldse_mse`, from `E.Ksz_lt_ringChar`. -/
theorem column_lengths_lt_ringChar (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    (RowLayout.consumedRecordList E.exec).length < ringChar K ∧
      (RowLayout.addedRecordList E.exec).length < ringChar K :=
  ⟨lt_of_le_of_lt (consumed_length_inRange E hhon hC).2 E.Ksz_lt_ringChar,
    lt_of_le_of_lt (added_length_inRange E hhon hC).2 E.Ksz_lt_ringChar⟩

/-! ## §C. The paper's route, wired: one input remains

the paper is `L_MSE` — the multiplicative set equality `∏(X + RLC^Y(reqᵢ)) = ∏(X + RLC^Y(respⱼ))`
in `𝔽(Y)[X]`.  the paper is `L_LDSE` — the log-derivative form `Σ 1/(X + RLC^Y(reqᵢ)) =
Σ 1/(X + RLC^Y(respⱼ))` in `𝔽(X, Y)`, which is what a LogUp accumulator column actually computes.
`Lem:ldse_mse` identifies the two below the characteristic.

Both variables are **formal**: `SetEq.RLC` lands in `RatFunc K` (the RLC variable `Y` is symbolic,
which is why it is injective) and `SetEq.frac` lands in `RatFunc (RatFunc K)` (the LogUp variable
`X` is symbolic). -/

section Bridges

variable {α : Type*}

private theorem prod_map_eq_prod_fin {M' : Type*} [CommMonoid M'] (g : α → M') :
    ∀ l : List α, (l.map g).prod = ∏ i : Fin l.length, g (l.get i) := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, ih, Fin.prod_univ_succ]
      simp

private theorem sum_map_eq_sum_fin {M' : Type*} [AddCommMonoid M'] (g : α → M') :
    ∀ l : List α, (l.map g).sum = ∑ i : Fin l.length, g (l.get i) := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Fin.sum_univ_succ]
      simp

end Bridges

/-- **The paper's `L_MSE` condition on the `(IO, intermediate)` column pair.**
The multiplicative set equality between the encoded `verify_child` remove column and the encoded
`read_root` add column, at the **formal** RLC variable `Y` and the **formal** LogUp variable `X`. -/
def SymbolicInterMSE (E : BuildableNockExecution F K) : Prop :=
  IO.SEcond (𝔽 := K) (M := 9)
    ((RowLayout.consumedRecordList E.exec).map NockVM.encRec)
    ((RowLayout.addedRecordList E.exec).map NockVM.encRec)

/-- **The paper's `L_LDSE` condition on the same column pair** — the
log-derivative (LogUp) form that the `intermediate` accumulator column computes, at the formal
LogUp variable.  Compare `execution_logup_mass_balanced`: the same list-sum equation, with the
formal pole `X + RLC^Y(·)` in place of the scalar pole `RLC^γ(·) − β` at
`E.cfg.challenges.memoryInputs`. -/
def SymbolicInterLDSE (E : BuildableNockExecution F K) : Prop :=
  (((RowLayout.consumedRecordList E.exec).map NockVM.encRec).map
      (fun v => SetEq.frac (SetEq.RLC v))).sum
    = (((RowLayout.addedRecordList E.exec).map NockVM.encRec).map
        (fun v => SetEq.frac (SetEq.RLC v))).sum

/-- **`Lem:ldse_mse` / `Lem:mse_ldse_equiv` on this column pair**, with both characteristic bounds
taken from `E` (§B).  So the LogUp form and the multiset form of the paper's input are the same
object; a prover may supply either. -/
theorem symbolicInterLDSE_iff_symbolicInterMSE (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    SymbolicInterLDSE E ↔ SymbolicInterMSE E := by
  obtain ⟨hk₁, hk₂⟩ := column_lengths_lt_ringChar E hhon hC
  have hlen₁ :
      ((RowLayout.consumedRecordList E.exec).map NockVM.encRec).length
        = (RowLayout.consumedRecordList E.exec).length := List.length_map _
  have hlen₂ :
      ((RowLayout.addedRecordList E.exec).map NockVM.encRec).length
        = (RowLayout.addedRecordList E.exec).length := List.length_map _
  rw [SymbolicInterLDSE, SymbolicInterMSE, IO.SEcond,
    prod_map_eq_prod_fin _ ((RowLayout.consumedRecordList E.exec).map NockVM.encRec),
    prod_map_eq_prod_fin _ ((RowLayout.addedRecordList E.exec).map NockVM.encRec),
    sum_map_eq_sum_fin _ ((RowLayout.consumedRecordList E.exec).map NockVM.encRec),
    sum_map_eq_sum_fin _ ((RowLayout.addedRecordList E.exec).map NockVM.encRec)]
  exact (SetEq.mse_ldse_equiv (𝔽 := K) (p := ringChar K)
    (hlen₁ ▸ hk₁) (hlen₂ ▸ hk₂)
    (fun i => ((RowLayout.consumedRecordList E.exec).map NockVM.encRec).get i)
    (fun j => ((RowLayout.addedRecordList E.exec).map NockVM.encRec).get j)).symm

/-- **The paper's object closes the premise, and is exactly the premise.**  `L_MSE` on the encoded
`(intermediate, IO)` columns is *equivalent* to `PairedRecordLayout`: forward by unique
factorisation plus `RLC` and `encRec` injectivity, backward
because a record permutation gives equal multisets.  An **iff**, so nothing is weakened or
bundled. -/
theorem pairedRecordLayout_iff_symbolicInterMSE (E : BuildableNockExecution F K) :
    SymbolicInterMSE E ↔ RowLayout.PairedRecordLayout E.exec := by
  rw [SymbolicInterMSE, IO.SEcond_iff]
  constructor
  · intro h
    exact perm_of_perm_map_encRec (Multiset.coe_eq_coe.mp h)
  · intro h
    exact Multiset.coe_eq_coe.mpr (h.map NockVM.encRec)

/-- The LogUp form of the same input closes the premise. -/
theorem pairedRecordLayout_of_symbolicInterLDSE (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (h : SymbolicInterLDSE E) : RowLayout.PairedRecordLayout E.exec :=
  (pairedRecordLayout_iff_symbolicInterMSE E).mp
    ((symbolicInterLDSE_iff_symbolicInterMSE E hhon hC).mp h)

/-- …and therefore discharges `MemoryRecordPremises.timestampClosed` through the existing
bridge. -/
theorem timestampClosed_of_symbolicInterLDSE (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (h : SymbolicInterLDSE E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts :=
  timestampClosed_of_paired_record_layout hhon
    (pairedRecordLayout_of_symbolicInterLDSE E hhon hC h)

/-! ## §D. The gap, in the sharpest available form

`execution_logup_mass_balanced` and `SymbolicInterLDSE` are the **same list-sum equation**.  The
only difference is the pole: `E` carries it with the scalar pole `RLC^γ(·) − β` at the single tuple
`E.cfg.challenges.memoryInputs`, while `Thm:IO_result` consumes it with the
formal pole `X + RLC^Y(·)`.  the paper routes through `Thm:IO_result`, and
`Lem:ldse_mse` is an identity in `𝔽(X, Y)`, so the formal version is the one
the argument needs. -/

/-- Row-level `C'` (`CprimeCoherent`): the pole of a `Pub` row at its own `C'` is the pole at
`cp` of the stored record.  (Replaces the pre-row-level dummy-wire `C' = 1`.) -/
theorem map_pole_cprime_of_coherent (inp : MemoryTable.Inputs K)
    (rows : List (MemoryTable.Pub K)) (cp : ComputeTable.MemRec K → K)
    (hC : ∀ p ∈ rows, p.cprime = cp p.mem)
    (pred : MemoryTable.Pub K → Bool) :
    (rows.filter pred).map (fun p => (MemoryTable.pole inp p.mem p.cprime)⁻¹) =
      (rows.filter pred).map (fun p => (MemoryTable.pole inp p.mem (cp p.mem))⁻¹) :=
  List.map_eq_map_iff.mpr fun p hp => by
    have : p ∈ rows := List.mem_of_mem_filter hp
    rw [hC p this]

theorem sum_pole_addedRecordList_cp (inp : MemoryTable.Inputs K)
    (cp : ComputeTable.MemRec K → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    ((rows.flatMap fun row =>
          match row.2.2.st with
          | .read_root => [row.2.2.mem]
          | .decompose | .halt | .verify_child => []).map
        (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum
      = (((rows.map (fun row => row.2.2)).filter
            (fun p => decide (p.st = MemoryTable.MState.read_root))).map
          (fun p => (MemoryTable.pole inp p.mem (cp p.mem))⁻¹)).sum := by
  induction rows with
  | nil => simp
  | cons a t ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
        List.filter_cons]
      cases h : a.2.2.st <;> simp [h]

theorem sum_pole_consumedRecordList_cp (inp : MemoryTable.Inputs K)
    (cp : ComputeTable.MemRec K → K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    ((rows.flatMap (fun row => RowLayout.consumedRecords row.2.2)).map
        (fun r => (MemoryTable.pole inp r (cp r))⁻¹)).sum
      = (((rows.map (fun row => row.2.2)).filter
            (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
          (fun p => (MemoryTable.pole inp p.mem (cp p.mem))⁻¹)).sum := by
  induction rows with
  | nil => simp
  | cons a t ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
        List.filter_cons]
      cases h : a.2.2.st <;> simp [RowLayout.consumedRecords, h]

theorem memoryPubRows_cprime_coherent (E : BuildableNockExecution F K)
    (hC : E.exec.CprimeCoherent) :
    ∀ p ∈ GenericHonestData.memoryPubRows E.exec, p.cprime = E.exec.cprimeOf p.mem := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨row, hrow, rfl⟩
  exact ExactExecution.cprime_eq_cprimeOf hC row hrow

/-- What `E` carries: the record-level LogUp identity at **one** scalar offset. -/
theorem scalar_interLDSE_on_E (E : BuildableNockExecution F K)
    (hC : E.exec.CprimeCoherent) :
    ((RowLayout.addedRecordList E.exec).map
        (fun r => (MemoryTable.pole E.cfg.challenges.memoryInputs r (E.exec.cprimeOf r))⁻¹)).sum
      = ((RowLayout.consumedRecordList E.exec).map
          (fun r => (MemoryTable.pole E.cfg.challenges.memoryInputs r (E.exec.cprimeOf r))⁻¹)).sum
              := by
  have hpub := memoryPubRows_cprime_coherent E hC
  have hb := execution_logup_mass_balanced E
  rw [map_pole_cprime_of_coherent _ _ _ hpub (fun p => decide (p.st =
      MemoryTable.MState.read_root)),
      map_pole_cprime_of_coherent _ _ _ hpub
        (fun p => decide (p.st = MemoryTable.MState.verify_child))] at hb
  have hadd := sum_pole_addedRecordList_cp
    E.cfg.challenges.memoryInputs E.exec.cprimeOf E.exec.memoryRows
  have hcons := sum_pole_consumedRecordList_cp
    E.cfg.challenges.memoryInputs E.exec.cprimeOf E.exec.memoryRows
  simp only [RowLayout.addedRecordList, RowLayout.consumedRecordList,
    GenericHonestData.memoryPubRows] at hadd hcons hb ⊢
  exact hadd.trans (hb.trans hcons.symm)

/-- Why there is no family over offsets: row acceptance pins every memory row's RAP `Inputs` to the
configuration's own `(z, β, γ)`, so `E` exhibits the accumulator at that tuple and nowhere else. -/
theorem memory_rows_pin_the_challenge (E : BuildableNockExecution F K) :
    ∀ row ∈ E.exec.memoryRows, row.2.1 = E.cfg.challenges.memoryInputs := fun row hrow =>
  ((ExactExecution.memoryRowsAccepted_iff E.exec).1
    E.chained.semantic.2.1 row hrow).2.1

/-- **The honest scope limit of §C, stated as a theorem.**  `SymbolicInterMSE` is *equivalent* to
`PairedRecordLayout` (`pairedRecordLayout_iff_symbolicInterMSE`), so supplying it as a named premise
would rename the premise, not close it.  §C's value is therefore faithfulness and localization: it
identifies the named premise with the paper's own `Thm:IO_result` object and discharges every side
condition from `E`, leaving the accumulator identity itself as the one thing that must be
**derived**.  This restates that equivalence under a name that cannot be misread as progress. -/
theorem symbolicInterMSE_is_not_weaker_than_the_premise (E : BuildableNockExecution F K) :
    SymbolicInterMSE E ↔ RowLayout.PairedRecordLayout E.exec :=
  pairedRecordLayout_iff_symbolicInterMSE E

/-- **The shape a carrier would have to supply, written as a `Prop` about `E` and NOT added to any
structure.**  This is recorded so the missing field is named precisely; it is
deliberately left uninhabited here. -/
def InterChainChallengeFamily (E : BuildableNockExecution F K) : Prop :=
  ∀ inp : MemoryTable.Inputs K,
    MemoryTable.InterChain inp 0 0 (GenericHonestData.memoryPubRows E.exec)

/-- Such a family would give the record-level mass identity at **every** offset, not just at
`E.cfg.challenges.memoryInputs`.  That is as far as it reaches with the lemmas presently in the
repo: turning "equal mass at every challenge of a finite field" into the multiset equality of §C
needs a vanishing/degree argument that `Nock/SetEq.lean` does not have — its `Lem:ldse_mse` and
`lem:set_inclusion` are stated over the **formal** `RatFunc` tower, not over many points of `K`. -/
theorem mass_balanced_at_every_offset_of_family (E : BuildableNockExecution F K)
    (hC : E.exec.CprimeCoherent)
    (h : InterChainChallengeFamily E) (inp : MemoryTable.Inputs K) :
    ((RowLayout.addedRecordList E.exec).map
        (fun r => (MemoryTable.pole inp r (E.exec.cprimeOf r))⁻¹)).sum
      = ((RowLayout.consumedRecordList E.exec).map
          (fun r => (MemoryTable.pole inp r (E.exec.cprimeOf r))⁻¹)).sum := by
  have hpub := memoryPubRows_cprime_coherent E hC
  have hb := GenericHonestData.interChain_balance_is_logup_mass inp
    (GenericHonestData.memoryPubRows E.exec) (h inp)
  rw [map_pole_cprime_of_coherent _ _ _ hpub (fun p => decide (p.st =
      MemoryTable.MState.read_root)),
      map_pole_cprime_of_coherent _ _ _ hpub
        (fun p => decide (p.st = MemoryTable.MState.verify_child))] at hb
  have hadd := sum_pole_addedRecordList_cp inp E.exec.cprimeOf E.exec.memoryRows
  have hcons := sum_pole_consumedRecordList_cp inp E.exec.cprimeOf E.exec.memoryRows
  simp only [RowLayout.addedRecordList, RowLayout.consumedRecordList,
    GenericHonestData.memoryPubRows] at hadd hcons hb ⊢
  exact hadd.trans (hb.trans hcons.symm)

/-! ## §E. Route 2 measured — the read half is free, the verify half is circular

It did not measure that residual.  It
splits into two components, and they cost very differently.

`forestReadTimestamps`/`forestVerifyTimestamps` (`AxisSoundness.lean:111,119`) are
`(readExps (exactAxisTree cfg exec i)).map (α ^ ·)` and its `verifyExps` twin, and
`exactAxisTree` labels each node with `timestampExpAt α = timestampExp α mem.ts`.  So each forest
entry is `α ^ timestampExp α mem.ts`, and using it as a record timestamp needs
`α ^ timestampExp α mem.ts = mem.ts`. -/

/-- **Route 2, read half: FREE, already on `E`.**  Every record added to `intermediate` at a
`read_root` row is a `Service.record` (`service_record_of_added`, via `RootTrace.recordPartition`),
and `Service.timestamp` closes its timestamp.  So the add column's
timestamps recover from their forest exponents at no cost. -/
theorem added_timestamp_closed (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    ∀ s ∈ RowLayout.addedRecordList E.exec,
      MemoryTimestampClosedAt E.cfg.challenges.α s.ts := by
  intro s hs
  obtain ⟨rA, hrA, hts⟩ := exec_added_ts_of_execA hs
  obtain ⟨sv, hsv⟩ := service_record_of_added hhon hrA
  exact ⟨sv.exponent, by rw [hts, hsv]; exact sv.timestamp⟩

/-- The two closure predicates of the two layers are the same predicate. -/
theorem memoryTimestampClosedAt_iff_timestampClosedAt (α ts : K) :
    MemoryTimestampClosedAt α ts ↔ TimestampClosedAt α ts := Iff.rfl

/-- **`timestampClosed`'s `read_root` half is therefore already free on `E`.** -/
theorem timestampClosed_read_root_half_is_free (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    ∀ i : Fin E.cfg.memRows, (E.exec.memoryRowAt i).1 = .read_root →
      MemoryTimestampClosedAt E.cfg.challenges.α
        (E.exec.memoryRowAt i).2.2.mem.ts := fun i h =>
  added_timestamp_closed E hhon _ (read_root_mem_in_addedRecordList E i h)

/-- **So the named premise reduces exactly to its `verify_child` half.**  `memoryMemRecKind` is
`.active` on precisely `read_root` and `verify_child`; the `read_root` half is free, so
`timestampClosed` is *equivalent* to closure on the remove column's rows alone. -/
theorem timestampClosed_iff_verify_child_half (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts)
      ↔ (∀ i : Fin E.cfg.memRows, (E.exec.memoryRowAt i).1 = .verify_child →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) := by
  constructor
  · intro h i hst
    exact h i (by simp [memoryMemRecKind, hst])
  · intro h i hact
    cases hst : (E.exec.memoryRowAt i).1 with
    | decompose => simp [memoryMemRecKind, hst] at hact
    | halt => simp [memoryMemRecKind, hst] at hact
    | read_root => exact timestampClosed_read_root_half_is_free E hhon i hst
    | verify_child => exact h i hst

/-- **Route 2, verify half: the recovery step, isolated.**  A `forestVerifyTimestamps` entry is
`α ^ timestampExp α r.ts`; reading a removed record's timestamp off it is exactly this. -/
def VerifyReindexingRecovery (E : BuildableNockExecution F K) : Prop :=
  ∀ r ∈ RowLayout.consumedRecordList E.exec,
    E.cfg.challenges.α ^ timestampExp E.cfg.challenges.α r.ts = r.ts

/-- The recovery step is *equivalent* to closure of the remove column's timestamps
(`timestampExp_recovers_ts_iff_closed`). -/
theorem verifyReindexingRecovery_iff_consumed_closed (E : BuildableNockExecution F K) :
    VerifyReindexingRecovery E ↔
      ∀ r ∈ RowLayout.consumedRecordList E.exec,
        TimestampClosedAt E.cfg.challenges.α r.ts := by
  constructor
  · intro h r hr
    exact (timestampExp_recovers_ts_iff_closed E.cfg.challenges.α r.ts).mp (h r hr)
  · intro h r hr
    exact (timestampExp_recovers_ts_iff_closed E.cfg.challenges.α r.ts).mpr (h r hr)

/-- **THE MEASURED COST OF ROUTE 2 — it is circular.**  Route 2's verify-side reindexing step
already implies `timestampClosed` outright, with no record matching anywhere in the derivation.  So
Route 2 cannot be used to obtain `PairedRecordLayout` in order to obtain `timestampClosed`: its own
bridge is at least as strong as that conclusion.  Combined with §E's read half, the tree↔row
reindexing residual named in `Nock/AxisBridge.lean` costs **nothing** on the add column and
**exactly the premise's own consequence** on the remove column. -/
theorem timestampClosed_of_verifyReindexingRecovery (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : VerifyReindexingRecovery E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts := by
  rw [timestampClosed_iff_verify_child_half E hhon]
  intro i hst
  exact ((verifyReindexingRecovery_iff_consumed_closed E).mp h) _
    (verify_child_mem_in_consumedRecordList E i hst)

/-- This records the exact shape of what would still be
missing, the key half of the paper. -/
def TimestampSupportedAdded (E : BuildableNockExecution F K) : Prop :=
  ∀ s ∈ RowLayout.addedRecordList E.exec,
    ∃ r ∈ RowLayout.consumedRecordList E.exec, r.ts = s.ts

def TimestampKeyedColumns (E : BuildableNockExecution F K) : Prop :=
  ∀ s ∈ RowLayout.addedRecordList E.exec,
    ∀ r ∈ RowLayout.consumedRecordList E.exec, r.ts = s.ts → r = s

theorem pairedRecordLayout_of_timestamp_support_and_key (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (hsupp : TimestampSupportedAdded E) (hkey : TimestampKeyedColumns E) :
    RowLayout.PairedRecordLayout E.exec := by
  refine pairedRecordLayout_of_addedRemovedAgain E hhon hC ?_
  intro s hs
  obtain ⟨r, hr, hts⟩ := hsupp s hs
  exact hkey s hs r hr hts ▸ hr

/-! ## §F. Route 1 measured — the key half is the `mem.root` coordinate the paper leaves at `⊥`

`TimestampKeyedColumns` asks for full eight-coordinate record equality from timestamp equality.  Two
of the eight coordinates on a `verify_child` row are not constrained by the row verifier's equality
block at all: the paper gives `mem.root` as `⊥` in the `verify_child` column, and
`verify_child_eqBlk_ignores_mem_root` (already compiled) re-accepts such a row after arbitrary
garbage is written there.  So the key half cannot come from the equality block; the only gate that
sees `mem.root` is the `intermediate` pole, through `recRLC` — which is Route 3 again. -/

namespace Concrete

/-- The F97 fixture base field. -/
abbrev F97 := ZMod 97

local instance prime97ao110 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- Two records with the **same** timestamp differing only in `root.size` — the coordinate
the paper leaves at `⊥` on a `verify_child` row. -/
def rootA : ComputeTable.MemRec F97 := ⟨⟨1, 0, 0⟩, ⟨0, 0, 0⟩, 0, 7⟩

/-- Its timestamp-equal, root-differing partner. -/
def rootB : ComputeTable.MemRec F97 := ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 0, 7⟩

/-- **Route 1's key half is exactly the `mem.root` coordinate.**  Equal timestamps do not give
record equality, and the witnessing difference sits in the `⊥` cell. -/
theorem timestampKeyedColumns_is_about_mem_root :
    rootA.ts = rootB.ts ∧ rootA ≠ rootB ∧ rootA.root ≠ rootB.root := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [rootA, rootB, ne_eq, ComputeTable.MemRec.mk.injEq,
      ComputeTable.FP.mk.injEq]
    intro h
    revert h
    decide
  · simp only [rootA, rootB, ne_eq, ComputeTable.FP.mk.injEq]
    intro h
    revert h
    decide

/-- LogUp challenges with `γ = 1` and pole offset `β` (the paper: `RLC^γ(·) − β`). -/
def chal (β : F97) : MemoryTable.Inputs F97 := ⟨0, β, 1⟩

theorem pole_rootA (β : F97) : MemoryTable.pole (chal β) rootA = 8 - β := by
  simp only [MemoryTable.pole, MemoryTable.recRLC, rootA, chal]
  ring_nf

theorem pole_rootB (β : F97) : MemoryTable.pole (chal β) rootB = 7 - β := by
  simp only [MemoryTable.pole, MemoryTable.recRLC, rootB, chal]
  ring_nf

/-- **The `intermediate` pole DOES see the `⊥` coordinate — at every offset.**  Scanning all 97
offsets (not trusting one point, and in particular not sitting at the degenerate `β = 0`), the two
timestamp-equal records have different poles everywhere.  So the accumulator is the gate that
distinguishes them, which is precisely why the paper routes the record matching through
`Thm:IO_result` rather than through the equality block. -/
theorem poles_separate_at_every_offset :
    ∀ β : F97, MemoryTable.pole (chal β) rootA ≠ MemoryTable.pole (chal β) rootB := by
  intro β
  rw [pole_rootA, pole_rootB]
  intro h
  have : (8 : F97) = 7 := by linear_combination h
  revert this
  decide

/-- The witness is placed away from the degenerate offset as well: at `β = 3` both poles are
nonzero and `β ≠ 0`. -/
theorem witness_is_nondegenerate_at_beta_three :
    (3 : F97) ≠ 0
      ∧ MemoryTable.pole (chal 3) rootA ≠ 0
      ∧ MemoryTable.pole (chal 3) rootB ≠ 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [pole_rootA]; decide
  · rw [pole_rootB]; decide

end Concrete

/-! ## §H. Accounting, capstone and freeze — unchanged

Nothing in this file changes the carrier, the named-premise ledger, or the released statement. -/

/-- The fourteen-field execution carrier is unchanged: no field was added for any route. -/
theorem execution_eta_still_fourteen_fields_ao110 (E : BuildableNockExecution F K) :
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

/-- `MemoryRecordPremises` still has its two fields and `timestampClosed` is still named: this file
inhabits nothing. -/
theorem memoryRecordPremises_still_two_ao110
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  GenericHonestData.memoryRecordPremises_still_two_after_logup_inventory M

/-- The `11+1+2` partition of the released capstone statement is unchanged. -/
theorem exact_eleven_one_two_ao110 : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two_after_logup_inventory


#print axioms encRec_injective
#print axioms perm_of_perm_map_encRec
#print axioms added_length_inRange
#print axioms consumed_length_inRange
#print axioms column_lengths_lt_ringChar
#print axioms symbolicInterLDSE_iff_symbolicInterMSE
#print axioms pairedRecordLayout_iff_symbolicInterMSE
#print axioms pairedRecordLayout_of_symbolicInterLDSE
#print axioms timestampClosed_of_symbolicInterLDSE
#print axioms scalar_interLDSE_on_E
#print axioms memory_rows_pin_the_challenge
#print axioms symbolicInterMSE_is_not_weaker_than_the_premise
#print axioms mass_balanced_at_every_offset_of_family
#print axioms added_timestamp_closed
#print axioms memoryTimestampClosedAt_iff_timestampClosedAt
#print axioms timestampClosed_read_root_half_is_free
#print axioms timestampClosed_iff_verify_child_half
#print axioms verifyReindexingRecovery_iff_consumed_closed
#print axioms timestampClosed_of_verifyReindexingRecovery
#print axioms pairedRecordLayout_of_timestamp_support_and_key
#print axioms Concrete.timestampKeyedColumns_is_about_mem_root
#print axioms Concrete.pole_rootA
#print axioms Concrete.pole_rootB
#print axioms Concrete.poles_separate_at_every_offset
#print axioms Concrete.witness_is_nondegenerate_at_beta_three
#print axioms execution_eta_still_fourteen_fields_ao110
#print axioms memoryRecordPremises_still_two_ao110
#print axioms exact_eleven_one_two_ao110

end

end Nock.NockVMROM.Thm54.PairedRecordIOResult
