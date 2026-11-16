import Nock.NockVMROM.Thm54.SemanticStrategy
import Nock.NockVMROM.Thm54.NodeEncoding

/-!
# Staged semantic timestamp specialization

`SemanticTimestampSkeleton` is the timestamp/noun topology committed before the timestamp
challenge `α` is sampled.  The production staged strategy additionally commits the complete
configuration and execution templates after `z`, so no carrier field can be selected after the
full joint coin.

The production `ExactExecution` carrier stores `ln_prev`, `ln`, and every table timestamp directly
in `K`.  The templates below split those columns from all unchanged configuration/row data,
materialize them at sampled `α`, recursively relabel the tree/forest, and transport the dependent
carrier geometry.  Recursive `SemanticStrategy.BindsAt` and both semantic-record bridge equations
are constructed from α-free template consistency.  The separate regenerated-label obligation
records the polynomial/counting work required before reusing sampled `alphaM` in the memory walk.
-/

namespace Nock.NockVMROM.Thm54.SemanticTimestampStrategy

open scoped Classical
open Nock Nock.Walk
open Nock.Framework.Thm54

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## The α-free commitment -/

/-- Natural exponents attached to one canonical compute row. -/
structure ComputeTimestampRow where
  state : ComputeTable.State
  lnPrevExponent : ℕ
  lnExponent : ℕ
  recordExponent : Fin 3 → ℕ

/-- Natural exponents attached to one canonical memory row.  Padding rows retain a canonical
natural exponent, although specialization forces their actual table record to be zero. -/
structure MemoryTimestampRow where
  state : MemoryTable.MState
  recordExponent : ℕ

/-- Adjacent compute rows hand the line exponent to the next row. -/
def ComputeLineExponentChain : List ComputeTimestampRow → Prop
  | [] => True
  | [_] => True
  | left :: right :: rest =>
      left.lnExponent = right.lnPrevExponent ∧
        ComputeLineExponentChain (right :: rest)

/-- The first canonical compute line starts at exponent zero. -/
def ComputeLineStartsAtZero : List ComputeTimestampRow → Prop
  | [] => False
  | row :: _ => row.lnPrevExponent = 0

/-- One α-free description of a canonical semantic memory-record occurrence. -/
structure CanonicalRecordSlot where
  record : SemanticStrategy.MemRecSkeleton
  exponent : ℕ

/-- The complete α-free timestamp commitment over a fixed noun/topology skeleton.

There is deliberately no element named `α`, no `K`-valued line or timestamp, no power, no
`bridgeRecords`, and no existential noun decoder in this structure. -/
structure SemanticTimestampSkeleton
    (F K : Type) [Field F] [Field K] [Algebra F K]
    (base : SemanticStrategy.SemanticSkeleton) where
  computeRows : List ComputeTimestampRow
  memoryRows : List MemoryTimestampRow
  semanticRequests : List CanonicalRecordSlot
  semanticResponses : List CanonicalRecordSlot
  computeTopology :
    List.Forall₂
      (fun row stamp => stamp.state = row.state)
      (SemanticStrategy.computeSkeletonRows base) computeRows
  memoryTopology :
    List.Forall₂
      (fun row stamp => stamp.state = row.state)
      (SemanticStrategy.memorySkeletonRows base) memoryRows
  computeStartsAtZero : ComputeLineStartsAtZero computeRows
  computeLineChain : ComputeLineExponentChain computeRows
  computeLineAdvance :
    ∀ stamp ∈ computeRows,
      stamp.lnExponent =
        stamp.lnPrevExponent + Nock.Framework.recordCount stamp.state
  computeRecordOffsets :
    ∀ stamp ∈ computeRows, ∀ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount stamp.state →
        stamp.recordExponent i = stamp.lnPrevExponent + (i : ℕ) + 1
  requestTopology :
    semanticRequests =
      (let paired :=
        (SemanticStrategy.computeSkeletonRows base).zip computeRows
       paired.flatMap fun pair =>
        (List.ofFn fun i : Fin 3 =>
          if h : (i : ℕ) < Nock.Framework.recordCount pair.1.state then
            some
              ({ record := pair.1.memoryRecord i h
                 exponent := pair.2.recordExponent i } : CanonicalRecordSlot)
          else none).filterMap id)
  responseTopology :
    semanticResponses =
      (let paired :=
        (SemanticStrategy.memorySkeletonRows base).zip memoryRows
       paired.filterMap fun pair =>
        if h : pair.1.state = .read_root then
          some
            ({ record := pair.1.memoryRecord (by simp [memoryMemRecKind, h])
               exponent := pair.2.recordExponent } : CanonicalRecordSlot)
        else none)

namespace SemanticTimestampSkeleton

/-- Realize one seed-independent noun/Nat slot as a semantic NMR record after `z` is sampled. -/
def semanticRecordAt (z : K) (slot : CanonicalRecordSlot) :
    (nmrMEF F K).Rec :=
  let root := GlobalCarryRecognizer.enc z slot.record.root
  let child := GlobalCarryRecognizer.enc z slot.record.child
  ((slot.record.axis : F),
    (((root.size, root.dyck, root.leaf),
      (child.size, child.dyck, child.leaf)),
      slot.exponent))

/-- The concrete table record computed from the same noun/Nat slot at `(z, α)`. -/
def tableRecordAt (z α : K) (slot : CanonicalRecordSlot) :
    ComputeTable.MemRec K where
  root := GlobalCarryRecognizer.enc z slot.record.root
  child := GlobalCarryRecognizer.enc z slot.record.child
  axis := (slot.record.axis : K)
  ts := α ^ slot.exponent

/-- RecordBridge is definitionally the encoding of the concretely specialized noun slot. -/
theorem bridge_semanticRecordAt
    (z α lmb : K) (slot : CanonicalRecordSlot) :
    bridge F K α lmb (semanticRecordAt (F := F) z slot) =
      NockVM.encRecFormR (tableRecordAt z α slot) lmb := by
  unfold bridge
  congr 1
  apply ComputeTable.MemRec.ext <;>
    simp [semanticRecordAt, tableRecordAt, memRecOfNMR, nmrEncoding, GlobalCarryRecognizer.enc]

/-- A noun-backed table record is nonzero at every nonzero NPR seed, independently of `α`. -/
theorem tableRecordAt_ne_zero
    {z : K} (hz : z ≠ 0) (α : K) (slot : CanonicalRecordSlot) :
    tableRecordAt z α slot ≠ ComputeTable.MemRec.zero := by
  intro h
  have hroot := congrArg ComputeTable.MemRec.root h
  have hsize := congrArg ComputeTable.FP.size hroot
  simp [tableRecordAt, ComputeTable.MemRec.zero,
    GlobalCarryRecognizer.enc_size, hz] at hsize

/-- `BindMemRec` plus the specialized timestamp identifies the complete concrete record. -/
theorem tableRecordAt_eq_of_bind
    {z α : K} {slot : CanonicalRecordSlot}
    {record : ComputeTable.MemRec K}
    (hbind : SemanticStrategy.BindMemRec z slot.record record)
    (htime : record.ts = α ^ slot.exponent) :
    tableRecordAt z α slot = record := by
  apply ComputeTable.MemRec.ext
  · exact hbind.1.symm
  · exact hbind.2.1.symm
  · exact hbind.2.2.symm
  · exact htime.symm

/-- Semantic request records computed from noun slots at the sampled NPR seed. -/
def semanticRequestsAt
    {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) (z : K) :
    List ((nmrMEF F K).Rec) :=
  S.semanticRequests.map (semanticRecordAt (F := F) z)

/-- Semantic response records computed from noun slots at the sampled NPR seed. -/
def semanticResponsesAt
    {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) (z : K) :
    List ((nmrMEF F K).Rec) :=
  S.semanticResponses.map (semanticRecordAt (F := F) z)

/-- Canonical active compute-record slots, in BFS row order and then `mr1,mr2,mr3` order. -/
def canonicalRequestSlots
    {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) : List CanonicalRecordSlot :=
  let paired := (SemanticStrategy.computeSkeletonRows base).zip S.computeRows
  paired.flatMap fun pair =>
    (List.ofFn fun i : Fin 3 =>
      if h : (i : ℕ) < Nock.Framework.recordCount pair.1.state then
        some
          ({ record := pair.1.memoryRecord i h
             exponent := pair.2.recordExponent i } : CanonicalRecordSlot)
      else none).filterMap id

/-- Canonical externally served memory slots: exactly `read_root`, in BFS order. -/
def canonicalResponseSlots
    {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) : List CanonicalRecordSlot :=
  let paired := (SemanticStrategy.memorySkeletonRows base).zip S.memoryRows
  paired.filterMap fun pair =>
    if h : pair.1.state = .read_root then
      some
        ({ record := pair.1.memoryRecord (by simp [memoryMemRecKind, h])
           exponent := pair.2.recordExponent } : CanonicalRecordSlot)
    else none

/-- The dependent topology proof fixes the compute exponent list length and row indexing. -/
theorem computeRows_length
    {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) :
    S.computeRows.length =
      (SemanticStrategy.computeSkeletonRows base).length :=
  S.computeTopology.length_eq.symm

/-- The dependent topology proof fixes the memory exponent list length and row indexing. -/
theorem memoryRows_length
    {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) :
    S.memoryRows.length =
      (SemanticStrategy.memorySkeletonRows base).length :=
  S.memoryTopology.length_eq.symm

/-- Semantic request multiplicity and order are exactly those of the canonical active slots. -/
theorem semanticRequests_length
    {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) :
    S.semanticRequests.length = S.canonicalRequestSlots.length := by
  exact congrArg List.length S.requestTopology

/-- Semantic response multiplicity and order are exactly those of canonical `read_root` slots. -/
theorem semanticResponses_length
    {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) :
    S.semanticResponses.length = S.canonicalResponseSlots.length := by
  exact congrArg List.length S.responseTopology

end SemanticTimestampSkeleton

/-! ## Canonical row-local semantic record extraction -/

/-- Active compute slots for one aligned skeleton/timestamp row. -/
def computeRowRecordSlots
    (row : SemanticStrategy.ComputeRowSkeleton)
    (stamp : ComputeTimestampRow) : List CanonicalRecordSlot :=
  (List.ofFn fun i : Fin 3 =>
    if h : (i : ℕ) < Nock.Framework.recordCount row.state then
      some
        ({ record := row.memoryRecord i h
           exponent := stamp.recordExponent i } : CanonicalRecordSlot)
    else none).filterMap id

/-- Externally served memory slot for one aligned skeleton/timestamp row. -/
def memoryRowResponseSlots
    (row : SemanticStrategy.MemoryRowSkeleton)
    (stamp : MemoryTimestampRow) : List CanonicalRecordSlot :=
  if h : row.state = .read_root then
    [({ record := row.memoryRecord (by simp [memoryMemRecKind, h])
        exponent := stamp.recordExponent } : CanonicalRecordSlot)]
  else []

/-! ## Concrete α-free configuration and carrier templates -/

/-- All table challenges except the timestamp challenge. -/
structure ChallengeVectorTemplate (K : Type*) where
  a : K
  b : K
  c : K
  z : K
  β : K
  γ : K

namespace ChallengeVectorTemplate

/-- Insert the two sampled challenges of the same round: the timestamp challenge `α` and the
Form R challenge `λ` (`lmb`). -/
def specialize (v : ChallengeVectorTemplate K) (α lmb : K) : ChallengeVector K where
  a := v.a
  b := v.b
  c := v.c
  α := α
  z := v.z
  β := v.β
  γ := v.γ
  lam := lmb

omit [Field K] in
@[simp] theorem specialize_alpha (v : ChallengeVectorTemplate K) (α lmb : K) :
    (v.specialize α lmb).α = α := rfl

omit [Field K] in
@[simp] theorem specialize_z (v : ChallengeVectorTemplate K) (α lmb : K) :
    (v.specialize α lmb).z = v.z := rfl

omit [Field K] in
@[simp] theorem specialize_lam (v : ChallengeVectorTemplate K) (α lmb : K) :
    (v.specialize α lmb).lam = lmb := rfl

end ChallengeVectorTemplate

/-- The complete α-free part of `ExactConfig`.  Geometry and its proofs are copied verbatim;
only `ChallengeVector.α` is absent. -/
structure ExactConfigTemplate (F K : Type*) [Field F] [Field K] [Algebra F K] where
  challenges : ChallengeVectorTemplate K
  Ksz : ℕ
  kMem : ℕ
  orbit : OrbitDomain K
  orbit_h_pos : 1 ≤ orbit.h
  compRows : ℕ
  memRows : ℕ
  compRows_pos : 0 < compRows
  memRows_pos : 0 < memRows
  compRows_le : compRows ≤ 2 ^ orbit.h
  memRows_le : memRows ≤ 2 ^ orbit.h
  eDeg : ℕ
  eDeg_eq_one : eDeg = 1
  compNodes : Fin compRows → K
  compNodes_spec :
    ∀ i, compNodes i = orbit.βcoset * orbit.ω ^ (i : ℕ)
  memNodes : Fin memRows → K
  memNodes_spec :
    ∀ i, memNodes i = orbit.βcoset * orbit.ω ^ (i : ℕ)

namespace ExactConfigTemplate

/-- Insert the sampled `(α, λ)` without changing any exact-domain geometry. -/
def specialize (T : ExactConfigTemplate F K) (α lmb : K) : ExactConfig F K where
  challenges := T.challenges.specialize α lmb
  Ksz := T.Ksz
  kMem := T.kMem
  orbit := T.orbit
  orbit_h_pos := T.orbit_h_pos
  compRows := T.compRows
  memRows := T.memRows
  compRows_pos := T.compRows_pos
  memRows_pos := T.memRows_pos
  compRows_le := T.compRows_le
  memRows_le := T.memRows_le
  eDeg := T.eDeg
  eDeg_eq_one := T.eDeg_eq_one
  compNodes := T.compNodes
  compNodes_spec := T.compNodes_spec
  memNodes := T.memNodes
  memNodes_spec := T.memNodes_spec

@[simp] theorem specialize_alpha (T : ExactConfigTemplate F K) (α lmb : K) :
    (T.specialize α lmb).challenges.α = α := rfl

@[simp] theorem specialize_z (T : ExactConfigTemplate F K) (α lmb : K) :
    (T.specialize α lmb).challenges.z = T.challenges.z := rfl

@[simp] theorem specialize_lam (T : ExactConfigTemplate F K) (α lmb : K) :
    (T.specialize α lmb).challenges.lam = lmb := rfl

end ExactConfigTemplate

/-- Replace only a memory record's timestamp when its slot is active; padding is reconstructed as
the exact production zero record.  `origin = 1` recovers the paper's honest closed form
`α^exponent`. -/
def specializeMemRec (α : K) (active : Bool) (exponent : ℕ)
    (record : ComputeTable.MemRec K) : ComputeTable.MemRec K :=
  if active then { record with ts := α ^ exponent }
  else ComputeTable.MemRec.zero

/-- Compute-table origin of one placeholder row: the α-free scalar such that
`ln_prev = origin * α^lnPrevExponent` at the placeholder's own `α`.  At exponent
zero this is just the published `ln_prev`, with no division.  Honest traces
(`ln_prev = α^e`) have `origin = 1` and recover `specializeMemRec`. -/
def computeLineOrigin (α ln_prev : K) (e : ℕ) : K :=
  match e with
  | 0 => ln_prev
  | Nat.succ _ => ln_prev / α ^ e

/-- Active compute-record timestamp scaled from a published line origin. -/
def specializeMemRecScaled (α origin : K) (active : Bool) (exponent : ℕ)
    (record : ComputeTable.MemRec K) : ComputeTable.MemRec K :=
  if active then { record with ts := origin * α ^ exponent }
  else ComputeTable.MemRec.zero

/-- Seed-time placeholder row plus the Nat metadata that replaces every ignored α-dependent
column.  The placeholder's old `Inputs.α`, line values, and timestamps are never read by
specialization. -/
structure ComputeRowTemplate where
  timestamp : ComputeTimestampRow
  placeholder : ComputeTable.State × ComputeTable.DTcomp K

/-- Seed-time placeholder memory row plus its Nat timestamp metadata. -/
structure MemoryRowTemplate where
  timestamp : MemoryTimestampRow
  placeholder : MemoryTable.MState × MemoryTable.DTmem K

namespace ComputeRowTemplate

/-- Materialize one compute row at `α`.  Line and record timestamps are
relative to the placeholder's α-free origin (`computeLineOrigin`):
`ln_prev = origin * α^e`, `ln = ln_prev * α^(lnExp-e)`,
`ts = ln_prev * α^(recExp-e)`.  When origin is `1` and exponents are
the honest ladder (`e ≤ lnExp`, `e ≤ recExp`) this is the previous
`α^e` overwrite.  `V_comp` never pins the origin. -/
def specialize (T : ComputeRowTemplate (K := K)) (α : K) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  let pub := T.placeholder.2.2.1
  let stamp := T.timestamp
  let e := stamp.lnPrevExponent
  let origin := computeLineOrigin T.placeholder.2.1.α pub.ln_prev e
  let lnPrev := origin * α ^ e
  let mr1 := specializeMemRecScaled α lnPrev
    (decide (computeMemRecKind stamp.state (0 : Fin 3) = .active))
    (stamp.recordExponent 0 - e) pub.mr1
  let mr2 := specializeMemRecScaled α lnPrev
    (decide (computeMemRecKind stamp.state (1 : Fin 3) = .active))
    (stamp.recordExponent 1 - e) pub.mr2
  let mr3 := specializeMemRecScaled α lnPrev
    (decide (computeMemRecKind stamp.state (2 : Fin 3) = .active))
    (stamp.recordExponent 2 - e) pub.mr3
  (stamp.state,
    ({ T.placeholder.2.1 with α := α },
      { pub with
        state := stamp.state
        ln_prev := lnPrev
        ln := lnPrev * α ^ (stamp.lnExponent - stamp.lnPrevExponent)
        mr1 := mr1
        mr2 := mr2
        mr3 := mr3 },
      T.placeholder.2.2.2))

/-- Specializing a template whose committed origin is `1` yields the closed form
`ln_prev = α^e`.  Honest generators satisfy this; `V_comp` does not require it. -/
theorem specialize_origin_one (T : ComputeRowTemplate (K := K)) (α : K)
    (h : computeLineOrigin T.placeholder.2.1.α T.placeholder.2.2.1.ln_prev
      T.timestamp.lnPrevExponent = 1) :
    (T.specialize α).2.2.1.ln_prev = α ^ T.timestamp.lnPrevExponent := by
  change computeLineOrigin T.placeholder.2.1.α T.placeholder.2.2.1.ln_prev
      T.timestamp.lnPrevExponent * α ^ T.timestamp.lnPrevExponent =
    α ^ T.timestamp.lnPrevExponent
  rw [h, one_mul]

end ComputeRowTemplate

namespace MemoryRowTemplate

/-- Timestamp-only materialization of one memory row at `α`: the a-bearing row the axis
accounting reads. -/
def specializeA (T : MemoryRowTemplate (K := K)) (α : K) :
    MemoryTable.MState × MemoryTable.DTmem K :=
  let pub := T.placeholder.2.2
  let stamp := T.timestamp
  (stamp.state,
    (T.placeholder.2.1,
      { pub with
        st := stamp.state
        mem := specializeMemRec α
          (decide (memoryMemRecKind stamp.state = .active))
          stamp.recordExponent pub.mem }))

/-- Active rows get `(T, C')` from their a-bearing record; every row gets `lambda? := λ`. -/
noncomputable def encodeRow (lmb : K) (row : MemoryTable.MState × MemoryTable.DTmem K) :
    MemoryTable.MState × MemoryTable.DTmem K :=
  (row.1, (row.2.1,
    if memoryMemRecKind row.1 = .active then
      { row.2.2 with
        mem := NockVM.formRRow row.2.2.mem lmb
        cprime? := some (NockVM.formRCprime row.2.2.mem lmb)
        lambda? := some lmb }
    else { row.2.2 with lambda? := some lmb }))

/-- Materialize one memory row at `α`: timestamps, then the row encode. -/
noncomputable def specialize (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    MemoryTable.MState × MemoryTable.DTmem K :=
  encodeRow lmb (T.specializeA α)

@[simp] theorem specialize_pt (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.pt = T.placeholder.2.2.pt := by
  unfold specialize encodeRow specializeA
  split <;> rfl

@[simp] theorem specialize_lc (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.lc = T.placeholder.2.2.lc := by
  unfold specialize encodeRow specializeA
  split <;> rfl

@[simp] theorem specialize_rc (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.rc = T.placeholder.2.2.rc := by
  unfold specialize encodeRow specializeA
  split <;> rfl

@[simp] theorem specialize_ver (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.ver = T.placeholder.2.2.ver := by
  unfold specialize encodeRow specializeA
  split <;> rfl

@[simp] theorem specialize_lcSt (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.lcSt = T.placeholder.2.2.lcSt := by
  unfold specialize encodeRow specializeA
  split <;> rfl

@[simp] theorem specialize_rcSt (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.rcSt = T.placeholder.2.2.rcSt := by
  unfold specialize encodeRow specializeA
  split <;> rfl

@[simp] theorem specialize_ipre (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.ipre = T.placeholder.2.2.ipre := by
  unfold specialize encodeRow specializeA
  split <;> rfl

@[simp] theorem specialize_icur (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.icur = T.placeholder.2.2.icur := by
  unfold specialize encodeRow specializeA
  split <;> rfl

theorem specialize_mem_active (T : MemoryRowTemplate (K := K)) (α lmb : K)
    (ha : memoryMemRecKind T.timestamp.state = .active) :
    (T.specialize α lmb).2.2.mem =
      NockVM.formRRow (specializeMemRec α true T.timestamp.recordExponent T.placeholder.2.2.mem)
        lmb := by
  unfold specialize encodeRow specializeA
  simp [ha]

theorem specialize_cprime_active (T : MemoryRowTemplate (K := K)) (α lmb : K)
    (ha : memoryMemRecKind T.timestamp.state = .active) :
    (T.specialize α lmb).2.2.cprime =
      NockVM.formRCprime (specializeMemRec α true T.timestamp.recordExponent T.placeholder.2.2.mem)
        lmb := by
  unfold specialize encodeRow specializeA
  simp [ha, MemoryTable.Pub.cprime]

theorem specialize_mem_inactive (T : MemoryRowTemplate (K := K)) (α lmb : K)
    (ha : memoryMemRecKind T.timestamp.state ≠ .active) :
    (T.specialize α lmb).2.2.mem = ComputeTable.MemRec.zero := by
  unfold specialize encodeRow specializeA
  simp [ha, specializeMemRec]

/-- The encode keeps `ts`: the timestamp-only and encoded rows agree on it. -/
theorem specialize_mem_ts (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.mem.ts = (T.specializeA α).2.2.mem.ts := by
  unfold specialize encodeRow
  split <;> rfl

/-- Every specialized row carries the package `λ`. -/
theorem specialize_lambda (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.lambda = lmb := by
  unfold specialize encodeRow
  split <;> simp [MemoryTable.Pub.lambda]

/-- Specialization keeps every column the encode does not touch. -/
theorem specialize_st (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.st = T.timestamp.state := by
  unfold specialize encodeRow specializeA
  split <;> rfl

theorem specialize_fst (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).1 = T.timestamp.state := rfl

theorem specialize_inputs (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.1 = T.placeholder.2.1 := rfl

end MemoryRowTemplate

/-- Relabelling twice is relabelling once. -/
private theorem mapNTree_mapNTree' {A B C : Type} (f : A → B) (g : B → C) (t : NTree A) :
    mapNTree g (mapNTree f t) = mapNTree (fun a => g (f a)) t := by
  let P := fun t : NTree A => mapNTree g (mapNTree f t) = mapNTree (fun a => g (f a)) t
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih
    simp only [P, mapNTree, List.map_map]
    refine congrArg (NTree.node (g (f lbl))) ?_
    apply List.map_congr_left
    intro c hc
    exact ih c hc
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

/-- Row encode of every memory row of an a-bearing execution (`MemoryRowTemplate.encodeRow`):
the executed (row-level) trace of an a-bearing one.  Compute rows are untouched. -/
noncomputable def _root_.Nock.NockVMROM.Thm54.ExactExecution.encodeMem {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    ExactExecution cfg where
  computeTree := exec.computeTree
  memoryForest := exec.memoryForest.map (mapNTree (MemoryRowTemplate.encodeRow cfg.challenges.lam))
  memoryForest_nonempty := by simpa using exec.memoryForest_nonempty
  memory_root_count := by simpa using exec.memory_root_count
  compute_bfs_length := exec.compute_bfs_length
  memory_bfs_length := by
    rw [bfsForest_mapNTree]; simpa using exec.memory_bfs_length

theorem _root_.Nock.NockVMROM.Thm54.ExactExecution.encodeMem_memoryRows {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    exec.encodeMem.memoryRows =
      exec.memoryRows.map (MemoryRowTemplate.encodeRow cfg.challenges.lam) := by
  simp only [ExactExecution.memoryRows, ExactExecution.encodeMem]
  rw [bfsForest_mapNTree]
  simp [List.map_map, Function.comp_def]

theorem _root_.Nock.NockVMROM.Thm54.ExactExecution.encodeMem_computeRows {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) : exec.encodeMem.computeRows = exec.computeRows := rfl

theorem _root_.Nock.NockVMROM.Thm54.ExactExecution.encodeMem_memoryRowAt {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) (i : Fin cfg.memRows) :
    exec.encodeMem.memoryRowAt i =
      MemoryRowTemplate.encodeRow cfg.challenges.lam (exec.memoryRowAt i) := by
  unfold ExactExecution.memoryRowAt
  simp only [List.get_eq_getElem, Fin.coe_cast]
  have h := congrArg (fun l => l[(i : ℕ)]?) (ExactExecution.encodeMem_memoryRows exec)
  simp only [List.getElem?_map] at h
  have hi : (i : ℕ) < exec.memoryRows.length := by
    rw [exec.memoryRows_length]; exact i.isLt
  have hi' : (i : ℕ) < exec.encodeMem.memoryRows.length := by
    rw [exec.encodeMem.memoryRows_length]; exact i.isLt
  rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at h
  simpa using h

namespace MemoryRowTemplate

/-! Field preservation of the Form R row encode. -/

@[simp] theorem encodeRow_fst (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (encodeRow lmb r).1 = r.1 := rfl
@[simp] theorem encodeRow_inputs (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (encodeRow lmb r).2.1 = r.2.1 := rfl
@[simp] theorem encodeRow_st (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (encodeRow lmb r).2.2.st = r.2.2.st := by unfold encodeRow; split <;> rfl
@[simp] theorem encodeRow_pt (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (encodeRow lmb r).2.2.pt = r.2.2.pt := by unfold encodeRow; split <;> rfl
@[simp] theorem encodeRow_lc (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (encodeRow lmb r).2.2.lc = r.2.2.lc := by unfold encodeRow; split <;> rfl
@[simp] theorem encodeRow_rc (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (encodeRow lmb r).2.2.rc = r.2.2.rc := by unfold encodeRow; split <;> rfl
@[simp] theorem encodeRow_ver (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (encodeRow lmb r).2.2.ver = r.2.2.ver := by unfold encodeRow; split <;> rfl
@[simp] theorem encodeRow_mem_root (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (encodeRow lmb r).2.2.mem.root = r.2.2.mem.root := by unfold encodeRow; split <;> rfl
@[simp] theorem encodeRow_mem_child (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (encodeRow lmb r).2.2.mem.child = r.2.2.mem.child := by unfold encodeRow; split <;> rfl
@[simp] theorem encodeRow_mem_ts (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (encodeRow lmb r).2.2.mem.ts = r.2.2.mem.ts := by unfold encodeRow; split <;> rfl
theorem encodeRow_mem_inactive (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K)
    (h : memoryMemRecKind r.1 ≠ .active) :
    (encodeRow lmb r).2.2.mem = r.2.2.mem := by
  unfold encodeRow; rw [if_neg h]
theorem encodeRow_mem_active (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K)
    (h : memoryMemRecKind r.1 = .active) :
    (encodeRow lmb r).2.2.mem = NockVM.formRRow r.2.2.mem lmb := by
  unfold encodeRow; rw [if_pos h]

end MemoryRowTemplate

/-- α-free forest-first carrier.  Its labels contain placeholder α-columns that are ignored by
the specialization functions; all geometry proofs mention only tree shape and template lengths. -/
structure ExactExecutionTemplate (T : ExactConfigTemplate F K) where
  computeTree : NTree (ComputeRowTemplate (K := K))
  memoryForest : List (NTree (MemoryRowTemplate (K := K)))
  memoryForest_nonempty : memoryForest ≠ []
  memory_root_count : memoryForest.length = T.kMem
  compute_bfs_length : (bfsForest [computeTree]).length = T.compRows
  memory_bfs_length : (bfsForest memoryForest).length = T.memRows

namespace ExactExecutionTemplate

/-- Canonical BFS compute templates. -/
def computeRows {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    List (ComputeRowTemplate (K := K)) :=
  (bfsForest [E.computeTree]).map NTree.label

/-- Canonical BFS memory templates. -/
def memoryRows {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) :
    List (MemoryRowTemplate (K := K)) :=
  (bfsForest E.memoryForest).map NTree.label

/-- Recursively specialize every compute and memory label.  `mapNTree` changes no edge, root,
or child order, so all dependent `ExactExecution` length proofs transport. -/
def specialize {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K) :
    ExactExecution (T.specialize α lmb) where
  computeTree := mapNTree (fun row => row.specialize α) E.computeTree
  memoryForest := E.memoryForest.map (mapNTree (fun row => row.specialize α lmb))
  memoryForest_nonempty := by simpa using E.memoryForest_nonempty
  memory_root_count := by
    change (E.memoryForest.map (mapNTree (fun row => row.specialize α lmb))).length = T.kMem
    simpa using E.memory_root_count
  compute_bfs_length := by
    change
      (bfsForest [mapNTree (fun row => row.specialize α) E.computeTree]).length =
        T.compRows
    rw [show [mapNTree (fun row => row.specialize α) E.computeTree] =
      [E.computeTree].map (mapNTree (fun row => row.specialize α)) by rfl,
      bfsForest_mapNTree]
    simpa using E.compute_bfs_length
  memory_bfs_length := by
    change
      (bfsForest (E.memoryForest.map
        (mapNTree (fun row => row.specialize α lmb)))).length = T.memRows
    rw [bfsForest_mapNTree]
    simpa using E.memory_bfs_length

/-- Specialized compute BFS rows are the pointwise specialization of template BFS rows. -/
theorem specialize_computeRows
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K) :
    (E.specialize α lmb).computeRows = E.computeRows.map (fun row => row.specialize α) := by
  simp only [ExactExecution.computeRows, specialize, computeRows]
  rw [show [mapNTree (fun row => row.specialize α) E.computeTree] =
    [E.computeTree].map (mapNTree (fun row => row.specialize α)) by rfl,
    bfsForest_mapNTree]
  simp [List.map_map, Function.comp_def]

/-- Specialized memory BFS rows are the pointwise specialization of template BFS rows. -/
theorem specialize_memoryRows
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K) :
    (E.specialize α lmb).memoryRows = E.memoryRows.map (fun row => row.specialize α lmb) := by
  simp only [ExactExecution.memoryRows, specialize, memoryRows]
  rw [bfsForest_mapNTree]
  simp [List.map_map, Function.comp_def]

/-- The a-bearing view of the specialized execution: same compute rows, memory rows
timestamp-only (`MemoryRowTemplate.specializeA`). -/
def specializeA {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K) :
    ExactExecution (T.specialize α lmb) where
  computeTree := (E.specialize α lmb).computeTree
  memoryForest := E.memoryForest.map (mapNTree (fun row => row.specializeA α))
  memoryForest_nonempty := by simpa using E.memoryForest_nonempty
  memory_root_count := by
    change (E.memoryForest.map (mapNTree (fun row => row.specializeA α))).length = T.kMem
    simpa using E.memory_root_count
  compute_bfs_length := (E.specialize α lmb).compute_bfs_length
  memory_bfs_length := by
    change
      (bfsForest (E.memoryForest.map
        (mapNTree (fun row => row.specializeA α)))).length = T.memRows
    rw [bfsForest_mapNTree]
    simpa using E.memory_bfs_length

theorem specializeA_memoryRows
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K) :
    (E.specializeA α lmb).memoryRows = E.memoryRows.map (fun row => row.specializeA α) := by
  simp only [ExactExecution.memoryRows, specializeA, memoryRows]
  rw [bfsForest_mapNTree]
  simp [List.map_map, Function.comp_def]

/-- Every specialized memory row carries the sampled `λ`. -/
theorem specialize_memory_lambda
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K) :
    ∀ row ∈ (E.specialize α lmb).memoryRows, row.2.2.lambda = (T.specialize α lmb).challenges.lam := by
  intro row hrow
  rw [specialize_memoryRows] at hrow
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hrow
  exact MemoryRowTemplate.specialize_lambda t α lmb

/-- The number of derived memory responses does not depend on the sampled `(α, λ)`: it counts the
template rows whose `ver` flag is set, and specialization never changes `ver`. -/
theorem specialize_derivedResponseIO_length
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K) :
    (E.specialize α lmb).derivedResponseIO.length =
      (E.memoryRows.filter (fun t => t.placeholder.2.2.ver)).length := by
  unfold ExactExecution.derivedResponseIO
  rw [E.specialize_memoryRows α lmb]
  induction E.memoryRows with
  | nil => rfl
  | cons t l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.length_append, ih, List.filter_cons,
        MemoryRowTemplate.specialize_ver]
      split <;> simp_all <;> omega

/-- Two sampled `(α, λ)` give derived response lists of equal length. -/
theorem specialize_derivedResponseIO_length_eq
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb α' lmb' : K) :
    (E.specialize α lmb).derivedResponseIO.length =
      (E.specialize α' lmb').derivedResponseIO.length := by
  rw [E.specialize_derivedResponseIO_length, E.specialize_derivedResponseIO_length]

/-- The number of derived compute requests does not depend on the sampled `λ`: the raw requests
are read from the compute rows, which `λ` never touches. -/
theorem specialize_derivedRequestIO_length_eq
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb lmb' : K) :
    (E.specialize α lmb).derivedRequestIO.length =
      (E.specialize α lmb').derivedRequestIO.length := by
  simp only [ExactExecution.derivedRequestIO, List.length_map]
  rfl

/-- The executed trace is the row encode of the a-bearing view. -/
theorem specialize_eq_encodeMem
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K) :
    E.specialize α lmb = (E.specializeA α lmb).encodeMem := by
  simp only [specialize, specializeA, ExactExecution.encodeMem, List.map_map]
  congr 1
  simp [Function.comp_def, mapNTree_mapNTree']
  intro _ _
  rfl

/-- The executed rows are the row encode of the a-bearing view. -/
theorem specialize_memoryRows_eq_encode
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K) :
    (E.specialize α lmb).memoryRows =
      (E.specializeA α lmb).memoryRows.map (MemoryRowTemplate.encodeRow lmb) := by
  rw [specialize_memoryRows, specializeA_memoryRows, List.map_map]
  rfl

end ExactExecutionTemplate

/-! ## Exact specialization equations -/

/-- Every α-dependent compute-table timestamp column at one canonical row, relative
to the published `ln_prev`.  Algorithm `NockCompute` / `V_comp` relates `ln`
and record timestamps to `ln_prev` by powers of `α`
and does **not** pin first-row `ln_prev`.  The absolute
form `ln_prev = α^lnPrevExponent` is the honest origin-1 convention, not a RAP
gate; `dataOf` no longer consumes it. -/
def ComputeTimestampSpecializesAt
    (α : K) (stamp : ComputeTimestampRow)
    (row : ComputeTable.State × ComputeTable.DTcomp K) : Prop :=
  row.1 = stamp.state ∧
    row.2.1.α = α ∧
    row.2.2.1.state = stamp.state ∧
    row.2.2.1.ln = row.2.2.1.ln_prev *
      α ^ (stamp.lnExponent - stamp.lnPrevExponent) ∧
    (∀ i : Fin 3,
      (computeMemRec row.2.2.1 i).ts =
        if computeMemRecKind stamp.state i = .active
        then row.2.2.1.ln_prev *
          α ^ (stamp.recordExponent i - stamp.lnPrevExponent)
        else 0) ∧
    (∀ i : Fin 3,
      computeMemRecKind stamp.state i = .padding →
        computeMemRec row.2.2.1 i = ComputeTable.MemRec.zero)

/-- The α-dependent memory-record timestamp at one canonical memory row. -/
def MemoryTimestampSpecializesAt
    (α : K) (stamp : MemoryTimestampRow)
    (row : MemoryTable.MState × MemoryTable.DTmem K) : Prop :=
  row.1 = stamp.state ∧
    row.2.2.st = stamp.state ∧
    row.2.2.mem.ts = (
      if memoryMemRecKind stamp.state = .active
      then α ^ stamp.recordExponent
      else 0) ∧
    (memoryMemRecKind stamp.state = .padding →
      row.2.2.mem = ComputeTable.MemRec.zero)

theorem MemoryRowTemplate.specializesAt_of_encodeRow {α lmb : K} {stamp : MemoryTimestampRow}
    {r : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp (MemoryRowTemplate.encodeRow lmb r)) :
    MemoryTimestampSpecializesAt α stamp r := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [MemoryRowTemplate.encodeRow_fst, MemoryRowTemplate.encodeRow_st,
    MemoryRowTemplate.encodeRow_mem_ts] at h1 h2 h3
  refine ⟨h1, h2, h3, fun hp => ?_⟩
  have hna : memoryMemRecKind r.1 ≠ .active := by rw [h1, hp]; decide
  rw [← MemoryRowTemplate.encodeRow_mem_inactive lmb r hna]
  exact h4 hp

/-- `α^m * α^(n-m) = α^n` when `m ≤ n`. -/
theorem pow_mul_pow_sub (α : K) {m n : ℕ} (h : m ≤ n) :
    α ^ m * α ^ (n - m) = α ^ n := by
  rw [← pow_add, Nat.add_sub_cancel' h]

/-- Absolute `α^e` specialization (honest origin `1`) implies the RAP-faithful
relative form.  Hand-built origin-1 rows use this to keep their `α^e` calculations. -/
theorem ComputeTimestampSpecializesAt.of_absolute
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hstate : row.1 = stamp.state)
    (hα : row.2.1.α = α)
    (hpub : row.2.2.1.state = stamp.state)
    (hlnPrev : row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
    (hln : row.2.2.1.ln = α ^ stamp.lnExponent)
    (hts : ∀ i : Fin 3,
      (computeMemRec row.2.2.1 i).ts =
        if computeMemRecKind stamp.state i = .active
        then α ^ stamp.recordExponent i
        else 0)
    (hpad : ∀ i : Fin 3,
      computeMemRecKind stamp.state i = .padding →
        computeMemRec row.2.2.1 i = ComputeTable.MemRec.zero)
    (hln_ge : stamp.lnPrevExponent ≤ stamp.lnExponent)
    (hrec_ge : ∀ i : Fin 3, stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    ComputeTimestampSpecializesAt α stamp row := by
  refine ⟨hstate, hα, hpub, ?_, ?_, hpad⟩
  · rw [hln, hlnPrev, ← pow_mul_pow_sub α hln_ge]
  · intro i
    have ht := hts i
    by_cases hk : computeMemRecKind stamp.state i = .active
    · rw [if_pos hk] at ht ⊢
      rw [hlnPrev, ht, ← pow_mul_pow_sub α (hrec_ge i)]
    · rw [if_neg hk] at ht ⊢
      exact ht

/-- Honest origin `1` recovers the closed-form record timestamp `α^e`. -/
theorem compute_ts_eq_pow_of_origin
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (htime : ComputeTimestampSpecializesAt α stamp row)
    (horigin : row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
    (i : Fin 3)
    (hge : stamp.lnPrevExponent ≤ stamp.recordExponent i)
    (hactive : computeMemRecKind stamp.state i = .active) :
    (computeMemRec row.2.2.1 i).ts = α ^ stamp.recordExponent i := by
  have ht := htime.2.2.2.2.1 i
  rw [if_pos hactive] at ht
  rw [ht, horigin, pow_mul_pow_sub α hge]

/-- An active compute record is exactly the concrete image of its noun/Nat slot. -/
theorem activeComputeRecord_eq_tableRecordAt
    {z α : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (htime : ComputeTimestampSpecializesAt α stamp row)
    (horigin : row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
    (i : Fin 3) (hi : (i : ℕ) < Nock.Framework.recordCount s.state)
    (hge : stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    computeMemRec row.2.2.1 i =
      SemanticTimestampSkeleton.tableRecordAt z α
        { record := s.memoryRecord i hi
          exponent := stamp.recordExponent i } := by
  have hbindOuter := hbind.1
  obtain ⟨_, _, _, _, _, _, _, _, hrecords⟩ := hbind
  have houter := htime.1
  have hstate : stamp.state = s.state := houter.symm.trans hbindOuter
  have hb := hrecords i
  rw [dif_pos hi] at hb
  have hk : computeMemRecKind stamp.state i = .active := by
    simp [computeMemRecKind, hstate, hi]
  refine (ComputeTable.MemRec.ext hb.1.symm hb.2.1.symm hb.2.2.symm ?_).symm
  simpa [SemanticTimestampSkeleton.tableRecordAt] using
    (compute_ts_eq_pow_of_origin htime horigin i hge hk).symm

/-- A live row-level memory record is the Form R encode of the concrete image of its noun/Nat
slot (`BindMemRow`, `Batch590`). -/
theorem activeMemoryRecord_eq_tableRecordAt
    {z α : K} {s : SemanticStrategy.MemoryRowSkeleton}
    {stamp : MemoryTimestampRow}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (hbind : SemanticStrategy.BindMemoryRow z s row)
    (htime : MemoryTimestampSpecializesAt α stamp row)
    (ha : memoryMemRecKind s.state = .active) :
    NockVM.encRecC row.2.2.mem row.2.2.cprime =
      NockVM.encRecFormR
        (SemanticTimestampSkeleton.tableRecordAt z α
          { record := s.memoryRecord ha
            exponent := stamp.recordExponent }) row.2.2.lambda := by
  have hbindOuter := hbind.1
  obtain ⟨_, _, _, _, _, hrecord, _⟩ := hbind
  obtain ⟨houter, _, htime, _⟩ := htime
  have hstate : stamp.state = s.state := houter.symm.trans hbindOuter
  rw [dif_pos ha] at hrecord
  have ha' : memoryMemRecKind stamp.state = .active := by
    simpa [hstate] using ha
  simp [ha'] at htime
  rw [hrecord.encRecC_eq]
  congr 1
  apply ComputeTable.MemRec.ext
  · exact hrecord.1
  · exact hrecord.2.1
  · rfl
  · exact htime

/-- Canonical request extraction is exactly the specialized semantic slot list for one row. -/
theorem computeRequestRecords_eq_semanticSlots
    {z α : K} (_hz : z ≠ 0)
    {s : SemanticStrategy.ComputeRowSkeleton}
    {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hbind : SemanticStrategy.BindComputeRow z s row)
    (htime : ComputeTimestampSpecializesAt α stamp row)
    (horigin : row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
    (hge : ∀ i : Fin 3, (i : ℕ) < Nock.Framework.recordCount stamp.state →
      stamp.lnPrevExponent ≤ stamp.recordExponent i) :
    NockVM.activeRequestRecords row.2.2.1 =
      (computeRowRecordSlots s stamp).map
        (SemanticTimestampSkeleton.tableRecordAt z α) := by
  have hrec := activeComputeRecord_eq_tableRecordAt hbind htime horigin
  have hst : stamp.state = s.state := htime.1.symm.trans hbind.1
  have hstate : row.2.2.1.state = s.state := hbind.2.2.1
  simp only [computeMemRec] at hrec
  have hge' : ∀ i : Fin 3, (i : ℕ) < Nock.Framework.recordCount s.state →
      stamp.lnPrevExponent ≤ stamp.recordExponent i := by
    intro i hi
    exact hge i (by simpa [hst] using hi)
  have hpos := Nock.Framework.recordCount_pos s.state
  have hle : Nock.Framework.recordCount s.state ≤ 3 := by
    cases s.state <;> decide
  have hcount :
      Nock.Framework.recordCount s.state = 1 ∨
        Nock.Framework.recordCount s.state = 2 ∨
        Nock.Framework.recordCount s.state = 3 := by
    omega
  rcases hcount with hcount | hcount | hcount
  · have hr0 : row.2.2.1.mr1 =
        SemanticTimestampSkeleton.tableRecordAt z α
          { record := s.memoryRecord 0 (by omega)
            exponent := stamp.recordExponent 0 } := by
      simpa using hrec (0 : Fin 3) (by omega) (hge' 0 (by omega))
    have hslots :
        NockVM.activeRequestRecords row.2.2.1 = [row.2.2.1.mr1] := by
      cases hs : s.state <;>
        norm_num [Nock.Framework.recordCount, hs] at hcount <;>
        simp_all [NockVM.activeRequestRecords]
    rw [hslots, hr0]
    simp [computeRowRecordSlots, hcount]
  · have hr0 : row.2.2.1.mr1 =
        SemanticTimestampSkeleton.tableRecordAt z α
          { record := s.memoryRecord 0 (by omega)
            exponent := stamp.recordExponent 0 } := by
      simpa using hrec (0 : Fin 3) (by omega) (hge' 0 (by omega))
    have hr1 : row.2.2.1.mr2 =
        SemanticTimestampSkeleton.tableRecordAt z α
          { record := s.memoryRecord 1 (by omega)
            exponent := stamp.recordExponent 1 } := by
      simpa using hrec (1 : Fin 3) (by omega) (hge' 1 (by omega))
    have hslots :
        NockVM.activeRequestRecords row.2.2.1 =
          [row.2.2.1.mr1, row.2.2.1.mr2] := by
      cases hs : s.state <;>
        norm_num [Nock.Framework.recordCount, hs] at hcount <;>
        simp_all [NockVM.activeRequestRecords]
    rw [hslots, hr0, hr1]
    simp [computeRowRecordSlots, hcount]
  · have hr0 : row.2.2.1.mr1 =
        SemanticTimestampSkeleton.tableRecordAt z α
          { record := s.memoryRecord 0 (by omega)
            exponent := stamp.recordExponent 0 } := by
      simpa using hrec (0 : Fin 3) (by omega) (hge' 0 (by omega))
    have hr1 : row.2.2.1.mr2 =
        SemanticTimestampSkeleton.tableRecordAt z α
          { record := s.memoryRecord 1 (by omega)
            exponent := stamp.recordExponent 1 } := by
      simpa using hrec (1 : Fin 3) (by omega) (hge' 1 (by omega))
    have hr2 : row.2.2.1.mr3 =
        SemanticTimestampSkeleton.tableRecordAt z α
          { record := s.memoryRecord 2 (by omega)
            exponent := stamp.recordExponent 2 } := by
      simpa using hrec (2 : Fin 3) (by omega) (hge' 2 (by omega))
    have hslots :
        NockVM.activeRequestRecords row.2.2.1 =
          [row.2.2.1.mr1, row.2.2.1.mr2, row.2.2.1.mr3] := by
      cases hs : s.state <;>
        norm_num [Nock.Framework.recordCount, hs] at hcount <;>
        simp_all [NockVM.activeRequestRecords]
    rw [hslots, hr0, hr1, hr2]
    simp [computeRowRecordSlots, hcount]

/-- Canonical response extraction is exactly the specialized semantic slot list for one row.
    `BindMemoryRow` carries honest `ver`. -/
theorem memoryResponseRecords_eq_semanticSlots
    {z α lmb : K}
    {s : SemanticStrategy.MemoryRowSkeleton}
    {stamp : MemoryTimestampRow}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (hbind : SemanticStrategy.BindMemoryRow z s row)
    (htime : MemoryTimestampSpecializesAt α stamp row)
    (hlam : row.2.2.lambda = lmb) :
    (MemoryTable.responseRecords row.2.2).map
        (fun r => NockVM.encRecC r row.2.2.cprime) =
      (memoryRowResponseSlots s stamp).map (fun slot =>
        NockVM.encRecFormR (SemanticTimestampSkeleton.tableRecordAt z α slot) lmb) := by
  have hver : row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) :=
    hbind.honest_ver
  have hst : row.2.2.st = s.state := hbind.2.2.1
  rw [MemoryTable.responseRecords_of_honest_ver _ hver]
  cases hs : s.state
  · have hrow : row.2.2.st = .decompose := by simpa [hs] using hst
    simp [memoryRowResponseSlots, hs, hrow]
  · have hrow : row.2.2.st = .halt := by simpa [hs] using hst
    simp [memoryRowResponseSlots, hs, hrow]
  · have ha : memoryMemRecKind s.state = .active := by simp [hs, memoryMemRecKind]
    have hrec := activeMemoryRecord_eq_tableRecordAt hbind htime ha
    rw [hlam] at hrec
    have hrow : row.2.2.st = .read_root := by simpa [hs] using hst
    simp [memoryRowResponseSlots, hs, hrow, hrec]
  · have hrow : row.2.2.st = .verify_child := by simpa [hs] using hst
    simp [memoryRowResponseSlots, hs, hrow]

private theorem rawRequests_eq_semanticSlots
    {z α : K} (hz : z ≠ 0) :
    ∀ {skeletonRows : List SemanticStrategy.ComputeRowSkeleton}
      {stamps : List ComputeTimestampRow}
      {rows : List (ComputeTable.State × ComputeTable.DTcomp K)},
      List.Forall₂
        (fun skeleton stamp => stamp.state = skeleton.state)
        skeletonRows stamps →
      List.Forall₂ (SemanticStrategy.BindComputeRow z) skeletonRows rows →
      List.Forall₂ (ComputeTimestampSpecializesAt α) stamps rows →
      List.Forall₂ (fun stamp row =>
          row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent) stamps rows →
      (∀ stamp ∈ stamps, ∀ i : Fin 3,
        (i : ℕ) < Nock.Framework.recordCount stamp.state →
          stamp.lnPrevExponent ≤ stamp.recordExponent i) →
      rows.flatMap (fun row => NockVM.activeRequestRecords row.2.2.1) =
        ((skeletonRows.zip stamps).flatMap fun pair =>
          computeRowRecordSlots pair.1 pair.2).map
            (SemanticTimestampSkeleton.tableRecordAt z α) := by
  intro skeletonRows stamps rows htop hbind htime horigin hge
  induction stamps generalizing skeletonRows rows with
  | nil =>
      cases htop
      cases hbind
      cases htime
      cases horigin
      rfl
  | cons stamp stampsTail ih =>
      cases skeletonRows with
      | nil => cases htop
      | cons s skeletonTail =>
          cases rows with
          | nil => cases hbind
          | cons row rowsTail =>
              cases htop with
              | cons hstate htopTail =>
                  cases hbind with
                  | cons hrow hbindTail =>
                      cases htime with
                      | cons hstamp htimeTail =>
                          cases horigin with
                          | cons horiginHead horiginTail =>
                              simp only [List.flatMap_cons, List.zip_cons_cons]
                              have hgeHead : ∀ i : Fin 3,
                                  (i : ℕ) < Nock.Framework.recordCount stamp.state →
                                    stamp.lnPrevExponent ≤ stamp.recordExponent i :=
                                fun i hi => hge stamp (by simp) i hi
                              have hgeTail : ∀ st ∈ stampsTail, ∀ i : Fin 3,
                                  (i : ℕ) < Nock.Framework.recordCount st.state →
                                    st.lnPrevExponent ≤ st.recordExponent i :=
                                fun st hst i hi => hge st (by simp [hst]) i hi
                              rw [computeRequestRecords_eq_semanticSlots hz hrow hstamp
                                    horiginHead hgeHead,
                                ih htopTail hbindTail htimeTail horiginTail hgeTail,
                                List.map_append]

private theorem rawResponses_eq_semanticSlots
    {z α lmb : K} :
    ∀ {skeletonRows : List SemanticStrategy.MemoryRowSkeleton}
      {stamps : List MemoryTimestampRow}
      {rows : List (MemoryTable.MState × MemoryTable.DTmem K)},
      List.Forall₂
        (fun skeleton stamp => stamp.state = skeleton.state)
        skeletonRows stamps →
      List.Forall₂ (SemanticStrategy.BindMemoryRow z) skeletonRows rows →
      List.Forall₂ (MemoryTimestampSpecializesAt α) stamps rows →
      (∀ row ∈ rows, row.2.2.lambda = lmb) →
      rows.flatMap (fun row =>
          (MemoryTable.responseRecords row.2.2).map
            (fun r => NockVM.encRecC r row.2.2.cprime)) =
        ((skeletonRows.zip stamps).flatMap fun pair =>
          memoryRowResponseSlots pair.1 pair.2).map (fun slot =>
            NockVM.encRecFormR (SemanticTimestampSkeleton.tableRecordAt z α slot) lmb) := by
  intro skeletonRows stamps rows htop hbind htime hlam
  induction hbind generalizing stamps with
  | nil =>
      cases htop
      cases htime
      rfl
  | cons hrow htail ih =>
      cases htop with
      | cons hstate htopTail =>
          cases htime with
          | cons hstamp htimeTail =>
              simp only [List.flatMap_cons, List.zip_cons_cons]
              rw [memoryResponseRecords_eq_semanticSlots hrow hstamp
                  (hlam _ (List.mem_cons_self ..)),
                ih htopTail htimeTail (fun r hr => hlam r (List.mem_cons_of_mem _ hr)),
                List.map_append]

namespace ComputeRowTemplate

theorem specializes (T : ComputeRowTemplate (K := K)) (α : K) :
    ComputeTimestampSpecializesAt α T.timestamp (T.specialize α) := by
  unfold ComputeTimestampSpecializesAt specialize
  dsimp
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [computeMemRec, specializeMemRecScaled, computeMemRecKind,
        computeLineOrigin] <;>
      split <;> rfl
  · intro i hi
    fin_cases i <;>
      simp_all [computeMemRec, specializeMemRecScaled, computeMemRecKind]

/-- An active record keeps all binding-relevant coordinates under timestamp specialization. -/
theorem bindMemRec_specialize_active
    {z α : K} {s : SemanticStrategy.MemRecSkeleton}
    {record : ComputeTable.MemRec K} {exponent : ℕ}
    (h : SemanticStrategy.BindMemRec z s record) :
    SemanticStrategy.BindMemRec z s
      (specializeMemRec α true exponent record) := by
  simpa [SemanticStrategy.BindMemRec, specializeMemRec] using h

theorem bindMemRow_specialize_active
    {z α : K} {s : SemanticStrategy.MemRecSkeleton}
    {record : ComputeTable.MemRec K} {cprime lmb : K} {exponent : ℕ}
    (h : SemanticStrategy.BindMemRow z s record cprime lmb) :
    SemanticStrategy.BindMemRow z s
      (specializeMemRec α true exponent record) cprime lmb := by
  simpa [SemanticStrategy.BindMemRow, specializeMemRec] using h

theorem bindMemRec_specialize_active_scaled
    {z α origin : K} {s : SemanticStrategy.MemRecSkeleton}
    {record : ComputeTable.MemRec K} {exponent : ℕ}
    (h : SemanticStrategy.BindMemRec z s record) :
    SemanticStrategy.BindMemRec z s
      (specializeMemRecScaled α origin true exponent record) := by
  simpa [SemanticStrategy.BindMemRec, specializeMemRecScaled] using h

/-- α-free binding of a compute template row to its noun row. -/
def BindsRow (z : K) (s : SemanticStrategy.ComputeRowSkeleton)
    (T : ComputeRowTemplate (K := K)) : Prop :=
  T.timestamp.state = s.state ∧
    SemanticStrategy.BindComputeRow z s T.placeholder

/-- Row binding is preserved by concrete timestamp specialization. -/
theorem bindsRow_specialize
    {z α : K} {s : SemanticStrategy.ComputeRowSkeleton}
    {T : ComputeRowTemplate (K := K)}
    (h : BindsRow z s T) :
    SemanticStrategy.BindComputeRow z s (T.specialize α) := by
  obtain ⟨hstamp, hrow⟩ := h
  obtain ⟨_houter, hseed, _hpubState, hs, hf, he, hdec, hsf, hmr⟩ := hrow
  refine ⟨hstamp, hseed, hstamp, hs, hf, he, hdec, hsf, ?_⟩
  intro i
  by_cases hi : (i : ℕ) < Nock.Framework.recordCount s.state
  · rw [dif_pos hi]
    have hactive : computeMemRecKind T.timestamp.state i = .active := by
      simp [computeMemRecKind, hstamp, hi]
    have hold := hmr i
    rw [dif_pos hi] at hold
    have hspec :
        computeMemRec (T.specialize α).2.2.1 i =
          specializeMemRecScaled α (T.specialize α).2.2.1.ln_prev true
            (T.timestamp.recordExponent i - T.timestamp.lnPrevExponent)
            (computeMemRec T.placeholder.2.2.1 i) := by
      fin_cases i <;>
        simp_all [ComputeRowTemplate.specialize, computeMemRec,
          specializeMemRecScaled, computeMemRecKind]
    rw [hspec]
    exact bindMemRec_specialize_active_scaled hold
  · rw [dif_neg hi]
    have hpadding : computeMemRecKind T.timestamp.state i = .padding := by
      simp [computeMemRecKind, hstamp, hi]
    fin_cases i <;>
      simp_all [ComputeRowTemplate.specialize, computeMemRec,
        specializeMemRecScaled, computeMemRecKind]

end ComputeRowTemplate

namespace MemoryRowTemplate

theorem specializes (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    MemoryTimestampSpecializesAt α T.timestamp (T.specialize α lmb) := by
  refine ⟨rfl, specialize_st T α lmb, ?_, ?_⟩
  · rw [specialize_mem_ts]
    unfold specializeA
    cases hs : T.timestamp.state <;>
      simp [hs, specializeMemRec, memoryMemRecKind, ComputeTable.MemRec.zero]
  · intro h
    exact specialize_mem_inactive T α lmb (by rw [h]; decide)

theorem specializesA (T : MemoryRowTemplate (K := K)) (α : K) :
    MemoryTimestampSpecializesAt α T.timestamp (T.specializeA α) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold specializeA
    cases hs : T.timestamp.state <;>
      simp [hs, specializeMemRec, memoryMemRecKind, ComputeTable.MemRec.zero]
  · intro h
    have ha : memoryMemRecKind T.timestamp.state ≠ .active := by rw [h]; decide
    unfold specializeA
    simp [ha, specializeMemRec]

/-- α-free binding of a memory template row to its noun row. -/
def BindsRow (z : K) (s : SemanticStrategy.MemoryRowSkeleton)
    (T : MemoryRowTemplate (K := K)) : Prop :=
  T.timestamp.state = s.state ∧
    SemanticStrategy.BindMemoryRowA z s T.placeholder

theorem bindsRow_specialize
    {z α lmb : K} {s : SemanticStrategy.MemoryRowSkeleton}
    {T : MemoryRowTemplate (K := K)}
    (h : BindsRow z s T) :
    SemanticStrategy.BindMemoryRow z s (T.specialize α lmb) := by
  obtain ⟨hstamp, hrow⟩ := h
  obtain ⟨_houter, hseed, _hpubState, hpt, hchild, hmem, hver⟩ := hrow
  refine ⟨hstamp, hseed, (specialize_st T α lmb).trans hstamp, by simpa using hpt, ?_, ?_,
    by simpa using hver⟩
  · intro i
    have hi := hchild i
    simpa [memoryChildCell] using hi
  · by_cases ha : memoryMemRecKind s.state = .active
    · rw [dif_pos ha]
      have ha' : memoryMemRecKind T.timestamp.state = .active := by
        simpa [hstamp] using ha
      have hold := hmem
      rw [dif_pos ha] at hold
      rw [specialize_mem_active T α lmb ha', specialize_cprime_active T α lmb ha',
        specialize_lambda T α lmb]
      obtain ⟨hr, hc, hax⟩ := hold
      refine ⟨by simpa [specializeMemRec] using hr, by simpa [specializeMemRec] using hc, ?_, ?_⟩
      · simp [NockVM.formRRow, specializeMemRec, hax]
      · simp [NockVM.formRCprime, specializeMemRec, hax]
    · rw [dif_neg ha]
      exact specialize_mem_inactive T α lmb (by rw [hstamp]; exact ha)

end MemoryRowTemplate

/-! ## Recursive semantic consistency of α-free templates -/

/-- Recursive compute-tree consistency before timestamp specialization.  This stores noun/row
binding only; it contains no `α`, powers, or specialized execution. -/
inductive ComputeTemplateTreeBinds (z : K) :
    NTree SemanticStrategy.ComputeRowSkeleton →
      NTree (ComputeRowTemplate (K := K)) → Prop
  | node {s sc row rc}
      (shape : sc.length = ComputeTable.fanoutComp s.state)
      (rowBinding : ComputeRowTemplate.BindsRow z s row)
      (children : List.Forall₂ (ComputeTemplateTreeBinds z) sc rc) :
      ComputeTemplateTreeBinds z (.node s sc) (.node row rc)

/-- Recursive memory-tree consistency before timestamp specialization. -/
inductive MemoryTemplateTreeBinds (z : K) :
    NTree SemanticStrategy.MemoryRowSkeleton →
      NTree (MemoryRowTemplate (K := K)) → Prop
  | node {s sc row rc}
      (shape : sc.length = MemoryTable.fanoutMem s.state)
      (rowBinding : MemoryRowTemplate.BindsRow z s row)
      (children : List.Forall₂ (MemoryTemplateTreeBinds z) sc rc) :
      MemoryTemplateTreeBinds z (.node s sc) (.node row rc)

private theorem totalSize_tail_lt
    {A : Type*} (tree : NTree A) (rest : List (NTree A)) :
    totalSize rest < totalSize (tree :: rest) := by
  rw [totalSize_cons]
  cases tree
  simp [NTree.size]

private theorem totalSize_singleton_le_cons
    {A : Type*} (tree : NTree A) (rest : List (NTree A)) :
    totalSize [tree] ≤ totalSize (tree :: rest) := by
  rw [totalSize_cons, totalSize_cons, totalSize_nil]
  omega

private theorem weighted_totalSize_tail_lt
    {A : Type*} (tree : NTree A) (rest : List (NTree A)) :
    2 * totalSize rest + 1 < 2 * totalSize (tree :: rest) + 1 := by
  have h := totalSize_tail_lt tree rest
  omega

mutual
  /-- Recursive compute consistency specializes to the production recursive binding. -/
  theorem ComputeTemplateTreeBinds.specialize
      {z α : K}
      {s : NTree SemanticStrategy.ComputeRowSkeleton}
      {tree : NTree (ComputeRowTemplate (K := K))}
      (h : ComputeTemplateTreeBinds z s tree) :
      SemanticStrategy.ComputeTreeBinds z s
        (mapNTree (fun row => row.specialize α) tree) := by
    cases h with
    | @node rootS schildren rootT tchildren shape rowBinding children =>
        rw [mapNTree]
        exact .node shape (ComputeRowTemplate.bindsRow_specialize rowBinding)
          (computeTemplateChildrenSpecialize children)
  termination_by 2 * totalSize [tree]
  decreasing_by simp [totalSize, NTree.size]; omega

  /-- Ordered child-list specialization used by recursive compute binding. -/
  theorem computeTemplateChildrenSpecialize
      {z α : K}
      {ss : List (NTree SemanticStrategy.ComputeRowSkeleton)}
      {trees : List (NTree (ComputeRowTemplate (K := K)))}
      (h : List.Forall₂ (ComputeTemplateTreeBinds z) ss trees) :
      List.Forall₂ (SemanticStrategy.ComputeTreeBinds z) ss
        (trees.map (mapNTree (fun row => row.specialize α))) := by
    cases h with
    | nil => exact .nil
    | cons head tail =>
        exact .cons head.specialize (computeTemplateChildrenSpecialize tail)
  termination_by 2 * totalSize trees + 1
  decreasing_by
    simp_wf
    all_goals
      first
      | omega
      | exact totalSize_singleton_le_cons _ _
      | exact weighted_totalSize_tail_lt _ _
end

mutual
  /-- Recursive memory consistency specializes to the production recursive binding. -/
  theorem MemoryTemplateTreeBinds.specialize
      {z α lmb : K}
      {s : NTree SemanticStrategy.MemoryRowSkeleton}
      {tree : NTree (MemoryRowTemplate (K := K))}
      (h : MemoryTemplateTreeBinds z s tree) :
      SemanticStrategy.MemoryTreeBinds z s
        (mapNTree (fun row => row.specialize α lmb) tree) := by
    cases h with
    | @node rootS schildren rootT tchildren shape rowBinding children =>
        rw [mapNTree]
        exact .node shape (MemoryRowTemplate.bindsRow_specialize rowBinding)
          (memoryTemplateChildrenSpecialize children)
  termination_by 2 * totalSize [tree]
  decreasing_by simp [totalSize, NTree.size]; omega

  /-- Ordered child-list specialization used by recursive memory binding. -/
  theorem memoryTemplateChildrenSpecialize
      {z α lmb : K}
      {ss : List (NTree SemanticStrategy.MemoryRowSkeleton)}
      {trees : List (NTree (MemoryRowTemplate (K := K)))}
      (h : List.Forall₂ (MemoryTemplateTreeBinds z) ss trees) :
      List.Forall₂ (SemanticStrategy.MemoryTreeBinds z) ss
        (trees.map (mapNTree (fun row => row.specialize α lmb))) := by
    cases h with
    | nil => exact .nil
    | cons head tail =>
        exact .cons head.specialize (memoryTemplateChildrenSpecialize tail)
  termination_by 2 * totalSize trees + 1
  decreasing_by
    simp_wf
    all_goals
      first
      | omega
      | exact totalSize_singleton_le_cons _ _
      | exact weighted_totalSize_tail_lt _ _
end

/-- The sole post-seed semantic consistency certificate for an α-free execution template.
It is recursive row/topology evidence, not an opaque `BindsAt` or bridge equation. -/
structure TemplateSemanticConsistencyAt
    (z : K) (base : SemanticStrategy.SemanticSkeleton)
    (T : ExactConfigTemplate F K) (E : ExactExecutionTemplate T) : Prop where
  sampledSeed : T.challenges.z = z
  computeTree : ComputeTemplateTreeBinds z base.computeTree E.computeTree
  memoryForest :
    List.Forall₂ (MemoryTemplateTreeBinds z) base.memoryForest E.memoryForest

private theorem specializeMemoryTemplateForest
    {z α lmb : K} :
    ∀ {skeleton : List (NTree SemanticStrategy.MemoryRowSkeleton)}
      {forest : List (NTree (MemoryRowTemplate (K := K)))},
      List.Forall₂ (MemoryTemplateTreeBinds z) skeleton forest →
      List.Forall₂ (SemanticStrategy.MemoryTreeBinds z) skeleton
        (forest.map (mapNTree (fun row => row.specialize α lmb))) := by
  intro skeleton forest h
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.specialize ih

/-- Recursive template consistency constructs the complete production `BindsAt` at every `α`. -/
theorem TemplateSemanticConsistencyAt.specialize
    {z α lmb : K} {base : SemanticStrategy.SemanticSkeleton}
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T}
    (h : TemplateSemanticConsistencyAt z base T E) :
    SemanticStrategy.BindsAt z base (T.specialize α lmb) (E.specialize α lmb) :=
  SemanticStrategy.BindsAt.ofTreeBindings
    (by simpa [ExactConfigTemplate.specialize] using h.sampledSeed)
    h.computeTree.specialize
    (specializeMemoryTemplateForest h.memoryForest)

/-! ## Constructed carrier-level specialization -/

/-- Exact alignment between the committed timestamp rows and the BFS rows carried by a concrete
α-free execution template. -/
structure TimestampCarrierAlignment
    {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base)
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : Prop where
  compute :
    List.Forall₂
      (fun stamp row => stamp = row.timestamp)
      S.computeRows E.computeRows
  memory :
    List.Forall₂
      (fun stamp row => stamp = row.timestamp)
      S.memoryRows E.memoryRows

/-- The portion of specialization determined solely by the concrete config/row/tree constructors.
Unlike `TimestampSpecializesAt`, this contains no semantic binding or IO premise. -/
structure TimestampCarrierSpecializesAt
    (α lmb : K) {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base)
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : Prop where
  challengeEquation : (T.specialize α lmb).challenges.α = α
  computeTimestampEquations :
    List.Forall₂ (ComputeTimestampSpecializesAt α)
      S.computeRows (E.specialize α lmb).computeRows
  memoryTimestampEquations :
    List.Forall₂ (MemoryTimestampSpecializesAt α)
      S.memoryRows (E.specialize α lmb).memoryRows

private theorem forall₂_compute_specializes (α : K) :
    ∀ {stamps : List ComputeTimestampRow}
      {rows : List (ComputeRowTemplate (K := K))},
      List.Forall₂ (fun stamp row => stamp = row.timestamp) stamps rows →
        List.Forall₂ (ComputeTimestampSpecializesAt α) stamps
          (rows.map (fun row => row.specialize α)) := by
  intro stamps rows h
  induction h with
  | nil => exact .nil
  | cons head tail ih =>
      subst head
      exact .cons (ComputeRowTemplate.specializes _ α) ih

private theorem forall₂_compute_origin (α : K) :
    ∀ {stamps : List ComputeTimestampRow}
      {rows : List (ComputeRowTemplate (K := K))},
      List.Forall₂ (fun stamp row => stamp = row.timestamp) stamps rows →
      (∀ row ∈ rows,
        computeLineOrigin row.placeholder.2.1.α row.placeholder.2.2.1.ln_prev
          row.timestamp.lnPrevExponent = 1) →
      List.Forall₂ (fun stamp row =>
          row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
        stamps (rows.map (fun row => row.specialize α)) := by
  intro stamps rows h horigin
  induction h with
  | nil => exact .nil
  | cons head tail ih =>
      subst head
      refine .cons (ComputeRowTemplate.specialize_origin_one _ α (horigin _ (by simp))) ?_
      exact ih (fun r hr => horigin r (by simp [hr]))

private theorem forall₂_memory_specializes (α lmb : K) :
    ∀ {stamps : List MemoryTimestampRow}
      {rows : List (MemoryRowTemplate (K := K))},
      List.Forall₂ (fun stamp row => stamp = row.timestamp) stamps rows →
        List.Forall₂ (MemoryTimestampSpecializesAt α) stamps
          (rows.map (fun row => row.specialize α lmb)) := by
  intro stamps rows h
  induction h with
  | nil => exact .nil
  | cons head tail ih =>
      subst head
      exact .cons (MemoryRowTemplate.specializes _ α lmb) ih

/-- The config and dependent forest-first execution residual is discharged constructively:
`ExactConfig` and `ExactExecution` are explicit functions of `α`, and every timestamp equation
follows from row specialization plus BFS alignment. -/
theorem ExactExecutionTemplate.carrierSpecializesAt
    {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T}
    (alignment : TimestampCarrierAlignment S E) (α lmb : K) :
    TimestampCarrierSpecializesAt α lmb S E := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [E.specialize_computeRows]
    exact forall₂_compute_specializes α alignment.compute
  · rw [E.specialize_memoryRows]
    exact forall₂_memory_specializes α lmb alignment.memory

/-- The request bridge equation is forced by noun topology, recursive semantic binding, and the
constructed timestamp equations; no field-coordinate equation is assumed. -/
theorem semanticRequestBridgeEquation
    {z α : K} (hz : z ≠ 0)
    {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (binding : SemanticStrategy.BindsAt z base cfg exec)
    (timestamps :
      List.Forall₂ (ComputeTimestampSpecializesAt α)
        S.computeRows exec.computeRows)
    (horigin :
      List.Forall₂ (fun stamp row =>
        row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
        S.computeRows exec.computeRows) :
    bridgeRecords F K α cfg.challenges.lam (S.semanticRequestsAt z) =
      exec.derivedRequestIO := by
  have hge : ∀ stamp ∈ S.computeRows, ∀ i : Fin 3,
      (i : ℕ) < Nock.Framework.recordCount stamp.state →
        stamp.lnPrevExponent ≤ stamp.recordExponent i := by
    intro stamp hst i hi
    have hrec := S.computeRecordOffsets stamp hst i hi
    omega
  have hraw :=
    rawRequests_eq_semanticSlots hz S.computeTopology
      binding.computeRows timestamps horigin hge
  have htop :
      S.semanticRequests =
        (((SemanticStrategy.computeSkeletonRows base).zip S.computeRows).flatMap
          fun pair => computeRowRecordSlots pair.1 pair.2) := by
    simpa [computeRowRecordSlots] using S.requestTopology
  calc
    bridgeRecords F K α cfg.challenges.lam (S.semanticRequestsAt z) =
        S.semanticRequests.map (fun slot =>
          NockVM.encRecFormR
            (SemanticTimestampSkeleton.tableRecordAt z α slot)
            cfg.challenges.lam) := by
      simp [bridgeRecords, SemanticTimestampSkeleton.semanticRequestsAt,
        List.map_map, Function.comp_def,
        SemanticTimestampSkeleton.bridge_semanticRecordAt]
    _ = ((((SemanticStrategy.computeSkeletonRows base).zip S.computeRows).flatMap
          fun pair => computeRowRecordSlots pair.1 pair.2).map fun slot =>
            NockVM.encRecFormR
              (SemanticTimestampSkeleton.tableRecordAt z α slot)
              cfg.challenges.lam) := by
      rw [htop]
    _ = (exec.computeRows.flatMap fun row =>
          NockVM.activeRequestRecords row.2.2.1).map
            (fun r => NockVM.encRecFormR r cfg.challenges.lam) := by
      rw [hraw]
      simp [List.map_map, Function.comp_def]
    _ = exec.derivedRequestIO := by
      simp [ExactExecution.derivedRequestIO, ExactExecution.rawRequests]

/-- The response bridge equation: row-level memory rows (`BindMemRow`) serve the Form R
encoding of the canonical a-bearing `read_root` slots. -/
theorem semanticResponseBridgeEquation
    {z α : K}
    {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (binding : SemanticStrategy.BindsAt z base cfg exec)
    (timestamps :
      List.Forall₂ (MemoryTimestampSpecializesAt α)
        S.memoryRows exec.memoryRows)
    (hlam : ∀ row ∈ exec.memoryRows, row.2.2.lambda = cfg.challenges.lam) :
    bridgeRecords F K α cfg.challenges.lam (S.semanticResponsesAt z) =
      exec.derivedResponseIO := by
  have hraw :=
    rawResponses_eq_semanticSlots S.memoryTopology
      binding.memoryRows timestamps hlam
  have htop :
      S.semanticResponses =
        (((SemanticStrategy.memorySkeletonRows base).zip S.memoryRows).flatMap
          fun pair => memoryRowResponseSlots pair.1 pair.2) := by
    rw [S.responseTopology]
    let pairs :=
      (SemanticStrategy.memorySkeletonRows base).zip S.memoryRows
    change pairs.filterMap _ = pairs.flatMap _
    induction pairs with
    | nil => rfl
    | cons pair rest ih =>
        by_cases h : pair.1.state = .read_root
        · simp [memoryRowResponseSlots, h, ih]
        · simp [memoryRowResponseSlots, h, ih]
  calc
    bridgeRecords F K α cfg.challenges.lam (S.semanticResponsesAt z) =
        S.semanticResponses.map (fun slot =>
          NockVM.encRecFormR
            (SemanticTimestampSkeleton.tableRecordAt z α slot)
            cfg.challenges.lam) := by
      simp [bridgeRecords, SemanticTimestampSkeleton.semanticResponsesAt,
        List.map_map, Function.comp_def,
        SemanticTimestampSkeleton.bridge_semanticRecordAt]
    _ = ((((SemanticStrategy.memorySkeletonRows base).zip S.memoryRows).flatMap
          fun pair => memoryRowResponseSlots pair.1 pair.2).map fun slot =>
            NockVM.encRecFormR
              (SemanticTimestampSkeleton.tableRecordAt z α slot)
              cfg.challenges.lam) := by
      rw [htop]
    _ = exec.memoryRows.flatMap (fun row =>
          (MemoryTable.responseRecords row.2.2).map
            (fun r => NockVM.encRecC r row.2.2.cprime)) := hraw.symm
    _ = exec.derivedResponseIO := by
      unfold ExactExecution.derivedResponseIO
      congr 1
      funext row
      by_cases hver : row.2.2.ver = true <;> simp [MemoryTable.responseRecords, hver]

/-- Compile-checked residual for constructing a specialized execution from α-free data.

The carrier arguments `cfg` and `exec` are already present.  Thus this structure records only the
missing constructor equations; it does **not** contain `∃ cfg exec,...` or any desired existence
conclusion as a field. -/
structure SpecializationExistenceResidual
    (z α : K) {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base)
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop where
  challengeEquation : cfg.challenges.α = α
  semanticBinding : SemanticStrategy.BindsAt z base cfg exec
  computeTimestampEquations :
    List.Forall₂ (ComputeTimestampSpecializesAt α) S.computeRows exec.computeRows
  memoryTimestampEquations :
    List.Forall₂ (MemoryTimestampSpecializesAt α) S.memoryRows exec.memoryRows
  requestBridgeEquation :
    bridgeRecords F K α cfg.challenges.lam (S.semanticRequestsAt z) = exec.derivedRequestIO
  responseBridgeEquation :
    bridgeRecords F K α cfg.challenges.lam (S.semanticResponsesAt z) = exec.derivedResponseIO

/-- The exact specialization relation.  This name emphasizes its semantic use; its definition is
the explicit constructor residual above, not an assumed existence theorem. -/
abbrev TimestampSpecializesAt
    (z α : K) {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base)
    (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop :=
  SpecializationExistenceResidual z α S cfg exec

/-- Minimal semantic completion datum: recursive equality of template topology and noun-row
slots.  It is α-free and contains neither `BindsAt` nor any of the eight bridge coordinates. -/
abbrev SemanticCompletionResidual
    (z : K) {base : SemanticStrategy.SemanticSkeleton}
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) : Prop :=
  TemplateSemanticConsistencyAt z base T E

/-- Assemble the full specialization relation from the constructively discharged carrier part and
the recursive α-free semantic consistency.  Both bridge equations are theorems. -/
theorem TimestampCarrierSpecializesAt.toTimestampSpecializesAt
    {z α lmb : K} {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T}
    (hz : z ≠ 0)
    (carrier : TimestampCarrierSpecializesAt α lmb S E)
    (semantic : SemanticCompletionResidual (base := base) z E)
    (horigin :
      List.Forall₂ (fun stamp row =>
        row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
        S.computeRows (E.specialize α lmb).computeRows) :
    TimestampSpecializesAt z α S (T.specialize α lmb) (E.specialize α lmb) where
  challengeEquation := carrier.challengeEquation
  semanticBinding := semantic.specialize
  computeTimestampEquations := carrier.computeTimestampEquations
  memoryTimestampEquations := carrier.memoryTimestampEquations
  requestBridgeEquation :=
    semanticRequestBridgeEquation hz semantic.specialize
      carrier.computeTimestampEquations horigin
  responseBridgeEquation :=
    semanticResponseBridgeEquation semantic.specialize
      carrier.memoryTimestampEquations (E.specialize_memory_lambda α lmb)

/-- Full constructor from α-free carriers, recursive noun/topology consistency, nonzero `z`,
and honest origin `1` on the committed compute templates. -/
theorem ExactExecutionTemplate.specializesAt
    {z α lmb : K} {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    {T : ExactConfigTemplate F K} {E : ExactExecutionTemplate T}
    (hz : z ≠ 0)
    (alignment : TimestampCarrierAlignment S E)
    (semantic : SemanticCompletionResidual (base := base) z E)
    (horigin : ∀ row ∈ E.computeRows,
      computeLineOrigin row.placeholder.2.1.α row.placeholder.2.2.1.ln_prev
        row.timestamp.lnPrevExponent = 1) :
    TimestampSpecializesAt z α S (T.specialize α lmb) (E.specialize α lmb) :=
  (E.carrierSpecializesAt alignment α lmb).toTimestampSpecializesAt hz semantic
    (by
      rw [E.specialize_computeRows]
      exact forall₂_compute_origin α alignment.compute horigin)

namespace TimestampSpecializesAt

/-- Specialization pins the table challenge itself, not merely a walk-family parameter. -/
theorem tableAlpha
    {z α : K} {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TimestampSpecializesAt z α S cfg exec) :
    cfg.challenges.α = α :=
  h.challengeEquation

/-- Specialization preserves the complete noun/topology binding at the sampled NPR seed. -/
theorem bindsAt
    {z α : K} {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TimestampSpecializesAt z α S cfg exec) :
    SemanticStrategy.BindsAt z base cfg exec :=
  h.semanticBinding

/-- The two semantic lists map to the execution's actual canonical derived IO. -/
theorem recordBridge
    {z α : K} {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TimestampSpecializesAt z α S cfg exec) :
    bridgeRecords F K α cfg.challenges.lam (S.semanticRequestsAt z) = exec.derivedRequestIO ∧
      bridgeRecords F K α cfg.challenges.lam (S.semanticResponsesAt z) = exec.derivedResponseIO :=
  ⟨h.requestBridgeEquation, h.responseBridgeEquation⟩

omit [Algebra F K] in
/-- Distinct slot exponents make the semantic timestamp determine the record; this is what `SemanticIOPreimage.requestTimestamp_determines` consumes. -/
theorem semanticRecordsAt_timestamp_determines (z : K) (l : List CanonicalRecordSlot)
    (h : (l.map CanonicalRecordSlot.exponent).Nodup) :
    ∀ x ∈ l.map (SemanticTimestampSkeleton.semanticRecordAt (F := F) z),
      ∀ y ∈ l.map (SemanticTimestampSkeleton.semanticRecordAt (F := F) z),
      x.2.2 = y.2.2 → x = y := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  have hab : a = b := List.inj_on_of_nodup_map h ha hb (by simpa
      [SemanticTimestampSkeleton.semanticRecordAt] using hxy)
  rw [hab]

/-- Add the bounded semantic-language facts to obtain the production `SemanticIOPreimage`.
Specialization supplies both bridge equations, with its challenge equation rewriting the
production index from `cfg.challenges.α` to the sampled `α`. -/
def toSemanticIOPreimage
    {z α : K} {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TimestampSpecializesAt z α S cfg exec)
    (timestampBound : ℕ)
    (timestampBound_le_order : timestampBound ≤ orderOf α)
    (requestTimestampBound :
      ∀ r ∈ S.semanticRequestsAt z, r.2.2 < timestampBound)
    (responseTimestampBound :
      ∀ r ∈ S.semanticResponsesAt z, r.2.2 < timestampBound)
    (semantic_lmio :
      IO.LmIO cfg.Ksz (S.semanticRequestsAt z) (S.semanticResponsesAt z))
    (requestExponent_nodup :
      (S.semanticRequests.map CanonicalRecordSlot.exponent).Nodup) :
    SemanticIOPreimage cfg exec where
  timestampBound := timestampBound
  timestampBound_le_order := by
    simpa [h.challengeEquation] using timestampBound_le_order
  semanticRequests := S.semanticRequestsAt z
  semanticResponses := S.semanticResponsesAt z
  requestTimestampBound := requestTimestampBound
  responseTimestampBound := responseTimestampBound
  semantic_lmio := semantic_lmio
  requestTimestamp_determines :=
    semanticRecordsAt_timestamp_determines z S.semanticRequests requestExponent_nodup
  requests_bridge := by
    simpa [h.challengeEquation] using h.requestBridgeEquation
  responses_bridge := by
    simpa [h.challengeEquation] using h.responseBridgeEquation

/-- Compatibility with the public `SemanticIOPreimage`/`RecordBridge` connector. -/
theorem semanticIOPreimage_maps
    {z α : K} {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : TimestampSpecializesAt z α S cfg exec)
    (timestampBound : ℕ)
    (timestampBound_le_order : timestampBound ≤ orderOf α)
    (requestTimestampBound :
      ∀ r ∈ S.semanticRequestsAt z, r.2.2 < timestampBound)
    (responseTimestampBound :
      ∀ r ∈ S.semanticResponsesAt z, r.2.2 < timestampBound)
    (semantic_lmio :
      IO.LmIO cfg.Ksz (S.semanticRequestsAt z) (S.semanticResponsesAt z)) :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam (S.semanticRequestsAt z) = exec.derivedRequestIO ∧
      bridgeRecords F K cfg.challenges.α cfg.challenges.lam (S.semanticResponsesAt z) = exec.derivedResponseIO :=
  ⟨by simpa [h.challengeEquation] using h.requestBridgeEquation,
    by simpa [h.challengeEquation] using h.responseBridgeEquation⟩

end TimestampSpecializesAt

/-! ## Challenge-ordered strategy shell -/

/-- One full exact carrier selected only after `α`, certified as a specialization of the fixed
pre-α commitment.  Remaining non-timestamp arrays live in `cfg` and `exec`; their α-dependent
timestamp columns are constrained by `specializes`. -/
structure SpecializedFamilyAt
    (z α lmb : K) {base : SemanticStrategy.SemanticSkeleton}
    (S : SemanticTimestampSkeleton F K base) where
  cfg : ExactConfig F K
  exec : ExactExecution cfg
  specializes : TimestampSpecializesAt z α S cfg exec
  /-- The selected configuration carries the sampled Form R `λ` of the same round. -/
  sampledLambda : cfg.challenges.lam = lmb

namespace SpecializedFamilyAt

/-- The table challenge selected by a specialized family. -/
def specializedAlpha
    {z α lmb : K} {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    (P : SpecializedFamilyAt z α lmb S) : K :=
  P.cfg.challenges.α

@[simp]
theorem specializedAlpha_eq
    {z α lmb : K} {base : SemanticStrategy.SemanticSkeleton}
    {S : SemanticTimestampSkeleton F K base}
    (P : SpecializedFamilyAt z α lmb S) :
    P.specializedAlpha = α :=
  P.specializes.tableAlpha

end SpecializedFamilyAt

/-! ## Production chronology: complete carrier templates fixed after `z` -/

/-- Data-only carrier committed after nonzero `z`.  This is the production raw chronology:
the complete configuration/execution templates are fixed, and the sole proposition is the phase
equation identifying the committed seed.  There is no semantic skeleton, timestamp alignment,
semantic consistency certificate, `BindsAt`, bridge equation, evaluator, or target. -/
structure DataOnlySeedFixedTimestampCarrier (z : K) where
  configTemplate : ExactConfigTemplate F K
  executionTemplate : ExactExecutionTemplate configTemplate
  sampledSeed : configTemplate.challenges.z = z

/-- Data-only production timestamp strategy.  The public claim is fixed before `z`; the complete
raw carrier templates are fixed after `z`; specialization later inserts only `alphaM`. -/
structure DataOnlyTemplateFixedStagedTimestampStrategy where
  claim : P8PublicClaim
  afterSeed :
    ∀ seed : { z : K // z ≠ 0 },
      DataOnlySeedFixedTimestampCarrier (F := F) (K := K) seed.1

namespace DataOnlyTemplateFixedStagedTimestampStrategy

/-- Data-only inhabitant factory.  Supplying a public claim, raw templates, and the seed phase
equation is sufficient; no semantic object or proposition appears in the constructor signature. -/
def ofRawData
    (claim : P8PublicClaim)
    (configAfterSeed :
      ∀ seed : { z : K // z ≠ 0 }, ExactConfigTemplate F K)
    (executionAfterSeed :
      ∀ seed : { z : K // z ≠ 0 },
        ExactExecutionTemplate (configAfterSeed seed))
    (sampledSeed :
      ∀ seed : { z : K // z ≠ 0 },
        (configAfterSeed seed).challenges.z = seed.1) :
    DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K) where
  claim := claim
  afterSeed := fun seed =>
    { configTemplate := configAfterSeed seed
      executionTemplate := executionAfterSeed seed
      sampledSeed := sampledSeed seed }

/-- Exact constructor-shape regression: these are all fields of the raw timestamp strategy. -/
theorem eta
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)) :
    T =
      { claim := T.claim
        afterSeed := T.afterSeed } :=
  rfl

/-- The unique data-only seed commitment selected by a joint coin. -/
def seedCommitment
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) :
    DataOnlySeedFixedTimestampCarrier (F := F) (K := K) (nprSeed ω) :=
  T.afterSeed ⟨nprSeed ω, hz⟩

/-- The raw configuration is the seed-fixed template specialized only at the sampled
`(alphaM, λ)` of one round. -/
def cfgAt
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) : ExactConfig F K :=
  (T.seedCommitment ω hz).configTemplate.specialize (alphaM ω) lmb

/-- The raw execution is the same seed-fixed template specialized only at the sampled
`(alphaM, λ)`. -/
def execAt
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    ExactExecution (T.cfgAt ω lmb hz) :=
  (T.seedCommitment ω hz).executionTemplate.specialize (alphaM ω) lmb

@[simp] theorem tableAlpha_eq_alphaM
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    (T.cfgAt ω lmb hz).challenges.α = alphaM ω :=
  rfl

@[simp] theorem tableLam_eq_sampled
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    (T.cfgAt ω lmb hz).challenges.lam = lmb :=
  rfl

@[simp] theorem sampledSeed
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) :
    (T.afterSeed ⟨z, hz⟩).configTemplate.challenges.z = z :=
  (T.afterSeed ⟨z, hz⟩).sampledSeed

end DataOnlyTemplateFixedStagedTimestampStrategy

/-- Everything determining the semantic exact carrier, committed after nonzero `z` and before
`alphaM`.  The dependent execution, timestamp alignment, and recursive noun consistency all refer
to these exact templates; there is no field for a later carrier choice. -/
structure SeedFixedTimestampCarrier
    (base : SemanticStrategy.SemanticSkeleton) (z : K) where
  timestampSkeleton : SemanticTimestampSkeleton F K base
  configTemplate : ExactConfigTemplate F K
  executionTemplate : ExactExecutionTemplate configTemplate
  carrierAlignment :
    TimestampCarrierAlignment timestampSkeleton executionTemplate
  semanticConsistency :
    TemplateSemanticConsistencyAt z base configTemplate executionTemplate
  /-- Honest origin `1`: each committed compute placeholder already satisfies
  `ln_prev = α^e` at its own `α`.  Required for the request/response LogUp
  match (`tableRecordAt` is the closed form `α^e`); `V_comp` does not check it. -/
  originOne : ∀ row ∈ executionTemplate.computeRows,
    computeLineOrigin row.placeholder.2.1.α row.placeholder.2.2.1.ln_prev
      row.timestamp.lnPrevExponent = 1

/-- Production staged strategy.  After `z`, the entire semantic carrier template is fixed.
There is deliberately no `afterFull` field. -/
structure TemplateFixedStagedTimestampStrategy where
  base : SemanticStrategy.SemanticSkeleton
  afterSeed :
    ∀ seed : { z : K // z ≠ 0 },
      SeedFixedTimestampCarrier (F := F) (K := K) base seed.1

/-- Forget semantic certification and retain exactly the data/phase commitments accepted by the
production raw chronology. -/
def TemplateFixedStagedTimestampStrategy.toDataOnly
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K)) :
    DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K) where
  claim := T.base.publicClaim
  afterSeed := fun seed =>
    { configTemplate := (T.afterSeed seed).configTemplate
      executionTemplate := (T.afterSeed seed).executionTemplate
      sampledSeed := (T.afterSeed seed).semanticConsistency.sampledSeed }

private theorem dependentApply_heq
    {A : Type*} {B : A → Sort*} (f : ∀ a, B a)
    {a b : A} (h : a = b) : HEq (f a) (f b) := by
  subst b
  rfl

namespace TemplateFixedStagedTimestampStrategy

/-- The unique seed commitment used at a joint coin. -/
def seedCommitment
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (hz : nprSeed ω ≠ 0) :
    SeedFixedTimestampCarrier (F := F) (K := K) T.base (nprSeed ω) :=
  T.afterSeed ⟨nprSeed ω, hz⟩

/-- The production configuration is definitionally the seed template specialized at the sampled
`(alphaM, λ)`. -/
def cfgAt
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) : ExactConfig F K :=
  (T.seedCommitment ω hz).configTemplate.specialize (alphaM ω) lmb

/-- The production execution is definitionally the same seed template specialized at the
sampled `(alphaM, λ)`. -/
def execAt
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    ExactExecution (T.cfgAt ω lmb hz) :=
  (T.seedCommitment ω hz).executionTemplate.specialize (alphaM ω) lmb

/-- Full specialization follows only from fields of the seed commitment. -/
theorem timestampSpecializesAt
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    TimestampSpecializesAt
      (nprSeed ω) (alphaM ω)
      (T.seedCommitment ω hz).timestampSkeleton
      (T.cfgAt ω lmb hz) (T.execAt ω lmb hz) :=
  (T.seedCommitment ω hz).executionTemplate.specializesAt hz
    (T.seedCommitment ω hz).carrierAlignment
    (T.seedCommitment ω hz).semanticConsistency
    (T.seedCommitment ω hz).originOne

/-- Exact sampled diagonal; no equality premise or post-full selection is present. -/
@[simp] theorem tableAlpha_eq_alphaM
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    (T.cfgAt ω lmb hz).challenges.α = alphaM ω :=
  (T.timestampSpecializesAt ω lmb hz).tableAlpha

/-- The sampled specialization retains the complete recursive noun binding. -/
theorem bindsAt
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    SemanticStrategy.BindsAt
      (nprSeed ω) T.base (T.cfgAt ω lmb hz) (T.execAt ω lmb hz) :=
  (T.timestampSpecializesAt ω lmb hz).bindsAt

/-- Both semantic IO bridges are generated from the seed-fixed noun/timestamp topology. -/
theorem recordBridges
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    bridgeRecords F K (alphaM ω) (T.cfgAt ω lmb hz).challenges.lam
        ((T.seedCommitment ω hz).timestampSkeleton.semanticRequestsAt (nprSeed ω)) =
        (T.execAt ω lmb hz).derivedRequestIO ∧
      bridgeRecords F K (alphaM ω) (T.cfgAt ω lmb hz).challenges.lam
        ((T.seedCommitment ω hz).timestampSkeleton.semanticResponsesAt (nprSeed ω)) =
        (T.execAt ω lmb hz).derivedResponseIO :=
  (T.timestampSpecializesAt ω lmb hz).recordBridge

/-- Same-seed commitments are heterogeneous-equal even when presented with different joint coins
and different proofs of seed nonzeroness.  Consequently every field of the timestamp skeleton,
config template, execution template, alignment, and semantic consistency certificate is shared. -/
theorem seedCommitment_heq_of_sameSeed
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω₁ ω₂ : JointCoins K)
    (hz₁ : nprSeed ω₁ ≠ 0) (hz₂ : nprSeed ω₂ ≠ 0)
    (hseed : nprSeed ω₁ = nprSeed ω₂) :
    HEq (T.seedCommitment ω₁ hz₁) (T.seedCommitment ω₂ hz₂) := by
  let seed₁ : { z : K // z ≠ 0 } := ⟨nprSeed ω₁, hz₁⟩
  let seed₂ : { z : K // z ≠ 0 } := ⟨nprSeed ω₂, hz₂⟩
  have hseeds : seed₁ = seed₂ := Subtype.ext hseed
  change HEq (T.afterSeed seed₁) (T.afterSeed seed₂)
  exact dependentApply_heq T.afterSeed hseeds

/-- Complete same-seed non-splicing receipt.  Equality of the entire seed package gives, in
particular, every non-timestamp row, witness, topology, geometry, and alignment coordinate.
The two carriers are then definitionally obtained by supplying only their respective `alphaM`
values to the shared specialization functions. -/
structure SameSeedNonSplicing
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω₁ ω₂ : JointCoins K) (lmb₁ lmb₂ : K)
    (hz₁ : nprSeed ω₁ ≠ 0) (hz₂ : nprSeed ω₂ ≠ 0)
    (hseed : nprSeed ω₁ = nprSeed ω₂) : Prop where
  commitmentShared :
    HEq (T.seedCommitment ω₁ hz₁) (T.seedCommitment ω₂ hz₂)
  timestampSkeletonShared :
    HEq (T.seedCommitment ω₁ hz₁).timestampSkeleton
      (T.seedCommitment ω₂ hz₂).timestampSkeleton
  configTemplateShared :
    HEq (T.seedCommitment ω₁ hz₁).configTemplate
      (T.seedCommitment ω₂ hz₂).configTemplate
  executionTemplateShared :
    HEq (T.seedCommitment ω₁ hz₁).executionTemplate
      (T.seedCommitment ω₂ hz₂).executionTemplate
  carrierAlignmentShared :
    HEq (T.seedCommitment ω₁ hz₁).carrierAlignment
      (T.seedCommitment ω₂ hz₂).carrierAlignment
  semanticConsistencyShared :
    HEq (T.seedCommitment ω₁ hz₁).semanticConsistency
      (T.seedCommitment ω₂ hz₂).semanticConsistency
  leftConfigGenerated :
    T.cfgAt ω₁ lmb₁ hz₁ =
      (T.seedCommitment ω₁ hz₁).configTemplate.specialize (alphaM ω₁) lmb₁
  rightConfigGenerated :
    T.cfgAt ω₂ lmb₂ hz₂ =
      (T.seedCommitment ω₂ hz₂).configTemplate.specialize (alphaM ω₂) lmb₂
  leftExecutionGenerated :
    HEq (T.execAt ω₁ lmb₁ hz₁)
      ((T.seedCommitment ω₁ hz₁).executionTemplate.specialize (alphaM ω₁) lmb₁)
  rightExecutionGenerated :
    HEq (T.execAt ω₂ lmb₂ hz₂)
      ((T.seedCommitment ω₂ hz₂).executionTemplate.specialize (alphaM ω₂) lmb₂)

/-- Same-seed non-splicing is forced by the production strategy type. -/
theorem sameSeed_nonSplicing
    (T : TemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (ω₁ ω₂ : JointCoins K) (lmb₁ lmb₂ : K)
    (hz₁ : nprSeed ω₁ ≠ 0) (hz₂ : nprSeed ω₂ ≠ 0)
    (hseed : nprSeed ω₁ = nprSeed ω₂) :
    SameSeedNonSplicing T ω₁ ω₂ lmb₁ lmb₂ hz₁ hz₂ hseed := by
  let seed₁ : { z : K // z ≠ 0 } := ⟨nprSeed ω₁, hz₁⟩
  let seed₂ : { z : K // z ≠ 0 } := ⟨nprSeed ω₂, hz₂⟩
  have hseeds : seed₁ = seed₂ := Subtype.ext hseed
  refine ⟨T.seedCommitment_heq_of_sameSeed ω₁ ω₂ hz₁ hz₂ hseed, ?_, ?_,
    ?_, ?_, ?_, rfl, rfl, HEq.rfl, HEq.rfl⟩
  · change HEq (T.afterSeed seed₁).timestampSkeleton
      (T.afterSeed seed₂).timestampSkeleton
    exact dependentApply_heq
      (fun seed => (T.afterSeed seed).timestampSkeleton) hseeds
  · change HEq (T.afterSeed seed₁).configTemplate
      (T.afterSeed seed₂).configTemplate
    exact dependentApply_heq
      (fun seed => (T.afterSeed seed).configTemplate) hseeds
  · change HEq (T.afterSeed seed₁).executionTemplate
      (T.afterSeed seed₂).executionTemplate
    exact dependentApply_heq
      (fun seed => (T.afterSeed seed).executionTemplate) hseeds
  · change HEq (T.afterSeed seed₁).carrierAlignment
      (T.afterSeed seed₂).carrierAlignment
    exact dependentApply_heq
      (fun seed => (T.afterSeed seed).carrierAlignment) hseeds
  · change HEq (T.afterSeed seed₁).semanticConsistency
      (T.afterSeed seed₂).semanticConsistency
    exact dependentApply_heq
      (fun seed => (T.afterSeed seed).semanticConsistency) hseeds

end TemplateFixedStagedTimestampStrategy

/-! ## Regenerated-label counting boundary -/

/-- Exact polynomial obligation created by reusing `alphaM` both to regenerate timestamp-bearing
memory labels and as the memory-walk challenge.  It does not claim the fixed-label walk bound:
the integrator must provide coordinate polynomials for the complete 32-coordinate encoder and a
counted bad set for the resulting composed failure predicate. -/
structure RegeneratedMemoryLabelCountingObligation
    {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T)
    (hchar : NodeEncoding.StateTagChar K)
    (lmb : K)
    (memoryWalkFails : K → Prop) where
  coordinateDegreeBound : ℕ
  coordinatePolynomial :
    ∀ row, row ∈ E.memoryRows →
      Fin NodeEncoding.memoryNodeWidth → Polynomial K
  coordinatePolynomial_eval :
    ∀ row (hrow : row ∈ E.memoryRows)
      (j : Fin NodeEncoding.memoryNodeWidth) (α : K),
      (coordinatePolynomial row hrow j).eval α =
        NodeEncoding.memoryNodeEncode hchar (row.specialize α lmb) j
  coordinatePolynomial_degree :
    ∀ row (hrow : row ∈ E.memoryRows)
      (j : Fin NodeEncoding.memoryNodeWidth),
      (coordinatePolynomial row hrow j).natDegree ≤ coordinateDegreeBound
  composedDegreeBound : ℕ
  badAlphas : Finset K
  failure_mem_badAlphas : ∀ α, memoryWalkFails α → α ∈ badAlphas
  badAlphas_card : badAlphas.card ≤ composedDegreeBound

/-- Exact number of regenerated complete memory-label coordinates that the polynomial receipt
must cover. -/
def regeneratedMemoryCoordinateCount
    {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) : ℕ :=
  E.memoryRows.length * NodeEncoding.memoryNodeWidth

/-- The exact coordinate count is the committed memory-row count times the complete encoder width
(`32`), with no hidden post-coin labels. -/
theorem regeneratedMemoryCoordinateCount_eq
    {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) :
    regeneratedMemoryCoordinateCount E =
      T.memRows * NodeEncoding.memoryNodeWidth := by
  unfold regeneratedMemoryCoordinateCount ExactExecutionTemplate.memoryRows
  rw [List.length_map, E.memory_bfs_length]


/-- It permits a post-full carrier choice and must not be used as the
production chronology; use `TemplateFixedStagedTimestampStrategy`. -/
structure StagedTimestampStrategy where
  base : SemanticStrategy.SemanticSkeleton
  afterSeed :
    ∀ z : K, z ≠ 0 → SemanticTimestampSkeleton F K base
  afterFull :
    ∀ (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0),
      SpecializedFamilyAt
        (nprSeed ω) (alphaM ω) lmb (afterSeed (nprSeed ω) hz)

namespace StagedTimestampStrategy

/-- The exact configuration selected on the full sampled coin. -/
def cfgAt
    (T : StagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) : ExactConfig F K :=
  (T.afterFull ω lmb hz).cfg

/-- The exact execution selected on the full sampled coin. -/
def execAt
    (T : StagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    ExactExecution (T.cfgAt ω lmb hz) :=
  (T.afterFull ω lmb hz).exec

/-- Exact diagonal in the orientation used by specialization.  No equality premise is supplied. -/
@[simp]
theorem specialized_eq_alphaM
    (T : StagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    (T.afterFull ω lmb hz).specializedAlpha = alphaM ω :=
  (T.afterFull ω lmb hz).specializedAlpha_eq

/-- Exact diagonal in the orientation consumed by
`exactAxisRefinement_P8AxisContainment`. -/
theorem exactAxisDiagonal
    (T : StagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    alphaM ω = (T.cfgAt ω lmb hz).challenges.α :=
  (T.afterFull ω lmb hz).specializes.tableAlpha.symm

/-- The specialization at a sampled coin retains the seed-time semantic binding. -/
theorem bindsAtSample
    (T : StagedTimestampStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    SemanticStrategy.BindsAt
      (nprSeed ω) T.base (T.cfgAt ω lmb hz) (T.execAt ω lmb hz) :=
  (T.afterFull ω lmb hz).specializes.bindsAt

end StagedTimestampStrategy

/-! ## Cardinal geometry -/

/-- This staged interface samples the existing joint space verbatim; it introduces no fifth coin
and makes no seed-only lift claim. -/
abbrev TimestampJointCoins (K : Type*) := JointCoins K

omit [Field K] in
/-- Cardinal receipt: the strategy remains on exactly four field coordinates. -/
theorem card_timestampJointCoins [Fintype K] :
    Fintype.card (TimestampJointCoins K) = Fintype.card K ^ 4 :=
  card_jointCoins

end

end Nock.NockVMROM.Thm54.SemanticTimestampStrategy

#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.SemanticTimestampSkeleton.computeRows_length
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.SemanticTimestampSkeleton.bridge_semanticRecordAt
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactConfigTemplate.specialize_alpha
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ComputeRowTemplate.bindsRow_specialize
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.bindsRow_specialize
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TemplateSemanticConsistencyAt.specialize
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactExecutionTemplate.carrierSpecializesAt
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.semanticRequestBridgeEquation
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.semanticResponseBridgeEquation
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactExecutionTemplate.specializesAt
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TimestampSpecializesAt.tableAlpha
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TimestampSpecializesAt.bindsAt
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TimestampSpecializesAt.recordBridge
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TimestampSpecializesAt.semanticIOPreimage_maps
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.SpecializedFamilyAt.specializedAlpha_eq
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy.eta
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy.tableAlpha_eq_alphaM
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy.sampledSeed
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TemplateFixedStagedTimestampStrategy.timestampSpecializesAt
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TemplateFixedStagedTimestampStrategy.tableAlpha_eq_alphaM
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TemplateFixedStagedTimestampStrategy.bindsAt
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TemplateFixedStagedTimestampStrategy.recordBridges
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TemplateFixedStagedTimestampStrategy.seedCommitment_heq_of_sameSeed
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.TemplateFixedStagedTimestampStrategy.sameSeed_nonSplicing
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.regeneratedMemoryCoordinateCount_eq
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.StagedTimestampStrategy.specialized_eq_alphaM
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.StagedTimestampStrategy.exactAxisDiagonal
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.StagedTimestampStrategy.bindsAtSample
#print axioms Nock.NockVMROM.Thm54.SemanticTimestampStrategy.card_timestampJointCoins
