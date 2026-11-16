import Nock.NMRMEF
import Nock.NockVM

/-!
# Exact Theorem 5.4 semantic-record bridge

The semantic axis lies in `F`, while the compute/memory tables are over `K`; the exact
conversion is therefore `algebraMap F K`, under `[Algebra F K]`.  The semantic timestamp
exponent is realized as `β ^ k` by the existing `nmrEncoding`, and the resulting table record
is flattened only by the stable `NockVM.encRec` API.

No global injectivity of this bridge is claimed.  In particular, powers of `β` need only be
injective on the bounded timestamp window used by an execution.  The list-level uniqueness
lemmas below consequently take injectivity on the actual source list as an explicit hypothesis.
-/

namespace Nock.NockVMROM.Thm54

open ComputeTable MemoryTable
open scoped Classical

/-- Convert a field-timestamped NMR record to the table's uniform-`K` memory record.

The fingerprints and timestamp already lie in `K`; the semantic axis is embedded with
`algebraMap F K`.  Thus this conversion requires an algebra structure, not an identification
`F = K`. -/
def memRecOfNMR (F K : Type) [Field F] [Field K] [Algebra F K]
    (r : NMR.Rec F K) : ComputeTable.MemRec K :=
  { root := ⟨r.root_fn.1, r.root_fn.2.1, r.root_fn.2.2⟩
    child := ⟨r.child_fn.1, r.child_fn.2.1, r.child_fn.2.2⟩
    axis := algebraMap F K r.axis
    ts := r.timestamp }

/-- Total semantic-record bridge to the nine coordinates consumed by the IO layer: the single
    Form R encode (`NockVM.encRecFormR`) of the a-bearing table image at the honest-package `λ`.
    `(T, C')` exist only here (and in the generator's row build), from the same Nock axis. -/
noncomputable def bridge (F K : Type) [Field F] [Field K] [Algebra F K] (β lmb : K)
    (r : (nmrMEF F K).Rec) : Fin 9 → K :=
  NockVM.encRecFormR (memRecOfNMR F K ((nmrEncoding F K β).encode r)) lmb

/-- The stable per-record assembly equation, independent of request/response row extraction. -/
@[simp]
theorem d2_record_bridge_agrees (F K : Type) [Field F] [Field K] [Algebra F K]
    (β lmb : K) (r : (nmrMEF F K).Rec) :
    NockVM.encRecFormR (memRecOfNMR F K ((nmrEncoding F K β).encode r))
        lmb =
      bridge F K β lmb r :=
  rfl

/-- Coordinate specification of the total bridge.  Coordinate `6` is Form R `T`, coordinate `7`
the realized semantic timestamp, coordinate `8` Form R `C'` — both from the embedded Nock axis at
the honest-package `λ`. -/
theorem bridge_coordinates (F K : Type) [Field F] [Field K] [Algebra F K] (β lmb : K)
    (r : (nmrMEF F K).Rec) :
    bridge F K β lmb r =
      ![r.2.1.1.1, r.2.1.1.2.1, r.2.1.1.2.2,
        r.2.1.2.1, r.2.1.2.2.1, r.2.1.2.2.2,
        MemoryTable.formRT lmb (MemoryTable.nockAxisOf (algebraMap F K r.1)),
        β ^ r.2.2,
        MemoryTable.formRC lmb (MemoryTable.nockAxisOf (algebraMap F K r.1))]
            := by
  funext i
  fin_cases i <;> rfl

/-- A one-row memory-table labeling whose row state is `read_root` and whose live record is
the table image of `r`.  Non-response columns are set to zero. -/
noncomputable def readRootLabel (F K : Type) [Field F] [Field K] [Algebra F K] (β lmb : K)
    (r : (nmrMEF F K).Rec) : ℕ → MState × MemoryTable.DTmem K :=
  fun _ =>
    (.read_root,
      ({ z := 0, β := 0, γ := 0 },
       { st := .read_root
         pt := Cell.zero
         lc := Cell.zero
         rc := Cell.zero
         lcSt := .read_root
         rcSt := .halt
         mem := { memRecOfNMR F K ((nmrEncoding F K β).encode r) with
           axis := MemoryTable.formRT lmb
             (MemoryTable.nockAxisOf (memRecOfNMR F K ((nmrEncoding F K β).encode r)).axis) }
         ipre := 0
         icur := 0
         cprime? := some (MemoryTable.formRC lmb
           (MemoryTable.nockAxisOf (memRecOfNMR F K ((nmrEncoding F K β).encode r)).axis)) }))

/-- On the concrete `read_root` row, the actual response extractor returns exactly the
semantic bridge record. -/
theorem d2_bridge_agrees (F K : Type) [Field F] [Field K] [Algebra F K] (β lmb : K)
    (r : (nmrMEF F K).Rec) :
    NockVM.respRecs (readRootLabel F K β lmb r) 1 = [bridge F K β lmb r] := by
  rfl

/-- Changing the realized timestamp changes the encoded record.  This is deliberately phrased
in terms of unequal powers: such discrimination is only automatic on a faithful power window. -/
theorem bridge_timestamp_discriminates (F K : Type) [Field F] [Field K] [Algebra F K]
    (β lmb : K) (r s : (nmrMEF F K).Rec)
    (htime : β ^ r.2.2 ≠ β ^ s.2.2) :
    bridge F K β lmb r ≠ bridge F K β lmb s := by
  intro h
  apply htime
  have h7 := congrFun h (7 : Fin 9)
  simpa [bridge, memRecOfNMR, NockVM.encRecFormR, NockVM.encRecC, nmrEncoding] using h7

/-- **Timestamp separation (Form R).**  On a list whose records lie in a faithful power window
and whose timestamp exponent determines the record,
the Form R bridge is injective.  Form R alone is not: axes `0` and `1` encode identically at every
`λ` (`Batch590.formR_zero_one_collide`); the timestamp slot separates distinct records. -/
theorem bridge_injOn_of_timestamps
    (F K : Type) [Field F] [Field K] [Algebra F K] (β lmb : K)
    {B : ℕ} (hB : B ≤ orderOf β) (rs : List ((nmrMEF F K).Rec))
    (hbound : ∀ r ∈ rs, r.2.2 < B)
    (hdet : ∀ x ∈ rs, ∀ y ∈ rs, x.2.2 = y.2.2 → x = y) :
    ∀ x ∈ rs, ∀ y ∈ rs, bridge F K β lmb x = bridge F K β lmb y → x = y := by
  intro x hx y hy h
  apply hdet x hx y hy
  have h7 : β ^ x.2.2 = β ^ y.2.2 := by
    simpa [bridge, memRecOfNMR, NockVM.encRecFormR, NockVM.encRecC, nmrEncoding] using
      congrFun h (7 : Fin 9)
  exact pow_injOn_Iio_orderOf
    (Set.mem_Iio.mpr (lt_of_lt_of_le (hbound x hx) hB))
    (Set.mem_Iio.mpr (lt_of_lt_of_le (hbound y hy) hB)) h7

/-! ## List-level connectors -/

/-- Map a semantic record list to the encoded list consumed by the IO layer. -/
noncomputable def bridgeRecords (F K : Type) [Field F] [Field K] [Algebra F K] (β lmb : K)
    (rs : List ((nmrMEF F K).Rec)) : List (Fin 9 → K) :=
  rs.map (bridge F K β lmb)

/-- Encoding records does not change list length. -/
@[simp]
theorem bridgeRecords_length (F K : Type) [Field F] [Field K] [Algebra F K]
    (β lmb : K) (rs : List ((nmrMEF F K).Rec)) :
    (bridgeRecords F K β lmb rs).length = rs.length := by
  simp [bridgeRecords]

/-- The IO range condition is unchanged by record encoding. -/
@[simp]
theorem bridgeRecords_inRange_iff (F K : Type) [Field F] [Field K] [Algebra F K]
    (Ksz : ℕ) (β lmb : K) (rs : List ((nmrMEF F K).Rec)) :
    IO.InRange Ksz (bridgeRecords F K β lmb rs).length ↔ IO.InRange Ksz rs.length := by
  simp [bridgeRecords]

/-- Mapping preserves `Nodup` when the bridge is injective on the actual source list. -/
theorem bridgeRecords_nodup_of_injOn
    (F K : Type) [Field F] [Field K] [Algebra F K] (β lmb : K)
    (rs : List ((nmrMEF F K).Rec))
    (hinj : ∀ x ∈ rs, ∀ y ∈ rs, bridge F K β lmb x = bridge F K β lmb y → x = y)
    (hnd : rs.Nodup) :
    (bridgeRecords F K β lmb rs).Nodup := by
  exact hnd.map_on hinj

/-- A bounded timestamp window discharges the local injectivity premise needed to preserve
`Nodup`. -/
theorem bridgeRecords_nodup_of_timestamp_bound
    (F K : Type) [Field F] [Field K] [Algebra F K] (β lmb : K)
    {B : ℕ} (hB : B ≤ orderOf β)
    (rs : List ((nmrMEF F K).Rec))
    (hbound : ∀ r ∈ rs, r.2.2 < B)
    (hdet : ∀ x ∈ rs, ∀ y ∈ rs, x.2.2 = y.2.2 → x = y)
    (hnd : rs.Nodup) :
    (bridgeRecords F K β lmb rs).Nodup :=
  bridgeRecords_nodup_of_injOn F K β lmb rs
    (bridge_injOn_of_timestamps F K β lmb hB rs hbound hdet) hnd

/-- Under injectivity on the source list, semantic and encoded `Nodup` are equivalent. -/
theorem bridgeRecords_nodup_iff
    (F K : Type) [Field F] [Field K] [Algebra F K] (β lmb : K)
    (rs : List ((nmrMEF F K).Rec))
    (hinj : ∀ x ∈ rs, ∀ y ∈ rs, bridge F K β lmb x = bridge F K β lmb y → x = y) :
    (bridgeRecords F K β lmb rs).Nodup ↔ rs.Nodup := by
  constructor
  · exact List.Nodup.of_map (bridge F K β lmb)
  · exact bridgeRecords_nodup_of_injOn F K β lmb rs hinj

/-- A semantic permutation remains a permutation after encoding. -/
theorem bridgeRecords_perm
    (F K : Type) [Field F] [Field K] [Algebra F K] (β lmb : K)
    {rs ss : List ((nmrMEF F K).Rec)} (h : rs.Perm ss) :
    (bridgeRecords F K β lmb rs).Perm (bridgeRecords F K β lmb ss) := by
  exact h.map (bridge F K β lmb)

/-- `LmIO` is preserved by record encoding when the bridge is injective on the semantic
request set.  Request multiplicity is preserved: no request `Nodup` assumption is made.

The request-set hypothesis is sufficient for response uniqueness because semantic `LmIO`
identifies the response set with the request set. -/
theorem bridgeRecords_LmIO_of_injOn
    (F K : Type) [Field F] [Field K] [Algebra F K] (Ksz : ℕ) (β lmb : K)
    {req resp : List ((nmrMEF F K).Rec)}
    (hinj : ∀ x ∈ req, ∀ y ∈ req, bridge F K β lmb x = bridge F K β lmb y → x = y)
    (h : IO.LmIO Ksz req resp) :
    IO.LmIO Ksz (bridgeRecords F K β lmb req) (bridgeRecords F K β lmb resp) := by
  obtain ⟨hrange, uniq, hlen, hnd, hmem, hperm⟩ := h
  refine ⟨bridgeRecords_inRange_iff F K Ksz β lmb req |>.2 hrange,
    bridgeRecords F K β lmb uniq, ?_, ?_, ?_, bridgeRecords_perm F K β lmb hperm⟩
  · simpa using hlen
  · apply bridgeRecords_nodup_of_injOn F K β lmb uniq
    · intro x hx y hy hxy
      exact hinj x ((hmem x).2 hx) y ((hmem y).2 hy) hxy
    · exact hnd
  · intro z
    simp only [bridgeRecords, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (hmem x).1 hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (hmem x).2 hx, rfl⟩

/-- Bounded-window form of `bridgeRecords_LmIO_of_injOn`.

Every semantic request timestamp lies in one window below `orderOf β`; bounded injectivity then
preserves the exact multiplicity-sensitive `LmIO` relation after encoding. -/
theorem bridgeRecords_LmIO
    (F K : Type) [Field F] [Field K] [Algebra F K] (Ksz : ℕ) (β lmb : K)
    {B : ℕ} (hB : B ≤ orderOf β)
    {req resp : List ((nmrMEF F K).Rec)}
    (hbound : ∀ r ∈ req, r.2.2 < B)
    (hdet : ∀ x ∈ req, ∀ y ∈ req, x.2.2 = y.2.2 → x = y)
    (h : IO.LmIO Ksz req resp) :
    IO.LmIO Ksz (bridgeRecords F K β lmb req) (bridgeRecords F K β lmb resp) :=
  bridgeRecords_LmIO_of_injOn F K Ksz β lmb
    (bridge_injOn_of_timestamps F K β lmb hB req hbound hdet) h

/-- Duplicate-request regression: bounded semantic encoding preserves base-language
multiplicity, while the encoded pair remains outside the uniqueness-strengthened `LIO`. -/
theorem bridgeRecords_LmIO_duplicate_regression
    (F K : Type) [Field F] [Field K] [Algebra F K]
    (Ksz : ℕ) (hKsz : 2 ≤ Ksz) (β lmb : K)
    {B : ℕ} (hB : B ≤ orderOf β)
    (r : (nmrMEF F K).Rec) (hr : r.2.2 < B) :
    IO.LmIO Ksz (bridgeRecords F K β lmb [r, r]) (bridgeRecords F K β lmb [r])
      ∧ ¬ IO.LIO Ksz (bridgeRecords F K β lmb [r, r]) (bridgeRecords F K β lmb [r]) := by
  constructor
  · apply bridgeRecords_LmIO F K Ksz β lmb hB
    · intro x hx
      have : x = r := by simpa using hx
      subst x
      exact hr
    · intro x hx y hy _
      have hx' : x = r := by simpa using hx
      have hy' : y = r := by simpa using hy
      exact hx'.trans hy'.symm
    · exact (IO.MEM_1_strict Ksz hKsz r).1
  · simpa [bridgeRecords] using (IO.MEM_1_strict Ksz hKsz (bridge F K β lmb r)).2

/-- `LIO` is preserved by list encoding when the bridge is injective on the response list,
which is exactly the list whose uniqueness `LIO` requires. -/
theorem bridgeRecords_LIO
    (F K : Type) [Field F] [Field K] [Algebra F K] (Ksz : ℕ) (β lmb : K)
    {req resp : List ((nmrMEF F K).Rec)}
    (hinj : ∀ x ∈ resp, ∀ y ∈ resp, bridge F K β lmb x = bridge F K β lmb y → x = y)
    (h : IO.LIO Ksz req resp) :
    IO.LIO Ksz (bridgeRecords F K β lmb req) (bridgeRecords F K β lmb resp) := by
  obtain ⟨hrange, hnd, hperm⟩ := h
  exact ⟨bridgeRecords_inRange_iff F K Ksz β lmb resp |>.2 hrange,
    bridgeRecords_nodup_of_injOn F K β lmb resp hinj hnd,
    bridgeRecords_perm F K β lmb hperm⟩

/-- The exact left side certified by `IO.io_result_LIO`, specialized to eight-coordinate
records over `K`. -/
noncomputable def IOSat {K : Type} [Field K] (p : ℕ) [CharP K p]
    (req resp : List (Fin 9 → K)) : Prop :=
  ∃ (m : Fin resp.length → ZMod p)
      (accP accM : ℕ → RatFunc (RatFunc K))
      (requests responses out_mem : RatFunc (RatFunc K)),
    (∀ j, m j ≠ 0)
      ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt req i)) accP requests req.length
      ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt resp i))
          (IO.castμ (𝔽 := K) m) accM responses out_mem resp.length
      ∧ requests = responses
      ∧ out_mem = 0

/-- Bridge-specific list wrapper around `IO.io_result_LIO`.

The uniqueness assumptions are semantic plus explicit bridge injectivity on each source list;
the wrapper derives the encoded `Nodup` obligations.  No `F = K` assumption is used. -/
theorem bridgeRecords_io_result_LIO
    (F K : Type) [Field F] [Field K] [Algebra F K] [Fintype K]
    {p : ℕ} [CharP K p]
    (Ksz : ℕ) (hKp : Ksz < p) (β lmb : K)
    (req resp : List ((nmrMEF F K).Rec))
    (hKreq : IO.InRange Ksz req.length) (hKresp : resp.length ≤ Ksz)
    (hreqnd : req.Nodup) (hrespnd : resp.Nodup)
    (hreqinj : ∀ x ∈ req, ∀ y ∈ req, bridge F K β lmb x = bridge F K β lmb y → x = y)
    (hrespinj : ∀ x ∈ resp, ∀ y ∈ resp, bridge F K β lmb x = bridge F K β lmb y → x = y) :
    IOSat p (bridgeRecords F K β lmb req) (bridgeRecords F K β lmb resp) ↔
      IO.LIO Ksz (bridgeRecords F K β lmb req) (bridgeRecords F K β lmb resp) := by
  exact IO.io_result_LIO Ksz hKp
    (bridgeRecords F K β lmb req) (bridgeRecords F K β lmb resp)
    (by simpa using hKreq) (by simpa using hKresp)
    (bridgeRecords_nodup_of_injOn F K β lmb req hreqinj hreqnd)
    (bridgeRecords_nodup_of_injOn F K β lmb resp hrespinj hrespnd)

/-- Singleton specialization of the IO wrapper for the concrete `read_root` bridge row. -/
theorem readRoot_io_result_LIO
    (F K : Type) [Field F] [Field K] [Algebra F K] [Fintype K]
    {p : ℕ} [CharP K p]
    (Ksz : ℕ) (hKsz : 1 ≤ Ksz) (hKp : Ksz < p) (β lmb : K)
    (r : (nmrMEF F K).Rec) :
    IOSat p [bridge F K β lmb r] [bridge F K β lmb r] ↔
      IO.LIO Ksz [bridge F K β lmb r] [bridge F K β lmb r] := by
  exact IO.io_result_LIO Ksz hKp
    [bridge F K β lmb r] [bridge F K β lmb r]
    ⟨by simp, hKsz⟩ (by simpa using hKsz) (by simp) (by simp)

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.memRecOfNMR
#print axioms Nock.NockVMROM.Thm54.bridge
#print axioms Nock.NockVMROM.Thm54.d2_record_bridge_agrees
#print axioms Nock.NockVMROM.Thm54.bridge_coordinates
#print axioms Nock.NockVMROM.Thm54.readRootLabel
#print axioms Nock.NockVMROM.Thm54.d2_bridge_agrees
#print axioms Nock.NockVMROM.Thm54.bridge_timestamp_discriminates
#print axioms Nock.NockVMROM.Thm54.bridge_injOn_of_timestamps
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_length
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_inRange_iff
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_nodup_of_injOn
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_nodup_of_timestamp_bound
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_nodup_iff
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_perm
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_LmIO_of_injOn
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_LmIO
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_LmIO_duplicate_regression
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_LIO
#print axioms Nock.NockVMROM.Thm54.IOSat
#print axioms Nock.NockVMROM.Thm54.bridgeRecords_io_result_LIO
#print axioms Nock.NockVMROM.Thm54.readRoot_io_result_LIO
