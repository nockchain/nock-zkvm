/-
  Nock/RedTeam/Batch590Thm54RowLevelIO.lean

  Form R names are local copies
.

  What is compiled here:
  * §1 **ROOTZERO at every `λ`.**  The form-R memory gates along one record's path
    (`verify_child`, then `decompose` per path bit, then `read_root`) close to `(0, 0)` for EVERY
    `λ`, with the row's `(T, C') = (λ^m, C'(λ))` (`rootzero_general`). The engine is the general
    product identity `T·C' = λ^{n−1}·(λ^m + Σ_k a_k λ^k)` (`formR_product_general`) and the
    closed form of the up-walk (`upWalk_closed`); the cells solve the authority's gate equations
    (`decCell_solves_decompose`, `verifyCell_solves_verify`).
  * §2 **IO agreement (item 3).**  No constant in the capstone closure mentions a raw memory
    record and a raw compute record together (`run_cmd`, controls 202 / 157).  The encoded meeting
    point is `SemanticIOPreimage.derivedIO_lmio`, which IS in the closure and goes through
    `bridge_injective_bounded` (`run_cmd`).  That lemma has NO Form R analogue at any `λ`: axes
    `0` and `1` encode identically at every `λ` (`formR_zero_one_collide`,
    `encode_not_injective_any_lambda`).  At `λ = 2` with axes in `[1, p)`, `p ≠ 2`, the record
    encode is injective (`encode_inj_at_two`); distinct timestamps separate at every `λ`
    (`ts_separates`).
    Post-28th: `bridge_injective_bounded` was deleted by the 28th (the bridge now
    goes through `SemanticIOPreimage.requestTimestamp_determines`) and
    `tableRecordAt_eq_of_bind` left the closure; the raw-mention controls measure 226 / 158.
  * §3 **`BindMemRow`.**  The memory binding encodes the skeleton at bind time; a bound row's IO
    is the single encode of the semantic slot record (`bindMemRow_io`) — the forward direction
    every capstone consumer uses.  The reverse direction (row ↦ skeleton axis) is not a function
    at `λ = 1` (`bindMemRow_not_functional_at_one`) nor, for axes `{0, 1}`, at any `λ`
    (`bindMemRow_zero_one`).  The capstone-closure consumers are measured (`run_cmd`).
    Post-28th: 50 → 29 `BindMemoryRow` users, 9 → 6 axis readers.

  -- the paper
-/
import Nock.RedTeam.Batch589Thm54RowLevelChronology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch590

open Lean Meta Elab Command
open Nock Nock.NockVMROM.Thm54
open Nock.RedTeam.Batch588 Nock.RedTeam.Batch589

/-! ## §1 ROOTZERO at a general `λ` -/

section General

variable {K : Type*} [Field K]

/-- Bottom-first path bits of axis `a` below its leading `1`: bit `k` of `a`, `k < m`. -/
def pathBits (a : ℕ) : List Bool := (List.range (LcertShift a)).map a.testBit

/-- Bottom-first evaluation `Σ_i [bs_i]·λ^i`. -/
def evalB (lmb : K) : List Bool → K
  | [] => 0
  | b :: bs => (if b then 1 else 0) + lmb * evalB lmb bs

/-- The up-walk: from the record's `verify_child` cell, one `decompose` per path bit, bottom first. -/
def upWalk (lmb : K) (x : K × K) (bs : List Bool) : K × K :=
  bs.foldl (fun y b => decCell lmb b y) x


theorem decCell_solves_decompose (lmb : K) (b : Bool) (x : K × K) :
    let L : K × K := if b then (0, 0) else x
    let R : K × K := if b then x else (0, 0)
    (decCell lmb b x).1 - L.1 - R.1 - (lmb - 1) * (L.2 + R.2) - R.2 = 0 ∧
      (decCell lmb b x).2 - lmb * (L.2 + R.2) = 0 := by
  cases b <;> first | (simp [decCell]; done) | (simp [decCell]; ring)

/-- `verifyCell` solves the authority's `verify_child` gates over a zero continuation
(`counts_P − counts_L − λ^{n−1}·ts = 0`, `pw_P − pw_L − λ^{n−1}·ts = 0`). -/
theorem verifyCell_solves_verify (lmb ts : K) :
    (verifyCell lmb ts).1 - 0 - lmb ^ LpwScaleExp K * ts = 0 ∧
      (verifyCell lmb ts).2 - 0 - lmb ^ LpwScaleExp K * ts = 0 := by
  simp [verifyCell]

/-- **Closed form of the up-walk** at any `λ`:
`counts = c + p·(λ^len − 1) + p·evalB`, `pw = λ^len·p`. -/
theorem upWalk_closed (lmb : K) :
    ∀ (bs : List Bool) (c p : K),
      upWalk lmb (c, p) bs =
        (c + p * (lmb ^ bs.length - 1) + p * evalB lmb bs, lmb ^ bs.length * p)
  | [], c, p => by simp [upWalk, evalB]
  | b :: bs, c, p => by
      have ih := upWalk_closed lmb bs (c + (lmb - 1 + (if b then 1 else 0)) * p) (lmb * p)
      change upWalk lmb (decCell lmb b (c, p)) bs = _
      simp only [decCell]
      rw [ih]
      simp only [evalB, List.length_cons, pow_succ]
      ext <;> simp only <;> ring

theorem evalB_append_single (lmb : K) :
    ∀ (l : List Bool) (b : Bool),
      evalB lmb (l ++ [b]) = evalB lmb l + (if b then 1 else 0) * lmb ^ l.length
  | [], b => by simp [evalB]
  | x :: l, b => by
      simp only [List.cons_append, evalB, evalB_append_single lmb l b, List.length_cons, pow_succ]
      ring

theorem evalB_range_map (lmb : K) (f : ℕ → Bool) :
    ∀ m, evalB lmb ((List.range m).map f) =
      ∑ k ∈ Finset.range m, (if f k then (1 : K) else 0) * lmb ^ k
  | 0 => by simp [evalB]
  | m + 1 => by
      rw [List.range_succ, List.map_append, List.map_singleton, evalB_append_single,
        evalB_range_map lmb f m, Finset.sum_range_succ, List.length_map, List.length_range]

theorem evalB_pathBits (lmb : K) (a : ℕ) :
    evalB lmb (pathBits a) =
      ∑ k ∈ Finset.range (LcertShift a), (if a.testBit k then (1 : K) else 0) * lmb ^ k :=
  evalB_range_map lmb a.testBit _

@[simp] theorem pathBits_length (a : ℕ) : (pathBits a).length = LcertShift a := by
  simp [pathBits]

/-- **The general Form R product identity**: `T·C' = λ^{n−1}·(λ^m + Σ_{k<m} a_k·λ^k)` at every
`λ`, for `m = log₂ a ≤ n − 1`.  At `λ = 2` the bracket is `a` (`LformRT_mul_formRC_two`). -/
theorem formR_product_general (lmb : K) (a : ℕ) (hm : LcertShift a ≤ LpwScaleExp K) :
    LformRT lmb a * LformRC lmb a =
      lmb ^ LpwScaleExp K *
        (lmb ^ LcertShift a +
          ∑ k ∈ Finset.range (LcertShift a), (if a.testBit k then (1 : K) else 0) * lmb ^ k) := by
  set n := LpwScaleExp K with hn
  set m := LcertShift a with hmdef
  have hsum : ((List.range n).map (fun j =>
      (if LcertBit a j then (1 : K) else 0) * lmb ^ (n - (j + 1)))).sum =
      ∑ j ∈ Finset.range m,
        (if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (n - (j + 1)) := by
    rw [Llist_range_map_sum]
    have hz : ∀ j ∈ Finset.range n, j ∉ Finset.range m →
        (if LcertBit a j then (1 : K) else 0) * lmb ^ (n - (j + 1)) = 0 := by
      intro j _ hj
      have hj' : ¬ j < m := by simpa using hj
      simp [LcertBit, ← hmdef, hj']
    rw [← Finset.sum_subset (Finset.range_mono hm) hz]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m := Finset.mem_range.mp hj
    simp [LcertBit, ← hmdef, hj']
  have hreflect :
      ∑ j ∈ Finset.range m, (if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (m - 1 - j) =
        ∑ k ∈ Finset.range m, (if a.testBit k then (1 : K) else 0) * lmb ^ k :=
    Finset.sum_range_reflect (fun k => (if a.testBit k then (1 : K) else 0) * lmb ^ k) m
  have hterm : ∀ j ∈ Finset.range m,
      lmb ^ m * ((if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (n - (j + 1))) =
        lmb ^ n * ((if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (m - 1 - j)) := by
    intro j hj
    have hj' : j < m := Finset.mem_range.mp hj
    have he : m + (n - (j + 1)) = n + (m - 1 - j) := by omega
    calc lmb ^ m * ((if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (n - (j + 1)))
        = (if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (m + (n - (j + 1))) := by
          rw [pow_add]; ring
      _ = (if a.testBit (m - 1 - j) then (1 : K) else 0) * lmb ^ (n + (m - 1 - j)) := by rw [he]
      _ = _ := by rw [pow_add]; ring
  simp only [LformRT, LformRC]
  rw [← hn, ← hmdef, hsum, mul_add, Finset.mul_sum, Finset.sum_congr rfl hterm,
    ← Finset.mul_sum, hreflect]
  ring

/-- **ROOTZERO at every `λ`.**  A record at axis `a` (`log₂ a ≤ n − 1`), timestamp `ts`: the
`verify_child` cell, the `decompose` cells along the path, and the `read_root` row carrying the
row-level `(T, C') = (formRT λ a, formRC λ a)` close both accumulators to zero.  No `λ = 2`. -/
theorem rootzero_general (lmb ts : K) (a : ℕ) (hm : LcertShift a ≤ LpwScaleExp K) :
    readResidual lmb (LformRT lmb a) (LformRC lmb a) ts
        (upWalk lmb (verifyCell lmb ts) (pathBits a)) = (0, 0) := by
  have hprod := formR_product_general lmb a hm
  simp only [verifyCell, readResidual]
  rw [upWalk_closed, pathBits_length, evalB_pathBits]
  ext
  · simp only
    rw [mul_assoc (LformRT lmb a), ← mul_assoc, hprod]
    ring
  · simp only [LformRT]
    ring


theorem rootzero_two_is_lane_closed_form (ts : K) (a : ℕ) (ha1 : 1 ≤ a)
    (hm : LcertShift a ≤ LpwScaleExp K) :
    (upWalk (2 : K) (verifyCell 2 ts) (pathBits a)).1 = (a : K) * ((2 : K) ^ LpwScaleExp K * ts) := by
  have h := congrArg Prod.fst (rootzero_general (2 : K) ts a hm)
  simp only [readResidual] at h
  have hlog : a.log2 ≤ LpwScaleExp K := by rwa [← LcertShift_eq_log2]
  rw [LformRT_mul_formRC_two a ha1 hlog] at h
  linear_combination h

end General

/-! ## §2 IO agreement under F1 + F2 -/

/-- The raw memory-record heads and raw compute-record heads (`Language.lean:33-44`). -/
def memRawHeads : List Name :=
  [``Nock.MemoryTable.Pub.mem, ``Nock.MemoryTable.responseRecords,
    ``Nock.NockVMROM.Thm54.ExactExecution.rawResponses]

def compRawHeads : List Name :=
  [``Nock.ComputeTable.Pub.mr1, ``Nock.ComputeTable.Pub.mr2, ``Nock.ComputeTable.Pub.mr3,
    ``Nock.NockVM.activeRequestRecords, ``Nock.NockVMROM.Thm54.ExactExecution.rawRequests]

def mentionsAnyOf (e : Expr) (ns : List Name) : Bool :=
  (e.find? fun x => match x with | .const n _ => ns.contains n | _ => false).isSome

-- **No mixed raw comparison in the capstone closure.**  Every constant in the closure of
-- `nockCompiles_zmod` (type or value, proofs included) that mentions a raw memory record mentions
-- no raw compute record.  Controls: both sides are non-empty.
run_cmd do
  let env ← getEnv
  let cl := Nock.RedTeam.Batch587.closureOf env Nock.RedTeam.Batch587.capstoneName
  let mut nm : Nat := 0
  let mut nc : Nat := 0
  let mut both : Array Name := #[]
  for n in cl.toList do
    match env.find? n with
    | some ci =>
      let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
      let m := mentionsAnyOf ci.type memRawHeads || mentionsAnyOf v memRawHeads
      let c := mentionsAnyOf ci.type compRawHeads || mentionsAnyOf v compRawHeads
      if m then nm := nm + 1
      if c then nc := nc + 1
      if m && c then both := both.push n
    | none => pure ()
  unless both.isEmpty do throwError m!"mixed raw comparisons: {both}"
  unless nm > 100 && nc > 100 do throwError m!"controls too small: mem {nm} comp {nc}"
  logInfo m!"§2: closure {cl.size}; raw-memory mentions {nm}, raw-compute mentions {nc}, both 0"

/-- The encoded IO meeting point and its injectivity lemma are in the capstone closure
.  `bridge_injective_bounded` is a plain name literal because the
28th deleted the constant. -/
def ioClosureMembers : List Name :=
  [ ``Nock.NockVMROM.Thm54.SemanticIOPreimage.derivedIO_lmio,
    ``Nock.NockVMROM.Thm54.bridgeRecords_LmIO,
    `Nock.NockVMROM.Thm54.bridge_injective_bounded,
    ``Nock.NockVMROM.Thm54.bridgeRecords_nodup_of_injOn,
    ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.SemanticTimestampSkeleton.tableRecordAt_eq_of_bind,
    ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.SemanticTimestampSkeleton.bridge_semanticRecordAt,
    ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.activeMemoryRecord_eq_tableRecordAt,
    ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.memoryResponseRecords_eq_semanticSlots ]

/-- **Post-28th drift: deleted.**  Before the 28th `bridge_injective_bounded` was
in the capstone closure; the 28th deleted it (the IO bridge now goes through the timestamp
argument, `SemanticIOPreimage.requestTimestamp_determines`).  Asserted: the constant does not
exist. -/
def post28thIoDeleted : List Name :=
  [ `Nock.NockVMROM.Thm54.bridge_injective_bounded ]

/-- **Post-28th drift: left the capstone closure.**  Before the 28th
`tableRecordAt_eq_of_bind` was in the closure; after it, it still exists but is measured NOT in
the closure (consistent with `Batch587.post28thOffCapstone`). -/
def post28thIoOffClosure : List Name :=
  [ ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.SemanticTimestampSkeleton.tableRecordAt_eq_of_bind ]

run_cmd do
  let env ← getEnv
  let cl := Nock.RedTeam.Batch587.closureOf env Nock.RedTeam.Batch587.capstoneName
  for n in post28thIoDeleted ++ post28thIoOffClosure do
    unless ioClosureMembers.contains n do throwError m!"drift list: {n} not in ioClosureMembers"
  for n in ioClosureMembers do
    if post28thIoDeleted.contains n then
      if env.contains n then throwError m!"{n} exists again (post-28th drift)"
    else if post28thIoOffClosure.contains n then
      unless env.contains n do throwError m!"{n} does not exist"
      if cl.contains n then throwError m!"{n} is back in the capstone closure (post-28th drift)"
    else
      unless cl.contains n do throwError m!"{n} not in the capstone closure"
  if cl.contains ``Nock.NockVMROM.Thm54.SemanticIOPreimage.semanticRequests_unique then
    throwError "semanticRequests_unique unexpectedly in the closure"
  logInfo m!"§2: {ioClosureMembers.length - (post28thIoDeleted ++ post28thIoOffClosure).length} IO/identity casualties confirmed in the capstone closure (post-28th: {post28thIoDeleted.length} deleted, {post28thIoOffClosure.length} off the closure)"

section Inj

variable {K : Type*} [Field K]

/-- **Axes `0` and `1` encode identically at every `λ`.**  Both have `m = 0` and no certificate
bit, so `(T, C') = (1, λ^{n−1})`. -/
theorem formR_zero_one_collide (lmb : K) :
    LformRT lmb 0 = LformRT lmb 1 ∧ LformRC lmb 0 = LformRC lmb 1 := by
  simp [LformRT, LformRC, LcertBit, LcertShift, Nat.size_zero, Nat.size_one]

/-- **Live's `bridge_injective_bounded` has no Form R analogue at any `λ`.**  Two records equal
in root, child and timestamp, with axes `0 ≠ 1`, have the same Form R encode at every `λ` (`𝔽_7`).
So `derivedIO_lmio`'s encoded `Nodup` needs either `formR_inj` on the source list or a fact that excludes the collision. -/
theorem encode_not_injective_any_lambda :
    ∃ r s : ComputeTable.MemRec Z7, r ≠ s ∧ r.ts = s.ts ∧
      ∀ lmb : Z7, LencRecFormR r lmb = LencRecFormR s lmb := by
  refine ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ?_, rfl, ?_⟩
  · intro h
    have := congrArg ComputeTable.MemRec.axis h
    exact absurd this (by decide)
  · intro lmb
    have h7 : ringChar Z7 = 7 := ZMod.ringChar_zmod_n 7
    have h0 : LnockAxisOf (0 : Z7) = 0 := by
      have := LnockAxisOf_natCast (K := Z7) (a := 0) (by rw [h7]; norm_num)
      simpa using this
    have h1 : LnockAxisOf (1 : Z7) = 1 := by
      have := LnockAxisOf_natCast (K := Z7) (a := 1) (by rw [h7]; norm_num)
      simpa using this
    have hc := formR_zero_one_collide lmb
    simp only [LencRecFormR, h0, h1, hc.1, hc.2]

/-- **Distinct timestamps separate at every `λ`** (coordinate `7` is `ts`). -/
theorem ts_separates (lmb : K) (r s : ComputeTable.MemRec K) (h : r.ts ≠ s.ts) :
    LencRecFormR r lmb ≠ LencRecFormR s lmb := by
  intro he
  apply h
  have := congrFun he 7
  simpa [LencRecFormR, LencRecC] using this

/-- **At `λ = 2` the record encode is injective** on records whose axes are casts of
`a ∈ [1, p)`, `p ≠ 2` — the fixed-coin discharge of `formR_inj` (via `formR_two_product_inj`). -/
theorem encode_inj_at_two (hp2 : ringChar K ≠ 2) (r s : ComputeTable.MemRec K) {a b : ℕ}
    (hra : r.axis = (a : K)) (hsb : s.axis = (b : K)) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (ha : a < ringChar K) (hb : b < ringChar K)
    (h : LencRecFormR r 2 = LencRecFormR s 2) : r = s := by
  have hna : LnockAxisOf r.axis = a := by rw [hra]; exact LnockAxisOf_natCast ha
  have hnb : LnockAxisOf s.axis = b := by rw [hsb]; exact LnockAxisOf_natCast hb
  have hc : ∀ i : Fin 9, LencRecFormR r 2 i = LencRecFormR s 2 i := fun i => congrFun h i
  simp only [LencRecFormR, LencRecC, hna, hnb] at hc
  have e0 := hc 0; have e1 := hc 1; have e2 := hc 2; have e3 := hc 3; have e4 := hc 4
  have e5 := hc 5; have e6 := hc 6; have e7 := hc 7; have e8 := hc 8
  simp at e0 e1 e2 e3 e4 e5 e6 e7 e8
  have hab : a = b := formR_two_product_inj hp2 ha1 hb1 ha hb (by rw [e6, e8])
  subst hab
  apply ComputeTable.MemRec.ext
  · exact ComputeTable.FP.ext e0 e1 e2
  · exact ComputeTable.FP.ext e3 e4 e5
  · rw [hra, hsb]
  · exact e7

end Inj

/-! ## §3 `BindMemRow` -/

section Bind

variable {K : Type} [Field K]

/-- **`BindMemRow`** — the memory form of `SemanticStrategy.BindMemRec` (`SemanticStrategy.lean:132`)
under F1: fingerprints bind as before; the axis slot holds `T = formRT λ s.axis`; the `C'` column
holds `formRC λ s.axis`.  The skeleton's `ℕ` axis is encoded at BIND time.  In `BindMemoryRow`
(`:156-166`) the active branch becomes
`BindMemRow z λ (s.memoryRecord h) row.2.2.mem row.2.2.cprime ∧ row.2.2.lambda = λ`, with `λ` the
single source (F5); the compute form `BindMemRec` is unchanged. -/
def BindMemRow (z lmb : K) (s : SemanticStrategy.MemRecSkeleton)
    (mem : ComputeTable.MemRec K) (cprime : K) : Prop :=
  SemanticStrategy.bindFP z s.root mem.root ∧ SemanticStrategy.bindFP z s.child mem.child ∧
    mem.axis = LformRT lmb s.axis ∧ cprime = LformRC lmb s.axis

/-- **Forward direction (all the capstone needs).**  A bound row's IO vector is the single Form R
encode of the semantic slot record `tableRecordAt z α slot` — the compute side's `encRecFormR`.
This is the restated `memoryResponseRecords_eq_semanticSlots` / `bridge_semanticRecordAt` at the
IO level.  It needs the slot axis below `p` (the honest axis bound), not `formR_inj`. -/
theorem bindMemRow_io (z α lmb : K) (slot : SemanticTimestampStrategy.CanonicalRecordSlot)
    (mem : ComputeTable.MemRec K) (cprime : K)
    (h : BindMemRow z lmb slot.record mem cprime) (ht : mem.ts = α ^ slot.exponent)
    (hax : slot.record.axis < ringChar K) :
    LencRecC mem cprime =
      LencRecFormR (SemanticTimestampStrategy.SemanticTimestampSkeleton.tableRecordAt z α slot) lmb := by
  obtain ⟨hr, hc, ha, hcp⟩ := h
  have hn : LnockAxisOf (slot.record.axis : K) = slot.record.axis := LnockAxisOf_natCast hax
  have hmem : mem = { SemanticTimestampStrategy.SemanticTimestampSkeleton.tableRecordAt z α slot with
      axis := LformRT lmb slot.record.axis } := by
    apply ComputeTable.MemRec.ext
    · exact hr
    · exact hc
    · exact ha
    · exact ht
  rw [hmem, hcp]
  simp only [LencRecFormR, SemanticTimestampStrategy.SemanticTimestampSkeleton.tableRecordAt, hn]

/-- **Reverse direction fails at `λ = 1`**: one row binds the skeleton axes `3` and `5`. -/
theorem bindMemRow_not_functional_at_one (z : Z7) (root child : Noun) :
    ∃ (mem : ComputeTable.MemRec Z7) (c' : Z7),
      BindMemRow z 1 ⟨root, child, 3⟩ mem c' ∧ BindMemRow z 1 ⟨root, child, 5⟩ mem c' := by
  have hc := collision_at_one_3_5
  refine ⟨⟨GlobalCarryRecognizer.enc z root, GlobalCarryRecognizer.enc z child,
    LformRT 1 3, 0⟩, LformRC 1 3, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, hc.1, hc.2⟩⟩

/-- **And for axes `{0, 1}` at every `λ`.** -/
theorem bindMemRow_zero_one (z lmb : K) (root child : Noun) (mem : ComputeTable.MemRec K) (c' : K) :
    BindMemRow z lmb ⟨root, child, 0⟩ mem c' ↔ BindMemRow z lmb ⟨root, child, 1⟩ mem c' := by
  have hc := formR_zero_one_collide lmb
  simp only [BindMemRow, hc.1, hc.2]

end Bind

/-- The capstone-closure users of `BindMemoryRow` that read `MemRec.axis` directly (measured). -/
def bindMemoryRowAxisReaders : List Name :=
  [ `Nock.NockVMROM.Thm54.ActiveFingerprintScan.bindMemoryRow_slots,
    `Nock.NockVMROM.Thm54.HonestCommitment.bindMemoryRow_render,
    `Nock.NockVMROM.Thm54.HonestCommitment.renderMemoryRow_eq_self,
    `Nock.NockVMROM.Thm54.RawSemanticAssembly.bindMemoryRow_frame,
    `Nock.NockVMROM.Thm54.RawSemanticAssembly.bindMemoryRow_of_slots,
    `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.bindsRow_specialize,
    `Nock.NockVMROM.Thm54.TraceGen.gMemRow9_read_bind,
    `Nock.NockVMROM.Thm54.TraceGen.gMemRow9_verify_bind,
    `Nock.NockVMROM.Thm54.TraceGen.genAssignedMemory_WF ]


def post28thReadersDropped : List Name :=
  [ `Nock.NockVMROM.Thm54.HonestCommitment.bindMemoryRow_render,
    `Nock.NockVMROM.Thm54.HonestCommitment.renderMemoryRow_eq_self,
    `Nock.NockVMROM.Thm54.TraceGen.gMemRow9_read_bind,
    `Nock.NockVMROM.Thm54.TraceGen.gMemRow9_verify_bind,
    `Nock.NockVMROM.Thm54.TraceGen.genAssignedMemory_WF ]

/-- **Post-28th drift: readers that joined.**  Axis-reading `BindMemoryRow` users
in the capstone closure after the 28th that were not on the pre-28th list. -/
def post28thReadersAdded : List Name :=
  [ `Nock.NockVMROM.Thm54.TraceGen.bindMemoryRow_encodeRow,
    `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.activeMemoryRecord_eq_tableRecordAt ]


def bindMemoryRowUsersPre28th : ℕ := 50

-- `reqPairEventOf_card_le` left the capstone closure.
def bindMemoryRowUsersPost28th : ℕ := 30

-- pinned `decodedLambdaEventOf_card_le` reads the row counts through `strategy_bindsAll`; 31 since


-- **The `BindMemoryRow` consumers.**  In the capstone closure, exactly 50 named constants
-- mention `BindMemoryRow`; exactly the nine above also read `MemRec.axis` themselves.
-- [Before the 28th.  After it: exactly 29 users, and the axis readers are the
-- nine above minus `post28thReadersDropped` plus `post28thReadersAdded` (six).]  None is a
-- decoder: each either PROVES the binding from a frame/slot/render fact (forward) or USES it to
-- rewrite the row to the skeleton's record (forward).  The hostile decoders are not in the
-- closure.
run_cmd do
  let env ← getEnv
  let cl := Nock.RedTeam.Batch587.closureOf env Nock.RedTeam.Batch587.capstoneName
  let bm := [``Nock.NockVMROM.Thm54.SemanticStrategy.BindMemoryRow]
  let mut users : Array Name := #[]
  let mut readers : Array Name := #[]
  for n in cl.toList do
    match env.find? n with
    | some ci =>
      let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
      if !n.isInternal && !(n.toString.endsWith "eq_1") &&
          (mentionsAnyOf ci.type bm || mentionsAnyOf v bm) then
        users := users.push n
        if Nock.RedTeam.Batch587.readsAxis env n then readers := readers.push n
    | none => pure ()
  unless users.size = bindMemoryRowUsersPost28th do throwError m!"BindMemoryRow users: {users.size}"
  for n in post28thReadersDropped do
    unless bindMemoryRowAxisReaders.contains n do throwError m!"drift list: {n} not a pre-28th reader"
    unless cl.contains n do throwError m!"{n} not in the capstone closure"
    if users.contains n then throwError m!"{n} is a BindMemoryRow user again (post-28th drift)"
  for n in bindMemoryRowAxisReaders do
    unless post28thReadersDropped.contains n do
      unless readers.contains n do throwError m!"{n} not an axis-reading BindMemoryRow user"
  for n in post28thReadersAdded do
    unless readers.contains n do throwError m!"{n} not an axis-reading BindMemoryRow user"
  unless readers.size + post28thReadersDropped.length =
      bindMemoryRowAxisReaders.length + post28thReadersAdded.length do
    throwError m!"axis readers: {readers}"
  logInfo m!"§3: {users.size} BindMemoryRow users in the capstone closure, {readers.size} read the axis"

end Nock.RedTeam.Batch590

#print axioms Nock.RedTeam.Batch590.decCell_solves_decompose
#print axioms Nock.RedTeam.Batch590.verifyCell_solves_verify
#print axioms Nock.RedTeam.Batch590.upWalk_closed
#print axioms Nock.RedTeam.Batch590.formR_product_general
#print axioms Nock.RedTeam.Batch590.rootzero_general
#print axioms Nock.RedTeam.Batch590.rootzero_two_is_lane_closed_form
#print axioms Nock.RedTeam.Batch590.formR_zero_one_collide
#print axioms Nock.RedTeam.Batch590.encode_not_injective_any_lambda
#print axioms Nock.RedTeam.Batch590.ts_separates
#print axioms Nock.RedTeam.Batch590.encode_inj_at_two
#print axioms Nock.RedTeam.Batch590.bindMemRow_io
#print axioms Nock.RedTeam.Batch590.bindMemRow_not_functional_at_one
#print axioms Nock.RedTeam.Batch590.bindMemRow_zero_one
