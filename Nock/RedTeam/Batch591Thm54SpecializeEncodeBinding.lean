/-
  Nock/RedTeam/Batch591Thm54SpecializeEncodeBinding.lean

  Hostile binding of the
  template/exec split, and honest completeness on the concrete axis-3 package.**

  What is compiled here:
  * Under S2 the exec row's
    `(T, C')` is a function of the template's axis (`s2_axis`, `s2_cprime`), and its IO is the
    compute side's single encode of the template record (`s2_io_eq_compute_encode`).  So the
    brief's attack — template passes `countsP_bin` with `a`, exec carries the encode of `a' ≠ a`
    — needs `formR a = formR a'`: impossible at `λ = 2` on `[1, p)` (`p8_split_forces_equal_at_two`)
    and IO-invisible otherwise (axes `0/1`, `Batch590.formR_zero_one_collide`).
  * §2 **The H1 wrap double-encodes under S2.**  Live's hostile wrap (`wrapMemoryLabel`) puts the
    DECODED row in the placeholder; S2 then encodes its axis slot `T` again, and the specialized
    `C'` is not the row's (`s2_wrap_reencodes`, `𝔽_7`, axis 5, `λ = 2`: `C' = 4 ≠ 5`).  The repaired
    wrap must put the JOINED Nock axis in the placeholder; its identity holds iff the decoded row
    is the encode of that axis (`wrapJoin_identity_iff`) — exactly the compute IO transport, which
    is uncompiled (first pass item 9).
  * §3 **Honest completeness on the live concrete axis-3 package** (`p = 73`,
    `K = GaloisField 73 3`, `honestAlpha = 4`).  The S2 row of
    the same template carries `(T, C') = (2, C'(3))` (`concrete_s2_row`), its IO is the compute
    request's single encode (`concrete_s2_io`), and it closes Form R ROOTZERO with `(T, C')` READ
    from the row (`concrete_s2_rootzero`).
-/
import Nock.RedTeam.Batch587Thm54RowLevelInventory
import Nock.RedTeam.Batch590Thm54RowLevelIO
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.NockVMROM.Thm54.TemplateAxisCounting

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch591

open Nock Nock.Walk Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.RedTeam.Batch588 Nock.RedTeam.Batch589 Nock.RedTeam.Batch590

/-! ## §0 The S2 specialization (local; lane names are not on live) -/

section S2

variable {K : Type} [Field K]

structure S2Row (K : Type) where
  row : MemoryTable.MState × MemoryTable.DTmem K
  cprime : K
  lmb : K

/-- Row-level IO: read the row (lane `encRecC mem cprime`), no encode. -/
def S2Row.io (r : S2Row K) : Fin 9 → K := LencRecC r.row.2.2.mem r.cprime

/-- **S2.** -/
noncomputable def s2Specialize (lmb α : K) (T : MemoryRowTemplate (K := K)) : S2Row K :=
  let base := T.specializeA α
  if memoryMemRecKind T.timestamp.state = .active then
    { row := (base.1, base.2.1,
        { base.2.2 with
          mem := { base.2.2.mem with
            axis := LformRT lmb (LnockAxisOf T.placeholder.2.2.mem.axis) } })
      cprime := LformRC lmb (LnockAxisOf T.placeholder.2.2.mem.axis)
      lmb := lmb }
  else
    { row := base, cprime := 1, lmb := lmb }

theorem s2_axis (lmb α : K) (T : MemoryRowTemplate (K := K))
    (h : memoryMemRecKind T.timestamp.state = .active) :
    (s2Specialize lmb α T).row.2.2.mem.axis =
      LformRT lmb (LnockAxisOf T.placeholder.2.2.mem.axis) := by
  simp [s2Specialize, h]

theorem s2_cprime (lmb α : K) (T : MemoryRowTemplate (K := K))
    (h : memoryMemRecKind T.timestamp.state = .active) :
    (s2Specialize lmb α T).cprime = LformRC lmb (LnockAxisOf T.placeholder.2.2.mem.axis) := by
  simp [s2Specialize, h]

theorem s2_ts (lmb α : K) (T : MemoryRowTemplate (K := K))
    (h : memoryMemRecKind T.timestamp.state = .active) :
    (s2Specialize lmb α T).row.2.2.mem.ts = α ^ T.timestamp.recordExponent := by
  simp [s2Specialize, h, MemoryRowTemplate.specializeA, specializeMemRec]

theorem s2_lambda (lmb α : K) (T : MemoryRowTemplate (K := K)) :
    (s2Specialize lmb α T).lmb = lmb := by
  unfold s2Specialize; split <;> rfl

/-- **IO of an S2 row = the compute side's single encode of the template record** (at its
specialized timestamp). -/
theorem s2_io_eq_compute_encode (lmb α : K) (T : MemoryRowTemplate (K := K))
    (h : memoryMemRecKind T.timestamp.state = .active) :
    (s2Specialize lmb α T).io = LencRecFormR ((T.specializeA α).2.2.mem) lmb := by
  have hax : (T.specializeA α).2.2.mem.axis = T.placeholder.2.2.mem.axis := by
    simp [MemoryRowTemplate.specializeA, specializeMemRec, h]
  simp only [S2Row.io, LencRecFormR, hax]
  simp [s2Specialize, h]

end S2


section Binding

variable {F K : Type} [Field F] [Field K] [Algebra F K] {p : ℕ} [CharP K p]

theorem specializedProblem_exec_is_specialize
    (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    (TemplateRawJointSoundness.specializedProblem T z hz α lmb).exec =
      (T.afterSeed ⟨z, hz⟩).executionTemplate.specialize α lmb :=
  rfl

end Binding

section Split

variable {K : Type} [Field K]

/-- **The brief's split needs a Form R collision.**  If an S2 exec row (built from a template with
axis `a`, `a < p`) carries the encode of `a'`, then `formR a = formR a'`. -/
theorem split_requires_collision (lmb α : K) (T : MemoryRowTemplate (K := K))
    (h : memoryMemRecKind T.timestamp.state = .active)
    {a a' : ℕ} (ha : a < ringChar K) (hT : T.placeholder.2.2.mem.axis = (a : K))
    (hrow : (s2Specialize lmb α T).row.2.2.mem.axis = LformRT lmb a' ∧
      (s2Specialize lmb α T).cprime = LformRC lmb a') :
    LformRT lmb a = LformRT lmb a' ∧ LformRC lmb a = LformRC lmb a' := by
  rw [s2_axis lmb α T h, hT, LnockAxisOf_natCast ha] at hrow
  rw [s2_cprime lmb α T h, hT, LnockAxisOf_natCast ha] at hrow
  exact hrow

/-- **At `λ = 2` on `[1, p)` (`p` odd) there is no split at all.** -/
theorem p8_split_forces_equal_at_two (hp2 : ringChar K ≠ 2) (α : K)
    (T : MemoryRowTemplate (K := K))
    (h : memoryMemRecKind T.timestamp.state = .active)
    {a a' : ℕ} (ha1 : 1 ≤ a) (ha : a < ringChar K) (ha1' : 1 ≤ a') (ha' : a' < ringChar K)
    (hT : T.placeholder.2.2.mem.axis = (a : K))
    (hrow : (s2Specialize 2 α T).row.2.2.mem.axis = LformRT 2 a' ∧
      (s2Specialize 2 α T).cprime = LformRC 2 a') :
    a = a' := by
  have hc := split_requires_collision 2 α T h ha hT hrow
  have hprod : LformRT (2 : K) a * LformRC 2 a = LformRT 2 a' * LformRC 2 a' := by
    rw [hc.1, hc.2]
  exact formR_two_product_inj hp2 ha1 ha1' ha ha' hprod

end Split

/-! ## §2 The H1 wrap under S2 -/

section Wrap

open Nock.NockVMROM.Thm54.StrategyOfTracesCore

/-- A decoded memory row over `𝔽_7`: a `read_root` row holding the chip's `T = 4` for axis `5`
at `λ = 2` (`Batch587.rowR1_values`), `ts = 1`. -/
noncomputable def decodedRowZ7 : MemoryTable.MState × MemoryTable.DTmem Z7 :=
  (.read_root, ⟨0, 0, 0⟩,
    { st := .read_root, pt := MemoryTable.Cell.zero, lc := MemoryTable.Cell.zero, rc := MemoryTable.Cell.zero,
      lcSt := .halt, rcSt := .halt, mem := ⟨0, 0, 4, 1⟩, ipre := 0, icur := 0 })

/-- **S2 re-encodes a wrapped decoded row.**  Live's hostile wrap `wrapMemoryLabel` puts the
decoded row (axis slot `T = 4`) in the placeholder; S2 reads `nockAxisOf 4 = 4` as a Nock axis and
writes `C'(4) = 4`, while the row's own `C'` is `C'(5) = 5`. -/
theorem s2_wrap_reencodes :
    (s2Specialize (2 : Z7) 1 (wrapMemoryLabel 1 decodedRowZ7)).cprime = 4 ∧
      LformRC (2 : Z7) 5 = 5 := by
  have hact : memoryMemRecKind (wrapMemoryLabel (1 : Z7) decodedRowZ7).timestamp.state =
      .active := by
    simp [wrapMemoryLabel, decodedRowZ7, memoryMemRecKind]
  rw [s2_cprime _ _ _ hact]
  have h4 : (wrapMemoryLabel (1 : Z7) decodedRowZ7).placeholder.2.2.mem.axis = ((4 : ℕ) : Z7) := by
    rfl
  rw [h4, LnockAxisOf_natCast (K := Z7) (a := 4) (by simp [ZMod.ringChar_zmod_n])]
  simp only [LformRC, pwScale_Z7]
  decide

/-- The repaired wrap: placeholder axis slot := the JOINED Nock axis `a`. -/
noncomputable def wrapJoin {K : Type} [Field K] [Fintype K] [DecidableEq K] (a : ℕ) (α : K)
    (row : MemoryTable.MState × MemoryTable.DTmem K) : MemoryRowTemplate (K := K) :=
  let w := wrapMemoryLabel α row
  { w with placeholder :=
      (w.placeholder.1, w.placeholder.2.1,
        { w.placeholder.2.2 with mem := { w.placeholder.2.2.mem with axis := (a : K) } }) }

/-- **What the repaired wrap needs.**  On an active decoded row with chip columns `(T, C')`, the
S2 specialization of the joined wrap reproduces `(T, C')` iff they are the Form R encode of the
joined axis.  On the hostile track that is the compute IO transport (`gadget_sound` + the LogUp
match keyed by the unique timestamp), which is not compiled anywhere. -/
theorem wrapJoin_identity_iff {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (lmb α : K) {a : ℕ} (ha : a < ringChar K)
    (row : MemoryTable.MState × MemoryTable.DTmem K) (cprime : K)
    (hact : memoryMemRecKind row.1 = .active) :
    ((s2Specialize lmb α (wrapJoin a α row)).row.2.2.mem.axis = row.2.2.mem.axis ∧
        (s2Specialize lmb α (wrapJoin a α row)).cprime = cprime) ↔
      (row.2.2.mem.axis = LformRT lmb a ∧ cprime = LformRC lmb a) := by
  have hact' : memoryMemRecKind (wrapJoin a α row).timestamp.state = .active := by
    simpa [wrapJoin, wrapMemoryLabel] using hact
  rw [s2_axis _ _ _ hact', s2_cprime _ _ _ hact']
  have hax : (wrapJoin a α row).placeholder.2.2.mem.axis = (a : K) := rfl
  rw [hax, LnockAxisOf_natCast ha]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩

end Wrap

/-! ## §3 Honest completeness on the live concrete axis-3 package -/

section Concrete

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open AxisBatching AxisBatching.MTree

local instance : CharP K73cubic 73 := inferInstance

theorem ringChar_K73 : ringChar K73cubic = 73 := ringChar.eq K73cubic 73

/-- The concrete template with the verify placeholder's axis slot set to `x` (live: `x = 3`). -/
noncomputable def verifyRowTemplateX (z x : K73cubic) : MemoryRowTemplate (K := K73cubic) where
  timestamp := { state := .verify_child, recordExponent := 1 }
  placeholder := (.verify_child, memoryInputs z,
    { verifyPubA z 0 with mem := { requestRecord z 0 with axis := x } })

noncomputable def readTemplateTreeX (z x : K73cubic) : NTree (MemoryRowTemplate (K := K73cubic)) :=
  .node (readRowTemplate z)
    [.node (decomposeRowTemplate z)
      [headTemplateTree z, .node (verifyRowTemplateX z x) [tailTemplateTree z]]]

/-- Live's concrete template is the `x = 3` instance (a-bearing, as S1 asks). -/
theorem readTemplateTree_eq_X (z : K73cubic) : readTemplateTree z = readTemplateTreeX z 3 := by
  simp only [readTemplateTree, readTemplateTreeX, decomposeTemplateTree, verifyTemplateTree,
    verifyRowTemplate, verifyRowTemplateX, verifyPubA, requestRecord]

theorem concrete_templateAxisTree (z x : K73cubic) :
    TemplateAxisCounting.templateAxisTree (readTemplateTreeX z x) =
      .read 1 (.decompose .halt (.verify 1 x .halt)) := by
  simp [readTemplateTreeX, readRowTemplate, decomposeRowTemplate, headTemplateTree,
    headRowTemplate, verifyRowTemplateX, tailTemplateTree, tailRowTemplate,
    TemplateAxisCounting.templateAxisTree]

theorem two_ne_zero_K73 : (2 : K73cubic) ≠ 0 :=
  SetEq.Lcast_ne_zero (p := 73) (k := 2) (by norm_num) (by norm_num)

theorem concrete_boundary_eval (z x α : K73cubic) :
    (countsP_bin (TemplateAxisCounting.templateAxisTree (readTemplateTreeX z x))).eval α =
      α * (x - 3) / 2 := by
  rw [concrete_templateAxisTree]
  simp [countsP_bin, indP_bin]
  field_simp [two_ne_zero_K73]
  ring

/-- **S1 completeness.**  With the a-bearing placeholder (`x = 3`), the template boundary vanishes
at every `α` — and live's concrete template is that template (`readTemplateTree_eq_X`). -/
theorem s1_concrete_boundary (z α : K73cubic) :
    (countsP_bin (TemplateAxisCounting.templateAxisTree (readTemplateTree z))).eval α = 0 := by
  rw [readTemplateTree_eq_X, concrete_boundary_eval]
  ring

theorem rowlevel_concrete_boundary_fails (z : K73cubic) :
    LformRT (2 : K73cubic) 3 = 2 ∧
      2 * (countsP_bin (TemplateAxisCounting.templateAxisTree
        (readTemplateTreeX z (LformRT 2 3)))).eval honestAlpha =
        -12 + 4 * LformRT (2 : K73cubic) 3 ∧
      (countsP_bin (TemplateAxisCounting.templateAxisTree
        (readTemplateTreeX z (LformRT 2 3)))).eval honestAlpha ≠ 0 := by
  have hs : LcertShift 3 = 1 := by decide
  have hT : LformRT (2 : K73cubic) 3 = 2 := by simp [LformRT, hs]
  have hv : (countsP_bin (TemplateAxisCounting.templateAxisTree
      (readTemplateTreeX z (LformRT 2 3)))).eval honestAlpha = -2 := by
    rw [concrete_boundary_eval, hT]
    show (4 : K73cubic) * (2 - 3) / 2 = -2
    field_simp [two_ne_zero_K73]
    ring
  refine ⟨hT, ?_, ?_⟩
  · rw [hv, hT]; ring
  · rw [hv]; exact neg_ne_zero.mpr two_ne_zero_K73

theorem three_lt_char : (3 : ℕ) < ringChar K73cubic := by rw [ringChar_K73]; norm_num

/-- **The S2 row of the live concrete verify template:** `(T, C') = (formRT λ 3, formRC λ 3)`,
`ts = α`, at any `λ`. -/
theorem concrete_s2_row (z lmb α : K73cubic) :
    (s2Specialize lmb α (verifyRowTemplate z)).row.2.2.mem.axis = LformRT lmb 3 ∧
      (s2Specialize lmb α (verifyRowTemplate z)).cprime = LformRC lmb 3 ∧
      (s2Specialize lmb α (verifyRowTemplate z)).row.2.2.mem.ts = α := by
  have hact : memoryMemRecKind (verifyRowTemplate z).timestamp.state = .active := by
    simp [verifyRowTemplate, memoryMemRecKind]
  have hax : (verifyRowTemplate z).placeholder.2.2.mem.axis = ((3 : ℕ) : K73cubic) := by
    simp [verifyRowTemplate, verifyPubA, requestRecord]
  refine ⟨?_, ?_, ?_⟩
  · rw [s2_axis _ _ _ hact, hax, LnockAxisOf_natCast three_lt_char]
  · rw [s2_cprime _ _ _ hact, hax, LnockAxisOf_natCast three_lt_char]
  · rw [s2_ts _ _ _ hact]; simp [verifyRowTemplate]

/-- **Honest IO.**  The S2 verify row's IO is the compute request's single encode
`encRecFormR (requestRecord z α) λ` — the record `V_comp` emits (`computeRow`'s `mr`). -/
theorem concrete_s2_io (z lmb α : K73cubic) :
    (s2Specialize lmb α (verifyRowTemplate z)).io = LencRecFormR (requestRecord z α) lmb := by
  have hact : memoryMemRecKind (verifyRowTemplate z).timestamp.state = .active := by
    simp [verifyRowTemplate, memoryMemRecKind]
  rw [s2_io_eq_compute_encode _ _ _ hact]
  congr 1
  simp [MemoryRowTemplate.specializeA, verifyRowTemplate, verifyPubA, requestRecord,
    specializeMemRec, memoryMemRecKind]

theorem pwScale_K73 : LpwScaleExp K73cubic = 6 := by
  simp only [LpwScaleExp, ringChar_K73]; decide

/-- **Form R ROOTZERO on the S2 row, `(T, C')` READ from the row.**  The authority's gates
(`verify_child`, one `decompose` per path bit of `3`, `read_root`) close both accumulators at
every `λ` with the row's own columns (`Batch590.rootzero_general`). -/
theorem concrete_s2_rootzero (z lmb α : K73cubic) :
    readResidual lmb (s2Specialize lmb α (verifyRowTemplate z)).row.2.2.mem.axis
        (s2Specialize lmb α (verifyRowTemplate z)).cprime
        (s2Specialize lmb α (verifyRowTemplate z)).row.2.2.mem.ts
        (upWalk lmb (verifyCell lmb (s2Specialize lmb α (verifyRowTemplate z)).row.2.2.mem.ts)
          (pathBits 3)) = (0, 0) := by
  obtain ⟨h1, h2, h3⟩ := concrete_s2_row z lmb α
  rw [h1, h2, h3]
  exact rootzero_general lmb α 3 (by rw [pwScale_K73]; decide)

end Concrete

end Nock.RedTeam.Batch591

#print axioms Nock.RedTeam.Batch591.s2_io_eq_compute_encode
#print axioms Nock.RedTeam.Batch591.s2_lambda
#print axioms Nock.RedTeam.Batch591.specializedProblem_exec_is_specialize
#print axioms Nock.RedTeam.Batch591.split_requires_collision
#print axioms Nock.RedTeam.Batch591.p8_split_forces_equal_at_two
#print axioms Nock.RedTeam.Batch591.s2_wrap_reencodes
#print axioms Nock.RedTeam.Batch591.wrapJoin_identity_iff
#print axioms Nock.RedTeam.Batch591.readTemplateTree_eq_X
#print axioms Nock.RedTeam.Batch591.concrete_boundary_eval
#print axioms Nock.RedTeam.Batch591.s1_concrete_boundary
#print axioms Nock.RedTeam.Batch591.rowlevel_concrete_boundary_fails
#print axioms Nock.RedTeam.Batch591.concrete_s2_row
#print axioms Nock.RedTeam.Batch591.concrete_s2_io
#print axioms Nock.RedTeam.Batch591.concrete_s2_rootzero
