import Nock.NockVMROM.Thm54.VclL.Compute.RecReaderQ7

/-!
# V4T6 : `node_records` at the VCL compute chip — the row-to-record link

.

* `exportRecsQ7` / `pathRecsQ7` — the accumulators' committed request records, which ARE
  `(exportReqFactsQ7S …).records` / `(pathReqFactsQ7S …).records` (`rfl`, any acceptance proof).
* `mem_activeRecords` — an active slot's record is committed.
* `decodePub_e_oneHot` / `decodePub_sf2f_oneHot` — the two restored (overlay-hosted) `Pub` roles
  the path records read are the physical ones at a one-hot row off the overlay states.
* `label_vcomp` — `Vcomp` and the one-hot state at every patched row label (`WalkQ7.vcomp_at`),
  so `mr1/mr2/mr3` are `expectedMr*` (`records_eq_expected_of_vcomp`): the root / child are
  fingerprints, never the ungated `ts`.
* **`row_records_Q7`** (per row) and **`node_records_Q7`** (per node of `treeV`).

Premises: acceptance at `computeChipVCLQ7S`, injective adjacent nodes, `N ≤ char`, and the
`z ≠ 0` / `z·z⁻¹` coin facts (`WalkQ7.frame_coins`).  No summand event, no trace premise.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace NodeRecQ7

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Reified Nock.Framework Nock.Framework.Reify Module
open Nock.ComputeTable (State DTcomp FP MemRec Vcomp)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.ComputePaperPacking (OneHotSelector oneHot_ofSubst)
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.SVWalk
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7
open Nock.NockVMROM.Thm54.VclL.Compute.TopoQ7 (lnPatch_pub_sfe)
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution (restoredPub_eval_of_oneHot)
open Nock.NockVMROM.Thm54.OptimizedComputeCodec (records_eq_expected_of_vcomp expectedMr1 expectedMr2
  expectedMr3)

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. Committed records -/

theorem mem_activeRecords {Kio : Type} [Field Kio] [DecidableEq Kio] {m : ℕ} (N ns : ℕ) (act : ℕ → ℕ → Kio)
    (rec : ℕ → ℕ → Fin m → Kio) (i s : ℕ) (hi : i < N) (hs : s < ns) (ha : act i s = 1) :
    rec i s ∈ activeRecords N ns act rec := by
  unfold activeRecords
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap]
  exact ⟨i, hi, s, hs, by simp [ha]⟩

section recs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq K]
  {hC : ℕ} {S : MemShape} {w : ℕ}

/-- The export accumulator's committed request records (`exportReqFactsQ7S`'s records). -/
def exportRecsQ7 (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) :
    List (Fin 11 → K) :=
  activeRecords V.N 3
    (fun i s => if i < V.N then
      actX (K := K) (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s else 0)
    (fun i s => recX11 V.basis (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s)

/-- The path accumulator's committed request records (`pathReqFactsQ7S`'s records). -/
def pathRecsQ7 (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) :
    List (Fin 8 → K) :=
  activeRecords V.N 2
    (fun i s => if i < V.N then
      actP (K := K) (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s else 0)
    (fun i s => recP V.basis (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s)

theorem exportReqFactsQ7S_records (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (Q : Fin w → F[X])
    (A : AcceptedRowsQ7S V.basis γc ρc V.N V.N
      (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal) chalV pubVal) :
    (exportReqFactsQ7S V.basis γc ρc V.N V.N
      (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal) chalV pubVal A).records =
      exportRecsQ7 V chalV pubVal Q := rfl

theorem pathReqFactsQ7S_records (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (Q : Fin w → F[X])
    (A : AcceptedRowsQ7S V.basis γc ρc V.N V.N
      (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal) chalV pubVal) :
    (pathReqFactsQ7S V.basis γc ρc V.N V.N
      (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal) chalV pubVal A).records =
      pathRecsQ7 V chalV pubVal Q := rfl

theorem rowEnvs_row (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (r : Fin V.N) :
    rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal r = rawEnvQ7 V chalV pubVal Q r := by
  simp [rowEnvs, r.isLt, rawEnvQ7]

theorem mem_exportRecs (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (r : Fin V.N) (s : ℕ) (hs : s < 3) (ha : actX (K := K) (rawEnvQ7 V chalV pubVal Q r) s = 1) :
    recX11 V.basis (rawEnvQ7 V chalV pubVal Q r) s ∈ exportRecsQ7 V chalV pubVal Q := by
  rw [← rowEnvs_row V chalV pubVal Q r] at ha ⊢
  exact mem_activeRecords V.N 3
    (fun i s => if i < V.N then
      actX (K := K) (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s else 0)
    (fun i s => recX11 V.basis (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s)
    r s r.isLt hs (by simp only [r.isLt, if_true]; exact ha)

theorem mem_pathRecs (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (r : Fin V.N) (s : ℕ) (hs : s < 2) (ha : actP (K := K) (rawEnvQ7 V chalV pubVal Q r) s = 1) :
    recP V.basis (rawEnvQ7 V chalV pubVal Q r) s ∈ pathRecsQ7 V chalV pubVal Q := by
  rw [← rowEnvs_row V chalV pubVal Q r] at ha ⊢
  exact mem_activeRecords V.N 2
    (fun i s => if i < V.N then
      actP (K := K) (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s else 0)
    (fun i s => recP V.basis (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s)
    r s r.isLt hs (by simp only [r.isLt, if_true]; exact ha)

end recs

section recsG
variable {F K K' : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq K]
  [Field K'] [Algebra F K'] [DecidableEq K'] {G : CoordGather F K'} (R : RecReader G K)
  {hC : ℕ} {S : MemShape} {T : TableSpec} [WideTable T] {w : ℕ}

/-- **The export accumulator's committed records over a reader** (`exportRecsQ7` at `ofBasis`). -/
def exportRecsQ7G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) :
    List (Fin 11 → K') :=
  activeRecords V.N 3
    (fun i s => if i < V.N then
      R.actX (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s else 0)
    (fun i s => R.recX11 (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s)

/-- **The path accumulator's committed records over a reader.** -/
def pathRecsQ7G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) :
    List (Fin 8 → K') :=
  activeRecords V.N 2
    (fun i s => if i < V.N then
      R.actP (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s else 0)
    (fun i s => R.recP (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s)

theorem exportRecsQ7_eq_G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    [FiniteDimensional F K] [Fintype K] :
    exportRecsQ7 V chalV pubVal Q = exportRecsQ7G (recReaderOfBasis V.basis) V chalV pubVal Q := rfl

theorem pathRecsQ7_eq_G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    [Fintype K] :
    pathRecsQ7 V chalV pubVal Q = pathRecsQ7G (recReaderOfBasis V.basis) V chalV pubVal Q := rfl

theorem mem_exportRecsG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (r : Fin V.N) (s : ℕ) (hs : s < 3) (ha : R.actX (rawEnvQ7 V chalV pubVal Q r) s = 1) :
    R.recX11 (rawEnvQ7 V chalV pubVal Q r) s ∈ exportRecsQ7G R V chalV pubVal Q := by
  rw [← rowEnvs_row V chalV pubVal Q r] at ha ⊢
  exact mem_activeRecords V.N 3
    (fun i s => if i < V.N then
      R.actX (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s else 0)
    (fun i s => R.recX11 (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s)
    r s r.isLt hs (by simp only [r.isLt, if_true]; exact ha)

theorem mem_pathRecsG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (r : Fin V.N) (s : ℕ) (hs : s < 2) (ha : R.actP (rawEnvQ7 V chalV pubVal Q r) s = 1) :
    R.recP (rawEnvQ7 V chalV pubVal Q r) s ∈ pathRecsQ7G R V chalV pubVal Q := by
  rw [← rowEnvs_row V chalV pubVal Q r] at ha ⊢
  exact mem_activeRecords V.N 2
    (fun i s => if i < V.N then
      R.actP (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s else 0)
    (fun i s => R.recP (rowEnvs (h := hC) V.computeNodes V.orbitC.ω Q chalV pubVal i) s)
    r s r.isLt hs (by simp only [r.isLt, if_true]; exact ha)

end recsG

/-! ## 2./3. Activity of the slots and the decoded fingerprints (env-only lemmas, in `RecReaderQ7`) -/

section decode
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- `Pub.e` (role 2, overlay-hosted only at `s1`) is the physical role at a one-hot row off `s1`
(the 3-limb corollary of `decodePub_e_oneHotG`). -/
theorem decodePub_e_oneHot [FiniteDimensional F K] (b : Basis (Fin 3) F K) (env : Env F) (st st' : State)
    (hst : st ≠ .s1)
    (h : OneHotSelector (gatherCorrectedFinalTypedEnv b env).toSourceEnv st) :
    (StrategyOfTracesLift.decodePub (gatherCorrectedFinalTypedEnv b env) st').e = fpAt b env roleE :=
  (decodePub_e_oneHotG _ st st' hst h).trans rfl

/-- `Pub.sf2_f` (role 7, overlay-hosted only at `s3`/`s4`) is the physical role off those states. -/
theorem decodePub_sf2f_oneHot [FiniteDimensional F K] (b : Basis (Fin 3) F K) (env : Env F)
    (st st' : State) (hst : st ≠ .s3 ∧ st ≠ .s4)
    (h : OneHotSelector (gatherCorrectedFinalTypedEnv b env).toSourceEnv st) :
    (StrategyOfTracesLift.decodePub (gatherCorrectedFinalTypedEnv b env) st').sf2_f =
      fpAt b env roleSf2F :=
  (decodePub_sf2f_oneHotG _ st st' hst h).trans rfl

end decode


/-! ## 4. State bookkeeping -/

section states

theorem states_rc2 (st : State) (h : 1 < recordCount st) (hne : st ≠ .s0) :
    st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9 := by
  cases st <;> simp_all [recordCount]

theorem states_rc3 (st : State) (h : 2 < recordCount st) : st = .s6 ∨ st = .s9 := by
  cases st <;> simp_all [recordCount]

theorem rc_le3 (st : State) : recordCount st ≤ 3 := by cases st <;> decide

theorem jra0 (st : State) (ax : ℕ → ℕ) (S : ℕ) : joinRecordAxis st ax S 0 = 3 := by
  cases st <;> rfl

theorem jra1 (st : State) (ax : ℕ → ℕ) (S : ℕ) (h : st ≠ .s0) : joinRecordAxis st ax S 1 = 2 := by
  cases st <;> simp_all [joinRecordAxis]

theorem jra2 (st : State) (ax : ℕ → ℕ) (S : ℕ) (h : st ≠ .s9) : joinRecordAxis st ax S 2 = 2 := by
  cases st <;> simp_all [joinRecordAxis]

variable {K : Type} [Field K]

theorem mr2_tail (i : Nock.ComputeTable.Inputs K) (p : Nock.ComputeTable.Pub K)
    (d : Nock.ComputeTable.Dec K)
    (h : p.state = .s2 ∨ p.state = .s5 ∨ p.state = .s6 ∨ p.state = .s7 ∨ p.state = .s8 ∨
      p.state = .s9) :
    (expectedMr2 i p d).root = d.f_t ∧ (expectedMr2 i p d).child = d.f_th := by
  unfold expectedMr2
  rcases h with h | h | h | h | h | h <;> simp [h]

theorem mr2_s0 (i : Nock.ComputeTable.Inputs K) (p : Nock.ComputeTable.Pub K)
    (d : Nock.ComputeTable.Dec K) (h : p.state = .s0) :
    (expectedMr2 i p d).root = p.s ∧ (expectedMr2 i p d).child = p.e := by
  unfold expectedMr2; simp [h]

theorem mr3_s6 (i : Nock.ComputeTable.Inputs K) (p : Nock.ComputeTable.Pub K)
    (d : Nock.ComputeTable.Dec K) (h : p.state = .s6) :
    (expectedMr3 i p d).root = d.f_tt ∧ (expectedMr3 i p d).child = d.f_tth := by
  unfold expectedMr3; simp [h]

theorem mr3_s9 (i : Nock.ComputeTable.Inputs K) (p : Nock.ComputeTable.Pub K)
    (d : Nock.ComputeTable.Dec K) (h : p.state = .s9) :
    (expectedMr3 i p d).root = p.sf1_e ∧ (expectedMr3 i p d).child = p.sf2_f := by
  unfold expectedMr3; simp [h]

end states

/-! ## 5. `Vcomp` at the patched label and the row-to-record link -/

section rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hC : ℕ} {S : MemShape}

section rowsG
variable {F K K' : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [DecidableEq K]
  [Field K'] [Algebra F K'] [FiniteDimensional F K'] [Fintype K'] [DecidableEq K'] [CharP K' (ringChar K')]
  {G : CoordGather F K'} (R : RecReader G K) {hC : ℕ} {S : MemShape} {T : TableSpec} [WideTable T] {w : ℕ}

/-- **`Vcomp` and the one-hot state at every patched row label, at a gather** (`label_vcomp`). -/
theorem label_vcompG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (RF : RowFactsQ7 (cdOfGG G V chalV pubVal) chalV pubVal Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K') = 1 → n = 1)
    (hz : zQ (cdOfGG G V chalV pubVal) chalV ≠ 0)
    (hzi : G.chalSlot chalV 5 = (zQ (cdOfGG G V chalV pubVal) chalV)⁻¹) (r : Fin V.N) :
    OneHotSelector (envsVG G V chalV pubVal Q r).toSourceEnv (rowLabel (envsPG G V chalV pubVal Q r)).1 ∧
      Vcomp (rowLabel (envsPG G V chalV pubVal Q r)).2.1 (rowLabel (envsPG G V chalV pubVal Q r)).2.2.1
        (rowLabel (envsPG G V chalV pubVal Q r)).2.2.2 := by
  obtain ⟨st, hst, hV⟩ := vcomp_at (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar hz hzi r
  have hst' : (rowLabel (envsPG G V chalV pubVal Q r)).1 = st :=
    WrapFixesVcomp.computeStateOf_of_oneHot (oneHot_ofSubst _ _ hst)
  refine ⟨by rw [hst']; exact (oneHot_lnPatch_iff _ _).1 hst, ?_⟩
  unfold rowLabel at hst' ⊢
  simp only at hst' ⊢
  rw [hst']
  exact hV

/-- **The row-to-record link, per row, at a gather and a reader**: the acceptance-derived row
facts are the hypotheses `RF` (`RowFactsQ7`) and `hrow` (the row is one-hot and its decoded
state is that one-hot state). -/
theorem row_records_Q7G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F)
    (Q : Fin T.width → F[X])
    (RF : RowFactsQ7 (cdOfGG G V chalV pubVal) chalV pubVal Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K') = 1 → n = 1)
    (hz : zQ (cdOfGG G V chalV pubVal) chalV ≠ 0)
    (hzi : G.chalSlot chalV 5 = (zQ (cdOfGG G V chalV pubVal) chalV)⁻¹)
    (bm : ∀ t, B0Cols F (S.table t)) (r : Fin V.N)
    (hrow : ∃ st, SelAt (rawEnvQ7 V chalV pubVal Q r) st ∧
      (rowLabel (envsVG G V chalV pubVal Q r)).1 = st)
    /- At an `s0` / `s9` row the path slot is active, or the row serves its
    axis-1 read itself (record child = root, decoded axis `1`). -/
    (hP0 : SelAt (rawEnvQ7 V chalV pubVal Q r) .s0 → R.actP (rawEnvQ7 V chalV pubVal Q r) 0 = 1 ∨
      (RV.pathChild (R.recP (rawEnvQ7 V chalV pubVal Q r) 0) =
          RV.pathRoot (R.recP (rawEnvQ7 V chalV pubVal Q r) 0) ∧
        RecordCarrier.natLift (algebraMap F K ((rawEnvQ7 V chalV pubVal Q r).trace axCol)) = 1))
    (hP9 : SelAt (rawEnvQ7 V chalV pubVal Q r) .s9 → R.actP (rawEnvQ7 V chalV pubVal Q r) 1 = 1 ∨
      (RV.pathChild (R.recP (rawEnvQ7 V chalV pubVal Q r) 1) =
          RV.pathRoot (R.recP (rawEnvQ7 V chalV pubVal Q r) 1) ∧
        RecordCarrier.natLift (algebraMap F K ((rawEnvQ7 V chalV pubVal Q r).trace axCol)) = 1))
    (j : ℕ)
    (hj : j < recordCount (rowLabel (envsPG G V chalV pubVal Q r)).1) :
    (∃ x ∈ exportRecsQ7G R V chalV pubVal Q,
      (RV.recordViewVCL F K K' T S hC).root 1 x =
          (traceRecOf (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) j).root ∧
      (RV.recordViewVCL F K K' T S hC).child 1 x =
          (traceRecOf (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) j).child ∧
      (RV.recordViewVCL F K K' T S hC).key 1 x =
          recKeyQ7' V (b0 (T := T) Q) (rowLabel (envsPG G V chalV pubVal Q r)).1
            (2 * (r : ℕ)) j ∧
      (RV.recordViewVCL F K K' T S hC).axis 1 V (b0 (T := T) Q) bm x =
          joinRecordAxis (rowLabel (envsPG G V chalV pubVal Q r)).1
            (axB0Q7 V (b0 (T := T) Q)) (2 * (r : ℕ)) j) ∨
    (∃ x ∈ pathRecsQ7G R V chalV pubVal Q,
      (RV.recordViewVCL F K K' T S hC).root 2 x =
          (traceRecOf (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) j).root ∧
      (RV.recordViewVCL F K K' T S hC).child 2 x =
          (traceRecOf (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) j).child ∧
      (RV.recordViewVCL F K K' T S hC).key 2 x =
          recKeyQ7' V (b0 (T := T) Q) (rowLabel (envsPG G V chalV pubVal Q r)).1
            (2 * (r : ℕ)) j ∧
      (RV.recordViewVCL F K K' T S hC).axis 2 V (b0 (T := T) Q) bm x =
          joinRecordAxis (rowLabel (envsPG G V chalV pubVal Q r)).1
            (axB0Q7 V (b0 (T := T) Q)) (2 * (r : ℕ)) j) ∨
    ((((rowLabel (envsPG G V chalV pubVal Q r)).1 = .s0 ∧ j = 1) ∨
        ((rowLabel (envsPG G V chalV pubVal Q r)).1 = .s9 ∧ j = 2)) ∧
      joinRecordAxis (rowLabel (envsPG G V chalV pubVal Q r)).1
        (axB0Q7 V (b0 (T := T) Q)) (2 * (r : ℕ)) j = 1 ∧
      (traceRecOf (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) j).child =
        (traceRecOf (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) j).root) := by
  obtain ⟨st, hsel, hst⟩ := hrow
  have hL1 : (rowLabel (envsPG G V chalV pubVal Q r)).1 = st := by
    rw [← hst, rowLabel_fst, rowLabel_fst]; rfl
  obtain ⟨hone, hV⟩ := label_vcompG V chalV pubVal Q RF hchar hz hzi r
  obtain ⟨hm1, hm2, hm3⟩ := records_eq_expected_of_vcomp hV
  have hps : (rowLabel (envsPG G V chalV pubVal Q r)).2.2.1.state = st := hL1
  have hsfe := lnPatch_pub_sfe (envsVG G V chalV pubVal Q r) (rowLabel (envsPG G V chalV pubVal Q r)).1
  simp only at hsfe
  obtain ⟨-, hs_, hf_, he_, -, -, hsf1e_, -, hsf2f_, -⟩ := hsfe
  have hdec : (rowLabel (envsPG G V chalV pubVal Q r)).2.2.2 =
      StrategyOfTracesLift.decodeDec (envsVG G V chalV pubVal Q r) := decodeDec_lnPatch _
  have hpub : (rowLabel (envsPG G V chalV pubVal Q r)).2.2.1 =
      StrategyOfTracesLift.decodePub (lnPatch (envsVG G V chalV pubVal Q r))
        (rowLabel (envsPG G V chalV pubVal Q r)).1 := rfl
  -- the readers' laws, at the raw row (the gathered base is `envsVG` by `rfl`)
  have hgb : gatheredBase G (rawEnvQ7 V chalV pubVal Q r) = envsVG G V chalV pubVal Q r := rfl
  have tr0 : ∀ L : (State × DTcomp K') × ℕ, traceRecOf L 0 = L.1.2.2.1.mr1 := fun _ => rfl
  have tr1 : ∀ L : (State × DTcomp K') × ℕ, traceRecOf L 1 = L.1.2.2.1.mr2 := fun _ => rfl
  have tr2 : ∀ L : (State × DTcomp K') × ℕ, traceRecOf L 2 = L.1.2.2.1.mr3 := fun _ => rfl
  rw [hL1] at hj ⊢
  rcases j with _ | _ | _ | j
  · -- record 0: the formula cell, export slot 0
    left
    refine ⟨_, mem_exportRecsG R V chalV pubVal Q r 0 (by norm_num) (R.actX_zero _), ?_, ?_, ?_, ?_⟩
    · rw [tr0, hm1]; show _ = (rowLabel (envsPG G V chalV pubVal Q r)).2.2.1.f
      rw [hpub, hf_]; exact R.xroot0 _ _
    · show RV.exportChild _ = _
      rw [R.xchild0, tr0, hm1]
      show _ = (rowLabel (envsPG G V chalV pubVal Q r)).2.2.2.f_t
      rw [hdec]; rfl
    · exact export_key_clauseQ7G R V chalV pubVal Q r st 0 (Or.inl rfl)
    · show RV.exportAxis _ = _
      rw [R.xaxis _ 0 (by norm_num), if_pos rfl, jra0]
  · by_cases h0 : st = .s0
    · subst h0
      have hroot : RV.pathRoot (R.recP (rawEnvQ7 V chalV pubVal Q r) 0) =
          (traceRecOf (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) 1).root := by
        rw [tr1, hm2, (mr2_s0 _ _ _ hps).1]
        show _ = (rowLabel (envsPG G V chalV pubVal Q r)).2.2.1.s
        rw [hpub, hs_]; exact R.proot0 _ _
      have hchild : RV.pathChild (R.recP (rawEnvQ7 V chalV pubVal Q r) 0) =
          (traceRecOf (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) 1).child := by
        rw [tr1, hm2, (mr2_s0 _ _ _ hps).2]
        show _ = (rowLabel (envsPG G V chalV pubVal Q r)).2.2.1.e
        rw [hpub, he_]
        rw [hL1] at hone
        exact R.pchild0 _ _ _ hone (by decide)
      rcases hP0 hsel with hact | ⟨hcr, hax⟩
      swap
      · -- The axis-1 read, served by the row's own gates
        right; right
        refine ⟨Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
        · show axB0Q7 V (b0 (T := T) Q) (2 * (r : ℕ) + 2) = 1
          rw [axB0Q7_s0, b0NatAt_row V chalV pubVal Q r]; exact hax
        · rw [← hroot, ← hchild]; exact hcr
      right; left
      refine ⟨_, mem_pathRecsG R V chalV pubVal Q r 0 (by norm_num) hact, hroot, hchild, ?_, ?_⟩
      · show RV.pathKey _ = _
        rw [path_key_clauseQ7G R V chalV pubVal Q r 0 (by norm_num)]; rfl
      · show RV.pathAxis _ = axB0Q7 V (b0 (T := T) Q) (2 * (r : ℕ) + 2)
        rw [R.paxis _ 0 (by norm_num), axB0Q7_s0, b0NatAt_row V chalV pubVal Q r]
    · have hx := states_rc2 st hj h0
      left
      refine ⟨_, mem_exportRecsG R V chalV pubVal Q r 1 (by norm_num)
        (R.actX_one _ st hsel hx), ?_, ?_, ?_, ?_⟩
      · rw [tr1, hm2, (mr2_tail _ _ _ (hps ▸ hx)).1]
        show _ = (rowLabel (envsPG G V chalV pubVal Q r)).2.2.2.f_t
        rw [hdec]; exact R.xroot1 _
      · show RV.exportChild _ = _
        rw [R.xchild1, tr1, hm2, (mr2_tail _ _ _ (hps ▸ hx)).2]
        show _ = (rowLabel (envsPG G V chalV pubVal Q r)).2.2.2.f_th
        rw [hdec]; rfl
      · exact export_key_clauseQ7G R V chalV pubVal Q r st 1 (Or.inr (Or.inl ⟨rfl, h0⟩))
      · show RV.exportAxis _ = _
        rw [R.xaxis _ 1 (by norm_num), if_neg (by decide), jra1 st _ _ h0]
  · rcases states_rc3 st hj with rfl | rfl
    · left
      refine ⟨_, mem_exportRecsG R V chalV pubVal Q r 2 (by norm_num) (R.actX_two _ hsel), ?_, ?_, ?_, ?_⟩
      · rw [tr2, hm3, (mr3_s6 _ _ _ hps).1]
        show _ = (rowLabel (envsPG G V chalV pubVal Q r)).2.2.2.f_tt
        rw [hdec]; exact R.xroot2 _
      · show RV.exportChild _ = _
        rw [R.xchild2, tr2, hm3, (mr3_s6 _ _ _ hps).2]
        show _ = (rowLabel (envsPG G V chalV pubVal Q r)).2.2.2.f_tth
        rw [hdec]; rfl
      · exact export_key_clauseQ7G R V chalV pubVal Q r .s6 2 (Or.inr (Or.inr ⟨rfl, by decide⟩))
      · show RV.exportAxis _ = _
        rw [R.xaxis _ 2 (by norm_num), if_neg (by decide), jra2 _ _ _ (by decide)]
    · have hroot : RV.pathRoot (R.recP (rawEnvQ7 V chalV pubVal Q r) 1) =
          (traceRecOf (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) 2).root := by
        rw [tr2, hm3, (mr3_s9 _ _ _ hps).1]
        show _ = (rowLabel (envsPG G V chalV pubVal Q r)).2.2.1.sf1_e
        rw [hpub, hsf1e_]; exact R.proot1 _ _
      have hchild : RV.pathChild (R.recP (rawEnvQ7 V chalV pubVal Q r) 1) =
          (traceRecOf (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) 2).child := by
        rw [tr2, hm3, (mr3_s9 _ _ _ hps).2]
        show _ = (rowLabel (envsPG G V chalV pubVal Q r)).2.2.1.sf2_f
        rw [hpub, hsf2f_]
        rw [hL1] at hone
        exact R.pchild1 _ _ _ hone ⟨by decide, by decide⟩
      rcases hP9 hsel with hact | ⟨hcr, hax⟩
      swap
      · -- OP9's axis-1 arm, served by the row's own gates
        right; right
        refine ⟨Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
        · show axB0Q7 V (b0 (T := T) Q) (2 * (r : ℕ) + 3) = 1
          rw [axB0Q7_s9, b0NatAt_row V chalV pubVal Q r]; exact hax
        · rw [← hroot, ← hchild]; exact hcr
      right; left
      refine ⟨_, mem_pathRecsG R V chalV pubVal Q r 1 (by norm_num) hact, hroot, hchild, ?_, ?_⟩
      · show RV.pathKey _ = _
        rw [path_key_clauseQ7G R V chalV pubVal Q r 1 (by norm_num)]; rfl
      · show RV.pathAxis _ = axB0Q7 V (b0 (T := T) Q) (2 * (r : ℕ) + 3)
        rw [R.paxis _ 1 (by norm_num), axB0Q7_s9, b0NatAt_row V chalV pubVal Q r]
  · exfalso; have := rc_le3 st; omega

/-- **The tree-node → row lemma, at a gather** (`treeV_node_row`). -/
theorem treeVG_node_row (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
    (u : NTree ((State × DTcomp K') × ℕ)) (hu : InTree (treeVG G V chalV pubVal Q) u) :
    ∃ r : Fin V.N, u.label =
      (rowLabel (envsPG G V chalV pubVal Q r), 2 * rowCarrier (envsPG G V chalV pubVal Q r)) := by
  obtain ⟨v, hv, hl⟩ := inTree_mapNTree _ _ u hu
  unfold treeV1G computeTree treeOfRows reconTree at hv
  obtain ⟨j, hj⟩ := inTree_buildT_label _ _ _ _ v hv
  refine ⟨if h : j - 1 < V.N then ⟨j - 1, h⟩ else ⟨0, V.hN⟩, ?_⟩
  rw [hl, hj]
  unfold at1
  split_ifs <;> rfl

/-- **The node carrier of row `r` is `r`, at a gather**, from the serial column (an acceptance fact,
the interface hypothesis) and `N ≤ char`. -/
theorem rowCarrier_eq_rowG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X])
    (hser : ∀ r : Fin V.N, (rawEnvQ7 V chalV pubVal Q r).trace serialCol = (r : F))
    (hNp : V.N ≤ ringChar K') (r : Fin V.N) :
    rowCarrier (envsVG G V chalV pubVal Q r) = r := by
  unfold rowCarrier
  rw [envsVG_expCol (T := T)]
  have h := hser r
  have he : (Q ⟨220, by have := WideTable.hw (T := T); omega⟩).eval (V.computeNodes r) = (r : F) := by
    rw [← h]; simp [rawEnvQ7, envOfTrace, serialCol, show 220 < T.width from by have := WideTable.hw (T := T); omega]
  rw [he, map_natCast]
  exact RecordCarrier.natLift_natCast (by omega)

/-- The committed request records per accumulator, over a reader. -/
def reqRecsQ7G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) :
    ∀ a : Fin 3, List (Fin (RV.mVCL a) → K')
  | 0 => []
  | 1 => exportRecsQ7G R V chalV pubVal Q
  | 2 => pathRecsQ7G R V chalV pubVal Q

/-- **`node_records` at a gather and a reader** (the frame field's conclusion): the acceptance
facts are the interface hypotheses `RF`, `hrow`, `hser` (and `N ≤ char K'`). -/
theorem node_records_Q7G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F)
    (Q : Fin T.width → F[X])
    (RF : RowFactsQ7 (cdOfGG G V chalV pubVal) chalV pubVal Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K') = 1 → n = 1)
    (hz : zQ (cdOfGG G V chalV pubVal) chalV ≠ 0)
    (hzi : G.chalSlot chalV 5 = (zQ (cdOfGG G V chalV pubVal) chalV)⁻¹)
    (hrow : ∀ r : Fin V.N, ∃ st, SelAt (rawEnvQ7 V chalV pubVal Q r) st ∧
      (rowLabel (envsVG G V chalV pubVal Q r)).1 = st)
    (hser : ∀ r : Fin V.N, (rawEnvQ7 V chalV pubVal Q r).trace serialCol = (r : F))
    (hP0 : ∀ r : Fin V.N, SelAt (rawEnvQ7 V chalV pubVal Q r) .s0 →
      R.actP (rawEnvQ7 V chalV pubVal Q r) 0 = 1 ∨
      (RV.pathChild (R.recP (rawEnvQ7 V chalV pubVal Q r) 0) =
          RV.pathRoot (R.recP (rawEnvQ7 V chalV pubVal Q r) 0) ∧
        RecordCarrier.natLift (algebraMap F K ((rawEnvQ7 V chalV pubVal Q r).trace axCol)) = 1))
    (hP9 : ∀ r : Fin V.N, SelAt (rawEnvQ7 V chalV pubVal Q r) .s9 →
      R.actP (rawEnvQ7 V chalV pubVal Q r) 1 = 1 ∨
      (RV.pathChild (R.recP (rawEnvQ7 V chalV pubVal Q r) 1) =
          RV.pathRoot (R.recP (rawEnvQ7 V chalV pubVal Q r) 1) ∧
        RecordCarrier.natLift (algebraMap F K ((rawEnvQ7 V chalV pubVal Q r).trace axCol)) = 1))
    (hNp : V.N ≤ ringChar K') (bm : ∀ t, B0Cols F (S.table t))
    (u : NTree ((State × DTcomp K') × ℕ)) (hu : InTree (treeVG G V chalV pubVal Q) u)
    (j : ℕ) (hj : j < recordCount u.label.1.1) :
    (∃ a : Fin 3, ∃ x ∈ reqRecsQ7G R V chalV pubVal Q a,
      (RV.recordViewVCL F K K' T S hC).root a x = (traceRecOf u.label j).root ∧
      (RV.recordViewVCL F K K' T S hC).child a x = (traceRecOf u.label j).child ∧
      (RV.recordViewVCL F K K' T S hC).key a x =
        recKeyQ7' V (b0 (T := T) Q) u.label.1.1 u.label.2 j ∧
      (RV.recordViewVCL F K K' T S hC).axis a V (b0 (T := T) Q) bm x =
        joinRecordAxis u.label.1.1 (axB0Q7 V (b0 (T := T) Q)) u.label.2 j) ∨
    (((u.label.1.1 = .s0 ∧ j = 1) ∨ (u.label.1.1 = .s9 ∧ j = 2)) ∧
      joinRecordAxis u.label.1.1 (axB0Q7 V (b0 (T := T) Q)) u.label.2 j = 1 ∧
      (traceRecOf u.label j).child = (traceRecOf u.label j).root) := by
  obtain ⟨r, hr⟩ := treeVG_node_row (G := G) V chalV pubVal Q u hu
  have hl : u.label = (rowLabel (envsPG G V chalV pubVal Q r), 2 * (r : ℕ)) := by
    rw [hr, show rowCarrier (envsPG G V chalV pubVal Q r) = rowCarrier (envsVG G V chalV pubVal Q r) from rfl,
      rowCarrier_eq_rowG V chalV pubVal Q hser hNp r]
  rw [hl] at hj ⊢
  rcases row_records_Q7G R V chalV pubVal Q RF hchar hz hzi bm r (hrow r) (hP0 r) (hP9 r) j hj with
    ⟨x, hx, h⟩ | ⟨x, hx, h⟩ | h
  · exact Or.inl ⟨1, x, hx, h⟩
  · exact Or.inl ⟨2, x, hx, h⟩
  · exact Or.inr h

end rowsG

/-- **`Vcomp` and the one-hot state at every patched row label** (`WalkQ7.vcomp_at`, as `TopoQ7.lblQ_row`). -/
theorem label_vcomp (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
    (RF : RowFactsQ7 (cdOfG V chalV pubVal) chalV pubVal Q)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz : zQ (cdOfG V chalV pubVal) chalV ≠ 0)
    (hzi : slotK V.basis chalV 5 = (zQ (cdOfG V chalV pubVal) chalV)⁻¹) (r : Fin V.N) :
    OneHotSelector (envsV V chalV pubVal Q r).toSourceEnv (rowLabel (envsP V chalV pubVal Q r)).1 ∧
      Vcomp (rowLabel (envsP V chalV pubVal Q r)).2.1 (rowLabel (envsP V chalV pubVal Q r)).2.2.1
        (rowLabel (envsP V chalV pubVal Q r)).2.2.2 := by
  obtain ⟨st, hst, hV⟩ := vcomp_at (cdOfG V chalV pubVal) chalV pubVal Q RF hchar hz hzi r
  have hst' : (rowLabel (envsP V chalV pubVal Q r)).1 = st :=
    WrapFixesVcomp.computeStateOf_of_oneHot (oneHot_ofSubst _ _ hst)
  refine ⟨by rw [hst']; exact (oneHot_lnPatch_iff _ _).1 hst, ?_⟩
  unfold rowLabel at hst' ⊢
  simp only at hst' ⊢
  rw [hst']
  exact hV

/-- **The row-to-record link, per row**: record `j < recordCount st` of compute row `r` (label
`(rowLabel (envsP r), 2r)`) is a committed export (`a = 1`) or path (`a = 2`) request record whose
root / child are the label's trace record, key `recKeyQ7'`, axis `joinRecordAxis` at `axB0Q7`. -/
theorem row_records_Q7 (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (Q : Fin 232 → F[X]) (hinj : Function.Injective V.computeNodes)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC) Q)
    (hz : zQ (cdOfG V chalV pubVal) chalV ≠ 0)
    (hzi : slotK V.basis chalV 5 = (zQ (cdOfG V chalV pubVal) chalV)⁻¹)
    (bm : ∀ t, B0Cols F (S.table t)) (r : Fin V.N) (j : ℕ)
    (hj : j < recordCount (rowLabel (envsP V chalV pubVal Q r)).1) :
    (∃ x ∈ exportRecsQ7 V chalV pubVal Q,
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).root 1 x =
          (traceRecOf (rowLabel (envsP V chalV pubVal Q r), 2 * (r : ℕ)) j).root ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).child 1 x =
          (traceRecOf (rowLabel (envsP V chalV pubVal Q r), 2 * (r : ℕ)) j).child ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).key 1 x =
          recKeyQ7' V (b0 (T := tableVCLE hC) Q) (rowLabel (envsP V chalV pubVal Q r)).1
            (2 * (r : ℕ)) j ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).axis 1 V (b0 (T := tableVCLE hC) Q) bm x =
          joinRecordAxis (rowLabel (envsP V chalV pubVal Q r)).1
            (axB0Q7 V (b0 (T := tableVCLE hC) Q)) (2 * (r : ℕ)) j) ∨
    (∃ x ∈ pathRecsQ7 V chalV pubVal Q,
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).root 2 x =
          (traceRecOf (rowLabel (envsP V chalV pubVal Q r), 2 * (r : ℕ)) j).root ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).child 2 x =
          (traceRecOf (rowLabel (envsP V chalV pubVal Q r), 2 * (r : ℕ)) j).child ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).key 2 x =
          recKeyQ7' V (b0 (T := tableVCLE hC) Q) (rowLabel (envsP V chalV pubVal Q r)).1
            (2 * (r : ℕ)) j ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).axis 2 V (b0 (T := tableVCLE hC) Q) bm x =
          joinRecordAxis (rowLabel (envsP V chalV pubVal Q r)).1
            (axB0Q7 V (b0 (T := tableVCLE hC) Q)) (2 * (r : ℕ)) j) ∨
    ((((rowLabel (envsP V chalV pubVal Q r)).1 = .s0 ∧ j = 1) ∨
        ((rowLabel (envsP V chalV pubVal Q r)).1 = .s9 ∧ j = 2)) ∧
      joinRecordAxis (rowLabel (envsP V chalV pubVal Q r)).1
        (axB0Q7 V (b0 (T := tableVCLE hC) Q)) (2 * (r : ℕ)) j = 1 ∧
      (traceRecOf (rowLabel (envsP V chalV pubVal Q r), 2 * (r : ℕ)) j).child =
        (traceRecOf (rowLabel (envsP V chalV pubVal Q r), 2 * (r : ℕ)) j).root) := by
  have RF := RowFactsQ7.of_satS (cdOf V chalV pubVal) chalV pubVal Q γc ρc hinj hsat
  exact row_records_Q7G (T := tableVCLE hC) (recReaderOfBasis V.basis) V chalV pubVal Q RF hchar hz hzi bm r
    (by obtain ⟨st, hsel, hst, -⟩ := row_ax_facts V γc ρc chalV pubVal Q hchar hsat r
        exact ⟨st, hsel, hst⟩)
    (fun h => Or.inl (actP_zero_s0 _ h)) (fun h => Or.inl (actP_one_s9 _ h)) j hj

/-- The committed request records per accumulator (`0` validity: none on the compute side). -/
def reqRecsQ7 (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) :
    ∀ a : Fin 3, List (Fin (RV.mVCL a) → K)
  | 0 => []
  | 1 => exportRecsQ7 V chalV pubVal Q
  | 2 => pathRecsQ7 V chalV pubVal Q

/-- **`node_records` at the VCL compute chip** (the frame field's conclusion, `inlineRecords = 0`):
every node of `treeV` and every `j < recordCount st` has a committed request record (export or
path accumulator) with the node's trace-record root / child, key `recKeyQ7'` at the node's label,
and axis `joinRecordAxis` at `axB0Q7`.  No summand event is used. -/
theorem node_records_Q7 (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (Q : Fin 232 → F[X]) (hadj : V.AdjacentC) (hinj : Function.Injective V.computeNodes)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC) Q)
    (hNp : V.N ≤ ringChar K)
    (hz : zQ (cdOfG V chalV pubVal) chalV ≠ 0)
    (hzi : slotK V.basis chalV 5 = (zQ (cdOfG V chalV pubVal) chalV)⁻¹)
    (bm : ∀ t, B0Cols F (S.table t))
    (u : NTree ((State × DTcomp K) × ℕ)) (hu : InTree (treeV V chalV pubVal Q) u)
    (j : ℕ) (hj : j < recordCount u.label.1.1) :
    (∃ a : Fin 3, ∃ x ∈ reqRecsQ7 V chalV pubVal Q a,
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).root a x = (traceRecOf u.label j).root ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).child a x = (traceRecOf u.label j).child ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).key a x =
        recKeyQ7' V (b0 (T := tableVCLE hC) Q) u.label.1.1 u.label.2 j ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).axis a V (b0 (T := tableVCLE hC) Q) bm x =
        joinRecordAxis u.label.1.1 (axB0Q7 V (b0 (T := tableVCLE hC) Q)) u.label.2 j) ∨
    (((u.label.1.1 = .s0 ∧ j = 1) ∨ (u.label.1.1 = .s9 ∧ j = 2)) ∧
      joinRecordAxis u.label.1.1 (axB0Q7 V (b0 (T := tableVCLE hC) Q)) u.label.2 j = 1 ∧
      (traceRecOf u.label j).child = (traceRecOf u.label j).root) := by
  have RF := RowFactsQ7.of_satS (cdOf V chalV pubVal) chalV pubVal Q γc ρc hinj hsat
  exact node_records_Q7G (T := tableVCLE hC) (recReaderOfBasis V.basis) V chalV pubVal Q RF hchar hz hzi
    (fun r => by
      obtain ⟨st, hsel, hst, -⟩ := row_ax_facts V γc ρc chalV pubVal Q hchar hsat r
      exact ⟨st, hsel, hst⟩)
    (serial_eq_row V γc ρc chalV pubVal Q hadj hinj hsat)
    (fun _ h => Or.inl (actP_zero_s0 _ h)) (fun _ h => Or.inl (actP_one_s9 _ h)) hNp bm u hu j hj

end rows

end

end NodeRecQ7
end VclL.Compute
end Nock.NockVMROM.Thm54
