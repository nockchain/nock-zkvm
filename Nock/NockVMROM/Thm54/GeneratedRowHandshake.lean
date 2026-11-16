import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.BoundSemanticTrace
import Nock.NockVMROM.Thm54.GlobalOpcodeScheduling
import Nock.NockVMROM.Thm54.GenericHonestCommitment

/-!
# Handshake: generated covered rows → reconstruction + C5

The generator builds `ComputeRowSemanticData` from a pre-seed skeleton via
`BoundSemanticTrace.buildCoveredRow` / `ofSkeleton` (literals, not
`chooseNoun`).  The reconstruction constructor reads
`computeSkeletonOf` / `dataOfCertificates`.  This module identifies the
two on covered rows and packages C5 without adding a field of `E`.

`LocalOpcodeCertificate` still needs `Vcomp` and child `evalFBy` — those
are the generator's 11-case obligations, not invented here.
`PairedRecordLayout` stays a Type extra (`memoryRecordPremises_of_paired_record_layout`).

Paper: `V_comp` `1728-1801`, OP0 `1751`, OP9 `1737-1738`, `NockProgram^Λ`
`1090-1098`, IO matching `1415-1431`.  Capstone type untouched. `11+1+2`
unchanged. `Gen.lean` / `BFSAssign.lean` not edited.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.GeneratedRowHandshake

open scoped Classical
open Nock
open ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GlobalOpcodeScheduling
open Nock.NockVMROM.Thm54.HonestCommitment

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Covered row data is `buildCoveredRow.1` -/

abbrev coveredRow
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    ComputeRowSemanticData q Λ row :=
  (buildCoveredRow hb hop hbind hfaith hleaves).1

/-- Covered root subject is the generated skeleton subject -/
@[simp] theorem covered_root_subject
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (coveredRow hb hop hbind hfaith hleaves).root.subject = s.subject := by
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state <;> rfl

@[simp] theorem covered_root_formula
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (coveredRow hb hop hbind hfaith hleaves).root.formula = s.formula := by
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state <;> rfl

@[simp] theorem covered_root_result
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (coveredRow hb hop hbind hfaith hleaves).root.result = s.evaluation := by
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state <;> rfl

@[simp] theorem covered_root_head
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (coveredRow hb hop hbind hfaith hleaves).root.head =
      P8Census.skeletonDec s .f_h := by
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state <;> rfl

@[simp] theorem covered_root_tail
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (coveredRow hb hop hbind hfaith hleaves).root.tail =
      P8Census.skeletonDec s .f_t := by
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state <;> rfl

@[simp] theorem covered_comparisons
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (coveredRow hb hop hbind hfaith hleaves).comparisons =
      P8Census.skeletonComparisons (K := K) s :=
  buildCoveredRow_comparisons hb hop hbind hfaith hleaves

/-! ## Reconstruction of a covered row -/

theorem covered_decomp_head
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hact : decActive row.1 .f_h = true) :
    decompNoun (coveredRow hb hop hbind hfaith hleaves) .f_h =
      s.decomposition .f_h (by simpa [hbind.1] using hact) := by
  have hactS : decActive s.state .f_h = true := by simpa [hbind.1] using hact
  rw [decompNoun, covered_root_head, P8Census.skeletonDec, dif_pos hactS]

theorem covered_decomp_tail
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hact : decActive row.1 .f_t = true) :
    decompNoun (coveredRow hb hop hbind hfaith hleaves) .f_t =
      s.decomposition .f_t (by simpa [hbind.1] using hact) := by
  have hactS : decActive s.state .f_t = true := by simpa [hbind.1] using hact
  rw [decompNoun, covered_root_tail, P8Census.skeletonDec, dif_pos hactS]

/-- Public-row realization of a covered row is the skeleton nouns themselves. -/
def coveredPubR
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hz : z ≠ 0)
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    ComputePublicRowNounRealization q (computePublicLabel row) :=
  let _ := hop; let _ := hfaith; let _ := hleaves
  bindComputeRow_realized hz hb hbind

/-- Reconstruction state, subject, formula, evaluation of a covered row
are the generated skeleton.  Subformula slots follow when the generated
call nouns sit in `NockProgram^Λ` -/
theorem computeSkeletonOf_covered_root
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hz : z ≠ 0)
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    let data := coveredRow hb hop hbind hfaith hleaves
    let pubR := coveredPubR hz hb hop hbind hfaith hleaves
    (computeSkeletonOf data pubR).state = s.state ∧
      (computeSkeletonOf data pubR).subject = s.subject ∧
      (computeSkeletonOf data pubR).formula = s.formula ∧
      (computeSkeletonOf data pubR).evaluation = s.evaluation := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [computeSkeletonOf, hbind.1]
  · simp [computeSkeletonOf, covered_root_subject hb hop hbind hfaith hleaves]
  · simp [computeSkeletonOf, covered_root_formula hb hop hbind hfaith hleaves]
  · simp [computeSkeletonOf, covered_root_result hb hop hbind hfaith hleaves]

theorem computeSkeletonOf_covered_decomp
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hz : z ≠ 0)
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (slot : DecSlot)
    (hact : decActive s.state slot = true) :
    let data := coveredRow hb hop hbind hfaith hleaves
    let pubR := coveredPubR hz hb hop hbind hfaith hleaves
    (computeSkeletonOf data pubR).decomposition slot
        (by simpa [computeSkeletonOf, hbind.1] using hact) =
      s.decomposition slot hact := by
  have hrow : decActive row.1 slot = true := by simpa [hbind.1] using hact
  cases slot with
  | f_h =>
      simpa [computeSkeletonOf] using
        covered_decomp_head hb hop hbind hfaith hleaves hrow
  | f_t =>
      simpa [computeSkeletonOf] using
        covered_decomp_tail hb hop hbind hfaith hleaves hrow
  | f_th | f_tt | f_tth | f_ttt =>
      -- Tail/branch slots: `decompNoun` reads `tails` / `branchTails`,
      -- which `buildCoveredRow` fills from `s.decomposition`.
      rcases s with ⟨state, subject, formula, evaluation,
        decomposition, subformula, memoryRecord⟩
      rcases row with ⟨rowState, inp, pub, dec⟩
      rcases hbind with
        ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
          hdec, hsf, hmr⟩
      change rowState = state at hrowState
      subst rowState
      cases state <;> first | rfl | cases hact

theorem covered_calls_length
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ) :
    (coveredRow hb hop hbind hfaith hleaves).calls.length =
      fanoutComp row.1 := by
  simpa [requiredCallRealizations_eq_fanout] using
    (coveredRow hb hop hbind hfaith hleaves).calls_count

/-- Covered call nouns are the generated subformula slots -/
theorem covered_callSlotNoun
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp row.1)
    (slot : TripleSlot) :
    callSlotNoun
      ((coveredRow hb hop hbind hfaith hleaves).calls.get
        ⟨i, by
          simpa [covered_calls_length hb hop hbind hfaith hleaves] using hi⟩)
      slot =
      s.subformula i (by simpa [hbind.1] using hi) slot := by
  have hiS : (i : ℕ) < fanoutComp s.state := by simpa [hbind.1] using hi
  rcases s with ⟨state, subject, formula, evaluation,
    decomposition, subformula, memoryRecord⟩
  rcases row with ⟨rowState, inp, pub, dec⟩
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  change rowState = state at hrowState
  subst rowState
  cases state with
  | s0 | s1 =>
      simp only [fanoutComp] at hiS
      omega
  | s2 =>
      revert slot
      fin_cases i <;> intro slot <;> cases slot <;> rfl
  | s3 | s4 =>
      revert slot
      revert hiS
      fin_cases i <;> intro hiS slot
      · cases slot <;> rfl
      · simp only [fanoutComp] at hiS; omega
      · simp only [fanoutComp] at hiS; omega
  | s5 | s6 | s7 | s8 | s9 | cons =>
      revert slot
      revert hiS
      fin_cases i <;> intro hiS slot
      · cases slot <;> rfl
      · cases slot <;> rfl
      · simp only [fanoutComp] at hiS; omega

/-- Generated call nouns sit in the committed subformula fingerprints. -/
theorem covered_callSlotNoun_enc
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp row.1)
    (slot : TripleSlot) :
    GlobalCarryRecognizer.enc row.2.1.z
      (callSlotNoun
        ((coveredRow hb hop hbind hfaith hleaves).calls.get
          ⟨i, by
            simpa [covered_calls_length hb hop hbind hfaith hleaves] using hi⟩)
        slot) =
      tripleFP (computeSubformulaFPs row.2.2.1 i) slot := by
  have hpacked := hbind
  rcases hbind with
    ⟨hrowState, hseed, hpubState, hsubject, hformula, hevaluation,
      hdec, hsf, hmr⟩
  have hiS : (i : ℕ) < fanoutComp s.state := by simpa [hrowState] using hi
  have hbindSF := hsf i
  simp only [dif_pos hiS] at hbindSF
  have hfp := hbindSF slot
  rw [covered_callSlotNoun hb hop hpacked hfaith hleaves i hi slot]
  simpa [SemanticStrategy.bindFP, hseed] using hfp.symm

/-- Reconstruction prefers the generated call when it is in `NockProgram^Λ`. -/
theorem subformulaNounOf_covered
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hz : z ≠ 0)
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp row.1)
    (slot : TripleSlot)
    (hwin : (s.subformula i (by simpa [hbind.1] using hi) slot).leaves ≤ Λ) :
    let data := coveredRow hb hop hbind hfaith hleaves
    let pubR := coveredPubR hz hb hop hbind hfaith hleaves
    subformulaNounOf data pubR i (by simpa [hbind.1] using hi) slot =
      s.subformula i (by simpa [hbind.1] using hi) slot := by
  let data := coveredRow hb hop hbind hfaith hleaves
  let pubR := coveredPubR hz hb hop hbind hfaith hleaves
  have hlen : (i : ℕ) < data.calls.length := by
    change (i : ℕ) < (coveredRow hb hop hbind hfaith hleaves).calls.length
    rw [covered_calls_length hb hop hbind hfaith hleaves]
    exact hi
  have hiS : (i : ℕ) < fanoutComp s.state := by simpa [hbind.1] using hi
  have hnoun := covered_callSlotNoun hb hop hbind hfaith hleaves i hi slot
  have henc := covered_callSlotNoun_enc hb hop hbind hfaith hleaves i hi slot
  have hbound : FieldEmbedding.BoundedBy q
      (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) := by
    rw [show callSlotNoun (data.calls.get ⟨i, hlen⟩) slot =
          s.subformula i hiS slot from hnoun]
    exact hb.2.2.2.2.1 i hiS slot
  have hleavesCall :
      (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot).leaves ≤ Λ := by
    rw [show callSlotNoun (data.calls.get ⟨i, hlen⟩) slot =
          s.subformula i hiS slot from hnoun]
    exact hwin
  have hw :
      FieldEmbedding.BoundedBy q (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) ∧
        (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot).leaves ≤ Λ ∧
          GlobalCarryRecognizer.enc row.2.1.z
            (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) =
            tripleFP (computeSubformulaFPs row.2.2.1 i) slot :=
    ⟨hbound, hleavesCall, henc⟩
  have hpref :=
    subformulaNounOf_leaves_of_call (q := q) (Λ := Λ) data pubR i
      (by simpa [hbind.1] using hi) slot hlen hw
  exact hpref.trans hnoun

theorem computeSkeletonOf_covered_subformula
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hz : z ≠ 0)
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state)
    (slot : TripleSlot)
    (hwin : (s.subformula i hi slot).leaves ≤ Λ) :
    let data := coveredRow hb hop hbind hfaith hleaves
    let pubR := coveredPubR hz hb hop hbind hfaith hleaves
    (computeSkeletonOf data pubR).subformula i
        (by simpa [computeSkeletonOf, hbind.1] using hi) slot =
      s.subformula i hi slot := by
  have hiRow : (i : ℕ) < fanoutComp row.1 := by simpa [hbind.1] using hi
  simpa [computeSkeletonOf] using
    subformulaNounOf_covered hz hb hop hbind hfaith hleaves i hiRow slot
      (by simpa [hbind.1] using hwin)

/-! ## C5 from a covered row -/

/-- `Vcomp` plus child `evalFBy` inhabit `LocalOpcodeCertificate` on the
covered row.  Not a field of `E` -/
theorem localCertificate_of_coveredRow
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {st : State} {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hs : s.state = st) (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s (st, (inp, pub, dec)))
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp inp pub dec)
    (hcalls :
      ∀ (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state),
        ∃ fuel, FieldEmbedding.evalFBy q fuel
          (s.subformula i hi .subject) (s.subformula i hi .formula) =
            some (s.subformula i hi .result)) :
    Nonempty (LocalOpcodeCertificate q Λ
      (coveredRow hb hop hbind hfaith hleaves)) :=
  canonicalLocalCertificate hs hb hop hbind hfaith hleaves
    hz hq hcast hv hcalls

/-- Packed-row form of `localCertificate_of_coveredRow` -/
theorem localCertificate_of_coveredRow'
    {q Λ : ℕ} {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K}
    (hb : s.BoundedBy q)
    (hop : SkeletonOperationalPremises q z s)
    (hbind : BindComputeRow z s row)
    (hfaith :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
        OpcodeSemantics.PairFaithful z q c.left c.right)
    (hleaves :
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hv : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hcalls :
      ∀ (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state),
        ∃ fuel, FieldEmbedding.evalFBy q fuel
          (s.subformula i hi .subject) (s.subformula i hi .formula) =
            some (s.subformula i hi .result)) :
    Nonempty (LocalOpcodeCertificate q Λ
      (coveredRow hb hop hbind hfaith hleaves)) := by
  revert hbind hv
  rcases row with ⟨st, inp, pub, dec⟩
  intro hbind hv
  exact localCertificate_of_coveredRow hbind.1.symm hb hop hbind hfaith hleaves
    hz hq hcast hv hcalls

/-- Whole-execution C5 from `ofSkeleton` rows.  Child `evalFBy` remains a
named generator obligation -/
theorem localCertificates_of_ofSkeleton
    {q Λ : ℕ} {z : K} [Fintype K] [DecidableEq K]
    {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (S : SemanticSkeleton)
    (binds : BindsAt z S cfg exec)
    (C : SkeletonP8Census K S Λ)
    (hb : S.BoundedBy q)
    (hcmp : SkeletonComparisonBoundedBy K q S)
    (hgood : z ∉ C.census.badSeeds (K := K))
    (hop :
      ∀ s ∈ computeSkeletonRows S,
        SkeletonOperationalPremises q z s)
    (data : ExactExecutionSemanticData q Λ cfg exec)
    (hrows :
      ∀ i : Fin cfg.compRows,
        data.rows i =
          ComputeRowSemanticData.ofSkeleton S exec binds C hb hcmp hgood hop i)
    (hz : z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hcalls :
      ∀ (i : Fin cfg.compRows)
        (j : Fin 3)
        (hj : (j : ℕ) < fanoutComp (skeletonRowAt S exec binds i).state),
        ∃ fuel, FieldEmbedding.evalFBy q fuel
          ((skeletonRowAt S exec binds i).subformula j hj .subject)
          ((skeletonRowAt S exec binds i).subformula j hj .formula) =
            some ((skeletonRowAt S exec binds i).subformula j hj .result)) :
    Nonempty (ExactExecutionLocalCertificates data) := by
  refine ⟨⟨fun i => ?_⟩⟩
  rw [hrows i]
  let s := skeletonRowAt S exec binds i
  have hsMem : s ∈ computeSkeletonRows S := List.get_mem _ _
  exact Classical.choice
    (localCertificate_of_coveredRow'
      ((List.forall_iff_forall_mem.mp hb.computeRows) s hsMem)
      (hop s hsMem)
      (skeletonRowAt_binds S exec binds i)
      (fun c hc => skeletonComparison_faithful S exec binds C hcmp hgood i c hc)
      (fun c hc => skeletonComparison_leaves S exec binds C i c hc)
      hz hq hcast (data.rowAccepted i).2.2 (fun j hj => hcalls i j hj))

/-! ## PRL stays a Type extra -/

/-- Generated `E` still supplies `PairedRecordLayout` as a named extra;
this is the consumer `dataOfCertificates` already uses. -/
def dataOfCertificates_of_generated
    (E : BuildableNockExecution F K)
    (certs : ExactExecutionLocalCertificates E.semanticData)
    (hq : E.q = ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (C : CensusRecordPremises E
      (residualPremises_of_localCertificates E certs hq)
      (memoryRecordPremises_of_paired_record_layout E hhon hprl))
    (hln : GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    Data E :=
  dataOfCertificates E certs hq hhon hprl C hln

theorem dataOfCertificates_of_generated_eq
    (E : BuildableNockExecution F K)
    (certs : ExactExecutionLocalCertificates E.semanticData)
    (hq : E.q = ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (C : CensusRecordPremises E
      (residualPremises_of_localCertificates E certs hq)
      (memoryRecordPremises_of_paired_record_layout E hhon hprl))
    (hln : GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    dataOfCertificates_of_generated E certs hq hhon hprl C hln =
      dataOfCertificates E certs hq hhon hprl C hln :=
  rfl

end

end Nock.NockVMROM.Thm54.GeneratedRowHandshake

#print axioms Nock.NockVMROM.Thm54.GeneratedRowHandshake.covered_root_subject
#print axioms Nock.NockVMROM.Thm54.GeneratedRowHandshake.computeSkeletonOf_covered_root
#print axioms Nock.NockVMROM.Thm54.GeneratedRowHandshake.covered_callSlotNoun
#print axioms Nock.NockVMROM.Thm54.GeneratedRowHandshake.subformulaNounOf_covered
#print axioms Nock.NockVMROM.Thm54.GeneratedRowHandshake.computeSkeletonOf_covered_subformula
#print axioms Nock.NockVMROM.Thm54.GeneratedRowHandshake.localCertificate_of_coveredRow
#print axioms Nock.NockVMROM.Thm54.GeneratedRowHandshake.localCertificate_of_coveredRow'
#print axioms Nock.NockVMROM.Thm54.GeneratedRowHandshake.localCertificates_of_ofSkeleton
#print axioms Nock.NockVMROM.Thm54.GeneratedRowHandshake.dataOfCertificates_of_generated
