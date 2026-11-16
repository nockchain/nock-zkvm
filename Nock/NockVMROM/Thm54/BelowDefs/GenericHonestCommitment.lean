/-
  Nock/NockVMROM/Thm54/BelowDefs/GenericHonestCommitment.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/GenericHonestCommitment.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.BelowDefs.HonestCommitment

namespace Nock.NockVMROM.Thm54

namespace GenericHonestCommitment

open scoped Classical
open Nock Nock.Walk Nock.NockVMROM
open SemanticStrategy SemanticTimestampStrategy
open SemanticTrace OpcodeSemantics
open HonestCommitment
open TemplateRawJointSoundness

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

def InactiveDecPaddingExec {cfg : ExactConfig F K} (_exec : ExactExecution cfg) : Prop :=
  True

theorem requiredTailRealizations_of_active (st : ComputeTable.State)
    (h : decActive st .f_th = true) :
    requiredTailRealizations st = 1 := by
  cases st <;> simp [decActive, hasTailDecomposition, requiredTailRealizations] at h ⊢

theorem requiredBranchTailRealizations_of_s6 (st : ComputeTable.State)
    (h : decActive st .f_tth = true) :
    requiredBranchTailRealizations st = 1 := by
  cases st <;> simp [decActive, requiredBranchTailRealizations] at h ⊢

theorem tails_ne_nil_of_th {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (h : decActive row.1 .f_th = true) :
    data.tails ≠ [] :=
  List.ne_nil_of_length_pos (by
    have := data.tails_count
    have h1 := requiredTailRealizations_of_active row.1 h
    omega)

theorem branchTails_ne_nil_of_tth {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (h : decActive row.1 .f_tth = true) :
    data.branchTails ≠ [] :=
  List.ne_nil_of_length_pos (by
    have := data.branchTails_count
    have h1 := requiredBranchTailRealizations_of_s6 row.1 h
    omega)

/-- The committed decomposition noun of one slot, read from `E.semanticData`.
Inactive slots are dummy atoms; `BindComputeRow` uses the field-zero branch for
those slots, never this dummy. -/
def decompNoun {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) : DecSlot → Noun
  | .f_h => data.root.head
  | .f_t => data.root.tail
  | .f_th =>
      if h : data.tails = [] then .atom 0
      else (data.tails.head h).head
  | .f_tt =>
      if h : data.tails = [] then .atom 0
      else (data.tails.head h).tail
  | .f_tth =>
      if h : data.branchTails = [] then .atom 0
      else (data.branchTails.head h).head
  | .f_ttt =>
      if h : data.branchTails = [] then .atom 0
      else (data.branchTails.head h).tail

theorem f_tt_active_iff_f_th (st : ComputeTable.State) :
    decActive st .f_tt = true ↔ decActive st .f_th = true := by
  cases st <;> simp [decActive, hasTailDecomposition]

theorem f_ttt_active_iff_f_tth (st : ComputeTable.State) :
    decActive st .f_ttt = true ↔ decActive st .f_tth = true := by
  cases st <;> simp [decActive]

theorem decompNoun_realizes_active {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) (slot : DecSlot)
    (hact : decActive row.1 slot = true) :
    OpcodeSemantics.Realizes row.2.1.z (SemanticStrategy.decFP row.2.2.2 slot)
      (decompNoun data slot) := by
  cases slot with
  | f_h =>
      simpa [decompNoun, SemanticStrategy.decFP] using data.root.head_realizes
  | f_t =>
      simpa [decompNoun, SemanticStrategy.decFP] using data.root.tail_realizes
  | f_th =>
      have hne := tails_ne_nil_of_th data hact
      rw [decompNoun, dif_neg hne]
      exact (data.tails.head hne).head_realizes
  | f_tt =>
      have hth : decActive row.1 .f_th = true := (f_tt_active_iff_f_th row.1).mp hact
      have hne := tails_ne_nil_of_th data hth
      rw [decompNoun, dif_neg hne]
      exact (data.tails.head hne).tail_realizes
  | f_tth =>
      have hne := branchTails_ne_nil_of_tth data hact
      rw [decompNoun, dif_neg hne]
      exact (data.branchTails.head hne).head_realizes
  | f_ttt =>
      have hth : decActive row.1 .f_tth = true := (f_ttt_active_iff_f_tth row.1).mp hact
      have hne := branchTails_ne_nil_of_tth data hth
      rw [decompNoun, dif_neg hne]
      exact (data.branchTails.head hne).tail_realizes

def chooseNoun {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) : Noun :=
  Classical.choose h

theorem chooseNoun_enc {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) :
    GlobalCarryRecognizer.enc z (chooseNoun h) = fp :=
  (Classical.choose_spec h).2

theorem chooseNoun_bounded {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) :
    FieldEmbedding.BoundedBy q (chooseNoun h) :=
  (Classical.choose_spec h).1

/-- Paper `NockProgram^Λ` window at the *reconstruction
selector*, not as a field of `NounRealization.FPRealized`. A windowed preimage may exist even when another
`BoundedBy q` preimage sits outside the window (`enc` collisions). -/
def FPRealizedWithin (z : K) (q Λ : ℕ) (fp : ComputeTable.FP K) : Prop :=
  ∃ n : Noun, FieldEmbedding.BoundedBy q n ∧ n.leaves ≤ Λ ∧
    GlobalCarryRecognizer.enc z n = fp

/-- Reconstruction selector: if a windowed realizer exists, pick one;
otherwise fall back to `chooseNoun`. Does not change `FPRealized`. -/
def chooseNounPreferWindow {z : K} {q Λ : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) : Noun :=
  if hw : FPRealizedWithin z q Λ fp then Classical.choose hw else chooseNoun h

theorem chooseNounPreferWindow_enc {z : K} {q Λ : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) :
    GlobalCarryRecognizer.enc z (chooseNounPreferWindow (Λ := Λ) h) = fp := by
  unfold chooseNounPreferWindow
  split_ifs with hw
  · exact (Classical.choose_spec hw).2.2
  · exact chooseNoun_enc h

theorem chooseNounPreferWindow_bounded {z : K} {q Λ : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) :
    FieldEmbedding.BoundedBy q (chooseNounPreferWindow (Λ := Λ) h) := by
  unfold chooseNounPreferWindow
  split_ifs with hw
  · exact (Classical.choose_spec hw).1
  · exact chooseNoun_bounded h

theorem fpSlot_active_realized {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPSlotRealized z q .active fp) : FPRealized z q fp :=
  h.1

/-- Subformula reconstruction prefers a `NockProgram^Λ` witness when one
exists (`chooseNounPreferWindow`). Encoding and `BoundedBy q` are unchanged. -/
def subformulaNoun {q : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (Λ : ℕ)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) : Noun :=
  let _sf := computeSubformulaFPs row.2.2.1 i
  have hkind : computeSubformulaKind row.1 i = .active := by
    simp [computeSubformulaKind, hi]
  have hslot := pubR.subformula i
  match slot with
  | .subject => chooseNounPreferWindow (Λ := Λ) (fpSlot_active_realized (hkind ▸ hslot.1))
  | .formula => chooseNounPreferWindow (Λ := Λ) (fpSlot_active_realized (hkind ▸ hslot.2.1))
  | .result => chooseNounPreferWindow (Λ := Λ) (fpSlot_active_realized (hkind ▸ hslot.2.2))

theorem subformulaNoun_enc {q : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (Λ : ℕ)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) :
    GlobalCarryRecognizer.enc row.2.1.z (subformulaNoun Λ pubR i hi slot) =
      tripleFP (computeSubformulaFPs row.2.2.1 i) slot := by
  have hkind : computeSubformulaKind row.1 i = .active := by
    simp [computeSubformulaKind, hi]
  have hslot := pubR.subformula i
  cases slot with
  | subject =>
      simp [subformulaNoun, tripleFP]
      exact chooseNounPreferWindow_enc (Λ := Λ) (fpSlot_active_realized (hkind ▸ hslot.1))
  | formula =>
      simp [subformulaNoun, tripleFP]
      exact chooseNounPreferWindow_enc (Λ := Λ) (fpSlot_active_realized (hkind ▸ hslot.2.1))
  | result =>
      simp [subformulaNoun, tripleFP]
      exact chooseNounPreferWindow_enc (Λ := Λ) (fpSlot_active_realized (hkind ▸ hslot.2.2))

theorem subformulaNoun_bounded {q : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (Λ : ℕ)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) :
    FieldEmbedding.BoundedBy q (subformulaNoun Λ pubR i hi slot) := by
  have hkind : computeSubformulaKind row.1 i = .active := by
    simp [computeSubformulaKind, hi]
  have hslot := pubR.subformula i
  cases slot with
  | subject =>
      simpa [subformulaNoun] using
        chooseNounPreferWindow_bounded (Λ := Λ) (fpSlot_active_realized (hkind ▸ hslot.1))
  | formula =>
      simpa [subformulaNoun] using
        chooseNounPreferWindow_bounded (Λ := Λ) (fpSlot_active_realized (hkind ▸ hslot.2.1))
  | result =>
      simpa [subformulaNoun] using
        chooseNounPreferWindow_bounded (Λ := Λ) (fpSlot_active_realized (hkind ▸ hslot.2.2))

/-- Slot projection of a row's committed call realization. -/
def callSlotNoun {z : K} (c : SemanticTrace.RealizedCall z) : TripleSlot → Noun
  | .subject => c.realization.subject
  | .formula => c.realization.formula
  | .result => c.realization.result

/-- Prefer the row's own `CallRealization` when that noun is a windowed
realizer of the committed fingerprint. Otherwise fall back to
`subformulaNoun`. Pins reconstruction at executions that already realized
the subformula (OP9 arm-fetch, OP6 window noun) without adding a field. -/
def subformulaNounOf {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) : Noun :=
  if hlen : (i : ℕ) < data.calls.length then
    if hw : FieldEmbedding.BoundedBy q
        (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) ∧
          (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot).leaves ≤ Λ ∧
            GlobalCarryRecognizer.enc row.2.1.z
              (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) =
              tripleFP (computeSubformulaFPs row.2.2.1 i) slot then
      callSlotNoun (data.calls.get ⟨i, hlen⟩) slot
    else
      subformulaNoun Λ pubR i hi slot
  else
    subformulaNoun Λ pubR i hi slot

theorem subformulaNounOf_enc {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) :
    GlobalCarryRecognizer.enc row.2.1.z (subformulaNounOf data pubR i hi slot) =
      tripleFP (computeSubformulaFPs row.2.2.1 i) slot := by
  unfold subformulaNounOf
  split_ifs with hlen hw
  · exact hw.2.2
  · exact subformulaNoun_enc Λ pubR i hi slot
  · exact subformulaNoun_enc Λ pubR i hi slot

theorem subformulaNounOf_bounded {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) :
    FieldEmbedding.BoundedBy q (subformulaNounOf data pubR i hi slot) := by
  unfold subformulaNounOf
  split_ifs with hlen hw
  · exact hw.1
  · exact subformulaNoun_bounded Λ pubR i hi slot
  · exact subformulaNoun_bounded Λ pubR i hi slot

def atomVal : Noun → ℕ
  | .atom k => k
  | .cell _ _ => 0

/-- Paper OP0: `mem_axis_2 = formula_tail`.  OP9's axis operand is
the atom-shape fact on `f_th`. -/
def AxisAtomPremises {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) : Prop :=
  (row.1 = .s0 → ∃ k, data.root.tail = .atom k) ∧
    (row.1 = .s9 → ∃ k, decompNoun data .f_th = .atom k)

theorem axisGates_ne_nil_of_s9 {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (h : row.1 = .s9) :
    data.axisGates ≠ [] :=
  List.ne_nil_of_length_pos (by
    have := data.axisGates_count
    simp [requiredAxisAtomGates, h] at this
    omega)

theorem eq_of_mem_of_length_one {α : Type*} {l : List α} {a b : α}
    (hlen : l.length = 1) (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  obtain ⟨x, rfl⟩ := exists_eq_singleton_of_length_one hlen
  simp only [List.mem_singleton] at ha hb
  exact ha.trans hb.symm

/-- C5 inhabits the named OP0/OP9 atom-shape extra.  OP0 uses the production
`PairFaithful` on `root.tail`.  OP9 identifies `decompNoun.f_th` with the
unique axis-gate tail via `axisGate_tail_mem` and the unique `.axisAtom`
census pair, then replays the production encoding -/
theorem axisAtomPremises_of_localCertificate {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    {data : ComputeRowSemanticData q Λ row}
    (cert : LocalOpcodeCertificate q Λ data) :
    AxisAtomPremises data := by
  cases cert with
  | s0 data fuel axis hstate hz hcast hhead hformula htail hmr hserved hv =>
      refine ⟨fun _ => ⟨axis, ?s0eq⟩, (fun h => by cases h)⟩
      have hv' := hv
      obtain ⟨_, _, _, hmem, _⟩ := hv'
      simp only [ComputeTable.memBlk, hstate] at hmem
      obtain ⟨hmr2, _, _, hsize, hdyck⟩ := hmem
      have haxisField : data.rowDec.f_t.leaf = (axis : K) := by
        calc
          data.rowDec.f_t.leaf = data.rowPub.mr2.axis :=
            (congrArg ComputeTable.MemRec.axis hmr2).symm
          _ = (axis : K) := hmr.axis_realizes
      have htailEnc :
          OpcodeSemantics.enc data.inpZ data.root.tail =
            OpcodeSemantics.enc data.inpZ (.atom axis) := by
        calc
          OpcodeSemantics.enc data.inpZ data.root.tail = data.rowDec.f_t :=
            data.root.tail_realizes.symm
          _ = ComputeTable.FP.atomFP data.inpZ (axis : K) :=
            ComputeTable.FP.ext hsize hdyck haxisField
          _ = OpcodeSemantics.enc data.inpZ (.atom axis) :=
            (GlobalCarryRecognizer.enc_atom data.inpZ axis).symm
      exact htail.faithful.eq_of_enc_eq hcast htailEnc
  | s1 data fuel hstate hz hcast hhead hformula hresult hv =>
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | s2 data fuel tail call1 call2 call3 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f h3s h3f hresult hcall1 hcall2 hcall3 hv =>
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | s3 data fuel call1 hstate hz hcast hhead hformula h1s h1f hresult hsize hcall hv =>
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | s4 data fuel call1 hstate hz hq hcast hhead hformula h1s h1f hresult
      hsize hcall hv =>
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | s5 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f hcompare hresult hcall1 hcall2 hv =>
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | s6 data fuel tail branch call1 call2 hstate hz hq hcast hhead hformula
      htail hbranchTail h1s h1fZero h1fOne h2s h2f hresult
      hconditionBound hconditionSize hcall1 hcall2 hv =>
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | s7 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hcall1 hcall2 hv =>
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | s8 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hcall1 hcall2 hv =>
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | s9 data fuel axis tail call1 call2 hstate hz hcast hhead hformula htail
      haxis h1s h1f h2s hresult hmr hserved hcall1 hcall2 hv =>
      constructor
      · intro h; cases h
      · intro _
        refine ⟨axis, ?s9eq⟩
        have hv' := hv
        obtain ⟨_, _, _, hmem, heval⟩ := hv'
        simp only [ComputeTable.memBlk, hstate] at hmem
        obtain ⟨_, _, hmr3, _⟩ := hmem
        simp only [ComputeTable.evalV, hstate] at heval
        obtain ⟨_, _, _, _, _, haxisSize, haxisDyck⟩ := heval
        have haxisField : data.rowDec.f_th.leaf = (axis : K) := by
          calc
            data.rowDec.f_th.leaf = data.rowPub.mr3.axis :=
              (congrArg ComputeTable.MemRec.axis hmr3).symm
            _ = (axis : K) := hmr.axis_realizes
        have haxisEnc :
            OpcodeSemantics.enc data.inpZ tail.head =
              OpcodeSemantics.enc data.inpZ (.atom axis) := by
          calc
            OpcodeSemantics.enc data.inpZ tail.head = data.rowDec.f_th :=
              tail.head_realizes.symm
            _ = ComputeTable.FP.atomFP data.inpZ (axis : K) :=
              ComputeTable.FP.ext haxisSize haxisDyck haxisField
            _ = OpcodeSemantics.enc data.inpZ (.atom axis) :=
              (GlobalCarryRecognizer.enc_atom data.inpZ axis).symm
        have htailAtom : tail.head = .atom axis :=
          haxis.faithful.eq_of_enc_eq hcast haxisEnc
        have hne :=
          tails_ne_nil_of_th data (by simp [decActive, hasTailDecomposition])
        have hgate_ne := axisGates_ne_nil_of_s9 data rfl
        have hlenT : data.tails.length = 1 := by
          simpa [requiredTailRealizations] using data.tails_count
        have hgate_mem : data.axisGates.head hgate_ne ∈ data.axisGates :=
          List.head_mem hgate_ne
        have hlisted := data.axisGate_listed (data.axisGates.head hgate_ne) hgate_mem
        have hcount : (requiredComparisonRoles data.rowState).count .axisAtom = 1 := by
          simp [requiredComparisonRoles_count_axisAtom, ComputeRowSemanticData.rowState]
        have huniq := comparison_of_role_unique data .axisAtom hcount haxis hlisted
        have htail_mem :=
          data.axisGate_tail_mem (data.axisGates.head hgate_ne) hgate_mem
        have hheads :
            data.tails.head hne = (data.axisGates.head hgate_ne).1 :=
          eq_of_mem_of_length_one hlenT (List.head_mem hne) htail_mem
        have hdecomp : decompNoun data .f_th = tail.head := by
          rw [decompNoun, dif_neg hne, hheads, huniq.1]
        exact hdecomp ▸ htailAtom
  | cons data fuel call1 call2 hstate hz hcast hformula h1s h1f h2s h2f
      hresult hcall1 hcall2 hv =>
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩

/-- C5 on every compute row inhabits the named `axisAtoms` family. -/
theorem axisAtoms_of_localCertificates {q Λ : ℕ}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {D : ExactExecutionSemanticData q Λ cfg exec}
    (certs : ExactExecutionLocalCertificates D) :
    ∀ i : Fin cfg.compRows, AxisAtomPremises (D.rows i) :=
  fun i => axisAtomPremises_of_localCertificate (certs.rows i)

/-- C5 at OP0: the formula tail is the served NMR axis atom -/
theorem s0_root_tail_eq_atom {q Λ : ℕ}
    {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K}
    {dec : ComputeTable.Dec K}
    {data : ComputeRowSemanticData q Λ (.s0, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data) :
    ∃ axis : ℕ, data.root.tail = .atom axis ∧
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun data.root.subject 1)
        axis data.root.result := by
  cases cert with
  | s0 data fuel axis hstate hz hcast hhead hformula htail hmr hserved hv =>
      refine ⟨axis, ?eq, hserved⟩
      have hv' := hv
      obtain ⟨_, _, _, hmem, _⟩ := hv'
      simp only [ComputeTable.memBlk, hstate] at hmem
      obtain ⟨hmr2, _, _, hsize, hdyck⟩ := hmem
      have haxisField : data.rowDec.f_t.leaf = (axis : K) := by
        calc
          data.rowDec.f_t.leaf = data.rowPub.mr2.axis :=
            (congrArg ComputeTable.MemRec.axis hmr2).symm
          _ = (axis : K) := hmr.axis_realizes
      have htailEnc :
          OpcodeSemantics.enc data.inpZ data.root.tail =
            OpcodeSemantics.enc data.inpZ (.atom axis) := by
        calc
          OpcodeSemantics.enc data.inpZ data.root.tail = data.rowDec.f_t :=
            data.root.tail_realizes.symm
          _ = ComputeTable.FP.atomFP data.inpZ (axis : K) :=
            ComputeTable.FP.ext hsize hdyck haxisField
          _ = OpcodeSemantics.enc data.inpZ (.atom axis) :=
            (GlobalCarryRecognizer.enc_atom data.inpZ axis).symm
      exact htail.faithful.eq_of_enc_eq hcast htailEnc

def memRecSkelOf {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (_hi : (i : ℕ) < Nock.Framework.recordCount row.1) : MemRecSkeleton :=
  if (i : ℕ) = 0 then
    { root := data.root.formula, child := data.root.tail, axis := 3 }
  else if (i : ℕ) = 1 then
    if h : row.1 = .s0 then
      { root := data.root.subject, child := data.root.result
        axis := atomVal data.root.tail }
    else if h : row.1 = .s2 ∨ row.1 = .s5 ∨ row.1 = .s6 ∨
        row.1 = .s7 ∨ row.1 = .s8 ∨ row.1 = .s9 then
      { root := data.root.tail, child := decompNoun data .f_th, axis := 2 }
    else
      { root := data.root.formula, child := data.root.tail, axis := 3 }
  else if h : row.1 = .s6 then
    { root := decompNoun data .f_tt, child := decompNoun data .f_tth, axis := 2 }
  else if h : row.1 = .s9 then
    { root := subformulaNounOf data pubR ⟨0, by omega⟩
        (by simp [ComputeTable.fanoutComp, h]) .result
      child := subformulaNounOf data pubR ⟨1, by omega⟩
        (by simp [ComputeTable.fanoutComp, h]) .formula
      axis := atomVal (decompNoun data .f_th) }
  else
    { root := data.root.formula, child := data.root.tail, axis := 3 }

theorem memRecSkelOf_mr1 {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hi : (0 : ℕ) < Nock.Framework.recordCount row.1) :
    memRecSkelOf data pubR ⟨0, by omega⟩ hi =
      { root := data.root.formula, child := data.root.tail, axis := 3 } := by
  simp [memRecSkelOf]

theorem memRecSkelOf_mr2_s0 {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hstate : row.1 = .s0)
    (hi : (1 : ℕ) < Nock.Framework.recordCount row.1) :
    memRecSkelOf data pubR ⟨1, by omega⟩ hi =
      { root := data.root.subject, child := data.root.result
        axis := atomVal data.root.tail } := by
  simp [memRecSkelOf, hstate]

theorem memRecSkelOf_mr2_tailDecomp {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hstate : row.1 = .s2 ∨ row.1 = .s5 ∨ row.1 = .s6 ∨
      row.1 = .s7 ∨ row.1 = .s8 ∨ row.1 = .s9)
    (hi : (1 : ℕ) < Nock.Framework.recordCount row.1) :
    memRecSkelOf data pubR ⟨1, by omega⟩ hi =
      { root := data.root.tail, child := decompNoun data .f_th, axis := 2 } := by
  have hne : row.1 ≠ .s0 := by
    intro hs0; rcases hstate with h | h | h | h | h | h <;> simp [hs0] at h
  simp [memRecSkelOf, hne, hstate]

theorem memRecSkelOf_mr3_s6 {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hstate : row.1 = .s6)
    (hi : (2 : ℕ) < Nock.Framework.recordCount row.1) :
    memRecSkelOf data pubR ⟨2, by omega⟩ hi =
      { root := decompNoun data .f_tt, child := decompNoun data .f_tth, axis := 2 } := by
  simp [memRecSkelOf, hstate]

theorem memRecSkelOf_mr3_s9 {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hstate : row.1 = .s9)
    (hi : (2 : ℕ) < Nock.Framework.recordCount row.1) :
    memRecSkelOf data pubR ⟨2, by omega⟩ hi =
      { root := subformulaNounOf data pubR ⟨0, by omega⟩
          (by simp [ComputeTable.fanoutComp, hstate]) .result
        child := subformulaNounOf data pubR ⟨1, by omega⟩
          (by simp [ComputeTable.fanoutComp, hstate]) .formula
        axis := atomVal (decompNoun data .f_th) } := by
  simp [memRecSkelOf, hstate]

def computeSkeletonOf {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    ComputeRowSkeleton where
  state := row.1
  subject := data.root.subject
  formula := data.root.formula
  evaluation := data.root.result
  decomposition := fun slot _ => decompNoun data slot
  subformula := fun i hi slot => subformulaNounOf data pubR i hi slot
  memoryRecord := fun i hi => memRecSkelOf data pubR i hi

def computeStampOf (lnPrevExp : ℕ)
    (row : ComputeTable.State × ComputeTable.DTcomp K) : ComputeTimestampRow where
  state := row.1
  lnPrevExponent := lnPrevExp
  lnExponent := lnPrevExp + Nock.Framework.recordCount row.1
  recordExponent := fun i => lnPrevExp + (i : ℕ) + 1

/-- First compute row starts at exponent zero: `ln_prev = 1`. -/
def FirstLineStartsAtOne {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  (exec.computePubAt ⟨0, cfg.compRows_pos⟩).ln_prev = 1

def computeNodeOf {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (lnPrevExp : ℕ) : ComputeNode K where
  skel := computeSkeletonOf data pubR
  stamp := computeStampOf lnPrevExp row
  row := row

/-- The remaining named premises on the way to `HonestCommitment.Data E`.
`computeOK` is `V_comp` plus
the compute-line hand-off, not first-row
`ln_prev = 1`. -/
structure ResidualPremises (E : BuildableNockExecution F K) where
  /-- Lean encoding: inactive private `Dec` zeros (`BindComputeRow` vs `Vcomp`). -/
  inactiveDec : InactiveDecPaddingExec E.exec
  /-- Paper: OP0/OP9 formula-tail / `f_th` are atoms.
  The range form `1737-1738` was already the
  repo's convention at five other sites. -/
  axisAtoms :
    ∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)
  /-- Lean package asks `q = ringChar K`; `E` carries `q ≤ ringChar K`. -/
  q_eq_ringChar : E.q = ringChar K

theorem computeRowAccepted_vcomp {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (h : ExactExecution.ComputeRowAccepted cfg row) :
    ComputeTable.Vcomp row.2.1 row.2.2.1 row.2.2.2 :=
  h.2.2

/-- `Vcomp`'s always-operative first record, in full: the `(input_formula, formula_tail)` opening at
axis `3` with timestamp `ln_prev · α`.

*Cite repair.*  `1850` is the
**introductory sentence** of the appendix's three-record block, so it supports only
*always-operative*; the `mem_record₁` item itself is **`1852`** and its timestamp constraint
`ln(i-1) · α = timestamp₁` is **`1854`**.  `V_comp`'s own first check is the algorithm line
**`1728`**, stated with **`z`**, so the `α` form is the appendix's.  Content unchanged. -/
theorem vcomp_mr1 {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row) :
    row.2.2.1.mr1 =
      ⟨row.2.2.1.f, row.2.2.2.f_t, 3, row.2.2.1.ln_prev * row.2.1.α⟩ :=
  (computeRowAccepted_vcomp hacc).2.1

theorem subFP_zero_of_sfz1 (pub : ComputeTable.Pub K) (h : ComputeTable.sfz1 pub) :
    computeSubformulaFPs pub 0 = (0, 0, 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [computeSubformulaFPs, ComputeTable.sfTriple, h1, h2, h3]

theorem subFP_zero_of_sfz2 (pub : ComputeTable.Pub K) (h : ComputeTable.sfz2 pub) :
    computeSubformulaFPs pub 1 = (0, 0, 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [computeSubformulaFPs, ComputeTable.sfTriple, h1, h2, h3]

theorem subFP_zero_of_sfz3 (pub : ComputeTable.Pub K) (h : ComputeTable.sfz3 pub) :
    computeSubformulaFPs pub 2 = (0, 0, 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [computeSubformulaFPs, ComputeTable.sfTriple, h1, h2, h3]

theorem evalV_inactive_subformula_zero
    {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K} {dec : ComputeTable.Dec K}
    (h : ComputeTable.evalV inp pub dec)
    (i : Fin 3) (hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp pub.state)) :
    computeSubformulaFPs pub i = (0, 0, 0) := by
  cases hst : pub.state
  · have he : ComputeTable.sfz1 pub ∧ ComputeTable.sfz2 pub ∧ ComputeTable.sfz3 pub := by
      simpa [ComputeTable.evalV, hst] using h
    fin_cases i
    · exact subFP_zero_of_sfz1 pub he.1
    · exact subFP_zero_of_sfz2 pub he.2.1
    · exact subFP_zero_of_sfz3 pub he.2.2
  · have he :
        pub.e = dec.f_t ∧ ComputeTable.sfz1 pub ∧ ComputeTable.sfz2 pub ∧
          ComputeTable.sfz3 pub := by
      simpa [ComputeTable.evalV, hst] using h
    fin_cases i
    · exact subFP_zero_of_sfz1 pub he.2.1
    · exact subFP_zero_of_sfz2 pub he.2.2.1
    · exact subFP_zero_of_sfz3 pub he.2.2.2
  · simp [ComputeTable.fanoutComp, hst] at hi
  · have heval := h
    simp [ComputeTable.evalV, hst] at heval
    obtain ⟨_, _, h2, h3, _⟩ := heval
    fin_cases i
    · simp [ComputeTable.fanoutComp, hst] at hi
    · exact subFP_zero_of_sfz2 pub h2
    · exact subFP_zero_of_sfz3 pub h3
  · have heval := h
    simp [ComputeTable.evalV, hst] at heval
    obtain ⟨_, _, _, _, h2, h3, _⟩ := heval
    fin_cases i
    · simp [ComputeTable.fanoutComp, hst] at hi
    · exact subFP_zero_of_sfz2 pub h2
    · exact subFP_zero_of_sfz3 pub h3
  · have heval := h
    simp [ComputeTable.evalV, hst] at heval
    obtain ⟨_, _, _, _, h3, _⟩ := heval
    fin_cases i
    · simp [ComputeTable.fanoutComp, hst] at hi
    · simp [ComputeTable.fanoutComp, hst] at hi
    · exact subFP_zero_of_sfz3 pub h3
  · have heval := h
    simp [ComputeTable.evalV, hst] at heval
    obtain ⟨_, _, _, _, _, _, _, _, h3⟩ := heval
    fin_cases i
    · simp [ComputeTable.fanoutComp, hst] at hi
    · simp [ComputeTable.fanoutComp, hst] at hi
    · exact subFP_zero_of_sfz3 pub h3
  · have heval := h
    simp [ComputeTable.evalV, hst] at heval
    obtain ⟨_, _, _, _, _, h3⟩ := heval
    fin_cases i
    · simp [ComputeTable.fanoutComp, hst] at hi
    · simp [ComputeTable.fanoutComp, hst] at hi
    · exact subFP_zero_of_sfz3 pub h3
  · have heval := h
    simp [ComputeTable.evalV, hst] at heval
    obtain ⟨_, _, _, _, _, h3⟩ := heval
    fin_cases i
    · simp [ComputeTable.fanoutComp, hst] at hi
    · simp [ComputeTable.fanoutComp, hst] at hi
    · exact subFP_zero_of_sfz3 pub h3
  · have heval := h
    simp [ComputeTable.evalV, hst] at heval
    obtain ⟨_, _, _, _, h3, _⟩ := heval
    fin_cases i
    · simp [ComputeTable.fanoutComp, hst] at hi
    · simp [ComputeTable.fanoutComp, hst] at hi
    · exact subFP_zero_of_sfz3 pub h3
  · have heval := h
    simp [ComputeTable.evalV, hst] at heval
    obtain ⟨_, _, _, _, _, h3⟩ := heval
    fin_cases i
    · simp [ComputeTable.fanoutComp, hst] at hi
    · simp [ComputeTable.fanoutComp, hst] at hi
    · exact subFP_zero_of_sfz3 pub h3

theorem bindComputeRow_publicAndDec {q Λ : ℕ} {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hacc : ExactExecution.ComputeRowAccepted cfg row) :
    row.1 = (computeSkeletonOf data pubR).state ∧
      row.2.1.z = row.2.1.z ∧
      row.2.2.1.state = (computeSkeletonOf data pubR).state ∧
      bindFP row.2.1.z (computeSkeletonOf data pubR).subject row.2.2.1.s ∧
      bindFP row.2.1.z (computeSkeletonOf data pubR).formula row.2.2.1.f ∧
      bindFP row.2.1.z (computeSkeletonOf data pubR).evaluation row.2.2.1.e ∧
      (∀ slot : DecSlot,
        if h : decActive (computeSkeletonOf data pubR).state slot = true
        then bindFP row.2.1.z
          ((computeSkeletonOf data pubR).decomposition slot h)
          (SemanticStrategy.decFP row.2.2.2 slot)
        else True) ∧
      (∀ i : Fin 3,
        if h : (i : ℕ) < ComputeTable.fanoutComp (computeSkeletonOf data pubR).state
        then ∀ slot : TripleSlot,
          bindFP row.2.1.z ((computeSkeletonOf data pubR).subformula i h slot)
            (tripleFP (computeSubformulaFPs row.2.2.1 i) slot)
        else computeSubformulaFPs row.2.2.1 i = (0, 0, 0)) := by
  refine ⟨rfl, rfl, hacc.1.symm, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [computeSkeletonOf, bindFP, OpcodeSemantics.Realizes] using
      data.root.subject_realizes
  · simpa [computeSkeletonOf, bindFP, OpcodeSemantics.Realizes] using
      data.root.formula_realizes
  · simpa [computeSkeletonOf, bindFP, OpcodeSemantics.Realizes] using
      data.root.result_realizes
  · intro slot
    by_cases hact : decActive (computeSkeletonOf data pubR).state slot = true
    · rw [dif_pos hact]
      simpa [computeSkeletonOf, bindFP, OpcodeSemantics.Realizes] using
        decompNoun_realizes_active data slot (by simpa [computeSkeletonOf] using hact)
    · rw [dif_neg hact]; trivial
  · intro i
    by_cases hi : (i : ℕ) < ComputeTable.fanoutComp (computeSkeletonOf data pubR).state
    · rw [dif_pos hi]
      intro slot
      simpa [computeSkeletonOf, bindFP] using (subformulaNounOf_enc data pubR i
        (by simpa [computeSkeletonOf] using hi) slot).symm
    · rw [dif_neg hi]
      have heval := (computeRowAccepted_vcomp hacc).2.2.2.2
      have hpub : row.2.2.1.state = row.1 := hacc.1.symm
      exact evalV_inactive_subformula_zero heval i
        (by simpa [computeSkeletonOf, hpub] using hi)

theorem bindMemRec_mr1 {q Λ : ℕ} {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hi : (0 : ℕ) < Nock.Framework.recordCount row.1) :
    BindMemRec row.2.1.z (memRecSkelOf data pubR ⟨0, by omega⟩ hi)
      (computeMemRec row.2.2.1 ⟨0, by omega⟩) := by
  have hmr1 := vcomp_mr1 hacc
  rw [memRecSkelOf_mr1]; simp only [computeMemRec]
  refine ⟨?_, ?_, ?_⟩
  · simpa [bindFP, hmr1, OpcodeSemantics.Realizes] using data.root.formula_realizes
  · simpa [bindFP, hmr1, OpcodeSemantics.Realizes] using data.root.tail_realizes
  · simp [hmr1]

theorem bindMemRec_inactive {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (i : Fin 3) (hi : ¬ ((i : ℕ) < Nock.Framework.recordCount row.1)) :
    computeMemRec row.2.2.1 i = ComputeTable.MemRec.zero := by
  have hmem := (computeRowAccepted_vcomp hacc).2.2.2.1
  have hst : row.2.2.1.state = row.1 := hacc.1.symm
  fin_cases i
  · have : 0 < Nock.Framework.recordCount row.1 :=
      Nat.succ_le_iff.mp (Nock.Framework.recordCount_pos row.1)
    exact (hi this).elim
  · have hle : Nock.Framework.recordCount row.2.2.1.state ≤ 1 := by
      simpa [hst] using Nat.le_of_not_gt (by simpa using hi)
    simpa [computeMemRec] using
      Nock.Framework.memBlk_mr2_zero (K := K) row.2.1 row.2.2.1 row.2.2.2 hmem hle
  · have hle : Nock.Framework.recordCount row.2.2.1.state ≤ 2 := by
      simpa [hst] using Nat.le_of_not_gt (by simpa using hi)
    simpa [computeMemRec] using
      Nock.Framework.memBlk_mr3_zero (K := K) row.2.1 row.2.2.1 row.2.2.2 hmem hle

theorem atomVal_atom (k : ℕ) : atomVal (.atom k) = k := rfl

theorem realizes_atom_leaf {z : K} {fp : ComputeTable.FP K} {k : ℕ}
    (h : OpcodeSemantics.Realizes z fp (.atom k)) :
    fp.leaf = (k : K) := by
  have henc : fp = GlobalCarryRecognizer.enc z (.atom k) := h
  rw [henc, GlobalCarryRecognizer.enc_atom]
  rfl

theorem vcomp_memBlk {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row) :
    ComputeTable.memBlk row.2.1 row.2.2.1 row.2.2.2 :=
  (computeRowAccepted_vcomp hacc).2.2.2.1

theorem accepted_pub_state {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row) :
    row.2.2.1.state = row.1 :=
  hacc.1.symm

theorem vcomp_mr2_s0 {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hstate : row.1 = .s0) :
    row.2.2.1.mr2 =
      ⟨row.2.2.1.s, row.2.2.1.e, row.2.2.2.f_t.leaf,
        row.2.2.1.ln_prev * row.2.1.α ^ 2⟩ := by
  have hmem := vcomp_memBlk hacc
  have hst : row.2.2.1.state = .s0 := (accepted_pub_state hacc).trans hstate
  simp only [ComputeTable.memBlk, hst] at hmem
  exact hmem.1

theorem vcomp_mr2_tailDecomp {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hstate : row.1 = .s2 ∨ row.1 = .s5 ∨ row.1 = .s6 ∨
      row.1 = .s7 ∨ row.1 = .s8 ∨ row.1 = .s9) :
    row.2.2.1.mr2 =
      ⟨row.2.2.2.f_t, row.2.2.2.f_th, 2,
        row.2.2.1.ln_prev * row.2.1.α ^ 2⟩ := by
  have hmem := vcomp_memBlk hacc
  have hst : row.2.2.1.state = row.1 := accepted_pub_state hacc
  rcases hstate with h | h | h | h | h | h
  · simp only [ComputeTable.memBlk, hst, h] at hmem; exact hmem.1
  · simp only [ComputeTable.memBlk, hst, h] at hmem; exact hmem.1
  · simp only [ComputeTable.memBlk, hst, h] at hmem; exact hmem.1
  · simp only [ComputeTable.memBlk, hst, h] at hmem; exact hmem.1
  · simp only [ComputeTable.memBlk, hst, h] at hmem; exact hmem.1
  · simp only [ComputeTable.memBlk, hst, h] at hmem; exact hmem.1

theorem vcomp_mr3_s6 {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hstate : row.1 = .s6) :
    row.2.2.1.mr3 =
      ⟨row.2.2.2.f_tt, row.2.2.2.f_tth, 2,
        row.2.2.1.ln_prev * row.2.1.α ^ 3⟩ := by
  have hmem := vcomp_memBlk hacc
  have hst : row.2.2.1.state = .s6 := (accepted_pub_state hacc).trans hstate
  simp only [ComputeTable.memBlk, hst] at hmem
  exact hmem.2.2.1

theorem vcomp_mr3_s9 {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hstate : row.1 = .s9) :
    row.2.2.1.mr3 =
      ⟨row.2.2.1.sf1_e, row.2.2.1.sf2_f, row.2.2.2.f_th.leaf,
        row.2.2.1.ln_prev * row.2.1.α ^ 3⟩ := by
  have hmem := vcomp_memBlk hacc
  have hst : row.2.2.1.state = .s9 := (accepted_pub_state hacc).trans hstate
  simp only [ComputeTable.memBlk, hst] at hmem
  exact hmem.2.2.1

theorem recordCount_mr2_live (st : ComputeTable.State)
    (h : (1 : ℕ) < Nock.Framework.recordCount st) :
    st = .s0 ∨ st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9 := by
  cases st <;> simp [Nock.Framework.recordCount] at h ⊢

theorem recordCount_mr3_live (st : ComputeTable.State)
    (h : (2 : ℕ) < Nock.Framework.recordCount st) :
    st = .s6 ∨ st = .s9 := by
  cases st <;> simp [Nock.Framework.recordCount] at h ⊢

theorem f_th_active_of_tailDecomp (st : ComputeTable.State)
    (h : st = .s2 ∨ st = .s5 ∨ st = .s6 ∨ st = .s7 ∨ st = .s8 ∨ st = .s9) :
    decActive st .f_th = true := by
  rcases h with h | h | h | h | h | h <;> simp [decActive, hasTailDecomposition, h]

theorem bindMemRec_mr2_s0 {q Λ : ℕ} {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hatoms : AxisAtomPremises data)
    (hstate : row.1 = .s0)
    (hi : (1 : ℕ) < Nock.Framework.recordCount row.1) :
    BindMemRec row.2.1.z (memRecSkelOf data pubR ⟨1, by omega⟩ hi)
      (computeMemRec row.2.2.1 ⟨1, by omega⟩) := by
  obtain ⟨k, hk⟩ := hatoms.1 hstate
  have hmr2 := vcomp_mr2_s0 hacc hstate
  have hleaf := realizes_atom_leaf (by
    simpa [hk, OpcodeSemantics.Realizes] using data.root.tail_realizes)
  rw [memRecSkelOf_mr2_s0 data pubR hstate hi]; simp only [computeMemRec]
  refine ⟨?_, ?_, ?_⟩
  · simpa [bindFP, hmr2, OpcodeSemantics.Realizes] using data.root.subject_realizes
  · simpa [bindFP, hmr2, OpcodeSemantics.Realizes] using data.root.result_realizes
  · simp [hmr2, hk, atomVal_atom, hleaf]

theorem bindMemRec_mr2_tailDecomp {q Λ : ℕ} {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hstate : row.1 = .s2 ∨ row.1 = .s5 ∨ row.1 = .s6 ∨
      row.1 = .s7 ∨ row.1 = .s8 ∨ row.1 = .s9)
    (hi : (1 : ℕ) < Nock.Framework.recordCount row.1) :
    BindMemRec row.2.1.z (memRecSkelOf data pubR ⟨1, by omega⟩ hi)
      (computeMemRec row.2.2.1 ⟨1, by omega⟩) := by
  have hmr2 := vcomp_mr2_tailDecomp hacc hstate
  have hth := f_th_active_of_tailDecomp row.1 hstate
  have hchild := decompNoun_realizes_active data .f_th hth
  rw [memRecSkelOf_mr2_tailDecomp data pubR hstate hi]; simp only [computeMemRec]
  refine ⟨?_, ?_, ?_⟩
  · simpa [bindFP, hmr2, OpcodeSemantics.Realizes] using data.root.tail_realizes
  · simpa [bindFP, hmr2, OpcodeSemantics.Realizes, decFP] using hchild
  · simp [hmr2]

theorem bindMemRec_mr2 {q Λ : ℕ} {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hatoms : AxisAtomPremises data)
    (hi : (1 : ℕ) < Nock.Framework.recordCount row.1) :
    BindMemRec row.2.1.z (memRecSkelOf data pubR ⟨1, by omega⟩ hi)
      (computeMemRec row.2.2.1 ⟨1, by omega⟩) := by
  rcases recordCount_mr2_live row.1 hi with h | h | h | h | h | h | h
  · exact bindMemRec_mr2_s0 data pubR hacc hatoms h hi
  · exact bindMemRec_mr2_tailDecomp data pubR hacc (Or.inl h) hi
  · exact bindMemRec_mr2_tailDecomp data pubR hacc (Or.inr (Or.inl h)) hi
  · exact bindMemRec_mr2_tailDecomp data pubR hacc
      (Or.inr (Or.inr (Or.inl h))) hi
  · exact bindMemRec_mr2_tailDecomp data pubR hacc
      (Or.inr (Or.inr (Or.inr (Or.inl h)))) hi
  · exact bindMemRec_mr2_tailDecomp data pubR hacc
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hi
  · exact bindMemRec_mr2_tailDecomp data pubR hacc
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) hi

theorem bindMemRec_mr3_s6 {q Λ : ℕ} {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hstate : row.1 = .s6)
    (hi : (2 : ℕ) < Nock.Framework.recordCount row.1) :
    BindMemRec row.2.1.z (memRecSkelOf data pubR ⟨2, by omega⟩ hi)
      (computeMemRec row.2.2.1 ⟨2, by omega⟩) := by
  have hmr3 := vcomp_mr3_s6 hacc hstate
  have htt : decActive row.1 .f_tt = true := by simp [decActive, hasTailDecomposition, hstate]
  have htth : decActive row.1 .f_tth = true := by simp [decActive, hstate]
  have hroot := decompNoun_realizes_active data .f_tt htt
  have hchild := decompNoun_realizes_active data .f_tth htth
  rw [memRecSkelOf_mr3_s6 data pubR hstate hi]; simp only [computeMemRec]
  refine ⟨?_, ?_, ?_⟩
  · simpa [bindFP, hmr3, OpcodeSemantics.Realizes, decFP] using hroot
  · simpa [bindFP, hmr3, OpcodeSemantics.Realizes, decFP] using hchild
  · simp [hmr3]

theorem bindMemRec_mr3_s9 {q Λ : ℕ} {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hatoms : AxisAtomPremises data)
    (hstate : row.1 = .s9)
    (hi : (2 : ℕ) < Nock.Framework.recordCount row.1) :
    BindMemRec row.2.1.z (memRecSkelOf data pubR ⟨2, by omega⟩ hi)
      (computeMemRec row.2.2.1 ⟨2, by omega⟩) := by
  obtain ⟨k, hk⟩ := hatoms.2 hstate
  have hmr3 := vcomp_mr3_s9 hacc hstate
  have hth : decActive row.1 .f_th = true := by
    simp [decActive, hasTailDecomposition, hstate]
  have hreal : OpcodeSemantics.Realizes row.2.1.z row.2.2.2.f_th (.atom k) := by
    simpa [hk, OpcodeSemantics.Realizes, decFP] using
      decompNoun_realizes_active data .f_th hth
  have hleaf := realizes_atom_leaf hreal
  have hf0 : (0 : ℕ) < ComputeTable.fanoutComp row.1 := by
    simp [ComputeTable.fanoutComp, hstate]
  have hf1 : (1 : ℕ) < ComputeTable.fanoutComp row.1 := by
    simp [ComputeTable.fanoutComp, hstate]
  have hroot := subformulaNounOf_enc data pubR ⟨0, by omega⟩ hf0 .result
  have hchild := subformulaNounOf_enc data pubR ⟨1, by omega⟩ hf1 .formula
  rw [memRecSkelOf_mr3_s9 data pubR hstate hi]; simp only [computeMemRec]
  refine ⟨?_, ?_, ?_⟩
  · simpa [bindFP, hmr3, computeSubformulaFPs, ComputeTable.sfTriple, tripleFP] using
      hroot.symm
  · simpa [bindFP, hmr3, computeSubformulaFPs, ComputeTable.sfTriple, tripleFP] using
      hchild.symm
  · simp [hmr3, hk, atomVal_atom, hleaf]

theorem bindMemRec_mr3 {q Λ : ℕ} {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hatoms : AxisAtomPremises data)
    (hi : (2 : ℕ) < Nock.Framework.recordCount row.1) :
    BindMemRec row.2.1.z (memRecSkelOf data pubR ⟨2, by omega⟩ hi)
      (computeMemRec row.2.2.1 ⟨2, by omega⟩) := by
  rcases recordCount_mr3_live row.1 hi with h | h
  · exact bindMemRec_mr3_s6 data pubR hacc h hi
  · exact bindMemRec_mr3_s9 data pubR hacc hatoms h hi

theorem bindComputeRow_of_axisAtoms {q Λ : ℕ} {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (hatoms : AxisAtomPremises data) :
    BindComputeRow row.2.1.z (computeSkeletonOf data pubR) row := by
  obtain ⟨hstate, _, hpub, hs, hf, he, hdec, hsf⟩ :=
    bindComputeRow_publicAndDec data pubR hacc
  refine ⟨hstate, rfl, hpub, hs, hf, he, hdec, hsf, ?_⟩
  intro i
  by_cases hi : (i : ℕ) < Nock.Framework.recordCount (computeSkeletonOf data pubR).state
  · rw [dif_pos hi]
    fin_cases i
    · simpa [computeSkeletonOf] using bindMemRec_mr1 data pubR hacc
        (by simpa [computeSkeletonOf] using hi)
    · simpa [computeSkeletonOf] using bindMemRec_mr2 data pubR hacc hatoms
        (by simpa [computeSkeletonOf] using hi)
    · simpa [computeSkeletonOf] using bindMemRec_mr3 data pubR hacc hatoms
        (by simpa [computeSkeletonOf] using hi)
  · rw [dif_neg hi]
    exact bindMemRec_inactive hacc i (by simpa [computeSkeletonOf] using hi)

/-- Public-row noun existence is already on `E.language`; it is not a new field. -/
theorem publicRowNoun_of_execution (E : BuildableNockExecution F K)
    (i : Fin E.cfg.compRows) :
    ComputePublicRowNounRealization E.q
      (computePublicLabel (E.exec.computeRowAt i)) := by
  have hAll :=
    ExactExecutionNounRealization.computeRows E.semanticData.language.nounRealization
  exact (List.forall_iff_forall_mem.mp hAll) _
    (List.mem_map.mpr ⟨_, ExactExecution.computeRowAt_mem E.exec i, rfl⟩)

/-- Named-premises `BindComputeRow` on every authoritative row.  `ResidualPremises`
is not rewritten: `axisAtoms` and `inactiveDec` are consumed here, while
`firstLine` and `q_eq_ringChar` remain for timestamp specialization and the
released package. -/
theorem bindComputeRow_of_residual (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (i : Fin E.cfg.compRows) :
    BindComputeRow (E.exec.computeRowAt i).2.1.z
      (computeSkeletonOf (E.semanticData.rows i) (publicRowNoun_of_execution E i))
      (E.exec.computeRowAt i) :=
  bindComputeRow_of_axisAtoms (E.semanticData.rows i)
    (publicRowNoun_of_execution E i) (E.semanticData.rowAccepted i)
    (P.axisAtoms i)

/-- Live `mr2`/`mr3` consume `axisAtoms` and do not discharge the record into `Data` /
`commitmentResidualOf`. -/
theorem residualPremises_still_three {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  ⟨P.inactiveDec, P.axisAtoms, P.q_eq_ringChar⟩

theorem residualPremises_still_four {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  residualPremises_still_three P

/-- C5 plus the modelling pin `q = ringChar K` inhabit `ResidualPremises`.
`inactiveDec` is `True` -/
def residualPremises_of_localCertificates
    (E : BuildableNockExecution F K)
    (certs : ExactExecutionLocalCertificates E.semanticData)
    (hq : E.q = ringChar K) : ResidualPremises E where
  inactiveDec := trivial
  axisAtoms := axisAtoms_of_localCertificates certs
  q_eq_ringChar := hq

/-- `E.language` already has the compute-line hand-off, the compute analog of
walk `ln(i)=α·ln(i-1)`.  It does not pin
first-row `ln_prev`. -/
theorem execution_has_compute_chain (E : BuildableNockExecution F K) :
    ∀ i : Fin E.cfg.compRows, ∀ hi : (i : ℕ) + 1 < E.cfg.compRows,
      (E.exec.computePubAt i).ln =
        (E.exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev :=
  (NounRealizedTraversableChainedSemanticExactLanguage.toChained
    E.language).compute_chain

end

end GenericHonestCommitment

end Nock.NockVMROM.Thm54
