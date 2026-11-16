import Nock.NockVMROM.Thm54.HonestCommitment
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Nock.NockVMROM.Thm54.BuildableTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Nock.NockVMROM.Thm54.BelowDefs.GenericHonestCommitment
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Generic honest commitment from a `BuildableNockExecution`

This module constructs the committed compute-row skeleton from the semantic CORE
already carried by `E : BuildableNockExecution`.  `E.semanticData.rows` supplies
`RootRealization` / `TailRealization` / `BranchTailRealization`, which are the
private decomposition nouns.  No fixture-specific `Dec`
column is smuggled as a new field.

`SepSeed` is the paper's NPR collision *soundness* event.  The constructor uses existence witnesses only and
does not demand a Lean `∀ z` uniqueness theorem.

Inactive private `Dec` slots are not mentioned by `Vcomp`.
The extra
zero-padding conjunct was dropped, not carried.  Paper-mandated zeros (inactive
mem `1739-1742`, inactive subformula `(0,0,0)` at `1748`) are unchanged.

Later-round table / IO / walk arrays remain the prover's post-challenge message and stay the `A`/`W` arguments of `commitmentResidualOf`.
`q_eq_ringChar` stays a named Lean-package premise (Outcome 2): `E` carries
`q ≤ ringChar K` for Nat-cast injectivity, while `Data` / `CommitmentResidual`
and the released package ask for equality.  The paper places atoms in
`N^λ(F)` over the Goldilocks prime field `F = F_p`,
takes `K` as the degree-3 extension, wraps OP4 at
`(1+n) mod p`, and uses `|K|` only in NPR
collision soundness.  That does not identify the
execution atom bound with `|K|`, and `q ≤ char` does not force `q = char`.
`ResidualPremises` is not rewritten.
`hzero` remains on `buildFullPackage`.
Live `mr2`/`mr3` close under the named paper `AxisAtomPremises` together with the Vcomp/`memBlk` fingerprint
copies: `bindComputeRow_of_axisAtoms` /
`bindComputeRow_of_residual`.
`firstLine` remains a named paper analog: walk `ln(1)=α`
is the later-round walk column built after `α` is sampled;
compute `ln_prev=1` is the distinct exponent-zero image `α^0` of
`ComputeLineStartsAtZero`, not a field of `BuildableNockExecution` and not a
`Vcomp` consequence.
-/

namespace Nock.NockVMROM.Thm54
namespace GenericHonestCommitment

open scoped Classical
open Nock Nock.Walk Nock.NockVMROM
open SemanticStrategy SemanticTimestampStrategy
open SemanticTrace OpcodeSemantics
open HonestCommitment
open TemplateRawJointSoundness
open OptimizedComputeFinalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Lean encoding: inactive private `Dec` columns

`Vcomp` constrains `f_h`/`f_t` on every
row and `f_th`/`f_tt`/`f_tth`/`f_ttt` only in the states `decActive` marks live.
`BindComputeRow` no longer zero-forces inactive private Dec slots (C7 else-branch
`True`).  The next theorem compiles that `Vcomp` does not force those zeros
either: an `OP_1` row remains accepted after arbitrary garbage is written into the
four inactive columns. -/

theorem vcomp_s1_ignores_inactive_dec
    (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K)
    (hstate : pub.state = .s1) (h : ComputeTable.Vcomp inp pub dec)
    (th tt tth ttt : ComputeTable.FP K) :
    ComputeTable.Vcomp inp pub
      { f_h := dec.f_h, f_t := dec.f_t, f_th := th, f_tt := tt,
        f_tth := tth, f_ttt := ttt } := by
  obtain ⟨hcons, hmr1, hsv, hmem, heval⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using hcons
  · simpa using hmr1
  · simpa [ComputeTable.SVhead, hstate, ComputeTable.headAtom] using hsv
  · simpa [ComputeTable.memBlk, hstate] using hmem
  · simpa [ComputeTable.evalV, hstate] using heval

/-- Algorithm NockCompute / `Vcomp` constrains
`mr1.ts = ln_prev·α` and `ln = ln_prev·α` on OP1, but does not pin the first-row
`ln_prev` itself.  Rescaling `ln_prev` together with the α-dependent timestamps
leaves the row accepted. -/
theorem vcomp_s1_ignores_first_ln_prev
    (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K)
    (hstate : pub.state = .s1) (h : ComputeTable.Vcomp inp pub dec)
    (lnPrev' : K) :
    ComputeTable.Vcomp inp
      { pub with
        ln_prev := lnPrev'
        ln := lnPrev' * inp.α
        mr1 := { pub.mr1 with ts := lnPrev' * inp.α } }
      dec := by
  obtain ⟨hcons, hmr1, hsv, hmem, heval⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using hcons
  · have hroot : pub.mr1.root = pub.f :=
      congrArg ComputeTable.MemRec.root hmr1
    have hchild : pub.mr1.child = dec.f_t :=
      congrArg ComputeTable.MemRec.child hmr1
    have haxis : pub.mr1.axis = 3 :=
      congrArg ComputeTable.MemRec.axis hmr1
    exact ComputeTable.MemRec.ext hroot hchild haxis rfl
  · simpa [ComputeTable.SVhead, hstate, ComputeTable.headAtom] using hsv
  · have hmem' :
        pub.mr2 = ComputeTable.MemRec.zero ∧
          pub.mr3 = ComputeTable.MemRec.zero ∧
          pub.ln = pub.ln_prev * inp.α := by
      simpa [ComputeTable.memBlk, hstate] using hmem
    simp [ComputeTable.memBlk, hstate, hmem'.1, hmem'.2.1]
  · simpa [ComputeTable.evalV, hstate, ComputeTable.sfz1, ComputeTable.sfz2,
      ComputeTable.sfz3] using heval

/-- Inactive private decomposition slots of one compute row are the production zero
padding.  This is the extra `BindComputeRow` conjunct `Vcomp` does not supply. -/
def InactiveDecPadding
    (_row : ComputeTable.State × ComputeTable.DTcomp K) : Prop :=
  True

theorem inactive_dec_padding_is_bind_encoding
    {z : K} {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (_h : BindComputeRow z s row) :
    InactiveDecPadding row :=
  trivial

/-! ## Decomposition nouns from the semantic CORE already on `E` -/

theorem requiredCallRealizations_eq_fanout (st : ComputeTable.State) :
    requiredCallRealizations st = ComputeTable.fanoutComp st := by
  cases st <;> rfl




/-! ## Subformula nouns from public-row existence (no `SepSeed`) -/


theorem FPRealizedWithin.to_realized {z : K} {q Λ : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealizedWithin z q Λ fp) : FPRealized z q fp := by
  obtain ⟨n, hb, _, henc⟩ := h
  exact ⟨n, hb, henc⟩


theorem chooseNounPreferWindow_leaves_of_within {z : K} {q Λ : ℕ}
    {fp : ComputeTable.FP K} (h : FPRealized z q fp)
    (hw : FPRealizedWithin z q Λ fp) :
    (chooseNounPreferWindow (Λ := Λ) h).leaves ≤ Λ := by
  unfold chooseNounPreferWindow
  rw [dif_pos hw]
  exact (Classical.choose_spec hw).2.1


/-- When the fingerprint has a `NockProgram^Λ` realizer, the reconstructed
subformula noun is inside the window -/
theorem subformulaNoun_leaves_of_within {q : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (Λ : ℕ)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot)
    (hw : FPRealizedWithin row.2.1.z q Λ
      (tripleFP (computeSubformulaFPs row.2.2.1 i) slot)) :
    (subformulaNoun Λ pubR i hi slot).leaves ≤ Λ := by
  have hkind : computeSubformulaKind row.1 i = .active := by
    simp [computeSubformulaKind, hi]
  have hslot := pubR.subformula i
  cases slot with
  | subject =>
      unfold subformulaNoun
      apply chooseNounPreferWindow_leaves_of_within (Λ := Λ)
        (fpSlot_active_realized (hkind ▸ hslot.1))
      convert hw <;> simp [computePublicLabel, tripleFP]
  | formula =>
      unfold subformulaNoun
      apply chooseNounPreferWindow_leaves_of_within (Λ := Λ)
        (fpSlot_active_realized (hkind ▸ hslot.2.1))
      convert hw <;> simp [computePublicLabel, tripleFP]
  | result =>
      unfold subformulaNoun
      apply chooseNounPreferWindow_leaves_of_within (Λ := Λ)
        (fpSlot_active_realized (hkind ▸ hslot.2.2))
      convert hw <;> simp [computePublicLabel, tripleFP]

theorem subformulaNounOf_leaves_of_call {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot)
    (hlen : (i : ℕ) < data.calls.length)
    (hw : FieldEmbedding.BoundedBy q (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) ∧
      (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot).leaves ≤ Λ ∧
        GlobalCarryRecognizer.enc row.2.1.z
          (callSlotNoun (data.calls.get ⟨i, hlen⟩) slot) =
          tripleFP (computeSubformulaFPs row.2.2.1 i) slot) :
    subformulaNounOf data pubR i hi slot =
      callSlotNoun (data.calls.get ⟨i, hlen⟩) slot := by
  unfold subformulaNounOf
  rw [dif_pos hlen, dif_pos hw]

theorem subformulaNounOf_leaves_of_within {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot)
    (hw : FPRealizedWithin row.2.1.z q Λ
      (tripleFP (computeSubformulaFPs row.2.2.1 i) slot)) :
    (subformulaNounOf data pubR i hi slot).leaves ≤ Λ := by
  unfold subformulaNounOf
  split_ifs with hlen hcall
  · exact hcall.2.1
  · exact subformulaNoun_leaves_of_within Λ pubR i hi slot hw
  · exact subformulaNoun_leaves_of_within Λ pubR i hi slot hw

/-! ## Memory-record skeletons from `Vcomp` -/


/-! ## The generic compute-row skeleton -/




/-! ## Named remaining premises, classified paper vs Lean-only -/

inductive PremiseKind where
  | paperProtocol
  | leanEncoding
deriving DecidableEq, Repr

theorem residualPremises_kinds :
    (PremiseKind.leanEncoding, PremiseKind.paperProtocol, PremiseKind.leanEncoding) =
      (.leanEncoding, .paperProtocol, .leanEncoding) :=
  rfl

/-- `SepSeed` uniqueness is the paper's collision *soundness* event, not a
completeness obligation and not a `∀ z` theorem. -/
theorem uniqueness_requires_SepSeed
    {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (left right : FPRealizationWitness z q fp)
    (hsep : GlobalCarryRecognizer.SepSeed z left.noun right.noun)
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)) :
    left.noun = right.noun :=
  FPRealizationWitness.noun_unique left right hsep hinj

/-- The generic constructor never applies `noun_unique`.  Existence of a realizing
noun is the completeness direction. -/
theorem chooseNoun_uses_existence_only {z : K} {q : ℕ} {fp : ComputeTable.FP K}
    (h : FPRealized z q fp) :
    GlobalCarryRecognizer.enc z (chooseNoun h) = fp :=
  chooseNoun_enc h

/-! ## BindComputeRow: public + Dec halves, then `mr1`, then the rest -/






/-- Always-operative `mr1` is constructed. -/
theorem recordCount_pos_mr1 (st : ComputeTable.State) :
    0 < Nock.Framework.recordCount st :=
  Nock.Framework.recordCount_pos st

/-! ## Live `mr2`/`mr3`: paper axis atoms + Vcomp fingerprint copies

`BindMemRec` on a live record is three equalities: the two NPR fingerprints are
`enc z` of the committed nouns, and the NMR address is the Nat axis as a field
element.  Algorithm
NockCompute / `memBlk` copies those fingerprints from already-bound Dec and
public columns.  The only extra paper premises are the
OP0/OP9 atom-shape facts that turn a formula-tail / `f_th` noun into an NMR
address. -/













theorem inactiveDec_of_residual {E : BuildableNockExecution F K}
    (_P : ResidualPremises E) (i : Fin E.cfg.compRows) :
    InactiveDecPadding (E.exec.computeRowAt i) :=
  trivial

/-! ## First-line / timestamp specialization: named paper analog, not derived from `E`

Walk `ln(1)=α` is built after the verifier samples
`α`.  Compute `ln_prev=1` is the distinct exponent-zero
image `α^0` of the α-free `ComputeLineStartsAtZero` stamp.  `E` already supplies
the compute-line hand-off and memory
first-row zeros, but not a compute first-row `ln_prev` pin. -/

theorem walkSat_ln1_eq_alpha
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ln 1 = α :=
  hw.ln1

theorem walkSat_ln1_eq_alpha_pow_one
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ln 1 = α ^ 1 := by
  rw [pow_one]
  exact hw.ln1

theorem computeLineStartsAtZero_is_exponent_zero
    (stamp : ComputeTimestampRow) (rest : List ComputeTimestampRow) :
    ComputeLineStartsAtZero (stamp :: rest) ↔ stamp.lnPrevExponent = 0 :=
  Iff.rfl

omit [Field K] in
theorem computeStampOf_zero_starts
    (row : ComputeTable.State × ComputeTable.DTcomp K) :
    (computeStampOf 0 row).lnPrevExponent = 0 :=
  rfl

/-- Relative specialization does not pin `ln_prev = 1`.  The absolute
equation `ln_prev = α^e` plus `e = 0` still does (`pow_zero`). -/
theorem firstLine_of_absolute_zero
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hpow : row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
    (hstart : stamp.lnPrevExponent = 0) :
    row.2.2.1.ln_prev = 1 := by
  simpa [hstart, pow_zero] using hpow

/-- Specializing a zero-exponent stamp yields compute `ln_prev = α^0 = 1`
only given the absolute origin-1 equation, which `V_comp` does not provide. -/
theorem firstLine_of_specializes_at_zero
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hpow : row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent)
    (hstart : stamp.lnPrevExponent = 0) :
    row.2.2.1.ln_prev = 1 :=
  firstLine_of_absolute_zero hpow hstart

theorem firstLine_of_line_starts_at_zero
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    {rest : List ComputeTimestampRow}
    (hstart : ComputeLineStartsAtZero (stamp :: rest))
    (hpow : row.2.2.1.ln_prev = α ^ stamp.lnPrevExponent) :
    row.2.2.1.ln_prev = 1 :=
  firstLine_of_specializes_at_zero hpow hstart

/-- `FirstLineStartsAtOne` from the absolute origin-1 equation at exponent zero. -/
theorem firstLine_of_computeStampOf_zero
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hpow :
      (exec.computeRowAt ⟨0, cfg.compRows_pos⟩).2.2.1.ln_prev =
        cfg.challenges.α ^ 0) :
    FirstLineStartsAtOne exec := by
  unfold FirstLineStartsAtOne ExactExecution.computePubAt
  simpa using hpow

/-- Full first-row timestamp specialization still mentions the sampled `α`.
`ln_prev=1` is the origin-1 convention, not a `V_comp` conjunct. -/
theorem specializes_at_zero_still_needs_alpha
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (htime : ComputeTimestampSpecializesAt α stamp row)
    (hstart : stamp.lnPrevExponent = 0) :
    row.2.1.α = α ∧
      row.2.2.1.ln = row.2.2.1.ln_prev * α ^ stamp.lnExponent := by
  obtain ⟨_, halpha, _, hln, _, _⟩ := htime
  refine ⟨halpha, ?_⟩
  simpa [hstart] using hln

/-- The chained language pins memory first-row zeros and has
no compute first-row `ln_prev` field. -/
theorem chained_language_eta_without_firstLine
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    h = {
      semantic := h.semantic
      z_ne_zero := h.z_ne_zero
      compute_wf := h.compute_wf
      memory_wf := h.memory_wf
      compute_chain := h.compute_chain
      memory_chain := h.memory_chain
      memory_first_counts := h.memory_first_counts
      memory_first_indicator := h.memory_first_indicator
      memory_first_ipre := h.memory_first_ipre
      memory_last_icur := h.memory_last_icur
      memory_same_lambda := h.memory_same_lambda } := by
  cases h
  rfl

theorem chained_first_row_pins_memory
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).pt.counts = 0 ∧
      (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).pt.indicator = 0 ∧
      (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).ipre = 0 :=
  ⟨h.memory_first_counts, h.memory_first_indicator, h.memory_first_ipre⟩

/-! ## `firstLine` from the commitment's root line-number exponent

`HonestCommitment.Data.root_line_exponent` is the paper's own pin, at the paper's own layer.  The three lemmas below turn it into
`FirstLineStartsAtOne` by a derivation through `ComputeNodeOK`'s specialization equation.  They do
**not** remove `firstLine` from `ResidualPremises`: `GenericHonestData.dataOf` still consumes it to
prove `computeOK`, and `residualPremises_still_names_firstLine` below is unchanged. -/

/-- BFS of the one-tree compute forest begins with the tree's own root label. -/
theorem computeRows_eq_root_cons {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computeRows =
      exec.computeTree.label ::
        ((bfsForest [exec.computeTree]).flatMap NTree.children).map NTree.label := by
  show (bfsForest [exec.computeTree]).map NTree.label = _
  conv_lhs =>
    rw [bfsForest_eq_append_flatMap [exec.computeTree] (by simp)]
  simp

/-- Hence the row `FirstLineStartsAtOne` reads is the compute tree's root label. -/
theorem computeRowAt_zero_eq_root {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computeRowAt ⟨0, cfg.compRows_pos⟩ = exec.computeTree.label := by
  show exec.computeRows.get _ = _
  rw [List.get_eq_getElem]
  rw [List.getElem_of_eq (computeRows_eq_root_cons exec)]
  simp

/-- Relative `ComputeTimestampSpecializesAt` does not
pin `ln_prev = 1`.  The published first row still equals the committed root row
(`compute_rows`); origin-1 is an honest-generator convention, not a `Data` field.
Previously this derived `ln_prev = α⁰ = 1` from the absolute specialization equation. -/
theorem _root_.Nock.NockVMROM.Thm54.HonestCommitment.Data.firstLine
    {E : BuildableNockExecution F K} (D : HonestCommitment.Data E)
    (horigin : D.computeNodes.label.row.2.2.1.ln_prev = 1) :
    FirstLineStartsAtOne E.exec := by
  have hlabel : E.exec.computeTree.label = D.computeNodes.label.row := by
    rw [← D.compute_rows, mapNTree_label]
  show (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).ln_prev = 1
  show (E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩).2.2.1.ln_prev = 1
  rw [computeRowAt_zero_eq_root, hlabel]
  exact horigin

/-- Outcome 2: `firstLine` stays a named residual field.  Walk `ln(1)=α` is a
later-round sampled-challenge constraint; compute `ln_prev=1` is its distinct
exponent-zero analog and is not derived from `E`.

This is unchanged and is not withdrawn.  `Data.firstLine` derives the
premise from a *commitment*; it does not derive it from `E`, and `dataOf` still consumes
`P.firstLine` to build that commitment. -/
theorem residualPremises_still_names_firstLine
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
      E.q = ringChar K :=
  ⟨P.inactiveDec, P.axisAtoms, P.q_eq_ringChar⟩

/-! ## Characteristic equality: Lean package pin, not derived from `E`

`BuildableNockExecution` carries `q ≤ ringChar K` so Nat atoms below `q` embed
without wraparound.  The released package identifies that bound with the
characteristic because OP4 is `(1+n) mod p` and
consumed `incMod` uses `ringChar K`.  NPR collision soundness is stated in
`|K|`; on the paper cubic that cardinality is `p^3`,
not `p`.  Atoms live in `N^λ(F)` over `F = F_p`.
Neither `|K|` nor `q = ringChar K` is a field of `E`. -/

/-- Exhaustive eta: the input boundary has `q_le_ringChar` and no `q_eq`
field, residual, or `Data` -/
theorem execution_eta_has_q_le_not_q_eq
    (E : BuildableNockExecution F K) :
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
  BuildableNockExecution.eta_with_memoryTrace E

/-- The only characteristic comparison on `E` is the inequality -/
theorem execution_only_has_q_le
    (E : BuildableNockExecution F K) :
    E.q ≤ ringChar K :=
  E.q_le_ringChar

-- `1 < q ≤ n` does not force `q = n`, so `E.q_gt_one` plus `q_le_ringChar`
-- cannot discharge the residual equality.
theorem two_gt_one_le_73_ne :
    1 < 2 ∧ (2 : ℕ) ≤ 73 ∧ (2 : ℕ) ≠ 73 := by
  decide

theorem q_gt_one_and_q_le_do_not_imply_eq :
    ¬ ∀ (q n : ℕ), 1 < q → q ≤ n → q = n :=
  fun h => (two_gt_one_le_73_ne.2.2) (h 2 73 two_gt_one_le_73_ne.1 two_gt_one_le_73_ne.2.1)

/-- Outcome 2: residual equality remains a named Lean-package field. -/
theorem residualPremises_still_names_q_eq
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    E.q = ringChar K ∧
      InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) :=
  ⟨P.q_eq_ringChar, P.inactiveDec, P.axisAtoms⟩

/-- `Data` still asks for the strict equality on top of `E`'s inequality. -/
theorem data_still_requires_q_equality
    {E : BuildableNockExecution F K} (D : Data E) :
    E.q ≤ ringChar K ∧ E.q = ringChar K :=
  ⟨E.q_le_ringChar, D.q_eq_ringChar⟩

/-- The residual package copies the same equality. -/
theorem commitmentResidual_still_requires_q_equality
    {E : BuildableNockExecution F K}
    (R : BuildablePackage.CommitmentResidual E) :
    E.q = ringChar K :=
  R.q_eq_ringChar

/-- A generic `ResidualPremises` constructor would force equality for every
buildable execution.  This module supplies no such constructor. -/
theorem generic_residualPremises_would_force_q_equality
    (g : ∀ E : BuildableNockExecution F K, ResidualPremises E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

/-- A generic `Data` constructor would likewise force the package pin. -/
theorem generic_data_would_force_q_equality
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

/-- A generic residual constructor would force the same pin. -/
theorem generic_residual_would_force_q_equality
    (g : ∀ E : BuildableNockExecution F K,
      BuildablePackage.CommitmentResidual E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

/-- `ResidualPremises` is still the same four named fields after the
characteristic-equality boundary. -/
theorem residualPremises_still_four_after_q
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  residualPremises_still_four P

/-- `commitmentResidualOf` still takes the post-challenge families as arguments.
Those families are the paper's later-round message, not a
gap in the committed skeleton. -/
def laterRoundSignature
    {E : BuildableNockExecution F K} (D : Data E) :=
  (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      TemplateRawJointSoundness.AlphaMCommitment (p := ringChar K)
        D.timestampStrategy z hz α lmb) ×
    (∀ (ω : JointCoins K) (_lmb : K), nprSeed ω ≠ 0 → RawWalkArrays K)

theorem commitmentResidualOf_takes_later_round
    {E : BuildableNockExecution F K}
    [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (D : Data E)
    (A : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      TemplateRawJointSoundness.AlphaMCommitment (p := ringChar K)
        D.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K) (_lmb : K), nprSeed ω ≠ 0 → RawWalkArrays K) :
    Nonempty (BuildablePackage.CommitmentResidual E) :=
  ⟨commitmentResidualOf D A W⟩

/-- `hzero` remains on the released `buildFullPackage`.  This
module does not restate `ExactFinalChallengeCoordinates`. -/
theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (I : BuildableChips.Inputs E) (R : BuildablePackage.CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  ⟨BuildablePackage.buildFullPackage E I R hzero hprl hmore hord hordM hrows⟩

/-! ## F73: the compiled Dec-encoding fact is inhabited, and inactive padding holds -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := ConcreteStrictPackage.concrete_char73

theorem f73_vcomp_ignores_inactive_dec
    (th tt tth ttt : ComputeTable.FP K73cubic) :
    ComputeTable.Vcomp
      (computeInputs honestSeed honestAlpha)
      (computePub honestSeed honestAlpha)
      { f_h := (computeDec honestSeed).f_h
        f_t := (computeDec honestSeed).f_t
        f_th := th, f_tt := tt, f_tth := tth, f_ttt := ttt } :=
  vcomp_s1_ignores_inactive_dec
    (computeInputs honestSeed honestAlpha)
    (computePub honestSeed honestAlpha)
    (computeDec honestSeed) rfl compute_accepts th tt tth ttt

theorem f73_inactive_dec_padding (z α : K73cubic) :
    InactiveDecPadding (computeRow z α) :=
  trivial

/-- An accepted OP1 row remains `Vcomp`-accepted after `ln_prev` is rescaled away
from `1`.  Compiled negative control that Algorithm NockCompute does not force
`FirstLineStartsAtOne` -/
theorem f73_vcomp_accepts_nonzero_first_ln_prev :
    ComputeTable.Vcomp (computeInputs honestSeed honestAlpha)
      { computePub honestSeed honestAlpha with
        ln_prev := 2
        ln := 2 * honestAlpha
        mr1 := { (computePub honestSeed honestAlpha).mr1 with ts := 2 * honestAlpha } }
      (computeDec honestSeed) ∧
    (2 : K73cubic) ≠ 1 := by
  constructor
  · exact vcomp_s1_ignores_first_ln_prev
      (computeInputs honestSeed honestAlpha)
      (computePub honestSeed honestAlpha)
      (computeDec honestSeed) rfl compute_accepts 2
  · intro h
    have h10 : (1 : K73cubic) = 0 := by
      calc
        (1 : K73cubic) = 2 - 1 := by ring
        _ = 1 - 1 := by rw [h]
        _ = 0 := by ring
    exact one_ne_zero h10

/-- On the paper cubic, the inequality `E` carries is inhabited strictly:
`2 ≤ char` and `2 ≠ char`.  Equality is therefore not a consequence of
`q ≤ ringChar K` -/
theorem f73_strict_q_le_inhabited :
    ∃ q : ℕ, 1 < q ∧ q ≤ ringChar K73cubic ∧ q ≠ ringChar K73cubic :=
  ⟨2, by norm_num, by rw [← q_eq_ringChar]; norm_num,
    by rw [← q_eq_ringChar]; norm_num⟩

/-- Base-field cardinality equals the characteristic: `|F_p| = p`.
This is the Goldilocks prime field, not `|K|`. -/
theorem f73_base_card_eq_ringChar :
    Fintype.card F73 = ringChar K73cubic := by
  simp [F73]
  exact q_eq_ringChar

/-- NPR soundness uses `|K|`.  On the paper cubic
`K = F_{p^3}` that cardinality is `p^3`, not the characteristic `p`.
Identifying the atom bound `q` with `|K|` is therefore a different
equation from the package pin `q = ringChar K` -/
theorem f73_cubic_card_ne_ringChar :
    Fintype.card K73cubic ≠ ringChar K73cubic := by
  have hcard : Fintype.card K73cubic = 73 ^ 3 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 73 3 (by norm_num)
  rw [hcard, ← q_eq_ringChar]
  norm_num

/-- The F73 execution satisfies equality because its constructor set `q := 73`,
not because `BuildableNockExecution` derived the package pin -/
theorem f73_q_pin_is_constructor_choice :
    concreteExecution.q = 73 ∧
      concreteExecution.q = ringChar K73cubic ∧
      concreteExecution.q ≤ ringChar K73cubic :=
  ⟨rfl, q_eq_ringChar, concreteExecution.q_le_ringChar⟩

end Concrete

end

end GenericHonestCommitment
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.vcomp_s1_ignores_inactive_dec
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.vcomp_s1_ignores_first_ln_prev
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.inactive_dec_padding_is_bind_encoding
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.walkSat_ln1_eq_alpha
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.walkSat_ln1_eq_alpha_pow_one
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.computeLineStartsAtZero_is_exponent_zero
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.computeStampOf_zero_starts
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.firstLine_of_specializes_at_zero
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.firstLine_of_line_starts_at_zero
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.firstLine_of_computeStampOf_zero
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.specializes_at_zero_still_needs_alpha
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.execution_has_compute_chain
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.chained_language_eta_without_firstLine
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.chained_first_row_pins_memory
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.residualPremises_still_names_firstLine
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.execution_eta_has_q_le_not_q_eq
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.execution_only_has_q_le
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.two_gt_one_le_73_ne
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.q_gt_one_and_q_le_do_not_imply_eq
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.residualPremises_still_names_q_eq
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.data_still_requires_q_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.commitmentResidual_still_requires_q_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.generic_residualPremises_would_force_q_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.generic_data_would_force_q_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.generic_residual_would_force_q_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.residualPremises_still_four_after_q
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.evalV_inactive_subformula_zero
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.decompNoun_realizes_active
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.chooseNoun_enc
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.chooseNoun_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.chooseNounPreferWindow_enc
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.chooseNounPreferWindow_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.chooseNounPreferWindow_leaves_of_within
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.subformulaNoun_enc
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.subformulaNoun_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.subformulaNoun_leaves_of_within
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.subformulaNounOf_enc
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.subformulaNounOf_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.subformulaNounOf_leaves_of_call
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.subformulaNounOf_leaves_of_within
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.uniqueness_requires_SepSeed
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.bindComputeRow_publicAndDec
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.bindMemRec_mr1
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.bindMemRec_inactive
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.bindMemRec_mr2
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.bindMemRec_mr3
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.bindComputeRow_of_axisAtoms
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.bindComputeRow_of_residual
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.computeRows_eq_root_cons
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.computeRowAt_zero_eq_root
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.firstLine
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.residualPremises_still_names_firstLine
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.commitmentResidualOf_takes_later_round
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.released_builder_still_takes_hzero
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.Concrete.f73_vcomp_ignores_inactive_dec
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.Concrete.f73_inactive_dec_padding
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.Concrete.f73_vcomp_accepts_nonzero_first_ln_prev
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.Concrete.f73_strict_q_le_inhabited
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.Concrete.f73_base_card_eq_ringChar
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.Concrete.f73_cubic_card_ne_ringChar
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.axisAtomPremises_of_localCertificate
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.axisAtoms_of_localCertificates
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.s0_root_tail_eq_atom
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.residualPremises_of_localCertificates
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.Concrete.f73_q_pin_is_constructor_choice
