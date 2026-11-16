import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.HonestCommitmentNodes
import Nock.NockVMROM.Thm54.BelowDefs.HonestCommitment
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The honest committed layer: rendering a committed skeleton at every sampled seed

Milestone 5 supplied that layer as data.  This module *constructs* it.

The paper fixes the order of the protocol: the prover commits (`Com(·)`, the paper, and the
walk table's `Com(...)` at the paper) and only then does the verifier answer with the sampled
challenges — `α, γ` at the paper, and the NPR seed `z` at the paper (`α` at `1813`),
which is the `r ∈ 𝕂` "uniformly randomly sampled" of `Def:ion_univariate`.
An honest prover therefore commits to *seed-free* data — Nock nouns, Nat axes, tree topology,
and Nat timestamp exponents — and can answer **any** sampled `(z, α)`.  That is exactly the
`∀ z ≠ 0, ∀ α` shape of the six committed checks: they are the completeness statement of a
commit-first prover strategy, not a per-transcript check.

`renderComputeRow z s row` is that answer at one row: it recomputes every fingerprint-bearing
column as `enc z ·` of the committed noun, keeps every column the seed does not touch, zeroes
paper-mandated inactive subformula / memory slots, and preserves inactive private Dec columns.  `bindComputeRow_render` is
unconditional, so the rendered table binds at *every* seed; `renderComputeRow_eq_self` says that
at the honest seed the rendering returns the supplied row unchanged, which is what makes
`honest_specialization` a theorem rather than an assumption.
-/

namespace Nock.NockVMROM.Thm54
namespace HonestCommitment

open Nock Nock.Walk Nock.NockVMROM
open SemanticStrategy SemanticTimestampStrategy
open TemplateRawJointSoundness RawSemanticAssembly

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Compute-row rendering -/

/-- The committed fingerprint of one subformula slot at seed `z`; state-inactive slots are the
production zero padding. -/
def renderSubFP (z : K) (s : ComputeRowSkeleton) (i : Fin 3) (slot : TripleSlot) :
    ComputeTable.FP K :=
  if h : (i : ℕ) < ComputeTable.fanoutComp s.state then
    GlobalCarryRecognizer.enc z (s.subformula i h slot)
  else 0

/-- The committed fingerprint of one formula-decomposition slot at seed `z`.  For inactive slots the original row value is preserved;
`BindComputeRow` does not constrain these columns. -/
def renderDecFP (z : K) (s : ComputeRowSkeleton) (origDec : ComputeTable.Dec K)
    (slot : DecSlot) : ComputeTable.FP K :=
  if h : decActive s.state slot = true then
    GlobalCarryRecognizer.enc z (s.decomposition slot h)
  else SemanticStrategy.decFP origDec slot

/-- The committed memory record of one compute slot at seed `z`.  Only the two nouns and the Nat
axis are committed; the timestamp
column is the `α`-power the later specialization overwrites, so it is carried over unchanged. -/
def renderMemRec (z : K) (s : ComputeRowSkeleton) (i : Fin 3)
    (orig : ComputeTable.MemRec K) : ComputeTable.MemRec K :=
  if h : (i : ℕ) < Nock.Framework.recordCount s.state then
    { root := GlobalCarryRecognizer.enc z (s.memoryRecord i h).root
      child := GlobalCarryRecognizer.enc z (s.memoryRecord i h).child
      axis := (((s.memoryRecord i h).axis : ℕ) : K)
      ts := orig.ts }
  else ComputeTable.MemRec.zero

/-- The sampled seed is the only challenge column the rendering touches. -/
def renderInputs (z : K) (inp : ComputeTable.Inputs K) : ComputeTable.Inputs K :=
  { inp with z := z }

/-- The rendered public columns of one compute row. -/
def renderPub (z : K) (s : ComputeRowSkeleton) (pub : ComputeTable.Pub K) :
    ComputeTable.Pub K :=
  { pub with
    state := s.state
    s := GlobalCarryRecognizer.enc z s.subject
    f := GlobalCarryRecognizer.enc z s.formula
    e := GlobalCarryRecognizer.enc z s.evaluation
    sf1_s := renderSubFP z s 0 .subject
    sf1_f := renderSubFP z s 0 .formula
    sf1_e := renderSubFP z s 0 .result
    sf2_s := renderSubFP z s 1 .subject
    sf2_f := renderSubFP z s 1 .formula
    sf2_e := renderSubFP z s 1 .result
    sf3_s := renderSubFP z s 2 .subject
    sf3_f := renderSubFP z s 2 .formula
    sf3_e := renderSubFP z s 2 .result
    mr1 := renderMemRec z s 0 pub.mr1
    mr2 := renderMemRec z s 1 pub.mr2
    mr3 := renderMemRec z s 2 pub.mr3 }

/-- The rendered private decomposition witness columns of one compute row.
For inactive slots the original `origDec` value is preserved. -/
def renderDec (z : K) (s : ComputeRowSkeleton) (origDec : ComputeTable.Dec K) :
    ComputeTable.Dec K where
  f_h := renderDecFP z s origDec .f_h
  f_t := renderDecFP z s origDec .f_t
  f_th := renderDecFP z s origDec .f_th
  f_tt := renderDecFP z s origDec .f_tt
  f_tth := renderDecFP z s origDec .f_tth
  f_ttt := renderDecFP z s origDec .f_ttt

/-- The honest prover's answer for one committed compute row at the sampled seed `z`.
Inactive decomposition slots are preserved from the original row. -/
def renderComputeRow (z : K) (s : ComputeRowSkeleton)
    (r : ComputeTable.State × ComputeTable.DTcomp K) :
    ComputeTable.State × ComputeTable.DTcomp K :=
  (s.state, (renderInputs z r.2.1, renderPub z s r.2.2.1, renderDec z s r.2.2.2))

@[simp] theorem decFP_renderDec (z : K) (s : ComputeRowSkeleton)
    (origDec : ComputeTable.Dec K) (slot : DecSlot) :
    SemanticStrategy.decFP (renderDec z s origDec) slot = renderDecFP z s origDec slot := by
  cases slot <;> rfl

@[simp] theorem computeSubformulaFPs_renderPub
    (z : K) (s : ComputeRowSkeleton) (pub : ComputeTable.Pub K) (i : Fin 3) :
    computeSubformulaFPs (renderPub z s pub) i =
      (renderSubFP z s i .subject, renderSubFP z s i .formula, renderSubFP z s i .result) := by
  fin_cases i <;> rfl

@[simp] theorem computeMemRec_renderPub
    (z : K) (s : ComputeRowSkeleton) (pub : ComputeTable.Pub K) (i : Fin 3) :
    computeMemRec (renderPub z s pub) i = renderMemRec z s i (computeMemRec pub i) := by
  fin_cases i <;> rfl

/-- **The rendered row binds, at every seed, with no hypothesis at all.**  This is the honest
prover's completeness against the sampled NPR seed of the paper. -/
theorem bindComputeRow_render (z : K) (s : ComputeRowSkeleton)
    (r : ComputeTable.State × ComputeTable.DTcomp K) :
    BindComputeRow z s (renderComputeRow z s r) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    by_cases h : decActive s.state slot = true
    · rw [dif_pos h]
      show SemanticStrategy.decFP (renderDec z s r.2.2.2) slot = _
      rw [decFP_renderDec, renderDecFP, dif_pos h]
    · rw [dif_neg h]
      trivial
  · intro i
    by_cases h : (i : ℕ) < ComputeTable.fanoutComp s.state
    · rw [dif_pos h]
      intro slot
      show tripleFP (computeSubformulaFPs (renderPub z s r.2.2.1) i) slot = _
      rw [computeSubformulaFPs_renderPub]
      cases slot <;> simp only [tripleFP, renderSubFP, dif_pos h]
    · rw [dif_neg h]
      show computeSubformulaFPs (renderPub z s r.2.2.1) i = (0, 0, 0)
      rw [computeSubformulaFPs_renderPub]
      simp only [renderSubFP, dif_neg h]
  · intro i
    by_cases h : (i : ℕ) < Nock.Framework.recordCount s.state
    · rw [dif_pos h]
      show BindMemRec z _ (computeMemRec (renderPub z s r.2.2.1) i)
      rw [computeMemRec_renderPub, renderMemRec, dif_pos h]
      exact ⟨rfl, rfl, rfl⟩
    · rw [dif_neg h]
      show computeMemRec (renderPub z s r.2.2.1) i = _
      rw [computeMemRec_renderPub, renderMemRec, dif_neg h]

/-- **At the honest seed the rendering is the identity.**  Every column it rewrites is already the
committed value, because the supplied row binds. -/
theorem renderComputeRow_eq_self {z : K} {s : ComputeRowSkeleton}
    {r : ComputeTable.State × ComputeTable.DTcomp K}
    (hb : BindComputeRow z s r) : renderComputeRow z s r = r := by
  obtain ⟨hstate, hz, hpubState, hs, hf, he, hdec, hsf, hmr⟩ := hb
  have hinp : renderInputs z r.2.1 = r.2.1 := by
    rw [renderInputs, ← hz]
  have hdec' : renderDec z s r.2.2.2 = r.2.2.2 := by
    have hslot : ∀ slot : DecSlot,
        renderDecFP z s r.2.2.2 slot = SemanticStrategy.decFP r.2.2.2 slot := by
      intro slot
      by_cases h : decActive s.state slot = true
      · have := hdec slot
        rw [dif_pos h] at this
        rw [renderDecFP, dif_pos h, this]
      · rw [renderDecFP, dif_neg h]
    have h1 := hslot .f_h
    have h2 := hslot .f_t
    have h3 := hslot .f_th
    have h4 := hslot .f_tt
    have h5 := hslot .f_tth
    have h6 := hslot .f_ttt
    cases hr : r.2.2.2
    simp only [SemanticStrategy.decFP, hr] at h1 h2 h3 h4 h5 h6
    simp only [renderDec, h1, h2, h3, h4, h5, h6]
  have hsub : ∀ (i : Fin 3) (slot : TripleSlot),
      renderSubFP z s i slot = tripleFP (computeSubformulaFPs r.2.2.1 i) slot := by
    intro i slot
    have := hsf i
    by_cases h : (i : ℕ) < ComputeTable.fanoutComp s.state
    · rw [dif_pos h] at this
      rw [renderSubFP, dif_pos h, this slot]
    · rw [dif_neg h] at this
      rw [renderSubFP, dif_neg h]
      cases slot <;> simp [tripleFP, this]
  have hrec : ∀ i : Fin 3,
      renderMemRec z s i (computeMemRec r.2.2.1 i) = computeMemRec r.2.2.1 i := by
    intro i
    have := hmr i
    by_cases h : (i : ℕ) < Nock.Framework.recordCount s.state
    · rw [dif_pos h] at this
      obtain ⟨hroot, hchild, haxis⟩ := this
      rw [renderMemRec, dif_pos h]
      exact ComputeTable.MemRec.ext hroot.symm hchild.symm haxis.symm rfl
    · rw [dif_neg h] at this
      rw [renderMemRec, dif_neg h, this]
  have hpub : renderPub z s r.2.2.1 = r.2.2.1 := by
    have hs' : GlobalCarryRecognizer.enc z s.subject = r.2.2.1.s := hs.symm
    have hf' : GlobalCarryRecognizer.enc z s.formula = r.2.2.1.f := hf.symm
    have he' : GlobalCarryRecognizer.enc z s.evaluation = r.2.2.1.e := he.symm
    have e0s := hsub 0 .subject
    have e0f := hsub 0 .formula
    have e0e := hsub 0 .result
    have e1s := hsub 1 .subject
    have e1f := hsub 1 .formula
    have e1e := hsub 1 .result
    have e2s := hsub 2 .subject
    have e2f := hsub 2 .formula
    have e2e := hsub 2 .result
    have m0 := hrec 0
    have m1 := hrec 1
    have m2 := hrec 2
    simp only [computeSubformulaFPs, ComputeTable.sfTriple, tripleFP] at e0s e0f e0e e1s e1f e1e e2s e2f e2e
    simp only [computeMemRec] at m0 m1 m2
    unfold renderPub
    rw [hs', hf', he', e0s, e0f, e0e, e1s, e1f, e1e, e2s, e2f, e2e, m0, m1, m2, ← hpubState]
  rw [renderComputeRow, hinp, hpub, hdec', ← hstate]

/-! ## Memory-row rendering -/

/-- The committed memory record of one memory row at seed `z`. -/
def renderMemoryMemRec (z : K) (s : MemoryRowSkeleton) (orig : ComputeTable.MemRec K) :
    ComputeTable.MemRec K :=
  if h : memoryMemRecKind s.state = .active then
    { root := GlobalCarryRecognizer.enc z (s.memoryRecord h).root
      child := GlobalCarryRecognizer.enc z (s.memoryRecord h).child
      axis := (((s.memoryRecord h).axis : ℕ) : K)
      ts := orig.ts }
  else ComputeTable.MemRec.zero

/-- The committed child cell of one memory row at seed `z`; only the noun fingerprint is
committed, and inactive slots are the whole zero cell. -/
def renderCell (z : K) (s : MemoryRowSkeleton) (i : Fin 2) (orig : MemoryTable.Cell K) :
    MemoryTable.Cell K :=
  if h : (i : ℕ) < MemoryTable.fanoutMem s.state then
    { orig with noun := GlobalCarryRecognizer.enc z (s.child i h) }
  else MemoryTable.Cell.zero

/-- The rendered public columns of one memory row. -/
def renderMemoryPub (z : K) (s : MemoryRowSkeleton) (pub : MemoryTable.Pub K) :
    MemoryTable.Pub K :=
  { pub with
    st := s.state
    ver := decide (s.state = MemoryTable.MState.read_root)
    pt := { pub.pt with noun := GlobalCarryRecognizer.enc z s.parent }
    lc := renderCell z s 0 pub.lc
    rc := renderCell z s 1 pub.rc
    mem := renderMemoryMemRec z s pub.mem }

theorem renderMemoryPub_lambda (z : K) (s : MemoryRowSkeleton) (pub : MemoryTable.Pub K) :
    (renderMemoryPub z s pub).lambda = pub.lambda := by
  simp [renderMemoryPub, MemoryTable.Pub.lambda]

/-- The honest prover's answer for one committed memory row at the sampled seed `z`. -/
def renderMemoryRow (z : K) (s : MemoryRowSkeleton)
    (r : MemoryTable.MState × MemoryTable.DTmem K) :
    MemoryTable.MState × MemoryTable.DTmem K :=
  (s.state, ({ r.2.1 with z := z }, renderMemoryPub z s r.2.2))

@[simp] theorem memoryChildCell_renderMemoryPub
    (z : K) (s : MemoryRowSkeleton) (pub : MemoryTable.Pub K) (i : Fin 2) :
    memoryChildCell (renderMemoryPub z s pub) i = renderCell z s i (memoryChildCell pub i) := by
  fin_cases i <;> rfl

/-- The rendered memory row binds at every seed, unconditionally. -/
theorem bindMemoryRow_render (z : K) (s : MemoryRowSkeleton)
    (r : MemoryTable.MState × MemoryTable.DTmem K) :
    BindMemoryRowA z s (renderMemoryRow z s r) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    by_cases h : (i : ℕ) < MemoryTable.fanoutMem s.state
    · rw [dif_pos h]
      show (memoryChildCell (renderMemoryPub z s r.2.2) i).noun = _
      rw [memoryChildCell_renderMemoryPub, renderCell, dif_pos h]
    · rw [dif_neg h]
      show memoryChildCell (renderMemoryPub z s r.2.2) i = _
      rw [memoryChildCell_renderMemoryPub, renderCell, dif_neg h]
  · by_cases h : memoryMemRecKind s.state = .active
    · rw [dif_pos h]
      show BindMemRec z _ (renderMemoryMemRec z s r.2.2.mem)
      rw [renderMemoryMemRec, dif_pos h]
      exact ⟨rfl, rfl, rfl⟩
    · rw [dif_neg h]
      show renderMemoryMemRec z s r.2.2.mem = _
      rw [renderMemoryMemRec, dif_neg h]

/-- At the honest seed the memory rendering is the identity. -/
theorem renderMemoryRow_eq_self {z : K} {s : MemoryRowSkeleton}
    {r : MemoryTable.MState × MemoryTable.DTmem K}
    (hb : BindMemoryRowA z s r) : renderMemoryRow z s r = r := by
  obtain ⟨hstate, hz, hst, hpt, hchild, hmem, hver⟩ := hb
  have hinp : ({ r.2.1 with z := z } : MemoryTable.Inputs K) = r.2.1 := by rw [← hz]
  have hpt' : GlobalCarryRecognizer.enc z s.parent = r.2.2.pt.noun := hpt.symm
  have hcell : ∀ i : Fin 2,
      renderCell z s i (memoryChildCell r.2.2 i) = memoryChildCell r.2.2 i := by
    intro i
    have := hchild i
    by_cases h : (i : ℕ) < MemoryTable.fanoutMem s.state
    · rw [dif_pos h] at this
      rw [renderCell, dif_pos h, ← this]
    · rw [dif_neg h] at this
      rw [renderCell, dif_neg h, this]
  have hmem' : renderMemoryMemRec z s r.2.2.mem = r.2.2.mem := by
    by_cases h : memoryMemRecKind s.state = .active
    · rw [dif_pos h] at hmem
      obtain ⟨hroot, hchild', haxis⟩ := hmem
      rw [renderMemoryMemRec, dif_pos h]
      exact ComputeTable.MemRec.ext hroot.symm hchild'.symm haxis.symm rfl
    · rw [dif_neg h] at hmem
      rw [renderMemoryMemRec, dif_neg h, hmem]
  have hlc := hcell 0
  have hrc := hcell 1
  simp only [memoryChildCell] at hlc hrc
  have hpub : renderMemoryPub z s r.2.2 = r.2.2 := by
    -- `Pub` carries an optParam default on `ver`, so `ext` is not generated; close by cases.
    rcases hr : r.2.2 with ⟨st, pt, lc, rc, lcSt, rcSt, mem, ipre, icur, ver, cprime?, lambda?⟩
    have hlc' : renderCell z s 0 lc = lc := by simpa [hr] using hlc
    have hrc' : renderCell z s 1 rc = rc := by simpa [hr] using hrc
    have hmem'' : renderMemoryMemRec z s mem = mem := by simpa [hr] using hmem'
    have hst' : st = s.state := by simpa [hr] using hst
    have hver' : ver = decide (s.state = MemoryTable.MState.read_root) := by
      simpa [hr] using hver
    have hptn : GlobalCarryRecognizer.enc z s.parent = pt.noun := by
      simpa [hr] using hpt'
    -- Goal after unfold is structural equality including `ver`.
    have : renderMemoryPub z s ⟨st, pt, lc, rc, lcSt, rcSt, mem, ipre, icur, ver, cprime?, lambda?⟩ =
        (⟨st, pt, lc, rc, lcSt, rcSt, mem, ipre, icur, ver, cprime?, lambda?⟩ : MemoryTable.Pub K) := by
      simp only [renderMemoryPub, hst', hptn, hlc', hrc', hmem'']
      -- still need `ver` and `pt` eta
      cases pt
      simpa using hver'.symm
    simpa [hr] using this
  rw [renderMemoryRow, hinp, hpub, ← hstate]

/-! ## The committed timestamp exponents

`ComputeTimestampSpecializesAt` (`SemanticTimestampStrategy.lean:481`) is the paper's statement
that the `α`-dependent columns of a row are exactly powers of the sampled timestamp challenge.  For a committed template it is precisely
the condition under which specialization returns the supplied row. -/

/-- Specialization at `α` returns the placeholder row exactly when the committed exponents are the
row's own timestamp columns.  `α ≠ 0` is required only for the `e > 0` origin recovery
`ln_prev / α^e * α^e`; the exponent-zero case is `pow_zero`. -/
theorem specialize_placeholder_eq {α : K} {stamp : ComputeTimestampRow}
    {r : ComputeTable.State × ComputeTable.DTcomp K}
    (hα : α ≠ 0)
    (h : ComputeTimestampSpecializesAt α stamp r) :
    ComputeRowTemplate.specialize ⟨stamp, r⟩ α = r := by
  obtain ⟨houter, halpha, hstate, hln, hts, hpad⟩ := h
  have hmr : ∀ i : Fin 3,
      specializeMemRecScaled α r.2.2.1.ln_prev
          (decide (computeMemRecKind stamp.state i = .active))
          (stamp.recordExponent i - stamp.lnPrevExponent)
          (computeMemRec r.2.2.1 i) = computeMemRec r.2.2.1 i := by
    intro i
    by_cases hk : computeMemRecKind stamp.state i = .active
    · have hts' := hts i
      rw [if_pos hk] at hts'
      simp only [specializeMemRecScaled, hk, decide_true, if_true]
      exact ComputeTable.MemRec.ext rfl rfl rfl hts'.symm
    · have hk' : computeMemRecKind stamp.state i = .padding := by
        cases hkk : computeMemRecKind stamp.state i with
        | active => exact absurd hkk hk
        | padding => rfl
      have hz := hpad i hk'
      simp only [specializeMemRecScaled, hk, decide_false]
      exact hz.symm
  have h0 := hmr 0
  have h1 := hmr 1
  have h2 := hmr 2
  simp only [computeMemRec] at h0 h1 h2
  have hinp : ({ r.2.1 with α := α } : ComputeTable.Inputs K) = r.2.1 := by rw [← halpha]
  have horigin :
      computeLineOrigin r.2.1.α r.2.2.1.ln_prev stamp.lnPrevExponent
        * α ^ stamp.lnPrevExponent = r.2.2.1.ln_prev := by
    unfold computeLineOrigin
    rw [halpha]
    cases stamp.lnPrevExponent with
    | zero => simp [halpha]
    | succ n =>
      exact div_mul_cancel₀ r.2.2.1.ln_prev (pow_ne_zero _ hα)
  unfold ComputeRowTemplate.specialize
  simp only []
  rw [hinp, horigin, ← hln, h0, h1, h2, ← hstate]
  exact congrArg
    (fun st => ((st, r.2.1, r.2.2.1, r.2.2.2) : ComputeTable.State × ComputeTable.DTcomp K))
    (hstate.trans houter.symm)

theorem memory_specializeA_placeholder_eq {α : K} {stamp : MemoryTimestampRow}
    {r : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp r) :
    MemoryRowTemplate.specializeA ⟨stamp, r⟩ α = r := by
  obtain ⟨houter, hst, hts, hpad⟩ := h
  have hmem :
      specializeMemRec α (decide (memoryMemRecKind stamp.state = .active))
          stamp.recordExponent r.2.2.mem = r.2.2.mem := by
    by_cases hk : memoryMemRecKind stamp.state = .active
    · rw [if_pos hk] at hts
      simp only [specializeMemRec, hk, decide_true, if_true]
      exact ComputeTable.MemRec.ext rfl rfl rfl hts.symm
    · have hk' : memoryMemRecKind stamp.state = .padding := by
        cases hkk : memoryMemRecKind stamp.state with
        | active => exact absurd hkk hk
        | padding => rfl
      have hz := hpad hk'
      simp only [specializeMemRec, hk, decide_false]
      exact hz.symm
  unfold MemoryRowTemplate.specializeA
  simp only []
  rw [hmem, ← hst]
  exact congrArg
    (fun st => ((st, r.2.1, r.2.2) : MemoryTable.MState × MemoryTable.DTmem K))
    (hst.trans houter.symm)

/-- Materializing the placeholder is the
Form R row encode of the a-bearing placeholder: `specialize = encodeRow ∘ specializeA`. -/
theorem memory_specialize_placeholder_eq {α lmb : K} {stamp : MemoryTimestampRow}
    {r : MemoryTable.MState × MemoryTable.DTmem K}
    (h : MemoryTimestampSpecializesAt α stamp r) :
    MemoryRowTemplate.specialize ⟨stamp, r⟩ α lmb = MemoryRowTemplate.encodeRow lmb r := by
  unfold MemoryRowTemplate.specialize
  rw [memory_specializeA_placeholder_eq h]

/-! ## Committed nodes

One committed node carries exactly the three seed-free objects an honest prover holds before the
verifier answers: the pre-seed skeleton row (nouns, Nat axes, state), the committed Nat timestamp
exponents, and the execution row it must reproduce at the honest sample. -/

/-- The template row the honest prover publishes for one committed node at seed `z`. -/
def renderComputeTemplate (z : K) (n : ComputeNode K) : ComputeRowTemplate (K := K) where
  timestamp := n.stamp
  placeholder := renderComputeRow z n.skel n.row

/-- The memory-side template row. -/
def renderMemoryTemplate (z : K) (n : MemoryNode K) : MemoryRowTemplate (K := K) where
  timestamp := n.stamp
  placeholder := renderMemoryRow z n.skel n.row

private theorem wf_tree_list {A : Type*} (lbl : A) (cs : List (NTree A)) :
    2 * totalSize cs + 1 < 2 * totalSize [NTree.node lbl cs] := by
  have h : totalSize [NTree.node lbl cs] = 1 + totalSize cs := by
    rw [totalSize_cons, totalSize_nil]
    simp [NTree.size, totalSize]
  omega

private theorem wf_list_head {A : Type*} (c : NTree A) (rest : List (NTree A)) :
    2 * totalSize [c] < 2 * totalSize (c :: rest) + 1 := by
  rw [totalSize_cons, totalSize_cons, totalSize_nil]
  omega

private theorem wf_list_tail {A : Type*} (c : NTree A) (rest : List (NTree A)) :
    2 * totalSize rest + 1 < 2 * totalSize (c :: rest) + 1 := by
  rw [totalSize_cons]
  have hc : 0 < c.size := by cases c; simp [NTree.size]
  omega

/-! ## The committed skeleton and its all-seed template binding -/

mutual
/-- **The rendered compute template binds to the committed skeleton at every seed.**  No
hypothesis about the seed is used: the committed nouns answer whatever the verifier samples. -/
theorem computeTemplateBinds (z α w : K) :
    ∀ (T : NTree (ComputeNode K)), ComputeNodesOK z α T →
      ComputeTemplateTreeBinds w (mapNTree ComputeNode.skel T)
        (mapNTree (renderComputeTemplate w) T)
  | .node lbl cs, h => by
      obtain ⟨hshape, hstamp, _, _⟩ := h _ (InTree.here _)
      simp only [NTree.label_node, NTree.children_node] at hshape hstamp
      rw [mapNTree, mapNTree]
      refine ComputeTemplateTreeBinds.node ?_ ⟨hstamp, bindComputeRow_render w lbl.skel lbl.row⟩
        (computeTemplateBindsList z α w cs (fun c hc => h.child (by simpa using hc)))
      simpa using hshape
termination_by T _ => 2 * totalSize [T]
decreasing_by exact wf_tree_list _ _

theorem computeTemplateBindsList (z α w : K) :
    ∀ (cs : List (NTree (ComputeNode K))), (∀ c ∈ cs, ComputeNodesOK z α c) →
      List.Forall₂ (ComputeTemplateTreeBinds w)
        (cs.map (mapNTree ComputeNode.skel)) (cs.map (mapNTree (renderComputeTemplate w)))
  | [], _ => .nil
  | c :: rest, h =>
      .cons (computeTemplateBinds z α w c (h c (by simp)))
        (computeTemplateBindsList z α w rest (fun x hx => h x (by simp [hx])))
termination_by cs _ => 2 * totalSize cs + 1
decreasing_by
  all_goals first
    | exact wf_list_head _ _
    | exact wf_list_tail _ _
end

mutual
/-- The memory-side counterpart. -/
theorem memoryTemplateBinds (z α w : K) :
    ∀ (T : NTree (MemoryNode K)), MemoryNodesOK z α T →
      MemoryTemplateTreeBinds w (mapNTree MemoryNode.skel T)
        (mapNTree (renderMemoryTemplate w) T)
  | .node lbl cs, h => by
      obtain ⟨hshape, hstamp, _, _⟩ := h _ (InTree.here _)
      simp only [NTree.label_node, NTree.children_node] at hshape hstamp
      rw [mapNTree, mapNTree]
      refine MemoryTemplateTreeBinds.node ?_ ⟨hstamp, bindMemoryRow_render w lbl.skel lbl.row⟩
        (memoryTemplateBindsList z α w cs (fun c hc => h.child (by simpa using hc)))
      simpa using hshape
termination_by T _ => 2 * totalSize [T]
decreasing_by exact wf_tree_list _ _

theorem memoryTemplateBindsList (z α w : K) :
    ∀ (cs : List (NTree (MemoryNode K))), (∀ c ∈ cs, MemoryNodesOK z α c) →
      List.Forall₂ (MemoryTemplateTreeBinds w)
        (cs.map (mapNTree MemoryNode.skel)) (cs.map (mapNTree (renderMemoryTemplate w)))
  | [], _ => .nil
  | c :: rest, h =>
      .cons (memoryTemplateBinds z α w c (h c (by simp)))
        (memoryTemplateBindsList z α w rest (fun x hx => h x (by simp [hx])))
termination_by cs _ => 2 * totalSize cs + 1
decreasing_by
  all_goals first
    | exact wf_list_head _ _
    | exact wf_list_tail _ _
end

/-! ## The honest sample returns the supplied execution -/

mutual
/-- **At the honest sample the rendered template specializes back to the supplied rows.**  This
is what makes `honest_specialization` a theorem. -/
theorem specializeRenderTree (z α : K) (hα : α ≠ 0) :
    ∀ (T : NTree (ComputeNode K)), ComputeNodesOK z α T →
      mapNTree (fun t => ComputeRowTemplate.specialize t α)
          (mapNTree (renderComputeTemplate z) T) = mapNTree ComputeNode.row T
  | .node lbl cs, h => by
      obtain ⟨_, _, hbind, htime⟩ := h _ (InTree.here _)
      simp only [NTree.label_node] at hbind htime
      rw [mapNTree, mapNTree, mapNTree, List.map_map]
      have hlbl : ComputeRowTemplate.specialize (renderComputeTemplate z lbl) α = lbl.row := by
        rw [renderComputeTemplate, renderComputeRow_eq_self hbind]
        exact specialize_placeholder_eq hα htime
      rw [hlbl]
      exact congrArg _ (specializeRenderList z α hα cs (fun c hc => h.child (by simpa using hc)))
termination_by T _ => 2 * totalSize [T]
decreasing_by exact wf_tree_list _ _

theorem specializeRenderList (z α : K) (hα : α ≠ 0) :
    ∀ (cs : List (NTree (ComputeNode K))), (∀ c ∈ cs, ComputeNodesOK z α c) →
      cs.map (fun t => mapNTree (fun u => ComputeRowTemplate.specialize u α)
          (mapNTree (renderComputeTemplate z) t)) = cs.map (mapNTree ComputeNode.row)
  | [], _ => rfl
  | c :: rest, h => by
      rw [List.map_cons, List.map_cons, specializeRenderTree z α hα c (h c (by simp)),
        specializeRenderList z α hα rest (fun x hx => h x (by simp [hx]))]
termination_by cs _ => 2 * totalSize cs + 1
decreasing_by
  all_goals first
    | exact wf_list_head _ _
    | exact wf_list_tail _ _
end

mutual
theorem specializeRenderMemTree (z α : K) :
    ∀ (T : NTree (MemoryNode K)), MemoryNodesOK z α T →
      mapNTree (fun t => MemoryRowTemplate.specializeA t α)
          (mapNTree (renderMemoryTemplate z) T) = mapNTree MemoryNode.row T
  | .node lbl cs, h => by
      obtain ⟨_, _, hbind, htime⟩ := h _ (InTree.here _)
      simp only [NTree.label_node] at hbind htime
      rw [mapNTree, mapNTree, mapNTree, List.map_map]
      have hlbl : MemoryRowTemplate.specializeA (renderMemoryTemplate z lbl) α = lbl.row := by
        rw [renderMemoryTemplate, renderMemoryRow_eq_self hbind]
        exact memory_specializeA_placeholder_eq htime
      rw [hlbl]
      exact congrArg _ (specializeRenderMemList z α cs (fun c hc => h.child (by simpa using hc)))
termination_by T _ => 2 * totalSize [T]
decreasing_by exact wf_tree_list _ _

theorem specializeRenderMemList (z α : K) :
    ∀ (cs : List (NTree (MemoryNode K))), (∀ c ∈ cs, MemoryNodesOK z α c) →
      cs.map (fun t => mapNTree (fun u => MemoryRowTemplate.specializeA u α)
          (mapNTree (renderMemoryTemplate z) t)) = cs.map (mapNTree MemoryNode.row)
  | [], _ => rfl
  | c :: rest, h => by
      rw [List.map_cons, List.map_cons, specializeRenderMemTree z α c (h c (by simp)),
        specializeRenderMemList z α rest (fun x hx => h x (by simp [hx]))]
termination_by cs _ => 2 * totalSize cs + 1
decreasing_by
  all_goals first
    | exact wf_list_head _ _
    | exact wf_list_tail _ _
end

/-! ## The committed configuration and execution templates -/

/-- The committed `α`-free configuration.  Every exact-domain datum is the supplied execution's
own; the only seed-dependent column is the sampled NPR seed itself. -/
def configTemplateOf (E : BuildableNockExecution F K) (z : K) : ExactConfigTemplate F K where
  challenges :=
    { a := E.cfg.challenges.a, b := E.cfg.challenges.b, c := E.cfg.challenges.c
      z := z, β := E.cfg.challenges.β, γ := E.cfg.challenges.γ }
  Ksz := E.cfg.Ksz
  kMem := E.cfg.kMem
  orbit := E.cfg.orbit
  orbit_h_pos := E.cfg.orbit_h_pos
  compRows := E.cfg.compRows
  memRows := E.cfg.memRows
  compRows_pos := E.cfg.compRows_pos
  memRows_pos := E.cfg.memRows_pos
  compRows_le := E.cfg.compRows_le
  memRows_le := E.cfg.memRows_le
  eDeg := E.cfg.eDeg
  eDeg_eq_one := E.cfg.eDeg_eq_one
  compNodes := E.cfg.compNodes
  compNodes_spec := E.cfg.compNodes_spec
  memNodes := E.cfg.memNodes
  memNodes_spec := E.cfg.memNodes_spec

namespace Data

variable {E : BuildableNockExecution F K}

/-- The committed execution template published at the sampled seed `z`. -/
def executionTemplate (D : Data E) (z : K) :
    ExactExecutionTemplate (configTemplateOf E z) where
  computeTree := mapNTree (renderComputeTemplate z) D.computeNodes
  memoryForest := D.memoryNodes.map (mapNTree (renderMemoryTemplate z))
  memoryForest_nonempty := by
    have hne : D.memoryNodes ≠ [] := by
      intro h
      apply E.execA.memoryForest_nonempty
      rw [← D.memory_rows, h, List.map_nil]
    simpa using hne
  memory_root_count := by
    have h1 : D.memoryNodes.length = E.execA.memoryForest.length := by
      rw [← D.memory_rows, List.length_map]
    rw [List.length_map, h1]
    exact E.execA.memory_root_count
  compute_bfs_length := by
    have hgen : ∀ (A : Type) (f : ComputeNode K → A) (t : NTree (ComputeNode K)),
        (bfsForest [mapNTree f t]).length = (bfsForest [t]).length := by
      intro A f t
      rw [show [mapNTree f t] = [t].map (mapNTree f) from rfl, bfsForest_mapNTree, List.length_map]
    rw [hgen _ (renderComputeTemplate z) D.computeNodes, ← hgen _ ComputeNode.row D.computeNodes,
      D.compute_rows]
    exact E.exec.compute_bfs_length
  memory_bfs_length := by
    have hgen : ∀ (A : Type) (f : MemoryNode K → A) (l : List (NTree (MemoryNode K))),
        (bfsForest (l.map (mapNTree f))).length = (bfsForest l).length := by
      intro A f l
      rw [bfsForest_mapNTree, List.length_map]
    rw [hgen _ (renderMemoryTemplate z) D.memoryNodes,
      ← hgen _ MemoryNode.row D.memoryNodes, D.memory_rows]
    exact E.execA.memory_bfs_length

omit [Field F] [Algebra F K] in
/-- The Form R row encode writes the `λ` it is given (the package `cfg.challenges.lam`). -/
theorem encodeRow_lambda (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K) :
    (MemoryRowTemplate.encodeRow lmb r).2.2.lambda = lmb := by
  unfold MemoryRowTemplate.encodeRow
  split <;> simp [MemoryTable.Pub.lambda]

/-- Specialization at the honest execution's own sampled `λ` (`E.cfg.challenges.lam`) and the
executed row encode write the same `λ`, and the committed nodes are the honest a-bearing forest,
so every seed's specialized memory row at that `λ` carries the honest row's `λ`.  (The template
is λ-free; at another sampled `λ` every row carries that `λ` instead,
`ExactExecutionTemplate.specialize_memory_lambda`.) -/
theorem memory_lambda_list (D : Data E) (z α : K) :
    (((D.executionTemplate z).specialize α E.cfg.challenges.lam).memoryRows.map
        fun r => r.2.2.lambda) =
      E.exec.memoryRows.map fun r => r.2.2.lambda := by
  rw [ExactExecutionTemplate.specialize_memoryRows]
  simp only [List.map_map, Function.comp_def, MemoryRowTemplate.specialize_lambda]
  rw [ExactExecutionTemplate.memoryRows, executionTemplate, bfsForest_mapNTree]
  simp only [List.map_map, Function.comp_def]
  rw [E.exec_encode, ExactExecution.encodeMem_memoryRows, ExactExecution.memoryRows,
    ← D.memory_rows, bfsForest_mapNTree]
  simp only [List.map_map, Function.comp_def, encodeRow_lambda]

theorem specialized_memory_lambda_eq (D : Data E) (z α : K) (i : Fin E.cfg.memRows) :
    (((D.executionTemplate z).specialize α E.cfg.challenges.lam).memoryPubAt i).lambda =
      (E.exec.memoryPubAt i).lambda := by
  have hlist := D.memory_lambda_list z α
  have hlenE : E.exec.memoryRows.length = E.cfg.memRows := E.exec.memoryRows_length
  have hlenS : ((D.executionTemplate z).specialize α E.cfg.challenges.lam).memoryRows.length =
      E.exec.memoryRows.length := by
    rw [ExactExecution.memoryRows_length, hlenE]
    rfl
  have hiE : (i : ℕ) < E.exec.memoryRows.length := by
    rw [hlenE]; exact i.isLt
  have hiS : (i : ℕ) < ((D.executionTemplate z).specialize α E.cfg.challenges.lam).memoryRows.length := by
    rw [hlenS]; exact hiE
  have hEq := List.getElem_of_eq hlist (by simpa [List.length_map] using hiS)
  have hL :=
    (List.getElem_map
      (l := ((D.executionTemplate z).specialize α E.cfg.challenges.lam).memoryRows)
      (f := fun r => r.2.2.lambda) (i := i.val)
      (h := by simpa [List.length_map] using hiS)).symm
  have hR :=
    List.getElem_map (l := E.exec.memoryRows)
      (f := fun r => r.2.2.lambda) (i := i.val)
      (h := by simpa [List.length_map] using hiE)
  simp only [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, List.get_eq_getElem]
  exact hL.trans (hEq.trans hR)

/-- The staged committed timestamp strategy: a seed-indexed family of `α`-free templates, all
generated from the one committed node tree. -/
def timestampStrategy (D : Data E) :
    DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K) :=
  DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData
    D.skeleton.publicClaim
    (fun seed => configTemplateOf E seed.1)
    (fun seed => D.executionTemplate seed.1)
    (fun _ => rfl)

/-- **The committed template is semantically consistent with the committed skeleton at every
sampled seed.** -/
theorem templateConsistency (D : Data E) (z : K) :
    TemplateSemanticConsistencyAt z D.skeleton (configTemplateOf E z) (D.executionTemplate z) where
  sampledSeed := rfl
  computeTree :=
    computeTemplateBinds E.cfg.challenges.z E.cfg.challenges.α z D.computeNodes D.computeOK
  memoryForest :=
    memoryTemplateBindsList E.cfg.challenges.z E.cfg.challenges.α z D.memoryNodes D.memoryOK

/-- The full production binding at every sampled `(z, α, λ)`. -/
theorem binds (D : Data E) (z : K) (α lmb : K) :
    BindsAt z D.skeleton ((configTemplateOf E z).specialize α lmb)
      ((D.executionTemplate z).specialize α lmb) :=
  (D.templateConsistency z).specialize

/-- At the honest sample the committed configuration is the supplied one. -/
theorem honest_cfg (_D : Data E) :
    (configTemplateOf E E.cfg.challenges.z).specialize E.cfg.challenges.α
      E.cfg.challenges.lam = E.cfg := rfl

set_option maxHeartbeats 800000 in
/-- **At the honest sample the committed template is the supplied execution.** -/
theorem honestAlpha_ne (_D : Data E) : E.cfg.challenges.α ≠ 0 := by
  intro hα
  obtain ⟨w⟩ := E.timestampBounds
  have hord := w.timestampBound_le_order
  have hzero : orderOf (0 : K) = 0 := by
    rw [orderOf_eq_zero_iff]
    intro h
    obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 h
    rw [zero_pow (by omega : n ≠ 0)] at hpow
    exact zero_ne_one hpow
  rw [hα, hzero] at hord
  have htb : w.timestampBound = 0 := by omega
  have hempty : w.semanticRequests = [] := by
    match hs : w.semanticRequests with
    | [] => rfl
    | r :: _ =>
      have hexp := w.requestTimestampBound r (by simp [hs])
      rw [htb] at hexp
      exact (Nat.not_lt_zero r.2.2 hexp).elim
  have hbridge := w.requests_bridge
  simp [hempty, bridgeRecords] at hbridge
  have hnil : E.exec.derivedRequestIO ≠ [] := by
    intro hnil
    obtain ⟨row, hrow⟩ :=
      List.exists_mem_of_ne_nil E.exec.computeRows E.exec.computeRows_nonempty
    have hactive : NockVM.activeRequestRecords row.2.2.1 ≠ [] := by
      cases hst : row.2.2.1.state <;> simp [NockVM.activeRequestRecords, hst]
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hactive
    have hmem : NockVM.encRecFormR r E.cfg.challenges.lam ∈ E.exec.derivedRequestIO := by
      rw [ExactExecution.derivedRequestIO_eq_computeRows]
      refine List.mem_map.mpr ⟨r, ?_, rfl⟩
      exact List.mem_flatMap.mpr ⟨row, hrow, hr⟩
    rw [hnil] at hmem
    simp at hmem
  exact hnil hbridge

theorem honest_execA (D : Data E) :
    (D.executionTemplate E.cfg.challenges.z).specializeA E.cfg.challenges.α
      E.cfg.challenges.lam = E.execA := by
  refine ExactExecution.ext _ _ ?_ ?_
  · show mapNTree (fun t => ComputeRowTemplate.specialize t E.cfg.challenges.α)
      (mapNTree (renderComputeTemplate E.cfg.challenges.z) D.computeNodes) = E.execA.computeTree
    rw [specializeRenderTree E.cfg.challenges.z E.cfg.challenges.α D.honestAlpha_ne
      D.computeNodes D.computeOK]
    rw [D.compute_rows, E.exec_encode]
    rfl
  · show (D.memoryNodes.map (mapNTree (renderMemoryTemplate E.cfg.challenges.z))).map
      (mapNTree (fun t => MemoryRowTemplate.specializeA t E.cfg.challenges.α)) =
        E.execA.memoryForest
    rw [List.map_map]
    rw [show ((fun t => mapNTree (fun u => MemoryRowTemplate.specializeA u E.cfg.challenges.α) t) ∘
        (fun t => mapNTree (renderMemoryTemplate E.cfg.challenges.z) t)) =
      (fun t => mapNTree (fun u => MemoryRowTemplate.specializeA u E.cfg.challenges.α)
        (mapNTree (renderMemoryTemplate E.cfg.challenges.z) t)) from rfl,
      specializeRenderMemList E.cfg.challenges.z E.cfg.challenges.α D.memoryNodes D.memoryOK]
    exact D.memory_rows

theorem honest_exec (D : Data E) :
    (D.executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α
      E.cfg.challenges.lam = E.exec := by
  rw [ExactExecutionTemplate.specialize_eq_encodeMem, E.exec_encode, D.honest_execA]
  rfl

/-- The honest seed is the execution's own sampled NPR seed, and it is nonzero because the exact
semantic language already requires it. -/
theorem honestSeed_ne (_D : Data E) : E.cfg.challenges.z ≠ 0 :=
  E.chained.z_ne_zero

/-- **`honest_specialization` is a theorem here, not an assumption.** -/
theorem honest_specialization (D : Data E) :
    specializedProblem D.timestampStrategy E.cfg.challenges.z D.honestSeed_ne
        E.cfg.challenges.α E.cfg.challenges.lam = ⟨E.cfg, E.exec⟩ :=
  congrArg (fun e => (⟨E.cfg, e⟩ : RawProblem F K)) D.honest_exec

/-- The supplied execution binds to the committed skeleton at its own sampled seed. -/
theorem honest_binds (D : Data E) :
    BindsAt E.cfg.challenges.z D.skeleton E.cfg E.exec := by
  rw [← D.honest_exec]
  exact D.binds E.cfg.challenges.z E.cfg.challenges.α E.cfg.challenges.lam

end Data

/-! ## Orbit capacity is a state-only invariant of the committed skeleton

Both IO prefixes are extracted by `activeRequestRecords` and `responseRecords`, which read the
row's state and nothing else.  A binding pins every row state to its committed skeleton row, so
the two prefix lengths are the same at every sampled seed as at the honest one. -/

/-- The number of memory requests one compute state emits. -/
def reqLen : ComputeTable.State → ℕ
  | .s1 | .s3 | .s4 | .cons => 1
  | .s0 | .s2 | .s5 | .s7 | .s8 => 2
  | .s6 | .s9 => 3

/-- The number of external responses one memory state serves; only `read_root` serves one. -/
def respLen : MemoryTable.MState → ℕ
  | .read_root => 1
  | _ => 0

theorem activeRequestRecords_length {z : K} {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (h : BindComputeRow z s row) :
    (NockVM.activeRequestRecords row.2.2.1).length = reqLen s.state := by
  have hst : row.2.2.1.state = s.state := h.2.2.1
  unfold NockVM.activeRequestRecords
  rw [hst]
  cases s.state <;> rfl

theorem responseRecords_length {z : K} {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : BindMemoryRow z s row) :
    (MemoryTable.responseRecords row.2.2).length = respLen s.state := by
  have hst : row.2.2.st = s.state := h.2.2.1
  have hver := BindMemoryRow.ver_eq z h
  unfold MemoryTable.responseRecords
  rw [hver]
  cases hs : s.state <;> simp [hs, respLen]

theorem rawRequests_length_of_forall₂ {z : K}
    {skelRows : List ComputeRowSkeleton}
    {rows : List (ComputeTable.State × ComputeTable.DTcomp K)}
    (h : List.Forall₂ (BindComputeRow z) skelRows rows) :
    (rows.flatMap (fun r => NockVM.activeRequestRecords r.2.2.1)).length
      = (skelRows.map (fun s => reqLen s.state)).sum := by
  induction h with
  | nil => rfl
  | @cons s row _ _ hb _ ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih,
        activeRequestRecords_length hb]

theorem derivedVerResponse_length {z : K} {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : BindMemoryRow z s row) :
    (if row.2.2.ver = true then 1 else 0) = respLen s.state := by
  have hver := BindMemoryRow.ver_eq z h
  rw [hver]
  cases s.state <;> simp [respLen]

theorem derivedResponseList_length_of_forall₂ {z : K}
    {skelRows : List MemoryRowSkeleton}
    {rows : List (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : List.Forall₂ (BindMemoryRow z) skelRows rows) :
    (rows.flatMap (fun row =>
        if row.2.2.ver = true then [NockVM.encRecC row.2.2.mem row.2.2.cprime] else [])).length
      = (skelRows.map (fun s => respLen s.state)).sum := by
  induction h with
  | nil => rfl
  | @cons s row _ _ hb _ ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih]
      rw [← derivedVerResponse_length hb]
      by_cases hv : row.2.2.ver = true <;> simp [hv]

/-- Any two executions binding the same committed skeleton have the same request-prefix length. -/
theorem derivedRequestIO_length_eq {z z' : K} {S : SemanticSkeleton}
    {cfg cfg' : ExactConfig F K} {exec : ExactExecution cfg} {exec' : ExactExecution cfg'}
    (h : BindsAt z S cfg exec) (h' : BindsAt z' S cfg' exec') :
    exec.derivedRequestIO.length = exec'.derivedRequestIO.length := by
  simp only [ExactExecution.derivedRequestIO, List.length_map,
    ExactExecution.rawRequests_eq_computeRows]
  rw [rawRequests_length_of_forall₂ h.derived_computeRows,
    rawRequests_length_of_forall₂ h'.derived_computeRows]

/-- The response-prefix counterpart. -/
theorem derivedResponseIO_length_eq {z z' : K} {S : SemanticSkeleton}
    {cfg cfg' : ExactConfig F K} {exec : ExactExecution cfg} {exec' : ExactExecution cfg'}
    (h : BindsAt z S cfg exec) (h' : BindsAt z' S cfg' exec') :
    exec.derivedResponseIO.length = exec'.derivedResponseIO.length := by
  simp only [ExactExecution.derivedResponseIO]
  rw [derivedResponseList_length_of_forall₂ h.derived_memoryRows,
    derivedResponseList_length_of_forall₂ h'.derived_memoryRows]

/-! ## The constructed commitment residual -/

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
variable {E : BuildableNockExecution F K}

/-- The committed template verifier.  The post-challenge table, IO and walk arrays are the
prover's *later-round* message — the paper has the prover build them only after the verifier
answers — so they are supplied here rather than derived. -/
def verifierOf (D : Data E)
    (A : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      TemplateRawJointSoundness.AlphaMCommitment (p := ringChar K) D.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K) (_lmb : K), nprSeed ω ≠ 0 → RawWalkArrays K) :
    ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K) :=
  ProductionRawVerifier.TemplateAdapter.Strategy.honest
    { timestamp := D.timestampStrategy, afterAlphaM := A, afterCoins := W }

/-- The compute tree's root label is compute row `0`. -/
theorem computeRowAt_zero_eq_treeRoot {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computeRowAt ⟨0, cfg.compRows_pos⟩ = exec.computeTree.label := by
  have hrows : exec.computeRows =
      exec.computeTree.label ::
        ((bfsForest [exec.computeTree]).flatMap NTree.children).map NTree.label := by
    show (bfsForest [exec.computeTree]).map NTree.label = _
    conv_lhs => rw [bfsForest_eq_append_flatMap [exec.computeTree] (by simp)]
    simp
  show exec.computeRows.get _ = _
  rw [List.get_eq_getElem, List.getElem_of_eq hrows]
  simp

/-- **The honest execution starts its compute line at `1`**, from the committed root row
(`Data.root_line_origin`) through `compute_rows`.  This is the value the deployed chip's
`finalLnInit` gate checks. -/
theorem Data.line_origin (D : Data E) :
    (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).ln_prev = 1 := by
  have hlabel : E.exec.computeTree.label = D.computeNodes.label.row := by
    rw [← D.compute_rows, mapNTree_label]
  show (E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩).2.2.1.ln_prev = 1
  rw [computeRowAt_zero_eq_treeRoot, hlabel]
  exact D.root_line_origin

/-- Every specialized memory table of the committed template shares row 0's `λ`.
Specialization and rendering copy `Pub.lambda`, and the committed nodes are the honest
forest and `specialize` writes the configuration's `λ` on every memory row
(`encodeRow`), so each specialized row's `Pub.lambda` is `familyAt`'s `cfg.challenges.lam`.
Not a field of `E` and not a `nockCompiles_zmod` hypothesis. -/
theorem Data.verifierMemoryLambdaUniform (D : Data E)
    (A : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      TemplateRawJointSoundness.AlphaMCommitment (p := ringChar K) D.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K) (_lmb : K), nprSeed ω ≠ 0 → RawWalkArrays K) :
    ∀ (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
      (i : Fin ((verifierOf D A W).familyAt ω lmb hz).cfg.memRows),
      (((verifierOf D A W).familyAt ω lmb hz).exec.memoryPubAt i).lambda =
        ((verifierOf D A W).familyAt ω lmb hz).cfg.challenges.lam :=
  fun ω lmb hz i => (verifierOf D A W).familyAt_memoryLambda ω lmb hz i

/-- **Milestone 5's committed layer, constructed.**  Every seed-indexed obligation of
`CommitmentResidual` — the committed template, the three all-seed committed checks, the honest
seed and `alphaM`, `honest_specialization`, and the three all-seed characteristic/capacity bounds
— is a theorem about the rendering of the committed data.  The remaining fields are the supplied
seed-free semantic obligations on the committed skeleton and the later-round arrays. -/
def commitmentResidualOf (D : Data E)
    (A : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      TemplateRawJointSoundness.AlphaMCommitment (p := ringChar K) D.timestampStrategy z hz α lmb)
    (W : ∀ (ω : JointCoins K) (_lmb : K), nprSeed ω ≠ 0 → RawWalkArrays K) :
    BuildablePackage.CommitmentResidual E where
  verifier := verifierOf D A W
  commitment := ⟨D.skeleton, D.nounSizeBound⟩
  claim_eq := rfl
  scan := fun z _ α lmb =>
    RawSemanticAssembly.activeFingerprintChecksAt_of_bindsAt (D.binds z α lmb)
  shapeMatch := fun z _ α lmb =>
    RawSemanticAssembly.execTreeShapeMatchesAt_of_bindsAt (D.binds z α lmb)
  rowFrame := fun z _ α lmb =>
    RawSemanticAssembly.rowFrameChecksAt_of_bindsAt (D.binds z α lmb)
  slotSemantics := D.slotSemantics
  recordEquations := D.recordEquations
  Λ := D.Λ
  census := D.census
  sizeWindowBound := D.sizeWindowBound
  honestSeed := E.cfg.challenges.z
  honestSeed_ne := D.honestSeed_ne
  honestAlpha := E.cfg.challenges.α
  honest_specialization := D.honest_specialization
  computeLineOrigin := D.line_origin
  q_eq_ringChar := D.q_eq_ringChar
  skeletonBounded := D.skeletonBounded
  combinedBounded := D.combinedBounded
  KszBound := fun _ _ _ _ => E.Ksz_lt_ringChar
  progCapacity := fun z _ α lmb => by
    show ((D.executionTemplate z).specialize α lmb).derivedRequestIO.length + 1 ≤
      2 ^ E.cfg.orbit.h
    rw [derivedRequestIO_length_eq (D.binds z α lmb) D.honest_binds]
    exact E.programIOCapacity
  memCapacity := fun z _ α lmb => by
    show ((D.executionTemplate z).specialize α lmb).derivedResponseIO.length + 1 ≤
      2 ^ E.cfg.orbit.h
    rw [derivedResponseIO_length_eq (D.binds z α lmb) D.honest_binds]
    exact E.memoryIOCapacity

/-! ## A trivial later-round message

These are the *only* pieces `commitmentResidualOf` leaves open, and they are the prover's
post-challenge arrays.  The all-zero choice inhabits the constructor but
carries no acceptance: nothing here claims the resulting strategy accepts any coin. -/

/-- All-zero post-`alphaM` family data. -/
def zeroFamilyData (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (α lmb : K) : AlphaMFamilyData T z hz α lmb where
  compNodeWidth := 1
  compNodeEncode := fun _ _ => 0
  memNodeWidth := 1
  memNodeEncode := fun _ _ => 0
  requests := 0
  responses := 0
  outMem := 0

/-- All-zero post-`alphaM` commitment. -/
def zeroAlphaM (T : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (α lmb : K) : AlphaMCommitment (p := ringChar K) T z hz α lmb where
  familyData := zeroFamilyData T z hz α lmb
  tables := { compute := fun _ => ⟨0, 0⟩, memory := fun _ => 0 }
  io := { multiplicity := fun _ => 0, progAcc := fun _ => 0, memAcc := fun _ => 0 }

/-- All-zero walk arrays. -/
def zeroWalk : RawWalkArrays K where
  computeLn := fun _ => 0
  computeCount := fun _ => 0
  computeAcc := fun _ => 0
  memoryLn := fun _ => 0
  memoryCount := fun _ => 0
  memoryAcc := fun _ => 0

/-- The committed residual over the all-zero later-round message. -/
def commitmentResidualOfZero (D : Data E) : BuildablePackage.CommitmentResidual E :=
  commitmentResidualOf D (fun z hz α lmb => zeroAlphaM D.timestampStrategy z hz α lmb)
    (fun _ _ _ => zeroWalk)

/-! ## F73: the constructor is inhabited

The existing F73 fixture already carries every seed-free datum the commitment needs — the OP1
skeleton row, the five-row memory skeleton, and the committed timestamp exponents — so it
instantiates `Data`.  The residual obtained from it is a *second* inhabitant of
`CommitmentResidual`, distinct from the hand-built `BuildablePackage.Concrete.residual73`: its
committed template is generated by the renderer at every seed rather than written down. -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open OptimizedComputeFinalTrace

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := ConcreteStrictPackage.concrete_char73
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem computeRowTemplate_specialize (z α : K73cubic) :
    (computeRowTemplate z).specialize α = computeRow z α := by
  simp [ComputeRowTemplate.specialize, computeRowTemplate, specializeMemRecScaled, computeLineOrigin,
    computeMemRecKind, Nock.Framework.recordCount, computeRow, computeInputs, computePub,
    requestRecord]

theorem dummyHaltRowTemplate_specializeA (z α : K73cubic) :
    (dummyHaltRowTemplate z).specializeA α = dummyHaltRow z := by
  simp [MemoryRowTemplate.specializeA, dummyHaltRowTemplate, specializeMemRec, memoryMemRecKind,
    dummyHaltRow, dummyHaltPub]

theorem readRowTemplate_specializeA (z α : K73cubic) :
    (readRowTemplate z).specializeA α = readRowA z α := by
  simp [MemoryRowTemplate.specializeA, readRowTemplate, specializeMemRec, memoryMemRecKind,
    readRowA, readPubA, readPub, requestRecord]

theorem decomposeRowTemplate_specializeA (z α : K73cubic) :
    (decomposeRowTemplate z).specializeA α = decomposeRow z α := by
  simp [MemoryRowTemplate.specializeA, decomposeRowTemplate, specializeMemRec, memoryMemRecKind,
    decomposeRow, decomposePub]

theorem headRowTemplate_specializeA (z α : K73cubic) :
    (headRowTemplate z).specializeA α = headRow z := by
  simp [MemoryRowTemplate.specializeA, headRowTemplate, specializeMemRec, memoryMemRecKind,
    headRow, headPub]

theorem verifyRowTemplate_specializeA (z α : K73cubic) :
    (verifyRowTemplate z).specializeA α = verifyRowA z α := by
  simp [MemoryRowTemplate.specializeA, verifyRowTemplate, specializeMemRec, memoryMemRecKind,
    verifyRowA, verifyPubA, verifyPub, requestRecord]

theorem tailRowTemplate_specializeA (z α : K73cubic) :
    (tailRowTemplate z).specializeA α = tailRow z := by
  simp [MemoryRowTemplate.specializeA, tailRowTemplate, specializeMemRec, memoryMemRecKind,
    tailRow, tailPub]

theorem bindA_of_bind {z : K73cubic} {s : MemoryRowSkeleton}
    {r : MemoryTable.MState × MemoryTable.DTmem K73cubic}
    (h : BindMemoryRow z s r) (hna : memoryMemRecKind s.state ≠ .active) :
    BindMemoryRowA z s r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, h7⟩
  rw [dif_neg hna] at h6 ⊢
  exact h6

theorem bindA_readRowA (z α : K73cubic) :
    BindMemoryRowA z readSkeletonRow (readRowA z α) := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := bind_readRow z α
  refine ⟨h1, h2, h3, h4, h5, ?_, h7⟩
  have ha : memoryMemRecKind readSkeletonRow.state = .active := rfl
  rw [dif_pos ha]
  refine ⟨rfl, rfl, ?_⟩
  simp [readRowA, readPubA, requestRecord, readSkeletonRow, requestSkeleton,
    SemanticStrategy.MemoryRowSkeleton.memoryRecord]

theorem bindA_verifyRowA (z α : K73cubic) :
    BindMemoryRowA z verifySkeletonRow (verifyRowA z α) := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := bind_verifyRow z α
  refine ⟨h1, h2, h3, h4, h5, ?_, h7⟩
  have ha : memoryMemRecKind verifySkeletonRow.state = .active := rfl
  rw [dif_pos ha]
  refine ⟨rfl, rfl, ?_⟩
  simp [verifyRowA, verifyPubA, requestRecord, verifySkeletonRow, requestSkeleton,
    SemanticStrategy.MemoryRowSkeleton.memoryRecord]

def computeNode : ComputeNode K73cubic where
  skel := computeSkeletonRow
  stamp := (computeRowTemplate honestSeed).timestamp
  row := computeRow honestSeed honestAlpha

def computeNodeTree : NTree (ComputeNode K73cubic) := .node computeNode []

def dummyHaltNode : MemoryNode K73cubic where
  skel := dummyHaltSkeletonRow
  stamp := (dummyHaltRowTemplate honestSeed).timestamp
  row := dummyHaltRow honestSeed

def dummyHaltNodeTree : NTree (MemoryNode K73cubic) := .node dummyHaltNode []

def readNode : MemoryNode K73cubic where
  skel := readSkeletonRow
  stamp := (readRowTemplate honestSeed).timestamp
  row := readRowA honestSeed honestAlpha

def decomposeNode : MemoryNode K73cubic where
  skel := decomposeSkeletonRow
  stamp := (decomposeRowTemplate honestSeed).timestamp
  row := decomposeRow honestSeed honestAlpha

def headNode : MemoryNode K73cubic where
  skel := headSkeletonRow
  stamp := (headRowTemplate honestSeed).timestamp
  row := headRow honestSeed

def verifyNode : MemoryNode K73cubic where
  skel := verifySkeletonRow
  stamp := (verifyRowTemplate honestSeed).timestamp
  row := verifyRowA honestSeed honestAlpha

def tailNode : MemoryNode K73cubic where
  skel := tailSkeletonRow
  stamp := (tailRowTemplate honestSeed).timestamp
  row := tailRow honestSeed

def memNodeTree : NTree (MemoryNode K73cubic) :=
  .node readNode
    [.node decomposeNode
      [.node headNode [], .node verifyNode [.node tailNode []]]]

theorem computeNodeTree_OK :
    ComputeNodesOK honestSeed honestAlpha computeNodeTree := by
  refine ComputeNodesOK.mk' ?_ (by simp)
  refine ⟨?_, rfl, bind_computeRow _ _, ?_⟩
  · simp [computeNode, computeSkeletonRow, ComputeTable.fanoutComp]
  · simp only [NTree.label_node, computeNode]
    rw [← computeRowTemplate_specialize honestSeed honestAlpha]
    exact ComputeRowTemplate.specializes _ _

theorem dummyHaltNodeTree_OK :
    MemoryNodesOK honestSeed honestAlpha dummyHaltNodeTree := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bindA_of_bind (bind_dummyHaltRow _) (by decide), ?_⟩ (by simp)
  simp only [NTree.label_node, dummyHaltNode]
  rw [← dummyHaltRowTemplate_specializeA honestSeed honestAlpha]
  exact MemoryRowTemplate.specializesA _ _

theorem memNodeTree_OK :
    MemoryNodesOK honestSeed honestAlpha memNodeTree := by
  refine MemoryNodesOK.mk' ⟨rfl, rfl, bindA_readRowA _ _, ?_⟩ ?_
  · simp only [NTree.label_node, readNode]
    rw [← readRowTemplate_specializeA honestSeed honestAlpha]
    exact MemoryRowTemplate.specializesA _ _
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bindA_of_bind (bind_decomposeRow _ _) (by decide), ?_⟩ ?_
    · simp only [NTree.label_node, decomposeNode]
      rw [← decomposeRowTemplate_specializeA honestSeed honestAlpha]
      exact MemoryRowTemplate.specializesA _ _
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine MemoryNodesOK.mk' ⟨rfl, rfl, bindA_of_bind (bind_headRow _) (by decide),
          ?_⟩ (by simp)
        simp only [NTree.label_node, headNode]
        rw [← headRowTemplate_specializeA honestSeed honestAlpha]
        exact MemoryRowTemplate.specializesA _ _
      · refine MemoryNodesOK.mk' ⟨rfl, rfl, bindA_verifyRowA _ _, ?_⟩ ?_
        · simp only [NTree.label_node, verifyNode]
          rw [← verifyRowTemplate_specializeA honestSeed honestAlpha]
          exact MemoryRowTemplate.specializesA _ _
        · intro e he
          simp only [List.mem_singleton] at he
          subst he
          refine MemoryNodesOK.mk' ⟨rfl, rfl, bindA_of_bind (bind_tailRow _) (by decide),
              ?_⟩ (by simp)
          simp only [NTree.label_node, tailNode]
          rw [← tailRowTemplate_specializeA honestSeed honestAlpha]
          exact MemoryRowTemplate.specializesA _ _

/-- The derived committed skeleton is literally the F73 committed skeleton. -/
theorem skeletonOfNodes_eq :
    skeletonOfNodes computeNodeTree [dummyHaltNodeTree, memNodeTree] =
      ConcreteStrictPackage.semanticSkeleton := by
  simp [skeletonOfNodes, computeNodeTree, dummyHaltNodeTree, memNodeTree, mapNTree, semanticSkeleton,
    computeNode, dummyHaltNode, readNode, decomposeNode, headNode, verifyNode, tailNode,
    dummyHaltSkeletonTree, readSkeletonTree, decomposeSkeletonTree, headSkeletonTree, verifySkeletonTree,
    tailSkeletonTree]

/-- **The honest commitment of the F73 fixture.** -/
def data73 : Data concreteExecution where
  computeNodes := computeNodeTree
  memoryNodes := [dummyHaltNodeTree, memNodeTree]
  compute_rows := by
    simp [computeNodeTree, computeNode, mapNTree, BuildableConcrete.concreteExecution,
      ConcreteStrictPackage.exec]
  memory_rows := by
    simp [dummyHaltNodeTree, dummyHaltNode, memNodeTree, readNode, decomposeNode, headNode,
      verifyNode, tailNode, mapNTree,
      BuildableConcrete.concreteExecution, ConcreteStrictPackage.execA, dummyHaltTree,
      readTreeA, decomposeTreeA, headTree, verifyTreeA, tailTree]
  computeOK := computeNodeTree_OK
  memoryOK := by
    intro t ht
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with h | h
    · rw [h]; exact dummyHaltNodeTree_OK
    · rw [h]; exact memNodeTree_OK
  root_line_exponent := rfl
  root_line_origin := rfl
  nounSizeBound := 2
  Λ := 2
  slotSemantics := skeletonOfNodes_eq ▸ ConcreteStrictPackage.slotSemantics
  recordEquations := skeletonOfNodes_eq ▸ ConcreteStrictPackage.recordEquations
  census := skeletonOfNodes_eq ▸ ConcreteStrictPackage.census
  sizeWindowBound := skeletonOfNodes_eq ▸ ConcreteStrictPackage.sizeWindowBound
  q_eq_ringChar := ConcreteStrictPackage.q_eq_ringChar
  skeletonBounded := skeletonOfNodes_eq ▸ ConcreteStrictPackage.skeletonBounded
  combinedBounded := skeletonOfNodes_eq ▸ ConcreteStrictPackage.combinedBounded

/-- The committed skeleton this commitment derives is exactly the F73 committed skeleton. -/
theorem data73_skeleton : data73.skeleton = ConcreteStrictPackage.semanticSkeleton :=
  skeletonOfNodes_eq

/-- **A second inhabitant of `CommitmentResidual`, with a constructed committed layer.** -/
def residual73' : BuildablePackage.CommitmentResidual concreteExecution :=
  commitmentResidualOfZero data73

theorem residual73'_nonvacuous :
    Nonempty (BuildablePackage.CommitmentResidual concreteExecution) :=
  ⟨residual73'⟩

theorem residual73'_claim :
    residual73'.verifier.raw.claim.subject = .atom 0 ∧
      residual73'.verifier.raw.claim.formula = .cell (.atom 1) (.atom 2) := by
  show data73.skeleton.computeTree.label.subject = (.atom 0) ∧
    data73.skeleton.computeTree.label.formula = (.cell (.atom 1) (.atom 2))
  simp [Data.skeleton, skeletonOfNodes, mapNTree_label]
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals first | rfl | decide

/-- `generated` at `residual73'`, window `Λ = 2`. -/
theorem residual73'_generated :
    GeneratedField.ClaimGenerated K73cubic residual73'.verifier.raw.claim residual73'.Λ :=
  GeneratedField.claimGenerated_of_eq residual73'_claim.1 residual73'_claim.2
    (OptimizedStrictFullPackage.Concrete.f73_program_generated 2 le_rfl)

/-- The full package over the constructed committed layer.
`hmore` is the remaining Relaxis join at form R (`kMem = 2` dummy halt). -/
def package73' (hmore : BuildableAxisWitness.LaterSeedZeros concreteExecution) :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F73 K73cubic 3 :=
  BuildablePackage.buildFullPackage concreteExecution
    BuildablePackage.Concrete.inputs73zero residual73'
    BuildablePackage.Concrete.inputs73zero_challenges
    BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
    hmore
    BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order BuildablePackage.Concrete.concreteExecution_rowsBound
      residual73'_generated OptimizedStrictFullPackage.Concrete.f73_primeField

/-- **The released fourteen-conjunct statement over a package whose committed half is
constructed.**  This is the first Theorem-5.4 instance in the tree in which no field of the
package is a supplied committed-layer datum other than the post-challenge arrays. -/
theorem statement73'
    (hmore : BuildableAxisWitness.LaterSeedZeros concreteExecution)
    (hax : FormRAxisBound (package73' hmore).optimized.sampled (package73' hmore).optimized.basis)
    (hbasis : FormRBasis (package73' hmore).optimized.basis)
    (hwidth : FormRWidth F73) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (package73' hmore) :=
  BuildablePackage.universalOptimizedFullStrictThm54 concreteExecution
    BuildablePackage.Concrete.inputs73zero residual73'
    BuildablePackage.Concrete.inputs73zero_challenges
    BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
    hmore
    BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order BuildablePackage.Concrete.concreteExecution_rowsBound
      residual73'_generated OptimizedStrictFullPackage.Concrete.f73_primeField
    hax hbasis hwidth

theorem regression73' (hmore : BuildableAxisWitness.LaterSeedZeros concreteExecution) :
    (package73' hmore).objects.cfg = concreteExecution.cfg ∧
      (package73' hmore).objects.exec = concreteExecution.exec ∧
      (package73' hmore).computeChip.rap.w = 303 ∧ (package73' hmore).computeChip.rap.s = 418 ∧
      (package73' hmore).memoryChip.rap.w = 205 ∧ (package73' hmore).memoryChip.rap.s = 156 :=
  ⟨rfl, rfl,
    (BuildablePackage.constructed_resources concreteExecution
      BuildablePackage.Concrete.inputs73zero residual73'
      BuildablePackage.Concrete.inputs73zero_challenges
      BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
      hmore
      BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order BuildablePackage.Concrete.concreteExecution_rowsBound
      residual73'_generated OptimizedStrictFullPackage.Concrete.f73_primeField).1,
    (BuildablePackage.constructed_resources concreteExecution
      BuildablePackage.Concrete.inputs73zero residual73'
      BuildablePackage.Concrete.inputs73zero_challenges
      BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
      hmore
      BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order BuildablePackage.Concrete.concreteExecution_rowsBound
      residual73'_generated OptimizedStrictFullPackage.Concrete.f73_primeField).2.1,
    (BuildablePackage.constructed_resources concreteExecution
      BuildablePackage.Concrete.inputs73zero residual73'
      BuildablePackage.Concrete.inputs73zero_challenges
      BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
      hmore
      BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order BuildablePackage.Concrete.concreteExecution_rowsBound
      residual73'_generated OptimizedStrictFullPackage.Concrete.f73_primeField).2.2.1,
    (BuildablePackage.constructed_resources concreteExecution
      BuildablePackage.Concrete.inputs73zero residual73'
      BuildablePackage.Concrete.inputs73zero_challenges
      BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
      hmore
      BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order BuildablePackage.Concrete.concreteExecution_rowsBound
      residual73'_generated OptimizedStrictFullPackage.Concrete.f73_primeField).2.2.2⟩

end Concrete

end

end HonestCommitment
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.HonestCommitment.bindComputeRow_render
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.renderComputeRow_eq_self
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.bindMemoryRow_render
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.renderMemoryRow_eq_self
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.specialize_placeholder_eq
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.memory_specialize_placeholder_eq
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.computeTemplateBinds
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.memoryTemplateBinds
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.specializeRenderTree
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.specializeRenderMemTree
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.executionTemplate
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.timestampStrategy
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.templateConsistency
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.binds
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.honest_cfg
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.honest_exec
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.honestSeed_ne
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.honest_specialization
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Data.honest_binds
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.derivedRequestIO_length_eq
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.derivedResponseIO_length_eq
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.verifierOf
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.commitmentResidualOf
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.commitmentResidualOfZero
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Concrete.data73
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Concrete.data73_skeleton
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Concrete.residual73'
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Concrete.residual73'_nonvacuous
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Concrete.package73'
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Concrete.statement73'
#print axioms Nock.NockVMROM.Thm54.HonestCommitment.Concrete.regression73'
