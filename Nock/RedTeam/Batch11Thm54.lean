/-
  Nock/RedTeam/Batch11Thm54.lean

HYGIENE: no `sorry`, `admit`, `native_decide`, `stop`, `axiom`, or `@[extern]`.  All generic
  proof-carrying declarations here are ⊆ {propext, Classical.choice, Quot.sound}.  Non-vacuity is
  audited over the AXIOM-CLEAN finite prime field `ZMod 7` (`Fact (Nat.Prime 7)` via `norm_num`) —
  which needs NO `goldilocks_prime` — and ALSO over the paper's concrete Goldilocks/extension field
  `Nock.Field.{Fp, K}`, where pulling `Nock.Field.goldilocks_prime` is expected and ALLOWED for the
  concrete-field witness.

  HEADLINE VERDICT (see `batch11_summary` at the bottom for full detail):
  * Axioms/`sorryAx` (checklist 1)                : PASS — bundle + all 8 instances kernel-clean.
  * Vacuity S1/S2/S3/S5/S6/S7/S8 (checklist 2)     : PASS — instances supply genuine predicates.
  * Vacuity S4 `IsTraversable` (checklist 2/4)     : FIXED — the class now takes
        `[UniqueMemoryExecutionSeparable ι M]` and carries recognition fields that reference the
        VM's `computeAccepts`/`memoryAccepts` (sound inclusion `L_RVT ⊆ L_comp/L_mem` + a
        VM-accepted recognised-leaf witness). The completeness half `L_comp ⊆ L_RVT` (inverse-BFS forest
        reconstruction) is now PROVEN too — the class carries `recognized_complete_compute`/
        `recognized_complete_memory` (discharged via `Walk.reconForest`), so S4 is a GENUINELY
        BIDIRECTIONAL recognition.
  * hcorrect / hidden hyps (checklist 3)           : PASS — `nock_uniqueMES.correct` proved from
        the recognizer (no `hcorrect`); S2 WF is honest (injective nodes, shared chal, per-row WF,
        z≠0), not circular.
  * Disclosure accuracy (checklist 4)              : MOSTLY PASS — one internal inconsistency (S4,
        above); plus S2's stored `Rprog`/`Rmem` are trivial decorations (disclosed in-module only).
  * `paper_NockVMROM_cost_mismatch` (checklist 5)  : PASS — axiom-free; genuinely refutes D1
        (paper 73=73 vs reified 1<13), modulo the disclosed hand-transcription of `paperNockCost`.
-/
import Nock.NockVMROM.Capstone
import Nock.Field
import Nock.RedTeam.Batch5Tables
import Mathlib.Tactic.NormNum.Prime

open scoped Classical

namespace Nock.RedTeam

open Nock Nock.Framework Nock.NockVMROM

/-- Axiom-clean primality fact for the small finite prime field used as the axiom-clean concrete
    witness.  Explicitly named to avoid collisions with other batches (`Nat.Prime 7` via `norm_num`;
    NO `goldilocks_prime`). -/
instance fact_prime_7_b11 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

local instance : CharP (ZMod 7) (ringChar (ZMod 7)) := ringChar.charP (ZMod 7)

/-- `NeZero 1` for the `Ksz := 1` instantiation (the language is empty at `Ksz = 0`). -/
instance neZero_one_b11 : NeZero (1 : ℕ) := ⟨by decide⟩

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## Checklist 1 — `#print axioms`: bundle + the 8 component instances (+ cost certs)
    Each MUST be exactly `[propext, Classical.choice, Quot.sound]` (or fewer).  FLAG any `sorryAx`.
    ══════════════════════════════════════════════════════════════════════════════════════ -/

-- The re-pointed structural bundle (`«Thm:NockVMROM»` target):
#print axioms NockVMROM_Thm54_structural
-- The 8 component instances named in the adversarial checklist:
#print axioms nock_uniqueMES                -- S1
#print axioms nock_hasCanonicalRAP          -- S2
#print axioms nock_opcodeMemoryOneHot       -- S3
#print axioms nock_traversalModel           -- S4 (data)
#print axioms nock_isTraversable            -- S4 (property)
#print axioms nock_hasTwoRAPVerification     -- S5
#print axioms nock_hasPerfectCompleteness    -- S6
#print axioms nock_hasConcreteSoundness      -- S7
#print axioms nock_hasCostModel              -- S8
-- The supporting whole-trace bridges (S2 crux) + cost certificates:
#print axioms Nock.Reified.computeTable_reified_iff
#print axioms Nock.Reified.memoryTable_reified_iff
#print axioms paper_NockVMROM_cost_mismatch  -- must be axiom-free
#print axioms nockVMROM_Thm54_corrected      -- must be axiom-free

/-- **[1.cite]** Naming the bundle exhibits its full `VerifiableVMCompilation` type (S1–S8 stored),
    NOT a `Prop`/`True` placeholder. -/
@[reducible] noncomputable def bundle_cite := @NockVMROM_Thm54_structural
@[reducible] noncomputable def uniqueMES_cite := @nock_uniqueMES
@[reducible] noncomputable def canonicalRAP_cite := @nock_hasCanonicalRAP
@[reducible] noncomputable def oneHot_cite := @nock_opcodeMemoryOneHot
@[reducible] noncomputable def traversalModel_cite := @nock_traversalModel
@[reducible] noncomputable def isTraversable_cite := @nock_isTraversable
@[reducible] noncomputable def twoRAP_cite := @nock_hasTwoRAPVerification
@[reducible] noncomputable def complete_cite := @nock_hasPerfectCompleteness
@[reducible] noncomputable def concreteSound_cite := @nock_hasConcreteSoundness
@[reducible] noncomputable def costed_cite := @nock_hasCostModel

def checklist1_doc : String :=
  "CHECKLIST 1 (sorryAx/axioms): PASS. `#print axioms` (build log) reports EXACTLY " ++
  "[propext, Classical.choice, Quot.sound] for: NockVMROM_Thm54_structural, and all 8 instances " ++
  "nock_uniqueMES / nock_hasCanonicalRAP / nock_opcodeMemoryOneHot / nock_traversalModel / " ++
  "nock_isTraversable / nock_hasTwoRAPVerification / nock_hasPerfectCompleteness / " ++
  "nock_hasConcreteSoundness / nock_hasCostModel, plus the S2 bridges computeTable_reified_iff / " ++
  "memoryTable_reified_iff.  paper_NockVMROM_cost_mismatch and nockVMROM_Thm54_corrected are " ++
  "AXIOM-FREE.  NO sorryAx anywhere.  Disposition: PASSED."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## Checklist 2 — Vacuity probes
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-! ### S5 `HasTwoRAPVerification.shared_io` — is `rapIOAccepts` genuine or `fun _ => True`? -/

/-- **[2.S5.a] `rapIOAccepts` is the genuine `IO.LmIO`, not `fun _ => True`.**  DISCRIMINATION: the
    empty request/response pair is REJECTED at `Ksz = 2` (`IO.LmIO` forces `1 ≤ |requests|`), so the
    acceptance relation is a real, discriminating predicate. -/
theorem b11_shared_io_not_true :
    ¬ (nockTwoRAPModel (ZMod 7) (ZMod 7) 0 1 2).rapIOAccepts ([], []) := by
  intro h
  have h2 : IO.LmIO 2 ([] : List ((nmrMEF (ZMod 7) (ZMod 7)).Rec)) [] := h
  rw [IO.LmIO_iff] at h2
  exact absurd h2.1.1 (by decide)

/-- **[2.S5.b] …and it is genuinely INHABITED** (the instance's non-vacuity obligation): a single
    self-matched zero record lies in `L_mIO` at `Ksz = 1`.  So `shared_io` is a real `∃`, discharged
    with real content — never `True`, never a trivial `bound := badProbability`. -/
theorem b11_shared_io_inhabited :
    ∃ w, (nockTwoRAPModel (ZMod 7) (ZMod 7) 0 1 1).rapIOAccepts w :=
  (nock_hasTwoRAPVerification (ZMod 7) (ZMod 7) 0 1 (le_refl 1)).shared_io

/-! ### S7 `HasConcreteSoundness` — is `bound` the real Schwartz–Zippel RHS, or `:= badProbability`? -/

/-- **[2.S7.a] `bound` is the real Schwartz–Zippel RHS, definitionally DISTINCT from
    `badProbability`.**  The S7 model's `bound` unfolds to the composite `(h/|K| + h(node_size-1)/|K|)`
    summed over the compute + memory-forest walks, while `badProbability` unfolds to the composite
    card ratio `walkBad.card/|K|² + walkBadForest.card/|K|²`.  These are different `def`s applied to
    the trial's `h`/`node_size` vs its `walkBad` set — so `bound` is NOT the degenerate
    `bound := badProbability`.  Both equalities hold by `rfl`, pinning each to its real quantity. -/
theorem b11_bound_is_real_rhs (F K : Type) [Field F] [Field K] [Fintype K] [DecidableEq K]
    (α β : K) (Ksz : ℕ) (t : ComputeWalkTrial K × ForestWalkTrial K) :
    (nockConcreteSoundness F K α β Ksz).bound t
      = computeWalkBound t.1 + forestWalkBound t.2 ∧
    (nockConcreteSoundness F K α β Ksz).badProbability t
      = computeWalkBadProb t.1 + forestWalkBadProb t.2 :=
  ⟨rfl, rfl⟩

def checklist2_S567_doc : String :=
  "CHECKLIST 2 (S5/S6/S7 vacuity): PASS. " ++
  "S5 shared_io: rapIOAccepts w := IO.LmIO Ksz w.1 w.2 — GENUINE (b11_shared_io_not_true rejects " ++
  "([],[]); b11_shared_io_inhabited exhibits a real inhabitant). NOT `fun _ => True`. " ++
  "S6 complete: accepted p := ∀k, Vcomp (real fold), hasSatisfyingAssignment p := ∃ex, " ++
  "airToRAP(computeAIR)…Satisfies (real reified RAP); `complete` = (.mp of computeTable_reified_iff) " ++
  "— GENUINE forward direction of a real iff, not True. " ++
  "S7 sound: bound t := computeWalkBound+forestWalkBound = (h/|K| + h(node_size-1)/|K|) summed — the " ++
  "REAL Schwartz–Zippel RHS, NOT `bound := badProbability` (badProbability = walkBad.card/|K|²). " ++
  "sound = add_le_add(walkBad_prob, walkBadForest_prob), the two REAL operational theorems. PASSED."

/-! ### S4 `IsTraversable` — vacuity now FIXED (genuine VM-referencing recognition) -/

/-- **[2.S4.FIXED] The Batch-11 S4 vacuity is CLOSED: `IsTraversable` now carries genuine
    VM-specific recognition content, and `b11_isTraversable_is_vacuous` is NO LONGER provable.**

    The class now takes `[S : UniqueMemoryExecutionSeparable ι M]` and adds four recognition fields
    referencing the VM's ACTUAL sub-verifiers `S.computeAccepts`/`S.memoryAccepts`:
    `recognizes_compute`/`recognizes_memory` (the sound inclusion `L_RVT^{F_i,n} ⊆ L_comp`/`L_mem`)
    and `compute_recognized`/`memory_recognized` (a VM-accepted `F_i`-recognised leaf witness).

    Hence the class does NOT hold for an arbitrary `VMSystem`.

    Below we cite that the recognition GENUINELY fires on the Nock instance: `recognizes_compute`
    entails Nock's own `V_comp` (via `computeAccepts`) on every `Fcomp`-recognised label, and
    `compute_recognized` exhibits a concrete `V_comp`-accepted leaf. -/
@[reducible] noncomputable def b11_isTraversable_recognizes_compute_cite
    (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :=
  (nock_isTraversable F K α β Ksz).recognizes_compute
@[reducible] noncomputable def b11_isTraversable_recognizes_memory_cite
    (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :=
  (nock_isTraversable F K α β Ksz).recognizes_memory
@[reducible] noncomputable def b11_isTraversable_compute_recognized_cite
    (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :=
  (nock_isTraversable F K α β Ksz).compute_recognized
@[reducible] noncomputable def b11_isTraversable_memory_recognized_cite
    (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :=
  (nock_isTraversable F K α β Ksz).memory_recognized

/-- **[2.S4.COMPLETE] The completeness half `L_comp ⊆ L_RVT` is now PROVEN — closing the former
    Track-7 gap.**  `IsTraversable` now also carries the reverse-inclusion fields
    `recognized_complete_compute`/`recognized_complete_memory`: every walk-structured accepting
    execution reconstructs (via the inverse-BFS `Walk.reconForest`) to a forest of
    `RVTWithArity (Fcomp/Fmem)` trees whose aggregate BFS labels are the execution rows.  Cited on
    the Nock instance below; discharged by `nockvmrom_compute_complete`/`nockvmrom_memory_complete`
    (pure ASSEMBLY of `Walk.reconForest_RVT`/`reconForest_properArity`/`reconForest_labels`).  With
    the sound inclusion (`recognizes_compute`/`recognizes_memory`) this makes S4 a GENUINELY
    BIDIRECTIONAL recognition `L ≡ L_RVT`. -/
@[reducible] noncomputable def b11_isTraversable_complete_compute_cite
    (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :=
  (nock_isTraversable F K α β Ksz).recognized_complete_compute
@[reducible] noncomputable def b11_isTraversable_complete_memory_cite
    (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :=
  (nock_isTraversable F K α β Ksz).recognized_complete_memory
/-- The standalone reverse-inclusion theorems the completeness fields are discharged by. -/
@[reducible] noncomputable def b11_nockvmrom_compute_complete_cite := @nockvmrom_compute_complete
@[reducible] noncomputable def b11_nockvmrom_memory_complete_cite := @nockvmrom_memory_complete

/-!

    Those four fields are removed at the class level;
    the S4 content is now EXACTLY the two VM-referencing inclusions — sound (`recognizes_*`, cited
    above) + complete (`recognized_complete_*`, cited above). Consequently the old
    `b11_nock_phi_is_refl` witness is REMOVED (there is no `φ` field to be `Equiv.refl`), and the
    non-vacuity rests SOLELY on the recognition fields, which reference the VM's
    `S.computeAccepts`/`S.memoryAccepts`. -/

def checklist2_S4_doc : String :=
  "CHECKLIST 2/4 (S4 IsTraversable vacuity): FIXED (was FAIL/disclosed-vacuous). " ++
  "IsTraversable now takes [S : UniqueMemoryExecutionSeparable ι M] and adds recognition fields " ++
  "(recognizes_compute/recognizes_memory + compute_recognized/memory_recognized) that reference " ++
  "the VM's ACTUAL sub-verifiers S.computeAccepts/S.memoryAccepts. The old uniform vacuity term " ++
  "(ComputeLang := RVTWithArity product, φ := Equiv.refl, no VM reference) NO LONGER TYPECHECKS — " ++
  "it cannot supply the recognition fields for an arbitrary VMSystem (they fail when the sub-verifier " ++
  "rejects everything or F_i recognises an empty tree language). So the class does NOT hold for an " ++
  "arbitrary VMSystem: b11_isTraversable_is_vacuous is REMOVED (no longer provable). The Nock " ++
  "instance discharges the recognition genuinely: Fcomp/Fmem embed Vcomp/Vmem, so recognizes_compute/ " ++
  "recognizes_memory prove the sound inclusion L_RVT ⊆ L_comp/L_mem, and compute_recognized/ " ++
  "memory_recognized exhibit a V_comp/V_mem-accepted Fcomp/Fmem-recognised leaf (cited: " ++
  "b11_isTraversable_recognizes_compute_cite etc.). UPDATE (φ residual RETIRED): the class no longer carries " ++
  "the ComputeLang/MemoryLang/φcomp/φmem fields (they were an Equiv.refl over a self-chosen Type, satisfiable " ++
  "by any VM); those four free fields are REMOVED, so b11_nock_phi_is_refl is gone and S4 rests on NO free-field " ++
  "Equiv.refl. UPDATE (completeness PROVEN): IsTraversable carries recognized_complete_compute/" ++
  "recognized_complete_memory — the reverse inclusion L_comp/L_mem ⊆ L_RVT via the inverse-BFS Walk.reconForest " ++
  "(discharged by nockvmrom_compute_complete/nockvmrom_memory_complete = assembly of reconForest_RVT/" ++
  "reconForest_properArity/reconForest_labels; cited b11_isTraversable_complete_compute_cite etc.). The former " ++
  "Track-7 gap is CLOSED. VERDICT: S4 is now GENUINELY NON-VACUOUS and BIDIRECTIONAL (sound inclusion + " ++
  "completeness), with the recognition content living entirely in the two VM-referencing inclusion fields and " ++
  "NO free-field Equiv.refl residual remaining."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## Checklist 3 — hidden assumptions / hcorrect
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- **[3.a] S1 `nock_uniqueMES.correct` is proved FROM the recognizer (no carried `hcorrect`).**  We
    re-derive the separation biconditional independently at a concrete field, exercising exactly the
    `language_unfold`-based `correct` field — it fires in both directions, so it is a genuine proof,
    not a delegated `hcorrect` hypothesis. -/
theorem b11_uniqueMES_correct_fires (x : Stmt (ZMod 7) (ZMod 7)) :
    Language (Tag (ZMod 7) (ZMod 7) 0 1 1) x ↔
      ∃ (w : Wit (ZMod 7) (ZMod 7)) (ioP ioM : List ((nmrMEF (ZMod 7) (ZMod 7)).Rec)),
        (ComputeTableAccepts x.compute w.computeDec ∧ ioP = w.progIO) ∧
        (MemoryTableAccepts x.memory ∧ ioM = w.memIO) ∧
        IO.LmIO 1 ioP ioM :=
  (nock_uniqueMES (ZMod 7) (ZMod 7) 0 1 1).correct x

def checklist3_doc : String :=
  "CHECKLIST 3 (hidden assumptions / hcorrect): PASS. " ++
  "S1: nock_uniqueMES.correct is proved by `rw [language_unfold]` + product destructuring (see " ++
  "Separation.lean:56-64) — NO hcorrect, NO abstract LangVM. computeAccepts/memoryAccepts are the " ++
  "REAL ComputeTableAccepts/MemoryTableAccepts folds; b11_uniqueMES_correct_fires exercises both " ++
  "directions. (Honest caveat: the separation is definitional — L_NockVMROM was BUILT as the " ++
  "separable conjunction CTA∧MTA∧LmIO — which is honest given it is the assembled recognizer.) " ++
  "S2 WF: ComputeProblem/MemProblem bundle ONLY honest well-formedness — hnodes (Injective nodes, " ++
  "needs |K|≥#rows), hchal (shared challenge vector), hwf (per-row RLC-nondegeneracy WF), hz (z≠0). " ++
  "NONE assume the conclusion (Vcomp/Satisfies), so no smuggled circularity. compute_iff/memory_iff " ++
  "= the real bridges computeTable_reified_iff/memoryTable_reified_iff applied field-by-field. PASSED."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## Checklist 4 — disclosure accuracy (see also S4 finding above)
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- **[4.a] S2 stored `Rprog`/`Rmem` are TRIVIAL decorations, not the load-bearing RAPs.**  The
    class stores `Rprog := airToRAP computeAIR 0 0 1 1 ∅ …` (empty domain, unit params), which
    is NOT the RAP whose satisfaction `progSatisfiable`/`compute_iff` actually use (those reify at
    each problem's OWN `eDeg/hExp/ω/β` over `Finset.image p.nodes univ`).  Disclosed in
    `CanonicalRAP.lean` ("Rprog/Rmem … at trivial parameters; the load-bearing content is the
    per-problem satisfiability predicate, not these").  We confirm the stored `Rprog` is the empty-
    domain reification (its constraint domain is `∅`). -/
theorem b11_stored_Rprog_trivial (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    (HasCanonicalRAP.Rprog (ι := Tag F K α β Ksz) (M := nmrMEF F K) (F := K)).e = 1 ∧
    (HasCanonicalRAP.Rprog (ι := Tag F K α β Ksz) (M := nmrMEF F K) (F := K)).h = 1 :=
  ⟨rfl, rfl⟩

def checklist4_doc : String :=
  "CHECKLIST 4 (disclosure accuracy): MOSTLY PASS, with the S4 inconsistency (see checklist2_S4_doc). " ++
  "S1 nmrMEF-vs-field-NMR: disclosed 1-1* (SC18); code proves over nmrMEF, nmrEncoding bridges " ++
  "k↦β^k bounded-injective — ACCURATE. " ++
  "S3 cons/cond-4b: disclosed 1-1* (SC9/SC13); instance has separate structuralSelector (cons) + 10 " ++
  "numeric, and record_pos makes cond-4b's io_zero antecedent vacuous BY DESIGN — ACCURATE. " ++
  "S2 w_RAP: disclosed 1-1* (SC17); the HasCanonicalRAP class shares NEITHER columns NOR RAP params " ++
  "(unlike the CanonicalRAP struct — no common_e/h/d/ω/β), and its stored Rprog/Rmem are " ++
  "trivial-parameter decorations (b11_stored_Rprog_trivial: e=1,h=1) — disclosed IN-MODULE, but NOT in " ++
  "SPEC-FREEZE §A; recommend surfacing. The load-bearing content is genuinely the per-problem " ++
  "compute_iff/memory_iff (the real bridges). " ++
  "S4 recognition: FIXED + COMPLETED + φ-RESIDUAL RETIRED — IsTraversable references the VM's " ++
  "computeAccepts/memoryAccepts via recognition fields (sound inclusion L_RVT ⊆ L_comp/L_mem + VM-accepted " ++
  "recognised-leaf witness) AND carries recognized_complete_compute/recognized_complete_memory (reverse " ++
  "inclusion L_comp/L_mem ⊆ L_RVT via inverse-BFS Walk.reconForest); b11_isTraversable_is_vacuous is REMOVED " ++
  "(no longer provable). The ComputeLang/MemoryLang/φcomp/φmem free fields are now REMOVED from the class, so " ++
  "S4 rests on NO free-field Equiv.refl. Completeness half (L_comp ⊆ L_RVT) PROVEN — former Track-7 gap " ++
  "CLOSED; S4 recognition is genuinely bidirectional. " ++
  "asymptotic-S7 + absolute costs: the bundle uses FIXED-field S7 (HasConcreteSoundness) only; " ++
  "asymptotic is a SEPARATE companion (HasAsymptoticSoundness), NOT bundled; absolute costs refuted " ++
  "via mismatch cert — ACCURATE (no overclaim: the bundle does not assert the asymptotic/absolute " ++
  "paper wording)."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## Checklist 5 — `paper_NockVMROM_cost_mismatch`: axiom-free + genuine refutation (not tautology)
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- **[5.a] The mismatch certificate, re-cited.**  Paper claims equal degree-4 gate counts
    (`73 = 73`), reified reality has memory strictly fewer (`1 < 13`), and columns disagree
    (`94 ≠ 184`).  This is the actual D1 inconsistency — paper-EQUAL vs reified-UNEQUAL — not a
    vacuous `73 = 73` tautology. -/
theorem b11_cost_mismatch_cite :
    (paperNockCost.compDeg4 = paperNockCost.memDeg4) ∧
    (reifiedNockCost.memDeg4 < reifiedNockCost.compDeg4) ∧
    (reifiedNockCost.compCols ≠ paperNockCost.compCols) :=
  paper_NockVMROM_cost_mismatch

/-- **[5.b] The reified figures are TIED to the real AIR (`reifiedNockCost_faithful`)** — so the
    refutation rests on machine-checked reality on the reified side (the paper side is disclosed
    hand-transcription; there is intentionally no theorem equating `paperNockCost` to the PDF). -/
theorem b11_reified_faithful_cite {K : Type*} [Field K] :
    reifiedNockCost.compCols = Nock.Reified.computeAIR.numTraceCols ∧
    reifiedNockCost.memCols = (Nock.Reified.memoryAIR (K := K)).numTraceCols :=
  ⟨(reifiedNockCost_faithful (K := K)).1, (reifiedNockCost_faithful (K := K)).2.2.2.2.1⟩

def checklist5_doc : String :=
  "CHECKLIST 5 (paper_NockVMROM_cost_mismatch): PASS. AXIOM-FREE (build log: 'does not depend on " ++
  "any axioms'). Genuinely refutes D1: paperNockCost.compDeg4 = paperNockCost.memDeg4 (73=73, the " ++
  "paper's equal-claim) is combined with reifiedNockCost.memDeg4 < compDeg4 (1<13, reified reality) " ++
  "and compCols ≠ (94≠184) — the paper-EQUAL/reified-UNEQUAL contradiction, NOT a vacuous 73=73 " ++
  "tautology. The reified side is TIED to the real computeAIR/memoryAIR counts via " ++
  "reifiedNockCost_faithful (b11_reified_faithful_cite). CAVEAT (disclosed): paperNockCost is " ++
  "hand-transcribed (no theorem ties it to the PDF), so the refutation is sound MODULO faithful " ++
  "transcription — this is intentional and documented (SC12/CENSUS §D). PASSED."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## Gate E — CONCRETE NON-VACUITY WITNESS (the bundle is inhabited at real finite fields)
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- **[E.1] AXIOM-CLEAN non-vacuity witness.**  The full S1–S8 structural bundle is inhabited over
    the axiom-clean finite prime field `ZMod 7` at `α = 0, β = 1, Ksz = 1` (`NeZero 1`).  This
    type-checks ⇒ the bundle is NOT vacuous.  Pulls only `[propext, Classical.choice, Quot.sound]`
    — NOT even `goldilocks_prime`. -/
@[reducible] noncomputable def b11_bundle_witness_zmod7 :
    VerifiableVMCompilation (Tag (ZMod 7) (ZMod 7) 0 1 1) (nmrMEF (ZMod 7) (ZMod 7)) (ZMod 7) 10 3
      (Nock.NockVMROM.Thm54.ProductionP8Containment.ExactProductionFixedFieldSoundness
        (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.ProductionP8Containment.exactProductionFixedFieldSoundness
        (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.ExactSegmentedCostVerification (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.exactSegmentedCostVerification (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.ExactChainedHasPerfectCompleteness (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.exactChainedHasPerfectCompleteness (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.ExactTwoRAPVerification (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.exactTwoRAPVerification (ZMod 7) (ZMod 7))
      (nock_uniqueMES (ZMod 7) (ZMod 7) 0 1 1)
      (Nock.NockVMROM.Thm54.ExactChainedHasCanonicalRAP2 (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.exactChainedHasCanonicalRAP2 (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.ExactChainedOneHot (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.exactChainedOneHot (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.ExactDefTraversable (ZMod 7) (ZMod 7))
      (Nock.NockVMROM.Thm54.exactDefTraversable (ZMod 7) (ZMod 7))
      (nock_languageInhabited (ZMod 7) (ZMod 7) 0 1 1) :=
  NockVMROM_Thm54_structural (ZMod 7) (ZMod 7) 0 1 1

/-- **[E.2] PAPER-FIELD non-vacuity witness.**  The bundle is ALSO inhabited over the paper's actual
    Goldilocks base field `𝔽 = 𝔽_p` and cubic extension `K = GaloisField p 3` at
    `α = 0, β = 1, Ksz = 1`.  This is the intended concrete field; per §G it is EXPECTED to pull
    `Nock.Field.goldilocks_prime` (the ONLY extra axiom, whitelisted for the concrete witness). -/
@[reducible] noncomputable def b11_bundle_witness_goldilocks :=
  NockVMROM_Thm54_structural Nock.Field.Fp Nock.Field.K (0 : Nock.Field.K) (1 : Nock.Field.K) 1

/-- The current bundle instead
consumes `ExactSegmentedCostVerification`; this theorem is retained as a control, not a bundle
projection. -/
theorem b11_bundle_costed_real :
    reifiedNockCost.memDeg4 < reifiedNockCost.compDeg4 :=
  (nock_hasCostModel (ZMod 7) (ZMod 7) 0 1 1).memory_fewer_deg4

/-- **[E.4] `language_nonempty` cite** — at `Ksz ≥ 1` the NockVMROM language is genuinely inhabited
    (a self-matched record witnesses the empty-table statement). -/
theorem b11_language_nonempty_cite (F K : Type) [Field F] [Field K] (α β : K) {Ksz : ℕ}
    (hK : 1 ≤ Ksz) (r : (nmrMEF F K).Rec) :
    Language (Tag F K α β Ksz) (⟨[], []⟩ : Stmt F K) :=
  language_nonempty F K α β hK r

/-- **[E.5] Concrete language inhabitant at `ZMod 7`, `Ksz = 1`** — a fully explicit member,
    confirming the recognizer is satisfiable (not vacuously false). -/
theorem b11_language_inhabited_zmod7 :
    Language (Tag (ZMod 7) (ZMod 7) 0 1 1) (⟨[], []⟩ : Stmt (ZMod 7) (ZMod 7)) :=
  language_nonempty (ZMod 7) (ZMod 7) 0 1 (le_refl 1)
    (((0 : ZMod 7), ((0, 0, 0), (0, 0, 0)), 0) : (nmrMEF (ZMod 7) (ZMod 7)).Rec)

/-- **[E.6] Discrimination: at `Ksz = 0` the language is EMPTY** (`L_mIO` forces `1 ≤ 0`), so the
    recognizer is genuinely discriminating, not vacuously-true. -/
theorem b11_language_empty_Ksz0 (x : Stmt (ZMod 7) (ZMod 7)) :
    ¬ Language (Tag (ZMod 7) (ZMod 7) 0 1 0) x :=
  not_language_Ksz_zero (ZMod 7) (ZMod 7) 0 1 x

def gateE_doc : String :=
  "GATE E (non-vacuity witness): PASSED. b11_bundle_witness_zmod7 : the FULL S1–S8 " ++
  "VerifiableVMCompilation bundle is inhabited over the AXIOM-CLEAN field ZMod 7 (α=0,β=1,Ksz=1, " ++
  "NeZero 1) — pulls ONLY [propext, Classical.choice, Quot.sound], NOT goldilocks_prime. " ++
  "b11_bundle_witness_goldilocks : the bundle is ALSO inhabited over the paper's Goldilocks 𝔽_p + " ++
  "cubic extension K = GaloisField p 3 — this pulls Nock.Field.goldilocks_prime (EXPECTED/ALLOWED " ++
  "per §G). language_nonempty is cited (b11_language_nonempty_cite) and instantiated concretely at " ++
  "ZMod 7 (b11_language_inhabited_zmod7), with the Ksz=0 emptiness discrimination " ++
  "(b11_language_empty_Ksz0). The bundle consumes exact six-AIR segmented cost verification; " ++
  "the old reified model remains only as b11_bundle_costed_real diagnostic evidence. " ++
  "GATE E.4 (see gateE4_doc): the Category-2 'honest WF' residual is CLOSED — the S2 WF-carrying " ++
  "ComputeProblem/MemProblem structures are inhabited by a REAL accepting trace (s0 compute row + " ++
  "halt memory row) over ZMod 7 with every WF field genuinely discharged (injective nodes on Fin 1, " ++
  "shared chal by rfl, per-row WF holds since s0/halt don't trigger rlc5/size8/size11/pole_ne, " ++
  "z=1≠0), and the compute_iff/memory_iff bridges FIRE (progSatisfiable/memSatisfiable DERIVED via " ++
  ".mp of computeTable_reified_iff/memoryTable_reified_iff) — so the honest WF is non-vacuously " ++
  "satisfiable, not a hidden vacuity."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## Gate E.4 — CONCRETE-RUN WF WITNESS (the S2 problem structures are inhabited by a REAL trace)
    ══════════════════════════════════════════════════════════════════════════════════════

    Closes the Category-2 "honest WF" residual.  The S2 `HasCanonicalRAP` instance
    (`nock_hasCanonicalRAP`) is unconditional over the problem structures
    `ComputeProblem`/`MemProblem`, but those structures CARRY the disclosed well-formedness as
    fields (`hnodes`, `hβ`, `hh1`, `hchal`, `hwf`, `hz`).  The open question — "are those WF jointly
    satisfiable by a REAL accepting Nock trace?" — is answered YES here, over the AXIOM-CLEAN field
    `ZMod 7`, by exhibiting a concrete accepting-trace witness that inhabits BOTH structures with
    EVERY WF field genuinely discharged, and then FIRING the `compute_iff`/`memory_iff` bridges on a
    real accepting row (deriving `progSatisfiable`/`memSatisfiable`, not restating them).

    The witness reuses the Batch-5 accepting rows: the `s0` compute row
    (`vcomp_positive_witness`, `z = 1`) and the `halt` memory row (`vmem_positive_witness`,
    `z = 1`).  Each WF field is discharged HONESTLY:
    * `hnodes` — `nodes := fun _ => 0` is injective on `Fin 1` (subsingleton domain);
    * `hchal`  — the shared challenge vector IS the row's own `computeEnvFull … .chal` (`rfl`);
    * `hwf`    — per-row `WF` holds because `s0`/`halt` do NOT trigger the conditional
                 non-degeneracy branches (`rlc5`/`size8`/`size11` for compute, `pole_ne` for
                 memory) — every antecedent (`state = s5/s8/cons`, `st = read_root/verify_child`)
                 is decidably false;
    * `hz`     — `z = 1 ≠ 0`;  `hβ` — `β = 1 ≠ 0`;  `hh1` — `1 ≤ 1`.

    HONESTY NOTE: this witness discharges the WF because the `s0`/`halt` row does not exercise the
    conditional non-degeneracy antecedents; a richer trace hitting `s5`/`s8`/`cons`/`read_root`
    would ADDITIONALLY witness those branches (a richer future witness, not required for
    non-vacuity).  What is established here is exactly what the residual asked: the WF-carrying S2
    problem structures are NON-VACUOUSLY inhabited by a real accepting run, and the S2 bridges fire
    on it — so the "honest WF" is a real, satisfiable side-condition, not a hidden vacuity. -/

/-- **[E.4.1] Concrete `ComputeProblem` witness over `ZMod 7`** (`n = 1`): the `s0` accepting
    compute row (`vcomp_positive_*`, `z = 1`), with every S2 well-formedness field genuinely
    discharged (injective `nodes` on `Fin 1`, shared `chal` by `rfl`, per-row `WF` since `s0` fires
    none of `rlc5`/`size8`/`size11`, `z = 1 ≠ 0`, `β = 1 ≠ 0`, `1 ≤ 1`). -/
noncomputable def b11_computeProblem_witness : Nock.NockVMROM.ComputeProblem (ZMod 7) where
  n := 1
  inp := fun _ => vcomp_positive_inp
  pub := fun _ => vcomp_positive_pub
  dec := fun _ => vcomp_positive_dec
  nodes := fun _ => 0
  chalVal := (Nock.Reified.computeEnvFull vcomp_positive_inp
    (ComputeTable.opSel vcomp_positive_pub.state) vcomp_positive_pub vcomp_positive_dec ⟨0, 0⟩).chal
  eDeg := 1
  hExp := 1
  ω := 1
  β := 1
  hnodes := fun a b _ => Subsingleton.elim a b
  hβ := one_ne_zero
  hh1 := le_refl 1
  hchal := fun _ => rfl
  hwf := fun _ =>
    { rlc5 := fun h _ => absurd h (by decide)
      size8 := fun h => absurd h (by decide)
      size11 := fun h => absurd h (by decide) }
  hz := fun _ => one_ne_zero

/-- **[E.4.2] The compute witness is ACCEPTED.**  `progAccepts` (the per-row algorithmic `Vcomp`
    fold) fires on the real `s0` row via `vcomp_positive_witness`. -/
theorem b11_computeProblem_accepts :
    (nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).progAccepts b11_computeProblem_witness :=
  fun _ => vcomp_positive_witness

/-- **[E.4.3] THE PAYOFF — the S2 compute bridge FIRES.**  Applying `HasCanonicalRAP.compute_iff`
    (which is literally `computeTable_reified_iff` field-by-field) to real acceptance yields a
    SATISFIABLE reified `computeAIR` RAP (`progSatisfiable`), UNCONDITIONALLY over `ZMod 7`.  This
    is genuinely derived (`.mp` of the bridge on `b11_computeProblem_accepts`), not restated. -/
theorem b11_computeProblem_satisfiable :
    (nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).progSatisfiable b11_computeProblem_witness :=
  ((nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).compute_iff b11_computeProblem_witness).mp
    b11_computeProblem_accepts

/-- **[E.4.4] Concrete `MemProblem` witness over `ZMod 7`** (`n = 1`): the `halt` accepting memory
    row (`vmem_positive_*`, `z = 1`), with every S2 well-formedness field genuinely discharged
    (injective `nodes` on `Fin 1`, shared `chal` by `rfl`, per-row `WF` since `halt` fires none of
    the `pole_ne` antecedent, `z = 1 ≠ 0`, `β = 1 ≠ 0`, `1 ≤ 1`). -/
noncomputable def b11_memProblem_witness : Nock.NockVMROM.MemProblem (ZMod 7) where
  n := 1
  minp := fun _ => vmem_positive_inp
  mrow := fun _ => vmem_positive_pub
  nodes := fun _ => 0
  chalVal := (Nock.Reified.memoryEnvFull vmem_positive_inp
    (MemoryTable.opSel vmem_positive_pub.st) vmem_positive_pub 0).chal
  eDeg := 1
  hExp := 1
  ω := 1
  β := 1
  hnodes := fun a b _ => Subsingleton.elim a b
  hβ := one_ne_zero
  hh1 := le_refl 1
  hchal := fun _ => rfl
  hwf := fun _ => { pole_ne := fun h => absurd h (by decide) }
  hz := fun _ => one_ne_zero

/-- **[E.4.5] The memory witness is ACCEPTED.**  `memAccepts` (the per-row algorithmic `Vmem` fold)
    fires on the real `halt` row via `vmem_positive_witness`. -/
theorem b11_memProblem_accepts :
    (nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).memAccepts b11_memProblem_witness :=
  fun _ => vmem_positive_witness

/-- **[E.4.6] THE PAYOFF — the S2 memory bridge FIRES.**  Applying `HasCanonicalRAP.memory_iff`
    (literally `memoryTable_reified_iff` field-by-field) to real acceptance yields a SATISFIABLE
    reified `memoryAIR` RAP (`memSatisfiable`), UNCONDITIONALLY over `ZMod 7`.  Genuinely derived
    (`.mp` of the bridge on `b11_memProblem_accepts`), not restated. -/
theorem b11_memProblem_satisfiable :
    (nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).memSatisfiable b11_memProblem_witness :=
  ((nock_hasCanonicalRAP (ZMod 7) (ZMod 7) 0 1 1).memory_iff b11_memProblem_witness).mp
    b11_memProblem_accepts

/-- **[E.4.7] S1 timestamp-encoding faithfulness is NON-VACUOUS.**  The bounded-injective
    `nmrEncoding` (semantic `k ↦ β^k`) genuinely applies on a NON-TRIVIAL window: over the
    axiom-clean field `ZMod 7` with `β = 3` (`orderOf (3 : ZMod 7) = 6`, `3` a primitive root mod
    `7`), `injective_bounded` yields injectivity on `{r | r.2.2 < 6}` — a size-6 window, not the
    degenerate empty/singleton one.  So the semantic `ℕ`-timestamp faithfully (injectively) models
    the field timestamp `β^k` across a real access window.

    **SC10/SC18 honesty:** the semantic-vs-field-timestamp `1-1*` is *inherent*, not a defect — a
    finite field carries no `LinearOrder` compatible with time, so `MEF.T` (which requires
    `LinearOrder`) literally cannot be `K`; the semantic `T := ℕ` model plus this bounded-injective
    encoding IS the faithful resolution, and this witness shows the bridge is genuinely inhabited. -/
theorem b11_nmrEncoding_injOn_witness :
    Set.InjOn (Nock.nmrEncoding (ZMod 7) (ZMod 7) 3).encode {r | r.2.2 < 6} := by
  have ho : orderOf (3 : ZMod 7) = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hlt
    interval_cases m <;> decide
  exact (Nock.nmrEncoding (ZMod 7) (ZMod 7) 3).injective_bounded (by rw [ho])

def gateE4_doc : String :=
  "GATE E.4 (concrete-run WF witness): PASSED — Category-2 'honest WF' residual CLOSED. " ++
  "The S2 WF-carrying problem structures ComputeProblem/MemProblem are inhabited by a REAL " ++
  "accepting trace (s0 compute row + halt memory row) over the AXIOM-CLEAN field ZMod 7 with EVERY " ++
  "WF field genuinely discharged: injective nodes on Fin 1 (Subsingleton.elim), shared chal by rfl " ++
  "(chalVal := the row's own computeEnvFull/memoryEnvFull .chal), per-row WF holds since s0/halt do " ++
  "NOT trigger the conditional non-degeneracy branches (rlc5/size8/size11 for compute, pole_ne for " ++
  "memory — antecedents state=s5/s8/cons resp. st=read_root/verify_child are decidably false), " ++
  "z=1≠0, β=1≠0, 1≤1. The compute_iff/memory_iff bridges then FIRE on the accepting rows: " ++
  "b11_computeProblem_satisfiable / b11_memProblem_satisfiable DERIVE progSatisfiable/memSatisfiable " ++
  "(.mp of the real bridges computeTable_reified_iff/memoryTable_reified_iff, NOT restated). So the " ++
  "honest WF is NON-VACUOUSLY satisfiable, not a hidden vacuity. HONESTY NOTE: this witness clears " ++
  "the WF because the s0/halt row does not exercise the conditional non-degeneracy antecedents; a " ++
  "richer trace hitting s5/s8/cons/read_root would ADDITIONALLY witness those branches (a richer " ++
  "future witness, not required for non-vacuity)."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SUMMARY
    ══════════════════════════════════════════════════════════════════════════════════════ -/


def batch11_summary : String :=
  "BATCH 11 — THM 5.4 STRUCTURAL BUNDLE (NockVMROM_Thm54_structural) RED-TEAM FINDINGS:\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "1. AXIOMS/sorryAx: PASS. Bundle + all 8 instances (+ S2 bridges) = [propext, Classical.choice, " ++
     "Quot.sound]. paper_NockVMROM_cost_mismatch + nockVMROM_Thm54_corrected AXIOM-FREE. No sorryAx.\n" ++
  "2. VACUITY: MIXED.\n" ++
  "   • S1/S2/S3/S5/S6/S7/S8 instances supply GENUINE predicates + real proofs → PASS. shared_io = " ++
     "real IO.LmIO (rejects ([],[])); S7 bound = real Schwartz–Zippel RHS (≠ badProbability); S6 " ++
     "complete = .mp of the real bridge; S8 cost tied to real AIR.\n" ++
  "   • S4 IsTraversable: FIXED (was FAIL). The class now takes [UniqueMemoryExecutionSeparable ι M] " ++
     "and carries recognition fields referencing the VM's computeAccepts/memoryAccepts (sound inclusion " ++
     "L_RVT ⊆ L_comp/L_mem + VM-accepted recognised-leaf witness). The old uniform vacuity term no longer " ++
     "typechecks ⇒ b11_isTraversable_is_vacuous REMOVED; the class does NOT hold for an arbitrary VMSystem. " ++
     "The ComputeLang/MemoryLang/φcomp/φmem free fields are REMOVED from the class ⇒ NO free-field Equiv.refl " ++
     "residual; non-vacuity rests entirely on the VM-referencing recognition. COMPLETENESS half (L_comp ⊆ " ++
     "L_RVT) PROVEN (recognized_complete_compute/_memory via inverse-BFS Walk.reconForest) — former Track-7 " ++
     "gap CLOSED; S4 recognition is genuinely BIDIRECTIONAL.\n" ++
  "3. HIDDEN HYPS / hcorrect: PASS. nock_uniqueMES.correct proved from language_unfold (no hcorrect); " ++
     "S2 WF is honest (injective nodes, shared chal, per-row WF, z≠0), not circular.\n" ++
  "4. DISCLOSURE: MOSTLY PASS. S1(nmrMEF)/S3(cons,cond-4b)/asymptotic-S7/absolute-costs disclosures " ++
     "ACCURATE. S4 φ-residual RESOLVED: the ComputeLang/MemoryLang/φ free fields are REMOVED, so the former " ++
     "'exact — genuine φ' vs vacuous-identity inconsistency is gone (S4 content = the two VM-referencing " ++
     "inclusions, no free-field Equiv.refl). ONE gap remains: S2 stored Rprog/Rmem are trivial empty-domain " ++
     "decorations (disclosed in-module only, not in SPEC-FREEZE §A).\n" ++
  "5. COST MISMATCH: PASS. Axiom-free; genuine paper-EQUAL(73=73)/reified-UNEQUAL(1<13) refutation, " ++
     "reified side tied to real AIR; paper side disclosed hand-transcription (sound modulo that).\n" ++
  "GATE E: PASS. Bundle inhabited at ZMod 7 (axiom-clean) AND at Goldilocks 𝔽_p/K (pulls " ++
     "goldilocks_prime, allowed). language_nonempty cited + instantiated; Ksz=0 emptiness discriminated.\n" ++
  "GATE E.4: PASS — Category-2 'honest WF' residual CLOSED. The S2 WF-carrying ComputeProblem/" ++
     "MemProblem structures are inhabited by a REAL accepting trace (s0 compute row + halt memory row) " ++
     "over ZMod 7 with EVERY WF field genuinely discharged (injective nodes on Fin 1, shared chal by " ++
     "rfl, per-row WF holds since s0/halt don't trigger the conditional rlc5/size8/size11/pole_ne " ++
     "branches, z=1≠0, β=1≠0, 1≤1); the compute_iff/memory_iff bridges FIRE, DERIVING progSatisfiable/" ++
     "memSatisfiable (.mp of computeTable_reified_iff/memoryTable_reified_iff) — so the honest WF is " ++
     "non-vacuously satisfiable, not a hidden vacuity. HONESTY NOTE: the s0/halt row does not exercise " ++
     "the conditional non-degeneracy antecedents; a richer trace hitting s5/s8/cons/read_root would " ++
     "additionally witness those branches (a richer future witness, not required for non-vacuity).\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "COULD I BREAK IT? The prior S4 vacuity is now FIXED. The bundle is REAL, kernel-clean, non-vacuous, " ++
  "and all 8 clauses carry genuine content. S4 traversability now REFERENCES the VM's " ++
  "computeAccepts/memoryAccepts via recognition fields (sound inclusion L_RVT ⊆ L_comp/L_mem + a " ++
  "VM-accepted recognised-leaf witness); the old uniform vacuity term no longer typechecks, so " ++
  "b11_isTraversable_is_vacuous is REMOVED and the class does NOT hold for an arbitrary VMSystem. " ++
  "The former S4 completeness gap (L_comp ⊆ L_RVT) is now CLOSED: recognized_complete_compute/_memory " ++
  "reconstruct the BFS forest via Walk.reconForest (nockvmrom_compute_complete/nockvmrom_memory_complete), so " ++
  "S4 recognition is bidirectional. The last φ residual is RETIRED: the ComputeLang/MemoryLang/φcomp/φmem free " ++
  "fields are removed from the class, so S4 rests on NO free-field Equiv.refl (its content is exactly the two " ++
  "VM-referencing inclusions). Recommend: surface the S2 trivial-stored-Rprog note into " ++
  "SPEC-FREEZE. Everything else PASSED. No sorryAx, no false global hypothesis, no crypto overclaim.\n" ++
  "AXIOM HYGIENE: generic decls ⊆ {propext, Classical.choice, Quot.sound}; the sole extra axiom is " ++
  "goldilocks_prime, pulled ONLY by b11_bundle_witness_goldilocks (allowed for the concrete witness)."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SELF-CERTIFICATION: `#print axioms` for every proof-carrying declaration in this artifact
    ══════════════════════════════════════════════════════════════════════════════════════ -/

#print axioms b11_shared_io_not_true
#print axioms b11_shared_io_inhabited
#print axioms b11_bound_is_real_rhs
#print axioms b11_isTraversable_recognizes_compute_cite
#print axioms b11_isTraversable_recognizes_memory_cite
#print axioms b11_isTraversable_compute_recognized_cite
#print axioms b11_isTraversable_memory_recognized_cite
#print axioms b11_isTraversable_complete_compute_cite
#print axioms b11_isTraversable_complete_memory_cite
#print axioms b11_nockvmrom_compute_complete_cite
#print axioms b11_nockvmrom_memory_complete_cite
#print axioms b11_uniqueMES_correct_fires
#print axioms b11_stored_Rprog_trivial
#print axioms b11_cost_mismatch_cite
#print axioms b11_reified_faithful_cite
#print axioms b11_bundle_witness_zmod7          -- expect: propext, Classical.choice, Quot.sound (NO goldilocks_prime)
#print axioms b11_bundle_witness_goldilocks     -- expect: + Nock.Field.goldilocks_prime (allowed)
#print axioms b11_bundle_costed_real
#print axioms b11_nmrEncoding_injOn_witness   -- S1 encoding faithfulness non-vacuity (ZMod 7)
#print axioms b11_language_nonempty_cite
#print axioms b11_language_inhabited_zmod7
#print axioms b11_language_empty_Ksz0
-- Gate E.4 — concrete-run WF witness (all six expect: propext, Classical.choice, Quot.sound; NO goldilocks_prime):
#print axioms b11_computeProblem_witness
#print axioms b11_computeProblem_accepts
#print axioms b11_computeProblem_satisfiable
#print axioms b11_memProblem_witness
#print axioms b11_memProblem_accepts
#print axioms b11_memProblem_satisfiable

end Nock.RedTeam
