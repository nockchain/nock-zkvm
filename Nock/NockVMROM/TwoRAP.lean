import Nock.NockVMROM.Soundness

/-!
# S5 `HasTwoRAPVerification` — the NockVMROM two-RAP verification instance (SC16)

Wires the two already-proven **operational walk-soundness probability bounds** into the abstract
Layer-1 `Nock.Framework.TwoRAPVerificationModel` / `HasTwoRAPVerification` surface on the
`NockVMROM` tag, over the semantic NMR memory-encoding family `nmrMEF F K`:

* the **compute** sub-RAP is the single-root execution walk — `Nock.NockVM.walkBad_prob`
  (`ComputeTrial := ComputeWalkTrial K`, reused from `Soundness.lean`);
* the **memory** sub-RAP is the multi-root memory *forest* walk —
  `Nock.NockVM.walkBadForest_prob` (`MemoryTrial := ForestWalkTrial K`);
* the **shared IO** acceptance relation is the paper's `L_mIO^{NMR,Ksz}` membership on a pair of
  request/response record lists (`W^IO_comp`, `W^IO_mem`) — the same `IO.LmIO` that appears in the
  `NockVMROM` recogniser (`Language.lean`, `accepts`) and in the third conjunct of
  `Nock.NockVM.V_NockVMROM_forest`.

The two soundness obligations are *literally* the two probability theorems; the non-vacuity
obligation `shared_io : ∃ w, rapIOAccepts w` is discharged with a concrete inhabitant of `L_mIO`
(a single self-matched record, the positive-witness pattern of `Language.language_nonempty`),
requiring only `1 ≤ Ksz` (the language is genuinely *empty* at `Ksz = 0`, cf.
`Language.not_language_Ksz_zero`).  No `True`, no trivial `bound := badProbability`.
-/

namespace Nock.NockVMROM

open Nock Nock.Framework

/-- **The NockVMROM two-RAP verification model (S5, SC16).**  Realises `TwoRAPVerificationModel` on
    the `NockVMROM` tag over `nmrMEF F K` and the field `K`.  The compute/memory trial spaces are
    the walk bundles of `Soundness.lean`; the bad-event probabilities and bounds are exactly the
    left/right-hand sides of `walkBad_prob` (compute) and `walkBadForest_prob` (memory forest); the
    shared-IO relation is `L_mIO^{NMR,Ksz}` membership on a `(requests, responses)` record pair. -/
noncomputable def nockTwoRAPModel (F K : Type) [Field F] [Field K] [Fintype K] [DecidableEq K]
    (α β : K) (Ksz : ℕ) : TwoRAPVerificationModel (Tag F K α β Ksz) (nmrMEF F K) K where
  ComputeTrial := ComputeWalkTrial K
  MemoryTrial := ForestWalkTrial K
  IOWitness := List ((nmrMEF F K).Rec) × List ((nmrMEF F K).Rec)
  computeBadProbability := computeWalkBadProb
  memoryBadProbability := forestWalkBadProb
  computeBound := computeWalkBound
  memoryBound := forestWalkBound
  rapIOAccepts w := IO.LmIO Ksz w.1 w.2
  ioBound := Ksz

/-- **The NockVMROM two-RAP verification instance (S5).**
    * `compute_sound` = the REAL `walkBad_prob` (single-root compute execution walk);
    * `memory_sound` = the REAL `walkBadForest_prob` (multi-root memory forest walk);
    * `shared_io` = a concrete inhabitant of `L_mIO^{NMR,Ksz}`: for `1 ≤ Ksz`, the singleton
      request/response lists `([r], [r])` (with `r` the zero record) lie in `L_mIO` — the positive
      IO-witness pattern of `Language.language_nonempty`, genuinely non-vacuous. -/
theorem nock_hasTwoRAPVerification (F K : Type) [Field F] [Field K] [Fintype K]
    [DecidableEq K] (α β : K) {Ksz : ℕ} (hK : 1 ≤ Ksz) :
    HasTwoRAPVerification (Tag F K α β Ksz) (nmrMEF F K) K (nockTwoRAPModel F K α β Ksz) where
  compute_sound t :=
    Nock.NockVM.walkBad_prob t.St t.enc t.hEnc t.lbl t.clab t.fo
      t.hSf t.hvalid t.harity t.hfo t.hFcommit
  memory_sound t :=
    Nock.NockVM.walkBadForest_prob t.St t.enc t.hEnc t.lbl t.clab t.fo
      t.hk t.hSf t.hvalid t.harity t.hfo t.hFcommit
  shared_io := by
    -- concrete `L_mIO` inhabitant: one self-matched (zero) record, mirroring `language_nonempty`
    let r0 : (nmrMEF F K).Rec := ((0 : F), ((0, 0, 0), (0, 0, 0)), 0)
    exact ⟨([r0], [r0]), ⟨le_refl 1, hK⟩, [r0], le_refl 1, List.nodup_singleton r0,
      fun _ => Iff.rfl, List.Perm.refl _⟩

#print axioms nockTwoRAPModel
#print axioms nock_hasTwoRAPVerification

end Nock.NockVMROM
