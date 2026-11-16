import Nock.NockVMROM.Thm54.BelowDefs.GenericHonestCommitment
import Nock.NockVMROM.Thm54.P8Core.Batch1091Thm54C2Alignment

/-!
# Named-premises assembly of `HonestCommitment.Data`

The earlier analysis stopped at four named `ResidualPremises`.  This module consumes those
premises, together with the semantic CORE already on `E`, to assemble the
committed compute node tree and every compute-side conjunct of
`HonestCommitment.Data.computeOK`.

`BindComputeRow` is already `bindComputeRow_of_residual`.  Walk `ln(1)=α`
 stays later-round; compute `ln_prev=1` is the named
`firstLine` analog, and with the compute-line hand-off
and Algorithm NockCompute timestamp products it
specializes every authoritative row (`ComputeTimestampSpecializesAt`).
The BFS inverse-reconstruction lifts those rows to a
committed compute tree with the execution's fanout.

Memory nodes are assembled from the same `E` plus two named paper extras:
halt atoms are `S_leaf := {halt}` already on `MemoryLeafAtomsRealized`
; `BindMemoryRow` follows from public-row realization and
`Vmem`; live NMR addresses (`Def:NMR`) are filled from
`E` (`axisNat_of_execution`); the closed-form timestamp `z^i`
 stays named.  Inverse-BFS reconstruction
(`Corr:forest`) lifts those rows to the committed
memory forest with the execution's fanout.
Record equations of the committed compute skeleton follow by construction
from `memRecSkelOf`.  `nounSizeBound` is the
paper leaf window `E.Λ`.  The five remaining census
extras stay named: served slot identification, NPR
leaf bounds on skeleton-projected pairs, size-window
leaf bounds, compute-row `q`-boundedness of decomposition nouns
, and census-pair `q`-boundedness including opcode and
axis atoms.  Memory-row `q`-boundedness is derived from `chooseNoun` of
public-row realization.  `ResidualPremises` stays four.
`commitmentResidualOf` still takes later-round `A`/`W`.
`hzero` remains.  No `∀ E, Data E`.

We do **not** inhabit `slotSemantics` from `E.needs.served`, assembled
record equations, NMR `axisNat`, or the paper base case `\(1,n_1)=n_1`
.  The Lean field is the OP0/OP9 `/` facts on the
reconstructed skeleton.  The missing hypothesis is identification of a
served lookup with that skeleton's subject, `mr2`/`mr3` axis, and child.
NMR axis carry is not re-litigated.

We do **not** inhabit `census` from already-assembled `nounSizeBound = E.Λ`,
`recordEquations`, the reconstructed skeleton, the paper NPR window
(`Lem:ion_univariate_sec` / `Corr:ion_single_security`),
or `data.comparison_leaves` on the free `data.comparisons` list.  The Lean
extra is `CombinedSkeletonCensus`: leaf bounds on reconstructed
`skeletonPairs` (public-claim self-pairs plus `skeletonComparisons`) and
parent-child `edgePairs`.  `comparison_leaves` bounds a role-matching list
that is not that projection.  The missing hypothesis is leaf bounds on the
skeleton-projected comparisons, the public-claim root nouns, and the edge
pairs.  SizeWindow and slot predicates are not weakened.

We do **not** inhabit `skeletonBounded` from already-held objects,
`census`, or `sizeWindowBound`.  The Lean extra is
`SemanticSkeleton.BoundedBy E.q`: atom values `< q` on reconstructed
compute-row nouns, including every active `decompNoun`
.  Memory-row/tree `q`-bounds, the compute root
triple, and subformula nouns are already derived.  `census` is
`leaves ≤ Λ` on the same reconstructed pairs, not that atom range.
The missing hypothesis is `BoundedBy q` on reconstructed compute-row
decomposition nouns.

We inhabit `combinedBounded` at consumed `q` (`11 < ringChar` and
named `q_eq_ringChar`) from named `skeletonBounded` on the assembled
skeleton. The extra is pair-wise `BoundedBy q` on
`combinedSkeletonPairs`: public-claim
self-pairs, `skeletonComparisons` (opcode atoms `0..9`, OP0/OP9 axis
atoms, `wut`/`tis`/`incMod` targets, and cells of row nouns), and edge
pairs. That is not a restatement of row `BoundedBy`: a free OP0 row at
`q = 12` (compatible with `11 < q`) can have every row noun `BoundedBy 12`
while the OP0 recursive-formula right-hand side is `.atom 12`. On the
assembled object the axis is `atomVal` of a `decompNoun` already in
`skeletonBounded`, opcode atoms `0..9` are `< q` from `11 < q`, and
`incMod` is `BoundedBy q` from `q = ringChar`. `Inputs` is not started.

We inhabit `MemoryRecordPremises.axisNat` 1-1 from already-held NMR
Nat-cast objects (`Def:NMR` the paper, lookup address
the paper).  Live `read_root` emissions are service records
(`recordPartition`); `Service.realization.axis_realizes` is the Nat-cast
of that NMR address.  Live `verify_child` committed `address` columns
are `vaxis` of `exactAxisTree`; `E.memoryTrace` already derives
`vaxis = Relaxis`, and `Relaxis` is a Nat-cast of the paper doubling
.  Honest assembly may use
`memoryRecordPremises_of_timestampClosed`.  The two-field eta is
unchanged.  `timestampClosed` stays named.  `axisAtoms` is the compute
OP0/OP9 formula-tail extra and is not swallowed.  `ForestExponentOrder`
is not inhabited.

We do **not** inhabit `timestampClosed` from the NMR Nat-cast of `axisNat`.
`vaxis = Relaxis` is the address column (`Def:NMR` the paper).
Live timestamps are a different NMR field (`Def:NMR` the paper,
closed form `z^i` the paper).  `verify_child` still emits no
`responseRecords`.  The object that would identify
each `verify_child` `mem` with a `Service.record` (hence `mem.ts` with
`Service.record.ts`) is record-level intermediate matching
`PairedRecordLayout` (`consumedRecordList.Perm addedRecordList`).  `E` carries only `RecordCountBalanced` (row
counts).  `verifyPartition` permutes wrapping MTree exponents, not
records.  Wrapping `timestampExp` is not a witness.
`ForestExponentOrder` is not inhabited.

We do **not** inhabit `PairedRecordLayout` from honest `memoryForest`,
inverse-BFS `reconForest`, NMR per-node carry, or the LogUp pairings that
already sit on `E`.  `addedRecordList` / `consumedRecordList` are the BFS
projections of `read_root` add and `verify_child` remove.
`reconForest` roundtrips those same labels.  `ServiceWalk` / `VerifyRoute`
bind the child noun and committed address, not the full `MemRec`.
`recordPartition` identifies added emissions with service records;
`verifyPartition` permutes wrapping exponents.  Structural `intermediate`
matching is `LmIO` of reconstructed timestamps.  `Vmem` `interV` is the
per-row pole inverse; chained LogUp mass equality is not `List.Perm` of
records.  The missing hypothesis is paper intermediate matching at
`MemRec` level, i.e. `PairedRecordLayout` itself.
`timestampClosed_of_paired_record_layout` still takes that extra.
`ForestExponentOrder` is not inhabited.

We do **not** inhabit `ResidualPremises.firstLine` from the walk
overlay / `WalkSat.ln1` / paper `ln(1)=α`.  `firstLine`
is first compute-row `ln_prev=1`.  Walk RAP
`ln(1)=α` is a later-round walk column after the verifier samples `α`
.  Those are different objects.  This does not
inhabit `PairedRecordLayout`, `timestampClosed`, or
`ForestExponentOrder`.

We do **not** inhabit `ResidualPremises.q_eq_ringChar` from
already-held char objects.  The extra is `E.q = ringChar K`.  `E`
carries `1 < q ≤ ringChar`.  `11 < ringChar` inhabits `StateTagChar`
 and, with named equality, `combinedBounded` at
consumed `q`.  Paper `|F|=p=char(K)` is the package
pin, not `|K|=p³`.  Equality does not follow
from the inequality plus `11 < char`.  F97 `q` is not bumped to
Goldilocks.  This does not start `inactiveDec` / `axisAtoms`.
-/

namespace Nock.NockVMROM.Thm54
namespace GenericHonestData

open scoped Classical
open Nock Nock.Walk Nock.NockVMROM
open SemanticStrategy SemanticTimestampStrategy
open SemanticTrace OpcodeSemantics
open HonestCommitment
open GenericHonestCommitment
open OptimizedComputeFinalTrace
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open ServedMemoryTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Timestamp exponents from the compute-line hand-off -/


def lnPrevExpNat (E : BuildableNockExecution F K) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      lnPrevExpNat E k +
        if hk : k < E.cfg.compRows then
          Nock.Framework.recordCount (E.exec.computeRowAt ⟨k, hk⟩).1
        else 0

def lnPrevExp (E : BuildableNockExecution F K) (i : Fin E.cfg.compRows) : ℕ :=
  lnPrevExpNat E i

-- analog, 1813
theorem lnPrevExp_zero (E : BuildableNockExecution F K) :
    lnPrevExp E ⟨0, E.cfg.compRows_pos⟩ = 0 :=
  rfl


theorem lnPrevExp_succ (E : BuildableNockExecution F K)
    (i : Fin E.cfg.compRows) (hi : (i : ℕ) + 1 < E.cfg.compRows) :
    lnPrevExp E ⟨(i : ℕ) + 1, hi⟩ =
      lnPrevExp E i + Nock.Framework.recordCount (E.exec.computeRowAt i).1 := by
  simp [lnPrevExp, lnPrevExpNat, i.isLt]

/-! ## Algorithm NockCompute timestamp products -/


theorem vcomp_ln {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row) :
    row.2.2.1.ln = row.2.2.1.ln_prev *
      row.2.1.α ^ Nock.Framework.recordCount row.1 := by
  have hmem := vcomp_memBlk hacc
  have hst : row.2.2.1.state = row.1 := accepted_pub_state hacc
  cases hrow : row.1
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α ^ 2 := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2.1
    simpa [Nock.Framework.recordCount, hrow] using h
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2
    simpa [Nock.Framework.recordCount, hrow] using h
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α ^ 2 := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2.2
    simpa [Nock.Framework.recordCount, hrow] using h
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2
    simpa [Nock.Framework.recordCount, hrow] using h
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2
    simpa [Nock.Framework.recordCount, hrow] using h
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α ^ 2 := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2.2
    simpa [Nock.Framework.recordCount, hrow] using h
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α ^ 3 := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2.2.2
    simpa [Nock.Framework.recordCount, hrow] using h
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α ^ 2 := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2.2
    simpa [Nock.Framework.recordCount, hrow] using h
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α ^ 2 := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2.2
    simpa [Nock.Framework.recordCount, hrow] using h
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α ^ 3 := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2.2
    simpa [Nock.Framework.recordCount, hrow] using h
  · have h : row.2.2.1.ln = row.2.2.1.ln_prev * row.2.1.α := by
      simp [ComputeTable.memBlk, hst, hrow] at hmem
      exact hmem.2.2
    simpa [Nock.Framework.recordCount, hrow] using h

/-- The `mem_record₁` timestamp equation itself.

*Cite repair.*  This cite list read the paper until it was repaired.  The equation
`ln(i-1) · α = timestamp₁` is **the paper**, inside the `mem_record₁` item that opens at
**`1852`**; `1850` is the block's introductory sentence and carries only the *always-operative*
content.  Note the sibling immediately below already cited `1852-1887`. -/

theorem vcomp_mr1_ts {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row) :
    row.2.2.1.mr1.ts = row.2.2.1.ln_prev * row.2.1.α := by
  have hmr1 := vcomp_mr1 hacc
  simp [hmr1]


theorem vcomp_active_record_ts {cfg : ExactConfig F K}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hacc : ExactExecution.ComputeRowAccepted cfg row)
    (i : Fin 3) (hi : (i : ℕ) < Nock.Framework.recordCount row.1) :
    (computeMemRec row.2.2.1 i).ts =
      row.2.2.1.ln_prev * row.2.1.α ^ ((i : ℕ) + 1) := by
  have hmem := vcomp_memBlk hacc
  have hst := accepted_pub_state hacc
  have hmr1 := vcomp_mr1_ts hacc
  fin_cases i
  · simp [computeMemRec, hmr1, pow_one]
  · have hlive := recordCount_mr2_live row.1 hi
    rcases hlive with h | h | h | h | h | h | h
    · have hmr2 := vcomp_mr2_s0 hacc h
      simp [computeMemRec, hmr2]
    · have hmr2 := vcomp_mr2_tailDecomp hacc (Or.inl h)
      simp [computeMemRec, hmr2]
    · have hmr2 := vcomp_mr2_tailDecomp hacc (Or.inr (Or.inl h))
      simp [computeMemRec, hmr2]
    · have hmr2 := vcomp_mr2_tailDecomp hacc (Or.inr (Or.inr (Or.inl h)))
      simp [computeMemRec, hmr2]
    · have hmr2 := vcomp_mr2_tailDecomp hacc
        (Or.inr (Or.inr (Or.inr (Or.inl h))))
      simp [computeMemRec, hmr2]
    · have hmr2 := vcomp_mr2_tailDecomp hacc
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      simp [computeMemRec, hmr2]
    · have hmr2 := vcomp_mr2_tailDecomp hacc
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      simp [computeMemRec, hmr2]
  · have hlive := recordCount_mr3_live row.1 hi
    rcases hlive with h | h
    · have hmr3 := vcomp_mr3_s6 hacc h
      simp [computeMemRec, hmr3]
    · have hmr3 := vcomp_mr3_s9 hacc h
      simp [computeMemRec, hmr3]

theorem same_alpha (E : BuildableNockExecution F K) (i : Fin E.cfg.compRows) :
    (E.exec.computeRowAt i).2.1.α = E.cfg.challenges.α := by
  have h := congrArg (fun inp : ComputeTable.Inputs K => inp.α)
    (E.semanticData.same_inputs i)
  simpa [ChallengeVector.computeInputs] using h

theorem same_z (E : BuildableNockExecution F K) (i : Fin E.cfg.compRows) :
    (E.exec.computeRowAt i).2.1.z = E.cfg.challenges.z :=
  E.semanticData.same_seed i


-- Relative form: `ln_prev(k) = ln_prev(0) * α^{e_k}`.  The origin is the
-- published first-row `ln_prev`, not the conventional `1`.  `V_comp` plus
-- the compute-line hand-off give the step; the base case is `pow_zero`.
theorem ln_prev_pow_nat (E : BuildableNockExecution F K) :
    ∀ (k : ℕ) (hk : k < E.cfg.compRows),
      (E.exec.computeRowAt ⟨k, hk⟩).2.2.1.ln_prev =
        (E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩).2.2.1.ln_prev *
          E.cfg.challenges.α ^ lnPrevExp E ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [lnPrevExp, lnPrevExpNat, pow_zero]
  | succ k ih =>
      intro hk
      have hk' : k < E.cfg.compRows := Nat.lt_of_succ_lt hk
      have hchain := execution_has_compute_chain E ⟨k, hk'⟩ hk
      have hln := vcomp_ln (E.semanticData.rowAccepted ⟨k, hk'⟩)
      have hα := same_alpha E ⟨k, hk'⟩
      have hsucc := lnPrevExp_succ E ⟨k, hk'⟩ hk
      have hprev := ih hk'
      have hstep :
          (E.exec.computeRowAt ⟨k + 1, hk⟩).2.2.1.ln_prev =
            (E.exec.computeRowAt ⟨k, hk'⟩).2.2.1.ln := by
        simpa [ExactExecution.computePubAt] using hchain.symm
      calc
        (E.exec.computeRowAt ⟨k + 1, hk⟩).2.2.1.ln_prev =
            (E.exec.computeRowAt ⟨k, hk'⟩).2.2.1.ln := hstep
        _ = (E.exec.computeRowAt ⟨k, hk'⟩).2.2.1.ln_prev *
              (E.exec.computeRowAt ⟨k, hk'⟩).2.1.α ^
                Nock.Framework.recordCount (E.exec.computeRowAt ⟨k, hk'⟩).1 := hln
        _ = ((E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩).2.2.1.ln_prev *
              E.cfg.challenges.α ^ lnPrevExp E ⟨k, hk'⟩) *
              E.cfg.challenges.α ^
                Nock.Framework.recordCount (E.exec.computeRowAt ⟨k, hk'⟩).1 := by
            rw [hprev, hα]
        _ = (E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩).2.2.1.ln_prev *
              E.cfg.challenges.α ^ lnPrevExp E ⟨k + 1, hk⟩ := by
            rw [hsucc, mul_assoc, pow_add]

theorem ln_prev_pow (E : BuildableNockExecution F K)
    (i : Fin E.cfg.compRows) :
    (E.exec.computeRowAt i).2.2.1.ln_prev =
      (E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩).2.2.1.ln_prev *
        E.cfg.challenges.α ^ lnPrevExp E i :=
  ln_prev_pow_nat E i i.isLt


theorem ln_pow (E : BuildableNockExecution F K)
    (i : Fin E.cfg.compRows) :
    (E.exec.computeRowAt i).2.2.1.ln =
      (E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩).2.2.1.ln_prev *
        E.cfg.challenges.α ^
          (lnPrevExp E i + Nock.Framework.recordCount (E.exec.computeRowAt i).1) := by
  have hln := vcomp_ln (E.semanticData.rowAccepted i)
  have hprev := ln_prev_pow E i
  have hα := same_alpha E i
  rw [hln, hprev, hα, mul_assoc, pow_add]


theorem computeTimestampSpecializesAt_of_residual
    (E : BuildableNockExecution F K) (_P : ResidualPremises E)
    (i : Fin E.cfg.compRows) :
    ComputeTimestampSpecializesAt E.cfg.challenges.α
      (computeStampOf (lnPrevExp E i) (E.exec.computeRowAt i))
      (E.exec.computeRowAt i) := by
  refine ⟨rfl, same_alpha E i, ?_, ?_, ?_, ?_⟩
  · exact (E.semanticData.rowAccepted i).1.symm
  · have hln := vcomp_ln (E.semanticData.rowAccepted i)
    have hα := same_alpha E i
    simpa [computeStampOf, Nat.add_sub_cancel_left] using (hα ▸ hln)
  · intro j
    simp only [computeStampOf, computeMemRecKind]
    by_cases hj : (j : ℕ) < Nock.Framework.recordCount (E.exec.computeRowAt i).1
    · simp only [hj, ↓reduceIte]
      have hts := vcomp_active_record_ts (E.semanticData.rowAccepted i) j hj
      have hα := same_alpha E i
      have hpow :
          (lnPrevExp E i + (j : ℕ) + 1) - lnPrevExp E i = (j : ℕ) + 1 := by
        omega
      simpa [hpow, hα] using hts
    · simp only [hj, ↓reduceIte]
      have hz := bindMemRec_inactive (E.semanticData.rowAccepted i) j hj
      simp [hz, ComputeTable.MemRec.zero]
  · intro j hjk
    have hj : ¬ ((j : ℕ) < Nock.Framework.recordCount
        (computeStampOf (lnPrevExp E i) (E.exec.computeRowAt i)).state) := by
      intro hlt
      simp [computeStampOf, computeMemRecKind] at hjk hlt
      simp [hlt] at hjk
    simpa [computeStampOf] using
      bindMemRec_inactive (E.semanticData.rowAccepted i) j hj

/-! ## Per-row committed compute node -/


def computeNodeAt (E : BuildableNockExecution F K) (_P : ResidualPremises E)
    (i : Fin E.cfg.compRows) : ComputeNode K :=
  computeNodeOf (E.semanticData.rows i) (publicRowNoun_of_execution E i)
    (lnPrevExp E i)

theorem computeNodeAt_row (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (i : Fin E.cfg.compRows) :
    (computeNodeAt E P i).row = E.exec.computeRowAt i :=
  rfl

theorem computeNodeAt_bind (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (i : Fin E.cfg.compRows) :
    BindComputeRow E.cfg.challenges.z (computeNodeAt E P i).skel
      (computeNodeAt E P i).row := by
  have hz := same_z E i
  rw [computeNodeAt, computeNodeOf, ← hz]
  exact bindComputeRow_of_residual E P i

theorem computeNodeAt_stamp_state (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (i : Fin E.cfg.compRows) :
    (computeNodeAt E P i).stamp.state = (computeNodeAt E P i).skel.state :=
  rfl


theorem computeNodeAt_specializes (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (i : Fin E.cfg.compRows) :
    ComputeTimestampSpecializesAt E.cfg.challenges.α
      (computeNodeAt E P i).stamp (computeNodeAt E P i).row :=
  computeTimestampSpecializesAt_of_residual E P i

/-! ## BFS inverse-reconstruction of the committed compute tree -/


theorem mapNTree_buildTF {α β : Type*} (f : α → β)
    (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → α) (h i : ℕ) :
    mapNTree f (buildTF kroots fo lbl h i) =
      buildTF kroots fo (fun j => f (lbl j)) h i := by
  suffices ∀ d i, h - i = d →
      mapNTree f (buildTF kroots fo lbl h i) =
        buildTF kroots fo (fun j => f (lbl j)) h i from this (h - i) i rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro i hi
    rw [buildTF, mapNTree, buildTF]
    refine congrArg (NTree.node (f (lbl i))) ?_
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    have hmem : j.1 ∈ childIdxsF kroots fo h i := j.property
    have hlt : h - j.1 < d := by
      simp only [childIdxsF, List.mem_filter, decide_eq_true_eq, List.mem_range'] at hmem
      omega
    exact ih (h - j.1) hlt j.1 rfl


theorem mapNTree_reconForest {α β : Type*} (f : α → β)
    (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → α) (h : ℕ) :
    (reconForest kroots fo lbl h).map (mapNTree f) =
      reconForest kroots fo (fun j => f (lbl j)) h := by
  simp only [reconForest]
  rw [List.map_map]
  apply List.map_congr_left
  intro i _hi
  exact mapNTree_buildTF f kroots fo lbl h i


def computeLabelAt (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (i : ℕ) : ComputeNode K :=
  if h : i - 1 < E.cfg.compRows then
    computeNodeAt E P ⟨i - 1, h⟩
  else
    computeNodeAt E P ⟨0, E.cfg.compRows_pos⟩

theorem computeLabelAt_row (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (i : ℕ) :
    (computeLabelAt E P i).row =
      (Option.map NTree.label (bfsForest [E.exec.computeTree])[i - 1]?).getD
        E.exec.computeTree.label := by
  by_cases h : i - 1 < E.cfg.compRows
  · have hlen : i - 1 < (bfsForest [E.exec.computeTree]).length := by
      rwa [E.exec.compute_bfs_length]
    unfold computeLabelAt
    rw [dif_pos h, computeNodeAt_row]
    have hrow :
        E.exec.computeRowAt ⟨i - 1, h⟩ =
          NTree.label ((bfsForest [E.exec.computeTree])[i - 1]'(hlen)) := by
      simp [ExactExecution.computeRowAt, ExactExecution.computeRows,
        List.get_eq_getElem, List.getElem_map, Fin.cast]
    rw [hrow, List.getElem?_eq_getElem hlen]
    rfl
  · unfold computeLabelAt
    rw [dif_neg h, computeNodeAt_row]
    have hge : (bfsForest [E.exec.computeTree]).length ≤ i - 1 := by
      rw [E.exec.compute_bfs_length]
      exact Nat.le_of_not_gt h
    rw [List.getElem?_eq_none hge]
    change E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩ = E.exec.computeTree.label
    have hbfs :
        bfsForest [E.exec.computeTree] =
          E.exec.computeTree ::
            bfsForest ([E.exec.computeTree].flatMap NTree.children) :=
      bfsForest_cons_eq [E.exec.computeTree] (List.cons_ne_nil _ _)
    simp [ExactExecution.computeRowAt, ExactExecution.computeRows, hbfs,
      List.get_eq_getElem, List.getElem_map, Fin.cast]


def computeForestOf (E : BuildableNockExecution F K) (P : ResidualPremises E) :
    List (NTree (ComputeNode K)) :=
  reconForest 1
    (foCol (bfsForest [E.exec.computeTree]))
    (computeLabelAt E P)
    (bfsForest [E.exec.computeTree]).length

theorem computeForestOf_length (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    (computeForestOf E P).length = 1 := by
  simp [computeForestOf, reconForest]


theorem computeForestOf_rows (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    (computeForestOf E P).map (mapNTree ComputeNode.row) = [E.exec.computeTree] := by
  rw [computeForestOf, mapNTree_reconForest]
  trans reconForest 1
      (foCol (bfsForest [E.exec.computeTree]))
      (fun i =>
        (Option.map NTree.label (bfsForest [E.exec.computeTree])[i - 1]?).getD
          E.exec.computeTree.label)
      (bfsForest [E.exec.computeTree]).length
  · congr 1
    funext i
    exact computeLabelAt_row E P i
  · exact exact_reconForest_bfsForest [E.exec.computeTree]
      (List.cons_ne_nil _ _) E.exec.computeTree.label


def computeNodesOf (E : BuildableNockExecution F K) (P : ResidualPremises E) :
    NTree (ComputeNode K) :=
  (computeForestOf E P).head
    (by
      intro h
      have := congrArg List.length h
      simp [computeForestOf_length E P] at this)

theorem computeForestOf_eq_singleton (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    computeForestOf E P = [computeNodesOf E P] := by
  have hlen := computeForestOf_length E P
  match h : computeForestOf E P with
  | [] =>
    have := congrArg List.length h
    simp [hlen] at this
  | t :: rest =>
    have h1 : (t :: rest).length = 1 := by rw [← h, hlen]
    have hrest : rest = [] := by
      simp at h1
      exact h1
    simp [computeNodesOf, h, hrest]

theorem computeNodesOf_rows (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    mapNTree ComputeNode.row (computeNodesOf E P) = E.exec.computeTree := by
  have hmap := computeForestOf_rows E P
  simpa [computeForestOf_eq_singleton E P] using hmap

theorem computeLabelAt_of_index (E : BuildableNockExecution F K)
    (P : ResidualPremises E) {i : ℕ}
    (hidx : i - 1 < E.cfg.compRows) :
    computeLabelAt E P i = computeNodeAt E P ⟨i - 1, hidx⟩ := by
  unfold computeLabelAt
  rw [dif_pos hidx]

/-- The reconstructed compute tree's root label is the row-zero committed node: `reconForest 1`
builds a single tree from index `1`, and `computeLabelAt` sends `1` to row `1 - 1 = 0`.
-- -/
theorem computeNodesOf_label (E : BuildableNockExecution F K) (P : ResidualPremises E) :
    (computeNodesOf E P).label = computeNodeAt E P ⟨0, E.cfg.compRows_pos⟩ := by
  show (buildTF 1 (foCol (bfsForest [E.exec.computeTree])) (computeLabelAt E P)
      (bfsForest [E.exec.computeTree]).length 1).label = _
  rw [buildTF_label]
  exact computeLabelAt_of_index E P (i := 1) E.cfg.compRows_pos

/-- **`HonestCommitment.Data.root_line_exponent` for the named-premises constructor.**  The
committed root stamp is `computeStampOf (lnPrevExp E ⟨0,_⟩) _` and `lnPrevExp` at row zero is `0`
(`lnPrevExp_zero`), so `dataOf` discharges the `root_line_exponent` carrier field with no new input and no change
to its signature. -- the paper -/
theorem computeNodesOf_root_line_exponent (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    (computeNodesOf E P).label.stamp.lnPrevExponent = 0 := by
  rw [computeNodesOf_label E P]
  rfl


theorem computeNodesOf_ok (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    ComputeNodesOK E.cfg.challenges.z E.cfg.challenges.α (computeNodesOf E P) := by
  intro t ht
  have hsing := computeForestOf_eq_singleton E P
  have htbfs : t ∈ bfsForest (computeForestOf E P) := by
    rw [hsing, mem_bfsForest]
    exact ⟨computeNodesOf E P, List.mem_singleton.mpr rfl, ht⟩
  have hvalid := foCol_BFSValidF [E.exec.computeTree] (List.cons_ne_nil _ _)
  have hSf := foCol_Sf_tilingF [E.exec.computeTree] (List.cons_ne_nil _ _)
  have hbfs := bfsForest_reconForest (kroots := 1)
      (foCol (bfsForest [E.exec.computeTree]))
      (computeLabelAt E P)
      (bfsForest [E.exec.computeTree]).length (Nat.le_refl 1) hSf hvalid
  rw [computeForestOf, hbfs, List.mem_map] at htbfs
  obtain ⟨i, hi, rfl⟩ := htbfs
  rw [List.mem_range'] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  simp only [Nat.one_mul]
  have hi1 : 1 ≤ 1 + k := by omega
  have hih : 1 + k ≤ (bfsForest [E.exec.computeTree]).length := by omega
  have hidx : k < E.cfg.compRows := by
    rw [← E.exec.compute_bfs_length]
    exact hk
  have hlbl : computeLabelAt E P (1 + k) = computeNodeAt E P ⟨k, hidx⟩ := by
    have : (1 + k) - 1 = k := Nat.add_sub_cancel_left 1 k
    simpa [this] using computeLabelAt_of_index E P (i := 1 + k) (by simpa [this] using hidx)
  have hchlen :
      (buildTF 1 (foCol (bfsForest [E.exec.computeTree]))
          (computeLabelAt E P) (bfsForest [E.exec.computeTree]).length (1 + k)).children.length =
        foCol (bfsForest [E.exec.computeTree]) (1 + k) := by
    rw [buildTF_children, childIdxsF_eq (kroots := 1) _ _ hSf hvalid hi1 hih,
      List.length_map, List.length_range']
  have hlen : k < (bfsForest [E.exec.computeTree]).length := hk
  set orig := (bfsForest [E.exec.computeTree])[k]'hlen
  have horigMem : orig ∈ bfsForest [E.exec.computeTree] := List.getElem_mem _
  have hin : InTree E.exec.computeTree orig := by
    obtain ⟨root, hroot, hin⟩ := (mem_bfsForest _ _).1 horigMem
    simp only [List.mem_singleton] at hroot
    subst root
    exact hin
  have htop := E.traversal.1
  have hfan :=
    fanout_eq_children_length_of_properArity
      (ComputeTable.comp_stateSep (K := K)) htop.1 htop.2 orig hin
  refine ⟨?fanout, ?st, ?bind, ?ts⟩
  · rw [buildTF_label, hchlen, hlbl]
    have hfo :
        foCol (bfsForest [E.exec.computeTree]) (1 + k) = orig.children.length := by
      unfold foCol orig
      have : 1 + k - 1 = k := Nat.add_sub_cancel_left 1 k
      simp [this, List.getElem?_eq_getElem hlen]
    have hstate :
        (computeNodeAt E P ⟨k, hidx⟩).skel.state = orig.label.1 := by
      simp [orig, computeNodeAt, computeNodeOf, computeSkeletonOf,
        ExactExecution.computeRowAt, ExactExecution.computeRows,
        List.get_eq_getElem, List.getElem_map, Fin.cast]
    rw [hfo, hstate]
    exact hfan.symm
  · rw [buildTF_label, hlbl]
    exact computeNodeAt_stamp_state E P ⟨k, hidx⟩
  · rw [buildTF_label, hlbl]
    exact computeNodeAt_bind E P ⟨k, hidx⟩
  · rw [buildTF_label, hlbl]
    exact computeNodeAt_specializes E P ⟨k, hidx⟩

/-! ## Memory-row nouns, halt atoms, and named NMR extras -/

/-- Paper closed form: a live memory-record timestamp is some power of `α`
.  `Vmem` treats `mem.ts` as a free IO column; the monomial is
the compute-line timestamp transferred by IO matching. -/

def MemoryTimestampClosedAt (α ts : K) : Prop :=
  ∃ e : ℕ, ts = α ^ e

noncomputable def memoryRecordExp (α ts : K) : ℕ :=
  if h : MemoryTimestampClosedAt α ts then h.choose else 0


theorem memoryRecordExp_spec {α ts : K} (h : MemoryTimestampClosedAt α ts) :
    ts = α ^ memoryRecordExp α ts := by
  simp only [memoryRecordExp, dif_pos h]
  exact h.choose_spec

/-- Named paper extras on the way to committed memory nodes.  Halt atoms
(`S_leaf := {halt}`) and public-row nouns are already on `E`.
Live NMR addresses are filled from `E` (`axisNat_of_execution`).
The closed-form timestamp stays named.  Honest `ver = (st = read_root)`
 is required for `BindMemoryRow` and for connecting
`addedRecordList` (by-state) to `rootResponseRecords` (by-`ver`). -/

structure MemoryRecordPremises (E : BuildableNockExecution F K) where
  /-- Paper: NMR address space is the Nat axis, Nat-cast into the field
  (`Def:NMR`). -/
  axisNat :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)
  /-- Paper: live memory-record timestamps are `α^i`. -/
  timestampClosed :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts
  /-- Honest IO selector: `ver = (st = read_root)`. -/
  honestVer :
    ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)

theorem memoryPublicRowNoun_of_execution (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) :
    MemoryPublicRowNounRealization E.q (E.exec.memoryRowAt i) := by
  have hAll :=
    ExactExecutionNounRealization.memoryRows E.semanticData.language.nounRealization
  exact (List.forall_iff_forall_mem.mp hAll) _
    (ExactExecution.memoryRowAt_mem E.exec i)

theorem memoryRowAccepted_of_execution (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) :
    ExactExecution.MemoryRowAccepted E.cfg (E.exec.memoryRowAt i) :=
  ExactExecution.memoryRowAt_accepted
    E.language.traversable.chained.semantic.2.1 i

theorem same_z_mem (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows) :
    (E.exec.memoryRowAt i).2.1.z = E.cfg.challenges.z :=
  (exactLanguage_challenges_loadBearing
      E.language.traversable.chained.semantic.toExactLanguage).2
    (E.exec.memoryRowAt i) (ExactExecution.memoryRowAt_mem E.exec i) |>.1

/-- The executed memory row is the Form R row encode of the a-bearing one (28th). -/
theorem exec_memoryRowAt_encode (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows) :
    E.exec.memoryRowAt i = MemoryRowTemplate.encodeRow E.cfg.challenges.lam (E.execA.memoryRowAt i) := by
  have h := ExactExecution.encodeMem_memoryRowAt E.execA i
  rw [← E.exec_encode] at h
  exact h

theorem memoryChildCell_encodeRow (lmb : K) (r : MemoryTable.MState × MemoryTable.DTmem K)
    (j : Fin 2) :
    memoryChildCell (MemoryRowTemplate.encodeRow lmb r).2.2 j = memoryChildCell r.2.2 j := by
  fin_cases j <;> simp [memoryChildCell]

def memoryBfsNode (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) :=
  (bfsForest E.exec.memoryForest)[i]'(by
    rw [E.exec.memory_bfs_length]
    exact i.isLt)

theorem memoryBfsNode_label (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) :
    (memoryBfsNode E i).label = E.exec.memoryRowAt i := by
  simp [memoryBfsNode, ExactExecution.memoryRowAt, ExactExecution.memoryRows,
    List.get_eq_getElem, List.getElem_map, Fin.cast]

theorem memoryBfsNode_mem (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) :
    memoryBfsNode E i ∈ bfsForest E.exec.memoryForest :=
  List.getElem_mem _

/-- The `i`-th BFS node of the a-bearing forest (28th: the served trace lives on `execA`). -/
def memoryBfsNodeA (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows) :
    NTree (MemoryTable.MState × MemoryTable.DTmem K) :=
  (bfsForest E.execA.memoryForest)[i]'(by
    rw [E.execA.memory_bfs_length]
    exact i.isLt)

theorem memoryBfsNodeA_label (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) :
    (memoryBfsNodeA E i).label = E.execA.memoryRowAt i := by
  simp [memoryBfsNodeA, ExactExecution.memoryRowAt, ExactExecution.memoryRows,
    List.get_eq_getElem, List.getElem_map, Fin.cast]

theorem memoryBfsNodeA_mem (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) :
    memoryBfsNodeA E i ∈ bfsForest E.execA.memoryForest :=
  List.getElem_mem _

private theorem memoryLeafAtoms_false {q : ℕ}
    {st : MemoryTable.MState} {data : MemoryTable.DTmem K}
    {ch : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))}
    (h : MemoryLeafAtomsRealized q (.node (st, data) ch))
    (hbad :
        ¬((st = .halt ∧ ch = []) ∨
          (st = .decompose ∧ ∃ l r, ch = [l, r]) ∨
          (st = .read_root ∧ ∃ c, ch = [c]) ∨
          (st = .verify_child ∧ ∃ c, ch = [c]))) :
    False := by
  cases st with
  | halt =>
      match ch with
      | [] => exact hbad (Or.inl ⟨rfl, rfl⟩)
      | _ :: _ =>
          change False at h
          exact h
  | decompose =>
      match ch with
      | [] =>
          change False at h
          exact h
      | [l] =>
          change False at h
          exact h
      | [l, r] =>
          exact hbad (Or.inr (Or.inl ⟨rfl, ⟨l, r, rfl⟩⟩))
      | _ :: _ :: _ :: _ =>
          change False at h
          exact h
  | read_root =>
      match ch with
      | [] =>
          change False at h
          exact h
      | [c] =>
          exact hbad (Or.inr (Or.inr (Or.inl ⟨rfl, ⟨c, rfl⟩⟩)))
      | _ :: _ :: _ =>
          change False at h
          exact h
  | verify_child =>
      match ch with
      | [] =>
          change False at h
          exact h
      | [c] =>
          exact hbad (Or.inr (Or.inr (Or.inr ⟨rfl, ⟨c, rfl⟩⟩)))
      | _ :: _ :: _ =>
          change False at h
          exact h


theorem memoryLeafAtoms_of_inTree {q : ℕ} :
    ∀ {T u : NTree (MemoryTable.MState × MemoryTable.DTmem K)},
      MemoryLeafAtomsRealized q T → InTree T u → MemoryLeafAtomsRealized q u := by
  intro T u hT hu
  induction hu with
  | here => exact hT
  | @sub c s t hs _ ih =>
      have hs' : MemoryLeafAtomsRealized q s := by
        cases c with
        | node lbl ch =>
            obtain ⟨st, data⟩ := lbl
            simp only [NTree.children_node] at hs
            cases st with
            | decompose =>
                match ch with
                | [l, r] =>
                    have hT' : MemoryLeafAtomsRealized q l ∧
                        MemoryLeafAtomsRealized q r := hT
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
                    rcases hs with rfl | rfl
                    · exact hT'.1
                    · exact hT'.2
                | [] => cases hs
                | [l] =>
                    exact (memoryLeafAtoms_false hT (by
                      intro hbad
                      rcases hbad with h | h | h | h
                      · cases h.1
                      · obtain ⟨_, _, hch⟩ := h.2
                        cases hch
                      · cases h.1
                      · cases h.1)).elim
                | _ :: _ :: _ :: _ =>
                    exact (memoryLeafAtoms_false hT (by
                      intro hbad
                      rcases hbad with h | h | h | h
                      · cases h.1
                      · obtain ⟨_, _, hch⟩ := h.2
                        cases hch
                      · cases h.1
                      · cases h.1)).elim
            | halt =>
                match ch with
                | [] => cases hs
                | _ :: _ =>
                    exact (memoryLeafAtoms_false hT (by
                      intro hbad
                      rcases hbad with h | h | h | h
                      · cases h.2
                      · cases h.1
                      · cases h.1
                      · cases h.1)).elim
            | read_root =>
                match ch with
                | [child] =>
                    have hT' : MemoryLeafAtomsRealized q child := hT
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
                    cases hs
                    exact hT'
                | [] => cases hs
                | _ :: _ :: _ =>
                    exact (memoryLeafAtoms_false hT (by
                      intro hbad
                      rcases hbad with h | h | h | h
                      · cases h.1
                      · cases h.1
                      · obtain ⟨_, hch⟩ := h.2
                        cases hch
                      · cases h.1)).elim
            | verify_child =>
                match ch with
                | [child] =>
                    have hT' : MemoryLeafAtomsRealized q child := hT
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
                    cases hs
                    exact hT'
                | [] => cases hs
                | _ :: _ :: _ =>
                    exact (memoryLeafAtoms_false hT (by
                      intro hbad
                      rcases hbad with h | h | h | h
                      · cases h.1
                      · cases h.1
                      · cases h.1
                      · obtain ⟨_, hch⟩ := h.2
                        cases hch)).elim
      exact ih hs'


theorem halt_shape_of_leafAtoms {q : ℕ}
    {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryLeafAtomsRealized q t) (hst : t.label.1 = .halt) :
    t.children = [] ∧
      ∃ k : ℕ, k < q ∧ (k : K) = t.label.2.2.pt.noun.leaf := by
  cases t with
  | node lbl ch =>
      obtain ⟨st, data⟩ := lbl
      cases st with
      | decompose => simp at hst
      | halt =>
          match ch with
          | [] =>
              refine ⟨rfl, ?_⟩
              exact h
          | _ :: _ =>
              exact (memoryLeafAtoms_false h (by
                intro hbad
                rcases hbad with h' | h' | h' | h'
                · cases h'.2
                · cases h'.1
                · cases h'.1
                · cases h'.1)).elim
      | read_root => simp at hst
      | verify_child => simp at hst


theorem haltAtom_exists (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (hhalt : (E.exec.memoryRowAt i).1 = .halt) :
    ∃ k : ℕ, k < E.q ∧
      (k : K) = (E.exec.memoryRowAt i).2.2.pt.noun.leaf := by
  have ht := memoryBfsNode_mem E i
  obtain ⟨root, hroot, hin⟩ := (mem_bfsForest _ _).1 ht
  have hleafRoot :=
    E.semanticData.language.nounRealization.memoryLeaves root hroot
  have hleaf := memoryLeafAtoms_of_inTree hleafRoot hin
  have hlab : (memoryBfsNode E i).label.1 = .halt := by
    simpa [memoryBfsNode_label] using hhalt
  simpa [memoryBfsNode_label] using (halt_shape_of_leafAtoms hleaf hlab).2

noncomputable def haltAtomVal (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (hhalt : (E.exec.memoryRowAt i).1 = .halt) : ℕ :=
  (haltAtom_exists E i hhalt).choose

theorem haltAtomVal_spec (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (hhalt : (E.exec.memoryRowAt i).1 = .halt) :
    haltAtomVal E i hhalt < E.q ∧
      (haltAtomVal E i hhalt : K) =
        (E.exec.memoryRowAt i).2.2.pt.noun.leaf :=
  (haltAtom_exists E i hhalt).choose_spec


def memoryParentNoun (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) : Noun :=
  if h : (E.exec.memoryRowAt i).1 = .halt then
    .atom (haltAtomVal E i h)
  else
    chooseNoun (memoryPublicRowNoun_of_execution E i).parent.1


theorem memoryParentNoun_halt (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (hhalt : (E.exec.memoryRowAt i).1 = .halt) :
    memoryParentNoun E i = .atom (haltAtomVal E i hhalt) := by
  simp [memoryParentNoun, hhalt]

def memoryChildNoun (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) (j : Fin 2)
    (hj : (j : ℕ) < MemoryTable.fanoutMem (E.exec.memoryRowAt i).1) : Noun :=
  let pubR := memoryPublicRowNoun_of_execution E i
  have hkind : memoryChildKind (E.exec.memoryRowAt i).1 j = .active := by
    simp [memoryChildKind, hj]
  have hcell :
      MemoryCellSlotRealized (E.exec.memoryRowAt i).2.1.z E.q .active
        (memoryChildCell (E.exec.memoryRowAt i).2.2 j) :=
    hkind ▸ pubR.child j
  chooseNoun (fpSlot_active_realized hcell)


def memoryMemRecSkel (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : Fin E.cfg.memRows)
    (hact : memoryMemRecKind (E.exec.memoryRowAt i).1 = .active) :
    MemRecSkeleton :=
  let pubR := memoryPublicRowNoun_of_execution E i
  have hmr := hact ▸ pubR.memoryRecord
  { root := chooseNoun hmr.2.1.1
    child := chooseNoun hmr.2.2.1
    axis := (M.axisNat i hact).choose }


def memorySkeletonOf (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : Fin E.cfg.memRows) :
    MemoryRowSkeleton where
  state := (E.exec.memoryRowAt i).1
  parent := memoryParentNoun E i
  haltAtom := fun h => haltAtomVal E i h
  haltParent := fun h => memoryParentNoun_halt E i h
  child := fun j hj => memoryChildNoun E i j hj
  memoryRecord := fun hact => memoryMemRecSkel E M i hact


def memoryStampOf (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows) :
    MemoryTimestampRow where
  state := (E.exec.memoryRowAt i).1
  recordExponent :=
    memoryRecordExp E.cfg.challenges.α (E.exec.memoryRowAt i).2.2.mem.ts


def memoryNodeAt (E : BuildableNockExecution F K) (M : MemoryRecordPremises E)
    (i : Fin E.cfg.memRows) : MemoryNode K where
  skel := memorySkeletonOf E M i
  stamp := memoryStampOf E i
  row := E.execA.memoryRowAt i

theorem memoryNodeAt_row (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : Fin E.cfg.memRows) :
    (memoryNodeAt E M i).row = E.execA.memoryRowAt i :=
  rfl


theorem bindFP_halt_parent (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (hhalt : (E.exec.memoryRowAt i).1 = .halt) :
    bindFP E.cfg.challenges.z (memoryParentNoun E i)
      (E.exec.memoryRowAt i).2.2.pt.noun := by
  have hacc := memoryRowAccepted_of_execution E i
  have hst : (E.exec.memoryRowAt i).2.2.st = .halt := hacc.1.symm.trans hhalt
  have heq : MemoryTable.eqBlk (E.exec.memoryRowAt i).2.1
      (E.exec.memoryRowAt i).2.2 := (hacc.2.2.1).2.1
  have hz := same_z_mem E i
  have hleaf := haltAtomVal_spec E i hhalt
  rw [bindFP, memoryParentNoun_halt E i hhalt, GlobalCarryRecognizer.enc_atom]
  refine ComputeTable.FP.ext ?_ ?_ ?_
  · have hsize : (E.exec.memoryRowAt i).2.2.pt.noun.size =
        (E.exec.memoryRowAt i).2.1.z := by
      simp [MemoryTable.eqBlk, hst] at heq
      exact heq.1
    simpa [ComputeTable.FP.atomFP] using hsize.trans hz
  · have hdyck : (E.exec.memoryRowAt i).2.2.pt.noun.dyck = 0 := by
      simp [MemoryTable.eqBlk, hst] at heq
      exact heq.2.1
    simpa [ComputeTable.FP.atomFP] using hdyck
  · simpa [ComputeTable.FP.atomFP] using hleaf.2.symm


theorem bindFP_live_parent (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (hnh : (E.exec.memoryRowAt i).1 ≠ .halt) :
    bindFP E.cfg.challenges.z (memoryParentNoun E i)
      (E.exec.memoryRowAt i).2.2.pt.noun := by
  have hz := same_z_mem E i
  simp [memoryParentNoun, hnh]
  simpa [bindFP, hz] using
    (chooseNoun_enc (memoryPublicRowNoun_of_execution E i).parent.1).symm


theorem bindFP_parent (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) :
    bindFP E.cfg.challenges.z (memoryParentNoun E i)
      (E.exec.memoryRowAt i).2.2.pt.noun := by
  by_cases hhalt : (E.exec.memoryRowAt i).1 = .halt
  · exact bindFP_halt_parent E i hhalt
  · exact bindFP_live_parent E i hhalt


theorem bindFP_child (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) (j : Fin 2)
    (hj : (j : ℕ) < MemoryTable.fanoutMem (E.exec.memoryRowAt i).1) :
    bindFP E.cfg.challenges.z (memoryChildNoun E i j hj)
      (memoryChildCell (E.exec.memoryRowAt i).2.2 j).noun := by
  have hz := same_z_mem E i
  let pubR := memoryPublicRowNoun_of_execution E i
  have hkind : memoryChildKind (E.exec.memoryRowAt i).1 j = .active := by
    simp [memoryChildKind, hj]
  have hcell :
      MemoryCellSlotRealized (E.exec.memoryRowAt i).2.1.z E.q .active
        (memoryChildCell (E.exec.memoryRowAt i).2.2 j) :=
    hkind ▸ pubR.child j
  simp [memoryChildNoun]
  simpa [bindFP, hz] using (chooseNoun_enc (fpSlot_active_realized hcell)).symm


theorem memoryChild_padding (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) (j : Fin 2)
    (hj : ¬ ((j : ℕ) < MemoryTable.fanoutMem (E.exec.memoryRowAt i).1)) :
    memoryChildCell (E.exec.memoryRowAt i).2.2 j = MemoryTable.Cell.zero := by
  have pubR := memoryPublicRowNoun_of_execution E i
  have hkind : memoryChildKind (E.exec.memoryRowAt i).1 j = .padding := by
    simp [memoryChildKind, hj]
  have hcell :
      MemoryCellSlotRealized (E.exec.memoryRowAt i).2.1.z E.q .padding
        (memoryChildCell (E.exec.memoryRowAt i).2.2 j) :=
    hkind ▸ pubR.child j
  simpa [MemoryCellSlotRealized] using hcell


theorem bindMemRec_memory (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : Fin E.cfg.memRows)
    (hact : memoryMemRecKind (E.exec.memoryRowAt i).1 = .active) :
    BindMemRec E.cfg.challenges.z (memoryMemRecSkel E M i hact)
      (E.execA.memoryRowAt i).2.2.mem := by
  have hz := same_z_mem E i
  let pubR := memoryPublicRowNoun_of_execution E i
  have hmr := hact ▸ pubR.memoryRecord
  have he := exec_memoryRowAt_encode E i
  have hroot : (E.execA.memoryRowAt i).2.2.mem.root = (E.exec.memoryRowAt i).2.2.mem.root := by
    rw [he]; simp
  have hchild :
      (E.execA.memoryRowAt i).2.2.mem.child = (E.exec.memoryRowAt i).2.2.mem.child := by
    rw [he]; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hroot]
    simpa [bindFP, memoryMemRecSkel, hz] using
      (chooseNoun_enc hmr.2.1.1).symm
  · rw [hchild]
    simpa [bindFP, memoryMemRecSkel, hz] using
      (chooseNoun_enc hmr.2.2.1).symm
  · simpa [memoryMemRecSkel] using (M.axisNat i hact).choose_spec


theorem memoryMemRec_padding (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (hpad : memoryMemRecKind (E.exec.memoryRowAt i).1 = .padding) :
    (E.exec.memoryRowAt i).2.2.mem = ComputeTable.MemRec.zero := by
  have pubR := memoryPublicRowNoun_of_execution E i
  have hmr :
      MemRecSlotRealized (E.exec.memoryRowAt i).2.1.z E.q .padding
        (E.exec.memoryRowAt i).2.2.mem :=
    hpad ▸ pubR.memoryRecord
  simpa [MemRecSlotRealized] using hmr


/-- The committed node's a-bearing row binds (`BindMemoryRowA`, 28th): every non-record column is
the executed row's (`encodeRow` touches only the record and `C'`), and the record's address is the
NMR Nat axis (`axisNat`). -/
theorem bindMemoryRow_of_assembly (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : Fin E.cfg.memRows) :
    BindMemoryRowA E.cfg.challenges.z (memorySkeletonOf E M i)
      (E.execA.memoryRowAt i) := by
  have hacc := memoryRowAccepted_of_execution E i
  have hz := same_z_mem E i
  have he := exec_memoryRowAt_encode E i
  have hver : (E.exec.memoryRowAt i).2.2.ver =
      decide ((memorySkeletonOf E M i).state = MemoryTable.MState.read_root) := by
    have h := M.honestVer (E.exec.memoryRowAt i) (ExactExecution.memoryRowAt_mem _ i)
    have hst : (E.exec.memoryRowAt i).2.2.st = (memorySkeletonOf E M i).state := by
      simp [memorySkeletonOf, ExactExecution.memoryRowAt]
      exact hacc.1.symm
    rw [← hst]; exact h
  have hpar := bindFP_parent E i
  have hst1 := hacc.1
  rw [he] at hz hver hpar hst1
  simp only [MemoryRowTemplate.encodeRow_inputs, MemoryRowTemplate.encodeRow_ver,
    MemoryRowTemplate.encodeRow_pt, MemoryRowTemplate.encodeRow_fst,
    MemoryRowTemplate.encodeRow_st] at hz hver hpar hst1
  have hstate : (E.execA.memoryRowAt i).1 = (memorySkeletonOf E M i).state := by
    simp [memorySkeletonOf, he]
  refine ⟨hstate, hz, hst1.symm.trans hstate, hpar, ?_, ?_, hver⟩
  · intro j
    by_cases hj : (j : ℕ) < MemoryTable.fanoutMem (memorySkeletonOf E M i).state
    · rw [dif_pos hj]
      have h := bindFP_child E i j (by simpa [memorySkeletonOf] using hj)
      rw [he, memoryChildCell_encodeRow] at h
      simpa [memorySkeletonOf] using h
    · rw [dif_neg hj]
      have h := memoryChild_padding E i j (by simpa [memorySkeletonOf] using hj)
      rw [he, memoryChildCell_encodeRow] at h
      exact h
  · by_cases hact : memoryMemRecKind (memorySkeletonOf E M i).state = .active
    · rw [dif_pos hact]
      simpa [memorySkeletonOf] using
        bindMemRec_memory E M i (by simpa [memorySkeletonOf] using hact)
    · rw [dif_neg hact]
      have hpad : memoryMemRecKind (E.exec.memoryRowAt i).1 = .padding := by
        cases hkk : memoryMemRecKind (E.exec.memoryRowAt i).1 with
        | active =>
            simp [memorySkeletonOf] at hact
            exact absurd hkk hact
        | padding => rfl
      have h := memoryMemRec_padding E i hpad
      have hna : memoryMemRecKind (E.execA.memoryRowAt i).1 ≠ .active := by
        rw [he] at hpad; simp only [MemoryRowTemplate.encodeRow_fst] at hpad
        rw [hpad]; decide
      rw [he, MemoryRowTemplate.encodeRow_mem_inactive _ _ hna] at h
      exact h


theorem memoryTimestampSpecializesAt_of_assembly_exec
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E)
    (i : Fin E.cfg.memRows) :
    MemoryTimestampSpecializesAt E.cfg.challenges.α (memoryStampOf E i)
      (E.exec.memoryRowAt i) := by
  have hacc := memoryRowAccepted_of_execution E i
  refine ⟨rfl, hacc.1.symm, ?_, ?_⟩
  · by_cases hact : memoryMemRecKind (memoryStampOf E i).state = .active
    · rw [if_pos hact]
      have hclosed := M.timestampClosed i (by simpa [memoryStampOf] using hact)
      simpa [memoryStampOf] using memoryRecordExp_spec hclosed
    · rw [if_neg hact]
      have hpad : memoryMemRecKind (E.exec.memoryRowAt i).1 = .padding := by
        cases hkk : memoryMemRecKind (E.exec.memoryRowAt i).1 with
        | active =>
            simp [memoryStampOf] at hact
            exact absurd hkk hact
        | padding => rfl
      have hz := memoryMemRec_padding E i hpad
      simp [hz, ComputeTable.MemRec.zero]
  · intro hpad
    have hpad' : memoryMemRecKind (E.exec.memoryRowAt i).1 = .padding := by
      simpa [memoryStampOf] using hpad
    exact memoryMemRec_padding E i hpad'


/-- The timestamp specialization holds on the a-bearing row (same `ts`, state and padding). -/
theorem memoryTimestampSpecializesAt_of_assembly
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E)
    (i : Fin E.cfg.memRows) :
    MemoryTimestampSpecializesAt E.cfg.challenges.α (memoryStampOf E i)
      (E.execA.memoryRowAt i) := by
  have h := memoryTimestampSpecializesAt_of_assembly_exec E M i
  rw [exec_memoryRowAt_encode E i] at h
  exact MemoryRowTemplate.specializesAt_of_encodeRow h

theorem memoryNodeAt_bind (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : Fin E.cfg.memRows) :
    BindMemoryRowA E.cfg.challenges.z (memoryNodeAt E M i).skel
      (memoryNodeAt E M i).row :=
  bindMemoryRow_of_assembly E M i

theorem memoryNodeAt_stamp_state (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : Fin E.cfg.memRows) :
    (memoryNodeAt E M i).stamp.state = (memoryNodeAt E M i).skel.state :=
  rfl


theorem memoryNodeAt_specializes (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : Fin E.cfg.memRows) :
    MemoryTimestampSpecializesAt E.cfg.challenges.α
      (memoryNodeAt E M i).stamp (memoryNodeAt E M i).row :=
  memoryTimestampSpecializesAt_of_assembly E M i

/-! ## BFS inverse-reconstruction of the committed memory forest
(`Corr:forest`) -/


def memoryLabelAt (E : BuildableNockExecution F K) (M : MemoryRecordPremises E)
    (i : ℕ) : MemoryNode K :=
  if h : i - 1 < E.cfg.memRows then
    memoryNodeAt E M ⟨i - 1, h⟩
  else
    memoryNodeAt E M ⟨0, E.cfg.memRows_pos⟩

theorem memoryLabelAt_row (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : ℕ) :
    (memoryLabelAt E M i).row =
      (Option.map NTree.label (bfsForest E.execA.memoryForest)[i - 1]?).getD
        E.execA.memoryFallbackLabel := by
  by_cases h : i - 1 < E.cfg.memRows
  · have hlen : i - 1 < (bfsForest E.execA.memoryForest).length := by
      rwa [E.execA.memory_bfs_length]
    unfold memoryLabelAt
    rw [dif_pos h, memoryNodeAt_row]
    have hrow :
        E.execA.memoryRowAt ⟨i - 1, h⟩ =
          NTree.label ((bfsForest E.execA.memoryForest)[i - 1]'(hlen)) := by
      simp [ExactExecution.memoryRowAt, ExactExecution.memoryRows,
        List.get_eq_getElem, List.getElem_map, Fin.cast]
    rw [hrow, List.getElem?_eq_getElem hlen]
    rfl
  · unfold memoryLabelAt
    rw [dif_neg h, memoryNodeAt_row]
    have hge : (bfsForest E.execA.memoryForest).length ≤ i - 1 := by
      rw [E.execA.memory_bfs_length]
      exact Nat.le_of_not_gt h
    rw [List.getElem?_eq_none hge]
    change E.execA.memoryRowAt ⟨0, E.cfg.memRows_pos⟩ = E.execA.memoryFallbackLabel
    have hne := E.execA.memoryForest_nonempty
    have h0 : (0 : ℕ) < E.execA.memoryForest.length :=
      List.length_pos_of_ne_nil hne
    have hb0 : (0 : ℕ) < (bfsForest E.execA.memoryForest).length := by
      rw [E.execA.memory_bfs_length]
      exact E.cfg.memRows_pos
    have hcons := bfsForest_cons_eq E.execA.memoryForest hne
    have hrow0 :
        E.execA.memoryRowAt ⟨0, E.cfg.memRows_pos⟩ =
          ((bfsForest E.execA.memoryForest)[0]'(hb0)).label := by
      simp [ExactExecution.memoryRowAt, ExactExecution.memoryRows,
        List.get_eq_getElem, List.getElem_map, Fin.cast]
    have hfb :
        E.execA.memoryFallbackLabel =
          (E.execA.memoryForest[0]'(h0)).label := by
      simp [ExactExecution.memoryFallbackLabel, List.get_eq_getElem]
    have hhead :
        (bfsForest E.execA.memoryForest)[0]'(hb0) =
          E.execA.memoryForest[0]'(h0) := by
      have hopt :
          (bfsForest E.execA.memoryForest)[0]? =
            E.execA.memoryForest[0]? := by
        rw [hcons, List.getElem?_append_left h0]
      rw [List.getElem?_eq_getElem hb0, List.getElem?_eq_getElem h0] at hopt
      exact Option.some.inj hopt
    exact hrow0.trans ((congrArg NTree.label hhead).trans hfb.symm)


def memoryForestOf (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) : List (NTree (MemoryNode K)) :=
  reconForest E.exec.memoryForest.length
    (foCol (bfsForest E.exec.memoryForest))
    (memoryLabelAt E M)
    (bfsForest E.exec.memoryForest).length

theorem memoryForestOf_length (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) :
    (memoryForestOf E M).length = E.exec.memoryForest.length := by
  simp [memoryForestOf, reconForest]


theorem memoryForestOf_rows (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) :
    (memoryForestOf E M).map (mapNTree MemoryNode.row) = E.execA.memoryForest := by
  -- The executed forest is the row encode of the a-bearing one: same shape.
  have hforest : E.exec.memoryForest =
      E.execA.memoryForest.map (mapNTree (MemoryRowTemplate.encodeRow E.cfg.challenges.lam)) := by
    rw [E.exec_encode]; rfl
  have hlen : E.exec.memoryForest.length = E.execA.memoryForest.length := by
    rw [hforest, List.length_map]
  have hbfs : bfsForest E.exec.memoryForest =
      (bfsForest E.execA.memoryForest).map (mapNTree (MemoryRowTemplate.encodeRow E.cfg.challenges.lam)) := by
    rw [hforest, bfsForest_mapNTree]
  have hfo : foCol (bfsForest E.exec.memoryForest) = foCol (bfsForest E.execA.memoryForest) := by
    funext i
    simp only [foCol, hbfs, List.getElem?_map, Option.map_map]
    congr 1
    cases (bfsForest E.execA.memoryForest)[i - 1]? <;> simp
  have hblen : (bfsForest E.exec.memoryForest).length =
      (bfsForest E.execA.memoryForest).length := by
    rw [hbfs, List.length_map]
  rw [memoryForestOf, mapNTree_reconForest, hlen, hfo, hblen]
  trans reconForest E.execA.memoryForest.length
      (foCol (bfsForest E.execA.memoryForest))
      (fun i =>
        (Option.map NTree.label (bfsForest E.execA.memoryForest)[i - 1]?).getD
          E.execA.memoryFallbackLabel)
      (bfsForest E.execA.memoryForest).length
  · congr 1
    funext i
    exact memoryLabelAt_row E M i
  · exact exact_reconForest_bfsForest E.execA.memoryForest
      E.execA.memoryForest_nonempty E.execA.memoryFallbackLabel


def memoryNodesOf (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) : List (NTree (MemoryNode K)) :=
  memoryForestOf E M

theorem memoryNodesOf_rows (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) :
    (memoryNodesOf E M).map (mapNTree MemoryNode.row) = E.execA.memoryForest :=
  memoryForestOf_rows E M

theorem memoryLabelAt_of_index (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) {i : ℕ}
    (hidx : i - 1 < E.cfg.memRows) :
    memoryLabelAt E M i = memoryNodeAt E M ⟨i - 1, hidx⟩ := by
  unfold memoryLabelAt
  rw [dif_pos hidx]


theorem memoryNodesOf_ok (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) :
    ∀ t ∈ memoryNodesOf E M,
      MemoryNodesOK E.cfg.challenges.z E.cfg.challenges.α t := by
  intro T hT u hu
  have htbfs : u ∈ bfsForest (memoryForestOf E M) :=
    (mem_bfsForest _ _).2 ⟨T, hT, hu⟩
  have hvalid := foCol_BFSValidF E.exec.memoryForest E.exec.memoryForest_nonempty
  have hSf := foCol_Sf_tilingF E.exec.memoryForest E.exec.memoryForest_nonempty
  have hk : 1 ≤ E.exec.memoryForest.length := by
    have := List.length_pos_of_ne_nil E.exec.memoryForest_nonempty
    omega
  have hbfs := bfsForest_reconForest
      (kroots := E.exec.memoryForest.length)
      (foCol (bfsForest E.exec.memoryForest))
      (memoryLabelAt E M)
      (bfsForest E.exec.memoryForest).length hk hSf hvalid
  unfold memoryNodesOf memoryForestOf at htbfs
  rw [hbfs, List.mem_map] at htbfs
  obtain ⟨i, hi, rfl⟩ := htbfs
  rw [List.mem_range'] at hi
  obtain ⟨k, hk', rfl⟩ := hi
  simp only [Nat.one_mul]
  have hi1 : 1 ≤ 1 + k := by omega
  have hih : 1 + k ≤ (bfsForest E.exec.memoryForest).length := by omega
  have hidx : k < E.cfg.memRows := by
    rw [← E.exec.memory_bfs_length]
    exact hk'
  have hlbl : memoryLabelAt E M (1 + k) = memoryNodeAt E M ⟨k, hidx⟩ := by
    have : (1 + k) - 1 = k := Nat.add_sub_cancel_left 1 k
    simpa [this] using memoryLabelAt_of_index E M (i := 1 + k)
      (by simpa [this] using hidx)
  have hchlen :
      (buildTF E.exec.memoryForest.length
          (foCol (bfsForest E.exec.memoryForest))
          (memoryLabelAt E M) (bfsForest E.exec.memoryForest).length (1 + k)).children.length =
        foCol (bfsForest E.exec.memoryForest) (1 + k) := by
    rw [buildTF_children, childIdxsF_eq (kroots := E.exec.memoryForest.length)
        _ _ hSf hvalid hi1 hih, List.length_map, List.length_range']
  have hlen : k < (bfsForest E.exec.memoryForest).length := hk'
  set orig := (bfsForest E.exec.memoryForest)[k]'hlen
  have horigMem : orig ∈ bfsForest E.exec.memoryForest := List.getElem_mem _
  have hin : ∃ root, root ∈ E.exec.memoryForest ∧ InTree root orig :=
    (mem_bfsForest _ _).1 horigMem
  obtain ⟨root, hroot, hin⟩ := hin
  have htop := E.traversal.2
  have hfan :=
    fanout_eq_children_length_of_properArity
      (MemoryTable.mem_stateSep (K := K)) (htop root hroot).1 (htop root hroot).2
      orig hin
  refine ⟨?fanout, ?st, ?bind, ?ts⟩
  · rw [buildTF_label, hchlen, hlbl]
    have hfo :
        foCol (bfsForest E.exec.memoryForest) (1 + k) = orig.children.length := by
      unfold foCol orig
      have : 1 + k - 1 = k := Nat.add_sub_cancel_left 1 k
      simp [this, List.getElem?_eq_getElem hlen]
    have hstate :
        (memoryNodeAt E M ⟨k, hidx⟩).skel.state = orig.label.1 := by
      simp [orig, memoryNodeAt, memorySkeletonOf,
        ExactExecution.memoryRowAt, ExactExecution.memoryRows,
        List.get_eq_getElem, List.getElem_map, Fin.cast]
    rw [hfo, hstate]
    exact hfan.symm
  · rw [buildTF_label, hlbl]
    exact memoryNodeAt_stamp_state E M ⟨k, hidx⟩
  · rw [buildTF_label, hlbl]
    exact memoryNodeAt_bind E M ⟨k, hidx⟩
  · rw [buildTF_label, hlbl]
    exact memoryNodeAt_specializes E M ⟨k, hidx⟩

/-! ## Remaining `Data` fields, named rather than bundled -/

/-- Memory-side committed nodes, now inhabited from `E` plus the two named
NMR extras in `MemoryRecordPremises`.  Halt atoms are `S_leaf := {halt}`
; `BindMemoryRow` and `MemoryTimestampSpecializesAt`
follow from public-row realization, `Vmem`, and the two extras. -/

structure MemoryAssemblyPremises (E : BuildableNockExecution F K) where
  memoryNodes : List (NTree (MemoryNode K))
  memory_rows :
    memoryNodes.map (mapNTree MemoryNode.row) = E.execA.memoryForest
  memoryOK :
    ∀ t ∈ memoryNodes, MemoryNodesOK E.cfg.challenges.z E.cfg.challenges.α t

/-- Inhabit the three-field memory bundle from the two named NMR extras. -/

def memoryAssemblyOf (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) : MemoryAssemblyPremises E where
  memoryNodes := memoryNodesOf E M
  memory_rows := memoryNodesOf_rows E M
  memoryOK := memoryNodesOf_ok E M

/-- Seed-independent census / window / bound obligations of `Data`
. `censusAssemblyOf` inhabits two of
those fields from `E` plus the reconstructed skeleton. -/
structure CensusAssemblyPremises (E : BuildableNockExecution F K)
    (computeNodes : NTree (ComputeNode K))
    (memoryNodes : List (NTree (MemoryNode K))) where
  nounSizeBound : ℕ
  slotSemantics :
    ∀ s ∈ computeSkeletonRows (skeletonOfNodes computeNodes memoryNodes),
      ServedLookupBridge.SkeletonSlotSemantics s
  recordEquations :
    ∀ s ∈ computeSkeletonRows (skeletonOfNodes computeNodes memoryNodes),
      ServedLookupBridge.SkeletonRecordEquations s
  census :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes computeNodes memoryNodes) E.Λ
  sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (skeletonOfNodes computeNodes memoryNodes) E.Λ
  skeletonBounded :
    (skeletonOfNodes computeNodes memoryNodes).BoundedBy E.q
  combinedBounded :
    ProductionP8Containment.CombinedBoundedBy K E.q
      (skeletonOfNodes computeNodes memoryNodes)

/-! ## Record equations by construction; remaining census extras named
 -/


theorem computeNodesOf_bfs_labels (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    (bfsForest [computeNodesOf E P]).map NTree.label =
      (List.range' 1 (bfsForest [E.exec.computeTree]).length).map
        (computeLabelAt E P) := by
  have hsing := computeForestOf_eq_singleton E P
  have hvalid := foCol_BFSValidF [E.exec.computeTree] (List.cons_ne_nil _ _)
  have hSf := foCol_Sf_tilingF [E.exec.computeTree] (List.cons_ne_nil _ _)
  rw [← hsing]
  exact reconForest_labels 1
    (foCol (bfsForest [E.exec.computeTree]))
    (computeLabelAt E P)
    (bfsForest [E.exec.computeTree]).length (Nat.le_refl 1) hSf hvalid


theorem computeSkeletonRows_of_assembly (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E) :
    computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) =
      (List.range' 1 (bfsForest [E.exec.computeTree]).length).map
        (fun i => (computeLabelAt E P i).skel) := by
  simp only [computeSkeletonRows, skeletonOfNodes]
  rw [show [mapNTree ComputeNode.skel (computeNodesOf E P)] =
        [computeNodesOf E P].map (mapNTree ComputeNode.skel) from rfl,
    bfsForest_mapNTree, List.map_map]
  calc
    (bfsForest [computeNodesOf E P]).map (NTree.label ∘ mapNTree ComputeNode.skel) =
        (bfsForest [computeNodesOf E P]).map (fun t => t.label.skel) := by
      refine List.map_congr_left fun t _ => mapNTree_label ComputeNode.skel t
    _ = ((bfsForest [computeNodesOf E P]).map NTree.label).map ComputeNode.skel := by
      rw [List.map_map]
      rfl
    _ = ((List.range' 1 (bfsForest [E.exec.computeTree]).length).map
          (computeLabelAt E P)).map ComputeNode.skel := by
      rw [computeNodesOf_bfs_labels E P]
    _ = (List.range' 1 (bfsForest [E.exec.computeTree]).length).map
          (fun i => (computeLabelAt E P i).skel) := by
      rw [List.map_map]
      rfl


theorem computeSkeletonOf_recordEquations {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    ServedLookupBridge.SkeletonRecordEquations (computeSkeletonOf data pubR) where
  s0_record := by
    intro h
    have hstate : row.1 = .s0 := h
    simp [computeSkeletonOf, memRecSkelOf, hstate]
  s9_record := by
    intro h
    have hstate : row.1 = .s9 := h
    simp [computeSkeletonOf, memRecSkelOf, P8Census.skeletonSubformula, hstate,
      ComputeTable.fanoutComp]


theorem recordEquations_of_assembly (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      ServedLookupBridge.SkeletonRecordEquations s := by
  intro s hs
  rw [computeSkeletonRows_of_assembly E P M] at hs
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
  rw [List.mem_range'] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  simp only [Nat.one_mul]
  have hidx : k < E.cfg.compRows := by
    rw [← E.exec.compute_bfs_length]
    exact hk
  have hlbl : computeLabelAt E P (1 + k) = computeNodeAt E P ⟨k, hidx⟩ := by
    have : (1 + k) - 1 = k := Nat.add_sub_cancel_left 1 k
    simpa [this] using computeLabelAt_of_index E P (i := 1 + k)
      (by simpa [this] using hidx)
  rw [hlbl, computeNodeAt, computeNodeOf]
  exact computeSkeletonOf_recordEquations (E.semanticData.rows ⟨k, hidx⟩)
    (publicRowNoun_of_execution E ⟨k, hidx⟩)

/-! ## Memory-row `q`-boundedness from public-row existence

`chooseNoun` of `FPRealized` carries `BoundedBy q`.  Halt atoms are
`S_leaf := {halt}` with `k < E.q`.  Compute-row
decomposition nouns remain `Realizes`-only (`decompNoun_realizes_active`)
and stay outside this derivation. -/


theorem memoryParentNoun_bounded (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) :
    FieldEmbedding.BoundedBy E.q (memoryParentNoun E i) := by
  by_cases hhalt : (E.exec.memoryRowAt i).1 = .halt
  · have h := haltAtomVal_spec E i hhalt
    simpa [memoryParentNoun_halt E i hhalt] using h.1
  · simp [memoryParentNoun, hhalt]
    exact chooseNoun_bounded (memoryPublicRowNoun_of_execution E i).parent.1


theorem memoryChildNoun_bounded (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows) (j : Fin 2)
    (hj : (j : ℕ) < MemoryTable.fanoutMem (E.exec.memoryRowAt i).1) :
    FieldEmbedding.BoundedBy E.q (memoryChildNoun E i j hj) := by
  let pubR := memoryPublicRowNoun_of_execution E i
  have hkind : memoryChildKind (E.exec.memoryRowAt i).1 j = .active := by
    simp [memoryChildKind, hj]
  have hcell :
      MemoryCellSlotRealized (E.exec.memoryRowAt i).2.1.z E.q .active
        (memoryChildCell (E.exec.memoryRowAt i).2.2 j) :=
    hkind ▸ pubR.child j
  simp [memoryChildNoun]
  exact chooseNoun_bounded (fpSlot_active_realized hcell)


theorem memoryMemRecSkel_bounded (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : Fin E.cfg.memRows)
    (hact : memoryMemRecKind (E.exec.memoryRowAt i).1 = .active) :
    (memoryMemRecSkel E M i hact).BoundedBy E.q := by
  let pubR := memoryPublicRowNoun_of_execution E i
  have hmr := hact ▸ pubR.memoryRecord
  simp [memoryMemRecSkel]
  exact ⟨chooseNoun_bounded hmr.2.1.1, chooseNoun_bounded hmr.2.2.1⟩


theorem memorySkeletonOf_bounded (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : Fin E.cfg.memRows) :
    (memorySkeletonOf E M i).BoundedBy E.q :=
  ⟨memoryParentNoun_bounded E i,
    fun j hj => memoryChildNoun_bounded E i j hj,
    fun hact => memoryMemRecSkel_bounded E M i hact⟩

theorem memoryLabelAt_bounded (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) (i : ℕ) :
    (memoryLabelAt E M i).skel.BoundedBy E.q := by
  unfold memoryLabelAt
  split_ifs with h
  · exact memorySkeletonOf_bounded E M ⟨i - 1, h⟩
  · exact memorySkeletonOf_bounded E M ⟨0, E.cfg.memRows_pos⟩


theorem memoryNodesOf_bfs_labels (E : BuildableNockExecution F K)
    (M : MemoryRecordPremises E) :
    (bfsForest (memoryForestOf E M)).map NTree.label =
      (List.range' 1 (bfsForest E.exec.memoryForest).length).map
        (memoryLabelAt E M) := by
  have hvalid := foCol_BFSValidF E.exec.memoryForest E.exec.memoryForest_nonempty
  have hSf := foCol_Sf_tilingF E.exec.memoryForest E.exec.memoryForest_nonempty
  have hk : 1 ≤ E.exec.memoryForest.length := by
    have := List.length_pos_of_ne_nil E.exec.memoryForest_nonempty
    omega
  exact reconForest_labels E.exec.memoryForest.length
    (foCol (bfsForest E.exec.memoryForest))
    (memoryLabelAt E M)
    (bfsForest E.exec.memoryForest).length hk hSf hvalid


theorem memorySkeletonRows_of_assembly (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E) :
    memorySkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) =
      (List.range' 1 (bfsForest E.exec.memoryForest).length).map
        (fun i => (memoryLabelAt E M i).skel) := by
  simp only [memorySkeletonRows, skeletonOfNodes, memoryNodesOf]
  rw [bfsForest_mapNTree, List.map_map]
  calc
    (bfsForest (memoryForestOf E M)).map
          (NTree.label ∘ mapNTree MemoryNode.skel) =
        (bfsForest (memoryForestOf E M)).map (fun t => t.label.skel) := by
      refine List.map_congr_left fun t _ => mapNTree_label MemoryNode.skel t
    _ = ((bfsForest (memoryForestOf E M)).map NTree.label).map
          MemoryNode.skel := by
      rw [List.map_map]
      rfl
    _ = ((List.range' 1 (bfsForest E.exec.memoryForest).length).map
          (memoryLabelAt E M)).map MemoryNode.skel := by
      rw [memoryNodesOf_bfs_labels E M]
    _ = (List.range' 1 (bfsForest E.exec.memoryForest).length).map
          (fun i => (memoryLabelAt E M i).skel) := by
      rw [List.map_map]
      rfl


theorem memorySkeletonRows_bounded (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E) :
    (memorySkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))).Forall
      (MemoryRowSkeleton.BoundedBy E.q) := by
  rw [List.forall_iff_forall_mem]
  intro s hs
  rw [memorySkeletonRows_of_assembly E P M] at hs
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
  exact memoryLabelAt_bounded E M i


theorem memoryTrees_bounded (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E) :
    ∀ tree ∈ (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).memoryForest,
      ∀ node, InTree tree node → node.label.BoundedBy E.q := by
  intro tree htree node hnode
  have hmem : node ∈ bfsForest
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).memoryForest :=
    (mem_bfsForest _ _).2 ⟨tree, htree, hnode⟩
  have hlab : node.label ∈ memorySkeletonRows
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) :=
    List.mem_map.mpr ⟨node, hmem, rfl⟩
  exact (List.forall_iff_forall_mem.mp (memorySkeletonRows_bounded E P M))
    node.label hlab

/-! ## Compute-side partial `q`-bounds; remaining census extras named
 -/


theorem computeSkeletonOf_root_bounded {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row)) :
    FieldEmbedding.BoundedBy q (computeSkeletonOf data pubR).subject ∧
      FieldEmbedding.BoundedBy q (computeSkeletonOf data pubR).formula ∧
      FieldEmbedding.BoundedBy q (computeSkeletonOf data pubR).evaluation := by
  simpa [computeSkeletonOf] using data.root_bounded


theorem computeSkeletonOf_subformula_bounded {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp row.1)
    (slot : TripleSlot) :
    FieldEmbedding.BoundedBy q
      ((computeSkeletonOf data pubR).subformula i hi slot) := by
  simpa [computeSkeletonOf] using subformulaNounOf_bounded data pubR i hi slot

/-- `needs.served` supplies a served lookup of *some* nouns at OP0.  It does
not identify them with the reconstructed skeleton. -/

theorem served_lookup_of_s0_needs {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) (h : row.1 = .s0) :
    ∃ lookup ∈ data.needs.served,
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun lookup.root 1) lookup.axis lookup.child := by
  have hlen : data.needs.served.length = 1 := by
    rw [data.needs.served_count]
    simp [requiredServedLookups, h]
  have hne : data.needs.served ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  exact ⟨data.needs.served.head hne, List.head_mem hne,
    (data.needs.served.head hne).served⟩

/-- `needs.served` supplies a served lookup of *some* nouns at OP9. -/

theorem served_lookup_of_s9_needs {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) (h : row.1 = .s9) :
    ∃ lookup ∈ data.needs.served,
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun lookup.root 1) lookup.axis lookup.child := by
  have hlen : data.needs.served.length = 1 := by
    rw [data.needs.served_count]
    simp [requiredServedLookups, h]
  have hne : data.needs.served ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  exact ⟨data.needs.served.head hne, List.head_mem hne,
    (data.needs.served.head hne).served⟩

/-- The exact missing OP0 identification: served nouns equal the reconstructed
skeleton's subject, `mr2` axis, and evaluation. -/

theorem skeletonSlotSemantics_of_s0_identification {z : K}
    (s : ComputeRowSkeleton) (lookup : ServedNounLookup z)
    (hstate : s.state = .s0) (hroot : lookup.root = s.subject)
    (haxis : lookup.axis = P8Census.skeletonMemoryAxis s 1)
    (hchild : lookup.child = s.evaluation) :
    ServedLookupBridge.SkeletonSlotSemantics s :=
    ServedLookupBridge.skeletonSlotSemantics_of_served
      (fun _ => hroot ▸ haxis ▸ hchild ▸ lookup.served)
      (fun h9 => nomatch hstate.symm.trans h9)

/-- The exact missing OP9 identification. -/

theorem skeletonSlotSemantics_of_s9_identification {z : K}
    (s : ComputeRowSkeleton) (lookup : ServedNounLookup z)
    (hstate : s.state = .s9)
    (hroot : lookup.root = P8Census.skeletonSubformula s 0 .result)
    (haxis : lookup.axis = P8Census.skeletonMemoryAxis s 2)
    (hchild : lookup.child = P8Census.skeletonSubformula s 1 .formula) :
    ServedLookupBridge.SkeletonSlotSemantics s :=
    ServedLookupBridge.skeletonSlotSemantics_of_served
      (fun h0 => nomatch hstate.symm.trans h0)
      (fun _ => hroot ▸ haxis ▸ hchild ▸ lookup.served)

/-- Skeleton-projected OP1 comparisons are `decompNoun`/`root` nouns, not the
free `data.comparisons` list. -/

theorem computeSkeletonOf_s1_skeletonComparisons {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s1) :
    P8Census.skeletonComparisons (K := K) (computeSkeletonOf data pubR) =
      [P8Census.skeletonUse .opcodeHead data.root.head (.atom 1),
        P8Census.skeletonUse .formulaCons data.root.formula
          (.cell data.root.head data.root.tail),
        P8Census.skeletonUse .producedResult data.root.result data.root.tail] := by
  simp [P8Census.skeletonComparisons, computeSkeletonOf, P8Census.skeletonDec,
    P8Census.skeletonUse, SemanticStrategy.decActive, decompNoun, h]

/-- Size-window extra is a leaf bound against `Λ`.  `SizeWindow` is an order
bound at the sampled seed. -/

theorem sizeWindow_is_order_bound {z : K} {n : Noun}
    (hw : OpcodeSemantics.SizeWindow z n) :
    n.leaves < orderOf z :=
  hw.leaves_lt_order

/-- `AxisAtomPremises` is atom *shape*, not `atomVal < q`.
Cite repaired: `1737` alone is `ln = ln_prev · z³`; the OP₉ axis fact is
`1738`. -/

theorem axisAtomPremises_are_shape {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    {data : ComputeRowSemanticData q Λ row} (h : AxisAtomPremises data) :
    (row.1 = .s0 → ∃ k, data.root.tail = .atom k) ∧
      (row.1 = .s9 → ∃ k, decompNoun data .f_th = .atom k) :=
  h

/-- Opcode-9 census pairs include `.atom 9`.  `E.q_gt_one` is only `1 < q`, so
combined boundedness is not a consequence of that field. -/

theorem atom_nine_not_bounded_by_two :
    ¬ FieldEmbedding.BoundedBy 2 (.atom 9) := by
  simp

/-- Remaining paper-named census extras after record equations, the committed
leaf-window numeral, and memory-row `q`-boundedness are assembled.  Served
`OP_0`/`OP_9` slot *identification* is not a `needs.served` length fact
.  NPR comparison and size-window leaf bounds are the
paper `Λ` window on skeleton projections; compute-row
atom `q`-boundedness of decomposition nouns and census-pair opcode/axis atoms
is not supplied by `realizedNouns` or memory `chooseNoun`.  None of these is
`True`. -/

structure CensusRecordPremises (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E) where
  slotSemantics :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      ServedLookupBridge.SkeletonSlotSemantics s
  census :
    EdgeComparisonCensus.CombinedSkeletonCensus K
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ
  sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ
  skeletonBounded :
    (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q
  combinedBounded :
    ProductionP8Containment.CombinedBoundedBy K E.q
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))

/-- Inhabit the seven-field census bundle: `nounSizeBound` is `E.Λ`,
record equations are the reconstructed `memRecSkelOf` identities, and the
five remaining extras are copied from `CensusRecordPremises`. -/

def censusAssemblyOf (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    CensusAssemblyPremises E (computeNodesOf E P) (memoryNodesOf E M) where
  nounSizeBound := E.Λ
  slotSemantics := C.slotSemantics
  recordEquations := recordEquations_of_assembly E P M
  census := C.census
  sizeWindowBound := C.sizeWindowBound
  skeletonBounded := C.skeletonBounded
  combinedBounded := C.combinedBounded

/-- `ResidualPremises` has three named fields after `firstLine` left the structure. -/
theorem residualPremises_still_four {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestCommitment.residualPremises_still_four P

/-- `firstLine` is first compute-row `ln_prev = 1`, not walk RAP `ln(1)=α`.
-- analog, 1813 -/
theorem firstLine_is_compute_ln_prev_eq_one
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    FirstLineStartsAtOne exec ↔
      (exec.computePubAt ⟨0, cfg.compRows_pos⟩).ln_prev = 1 :=
  Iff.rfl

/-- Paper walk initial line.  Distinct from `firstLine`.
-- -/
theorem walkSat_ln1_is_sampled_alpha
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ln 1 = α :=
  hw.ln1

/-- Walk starts at `α^1`; the compute first-row analog is `α^0 = 1`.
-- analog, 1813 -/
theorem walk_ln1_is_alpha_pow_one
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed initial_count : K} {h : ℕ}
    (hw : WalkSat cur chld' fo ln count acc α seed initial_count h) :
    ln 1 = α ^ 1 := by
  rw [pow_one]
  exact hw.ln1

/-- The two right-hand sides differ whenever `α ≠ 1`.  Not an inhabit of
`firstLine` from walk RAP. -- the paper analog, 1813 -/
theorem walk_alpha_ne_compute_one {α : K} (hα : α ≠ 1) :
    α ^ 1 ≠ (1 : K) := by
  simpa [pow_one] using hα

/-- `V_comp` does not pin first-row `ln_prev`. -- the paper -/
theorem firstLine_of_residual
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    E.q = ringChar K :=
  P.q_eq_ringChar

/-- Residual extra is the execution pin `E.q = ringChar K`.
Paper `|F|=p=char(K)`, not `|K|=p³`. -- the paper -/
theorem residual_q_eq_ringChar_is_equality
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    E.q = ringChar K :=
  P.q_eq_ringChar

/-- Already-held on `E`: `1 < q ≤ ringChar`.  No equality field.
-- -/
theorem execution_already_held_is_q_le
    (E : BuildableNockExecution F K) :
    1 < E.q ∧ E.q ≤ ringChar K :=
  ⟨E.q_gt_one, E.q_le_ringChar⟩

/-- `11 < char` plus `1 < q ≤ char` does not force `q = char`.
-- -/
theorem eleven_lt_and_q_le_do_not_give_q_eq :
    ¬ ∀ (q n : ℕ), 11 < n → 1 < q → q ≤ n → q = n := by
  intro h
  have : (12 : ℕ) = 73 := h 12 73 (by omega) (by omega) (by omega)
  omega

/-- Transporting `11 < ringChar` to `11 < E.q` needs equality, not `q ≤ char`.
-- -/
theorem eleven_lt_char_does_not_give_eleven_lt_q :
    ¬ ∀ (q n : ℕ), 11 < n → q ≤ n → 11 < q := by
  intro h
  have : 11 < 2 := h 2 73 (by omega) (by omega)
  omega

/-- `MemoryRecordPremises` is the two named NMR extras, not a vacuous wrapper. -/

theorem memoryRecordPremises_still_two {E : BuildableNockExecution F K}
    (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨M.axisNat, M.timestampClosed⟩

/-- `CensusRecordPremises` is the five remaining named extras, not a vacuous
wrapper.  Record equations and `nounSizeBound` are not among them. -/

theorem censusRecordPremises_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    (∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      ServedLookupBridge.SkeletonSlotSemantics s) ∧
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ ∧
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q ∧
      ProductionP8Containment.CombinedBoundedBy K E.q
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) :=
  ⟨C.slotSemantics, C.census, C.sizeWindowBound, C.skeletonBounded,
    C.combinedBounded⟩

theorem censusAssemblyOf_nounSizeBound (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).nounSizeBound = E.Λ :=
  rfl

theorem censusAssemblyOf_recordEquations (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).recordEquations =
      recordEquations_of_assembly E P M :=
  rfl

/-- Named-premises `Data` constructor.

Compute nodes, `compute_rows`, and `computeOK` are assembled from `E` plus
the four `ResidualPremises`.  Memory nodes, `memory_rows`, and `memoryOK`
are assembled from `E` plus the two named NMR extras via `memoryAssemblyOf`
(`Def:NMR` the paper, closed-form timestamps the paper); halt
atoms are `S_leaf := {halt}` already on `E`.  `Λ` is
`E.Λ`.  `q_eq_ringChar` is `P.q_eq_ringChar`.  Record equations are
assembled by construction; `nounSizeBound` is
`E.Λ`.  Memory-row `q`-boundedness is derived.
Slot identification, the NPR census and size-window
leaf bounds, and compute-row decomposition
boundedness stay named extras.  Census-pair `combinedBounded` is inhabited
at consumed `q` from named `skeletonBounded`.
No `∀ E, Data E` and no later-round `A`/`W`. -/

def dataOf (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : FirstLineStartsAtOne E.exec) :
    Data E where
  computeNodes := computeNodesOf E P
  memoryNodes := M.memoryNodes
  compute_rows := computeNodesOf_rows E P
  memory_rows := M.memory_rows
  computeOK := computeNodesOf_ok E P
  memoryOK := M.memoryOK
  root_line_exponent := computeNodesOf_root_line_exponent E P
  root_line_origin := by rw [computeNodesOf_label]; exact hln
  nounSizeBound := C.nounSizeBound
  Λ := E.Λ
  slotSemantics := C.slotSemantics
  recordEquations := C.recordEquations
  census := C.census
  sizeWindowBound := C.sizeWindowBound
  q_eq_ringChar := P.q_eq_ringChar
  skeletonBounded := C.skeletonBounded
  combinedBounded := C.combinedBounded

/-- Convenience: `Data` from residual premises plus the two NMR extras
and the still-named census bundle. -/

def dataOfRecord (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) (memoryNodesOf E M))
    (hln : FirstLineStartsAtOne E.exec) :
    Data E :=
  dataOf E P (memoryAssemblyOf E M) C hln

theorem dataOf_retains_named_equality
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).q_eq_ringChar = P.q_eq_ringChar :=
  rfl

theorem dataOfRecord_memory_is_assembled
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) (memoryNodesOf E M))
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOfRecord E P M C hln).memoryNodes = memoryNodesOf E M ∧
      (dataOfRecord E P M C hln).memory_rows = memoryNodesOf_rows E M ∧
      (dataOfRecord E P M C hln).memoryOK = memoryNodesOf_ok E M :=
  ⟨rfl, rfl, rfl⟩

/-- Convenience: `Data` from residual premises, the two NMR extras, and the
five remaining named census extras.  Record equations and `nounSizeBound`
are assembled.  `combinedBounded` may be filled by
`censusRecordPremises_of_skeletonBounded` at consumed `q`. -/

def dataOfCensus (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M)
    (hln : FirstLineStartsAtOne E.exec) :
    Data E :=
  dataOfRecord E P M (censusAssemblyOf E P M C) hln

theorem dataOfCensus_derived_fields (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (C : CensusRecordPremises E P M)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOfCensus E P M C hln).nounSizeBound = E.Λ ∧
      (dataOfCensus E P M C hln).recordEquations =
        recordEquations_of_assembly E P M ∧
      (dataOfCensus E P M C hln).Λ = E.Λ :=
  ⟨rfl, rfl, rfl⟩

/-- Outcome 2: no constructor `∀ E, Data E`. -/
theorem generic_data_would_force_q_equality
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

/-! ## `slotSemantics` does not follow from `needs.served` /
record equations / NMR `axisNat` / the paper `\(1,n)=n` base case

The NMR slot text defines the Nock `/` operator:
OP0 looks up `\(n_2,n_1)`, the root axis is `1` so `\(1,n_1)=n_1`, and
children are `2·axis` / `2·axis+1`.  The Lean extra
`CensusRecordPremises.slotSemantics` is not that definition: it is the
OP0/OP9 instance `Noun.slot axis subject = some evaluation` on the
reconstructed compute skeleton (`ServedLookupBridge.SkeletonSlotSemantics`).
`needs.served` supplies a `ServedLookup` of *some* nouns.  The paper base
case inhabits that lookup at axis `1` for every noun, without identifying
the skeleton `mr2` axis or evaluation.  Assembled record equations are
root/child identities, not `/`.  NMR `axisNat` is a memory-table Nat-cast
(`Def:NMR` the paper), not a compute-skeleton `/` fact. -/

/-- The named extra expands to the OP0/OP9 `/` facts on a compute skeleton
row, not `True` and not the NMR address-space Nat-cast.
-- -/
theorem slotSemantics_is_noun_slot
    (s : ComputeRowSkeleton)
    (h : ServedLookupBridge.SkeletonSlotSemantics s) :
    (s.state = .s0 →
      Noun.slot (P8Census.skeletonMemoryAxis s 1) s.subject =
        some s.evaluation) ∧
      (s.state = .s9 →
        Noun.slot (P8Census.skeletonMemoryAxis s 2)
          (P8Census.skeletonSubformula s 0 .result) =
            some (P8Census.skeletonSubformula s 1 .formula)) :=
  ⟨h.s0_slot, h.s9_slot⟩

/-- Paper base case: `\(1, n_1) = n_1` for every noun.  This inhabits a
`ServedLookup` without identifying the reconstructed skeleton.
-- -/
theorem served_lookup_of_axis_one (n : Noun) :
    GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun n 1) 1 n :=
  RecognizerCompleteness.servedLookup_root n

/-- NMR `axisNat` is a live *memory-table* address as a Nat-cast into the
field.  It does not mention `Noun.slot` or a compute-skeleton row.
-- -/
theorem axisNat_is_memory_table_nat_cast
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  M.axisNat

/-- `censusAssemblyOf` still copies `slotSemantics` from the named extra.
-- -/
theorem censusAssemblyOf_copies_slotSemantics
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).slotSemantics = C.slotSemantics :=
  rfl

/-- **Missing hypothesis.**  A served lookup inhabits OP0
`SkeletonSlotSemantics` only after identification with the reconstructed
skeleton's subject, `mr2` axis, and evaluation.  `needs.served` length,
the paper `\(1,n)=n` base case, assembled record equations, and NMR
`axisNat` do not supply those equalities. -- the paper -/
theorem slotSemantics_of_s0_served_and_identification {z : K}
    (s : ComputeRowSkeleton) (lookup : ServedNounLookup z)
    (hstate : s.state = .s0) (hroot : lookup.root = s.subject)
    (haxis : lookup.axis = P8Census.skeletonMemoryAxis s 1)
    (hchild : lookup.child = s.evaluation) :
    ServedLookupBridge.SkeletonSlotSemantics s :=
  skeletonSlotSemantics_of_s0_identification s lookup hstate hroot haxis
    hchild

/-- Explicit OP0 row whose `mr2` axis is `2` and whose subject is an atom.
Record equations hold; `/[2, atom 0]` is `none`. -- the paper -/
def s0SlotFailRow : ComputeRowSkeleton where
  state := .s0
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 2)
  evaluation := .atom 1
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun i _ =>
    if (i : ℕ) = 1 then
      ⟨.atom 0, .atom 1, 2⟩
    else
      ⟨.atom 0, .atom 2, 3⟩

theorem s0SlotFailRow_axis :
    P8Census.skeletonMemoryAxis s0SlotFailRow 1 = 2 := by
  simp [P8Census.skeletonMemoryAxis, s0SlotFailRow,
    Nock.Framework.recordCount]

theorem s0SlotFailRow_recordEquations :
    ServedLookupBridge.SkeletonRecordEquations s0SlotFailRow where
  s0_record := by
    intro _
    simp [s0SlotFailRow]
  s9_record := by
    intro h
    cases h

/-- The same row fails the named `/` extra: `/[2, atom 0]` is `none`.
-- -/
theorem s0SlotFailRow_slot_ne :
    Noun.slot (P8Census.skeletonMemoryAxis s0SlotFailRow 1)
      s0SlotFailRow.subject ≠ some s0SlotFailRow.evaluation := by
  rw [s0SlotFailRow_axis]
  simp [s0SlotFailRow, Noun.slot]

theorem slotSemantics_fails_of_atom_subject_axis_two :
    ¬ ServedLookupBridge.SkeletonSlotSemantics s0SlotFailRow := by
  intro h
  exact s0SlotFailRow_slot_ne (h.s0_slot rfl)

/-- Paper `\(1,n_1)=n_1` still inhabits a served lookup on that subject.
-- -/
theorem served_lookup_axis_one_holds_on_fail_subject :
    GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun s0SlotFailRow.subject 1) 1
      s0SlotFailRow.subject :=
  served_lookup_of_axis_one _

/-- Combined: assembled-style record equations hold, the paper axis-1
base case holds, and the named extra fails.  The missing identification
is therefore extra. -- the paper -/
theorem slotSemantics_does_not_follow_from_records_or_axis_one :
    ServedLookupBridge.SkeletonRecordEquations s0SlotFailRow ∧
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun s0SlotFailRow.subject 1) 1
        s0SlotFailRow.subject ∧
      ¬ ServedLookupBridge.SkeletonSlotSemantics s0SlotFailRow :=
  ⟨s0SlotFailRow_recordEquations,
    served_lookup_axis_one_holds_on_fail_subject,
    slotSemantics_fails_of_atom_subject_axis_two⟩

/-- Concrete nonempty skeleton whose unique compute row is that OP0 atom.
-- -/
def s0SlotFailSkeleton : SemanticSkeleton where
  computeTree := .node s0SlotFailRow []
  memoryForest := []

theorem s0SlotFailSkeleton_computeRows :
    computeSkeletonRows s0SlotFailSkeleton = [s0SlotFailRow] := by
  unfold computeSkeletonRows s0SlotFailSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- The consumed `∀ s ∈ computeSkeletonRows` extra fails on this skeleton.
-- -/
theorem slotSemantics_forall_fails_on_atom_axis_two :
    ¬ ∀ s ∈ computeSkeletonRows s0SlotFailSkeleton,
        ServedLookupBridge.SkeletonSlotSemantics s := by
  intro h
  rw [s0SlotFailSkeleton_computeRows] at h
  exact slotSemantics_fails_of_atom_subject_axis_two (h _ (by simp))

/-! ## `census` does not follow from `nounSizeBound` / record
equations / free `comparison_leaves` / the paper `Λ` window definition

The paper census CORE (`Lem:ion_univariate_sec`, `Corr:ion_single_security`) is collision soundness for a list of nouns of length
at most `Λ`.  The Lean extra `CensusRecordPremises.census` is not that
definition: it is `CombinedSkeletonCensus` on the reconstructed skeleton —
leaf bounds on `skeletonPairs` (public-claim self-pairs plus
`P8Census.skeletonComparisons`) and parent-child `edgePairs`.
`nounSizeBound = E.Λ` is the already-assembled numeral, not a leaf proof.
Assembled record equations are `memRecSkelOf` identities
.  `data.comparison_leaves` bounds the free
role-matching `data.comparisons` list, which the earlier analysis already compiled is not
the skeleton projection.  SizeWindow (`n.leaves ≤ Λ` on OP3/OP4/OP6
products) is a different extra and is not swallowed. -/

/-- The named extra expands to P8-pair and edge leaf bounds on the
reconstructed skeleton, not `True` and not `data.comparison_leaves`.
-- -/
theorem census_is_skeleton_pair_leaf_bounds
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (∀ pair ∈ BoundSemanticTrace.skeletonPairs K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      pair.1.leaves ≤ E.Λ ∧ pair.2.leaves ≤ E.Λ) ∧
      (∀ pair ∈ EdgeComparisonCensus.edgePairs
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).computeTree,
        pair.1.leaves ≤ E.Λ ∧ pair.2.leaves ≤ E.Λ) :=
  ⟨C.census.p8.leaves_bounded, C.census.edges.leaves_bounded⟩

/-- `censusAssemblyOf` still copies `census` from the named extra.
-- -/
theorem censusAssemblyOf_copies_census
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).census = C.census :=
  rfl

/-- `data.comparison_leaves` bounds the free role-matching list, not
`skeletonComparisons`. -- the paper -/
theorem comparison_leaves_quantify_data_comparisons
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row) :
    (∀ c ∈ data.comparisons, c.LeavesBounded Λ) ∧
      data.comparisons.map ComparisonUse.role = requiredComparisonRoles row.1 :=
  ⟨data.comparison_leaves, data.comparison_roles⟩

/-- **Missing hypothesis.**  Leaf bounds on the reconstructed
`skeletonComparisons` list, the public-claim root nouns, and the
parent-child edge pairs inhabit `CombinedSkeletonCensus`.  Free
`data.comparison_leaves`, the numeral `nounSizeBound = E.Λ`, assembled
record equations, and the paper `Λ` window definition do not supply those
skeleton-projected bounds.  SizeWindow is not weakened.
-- -/
theorem census_of_identified_skeleton_pairs
    {S : SemanticSkeleton} {Λ : ℕ}
    (hrows : ∀ s ∈ computeSkeletonRows S,
      ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ)
    (hroot :
      S.computeTree.label.subject.leaves ≤ Λ ∧
        S.computeTree.label.formula.leaves ≤ Λ ∧
          S.computeTree.label.evaluation.leaves ≤ Λ)
    (hedges : ∀ pair ∈ EdgeComparisonCensus.edgePairs S.computeTree,
      pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ) :
    EdgeComparisonCensus.CombinedSkeletonCensus K S Λ := by
  refine ⟨⟨?_⟩, ⟨hedges⟩⟩
  intro pair hp
  unfold BoundSemanticTrace.skeletonPairs at hp
  rw [List.mem_append] at hp
  cases hp with
  | inl hp =>
      simp [SemanticSkeleton.publicClaim] at hp
      obtain rfl | rfl | rfl := hp
      · exact ⟨hroot.1, hroot.1⟩
      · exact ⟨hroot.2.1, hroot.2.1⟩
      · exact ⟨hroot.2.2, hroot.2.2⟩
  | inr hp =>
      rw [List.mem_map] at hp
      obtain ⟨c, hc, rfl⟩ := hp
      rw [P8Census.skeletonComparisonCensus, List.mem_flatMap] at hc
      obtain ⟨s, hs, hcs⟩ := hc
      exact hrows s hs c hcs

/-- Explicit OP1 row whose formula is a two-leaf cell.  Record equations
hold (the row is not OP0/OP9).  The named census extra at `Λ = 1` fails
because that formula has two leaves. -- the paper -/
def s1CensusFailRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 0)
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

theorem s1CensusFailRow_formula_leaves :
    s1CensusFailRow.formula.leaves = 2 := by
  simp only [s1CensusFailRow]
  rfl

theorem s1CensusFailRow_recordEquations :
    ServedLookupBridge.SkeletonRecordEquations s1CensusFailRow where
  s0_record := by
    intro h
    cases h
  s9_record := by
    intro h
    cases h

/-- A free role-matching OP1 comparison list of one-leaf atoms.  This is
the `data.comparisons` shape: roles match, leaves `≤ 1`, nouns are not
the reconstructed formula cell. -- the paper -/
def s1FreeComparisons : List ComparisonUse :=
  [P8Census.skeletonUse .opcodeHead (.atom 0) (.atom 1),
    P8Census.skeletonUse .formulaCons (.atom 0) (.atom 0),
    P8Census.skeletonUse .producedResult (.atom 0) (.atom 0)]

theorem s1FreeComparisons_roles :
    s1FreeComparisons.map ComparisonUse.role = requiredComparisonRoles .s1 := by
  simp [s1FreeComparisons, P8Census.skeletonUse, requiredComparisonRoles]

theorem s1FreeComparisons_leaves_le_one :
    ∀ c ∈ s1FreeComparisons, c.LeavesBounded 1 := by
  intro c hc
  simp [s1FreeComparisons, P8Census.skeletonUse] at hc
  obtain rfl | rfl | rfl := hc
  · simp [ComparisonUse.LeavesBounded, Noun.leaves]
  · simp [ComparisonUse.LeavesBounded, Noun.leaves]
  · simp [ComparisonUse.LeavesBounded, Noun.leaves]

/-- The free list is not the reconstructed `skeletonComparisons` list.
The formulaCons left noun is `.atom 0` on the free list and the two-leaf
cell on the skeleton. -- the paper -/
theorem s1FreeComparisons_ne_skeletonComparisons :
    s1FreeComparisons ≠
      P8Census.skeletonComparisons (K := K) s1CensusFailRow := by
  intro h
  have hf :
      (s1FreeComparisons[1]?.map ComparisonUse.left) =
        ((P8Census.skeletonComparisons (K := K) s1CensusFailRow)[1]?.map
          ComparisonUse.left) :=
    congrArg (fun cs => cs[1]?.map ComparisonUse.left) h
  simp [s1FreeComparisons, P8Census.skeletonUse, P8Census.skeletonComparisons,
    s1CensusFailRow, P8Census.skeletonDec, SemanticStrategy.decActive] at hf

/-- Concrete nonempty skeleton whose unique compute row is that OP1 cell.
-- -/
def s1CensusFailSkeleton : SemanticSkeleton where
  computeTree := .node s1CensusFailRow []
  memoryForest := []

theorem s1CensusFailSkeleton_computeRows :
    computeSkeletonRows s1CensusFailSkeleton = [s1CensusFailRow] := by
  unfold computeSkeletonRows s1CensusFailSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem s1CensusFailSkeleton_formula_pair_mem :
    (s1CensusFailRow.formula, s1CensusFailRow.formula) ∈
      BoundSemanticTrace.skeletonPairs K s1CensusFailSkeleton := by
  unfold BoundSemanticTrace.skeletonPairs
  refine List.mem_append.mpr (.inl ?_)
  simp [SemanticSkeleton.publicClaim, s1CensusFailSkeleton, s1CensusFailRow]

/-- The named extra fails at `Λ = 1`: the reconstructed formula has two
leaves. -- the paper -/
theorem census_fails_of_two_leaf_formula :
    ¬ EdgeComparisonCensus.CombinedSkeletonCensus K s1CensusFailSkeleton 1 := by
  intro h
  have hpair : (s1CensusFailRow.formula, s1CensusFailRow.formula) ∈
      BoundSemanticTrace.skeletonPairs (K := K) s1CensusFailSkeleton :=
    s1CensusFailSkeleton_formula_pair_mem (K := K)
  have hb :
      s1CensusFailRow.formula.leaves ≤ 1 ∧
        s1CensusFailRow.formula.leaves ≤ 1 :=
    h.p8.leaves_bounded (pair := (s1CensusFailRow.formula, s1CensusFailRow.formula))
      hpair
  have hle : s1CensusFailRow.formula.leaves ≤ 1 := hb.1
  rw [s1CensusFailRow_formula_leaves] at hle
  exact Nat.not_succ_le_self 1 hle

/-- Combined: assembled-style record equations hold, a free role-matching
comparison list is `LeavesBounded 1`, and the named extra fails.  The
skeleton-pair identification is therefore extra.  This does not inhabit
`sizeWindowBound` or `slotSemantics` in general.
-- -/
theorem census_does_not_follow_from_records_or_free_comparison_leaves :
    ServedLookupBridge.SkeletonRecordEquations s1CensusFailRow ∧
      (s1FreeComparisons.map ComparisonUse.role = requiredComparisonRoles .s1) ∧
      (∀ c ∈ s1FreeComparisons, c.LeavesBounded 1) ∧
      s1FreeComparisons ≠
        P8Census.skeletonComparisons (K := K) s1CensusFailRow ∧
      ¬ EdgeComparisonCensus.CombinedSkeletonCensus K s1CensusFailSkeleton 1 :=
  ⟨s1CensusFailRow_recordEquations,
    s1FreeComparisons_roles,
    s1FreeComparisons_leaves_le_one,
    s1FreeComparisons_ne_skeletonComparisons,
    census_fails_of_two_leaf_formula⟩

/-- On this OP1 skeleton the size-window list is empty, so
`SizeWindowNounsBoundedBy` holds vacuously.  That is not a general inhabit
of the named `sizeWindowBound` extra, which quantifies OP3/OP4/OP6
products. -- the paper -/
theorem s1CensusFailSkeleton_sizeWindowBound_vacuous :
    SizeWindowCounting.SizeWindowNounsBoundedBy s1CensusFailSkeleton 1 := by
  intro n hn
  have hrows := s1CensusFailSkeleton_computeRows
  simp [SizeWindowCounting.skeletonSizeWindowNouns] at hn
  rw [hrows] at hn
  simp [SizeWindowCounting.requiredSizeWindowNouns, s1CensusFailRow] at hn

/-! ## `skeletonBounded` does not follow from already-held objects /
`census` / `sizeWindowBound`

The paper atom range is `N^λ(F)` over Goldilocks `F_p`.
The Lean extra `CensusRecordPremises.skeletonBounded` is
`SemanticSkeleton.BoundedBy E.q`: `FieldEmbedding.BoundedBy q` on every
reconstructed compute-row noun, including active decomposition slots
(`ComputeRowSkeleton.BoundedBy`), plus the already-derived memory-row and
memory-tree conjuncts.  `census` is `leaves ≤ Λ` on reconstructed
`skeletonPairs` / `edgePairs`.  `sizeWindowBound` is
the same leaf window on OP3/OP4/OP6 products.  Those extras share some
reconstructed nouns with the compute row, but they are not the atom-range
predicate.  Memory-row/tree bounds, the compute root triple, and
subformula nouns are already theorems of `E` plus named NMR extras.
Active `decompNoun` remains `Realizes`-only.  `combinedBounded` is not
used. -/

/-- The named extra expands to atom-range `BoundedBy q`, not `leaves ≤ Λ`.
-- -/
theorem skeletonBounded_is_q_atom_range
    {q : ℕ} {S : SemanticSkeleton} (h : S.BoundedBy q) :
    (computeSkeletonRows S).Forall (ComputeRowSkeleton.BoundedBy q) ∧
      (memorySkeletonRows S).Forall (MemoryRowSkeleton.BoundedBy q) ∧
      (∀ tree ∈ S.memoryForest, ∀ node, InTree tree node →
        node.label.BoundedBy q) :=
  ⟨h.computeRows, h.memoryRows, h.memoryTrees⟩

/-- One leaf does not imply atom value `< q`.  Census/`sizeWindowBound`
are leaf windows; `skeletonBounded` is the atom range.
-- -/
theorem atom_two_one_leaf_not_bounded_by_two :
    (Noun.atom 2).leaves = 1 ∧ ¬ FieldEmbedding.BoundedBy 2 (Noun.atom 2) := by
  constructor
  · rfl
  · simp

/-- `censusAssemblyOf` still copies `skeletonBounded` from the named extra.
-- -/
theorem censusAssemblyOf_copies_skeletonBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).skeletonBounded = C.skeletonBounded :=
  rfl

/-- `combinedBounded` stays a distinct named extra; this item does not
inhabit it. -- the paper -/
theorem censusAssemblyOf_copies_combinedBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    (censusAssemblyOf E P M C).combinedBounded = C.combinedBounded :=
  rfl

/-- Memory-record nouns of `computeSkeletonOf` are the root triple,
`decompNoun`, or already-bounded subformula nouns.  Decomposition
atom-range is therefore the remaining compute-row obligation.
-- -/
theorem memRecSkelOf_bounded_of_decomp
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hdecomp : ∀ (slot : DecSlot),
      SemanticStrategy.decActive row.1 slot = true →
        FieldEmbedding.BoundedBy q (decompNoun data slot))
    (i : Fin 3) (hi : (i : ℕ) < Nock.Framework.recordCount row.1) :
    (memRecSkelOf data pubR i hi).BoundedBy q := by
  have hroot := ComputeRowSemanticData.root_bounded data
  have hf_t : SemanticStrategy.decActive row.1 .f_t = true :=
    (SemanticStrategy.decActive_cases row.1).2.1
  have htail : FieldEmbedding.BoundedBy q data.root.tail := by
    simpa [decompNoun] using hdecomp .f_t hf_t
  fin_cases i <;> dsimp [memRecSkelOf, MemRecSkeleton.BoundedBy]
  · exact ⟨hroot.2.1, htail⟩
  · split_ifs with hs0 htailSt
    · exact ⟨hroot.1, hroot.2.2⟩
    · refine ⟨htail, hdecomp .f_th ?_⟩
      exact (SemanticStrategy.decActive_cases row.1).2.2.1.mpr htailSt
    · exact ⟨hroot.2.1, htail⟩
  · split_ifs with hs6 hs9
    · refine ⟨hdecomp .f_tt ?_, hdecomp .f_tth ?_⟩
      · simp [SemanticStrategy.decActive, SemanticStrategy.hasTailDecomposition, hs6]
      · simp [SemanticStrategy.decActive, hs6]
    · exact ⟨subformulaNounOf_bounded data pubR ⟨0, by decide⟩
          (by simp [ComputeTable.fanoutComp, hs9]) .result,
        subformulaNounOf_bounded data pubR ⟨1, by decide⟩
          (by simp [ComputeTable.fanoutComp, hs9]) .formula⟩
    · exact ⟨hroot.2.1, htail⟩

/-- **Missing hypothesis.**  Atom-range bounds on reconstructed
`decompNoun` slots, together with already-held root/subformula bounds,
inhabit compute-row `BoundedBy q`.  `census` leaf bounds and
`sizeWindowBound` do not supply those atom values.
-- -/
theorem computeSkeletonOf_bounded_of_decomp
    {q Λ : ℕ} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (hdecomp : ∀ (slot : DecSlot),
      SemanticStrategy.decActive row.1 slot = true →
        FieldEmbedding.BoundedBy q (decompNoun data slot)) :
    (computeSkeletonOf data pubR).BoundedBy q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (computeSkeletonOf_root_bounded data pubR).1
  · exact (computeSkeletonOf_root_bounded data pubR).2.1
  · exact (computeSkeletonOf_root_bounded data pubR).2.2
  · intro slot hact
    exact hdecomp slot (by simpa [computeSkeletonOf] using hact)
  · intro i hi slot
    exact computeSkeletonOf_subformula_bounded data pubR i hi slot
  · intro i hi
    simpa [computeSkeletonOf] using
      memRecSkelOf_bounded_of_decomp data pubR hdecomp i hi

/-- **Missing hypothesis, assembled.**  Decomposition atom-range on every
reconstructed compute-skeleton row, plus already-derived memory-row/tree
bounds, inhabits `CensusRecordPremises.skeletonBounded`.
-- -/
theorem skeletonBounded_of_decomp_bounds
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hdecomp :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ∀ (slot : DecSlot)
          (hact : SemanticStrategy.decActive s.state slot = true),
          FieldEmbedding.BoundedBy E.q (s.decomposition slot hact)) :
    (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q where
  computeRows := by
    rw [List.forall_iff_forall_mem]
    intro s hs
    have hd := hdecomp s hs
    rw [computeSkeletonRows_of_assembly E P M] at hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
    rw [List.mem_range'] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp only [Nat.one_mul]
    have hidx : k < E.cfg.compRows := by
      rw [← E.exec.compute_bfs_length]
      exact hk
    have hlbl : computeLabelAt E P (1 + k) = computeNodeAt E P ⟨k, hidx⟩ := by
      have : (1 + k) - 1 = k := Nat.add_sub_cancel_left 1 k
      simpa [this] using computeLabelAt_of_index E P (i := 1 + k)
        (by simpa [this] using hidx)
    rw [hlbl, computeNodeAt, computeNodeOf]
    refine computeSkeletonOf_bounded_of_decomp (E.semanticData.rows ⟨k, hidx⟩)
      (publicRowNoun_of_execution E ⟨k, hidx⟩) ?_
    simpa [hlbl, computeNodeAt, computeNodeOf, computeSkeletonOf] using hd
  memoryRows := memorySkeletonRows_bounded E P M
  memoryTrees := memoryTrees_bounded E P M

/-- Explicit OP1 row whose formula is a two-leaf cell of atoms `< 2`, while
the active decomposition slots are `.atom 2`.  Root/subformula/memory-record
conjuncts of `BoundedBy 2` hold; the decomposition conjunct fails.
-- -/
def s1DecompFailRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 0)
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 2
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 1⟩

theorem s1DecompFailRow_recordEquations :
    ServedLookupBridge.SkeletonRecordEquations s1DecompFailRow where
  s0_record := by
    intro h
    cases h
  s9_record := by
    intro h
    cases h

theorem s1DecompFailRow_root_subformula_memory_bounded :
    FieldEmbedding.BoundedBy 2 s1DecompFailRow.subject ∧
      FieldEmbedding.BoundedBy 2 s1DecompFailRow.formula ∧
        FieldEmbedding.BoundedBy 2 s1DecompFailRow.evaluation ∧
          (∀ i h slot, FieldEmbedding.BoundedBy 2
            (s1DecompFailRow.subformula i h slot)) ∧
            (∀ i h, (s1DecompFailRow.memoryRecord i h).BoundedBy 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [s1DecompFailRow]
  · simp [s1DecompFailRow]
  · simp [s1DecompFailRow]
  · intro i h slot
    simp [s1DecompFailRow]
  · intro i h
    simp [s1DecompFailRow, MemRecSkeleton.BoundedBy]

def s1DecompFailSkeleton : SemanticSkeleton where
  computeTree := .node s1DecompFailRow []
  memoryForest := []

theorem s1DecompFailSkeleton_computeRows :
    computeSkeletonRows s1DecompFailSkeleton = [s1DecompFailRow] := by
  unfold computeSkeletonRows s1DecompFailSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- The named extra fails at `q = 2`: active decomposition is `.atom 2`.
-- -/
theorem skeletonBounded_fails_of_decomp_atom_two :
    ¬ s1DecompFailSkeleton.BoundedBy 2 := by
  intro h
  have hs : s1DecompFailRow ∈ computeSkeletonRows s1DecompFailSkeleton := by
    simp [s1DecompFailSkeleton_computeRows]
  have hb := (List.forall_iff_forall_mem.mp h.computeRows) _ hs
  have hf_h : SemanticStrategy.decActive .s1 .f_h = true := by
    simp [SemanticStrategy.decActive]
  have hdec : FieldEmbedding.BoundedBy 2
      (s1DecompFailRow.decomposition .f_h hf_h) :=
    hb.2.2.2.1 .f_h hf_h
  simp [s1DecompFailRow] at hdec

/-- Census at `Λ = 2` holds: every reconstructed pair, including the
unbounded decomposition atom, has at most two leaves.  This is not
`BoundedBy 2`. -- the paper -/
theorem s1DecompFailSkeleton_census :
    EdgeComparisonCensus.CombinedSkeletonCensus K s1DecompFailSkeleton 2 :=
  census_of_identified_skeleton_pairs
    (fun s hs c hc => by
      rw [s1DecompFailSkeleton_computeRows] at hs
      simp only [List.mem_singleton] at hs
      subst hs
      simp [P8Census.skeletonComparisons, P8Census.skeletonUse,
        P8Census.skeletonDec, s1DecompFailRow, SemanticStrategy.decActive] at hc
      obtain rfl | rfl | rfl := hc
      · simp [ComparisonUse.LeavesBounded, Noun.leaves]
      · simp [ComparisonUse.LeavesBounded, Noun.leaves]
      · simp [ComparisonUse.LeavesBounded, Noun.leaves])
    ⟨by simp [s1DecompFailSkeleton, s1DecompFailRow, Noun.leaves],
      by simp [s1DecompFailSkeleton, s1DecompFailRow, Noun.leaves],
      by simp [s1DecompFailSkeleton, s1DecompFailRow, Noun.leaves]⟩
    (fun pair hp => by
      unfold EdgeComparisonCensus.edgePairs s1DecompFailSkeleton at hp
      rw [bfsForest_cons_eq _ (by simp)] at hp
      simp [bfsForest_nil, EdgeComparisonCensus.rowEdgePairs,
        NTree.childOpt] at hp)

/-- Size-window extra is empty on this OP1 skeleton, hence holds at `Λ = 2`.
That is not a general inhabit of `sizeWindowBound`. -- the paper -/
theorem s1DecompFailSkeleton_sizeWindowBound_vacuous :
    SizeWindowCounting.SizeWindowNounsBoundedBy s1DecompFailSkeleton 2 := by
  intro n hn
  have hrows := s1DecompFailSkeleton_computeRows
  simp [SizeWindowCounting.skeletonSizeWindowNouns] at hn
  rw [hrows] at hn
  simp [SizeWindowCounting.requiredSizeWindowNouns, s1DecompFailRow] at hn

/-- Combined: `census` and `sizeWindowBound` hold on a reconstructed OP1
skeleton whose decomposition atom is not `BoundedBy q`.  `skeletonBounded`
is therefore not a restatement of those extras, and does not follow from
already-held root/subformula/memory-record bounds.
-- -/
theorem skeletonBounded_does_not_follow_from_census_or_sizeWindow :
    ServedLookupBridge.SkeletonRecordEquations s1DecompFailRow ∧
      FieldEmbedding.BoundedBy 2 s1DecompFailRow.subject ∧
      FieldEmbedding.BoundedBy 2 s1DecompFailRow.formula ∧
      FieldEmbedding.BoundedBy 2 s1DecompFailRow.evaluation ∧
      (∀ i h slot, FieldEmbedding.BoundedBy 2
        (s1DecompFailRow.subformula i h slot)) ∧
      (∀ i h, (s1DecompFailRow.memoryRecord i h).BoundedBy 2) ∧
      EdgeComparisonCensus.CombinedSkeletonCensus K s1DecompFailSkeleton 2 ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy s1DecompFailSkeleton 2 ∧
      ¬ s1DecompFailSkeleton.BoundedBy 2 :=
  let hroot := s1DecompFailRow_root_subformula_memory_bounded
  ⟨s1DecompFailRow_recordEquations, hroot.1, hroot.2.1, hroot.2.2.1,
    hroot.2.2.2.1, hroot.2.2.2.2, s1DecompFailSkeleton_census,
    s1DecompFailSkeleton_sizeWindowBound_vacuous,
    skeletonBounded_fails_of_decomp_atom_two⟩

/-! ## `combinedBounded` at consumed `q`

The Lean extra `CensusRecordPremises.combinedBounded` is
`CombinedBoundedBy K E.q` on the assembled skeleton: every noun of every
pair in `combinedSkeletonPairs` is `BoundedBy E.q`.
Those pairs are the public-claim self-pairs, the state-indexed
`skeletonComparisons` (including opcode atoms `0..9` and OP0/OP9 axis
atoms), and parent-child `edgePairs`.  Row
`skeletonBounded` does not mention those synthesized rights.  On a free
skeleton the missing hypothesis is `skeletonMemoryAxis < q` on OP0 `mr2`
and OP9 `mr3`.  On the assembled skeleton those axes are `atomVal` of
already-bounded `decompNoun`s, so the extra follows from named
`skeletonBounded` plus `11 < ringChar` and `q_eq_ringChar`. -/

/-- The named extra expands to pair-wise atom-range on census/edge pairs.
-- -/
theorem combinedBounded_is_pair_atom_range {q : ℕ} {S : SemanticSkeleton}
    (h : ProductionP8Containment.CombinedBoundedBy K q S) :
    ∀ pair ∈ EdgeComparisonCensus.combinedSkeletonPairs K S,
      FieldEmbedding.BoundedBy q pair.1 ∧
        FieldEmbedding.BoundedBy q pair.2 :=
  h

/-- Opcode atoms `0..9` are in range at the consumed bound `11 < q`.
-- -/
theorem opcode_atom_bounded_of_eleven_lt {q n : ℕ} (hq : 11 < q)
    (hn : n ≤ 9) : FieldEmbedding.BoundedBy q (.atom n) := by
  simp only [FieldEmbedding.BoundedBy_atom]
  omega

/-- `atomVal` of a `q`-bounded noun is `< q`. -/

theorem atomVal_lt_of_bounded {q : ℕ} {n : Noun}
    (h : FieldEmbedding.BoundedBy q n) (hq : 0 < q) :
    atomVal n < q := by
  cases n with
  | atom k => simpa [atomVal] using h
  | cell _ _ =>
      simp only [atomVal]
      exact hq

/-- Inactive `skeletonDec` fallback is `.atom 0`; active slots are row
decomposition nouns. -- the paper -/
theorem skeletonDec_bounded {q : ℕ} {s : ComputeRowSkeleton}
    (hb : s.BoundedBy q) (hq : 0 < q) (slot : DecSlot) :
    FieldEmbedding.BoundedBy q (P8Census.skeletonDec s slot) := by
  unfold P8Census.skeletonDec
  split_ifs with hact
  · exact hb.2.2.2.1 slot hact
  · simp only [FieldEmbedding.BoundedBy_atom]
    exact hq

/-- Inactive `skeletonSubformula` fallback is `.atom 0`. -- the paper -/
theorem skeletonSubformula_bounded {q : ℕ} {s : ComputeRowSkeleton}
    (hb : s.BoundedBy q) (hq : 0 < q) (i : Fin 3) (slot : TripleSlot) :
    FieldEmbedding.BoundedBy q (P8Census.skeletonSubformula s i slot) := by
  unfold P8Census.skeletonSubformula
  split_ifs with hi
  · exact hb.2.2.2.2.1 i hi slot
  · simp only [FieldEmbedding.BoundedBy_atom]
    exact hq

/-- Modular OP4 target is `q`-bounded when the operand is. -/

theorem incMod_bounded {q : ℕ} {n : Noun} (hq : 0 < q)
    (h : FieldEmbedding.BoundedBy q n) :
    FieldEmbedding.BoundedBy q (incMod q n) := by
  cases n with
  | atom k =>
      simp only [incMod, FieldEmbedding.BoundedBy_atom]
      exact Nat.mod_lt _ hq
  | cell _ _ =>
      simp only [incMod, FieldEmbedding.BoundedBy_atom]
      exact hq

private theorem eleven_lt_pos {q : ℕ} (hq : 11 < q) : 0 < q :=
  Nat.lt_trans (by decide : 0 < 11) hq

private theorem eleven_lt_one {q : ℕ} (hq : 11 < q) : 1 < q :=
  Nat.lt_trans (by decide : 1 < 11) hq

/-- Row `BoundedBy q` plus consumed `11 < q`, `q = ringChar`, and OP0/OP9
axis range close every `skeletonComparisons` side. -- the paper -/
theorem skeletonComparisons_pair_bounded {q : ℕ}
    {s : ComputeRowSkeleton} (hb : s.BoundedBy q) (hq : 11 < q)
    (hchar : q = ringChar K)
    (haxis0 : s.state = .s0 → P8Census.skeletonMemoryAxis s 1 < q)
    (haxis9 : s.state = .s9 → P8Census.skeletonMemoryAxis s 2 < q)
    {c : ComparisonUse}
    (hc : c ∈ P8Census.skeletonComparisons (K := K) s) :
    FieldEmbedding.BoundedBy q c.left ∧ FieldEmbedding.BoundedBy q c.right := by
  have hq0 := eleven_lt_pos hq
  have hq1 := eleven_lt_one hq
  have hdec (slot : DecSlot) := skeletonDec_bounded hb hq0 slot
  have hsf (i : Fin 3) (slot : TripleSlot) :=
    skeletonSubformula_bounded hb hq0 i slot
  cases hst : s.state
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨hdec .f_h, opcode_atom_bounded_of_eleven_lt hq (by decide)⟩
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hdec .f_t, by
        simp only [FieldEmbedding.BoundedBy_atom]
        exact haxis0 hst⟩
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨hdec .f_h, opcode_atom_bounded_of_eleven_lt hq (by decide)⟩
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hb.2.2.1, hdec .f_t⟩
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hdec .f_h, opcode_atom_bounded_of_eleven_lt hq (by decide)⟩
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hdec .f_t, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_th, hdec .f_tt⟩⟩
    · exact ⟨hsf 0 .subject, hb.1⟩
    · exact ⟨hsf 0 .formula, hdec .f_th⟩
    · exact ⟨hsf 1 .subject, hb.1⟩
    · exact ⟨hsf 1 .formula, hdec .f_tt⟩
    · exact ⟨hsf 2 .subject, hsf 0 .result⟩
    · exact ⟨hsf 2 .formula, hsf 1 .result⟩
    · exact ⟨hb.2.2.1, hsf 2 .result⟩
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨hdec .f_h, opcode_atom_bounded_of_eleven_lt hq (by decide)⟩
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hsf 0 .subject, hb.1⟩
    · exact ⟨hsf 0 .formula, hdec .f_t⟩
    · exact ⟨hb.2.2.1, FieldEmbedding.wut_boundedBy hq1 _⟩
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨hdec .f_h, opcode_atom_bounded_of_eleven_lt hq (by decide)⟩
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hsf 0 .subject, hb.1⟩
    · exact ⟨hsf 0 .formula, hdec .f_t⟩
    · refine ⟨hb.2.2.1, ?_⟩
      rw [← hchar]
      exact incMod_bounded hq0 (hsf 0 .result)
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hdec .f_h, opcode_atom_bounded_of_eleven_lt hq (by decide)⟩
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hdec .f_t, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_th, hdec .f_tt⟩⟩
    · exact ⟨hsf 0 .subject, hb.1⟩
    · exact ⟨hsf 0 .formula, hdec .f_th⟩
    · exact ⟨hsf 1 .subject, hb.1⟩
    · exact ⟨hsf 1 .formula, hdec .f_tt⟩
    · exact ⟨hsf 0 .result, hsf 1 .result⟩
    · exact ⟨hb.2.2.1, FieldEmbedding.tis_boundedBy hq1 _ _⟩
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hdec .f_h, opcode_atom_bounded_of_eleven_lt hq (by decide)⟩
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hdec .f_t, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_th, hdec .f_tt⟩⟩
    · exact ⟨hdec .f_tt, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_tth, hdec .f_ttt⟩⟩
    · exact ⟨hsf 0 .subject, hb.1⟩
    · exact ⟨hsf 0 .formula, hdec .f_tth⟩
    · exact ⟨hsf 0 .formula, hdec .f_ttt⟩
    · exact ⟨hsf 1 .subject, hb.1⟩
    · exact ⟨hsf 1 .formula, hdec .f_th⟩
    · exact ⟨hb.2.2.1, hsf 0 .result⟩
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hdec .f_h, opcode_atom_bounded_of_eleven_lt hq (by decide)⟩
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hdec .f_t, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_th, hdec .f_tt⟩⟩
    · exact ⟨hsf 1 .subject, hb.1⟩
    · exact ⟨hsf 1 .formula, hdec .f_th⟩
    · exact ⟨hsf 0 .subject, hsf 1 .result⟩
    · exact ⟨hsf 0 .formula, hdec .f_tt⟩
    · exact ⟨hb.2.2.1, hsf 0 .result⟩
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hdec .f_h, opcode_atom_bounded_of_eleven_lt hq (by decide)⟩
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hdec .f_t, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_th, hdec .f_tt⟩⟩
    · exact ⟨hsf 1 .subject, hb.1⟩
    · exact ⟨hsf 1 .formula, hdec .f_th⟩
    · exact ⟨hsf 0 .subject,
        FieldEmbedding.BoundedBy_cell.mpr ⟨hsf 1 .result, hb.1⟩⟩
    · exact ⟨hsf 0 .formula, hdec .f_tt⟩
    · exact ⟨hb.2.2.1, hsf 0 .result⟩
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hdec .f_h, opcode_atom_bounded_of_eleven_lt hq (by decide)⟩
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hdec .f_t, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_th, hdec .f_tt⟩⟩
    · exact ⟨hdec .f_th, by
        simp only [FieldEmbedding.BoundedBy_atom]
        exact haxis9 hst⟩
    · exact ⟨hsf 0 .subject, hb.1⟩
    · exact ⟨hsf 0 .formula, hdec .f_tt⟩
    · exact ⟨hsf 1 .subject, hsf 0 .result⟩
    · exact ⟨hb.2.2.1, hsf 1 .result⟩
  · simp [P8Census.skeletonComparisons, hst, P8Census.skeletonUse] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hb.2.1, FieldEmbedding.BoundedBy_cell.mpr ⟨hdec .f_h, hdec .f_t⟩⟩
    · exact ⟨hsf 0 .subject, hb.1⟩
    · exact ⟨hsf 0 .formula, hdec .f_h⟩
    · exact ⟨hsf 1 .subject, hb.1⟩
    · exact ⟨hsf 1 .formula, hdec .f_t⟩
    · exact ⟨hb.2.2.1,
        FieldEmbedding.BoundedBy_cell.mpr ⟨hsf 0 .result, hsf 1 .result⟩⟩

theorem computeTree_label_mem_rows (S : SemanticSkeleton) :
    S.computeTree.label ∈ computeSkeletonRows S := by
  unfold computeSkeletonRows
  refine List.mem_map.mpr ⟨S.computeTree, ?_, rfl⟩
  exact (mem_bfsForest [S.computeTree] S.computeTree).2
    ⟨S.computeTree, by simp, InTree.here _⟩

theorem computeRow_bounded_of_mem {q : ℕ} {S : SemanticSkeleton}
    (hb : S.BoundedBy q) {s : ComputeRowSkeleton}
    (hs : s ∈ computeSkeletonRows S) : s.BoundedBy q :=
  (List.forall_iff_forall_mem.mp hb.computeRows) s hs

/-- Edge triples compare child root nouns to the parent's subformula slots.
-- -/
theorem edgeTriple_bounded {q : ℕ} {parent child : ComputeRowSkeleton}
    {i : Fin 3} (hp : parent.BoundedBy q) (hc : child.BoundedBy q)
    (hq : 0 < q) {pair : Noun × Noun}
    (hpair : pair ∈ EdgeComparisonCensus.edgeTriple parent child i) :
    FieldEmbedding.BoundedBy q pair.1 ∧ FieldEmbedding.BoundedBy q pair.2 := by
  simp [EdgeComparisonCensus.edgeTriple, List.mem_cons, List.not_mem_nil] at hpair
  rcases hpair with rfl | rfl | rfl
  · exact ⟨hc.1, skeletonSubformula_bounded hp hq i .subject⟩
  · exact ⟨hc.2.1, skeletonSubformula_bounded hp hq i .formula⟩
  · exact ⟨hc.2.2.1, skeletonSubformula_bounded hp hq i .result⟩

theorem childOpt_mem {α : Type*} {t : NTree α} {i : ℕ} {child : NTree α}
    (h : t.childOpt i = some child) : child ∈ t.children := by
  unfold NTree.childOpt at h
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.getElem_mem hlt

/-- Missing hypothesis on a free skeleton: OP0/OP9 census axis atoms are
`< q`, in addition to row `BoundedBy q` and the consumed char bound.
-- -/
theorem combinedBounded_of_skeletonBounded_and_axis_range {q : ℕ}
    {S : SemanticSkeleton} (hb : S.BoundedBy q) (hq : 11 < q)
    (hchar : q = ringChar K)
    (haxis : ∀ s ∈ computeSkeletonRows S,
      (s.state = .s0 → P8Census.skeletonMemoryAxis s 1 < q) ∧
        (s.state = .s9 → P8Census.skeletonMemoryAxis s 2 < q)) :
    ProductionP8Containment.CombinedBoundedBy K q S := by
  intro pair hp
  unfold EdgeComparisonCensus.combinedSkeletonPairs at hp
  rw [List.mem_append] at hp
  have hq0 := eleven_lt_pos hq
  rcases hp with hp | hp
  · unfold BoundSemanticTrace.skeletonPairs at hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · have hroot := computeRow_bounded_of_mem hb (computeTree_label_mem_rows S)
      simp [SemanticSkeleton.publicClaim, List.mem_cons, List.not_mem_nil] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨hroot.1, hroot.1⟩
      · exact ⟨hroot.2.1, hroot.2.1⟩
      · exact ⟨hroot.2.2.1, hroot.2.2.1⟩
    · rw [List.mem_map] at hp
      obtain ⟨c, hc, rfl⟩ := hp
      unfold P8Census.skeletonComparisonCensus at hc
      rw [List.mem_flatMap] at hc
      obtain ⟨s, hs, hc⟩ := hc
      simpa [SemanticTrace.ComparisonUse.pair] using
        skeletonComparisons_pair_bounded (computeRow_bounded_of_mem hb hs) hq
          hchar (haxis s hs).1 (haxis s hs).2 hc
  · unfold EdgeComparisonCensus.edgePairs at hp
    rw [List.mem_flatMap] at hp
    obtain ⟨node, hnode, hrow⟩ := hp
    have hnodeB := computeRow_bounded_of_mem hb (by
      unfold computeSkeletonRows
      exact List.mem_map.mpr ⟨node, hnode, rfl⟩)
    unfold EdgeComparisonCensus.rowEdgePairs at hrow
    rw [List.mem_flatMap] at hrow
    obtain ⟨triples, htriples, hpair⟩ := hrow
    rw [List.mem_ofFn] at htriples
    obtain ⟨i, rfl⟩ := htriples
    cases hch : node.childOpt i with
    | none => simp [hch] at hpair
    | some child =>
        simp [hch] at hpair
        have hinNode : InTree S.computeTree node := by
          obtain ⟨t, ht, hin⟩ := (mem_bfsForest [S.computeTree] node).1 hnode
          simp only [List.mem_singleton] at ht
          subst t
          exact hin
        have hinChild : InTree S.computeTree child :=
          InTree_trans hinNode
            (InTree.sub (childOpt_mem (i := (i : ℕ)) hch) (InTree.here child))
        have hchildB := computeRow_bounded_of_mem hb (by
          unfold computeSkeletonRows
          refine List.mem_map.mpr ⟨child, ?_, rfl⟩
          exact (mem_bfsForest [S.computeTree] child).2
            ⟨S.computeTree, by simp, hinChild⟩)
        exact edgeTriple_bounded hnodeB hchildB hq0 hpair

/-- Assembled OP0 `mr2` axis is `atomVal` of the formula tail.
-- -/
theorem computeSkeletonOf_s0_memoryAxis {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s0) :
    P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 1 =
      atomVal data.root.tail := by
  simp [P8Census.skeletonMemoryAxis, computeSkeletonOf, memRecSkelOf, h,
    Nock.Framework.recordCount]

/-- C5's OP0 `ServedLookup` is the reconstructed skeleton slot fact: subject,
`mr2` axis, and evaluation are the root nouns, and the axis is the formula-tail
atom.  No extra identification. -- the paper -/
theorem computeSkeletonOf_slotSemantics_of_s0 {q Λ : ℕ}
    {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K}
    {dec : ComputeTable.Dec K}
    {data : ComputeRowSemanticData q Λ (.s0, (inp, pub, dec))}
    (cert : LocalOpcodeCertificate q Λ data)
    (pubR : ComputePublicRowNounRealization q
      (computePublicLabel (.s0, (inp, pub, dec)))) :
    ServedLookupBridge.SkeletonSlotSemantics (computeSkeletonOf data pubR) := by
  obtain ⟨axis, htail, hserved⟩ := s0_root_tail_eq_atom cert
  refine ServedLookupBridge.skeletonSlotSemantics_of_served ?h0 ?h9
  · intro _
    have haxis :
        P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 1 = axis := by
      rw [computeSkeletonOf_s0_memoryAxis data pubR rfl, htail, atomVal_atom]
    rw [haxis]
    exact hserved
  · intro h9
    simp [computeSkeletonOf] at h9

/-- Assembled OP9 `mr3` axis is `atomVal` of `decompNoun f_th`.
-- -/
theorem computeSkeletonOf_s9_memoryAxis {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s9) :
    P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 2 =
      atomVal (decompNoun data .f_th) := by
  simp [P8Census.skeletonMemoryAxis, computeSkeletonOf, memRecSkelOf, h,
    Nock.Framework.recordCount]

theorem computeSkeletonOf_s0_axis_lt {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s0)
    (hb : (computeSkeletonOf data pubR).BoundedBy q) (hq : 0 < q) :
    P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 1 < q := by
  rw [computeSkeletonOf_s0_memoryAxis data pubR h]
  refine atomVal_lt_of_bounded ?_ hq
  have hact : SemanticStrategy.decActive row.1 .f_t = true :=
    (SemanticStrategy.decActive_cases row.1).2.1
  simpa [computeSkeletonOf, decompNoun] using
    hb.2.2.2.1 .f_t (by simpa [computeSkeletonOf] using hact)

theorem computeSkeletonOf_s9_axis_lt {q Λ : ℕ}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (pubR : ComputePublicRowNounRealization q (computePublicLabel row))
    (h : row.1 = .s9)
    (hb : (computeSkeletonOf data pubR).BoundedBy q) (hq : 0 < q) :
    P8Census.skeletonMemoryAxis (computeSkeletonOf data pubR) 2 < q := by
  rw [computeSkeletonOf_s9_memoryAxis data pubR h]
  refine atomVal_lt_of_bounded ?_ hq
  have hact : SemanticStrategy.decActive row.1 .f_th = true := by
    simp [SemanticStrategy.decActive, SemanticStrategy.hasTailDecomposition, h]
  simpa [computeSkeletonOf] using
    hb.2.2.2.1 .f_th (by simpa [computeSkeletonOf] using hact)

theorem assembled_computeRow_eq (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    {s : ComputeRowSkeleton}
    (hs : s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M))) :
    ∃ i : Fin E.cfg.compRows,
      s = computeSkeletonOf (E.semanticData.rows i)
        (publicRowNoun_of_execution E i) := by
  rw [computeSkeletonRows_of_assembly E P M] at hs
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hs
  rw [List.mem_range'] at hn
  obtain ⟨k, hk, rfl⟩ := hn
  simp only [Nat.one_mul]
  have hidx : k < E.cfg.compRows := by
    rw [← E.exec.compute_bfs_length]
    exact hk
  refine ⟨⟨k, hidx⟩, ?_⟩
  have hlbl : computeLabelAt E P (1 + k) = computeNodeAt E P ⟨k, hidx⟩ := by
    have : (1 + k) - 1 = k := Nat.add_sub_cancel_left 1 k
    simpa [this] using computeLabelAt_of_index E P (i := 1 + k)
      (by simpa [this] using hidx)
  rw [hlbl, computeNodeAt, computeNodeOf]

/-- Assembled OP0/OP9 axes are `atomVal` of `skeletonBounded` nouns, hence
`< q`. -- the paper -/
theorem assembled_axis_range_of_skeletonBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hs : (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hq : 0 < E.q) :
    ∀ s ∈ computeSkeletonRows
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
      (s.state = .s0 → P8Census.skeletonMemoryAxis s 1 < E.q) ∧
        (s.state = .s9 → P8Census.skeletonMemoryAxis s 2 < E.q) := by
  intro s hsmem
  obtain ⟨i, rfl⟩ := assembled_computeRow_eq E P M hsmem
  have hb := computeRow_bounded_of_mem hs hsmem
  refine ⟨?_, ?_⟩
  · intro hst
    have hrow : (E.exec.computeRowAt i).1 = .s0 := by
      simpa [computeSkeletonOf] using hst
    exact computeSkeletonOf_s0_axis_lt (E.semanticData.rows i)
      (publicRowNoun_of_execution E i) hrow hb hq
  · intro hst
    have hrow : (E.exec.computeRowAt i).1 = .s9 := by
      simpa [computeSkeletonOf] using hst
    exact computeSkeletonOf_s9_axis_lt (E.semanticData.rows i)
      (publicRowNoun_of_execution E i) hrow hb hq

/-- **Inhabit at consumed `q`.**  Named `skeletonBounded` on the assembled
skeleton, plus `11 < ringChar` and `q_eq_ringChar`, closes
`CensusRecordPremises.combinedBounded`.  Not a restatement: see
`combinedBounded_not_restatement_at_consumed_q`.
-- -/
theorem combinedBounded_of_skeletonBounded_at_consumed_q
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hs : (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K) :
    ProductionP8Containment.CombinedBoundedBy K E.q
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) := by
  have hq : 11 < E.q := by rw [P.q_eq_ringChar]; exact hgt
  exact combinedBounded_of_skeletonBounded_and_axis_range hs hq P.q_eq_ringChar
    (assembled_axis_range_of_skeletonBounded E P M hs (eleven_lt_pos hq))

/-- Assembled `combinedBounded` still consumes named `q_eq_ringChar`.
Already-held `11 < ringChar` does not discharge the extra.
-- -/
theorem combinedBounded_at_consumed_q_still_names_q_eq
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (hs : (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K) :
    ProductionP8Containment.CombinedBoundedBy K E.q
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) ∧
      E.q = ringChar K :=
  ⟨combinedBounded_of_skeletonBounded_at_consumed_q E P M hs hgt, P.q_eq_ringChar⟩

/-- The five-field eta is unchanged. -- the paper -/
def censusRecordPremises_of_skeletonBounded
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (slotSemantics :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ServedLookupBridge.SkeletonSlotSemantics s)
    (census :
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (sizeWindowBound :
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (skeletonBounded :
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K) :
    CensusRecordPremises E P M where
  slotSemantics := slotSemantics
  census := census
  sizeWindowBound := sizeWindowBound
  skeletonBounded := skeletonBounded
  combinedBounded :=
    combinedBounded_of_skeletonBounded_at_consumed_q E P M skeletonBounded hgt

theorem censusRecordPremises_of_skeletonBounded_fills_combined
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (slotSemantics :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ServedLookupBridge.SkeletonSlotSemantics s)
    (census :
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (sizeWindowBound :
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (skeletonBounded :
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K) :
    (censusRecordPremises_of_skeletonBounded E P M slotSemantics census
        sizeWindowBound skeletonBounded hgt).combinedBounded =
      combinedBounded_of_skeletonBounded_at_consumed_q E P M
        skeletonBounded hgt :=
  rfl

/-- `Data` from the four remaining census extras at consumed `q`. -/

def dataOfCensusAtConsumed (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryRecordPremises E)
    (slotSemantics :
      ∀ s ∈ computeSkeletonRows
          (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)),
        ServedLookupBridge.SkeletonSlotSemantics s)
    (census :
      EdgeComparisonCensus.CombinedSkeletonCensus K
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (sizeWindowBound :
      SizeWindowCounting.SizeWindowNounsBoundedBy
        (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)) E.Λ)
    (skeletonBounded :
      (skeletonOfNodes (computeNodesOf E P) (memoryNodesOf E M)).BoundedBy E.q)
    (hgt : 11 < ringChar K) (hln : FirstLineStartsAtOne E.exec) :
    Data E :=
  dataOfCensus E P M (censusRecordPremises_of_skeletonBounded E P M
    slotSemantics census sizeWindowBound skeletonBounded hgt) hln

/-- Free OP0 row at consumed-compatible `q = 12`: every reconstructed noun
is `.atom 0` or `[0 0]`, while `mr2` axis is `12`. -- the paper -/
def s0AxisFailRow : ComputeRowSkeleton where
  state := .s0
  subject := .atom 0
  formula := .cell (.atom 0) (.atom 0)
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun i _ =>
    if (i : ℕ) = 1 then ⟨.atom 0, .atom 0, 12⟩ else ⟨.atom 0, .atom 0, 1⟩

def s0AxisFailSkeleton : SemanticSkeleton where
  computeTree := .node s0AxisFailRow []
  memoryForest := []

theorem s0AxisFailSkeleton_computeRows :
    computeSkeletonRows s0AxisFailSkeleton = [s0AxisFailRow] := by
  unfold computeSkeletonRows s0AxisFailSkeleton
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem s0AxisFailRow_bounded_by_twelve :
    s0AxisFailRow.BoundedBy 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s0AxisFailRow]
  · simp [s0AxisFailRow]
  · simp [s0AxisFailRow]
  · intro slot hact
    simp [s0AxisFailRow]
  · intro i h slot
    simp [s0AxisFailRow]
  · intro i h
    simp [s0AxisFailRow, MemRecSkeleton.BoundedBy]
    split_ifs <;> simp

theorem s0AxisFailSkeleton_bounded_by_twelve :
    s0AxisFailSkeleton.BoundedBy 12 where
  computeRows := by
    rw [List.forall_iff_forall_mem]
    intro s hs
    rw [s0AxisFailSkeleton_computeRows] at hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact s0AxisFailRow_bounded_by_twelve
  memoryRows := by
    rw [List.forall_iff_forall_mem]
    intro s hs
    unfold memorySkeletonRows s0AxisFailSkeleton at hs
    simp [bfsForest_nil] at hs
  memoryTrees := by
    intro tree ht
    simp [s0AxisFailSkeleton] at ht

theorem s0AxisFailRow_memoryAxis :
    P8Census.skeletonMemoryAxis s0AxisFailRow 1 = 12 := by
  simp [P8Census.skeletonMemoryAxis, s0AxisFailRow, Nock.Framework.recordCount]

theorem eleven_lt_twelve : 11 < 12 := by decide

/-- OP0 recursive-formula pair is `(.atom 0, .atom 12)`, in the extra's
quantifier at consumed-compatible `q`. -- the paper -/
theorem s0AxisFailRow_axis_pair_mem :
    (Noun.atom 0, Noun.atom 12) ∈
      BoundSemanticTrace.skeletonPairs K s0AxisFailSkeleton := by
  unfold BoundSemanticTrace.skeletonPairs
  refine List.mem_append.mpr (.inr ?_)
  refine List.mem_map.mpr
    ⟨P8Census.skeletonUse .recursiveFormula (.atom 0) (.atom 12), ?_, rfl⟩
  simp [P8Census.skeletonComparisonCensus, s0AxisFailSkeleton_computeRows,
    P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    P8Census.skeletonMemoryAxis, s0AxisFailRow, SemanticStrategy.decActive,
    Nock.Framework.recordCount]

/-- Predicates are distinct at consumed-compatible `q = 12`: row
`BoundedBy 12` holds and `CombinedBoundedBy` fails on the OP0 axis atom.
This is not an assembled `Data` counterexample.
-- -/
theorem combinedBounded_not_restatement_at_consumed_q :
    11 < 12 ∧
      s0AxisFailSkeleton.BoundedBy 12 ∧
      ¬ ProductionP8Containment.CombinedBoundedBy K 12 s0AxisFailSkeleton := by
  refine ⟨eleven_lt_twelve, s0AxisFailSkeleton_bounded_by_twelve, ?_⟩
  intro h
  have hpair : (Noun.atom 0, Noun.atom 12) ∈
      EdgeComparisonCensus.combinedSkeletonPairs K s0AxisFailSkeleton := by
    unfold EdgeComparisonCensus.combinedSkeletonPairs
    exact List.mem_append.mpr (.inl (s0AxisFailRow_axis_pair_mem (K := K)))
  have hb := h _ hpair
  simp [FieldEmbedding.BoundedBy] at hb

/-! ## `axisNat` is the already-held NMR Nat-cast

Paper `Def:NMR` puts the address in `𝔽` as the Nat axis
label of `child` relative to `root`.  Lookup validity is
`axis_root(child) = address` on every compute-table memory record.  The
Lean extra is that same Nat-cast on live memory-table `mem.axis`.

`read_root` emissions are service records (`recordPartition`).
`Service.realization.axis_realizes` is already `record.axis = (axis : K)`.
`verify_child` committed addresses are `vaxis` of `exactAxisTree`; the
served walk already derives `vaxis = Relaxis`,
and `Relaxis` is a Nat-cast of the paper doubling.  Inverse-BFS
`memoryNodesOf` still consumes `MemoryRecordPremises` and does not inhabit
the extra.  `axisAtoms` is the compute OP0/OP9 formula-tail extra
 and is a different object.  `timestampClosed` is not
attempted. -/


theorem vaddr_is_nat_cast (e : ℕ) :
    ∀ t : MTree K, ∃ n : ℕ, vaddr e t = (n : K) := by
  intro t
  induction t with
  | halt => exact ⟨0, by simp [vaddr]⟩
  | decompose l r ihl ihr =>
      by_cases hvl : verifyCount e l = 1
      · simpa [vaddr, hvl] using ihl
      · obtain ⟨n, hn⟩ := ihr
        refine ⟨n + 2 ^ vdep e r, ?_⟩
        simp [vaddr, hvl, hn, Nat.cast_add, Nat.cast_pow]
  | read _e c ih => simpa [vaddr] using ih
  | verify e' _a c ih =>
      by_cases he : e' = e
      · exact ⟨0, by simp [vaddr, he]⟩
      · simpa [vaddr, he] using ih


theorem relaxis_is_nat_cast (e : ℕ) :
    ∀ t : MTree K, ∃ n : ℕ, Relaxis e t = (n : K) := by
  intro t
  induction t with
  | halt => exact ⟨0, by simp [Relaxis]⟩
  | decompose l r ihl ihr =>
      by_cases hrl : readCount e l = 1
      · simpa [Relaxis, hrl] using ihl
      · simpa [Relaxis, hrl] using ihr
  | read e' c ih =>
      by_cases he : e' = e
      · obtain ⟨n, hn⟩ := vaddr_is_nat_cast e c
        refine ⟨n + 2 ^ vdep e c, ?_⟩
        simp [Relaxis, he, hn, Nat.cast_add, Nat.cast_pow]
      · simpa [Relaxis, he] using ih
  | verify _e' _a c ih => simpa [Relaxis] using ih


theorem service_axis_is_nat_cast
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (s : Service cfg exec) :
    ∃ n : ℕ, s.record.axis = (n : K) :=
  ⟨s.axis, s.realization.axis_realizes⟩

theorem exists_memoryTreeAt_eq {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) {t : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (ht : t ∈ exec.memoryForest) :
    ∃ i : Fin cfg.kMem, exec.memoryTreeAt i = t := by
  obtain ⟨n, hn, heq⟩ := List.getElem_of_mem ht
  have hn' : n < cfg.kMem := exec.memory_root_count ▸ hn
  refine ⟨⟨n, hn'⟩, ?_⟩
  simp [ExactExecution.memoryTreeAt, Fin.cast, List.get_eq_getElem, heq]

theorem memory_fanout_of_intree (E : BuildableNockExecution F K)
    {root node : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hroot : root ∈ E.exec.memoryForest) (hin : InTree root node) :
    MemoryTable.fanoutMem node.label.1 = node.children.length := by
  have hbfs : node ∈ bfsForest E.exec.memoryForest :=
    (mem_bfsForest _ _).2 ⟨root, hroot, hin⟩
  exact MemoryExactTopology.fanout_binding
    E.language.traversable.memory_topology node hbfs

/-- Fanout binding on the a-bearing forest: the row encode keeps state and shape. -/
theorem memory_fanout_of_intreeA (E : BuildableNockExecution F K)
    {root node : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hroot : root ∈ E.execA.memoryForest) (hin : InTree root node) :
    MemoryTable.fanoutMem node.label.1 = node.children.length := by
  have hbfsA : node ∈ bfsForest E.execA.memoryForest :=
    (mem_bfsForest _ _).2 ⟨root, hroot, hin⟩
  have hbfs : mapNTree (MemoryRowTemplate.encodeRow E.cfg.challenges.lam) node ∈
      bfsForest E.exec.memoryForest := by
    have hforest : E.exec.memoryForest =
        E.execA.memoryForest.map (mapNTree (MemoryRowTemplate.encodeRow E.cfg.challenges.lam)) := by
      rw [E.exec_encode]; rfl
    rw [hforest, bfsForest_mapNTree]
    exact List.mem_map_of_mem hbfsA
  have h := MemoryExactTopology.fanout_binding
    E.language.traversable.memory_topology _ hbfs
  simpa using h

private theorem toMTree_ofNTree_verify
    (Eexp : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (hst : t.label.1 = .verify_child)
    (hfo : MemoryTable.fanoutMem t.label.1 = t.children.length) :
    ∃ c, t.children = [c] ∧
      (ofNTree Eexp t).toMTree =
        MTree.verify (Eexp t) t.label.2.2.mem.axis (ofNTree Eexp c).toMTree := by
  cases t with
  | node lbl ch =>
      obtain ⟨st, data⟩ := lbl
      have hst' : st = .verify_child := by simpa [NTree.label_node] using hst
      subst hst'
      have hlen : ch.length = 1 := by
        have h := hfo
        simp only [MemoryTable.fanoutMem, NTree.label_node, NTree.children_node] at h
        omega
      obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hlen
      refine ⟨c, rfl, ?_⟩
      simp [ofNTree_verify, MemWalk.toMTree]

private theorem toMTree_ofNTree_read
    (Eexp : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (hst : t.label.1 = .read_root)
    (hfo : MemoryTable.fanoutMem t.label.1 = t.children.length) :
    ∃ c, t.children = [c] ∧
      (ofNTree Eexp t).toMTree =
        MTree.read (Eexp t) (ofNTree Eexp c).toMTree := by
  cases t with
  | node lbl ch =>
      obtain ⟨st, data⟩ := lbl
      have hst' : st = .read_root := by simpa [NTree.label_node] using hst
      subst hst'
      have hlen : ch.length = 1 := by
        have h := hfo
        simp only [MemoryTable.fanoutMem, NTree.label_node, NTree.children_node] at h
        omega
      obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hlen
      refine ⟨c, rfl, ?_⟩
      simp [ofNTree_read, MemWalk.toMTree]

private theorem toMTree_ofNTree_decompose
    (Eexp : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K))
    (hst : t.label.1 = .decompose)
    (hfo : MemoryTable.fanoutMem t.label.1 = t.children.length) :
    ∃ l r, t.children = [l, r] ∧
      (ofNTree Eexp t).toMTree =
        MTree.decompose (ofNTree Eexp l).toMTree (ofNTree Eexp r).toMTree := by
  cases t with
  | node lbl ch =>
      obtain ⟨st, data⟩ := lbl
      have hst' : st = .decompose := by simpa [NTree.label_node] using hst
      subst hst'
      have hlen : ch.length = 2 := by
        have h := hfo
        simp only [MemoryTable.fanoutMem, NTree.label_node, NTree.children_node] at h
        omega
      obtain ⟨l, r, rfl⟩ := List.length_eq_two.mp hlen
      refine ⟨l, r, rfl, ?_⟩
      simp [ofNTree_decompose, MemWalk.toMTree]

private theorem mem_of_singleton_children
    {s c : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    {data : MemoryTable.DTmem K} {st : MemoryTable.MState}
    {ch : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))}
    (hch : (NTree.node (st, data) ch).children = [c])
    (hs : s ∈ (NTree.node (st, data) ch).children) :
    s = c := by
  simpa [NTree.children_node, hch] using hs

private theorem mem_of_pair_children
    {s l r : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    {data : MemoryTable.DTmem K} {st : MemoryTable.MState}
    {ch : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))}
    (hch : (NTree.node (st, data) ch).children = [l, r])
    (hs : s ∈ (NTree.node (st, data) ch).children) :
    s = l ∨ s = r := by
  simpa [NTree.children_node, hch] using hs


private theorem verifyExp_mem_of_intree
    (Eexp : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ)
    {root node : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hin : InTree root node) (hst : node.label.1 = .verify_child)
    (hfo : ∀ u, InTree root u →
      MemoryTable.fanoutMem u.label.1 = u.children.length) :
    Eexp node ∈ verifyExps (ofNTree Eexp root).toMTree := by
  induction hin with
  | here t =>
      obtain ⟨c, _, hmt⟩ :=
        toMTree_ofNTree_verify Eexp t hst (hfo t (InTree.here t))
      simpa [hmt, verifyExps] using (List.mem_cons_self : _ ∈ _ :: _)
  | @sub root s node hs hin ih =>
      have hfo_s : ∀ u, InTree s u →
          MemoryTable.fanoutMem u.label.1 = u.children.length :=
        fun u hu => hfo u (InTree.sub hs hu)
      have ih' := ih hst hfo_s
      have hrootfo := hfo root (InTree.here root)
      cases root with
      | node lbl ch =>
          obtain ⟨st, data⟩ := lbl
          cases st with
          | halt =>
              have hlen : ch.length = 0 := by
                have h := hrootfo
                simp only [MemoryTable.fanoutMem, NTree.label_node,
                  NTree.children_node] at h
                omega
              obtain rfl := List.length_eq_zero_iff.mp hlen
              simp [NTree.children_node] at hs
          | decompose =>
              obtain ⟨l, r, hch, hmt⟩ :=
                toMTree_ofNTree_decompose Eexp (.node (.decompose, data) ch)
                  (by simp [NTree.label_node])
                  (by
                    have h := hrootfo
                    simpa [NTree.label_node, NTree.children_node] using h)
              rcases mem_of_pair_children hch hs with rfl | rfl
              · simpa [hmt, verifyExps] using List.mem_append.mpr (.inl ih')
              · simpa [hmt, verifyExps] using List.mem_append.mpr (.inr ih')
          | read_root =>
              obtain ⟨c, hch, hmt⟩ :=
                toMTree_ofNTree_read Eexp (.node (.read_root, data) ch)
                  (by simp [NTree.label_node])
                  (by
                    have h := hrootfo
                    simpa [NTree.label_node, NTree.children_node] using h)
              have := mem_of_singleton_children hch hs
              subst this
              simpa [hmt, verifyExps] using ih'
          | verify_child =>
              obtain ⟨c, hch, hmt⟩ :=
                toMTree_ofNTree_verify Eexp (.node (.verify_child, data) ch)
                  (by simp [NTree.label_node])
                  (by
                    have h := hrootfo
                    simpa [NTree.label_node, NTree.children_node] using h)
              have := mem_of_singleton_children hch hs
              subst this
              simpa [hmt, verifyExps] using List.mem_cons_of_mem _ ih'


private theorem vaxis_intree_verify
    (Eexp : NTree (MemoryTable.MState × MemoryTable.DTmem K) → ℕ)
    {root node : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (hin : InTree root node) (hst : node.label.1 = .verify_child)
    (hfo : ∀ u, InTree root u →
      MemoryTable.fanoutMem u.label.1 = u.children.length)
    (huniq :
      verifyCount (Eexp node) (ofNTree Eexp root).toMTree = 1) :
    vaxis (Eexp node) (ofNTree Eexp root).toMTree =
      node.label.2.2.mem.axis := by
  induction hin with
  | here t =>
      obtain ⟨c, _, hmt⟩ :=
        toMTree_ofNTree_verify Eexp t hst (hfo t (InTree.here t))
      simp [hmt, vaxis]
  | @sub root s node hs hin ih =>
      have hfo_s : ∀ u, InTree s u →
          MemoryTable.fanoutMem u.label.1 = u.children.length :=
        fun u hu => hfo u (InTree.sub hs hu)
      have hrootfo := hfo root (InTree.here root)
      cases root with
      | node lbl ch =>
          obtain ⟨st, data⟩ := lbl
          cases st with
          | halt =>
              have hlen : ch.length = 0 := by
                have h := hrootfo
                simp only [MemoryTable.fanoutMem, NTree.label_node,
                  NTree.children_node] at h
                omega
              obtain rfl := List.length_eq_zero_iff.mp hlen
              simp [NTree.children_node] at hs
          | decompose =>
              obtain ⟨l, r, hch, hmt⟩ :=
                toMTree_ofNTree_decompose Eexp (.node (.decompose, data) ch)
                  (by simp [NTree.label_node])
                  (by
                    have h := hrootfo
                    simpa [NTree.label_node, NTree.children_node] using h)
              have hsum :
                  verifyCount (Eexp node) (ofNTree Eexp l).toMTree +
                    verifyCount (Eexp node) (ofNTree Eexp r).toMTree = 1 := by
                simpa [hmt, verifyCount] using huniq
              rcases mem_of_pair_children hch hs with hsl | hsr
              · have hmem :=
                  verifyExp_mem_of_intree Eexp hin hst hfo_s
                have hpos :
                    0 < verifyCount (Eexp node) (ofNTree Eexp l).toMTree := by
                  rw [verifyCount_eq_count, ← hsl]
                  exact List.count_pos_iff.mpr hmem
                have hl :
                    verifyCount (Eexp node) (ofNTree Eexp l).toMTree = 1 := by
                  omega
                have hl_s :
                    verifyCount (Eexp node) (ofNTree Eexp s).toMTree = 1 := by
                  rw [hsl]; exact hl
                have ih' := ih hst hfo_s hl_s
                simpa [hmt, vaxis, hl, hsl] using ih'
              · have hmem :=
                  verifyExp_mem_of_intree Eexp hin hst hfo_s
                have hpos :
                    0 < verifyCount (Eexp node) (ofNTree Eexp r).toMTree := by
                  rw [verifyCount_eq_count, ← hsr]
                  exact List.count_pos_iff.mpr hmem
                have hr :
                    verifyCount (Eexp node) (ofNTree Eexp r).toMTree = 1 := by
                  omega
                have hvl :
                    ¬ verifyCount (Eexp node) (ofNTree Eexp l).toMTree = 1 := by
                  omega
                have hr_s :
                    verifyCount (Eexp node) (ofNTree Eexp s).toMTree = 1 := by
                  rw [hsr]; exact hr
                have ih' := ih hst hfo_s hr_s
                simpa [hmt, vaxis, hvl, hsr] using ih'
          | read_root =>
              obtain ⟨c, hch, hmt⟩ :=
                toMTree_ofNTree_read Eexp (.node (.read_root, data) ch)
                  (by simp [NTree.label_node])
                  (by
                    have h := hrootfo
                    simpa [NTree.label_node, NTree.children_node] using h)
              have hs_eq : s = c := mem_of_singleton_children hch hs
              have ih' := ih hst hfo_s (by
                rw [hs_eq]
                simpa [hmt, verifyCount] using huniq)
              simpa [hmt, vaxis, hs_eq] using ih'
          | verify_child =>
              obtain ⟨c, hch, hmt⟩ :=
                toMTree_ofNTree_verify Eexp (.node (.verify_child, data) ch)
                  (by simp [NTree.label_node])
                  (by
                    have h := hrootfo
                    simpa [NTree.label_node, NTree.children_node] using h)
              have hs_eq : s = c := mem_of_singleton_children hch hs
              by_cases he : Eexp (.node (.verify_child, data) ch) = Eexp node
              · have hcnt :
                    1 + verifyCount (Eexp node) (ofNTree Eexp c).toMTree = 1 := by
                  simpa [hmt, verifyCount, he] using huniq
                have hzeroC :
                    verifyCount (Eexp node) (ofNTree Eexp c).toMTree = 0 := by
                  omega
                have hmem :=
                  verifyExp_mem_of_intree Eexp hin hst hfo_s
                have hpos :
                    0 < verifyCount (Eexp node) (ofNTree Eexp c).toMTree := by
                  rw [verifyCount_eq_count, ← hs_eq]
                  exact List.count_pos_iff.mpr hmem
                exact (lt_irrefl _ (hzeroC ▸ hpos)).elim
              · have ih' := ih hst hfo_s (by
                  rw [hs_eq]
                  simpa [hmt, verifyCount, he] using huniq)
                simpa [hmt, vaxis, he, hs_eq] using ih'


theorem axisNat_of_read_root (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (h : (E.execA.memoryRowAt i).1 = .read_root)
    (hver : (E.execA.memoryRowAt i).2.2.ver = true) :
    ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) := by
  have ht := memoryBfsNodeA_mem E i
  obtain ⟨root, hroot, hin⟩ := (mem_bfsForest _ _).1 ht
  obtain ⟨r, hr⟩ := exists_memoryTreeAt_eq E.execA hroot
  have hlab : (memoryBfsNodeA E i).label = E.execA.memoryRowAt i :=
    memoryBfsNodeA_label E i
  have hmem :
      (E.execA.memoryRowAt i).2.2.mem ∈
        rootResponseRecords E.execA r := by
    refine List.mem_flatMap.mpr ⟨memoryBfsNodeA E i, ?_, ?_⟩
    · have : memoryBfsNodeA E i ∈ bfsForest [E.execA.memoryTreeAt r] := by
        rw [hr]
        exact (mem_bfsForest _ _).2 ⟨root, List.mem_singleton.mpr rfl, hin⟩
      exact this
    · simp [MemoryTable.responseRecords, hver, hlab]
  have hpart := (E.memoryTrace.roots r).recordPartition
  have hsvc :
      (E.execA.memoryRowAt i).2.2.mem ∈
        ((E.memoryTrace.roots r).services.map Service.record) := by
    simpa [hpart] using hmem
  obtain ⟨s, _, hs⟩ := List.mem_map.mp hsvc
  exact ⟨s.axis, by simpa [hs] using s.realization.axis_realizes⟩


theorem axisNat_of_verify_child (E : BuildableNockExecution F K)
    (i : Fin E.cfg.memRows)
    (h : (E.execA.memoryRowAt i).1 = .verify_child) :
    ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) := by
  have ht := memoryBfsNodeA_mem E i
  obtain ⟨root, hroot, hin⟩ := (mem_bfsForest _ _).1 ht
  obtain ⟨r, hr⟩ := exists_memoryTreeAt_eq E.execA hroot
  have hlab : (memoryBfsNodeA E i).label = E.execA.memoryRowAt i :=
    memoryBfsNodeA_label E i
  have hst : (memoryBfsNodeA E i).label.1 = .verify_child := by
    simpa [hlab] using h
  let Eexp := timestampExpAt E.cfg.challenges.α
  have hfo : ∀ u, InTree (E.execA.memoryTreeAt r) u →
      MemoryTable.fanoutMem u.label.1 = u.children.length := by
    intro u hu
    exact memory_fanout_of_intreeA E (by simpa [hr] using hroot)
      (by simpa [hr] using hu)
  have hin' : InTree (E.execA.memoryTreeAt r) (memoryBfsNodeA E i) := by
    simpa [hr] using hin
  have hmemE :
      Eexp (memoryBfsNodeA E i) ∈
        verifyExps (exactAxisTree E.cfg E.execA r) := by
    simpa [exactAxisTree, Eexp] using
      verifyExp_mem_of_intree Eexp hin' hst hfo
  have hts :=
    ExactServedMemoryTrace.rootTimestampPowersNodup E.memoryTrace r
  have hvnd := (E.memoryTrace.roots r).verifyExps_nodup hts
  have huniq :
      verifyCount (Eexp (memoryBfsNodeA E i))
        (ofNTree Eexp (E.execA.memoryTreeAt r)).toMTree = 1 := by
    simpa [exactAxisTree, Eexp] using
      verifyCount_eq_one_of_mem _ _ hvnd hmemE
  have hvaxis :=
    vaxis_intree_verify Eexp hin' hst hfo huniq
  have hread :
      Eexp (memoryBfsNodeA E i) ∈
        readExps (exactAxisTree E.cfg E.execA r) :=
    ((E.memoryTrace.roots r).support _).mpr
      (by simpa [exactAxisTree, Eexp] using hmemE)
  have hval :=
    (E.memoryTrace.roots r).axisValidity hts
      (Eexp (memoryBfsNodeA E i)) hread
  obtain ⟨n, hn⟩ := relaxis_is_nat_cast (Eexp (memoryBfsNodeA E i))
    (exactAxisTree E.cfg E.execA r)
  refine ⟨n, ?_⟩
  calc (E.execA.memoryRowAt i).2.2.mem.axis
      = (memoryBfsNodeA E i).label.2.2.mem.axis := by simp [hlab]
    _ = vaxis (Eexp (memoryBfsNodeA E i))
          (ofNTree Eexp (E.execA.memoryTreeAt r)).toMTree := hvaxis.symm
    _ = vaxis (Eexp (memoryBfsNodeA E i))
          (exactAxisTree E.cfg E.execA r) := by simp [exactAxisTree, Eexp]
    _ = Relaxis (Eexp (memoryBfsNodeA E i))
          (exactAxisTree E.cfg E.execA r) := hval
    _ = (n : K) := hn

/-- Live memory-table NMR addresses are Nat-casts already held on `E`.
`read_root` uses the service-record Nat-cast (`Def:NMR` the paper).
`verify_child` uses the walk's `vaxis = Relaxis` Nat-cast.
Under honest `ver`, every `read_root` row is emitted to `rootResponseRecords`.
-- -/
theorem axisNat_of_execution (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) := by
  intro i hact
  have he := exec_memoryRowAt_encode E i
  cases hst : (E.exec.memoryRowAt i).1 with
  | decompose => simp [memoryMemRecKind, hst] at hact
  | halt => simp [memoryMemRecKind, hst] at hact
  | read_root =>
      have hacc := memoryRowAccepted_of_execution E i
      have hst' : (E.exec.memoryRowAt i).2.2.st = .read_root := hacc.1.symm.trans hst
      have hver : (E.exec.memoryRowAt i).2.2.ver = true := by
        have h := hhon _ (ExactExecution.memoryRowAt_mem _ i)
        simpa [hst'] using h
      rw [he] at hst hver
      simp only [MemoryRowTemplate.encodeRow_fst, MemoryRowTemplate.encodeRow_ver] at hst hver
      exact axisNat_of_read_root E i hst hver
  | verify_child =>
      rw [he] at hst
      simp only [MemoryRowTemplate.encodeRow_fst] at hst
      exact axisNat_of_verify_child E i hst

/-- `timestampClosed` and honest `ver` stay named.
-- -/
def memoryRecordPremises_of_timestampClosed
    (E : BuildableNockExecution F K)
    (timestampClosed :
      ∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts)
    (honestVer :
      ∀ row ∈ E.exec.memoryRows,
        row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    MemoryRecordPremises E where
  axisNat := axisNat_of_execution E honestVer
  timestampClosed := timestampClosed
  honestVer := honestVer

theorem memoryRecordPremises_of_timestampClosed_fills_axisNat
    (E : BuildableNockExecution F K)
    (timestampClosed :
      ∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts)
    (honestVer :
      ∀ row ∈ E.exec.memoryRows,
        row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    (memoryRecordPremises_of_timestampClosed E timestampClosed honestVer).axisNat =
      axisNat_of_execution E honestVer :=
  rfl

/-- The two-field eta is unchanged.  Honest assembly fills `axisNat`.
`timestampClosed` remains a named premise. -- the paper -/
theorem memoryRecordPremises_still_two_after_axis_inventory
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨M.axisNat, M.timestampClosed⟩


theorem residual_pair_still_eleven_one_two : 11 + 1 + 2 = 14 :=
  rfl

/-! ## `timestampClosed` does not follow from inhabited `axisNat`

Paper closed form is existence `∃ e, ts = α^e` on live
NMR memory-record timestamps.  We inhabit the address extra
(`Def:NMR` the paper) as `∃ n, mem.axis = (n : K)` from
`recordPartition` / `vaxis = Relaxis`.  Those objects are the address
column, not timestamp space (`Def:NMR` the paper).  `verify_child`
still emits no external IO response (`responseRecords`).
The missing hypothesis remains field-equality of each `verify_child`
`mem.ts` with some `Service.record.ts`.  Record-level intermediate
matching `PairedRecordLayout` (`consumedRecordList.Perm addedRecordList`) would supply that identification, because added
records are already service records via `recordPartition`.  `E` carries
only `RecordCountBalanced` (row counts).
`verifyPartition` permutes wrapping MTree exponents, not records.
Wrapping `timestampExp` is not a witness.  This does not inhabit
`ForestExponentOrder`. -/

/-- `vaxis` at a matching verify node is the committed address, not a
timestamp. -- the paper -/
theorem vaxis_of_matching_verify (e : ℕ) (a : K) (c : MTree K) :
    vaxis e (.verify e a c) = a := by
  simp [vaxis]

/-- `Relaxis` at a verify node ignores the committed address and recurses.
It is the topological doubling, not `mem.ts`. -- the paper -/
theorem relaxis_at_verify_ignores_committed_axis
    (e e' : ℕ) (a : K) (c : MTree K) :
    Relaxis e (.verify e' a c) = Relaxis e c := by
  simp [Relaxis]

/-- Inhabited `axisNat` on a `verify_child` row is the address column.
-- -/
theorem axisNat_of_verify_child_is_address_column
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (h : (E.execA.memoryRowAt i).1 = .verify_child) :
    ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  axisNat_of_verify_child E i h

/-- `timestampExpAt` is wrapping `timestampExp` of that node's `mem.ts`.
Not a closed-form witness. -- the paper -/
theorem timestampExpAt_is_wrapping_timestampExp (α : K)
    (t : NTree (MemoryTable.MState × MemoryTable.DTmem K)) :
    timestampExpAt α t = timestampExp α (NTree.label t).2.2.mem.ts :=
  rfl

/-- Per-root `verifyPartition` permutes wrapping MTree exponents with
service exponents.  It is not a permutation of `MemRec`s.
-- -/
theorem verifyPartition_permutes_exponents
    (E : BuildableNockExecution F K) (i : Fin E.cfg.kMem) :
    (verifyExps (exactAxisTree E.cfg E.execA i)).Perm
      ((E.memoryTrace.roots i).services.map Service.exponent) :=
  (E.memoryTrace.roots i).verifyPartition

/-- `E` carries row-count balance, not record-list permutation.
-- -/
theorem execution_recordCountBalance_is_count_equality
    (E : BuildableNockExecution F K) :
    RowLayout.memoryStateCount E.exec .verify_child =
      RowLayout.memoryStateCount E.exec .read_root :=
  E.recordCountBalance

/-- `PairedRecordLayout` is the consumed/added `MemRec` permutation.
-- -/
theorem paired_record_layout_is_consumed_added_perm
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    RowLayout.PairedRecordLayout exec =
      (RowLayout.consumedRecordList exec).Perm
        (RowLayout.addedRecordList exec) :=
  rfl

/-- A `read_root` row's `mem` is in `addedRecordList` (by-state). -- the paper -/
theorem read_root_mem_in_addedRecordList
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .read_root) :
    (E.exec.memoryRowAt i).2.2.mem ∈ RowLayout.addedRecordList E.exec := by
  have hacc := memoryRowAccepted_of_execution E i
  have hst : (E.exec.memoryRowAt i).2.2.st = .read_root := hacc.1.symm.trans h
  refine List.mem_flatMap.mpr ⟨E.exec.memoryRowAt i, ?_, ?_⟩
  · exact ExactExecution.memoryRowAt_mem E.exec i
  · simp [hst]

/-- A `verify_child` row's `mem` is in `consumedRecordList`, not
`responseRecords`. -- the paper -/
theorem verify_child_mem_in_consumedRecordList
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .verify_child) :
    (E.exec.memoryRowAt i).2.2.mem ∈ RowLayout.consumedRecordList E.exec := by
  have hacc := memoryRowAccepted_of_execution E i
  have hst : (E.exec.memoryRowAt i).2.2.st = .verify_child :=
    hacc.1.symm.trans h
  refine List.mem_flatMap.mpr ⟨E.exec.memoryRowAt i, ?_, ?_⟩
  · exact ExactExecution.memoryRowAt_mem E.exec i
  · simp [RowLayout.consumedRecords, hst]

/-- Added `read_root` records are already service records via
`recordPartition`, under honest `ver`. -- the paper -/
theorem service_record_of_added
    {E : BuildableNockExecution F K} {r : ComputeTable.MemRec K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hr : r ∈ RowLayout.addedRecordList E.execA) :
    ∃ s : Service E.cfg E.execA, r = s.record := by
  obtain ⟨row, hrow, hresp⟩ := List.mem_flatMap.mp hr
  have hst : row.2.2.st = .read_root := by
    cases h : row.2.2.st <;> simp [h] at hresp ⊢
  have hr_eq : r = row.2.2.mem := by
    simpa [hst] using hresp
  have hrowE : MemoryRowTemplate.encodeRow E.cfg.challenges.lam row ∈ E.exec.memoryRows := by
    rw [E.exec_encode, ExactExecution.encodeMem_memoryRows]
    exact List.mem_map_of_mem hrow
  have hver : row.2.2.ver = true := by
    have h := hhon _ hrowE
    simp only [MemoryRowTemplate.encodeRow_ver, MemoryRowTemplate.encodeRow_st] at h
    simpa [hst] using h
  have hrows : row ∈ (bfsForest E.execA.memoryForest).map NTree.label := by
    simpa [ExactExecution.memoryRows] using hrow
  obtain ⟨node, hnode, hlab⟩ := List.mem_map.mp hrows
  obtain ⟨root, hroot, hin⟩ := (mem_bfsForest _ _).1 hnode
  obtain ⟨i, hi⟩ := exists_memoryTreeAt_eq E.execA hroot
  have hmem : r ∈ rootResponseRecords E.execA i := by
    refine List.mem_flatMap.mpr ⟨node, ?_, ?_⟩
    · have : node ∈ bfsForest [E.execA.memoryTreeAt i] := by
        rw [hi]
        exact (mem_bfsForest _ _).2 ⟨root, List.mem_singleton.mpr rfl, hin⟩
      exact this
    · simp [MemoryTable.responseRecords, hver, hlab, hr_eq]
  have hpart := (E.memoryTrace.roots i).recordPartition
  have hsvc :
      r ∈ ((E.memoryTrace.roots i).services.map Service.record) := by
    simpa [hpart] using hmem
  obtain ⟨s, _, hs⟩ := List.mem_map.mp hsvc
  exact ⟨s, hs.symm⟩

/-- The executed records added to `intermediate` are the row encodes of the a-bearing ones:
every executed added record has the timestamp of an a-bearing added record (28th). -/
theorem exec_added_ts_of_execA
    {E : BuildableNockExecution F K} {r : ComputeTable.MemRec K}
    (hr : r ∈ RowLayout.addedRecordList E.exec) :
    ∃ rA ∈ RowLayout.addedRecordList E.execA, r.ts = rA.ts := by
  obtain ⟨row, hrow, hresp⟩ := List.mem_flatMap.mp hr
  have hst : row.2.2.st = .read_root := by
    cases h : row.2.2.st <;> simp [h] at hresp ⊢
  have hr_eq : r = row.2.2.mem := by
    simpa [hst] using hresp
  rw [E.exec_encode, ExactExecution.encodeMem_memoryRows] at hrow
  obtain ⟨rowA, hrowA, rfl⟩ := List.mem_map.mp hrow
  simp only [MemoryRowTemplate.encodeRow_st] at hst
  refine ⟨rowA.2.2.mem, List.mem_flatMap.mpr ⟨rowA, hrowA, by simp [hst]⟩, ?_⟩
  rw [hr_eq]
  simp

/-- **Missing hypothesis after axisNat.**  Record-level intermediate
matching identifies every live `mem` with a `Service.record`, hence
inhabits `timestampClosed` via `Service.timestamp`.  Served/`read_root`
emissions already have that identification (`recordPartition`).
`verify_child` needs `consumedRecordList.Perm addedRecordList`.
-- -/
theorem identified_service_timestamps_of_paired_record_layout
    {E : BuildableNockExecution F K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : RowLayout.PairedRecordLayout E.exec) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        ∃ s : Service E.cfg E.execA,
          (E.exec.memoryRowAt i).2.2.mem.ts = s.record.ts := by
  intro i hact
  have hadd : (E.exec.memoryRowAt i).2.2.mem ∈ RowLayout.addedRecordList E.exec := by
    cases hst : (E.exec.memoryRowAt i).1 with
    | decompose => simp [memoryMemRecKind, hst] at hact
    | halt => simp [memoryMemRecKind, hst] at hact
    | read_root => exact read_root_mem_in_addedRecordList E i hst
    | verify_child =>
        have hcons := verify_child_mem_in_consumedRecordList E i hst
        have hperm :
            (RowLayout.consumedRecordList E.exec).Perm
              (RowLayout.addedRecordList E.exec) :=
          h
        exact hperm.mem_iff.mp hcons
  obtain ⟨rA, hrA, hts⟩ := exec_added_ts_of_execA hadd
  obtain ⟨s, hs⟩ := service_record_of_added hhon hrA
  exact ⟨s, by rw [hts, hs]⟩

/-- `PairedRecordLayout` inhabits the named extra, via the identification
above and already-held `Service.timestamp`. -- the paper -/
theorem timestampClosed_of_paired_record_layout
    {E : BuildableNockExecution F K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : RowLayout.PairedRecordLayout E.exec) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts := by
  intro i hact
  obtain ⟨s, hs⟩ := identified_service_timestamps_of_paired_record_layout hhon h i hact
  exact ⟨s.exponent, hs.trans s.timestamp⟩

/-- `PairedRecordLayout` plus honest `ver` inhabits the NMR extras.
PRL itself stays a Type extra, not a field of `E`. -- the paper -/
def memoryRecordPremises_of_paired_record_layout
    (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : RowLayout.PairedRecordLayout E.exec) :
    MemoryRecordPremises E :=
  memoryRecordPremises_of_timestampClosed E
    (timestampClosed_of_paired_record_layout hhon h) hhon

theorem memoryRecordPremises_of_paired_record_layout_fills_timestampClosed
    (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : RowLayout.PairedRecordLayout E.exec) :
    (memoryRecordPremises_of_paired_record_layout E hhon h).timestampClosed =
      timestampClosed_of_paired_record_layout hhon h :=
  rfl

/-- `Data` from C5, the modelling pin `q = ringChar K`, `PairedRecordLayout`,
honest `ver`, and the remaining census extras.  Not `∀ E`.
-- -/
def dataOfCertificates (E : BuildableNockExecution F K)
    (certs : ExactExecutionLocalCertificates E.semanticData)
    (hq : E.q = ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (C : CensusRecordPremises E
      (residualPremises_of_localCertificates E certs hq)
      (memoryRecordPremises_of_paired_record_layout E hhon hprl))
    (hln : FirstLineStartsAtOne E.exec) :
    Data E :=
  dataOfCensus E (residualPremises_of_localCertificates E certs hq)
    (memoryRecordPremises_of_paired_record_layout E hhon hprl) C hln

/-- Honest assembly still takes named `timestampClosed`. -- the paper -/
theorem memoryRecordPremises_of_timestampClosed_copies_timestampClosed
    (E : BuildableNockExecution F K)
    (timestampClosed :
      ∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts)
    (honestVer :
      ∀ row ∈ E.exec.memoryRows,
        row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    (memoryRecordPremises_of_timestampClosed E timestampClosed honestVer).timestampClosed =
      timestampClosed :=
  rfl

/-- After the axisNat inhabit and this inventory, both NMR extras remain on
the eta.  `timestampClosed` stays named. -- the paper -/
theorem memoryRecordPremises_still_two_after_timestamp_identification
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨M.axisNat, M.timestampClosed⟩

/-! ## `PairedRecordLayout` does not follow from forest / NMR / LogUp

Paper add/remove matches full `mem_record`s
on the two memory-table columns.  Honest `memoryForest` is the BFS source of
both lists and does not equate them.  Inverse-BFS `reconForest` roundtrips
the same labels.  NMR per-node carry
(`Def:NMR` the paper) binds the child noun and committed address
on `VerifyRoute` / `ServiceWalk`, not the `MemRec`.  LogUp on `E` is per-row
`interV`, adjacent `ipre`/`icur`,
wrapping-exponent `verifyPartition`, and reconstructed-timestamp `LmIO`
.  The upgrade of LogUp mass to a record perm is
`Thm:IO_result` on those two columns, which is
`PairedRecordLayout`.  This does not inhabit `ForestExponentOrder`. -/

/-- Added records are the by-state `read_root` emissions of the authoritative forest.
-- -/
theorem addedRecordList_from_memoryForest
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    RowLayout.addedRecordList exec =
      ((bfsForest exec.memoryForest).map NTree.label).flatMap
        (fun row =>
          match row.2.2.st with
          | .read_root => [row.2.2.mem]
          | .decompose | .halt | .verify_child => []) :=
  rfl

/-- Consumed records are the `verify_child` removals of the same forest.
-- -/
theorem consumedRecordList_from_memoryForest
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    RowLayout.consumedRecordList exec =
      ((bfsForest exec.memoryForest).map NTree.label).flatMap
        (fun row => RowLayout.consumedRecords row.2.2) :=
  rfl

/-- Inverse-BFS reconstruction roundtrips the same forest, including each
node's `mem`.  It does not permute consumed against added.
-- -/
theorem reconForest_roundtrip_is_label_equality
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E) :
    (memoryForestOf E M).map (mapNTree MemoryNode.row) = E.execA.memoryForest :=
  memoryForestOf_rows E M

/-- `VerifyRoute.here` binds the walked noun to the service child and the
committed address to the service axis.  It does not bind `mem.ts` or the
full `MemRec`. -- the paper -/
theorem verify_route_here_binds_child_and_address
    {e : ℕ} {child : Noun} {recAxis : K} {n : Noun} {a : K} {c : MTree K}
    (h : VerifyRoute e child recAxis [] n (.verify e a c)) :
    n = child ∧ a = recAxis := by
  cases h with
  | here hchild hcommitted => exact ⟨hchild, hcommitted⟩
  | verify_other hne => exact (hne rfl).elim

/-- `ServiceWalk.verify` recurses on the same noun.  It does not bind a
`MemRec`. -- the paper -/
theorem service_walk_verify_recurses_on_noun
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {services : List (Service cfg exec)} {n : Noun} {e : ℕ} {a : K}
    {c : MTree K} (h : ServiceWalk services n (.verify e a c)) :
    ServiceWalk services n c := by
  cases h with
  | verify below => exact below

/-- `recordPartition` identifies this root's `read_root` emissions with
service records.  There is no consumed-record field.
-- -/
theorem record_partition_is_read_root_emissions
    (E : BuildableNockExecution F K) (i : Fin E.cfg.kMem) :
    rootResponseRecords E.execA i =
      (E.memoryTrace.roots i).services.map Service.record :=
  (E.memoryTrace.roots i).recordPartition

/-- Exhaustive `RootTrace` fields: read-record partition, wrapping-exponent
partitions, and the noun-indexed walk.  No consumed-`MemRec` partition.
-- -/
theorem root_trace_has_read_records_and_exponent_partitions
    (E : BuildableNockExecution F K) (i : Fin E.cfg.kMem) :
    rootResponseRecords E.execA i =
        (E.memoryTrace.roots i).services.map Service.record ∧
      (readExps (exactAxisTree E.cfg E.execA i)).Perm
        ((E.memoryTrace.roots i).services.map Service.exponent) ∧
      (verifyExps (exactAxisTree E.cfg E.execA i)).Perm
        ((E.memoryTrace.roots i).services.map Service.exponent) ∧
      ServiceWalk (E.memoryTrace.roots i).services
        (E.memoryTrace.roots i).subject (exactAxisTree E.cfg E.execA i) :=
  ⟨(E.memoryTrace.roots i).recordPartition,
    (E.memoryTrace.roots i).readPartition,
    (E.memoryTrace.roots i).verifyPartition,
    (E.memoryTrace.roots i).traversal⟩

/-- Every accepted memory row satisfies `Vmem`.  That is the per-row
algorithmic verifier, not a record perm. -- the paper -/
theorem execution_vmem
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows) :
    MemoryTable.Vmem (E.exec.memoryRowAt i).2.1 (E.exec.memoryRowAt i).2.2 :=
  (memoryRowAccepted_of_execution E i).2.2.1

/-- `read_root` `interV` is the per-row add of `pole⁻¹`, not a list perm.
-- -/
theorem read_root_interV_is_pole_add
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .read_root) :
    let p := (E.exec.memoryRowAt i).2.2
    p.icur - p.ipre =
      (MemoryTable.pole (E.exec.memoryRowAt i).2.1 p.mem p.cprime)⁻¹ := by
  have hacc := memoryRowAccepted_of_execution E i
  have hst : (E.exec.memoryRowAt i).2.2.st = .read_root := hacc.1.symm.trans h
  have hinter :
      MemoryTable.interV (E.exec.memoryRowAt i).2.1 (E.exec.memoryRowAt i).2.2 :=
    hacc.2.2.1.2.2
  simpa [MemoryTable.interV, hst] using hinter

/-- `verify_child` `interV` is the per-row remove of `pole⁻¹`, not a list perm.
-- -/
theorem verify_child_interV_is_pole_remove
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (h : (E.exec.memoryRowAt i).1 = .verify_child) :
    let p := (E.exec.memoryRowAt i).2.2
    p.ipre - p.icur =
      (MemoryTable.pole (E.exec.memoryRowAt i).2.1 p.mem p.cprime)⁻¹ := by
  have hacc := memoryRowAccepted_of_execution E i
  have hst : (E.exec.memoryRowAt i).2.2.st = .verify_child :=
    hacc.1.symm.trans h
  have hinter :
      MemoryTable.interV (E.exec.memoryRowAt i).2.1 (E.exec.memoryRowAt i).2.2 :=
    hacc.2.2.1.2.2
  simpa [MemoryTable.interV, hst] using hinter

/-- Chained LogUp with zero boundaries forces equal pole mass, not
`List.Perm` of `MemRec`s.  The upgrade to a record perm is `Thm:IO_result`
. -- the paper -/
theorem interChain_balance_is_logup_mass
    (inp : MemoryTable.Inputs K) (rows : List (MemoryTable.Pub K))
    (h : MemoryTable.InterChain inp 0 0 rows) :
    ((rows.filter (fun p => decide (p.st = MemoryTable.MState.read_root))).map
        (fun p => (MemoryTable.pole inp p.mem p.cprime)⁻¹)).sum
      = ((rows.filter
            (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
          (fun p => (MemoryTable.pole inp p.mem p.cprime)⁻¹)).sum :=
  MemoryTable.interChain_balance inp rows h

/-- Structural `intermediate` matching on `E` is `LmIO` of reconstructed
`α^{timestampExp}` lists, not of live `MemRec`s.
-- -/
theorem execution_structural_intermediate_matching
    [DecidableEq K] (E : BuildableNockExecution F K) :
    IO.LmIO E.cfg.Ksz (forestReadTimestamps E.cfg E.execA)
      (forestVerifyTimestamps E.cfg E.execA) :=
  E.memoryTrace.intermediateMatching

/-- **Missing hypothesis.**  Paper intermediate matching at record level
: the `verify_child` remove list permutes with the
`read_root` add list.  This is
`PairedRecordLayout`.  It does not sit on `E`. -/
def IntermediateRecordMatching {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) : Prop :=
  RowLayout.PairedRecordLayout exec

/-- The missing pairing is definitionally the consumed/added `MemRec` perm.
-- -/
theorem intermediate_record_matching_is_paired_layout
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    IntermediateRecordMatching exec =
      (RowLayout.consumedRecordList exec).Perm
        (RowLayout.addedRecordList exec) :=
  rfl

/-- The already-compiled implication: record perm inhabits `timestampClosed`
under honest `ver`.  The perm remains an extra binder. -- the paper -/
theorem timestampClosed_of_intermediate_record_matching
    {E : BuildableNockExecution F K}
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (h : IntermediateRecordMatching E.exec) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts :=
  timestampClosed_of_paired_record_layout hhon h

/-- Honest assembly still takes named `timestampClosed`.  The two-field eta
is unchanged. -- the paper -/
theorem memoryRecordPremises_still_two_after_record_layout_inventory
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨M.axisNat, M.timestampClosed⟩

/-! ## The paper's `intermediate` accumulator IS on `E`, and the residual it leaves

The earlier analysis listed "LogUp on `E`" among the objects weaker than `PairedRecordLayout` but did not
assemble the accumulator.  It assembles.  the paper is the `read_root` ADD gate
`intermediate_{i+1} - intermediate_i = (RLC(mem_record) + X)^{-1}`; the paper is the
`verify_child` REMOVE gate `intermediate_i - intermediate_{i+1} = (RLC(mem_record) + X)^{-1}`;
the paper is the single row recurrence over the whole memory table; and
the paper pins the accumulator's initial and terminal values to zero *globally*
("a global terminal constraint check is required to ensure that the final value of
`intermediate` is zero, while its initial value is also constrained to be zero").  Every one of
those four is already carried: `MemoryRowAccepted` gives per-row `interV`, and
`ChainedSemanticExactLanguage` gives the adjacent hand-off `memory_chain` together with
`memory_first_ipre` and `memory_last_icur`.  So `execution_interChain` and
`execution_logup_mass_balanced` are **derived here, unconditionally** — the paper's own
accumulator, in record-list form, from objects already on `E`.

The mass is not the matching.  the paper upgrades the accumulator to the record-level
matching by `Thm:IO_result`, whose LDSE-to-MSE step (`Lem:ldse_mse` the paper,
`lem:set_inclusion` the paper) is an identity in the rational function field
`F(X, Y)` — not an implication at one sampled `(γ, β)`.
`logup_mass_does_not_determine_record_perm` compiles that separation at the real fixture field
`ZMod 97`: two `Nodup` two-record lists of equal length whose `pole⁻¹` masses agree and which
are not `List.Perm`.

The residual is therefore **sharpened, not removed**.  `addedRecordList` is already `Nodup` on
`E` (`addedRecordList_nodup`, from `requestNodup` plus `LmIO` through `cor_uni_req_uni_resp`),
and the two lists already have equal length (`E.recordCountBalance` through
`consumed_length_eq_added_length`), so the ONE remaining hypothesis is the paper's own single
inclusion at the paper — "every timestamp needs to be removed from the IO multiset, added
to `intermediate`, and then removed again" — namely `AddedRemovedAgain`.
`pairedRecordLayout_of_addedRemovedAgain` closes `PairedRecordLayout` from exactly that, and
`addedRemovedAgain_iff_pairedRecordLayout` shows the reduction is an *equivalence*, so nothing
was weakened or bundled.  `timestampClosed_of_addedRemovedAgain` then discharges
`MemoryRecordPremises.timestampClosed` through the already-compiled bridge.

Two compiled facts locate why the inclusion is not readable off `E`.  First, the equality block
leaves `mem.root` at `⊥` on a `verify_child` row: `verify_child_eqBlk_ignores_mem_root` re-accepts the row after arbitrary
garbage is written into the removed record's root, so `Vmem` never compares a removed record's
root with an added record's root and the `intermediate` pole is the only gate that sees it.
Second, the *exponent-list* layer cannot substitute for the *record-list* layer:
`root_trace_has_read_records_and_exponent_partitions` shows `RootTrace` has a record-level
partition on the read side only, and its verify side is `verifyExps`, whose entries are
`timestampExpAt α = timestampExp α mem.ts`.  `timestampExp_recovers_ts_iff_closed` proves that
`α ^ timestampExp α ts = ts` **iff** `TimestampClosedAt α ts`, so recovering a record from its
chosen exponent is equivalent to the timestamp closure that `timestampClosed` is asking for.
`MTree.verify` retains only `(ℕ, K)` — an exponent and an axis — so no `MemRec` survives into
`exactAxisTree` at all.

Carrying `AddedRemovedAgain` would need a verify-side record partition on
`ServedMemoryTrace.RootTrace`, i.e. a new field of `BuildableNockExecution`.  That is a carrier
extension and is NOT made here.  `ForestExponentOrder` is untouched, `ResidualPremises` stays
four, `MemoryRecordPremises` stays two, and `CensusRecordPremises` stays five. -/

/-- The memory table's `Pub` rows in BFS order — the ordered row list the paper's `intermediate`
accumulator runs over. -/

def memoryPubRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (MemoryTable.Pub K) :=
  exec.memoryRows.map (fun row => row.2.2)

theorem memoryPubRows_length {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    (memoryPubRows exec).length = cfg.memRows := by
  simp [memoryPubRows]

theorem memoryPubRows_getElem {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : ℕ) (h : i < cfg.memRows) :
    (memoryPubRows exec)[i]'(by rw [memoryPubRows_length]; exact h)
      = exec.memoryPubAt ⟨i, h⟩ := by
  simp [memoryPubRows, ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    List.get_eq_getElem]

/-- The adjacent hand-off plus the two global zero boundaries assemble the paper's ordered
`intermediate` accumulator over a row list. -/

theorem interChain_of_handoff (inp : MemoryTable.Inputs K) :
    ∀ (rows : List (MemoryTable.Pub K)) (seed term : K),
      (∀ p ∈ rows, MemoryTable.interV inp p) →
      (∀ i : ℕ, ∀ hi : i + 1 < rows.length,
          (rows[i]'(Nat.lt_of_succ_lt hi)).icur = (rows[i + 1]'hi).ipre) →
      (rows = [] → seed = term) →
      (∀ h0 : 0 < rows.length, (rows[0]'h0).ipre = seed) →
      (∀ h0 : 0 < rows.length,
          (rows[rows.length - 1]'(Nat.sub_lt h0 Nat.one_pos)).icur = term) →
      MemoryTable.InterChain inp seed term rows := by
  intro rows
  induction rows with
  | nil => intro seed term _ _ hnil _ _; exact hnil rfl
  | cons p rest ih =>
      intro seed term hall hadj _ hfirst hlast
      refine ⟨?_, hall p List.mem_cons_self, ?_⟩
      · exact hfirst (by simp)
      · refine ih p.icur term (fun q hq => hall q (List.mem_cons_of_mem _ hq)) ?_ ?_ ?_ ?_
        · intro i hi
          exact hadj (i + 1) (by simpa using hi)
        · intro hnil
          subst hnil
          exact hlast (by simp)
        · intro h0
          exact (hadj 0 (by simpa using h0)).symm
        · intro h0
          obtain ⟨m, hm⟩ : ∃ m, rest.length = m + 1 := ⟨rest.length - 1, by omega⟩
          have h := hlast (by simp)
          simp only [List.length_cons, hm, Nat.add_sub_cancel] at h ⊢
          exact h

/-- **Derived, not assumed.**  The whole ordered `intermediate` accumulator of the paper's memory
table, with both global zero boundaries, holds on `E`: per-row `interV` from
`MemoryRowAccepted`, the hand-off from `ChainedSemanticExactLanguage.memory_chain`, and the two
boundaries from `memory_first_ipre` / `memory_last_icur`. -/

theorem execution_interChain (E : BuildableNockExecution F K) :
    MemoryTable.InterChain E.cfg.challenges.memoryInputs 0 0 (memoryPubRows E.exec) := by
  have hlen := memoryPubRows_length E.exec
  refine interChain_of_handoff _ _ 0 0 ?_ ?_ (fun _ => rfl) ?_ ?_
  · intro p hp
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp
    have hacc := (ExactExecution.memoryRowsAccepted_iff E.exec).1
      E.chained.semantic.2.1 row hrow
    have hv := hacc.2.2.1
    rw [hacc.2.1] at hv
    exact hv.2.2
  · intro i hi
    rw [hlen] at hi
    rw [memoryPubRows_getElem E.exec i (by omega),
      memoryPubRows_getElem E.exec (i + 1) hi]
    exact E.chained.memory_chain ⟨i, by omega⟩ hi
  · intro _
    rw [memoryPubRows_getElem E.exec 0 E.cfg.memRows_pos]
    exact E.chained.memory_first_ipre
  · intro _
    have hpos := E.cfg.memRows_pos
    have hidx : (memoryPubRows E.exec).length - 1 = E.cfg.memRows - 1 := by rw [hlen]
    simp only [hidx]
    rw [memoryPubRows_getElem E.exec (E.cfg.memRows - 1) (by omega)]
    exact E.chained.memory_last_icur

/-- The `read_root` add column, in record-list form, is the `addedRecordList` mass. -/

theorem sum_pole_addedRecordList (inp : MemoryTable.Inputs K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    ((rows.flatMap fun row =>
          match row.2.2.st with
          | .read_root => [row.2.2.mem]
          | .decompose | .halt | .verify_child => []).map
        (fun r => (MemoryTable.pole inp r 1)⁻¹)).sum
      = (((rows.map (fun row => row.2.2)).filter
            (fun p => decide (p.st = MemoryTable.MState.read_root))).map
          (fun p => (MemoryTable.pole inp p.mem 1)⁻¹)).sum := by
  induction rows with
  | nil => simp
  | cons a t ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
        List.filter_cons]
      cases h : a.2.2.st <;> simp [h]

/-- The `verify_child` remove column, in record-list form, is the `consumedRecordList` mass. -/

theorem sum_pole_consumedRecordList (inp : MemoryTable.Inputs K)
    (rows : List (MemoryTable.MState × MemoryTable.DTmem K)) :
    ((rows.flatMap (fun row => RowLayout.consumedRecords row.2.2)).map
        (fun r => (MemoryTable.pole inp r 1)⁻¹)).sum
      = (((rows.map (fun row => row.2.2)).filter
            (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
          (fun p => (MemoryTable.pole inp p.mem 1)⁻¹)).sum := by
  induction rows with
  | nil => simp
  | cons a t ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
        List.filter_cons]
      cases h : a.2.2.st <;> simp [RowLayout.consumedRecords, h]

/-- **Derived, not assumed.**  On `E`, the added and consumed record lists carry equal LogUp
mass (dummy `C' = Pub.cprime`, `getD 1`).  This is the paper's `intermediate` balance. -/

theorem execution_logup_mass_balanced (E : BuildableNockExecution F K) :
    (((memoryPubRows E.exec).filter
        (fun p => decide (p.st = MemoryTable.MState.read_root))).map
        (fun p => (MemoryTable.pole E.cfg.challenges.memoryInputs p.mem p.cprime)⁻¹)).sum
      = (((memoryPubRows E.exec).filter
            (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
          (fun p => (MemoryTable.pole E.cfg.challenges.memoryInputs p.mem p.cprime)⁻¹)).sum :=
  MemoryTable.interChain_balance E.cfg.challenges.memoryInputs
    (memoryPubRows E.exec) (execution_interChain E)

/-- Under honest `ver`, raw memory responses ARE the added record list. -- the paper -/
theorem rawResponses_eq_addedRecordList {cfg : ExactConfig F K}
    (exec : ExactExecution cfg)
    (hhon : ∀ row ∈ exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    exec.rawResponses = RowLayout.addedRecordList exec :=
  RowLayout.rawResponses_eq_addedRecordList exec hhon

/-- `E.requestNodup` upgrades the semantic `LmIO` to `LIO`. -/

theorem execution_lio_of_requestNodup (E : BuildableNockExecution F K) :
    IO.LIO E.cfg.Ksz E.exec.derivedRequestIO E.exec.derivedResponseIO :=
  IO.cor_uni_req_uni_resp E.cfg.Ksz
    E.exec.derivedRequestIO E.exec.derivedResponseIO
    E.requestNodup (Classical.choice E.timestampBounds).derivedIO_lmio

/-- **Already held under honest `ver`.**  The added record list is repeat-free on `E`, because the
encoded responses are (`Def:unique_request` / `cor_uni_req_uni_resp`). -/

theorem addedRecordList_nodup (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    (RowLayout.addedRecordList E.exec).Nodup := by
  have h : ((RowLayout.addedRecordList E.exec).map
      (fun r => NockVM.encRecC r (E.exec.cprimeOf r))).Nodup := by
    have hnd := (execution_lio_of_requestNodup E).2.1
    rwa [ExactExecution.derivedResponseIO_eq_map_encRecC E.exec hC,
      rawResponses_eq_addedRecordList _ hhon] at hnd
  exact h.of_map _

/-- **The single remaining hypothesis for `PairedRecordLayout`.**  The paper's own sentence at
the paper: every record added to `intermediate` at a `read_root` row is removed again at a
`verify_child` row.  One direction only; the reverse inclusion, both `Nodup`s, and the counts
are already available. -/

def AddedRemovedAgain {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  ∀ r ∈ RowLayout.addedRecordList exec, r ∈ RowLayout.consumedRecordList exec

/-- **Already held.**  The two record lists have equal length, from `E.recordCountBalance`. -/

theorem consumed_length_eq_added_length (E : BuildableNockExecution F K) :
    (RowLayout.consumedRecordList E.exec).length
      = (RowLayout.addedRecordList E.exec).length := by
  rw [← RowLayout.verifyChildCount_eq_consumed_length,
    ← RowLayout.readRootCount_eq_added_length]
  exact E.recordCountBalance

/-- **The reduction.**  `PairedRecordLayout` follows from the paper's single inclusion, using
objects already on `E` plus honest `ver`: `addedRecordList_nodup` and
`consumed_length_eq_added_length`. -/

theorem pairedRecordLayout_of_addedRemovedAgain (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (h : AddedRemovedAgain E.exec) :
    RowLayout.PairedRecordLayout E.exec :=
  (((addedRecordList_nodup E hhon hC).subperm h).perm_of_length_le
    (le_of_eq (consumed_length_eq_added_length E))).symm

/-- The reduction is not a weakening in the other direction either. -- the paper -/
theorem addedRemovedAgain_of_pairedRecordLayout {cfg : ExactConfig F K}
    {exec : ExactExecution cfg} (h : RowLayout.PairedRecordLayout exec) :
    AddedRemovedAgain exec :=
  fun _ hr => h.mem_iff.mpr hr

/-- **The reduction is an equivalence at `E` under honest `ver`.** -/

theorem addedRemovedAgain_iff_pairedRecordLayout (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent) :
    AddedRemovedAgain E.exec ↔ RowLayout.PairedRecordLayout E.exec :=
  ⟨pairedRecordLayout_of_addedRemovedAgain E hhon hC, addedRemovedAgain_of_pairedRecordLayout⟩

/-- `timestampClosed` through the already-compiled bridge, from the sharpened hypothesis.
The hypothesis remains an extra binder; it is not derived from `E`. -/

theorem timestampClosed_of_addedRemovedAgain (E : BuildableNockExecution F K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : E.exec.CprimeCoherent)
    (h : AddedRemovedAgain E.exec) :
    ∀ i : Fin E.cfg.memRows,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
        MemoryTimestampClosedAt E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts :=
  timestampClosed_of_paired_record_layout hhon
    (pairedRecordLayout_of_addedRemovedAgain E hhon hC h)

/-- **Compiled negative.**  The paper's equality block leaves `mem.root` at `⊥` on a
`verify_child` row: an accepted
row's equality block stays satisfied after arbitrary garbage is written into the removed
record's root.  So `Vmem` never compares a removed record's root against an added record's
root; the `intermediate` pole is the only gate that sees it. -/

theorem verify_child_eqBlk_ignores_mem_root
    (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K)
    (hst : p.st = MemoryTable.MState.verify_child)
    (h : MemoryTable.eqBlk inp p) (root' : ComputeTable.FP K) :
    MemoryTable.eqBlk inp { p with mem := { p.mem with root := root' } } := by
  simp only [MemoryTable.eqBlk, hst] at h ⊢
  exact h

/-- **The exponent-list layer versus the record-list layer.**  `RootTrace`'s verify side is
`verifyExps`, whose entries are `timestampExpAt α = timestampExp α mem.ts`.  Recovering the
timestamp from that chosen exponent is *equivalent* to the timestamp closure
`timestampClosed` is asking for, so the exponent-list layer cannot supply the record-list
layer without circularity. -/

theorem timestampExp_recovers_ts_iff_closed [Fintype K] [DecidableEq K] (α ts : K) :
    α ^ timestampExp α ts = ts ↔ TimestampClosedAt α ts :=
  ⟨fun h => ⟨timestampExp α ts, h.symm⟩, fun h => (timestampExp_spec h).symm⟩

/-! ### Concrete separation at the fixture field -/

namespace AO109Concrete

/-- The F97 fixture base field. -/
abbrev F97ao := ZMod 97

local instance prime97ao : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- A record whose only nonzero component is its timestamp. -/
def tsOnlyRecord (t : F97ao) : ComputeTable.MemRec F97ao := ⟨0, 0, 0, t⟩

/-- LogUp challenges `(β, γ) = (0, 1)`, so the pole of a timestamp-only record is its
timestamp. -/
def massChallenges : MemoryTable.Inputs F97ao := ⟨0, 0, 1⟩


theorem pole_tsOnlyRecord (t : F97ao) :
    MemoryTable.pole massChallenges (tsOnlyRecord t) = t := by
  simp [MemoryTable.pole, MemoryTable.recRLC, tsOnlyRecord, massChallenges]

theorem inv_96 : (96 : F97ao)⁻¹ = 96 := inv_eq_of_mul_eq_one_right (by decide)
theorem inv_2 : (2 : F97ao)⁻¹ = 49 := inv_eq_of_mul_eq_one_right (by decide)
theorem inv_95 : (95 : F97ao)⁻¹ = 48 := inv_eq_of_mul_eq_one_right (by decide)

/-- **Compiled negative: equal LogUp mass is not the record matching.**  At the real fixture
field, two repeat-free two-record lists of equal length have equal `pole⁻¹` mass and are not a
`List.Perm`.  So `execution_logup_mass_balanced` cannot yield `PairedRecordLayout`; the paper's
upgrade is `Thm:IO_result`, whose LDSE-to-MSE step is an identity in
`F(X, Y)`, not at one sampled `(γ, β)`. -/

theorem logup_mass_does_not_determine_record_perm :
    ((([tsOnlyRecord 1, tsOnlyRecord 96]).map
        (fun r => (MemoryTable.pole massChallenges r)⁻¹)).sum
      = (([tsOnlyRecord 2, tsOnlyRecord 95]).map
          (fun r => (MemoryTable.pole massChallenges r)⁻¹)).sum)
    ∧ ([tsOnlyRecord 1, tsOnlyRecord 96] :
        List (ComputeTable.MemRec F97ao)).Nodup
    ∧ ([tsOnlyRecord 2, tsOnlyRecord 95] :
        List (ComputeTable.MemRec F97ao)).Nodup
    ∧ ([tsOnlyRecord 2, tsOnlyRecord 95] :
        List (ComputeTable.MemRec F97ao)).length
        = ([tsOnlyRecord 1, tsOnlyRecord 96] :
            List (ComputeTable.MemRec F97ao)).length
    ∧ ¬ ([tsOnlyRecord 2, tsOnlyRecord 95] :
          List (ComputeTable.MemRec F97ao)).Perm
            [tsOnlyRecord 1, tsOnlyRecord 96] := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      pole_tsOnlyRecord, inv_one, inv_96, inv_2, inv_95]
    decide
  · simp only [tsOnlyRecord, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, and_true, or_false, ComputeTable.MemRec.mk.injEq, true_and]
    decide
  · simp only [tsOnlyRecord, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, and_true, or_false, ComputeTable.MemRec.mk.injEq, true_and]
    decide
  · intro hp
    have hmem : tsOnlyRecord 2 ∈
        ([tsOnlyRecord 1, tsOnlyRecord 96] :
          List (ComputeTable.MemRec F97ao)) :=
      hp.mem_iff.mp List.mem_cons_self
    simp only [tsOnlyRecord, List.mem_cons, List.not_mem_nil, or_false,
      ComputeTable.MemRec.mk.injEq, true_and] at hmem
    revert hmem
    decide

end AO109Concrete

/-- Honest assembly still takes named `timestampClosed`.  The two-field eta is unchanged after
the earlier inventory. -- the paper -/
theorem memoryRecordPremises_still_two_after_logup_inventory
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K)) ∧
      (∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          MemoryTimestampClosedAt E.cfg.challenges.α
            (E.exec.memoryRowAt i).2.2.mem.ts) :=
  ⟨M.axisNat, M.timestampClosed⟩

end

end GenericHonestData
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.GenericHonestData.lnPrevExp_zero
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.lnPrevExp_succ
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.vcomp_ln
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.vcomp_mr1_ts
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.vcomp_active_record_ts
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.ln_prev_pow
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.ln_pow
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeTimestampSpecializesAt_of_residual
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeNodeAt_bind
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeNodeAt_specializes
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.mapNTree_buildTF
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeForestOf_rows
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeNodesOf_rows
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeNodesOf_ok
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.haltAtom_exists
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.bindFP_halt_parent
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.bindMemoryRow_of_assembly
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryTimestampSpecializesAt_of_assembly
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryForestOf_rows
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryNodesOf_rows
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryNodesOf_ok
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryAssemblyOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryRecordPremises_still_two
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOfRecord
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOf_retains_named_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOfRecord_memory_is_assembled
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeNodesOf_bfs_labels
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeSkeletonRows_of_assembly
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeSkeletonOf_recordEquations
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.recordEquations_of_assembly
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryParentNoun_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryChildNoun_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryMemRecSkel_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memorySkeletonOf_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryLabelAt_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryNodesOf_bfs_labels
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memorySkeletonRows_of_assembly
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memorySkeletonRows_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryTrees_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeSkeletonOf_root_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeSkeletonOf_subformula_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.served_lookup_of_s0_needs
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.served_lookup_of_s9_needs
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.skeletonSlotSemantics_of_s0_identification
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.skeletonSlotSemantics_of_s9_identification
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeSkeletonOf_s1_skeletonComparisons
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.sizeWindow_is_order_bound
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.axisAtomPremises_are_shape
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.atom_nine_not_bounded_by_two
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusAssemblyOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusRecordPremises_still_five
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusAssemblyOf_nounSizeBound
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusAssemblyOf_recordEquations
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOfCensus
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOfCensus_derived_fields
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.generic_data_would_force_q_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.residualPremises_still_four
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.firstLine_is_compute_ln_prev_eq_one
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.walkSat_ln1_is_sampled_alpha
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.walk_ln1_is_alpha_pow_one
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.walk_alpha_ne_compute_one
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.firstLine_of_residual
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.residual_q_eq_ringChar_is_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.execution_already_held_is_q_le
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.eleven_lt_and_q_le_do_not_give_q_eq
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.eleven_lt_char_does_not_give_eleven_lt_q
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.slotSemantics_is_noun_slot
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.served_lookup_of_axis_one
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.axisNat_is_memory_table_nat_cast
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusAssemblyOf_copies_slotSemantics
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.slotSemantics_of_s0_served_and_identification
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s0SlotFailRow_axis
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s0SlotFailRow_recordEquations
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s0SlotFailRow_slot_ne
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.slotSemantics_fails_of_atom_subject_axis_two
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.served_lookup_axis_one_holds_on_fail_subject
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.slotSemantics_does_not_follow_from_records_or_axis_one
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s0SlotFailSkeleton_computeRows
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.slotSemantics_forall_fails_on_atom_axis_two
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.census_is_skeleton_pair_leaf_bounds
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusAssemblyOf_copies_census
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.comparison_leaves_quantify_data_comparisons
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.census_of_identified_skeleton_pairs
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1CensusFailRow_formula_leaves
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1CensusFailRow_recordEquations
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1FreeComparisons_roles
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1FreeComparisons_leaves_le_one
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1FreeComparisons_ne_skeletonComparisons
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1CensusFailSkeleton_computeRows
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1CensusFailSkeleton_formula_pair_mem
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.census_fails_of_two_leaf_formula
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.census_does_not_follow_from_records_or_free_comparison_leaves
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1CensusFailSkeleton_sizeWindowBound_vacuous
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.skeletonBounded_is_q_atom_range
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.atom_two_one_leaf_not_bounded_by_two
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusAssemblyOf_copies_skeletonBounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusAssemblyOf_copies_combinedBounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memRecSkelOf_bounded_of_decomp
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeSkeletonOf_bounded_of_decomp
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.skeletonBounded_of_decomp_bounds
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1DecompFailRow_recordEquations
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1DecompFailRow_root_subformula_memory_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1DecompFailSkeleton_computeRows
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.skeletonBounded_fails_of_decomp_atom_two
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1DecompFailSkeleton_census
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s1DecompFailSkeleton_sizeWindowBound_vacuous
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.skeletonBounded_does_not_follow_from_census_or_sizeWindow
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.combinedBounded_is_pair_atom_range
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.opcode_atom_bounded_of_eleven_lt
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.atomVal_lt_of_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.skeletonDec_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.skeletonSubformula_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.incMod_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.skeletonComparisons_pair_bounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.combinedBounded_of_skeletonBounded_and_axis_range
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeSkeletonOf_s0_memoryAxis
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeSkeletonOf_slotSemantics_of_s0
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.computeSkeletonOf_s9_memoryAxis
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.assembled_axis_range_of_skeletonBounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.combinedBounded_of_skeletonBounded_at_consumed_q
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.combinedBounded_at_consumed_q_still_names_q_eq
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusRecordPremises_of_skeletonBounded
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.censusRecordPremises_of_skeletonBounded_fills_combined
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOfCensusAtConsumed
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s0AxisFailRow_bounded_by_twelve
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.s0AxisFailRow_memoryAxis
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.combinedBounded_not_restatement_at_consumed_q
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.vaddr_is_nat_cast
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.relaxis_is_nat_cast
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.service_axis_is_nat_cast
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.axisNat_of_read_root
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.axisNat_of_verify_child
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.axisNat_of_execution
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryRecordPremises_of_timestampClosed
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryRecordPremises_of_timestampClosed_fills_axisNat
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryRecordPremises_still_two_after_axis_inventory
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.residual_pair_still_eleven_one_two
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.vaxis_of_matching_verify
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.relaxis_at_verify_ignores_committed_axis
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.axisNat_of_verify_child_is_address_column
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.timestampExpAt_is_wrapping_timestampExp
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.verifyPartition_permutes_exponents
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.execution_recordCountBalance_is_count_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.paired_record_layout_is_consumed_added_perm
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.read_root_mem_in_addedRecordList
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.verify_child_mem_in_consumedRecordList
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.service_record_of_added
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.identified_service_timestamps_of_paired_record_layout
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.timestampClosed_of_paired_record_layout
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryRecordPremises_of_paired_record_layout
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryRecordPremises_of_paired_record_layout_fills_timestampClosed
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOfCertificates
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryRecordPremises_of_timestampClosed_copies_timestampClosed
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryRecordPremises_still_two_after_timestamp_identification
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.addedRecordList_from_memoryForest
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.consumedRecordList_from_memoryForest
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.reconForest_roundtrip_is_label_equality
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.verify_route_here_binds_child_and_address
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.service_walk_verify_recurses_on_noun
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.record_partition_is_read_root_emissions
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.root_trace_has_read_records_and_exponent_partitions
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.execution_vmem
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.read_root_interV_is_pole_add
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.verify_child_interV_is_pole_remove
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.interChain_balance_is_logup_mass
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.execution_structural_intermediate_matching
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.intermediate_record_matching_is_paired_layout
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.timestampClosed_of_intermediate_record_matching
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryRecordPremises_still_two_after_record_layout_inventory
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryPubRows_length
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryPubRows_getElem
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.interChain_of_handoff
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.execution_interChain
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.sum_pole_addedRecordList
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.sum_pole_consumedRecordList
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.execution_logup_mass_balanced
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.rawResponses_eq_addedRecordList
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.execution_lio_of_requestNodup
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.addedRecordList_nodup
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.consumed_length_eq_added_length
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.pairedRecordLayout_of_addedRemovedAgain
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.addedRemovedAgain_of_pairedRecordLayout
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.addedRemovedAgain_iff_pairedRecordLayout
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.timestampClosed_of_addedRemovedAgain
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.verify_child_eqBlk_ignores_mem_root
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.timestampExp_recovers_ts_iff_closed
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.AO109Concrete.pole_tsOnlyRecord
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.AO109Concrete.logup_mass_does_not_determine_record_perm
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryRecordPremises_still_two_after_logup_inventory
