/-
  Nock/RedTeam/Batch24A1Thm54StrictCommitment.lean

  Three attacks are run, and all three are answered by compiled artifacts rather than prose.

  1. **Vacuity.**  Are `CanonicalCommitmentCheck` and `ActiveFingerprintChecks` jointly satisfiable at
     all, or is the whole packet a statement about an empty premise?  `b24a1_jointly_nonvacuous`
     exhibits a complete concrete witness over `ℚ` — an explicit `ExactConfig`/`ExactExecution`, raw
     family and raw message, a one-compute-row/one-memory-row commitment passing
     `CanonicalCommitmentCheck 3`, and the post-seed scan passing at *every* seed `z`.  The scanned
     list is nonempty (`b24a1_sample_scan_ne_nil`), so the check is not satisfied by having nothing to
     check.  `b24a1_strictStrategy_nonvacuous` inhabits `StrictRawP8Strategy` itself.

  2. **Post-seed noun selection.**  Can a prover pick the semantic nouns after seeing `z` and still
     inhabit the type?  No: `beforeSeed` is a field, so the commitment schedule of any strict strategy
     is constant (`b24a1_strict_commitment_is_constant`).  The separation is *proper*, not a
     tautology: `b24a1_loose_schedule_admits_post_seed_choice` compiles a seed-dependent commitment
     schedule over `ℚ` that the loose interface accepts and the strict type cannot express.

  3. **Non-noun forgery.**  `NounRealizationCounterRegression.badFP` is a publicly acceptable
     fingerprint with no bounded-noun preimage.  `b24a1_badFP_fails_active_scan` shows it can never be
     a scanned active fingerprint of a canonically committed strategy, because the scan's consequence
     is exactly the `BoundGates.LeafBoundGate` (`FPRealized`) that `badFP` provably fails.

  Nothing below assumes acceptance.
-/

import Nock.NockVMROM.Thm54.StrictRawStrategy
import Nock.RedTeam.Batch21Thm54ActiveRealization

namespace Nock.RedTeam.Batch24A1

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.ActiveFingerprintScan
open Nock.NockVMROM.Thm54.StrictRawStrategy

noncomputable section

/-! ## A concrete raw family over `ℚ`

Everything below is a literal value: a single-generator orbit of capacity `2`, one compute row in
state `.s1` (`fanoutComp = 0`, `recordCount = 1`) and one `halt` memory row, so both carriers are
leaves. -/

/-- BFS of a one-node forest is that node. -/
theorem bfs_singleton_leaf {LT : Type} (x : LT) :
    bfsForest [NTree.node x []] = [NTree.node x []] := by
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- A genuine single-generator orbit over `ℚ`: `ω = -1` has multiplicative order `2 = 2 ^ 1`. -/
def qOrbit : Nock.Framework.Thm54.OrbitDomain ℚ where
  h := 1
  ω := -1
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := by simp [orderOf_neg_one]

/-- Compute-table inputs carrying the sampled seed. -/
def sampleInputs (z : ℚ) : ComputeTable.Inputs ℚ :=
  { α := 0, z := z, a := 0, b := 0, c := 0 }

/-- Memory-table inputs carrying the sampled seed. -/
def sampleMemInputs (z : ℚ) : MemoryTable.Inputs ℚ :=
  { z := z, β := 0, γ := 0 }

/-- The committed public compute row: its live fingerprints are exactly the NPR encodings of the
pre-committed nouns of `StrictCommitment.sampleComputeRow`; every padding slot is exact zero. -/
def samplePub (z : ℚ) : ComputeTable.Pub ℚ where
  state := .s1
  s := GlobalCarryRecognizer.enc z (.atom 0)
  f := GlobalCarryRecognizer.enc z (.cell (.atom 1) (.atom 2))
  e := GlobalCarryRecognizer.enc z (.atom 2)
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 0
  ln := 0
  mr1 :=
    { root := GlobalCarryRecognizer.enc z (.atom 0)
      child := GlobalCarryRecognizer.enc z (.atom 2)
      axis := ((1 : ℕ) : ℚ)
      ts := 0 }
  mr2 := ComputeTable.MemRec.zero
  mr3 := ComputeTable.MemRec.zero

/-- The committed private decomposition columns: `f_h`/`f_t` live, the rest exact zero padding. -/
def sampleDec (z : ℚ) : ComputeTable.Dec ℚ where
  f_h := GlobalCarryRecognizer.enc z (.atom 1)
  f_t := GlobalCarryRecognizer.enc z (.atom 2)
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

/-- The single committed compute execution row. -/
def sampleComputeExecRow (z : ℚ) : ComputeTable.State × ComputeTable.DTcomp ℚ :=
  (.s1, sampleInputs z, samplePub z, sampleDec z)

/-- The committed public memory row: a `halt` leaf whose parent fingerprint encodes the precommitted
Nat atom, with whole-cell zero children and a padding memory record. -/
def sampleMemPub (z : ℚ) : MemoryTable.Pub ℚ where
  st := .halt
  pt := { noun := GlobalCarryRecognizer.enc z (.atom 2), indicator := 0, counts := 0 }
  lc := MemoryTable.Cell.zero
  rc := MemoryTable.Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := ComputeTable.MemRec.zero
  ipre := 0
  icur := 0

/-- The single committed memory execution row. -/
def sampleMemoryExecRow (z : ℚ) : MemoryTable.MState × MemoryTable.DTmem ℚ :=
  (.halt, sampleMemInputs z, sampleMemPub z)

/-- A complete concrete exact configuration at seed `z`. -/
def sampleCfg (z : ℚ) : ExactConfig ℚ ℚ where
  challenges := { a := 0, b := 0, c := 0, α := 0, z := z, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 0
  kMem := 1
  orbit := qOrbit
  orbit_h_pos := by norm_num [qOrbit]
  compRows := 1
  memRows := 1
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [qOrbit]
  memRows_le := by norm_num [qOrbit]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => qOrbit.βcoset * qOrbit.ω ^ (i : ℕ)
  compNodes_spec := fun _ => rfl
  memNodes := fun i => qOrbit.βcoset * qOrbit.ω ^ (i : ℕ)
  memNodes_spec := fun _ => rfl

/-- The concrete forest-first execution: one compute leaf, one memory leaf. -/
def sampleExec (z : ℚ) : ExactExecution (sampleCfg z) where
  computeTree := .node (sampleComputeExecRow z) []
  memoryForest := [.node (sampleMemoryExecRow z) []]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by rw [bfs_singleton_leaf]; rfl
  memory_bfs_length := by rw [bfs_singleton_leaf]; rfl

/-- The concrete raw family. -/
def sampleFamily (z : ℚ) : RawPlusIOSegmentedFamily ℚ ℚ where
  problem := { cfg := sampleCfg z, exec := sampleExec z }
  computeWalkAlpha := 0
  memoryWalkAlpha := 0
  walkGamma := 0
  compNodeWidth := 0
  compNodeEncode := fun _ i => i.elim0
  memNodeWidth := 0
  memNodeEncode := fun _ i => i.elim0
  requests := 0
  responses := 0
  outMem := 0

/-- The concrete raw prover message at modular prime `3`. -/
def sampleMessage (z : ℚ) : RawMessage (sampleFamily z) 3 where
  tables :=
    { compute := fun _ => { consInv := 0, invGen := 0 }
      memory := fun _ => 0 }
  walks :=
    { computeLn := fun _ => 0
      computeCount := fun _ => 0
      computeAcc := fun _ => 0
      memoryLn := fun _ => 0
      memoryCount := fun _ => 0
      memoryAcc := fun _ => 0 }
  io :=
    { multiplicity := fun _ => 0
      progAcc := fun _ => 0
      memAcc := fun _ => 0 }

theorem sampleFamily_computeRows (z : ℚ) :
    (sampleFamily z).exec.computeRows = [sampleComputeExecRow z] := by
  have h : (sampleFamily z).exec.computeTree = .node (sampleComputeExecRow z) [] := rfl
  unfold ExactExecution.computeRows
  rw [h, bfs_singleton_leaf]
  rfl

theorem sampleFamily_memoryRows (z : ℚ) :
    (sampleFamily z).exec.memoryRows = [sampleMemoryExecRow z] := by
  have h : (sampleFamily z).exec.memoryForest = [.node (sampleMemoryExecRow z) []] := rfl
  unfold ExactExecution.memoryRows
  rw [h, bfs_singleton_leaf]
  rfl

/-! ## Attack 1: vacuity -/

/-- The concrete compute row really is bound to the pre-seed skeleton row. -/
theorem sample_bindComputeRow (z : ℚ) :
    SemanticStrategy.BindComputeRow z sampleComputeRow (sampleComputeExecRow z) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [SemanticStrategy.decActive, SemanticStrategy.hasTailDecomposition,
        SemanticStrategy.decFP, SemanticStrategy.bindFP, sampleComputeRow,
        sampleComputeExecRow, sampleDec]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp sampleComputeRow.state) := by
      simp [sampleComputeRow, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, sampleComputeExecRow, samplePub]
  · intro i
    have hrc : Nock.Framework.recordCount sampleComputeRow.state = 1 := rfl
    have hlt : (i : ℕ) < 3 := i.isLt
    by_cases hi : (i : ℕ) < Nock.Framework.recordCount sampleComputeRow.state
    · rw [dif_pos hi]
      have hi' : (i : ℕ) < 1 := by rwa [hrc] at hi
      have h0 : i = (0 : Fin 3) := Fin.eq_of_val_eq (by simpa using (by omega : (i : ℕ) = 0))
      subst h0
      exact ⟨rfl, rfl, rfl⟩
    · rw [dif_neg hi]
      have hi' : ¬ ((i : ℕ) < 1) := by rwa [hrc] at hi
      rcases (by omega : (i : ℕ) = 1 ∨ (i : ℕ) = 2) with hv | hv
      · have h1 : i = (1 : Fin 3) := Fin.eq_of_val_eq (by simpa using hv)
        subst h1
        rfl
      · have h2 : i = (2 : Fin 3) := Fin.eq_of_val_eq (by simpa using hv)
        subst h2
        rfl

/-- The concrete memory row really is bound to the pre-seed skeleton row. -/
theorem sample_bindMemoryRow (z : ℚ) :
    SemanticStrategy.BindMemoryRow z sampleMemoryRow (sampleMemoryExecRow z) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem sampleMemoryRow.state) := by
      simp [sampleMemoryRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rw [dif_neg (by decide : ¬ (memoryMemRecKind sampleMemoryRow.state = .active))]
    rfl

/-- **The post-seed scan passes at every seed.** -/
theorem sample_activeFingerprintChecks (z : ℚ) :
    ActiveFingerprintChecksOn z sampleCommitment (sampleFamily z) := by
  apply activeFingerprintChecksOn_of_forall₂
  · rw [sampleCommitment_computeRows, sampleFamily_computeRows]
    exact .cons (sample_bindComputeRow z) .nil
  · rw [sampleCommitment_memoryRows, sampleFamily_memoryRows]
    exact .cons (sample_bindMemoryRow z) .nil

/-- The scanned list is genuinely nonempty: there is something for the check to check. -/
theorem b24a1_sample_scan_ne_nil (z : ℚ) :
    activeComputeSlotsOn sampleCommitment (sampleFamily z) ≠ [] := by
  intro h
  have hmem :
      (computeSlotNoun sampleComputeRow .subject,
          computeSlotFP (sampleComputeExecRow z) .subject) ∈
        activeComputeSlotsOn sampleCommitment (sampleFamily z) := by
    refine mem_activeComputeSlotsOn_of_mem_zip ?_ (mem_computeRowSlots _ _ (a := .subject) rfl)
    rw [sampleCommitment_computeRows, sampleFamily_computeRows]
    simp
  rw [h] at hmem
  simp at hmem

/-- One
concrete commitment over `ℚ` passes the seed-independent `CanonicalCommitmentCheck 3`, and, at every
seed, the concrete raw message's committed fingerprints pass the active-fingerprint scan against that
same commitment — with a nonempty scan list. -/
theorem b24a1_jointly_nonvacuous (z : ℚ) :
    CanonicalCommitmentCheck 3 sampleCommitment ∧
      ActiveFingerprintChecks 3 z sampleCommitment (sampleMessage z) ∧
      activeComputeSlotsOn sampleCommitment (sampleFamily z) ≠ [] :=
  ⟨sampleCommitment_canonical.1, sample_activeFingerprintChecks z,
    b24a1_sample_scan_ne_nil z⟩

/-- Every scanned active compute fingerprint of the concrete witness is a genuine bounded-noun
encoding — the leaf/decode bound gate holds, on a real inhabited instance. -/
theorem b24a1_sample_scan_realized (z : ℚ)
    {fp : ComputeTable.FP ℚ}
    (hfp : fp ∈ activeComputeFingerprints sampleCommitment (sampleFamily z)) :
    FPRealized z 3 fp :=
  activeComputeFingerprints_realized sampleCommitment_canonical.1
    (sample_activeFingerprintChecks z) hfp

/-- The concrete strict raw strategy: the commitment is fixed once, the post-seed data is the same
concrete family/message at each seed, and the coin continuation is zero arrays. -/
def sampleStrategy : StrictRawP8Strategy ℚ ℚ 3 where
  claim := sampleCommitment.skeleton.publicClaim
  beforeSeed := sampleCommitment
  claim_eq := rfl
  afterSeed := fun z _ =>
    { family := sampleFamily z
      message := sampleMessage z
      sampledSeed := rfl
      fingerprintChecks := sample_activeFingerprintChecks z }
  afterCoins := fun _ _ =>
    { topology :=
        { compute := { childPayload := fun _ _ => ComputeLinkPayload.zero }
          memory := { childPayload := fun _ _ => MemoryTable.Cell.zero } }
      walks :=
        { computeLn := fun _ => 0
          computeCount := fun _ => 0
          computeAcc := fun _ => 0
          memoryLn := fun _ => 0
          memoryCount := fun _ => 0
          memoryAcc := fun _ => 0 } }

/-- **The strict raw strategy type is inhabited**, so every A1 statement about it concerns a
satisfiable interface. -/
theorem b24a1_strictStrategy_nonvacuous :
    Nonempty (StrictRawP8Strategy ℚ ℚ 3) ∧
      sampleStrategy.beforeSeed = sampleCommitment :=
  ⟨⟨sampleStrategy⟩, rfl⟩

/-- The concrete strategy's own capstone: at every nonzero seed, every scanned fingerprint is a
bounded-noun encoding, from the two deterministic checks alone. -/
theorem b24a1_sampleStrategy_realized (z : ℚ) (hz : z ≠ 0)
    {fp : ComputeTable.FP ℚ}
    (hfp : fp ∈
      activeComputeFingerprints sampleStrategy.beforeSeed
        (sampleStrategy.afterSeed z hz).family) :
    FPRealized z 3 fp :=
  sampleStrategy.scanned_fingerprint_realized sampleCommitment_canonical.1 z hz hfp

/-! ## Attack 2: post-seed noun selection -/

/-- **The strict type cannot select nouns after the seed.**  Its commitment schedule is constant, by
`rfl`: `beforeSeed` is a field, not a function of `z`. -/
theorem b24a1_strict_commitment_is_constant
    {F K : Type} [Field F] [Field K] [Algebra F K] {p : ℕ}
    (T : StrictRawP8Strategy F K p) (z₁ z₂ : K) (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    T.looseSchedule z₁ h₁ = T.looseSchedule z₂ h₂ ∧
      T.looseSchedule z₁ h₁ = T.beforeSeed :=
  ⟨T.looseSchedule_const z₁ z₂ h₁ h₂, rfl⟩

/-- A seed-dependent commitment schedule: the very behaviour the strict type forbids. -/
def postSeedChosenSchedule : StrictRawP8Strategy.LooseCommitmentSchedule ℚ :=
  fun z _ =>
    { skeleton := sampleCommitment.skeleton
      nounSizeBound := if z = 1 then 2 else 3 }

/-- **Attack 2 answered, and the separation is proper.**  The loose interface really does admit a
commitment chosen after `z` — here the committed size bound differs at `z = 1` and `z = 2` — so
`b24a1_strict_commitment_is_constant` is a genuine restriction on the prover, not a tautology about an
interface that could not vary anyway. -/
theorem b24a1_loose_schedule_admits_post_seed_choice :
    postSeedChosenSchedule 1 one_ne_zero ≠ postSeedChosenSchedule 2 two_ne_zero := by
  intro h
  have := congrArg SkeletonCommitment.nounSizeBound h
  simp [postSeedChosenSchedule] at this

/-- No strict strategy's schedule is the post-seed chooser: the strict interface is strictly
contained in the loose one. -/
theorem b24a1_no_strict_strategy_chooses_post_seed
    (T : StrictRawP8Strategy ℚ ℚ 3) :
    T.looseSchedule ≠ postSeedChosenSchedule := by
  intro h
  apply b24a1_loose_schedule_admits_post_seed_choice
  rw [← h]
  exact T.looseSchedule_const 1 2 one_ne_zero two_ne_zero

/-! ## Attack 3: non-noun forgery -/

/-- **Attack 3 answered: the active scan excludes the non-noun forgery.**  `badFP` has no bounded-noun
preimage at `z = 1`, so it cannot appear among the scanned active compute fingerprints of any
canonically committed family — for any modular prime `p`.  This is the leaf/decode bound gate of
`BoundGates`, now discharged by the two deterministic A1 checks instead of assumed. -/
theorem b24a1_badFP_fails_active_scan (p : ℕ)
    {C : SkeletonCommitment}
    {R : RawPlusIOSegmentedFamily NounRealizationCounterRegression.K289
      NounRealizationCounterRegression.K289}
    (hcanon : CanonicalCommitmentCheck p C)
    (hcheck : ActiveFingerprintChecksOn
      (1 : NounRealizationCounterRegression.K289) C R) :
    NounRealizationCounterRegression.badFP ∉ activeComputeFingerprints C R := by
  intro hmem
  exact NounRealizationCounterRegression.badFP_not_realized p
    (activeComputeFingerprints_realized hcanon hcheck hmem)

/-- Re-export of the standing fact that makes attack 3 non-trivial: `badRow` is *publicly accepted*
and yet realizes no noun, so plain acceptance does not exclude it — only the leaf/decode gate that the
A1 scan now discharges does. -/
theorem b24a1_badRow_accepted_but_unrealized (q : ℕ) :
    MemoryPublicRowAccepted NounRealizationCounterRegression.badRow ∧
      ¬ MemoryPublicRowNounRealization q NounRealizationCounterRegression.badRow :=
  BoundGates.leafBoundGate_rejects_badRow q

end

end Nock.RedTeam.Batch24A1

#print axioms Nock.RedTeam.Batch24A1.bfs_singleton_leaf
#print axioms Nock.RedTeam.Batch24A1.sampleFamily_computeRows
#print axioms Nock.RedTeam.Batch24A1.sampleFamily_memoryRows
#print axioms Nock.RedTeam.Batch24A1.sample_bindComputeRow
#print axioms Nock.RedTeam.Batch24A1.sample_bindMemoryRow
#print axioms Nock.RedTeam.Batch24A1.sample_activeFingerprintChecks
#print axioms Nock.RedTeam.Batch24A1.b24a1_sample_scan_ne_nil
#print axioms Nock.RedTeam.Batch24A1.b24a1_jointly_nonvacuous
#print axioms Nock.RedTeam.Batch24A1.b24a1_sample_scan_realized
#print axioms Nock.RedTeam.Batch24A1.b24a1_strictStrategy_nonvacuous
#print axioms Nock.RedTeam.Batch24A1.b24a1_sampleStrategy_realized
#print axioms Nock.RedTeam.Batch24A1.b24a1_strict_commitment_is_constant
#print axioms Nock.RedTeam.Batch24A1.b24a1_loose_schedule_admits_post_seed_choice
#print axioms Nock.RedTeam.Batch24A1.b24a1_no_strict_strategy_chooses_post_seed
#print axioms Nock.RedTeam.Batch24A1.b24a1_badFP_fails_active_scan
#print axioms Nock.RedTeam.Batch24A1.b24a1_badRow_accepted_but_unrealized
