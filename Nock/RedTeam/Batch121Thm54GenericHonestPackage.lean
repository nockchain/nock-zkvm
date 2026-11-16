import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.ConcreteStrictPackage
import Nock.RedTeam.Batch107Thm54StateTagChar
import Nock.RedTeam.Batch120Thm54GenericHonestPackage
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Paper frame:

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  `Inputs.stateTagChar` is the same `Prop` as
`NodeEncoding.StateTagChar` = `InjOn natCast (Iic 11)`.  Bound 11 is the paper
`cons` tag, not an NMR-axis claim.  Additive `inputsOfPaperChar` / `packageOfPaperChar`
read the field from `hgt` and do not change `packageOf`'s signature.
Residual `q_eq_ringChar` is the execution pin `E.q = ringChar K` and stays
named; F97 `q` is not bumped to Goldilocks.  IO coins/flags and compiler
folds stay named.  Walk overlays are unchanged.  Fibre `Accepts` stays
`∀ a g`.  Accounting remains `11+1+2`.  The overlay is not rounded into a universal
constructor or a consumed-capstone restatement.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch121

open scoped Classical Polynomial
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.NodeEncoding
open Nock.AxisBridge
open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## A. Same Prop: `Inputs.stateTagChar` = `StateTagChar` = `InjOn Iic 11` -/

/-- Encoding extra is still `InjOn natCast (Iic 11)`.  Not weakened. -/
theorem stateTagChar_def_unchanged :
    NodeEncoding.StateTagChar K =
      Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11) :=
  rfl

/-- Chip field has that same type -/
theorem inputs_stateTagChar_is_encoding_extra
    {E : BuildableNockExecution F K} (I : Inputs E) :
    NodeEncoding.StateTagChar K :=
  I.stateTagChar

/-- Independently, `11 < ringChar` inhabits `InjOn Iic 11`.  This proof
does not cite the production wrapper -/
theorem independent_forward (h : 11 < ringChar K) :
    Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11) := by
  haveI := ringChar.charP K
  intro m hm n hn hmn
  apply CharP.natCast_injOn_Iio K (ringChar K)
  · exact lt_of_le_of_lt hm h
  · exact lt_of_le_of_lt hn h
  · exact hmn

theorem independent_hgt_inhabits_stateTagChar (hgt : 11 < ringChar K) :
    NodeEncoding.StateTagChar K :=
  independent_forward hgt

/-- Positive-char converse, independent of the production wrapper. -/
theorem independent_converse
    (hchar : Set.InjOn (fun n : ℕ => (n : K)) (Set.Iic 11))
    (hpos : 0 < ringChar K) : 11 < ringChar K := by
  haveI := ringChar.charP K
  by_contra hnot
  have hle : ringChar K ≤ 11 := Nat.not_lt.mp hnot
  have hcast : ((ringChar K : ℕ) : K) = ((0 : ℕ) : K) := by
    simp [CharP.cast_eq_zero]
  have heq : ringChar K = 0 :=
    hchar (show ringChar K ∈ Set.Iic 11 from hle)
      (by simp : (0 : ℕ) ∈ Set.Iic 11) hcast
  exact (Nat.ne_of_gt hpos) heq

theorem independent_iff (hpos : 0 < ringChar K) :
    NodeEncoding.StateTagChar K ↔ 11 < ringChar K :=
  ⟨fun hchar => independent_converse hchar hpos,
    independent_hgt_inhabits_stateTagChar⟩

/-- Assembled `hgt` is positive characteristic, so the iff applies. -/
theorem assembled_char_pos (hgt : 11 < ringChar K) : 0 < ringChar K :=
  Nat.zero_lt_of_lt hgt

theorem stateTagChar_iff_assembled (hgt : 11 < ringChar K) :
    NodeEncoding.StateTagChar K ↔ 11 < ringChar K :=
  independent_iff (assembled_char_pos hgt)

/-- Char-0 still blocks an unguarded iff -/
theorem iff_requires_positive_char {L : Type*} [Field L] [CharZero L] :
    NodeEncoding.StateTagChar L ∧ ¬ 11 < ringChar L :=
  Batch107.iff_requires_positive_char

/-- Paper `cons` tag is opcode 11.  Bound 11 is that tag, not NMR axis. -/
theorem computeStateTag_cons :
    NodeEncoding.computeStateTag .cons = 11 :=
  rfl

theorem paper_opcode_set_is_cons_at_eleven :
    Batch107.paperOpcodeFinset = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11} ∧
      Batch107.paperOpcodeFinset.card = 11 ∧
      NodeEncoding.computeStateTag .cons ∈ Batch107.paperOpcodeFinset :=
  ⟨rfl, Batch107.paperOpcodeFinset_card, by decide⟩

theorem stateTagChar_fails_at_char_eleven :
    letI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
    ¬ NodeEncoding.StateTagChar (ZMod 11) :=
  Batch107.stateTagChar_fails_at_char_eleven

/-! ## B. Additive overlay reads the field from `hgt`; `packageOf` unchanged -/

/-- Overlay definition: only `stateTagChar` is rewritten from `hgt`. -/
theorem overlay_is_with_stateTagChar {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) :
    inputsOfPaperChar I hgt =
      { I with stateTagChar :=
          NodeEncoding.stateTagChar_of_ringChar_gt_eleven hgt } :=
  rfl

/-- Chip field of the overlay is the paper bound, not a free extra. -/
theorem overlay_reads_hgt {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) :
    (inputsOfPaperChar I hgt).stateTagChar =
      NodeEncoding.stateTagChar_of_ringChar_gt_eleven hgt :=
  rfl

theorem overlay_eq_of_char {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) :
    (inputsOfPaperChar I hgt).stateTagChar = inputs_stateTagChar_of_char hgt :=
  Subsingleton.elim _ _

/-- `StateTagChar` is a `Prop`, so the overlaid proof equals the caller's.
Not a different object; not a claim that the overlay is a no-op. -/
theorem overlay_eq_caller_by_proof_irrelevance
    {E : BuildableNockExecution F K} (I : Inputs E)
    (hgt : 11 < ringChar K) :
    (inputsOfPaperChar I hgt).stateTagChar = I.stateTagChar :=
  Subsingleton.elim _ _

/-- Independent inhabit of the chip field from `hgt` -/
theorem overlay_inhabits_from_independent_forward
    {E : BuildableNockExecution F K} (_I : Inputs E)
    (hgt : 11 < ringChar K) :
    NodeEncoding.StateTagChar K :=
  independent_hgt_inhabits_stateTagChar hgt

/-- Fifteen-field eta is unchanged: the field remains on the record. -/
theorem inputs_is_fifteen_fields {E : BuildableNockExecution F K}
    (I : Inputs E) :
    I =
      { stateTagChar := I.stateTagChar
        computeWalkAlpha := I.computeWalkAlpha
        memoryWalkAlpha := I.memoryWalkAlpha
        walkGamma := I.walkGamma
        hOrb := I.hOrb
        basis := I.basis
        orbit := I.orbit
        activeDomains := I.activeDomains
        ioCoins := I.ioCoins
        ioPoleHitGood := I.ioPoleHitGood
        ioGammaGood := I.ioGammaGood
        ioLogDerivGood := I.ioLogDerivGood
        computeChallenges := I.computeChallenges
        memoryScalarChallenge := I.memoryScalarChallenge
        memoryExtensionFold := I.memoryExtensionFold
        interPoleHitGood := I.interPoleHitGood
        honestVer := I.honestVer
        ioGood10 := I.ioGood10
        interPoleHitGood10 := I.interPoleHitGood10 } :=
  Batch120.inputs_is_fifteen_fields I

/-- `packageOf` still consumes `Data`, `11 < ringChar`, and named `Inputs`. -/
theorem packageOf_signature_unchanged
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    packageOf D hgt I hprl hmore hord hordM hrows hgenF hF =
      buildFullPackageWith E I (commitmentResidualOfArrays_of_char D hgt)
        (computeChallenge_pins E I) hprl hmore hord hordM hrows hgenF hF :=
  rfl

/-- Additive package is `packageOf` at the overlaid Inputs. -/
theorem packageOfPaperChar_eq {E : BuildableNockExecution F K} (D : Data E)
    (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    packageOfPaperChar D hgt I hprl hmore hord hordM hrows hgenF hF =
      packageOf D hgt (inputsOfPaperChar I hgt) hprl hmore hord hordM hrows hgenF hF :=
  rfl

theorem packageOf_still_takes_named_inputs_after_paper_char
    {E : BuildableNockExecution F K} (D : Data E)
    (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    packageOf D hgt I hprl hmore hord hordM hrows hgenF hF =
      buildFullPackageWith E I (commitmentResidualOfArrays_of_char D hgt)
        (computeChallenge_pins E I) hprl hmore hord hordM hrows hgenF hF ∧
      packageOfPaperChar D hgt I hprl hmore hord hordM hrows hgenF hF =
        packageOf D hgt (inputsOfPaperChar I hgt) hprl hmore hord hordM hrows hgenF hF :=
  ⟨rfl, rfl⟩

/-! ## C. Residual `q_eq_ringChar` stays named; F97 `q` not bumped -/

/-- Residual extra is the execution pin `E.q = ringChar K`, not opcode-tag
injectivity -/
theorem residual_q_eq_ringChar_is_execution_pin
    {E : BuildableNockExecution F K} (D : Data E) :
    E.q = ringChar K :=
  D.q_eq_ringChar

/-- `11 < n` does not force `q = n`.  The opcode-tag bound is not the
execution pin -/
theorem eleven_lt_does_not_give_q_eq :
    ¬ ∀ (q n : ℕ), 11 < n → q = n := by
  intro h
  have : (17 : ℕ) = 13 := h 17 13 (by omega)
  omega

/-- `Data` still names the execution pin.  Overlay does not touch `Data`. -/
theorem data_still_names_q_eq_ringChar {E : BuildableNockExecution F K}
    (D : Data E) :
    D =
      { computeNodes := D.computeNodes
        memoryNodes := D.memoryNodes
        compute_rows := D.compute_rows
        memory_rows := D.memory_rows
        computeOK := D.computeOK
        memoryOK := D.memoryOK
        root_line_exponent := D.root_line_exponent
        root_line_origin := D.root_line_origin
        nounSizeBound := D.nounSizeBound
        Λ := D.Λ
        slotSemantics := D.slotSemantics
        recordEquations := D.recordEquations
        census := D.census
        sizeWindowBound := D.sizeWindowBound
        q_eq_ringChar := D.q_eq_ringChar
        skeletonBounded := D.skeletonBounded
        combinedBounded := D.combinedBounded } :=
  Batch120.data_has_no_inputs_coins D

theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } :=
  Batch120.residualPremises_eta_still_four P

/-- Paper Goldilocks prime is `> 11`.  Fixture `q` is not that prime. -/
theorem independent_goldilocks_p_gt_eleven :
    11 < 2 ^ 64 - 2 ^ 32 + 1 := by
  norm_num

theorem goldilocks_p_ne_f97_q : 2 ^ 64 - 2 ^ 32 + 1 ≠ 97 := by
  norm_num

theorem goldilocks_p_ne_f73_q : 2 ^ 64 - 2 ^ 32 + 1 ≠ 73 := by
  norm_num

/-! ## D. IO / compiler folds not invented; walk overlays unchanged -/

theorem overlay_preserves_io {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) :
    (inputsOfPaperChar I hgt).ioCoins = I.ioCoins ∧
      (inputsOfPaperChar I hgt).ioPoleHitGood = I.ioPoleHitGood ∧
      (inputsOfPaperChar I hgt).ioGammaGood = I.ioGammaGood ∧
      (inputsOfPaperChar I hgt).ioLogDerivGood = I.ioLogDerivGood :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem overlay_preserves_cubic {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) :
    (inputsOfPaperChar I hgt).computeChallenges =
        I.computeChallenges :=
  rfl

theorem overlay_preserves_walk {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) :
    (inputsOfPaperChar I hgt).computeWalkAlpha = I.computeWalkAlpha ∧
      (inputsOfPaperChar I hgt).memoryWalkAlpha = I.memoryWalkAlpha ∧
      (inputsOfPaperChar I hgt).walkGamma = I.walkGamma :=
  ⟨rfl, rfl, rfl⟩

theorem overlay_commutes_walk_sample {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) (a g : K) :
    inputsOfPaperChar (inputsOfWalkSample I a g) hgt =
      inputsOfWalkSample (inputsOfPaperChar I hgt) a g :=
  rfl

theorem overlay_commutes_fibre_alphaM {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) :
    inputsOfPaperChar (inputsOfFibreAlphaM I) hgt =
      inputsOfFibreAlphaM (inputsOfPaperChar I hgt) :=
  rfl

theorem overlay_commutes_composed {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) (a g : K) :
    inputsOfPaperChar (inputsOfWalkSampleWithAlphaM I a g) hgt =
      inputsOfWalkSampleWithAlphaM (inputsOfPaperChar I hgt) a g :=
  rfl

theorem overlay_commutes_fold2 {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) :
    inputsOfPaperChar (inputsFold2 I) hgt =
      inputsFold2 (inputsOfPaperChar I hgt) :=
  rfl

theorem ao96_overlay_still_only_walk_pair {E : BuildableNockExecution F K}
    (I : Inputs E) (a g : K) :
    (inputsOfWalkSample I a g).computeWalkAlpha = a ∧
      (inputsOfWalkSample I a g).walkGamma = g ∧
      (inputsOfWalkSample I a g).memoryWalkAlpha = I.memoryWalkAlpha ∧
      (inputsOfWalkSample I a g).stateTagChar = I.stateTagChar ∧
      (inputsOfWalkSample I a g).ioCoins = I.ioCoins :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem sampled_of_paper_char_reads_named_io
    {E : BuildableNockExecution F K} (I : Inputs E)
    (hgt : 11 < ringChar K) :
    (sampledAssignment E (inputsOfPaperChar I hgt)).sampled.coins = I.ioCoins :=
  rfl

/-- Remaining named `Inputs` after the char overlay: FiniteIO coins/flags,
compiler folds `9`/`11`/`36`, memory scalar/extension, interpolation. -/
theorem remaining_named_after_paper_char {E : BuildableNockExecution F K}
    (I : Inputs E) (hgt : 11 < ringChar K) :
    (inputsOfPaperChar I hgt).ioCoins = I.ioCoins ∧
      (inputsOfPaperChar I hgt).computeChallenges = I.computeChallenges ∧
      (inputsOfPaperChar I hgt).memoryScalarChallenge =
        I.memoryScalarChallenge ∧
      (inputsOfPaperChar I hgt).memoryExtensionFold = I.memoryExtensionFold ∧
      (inputsOfPaperChar I hgt).hOrb = I.hOrb ∧
      (inputsOfPaperChar I hgt).basis = I.basis ∧
      (inputsOfPaperChar I hgt).orbit = I.orbit ∧
      (inputsOfPaperChar I hgt).activeDomains = I.activeDomains :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem computeChallenges_are_folds_9_11_36
    (c : FinalComputeChallengeTuple K) :
    c = ⟨c.eqA, c.eqB, c.eqC⟩ := by
  cases c
  rfl

/-! ## E. Fibre `Accepts` stays `∀ a g`; not `∀ ω` -/

theorem packageOfPaperChar_fibre_accepts_still_forall_ag
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K,
      (packageOfPaperChar D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  GenericHonestPackage.packageOfPaperChar_fibre_accepts D hgt I hprl hmore hord hordM hrows hgenF hF horder

theorem packageOf_fibre_accepts_still_forall_ag
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (horder : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z)
      E.cfg.challenges.α) :
    ∀ a g : K,
      (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts (honestCoin E a g) E.cfg.challenges.lam :=
  GenericHonestPackage.packageOf_fibre_accepts_still_forall_ag D hgt I hprl hmore hord hordM hrows hgenF hF
    horder

theorem packageOfPaperChar_not_forall_omega
    {E : BuildableNockExecution F K} (D : Data E) (hgt : 11 < ringChar K)
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (lmb : K) :
    ¬ ∀ ω : JointCoins K, (packageOfPaperChar D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOfPaperChar_not_forall_omega D hgt I hprl hmore hord hordM hrows hgenF hF (lmb := lmb)

/-! ## F. Wrong layer: NMR / capstone not re-litigated; extras stay named -/

/-- NMR address space remains the Nat-cast memory-table axis.
Bound 11 is the `cons` opcode tag, not this axis -/
theorem nmr_axis_is_not_opcode_tag
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    NodeEncoding.computeStateTag .cons = 11 ∧
      ∀ i : Fin E.cfg.memRows,
        memoryMemRecKind (E.exec.memoryRowAt i).1 = .active →
          ∃ n : ℕ, (E.execA.memoryRowAt i).2.2.mem.axis = (n : K) :=
  ⟨computeStateTag_cons, M.axisNat⟩

theorem censusRecordPremises_eta_still_five
    {E : BuildableNockExecution F K} {P : ResidualPremises E}
    {M : MemoryRecordPremises E} (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  Batch120.censusRecordPremises_eta_still_five C

theorem memoryRecordPremises_eta_still_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat,
        timestampClosed := M.timestampClosed,
        honestVer := M.honestVer } :=
  Batch120.memoryRecordPremises_eta_still_two M

theorem dataOfCensusAtConsumed_still_names_remaining_extras
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
    (hgt : 11 < ringChar K)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    let D := dataOfCensusAtConsumed E P M slotSemantics census
      sizeWindowBound skeletonBounded hgt hln
    D.slotSemantics = slotSemantics ∧
      D.census = census ∧
      D.sizeWindowBound = sizeWindowBound ∧
      D.skeletonBounded = skeletonBounded ∧
      D.q_eq_ringChar = P.q_eq_ringChar :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem released_builder_still_takes_hzero
    {E : BuildableNockExecution F K}
    (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = default)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    Nonempty (OptimizedFullStrictNockVMROMPackage F K I.hOrb) :=
  Batch120.released_builder_still_takes_hzero I hprl hmore hord hordM hrows hhon R hzero hgenF hF

inductive ReviewedField121
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | exact_resources
  | row_budgets
  | shared_forest_axis
deriving DecidableEq

def substantiveFields121 : List ReviewedField121 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields121 : List ReviewedField121 := [.structural]

def residualFields121 : List ReviewedField121 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]

/-- The char overlay is not a statement-field class move. -/
theorem independent_exact_eleven_one_two_accounting :
    substantiveFields121.length = 11 ∧
      typeSummaryFields121.length = 1 ∧
      residualFields121 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields121.length = 2 ∧
      (substantiveFields121 ++ typeSummaryFields121 ++ residualFields121).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

variable [Fintype F] [DecidableEq F]

/-- Liveness receipt, not a content pin: the released capstone still elaborates at these
instances and the paper alias still resolves to it.  It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

/-! ## G. F73: overlay inhabits from `11 < ringChar`; IO stays named -/

namespace Concrete

open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete
open GenericHonestArrays.Concrete
open BuildableChips.Concrete
open GenericHonestPackage.Concrete

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem f73_char_gt_eleven : 11 < ringChar K73cubic :=
  GenericHonestArrays.Concrete.f73_char_gt_eleven

/-- F73 chip `stateTagChar` is the paper bound -/
theorem f73_overlay_inhabits_from_hgt :
    inputs73PaperChar.stateTagChar =
      GenericHonestArrays.stateTagChar_of_paper_char f73_char_gt_eleven :=
  Subsingleton.elim _ _

theorem f73_overlay_preserves_io :
    inputs73PaperChar.ioCoins = inputs73Fold2.ioCoins ∧
      inputs73PaperChar.computeChallenges = inputs73Fold2.computeChallenges ∧
      inputs73PaperChar.computeWalkAlpha = inputs73Fold2.computeWalkAlpha ∧
      inputs73PaperChar.memoryWalkAlpha = inputs73Fold2.memoryWalkAlpha :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- F73 execution pin stays `q = 73 = ringChar`, not Goldilocks. -/
theorem f73_q_eq_ringChar_stays_named :
    concreteExecution.q = 73 ∧
      concreteExecution.q = ringChar K73cubic ∧
      2 ^ 64 - 2 ^ 32 + 1 ≠ 73 :=
  ⟨rfl, data73.q_eq_ringChar, goldilocks_p_ne_f73_q⟩

-- Form R leftover LaterSeedZeros residual.
variable (hmore73 : BuildableAxisWitness.LaterSeedZeros concreteExecution)
include hmore73

theorem f73_packageOf_signature_unchanged :
    package73Of hmore73 = packageOf data73 f73_char_gt_eleven inputs73Fold2
      BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
      hmore73
      BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order
    BuildablePackage.Concrete.concreteExecution_rowsBound
    data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField ∧
      package73OfPaperChar hmore73 =
        packageOf data73 f73_char_gt_eleven inputs73PaperChar
          BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
          hmore73
          BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order
    BuildablePackage.Concrete.concreteExecution_rowsBound
    data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField :=
  ⟨rfl, rfl⟩

theorem f73_not_forall_omega (lmb : K73cubic) :
    ¬ ∀ ω : JointCoins K73cubic, (package73OfPaperChar hmore73).strategy.Accepts ω lmb :=
  GenericHonestPackage.packageOfPaperChar_not_forall_omega data73
    f73_char_gt_eleven inputs73Fold2
    BuildablePackage.Concrete.concreteExecution_pairedRecordLayout
    hmore73
    BuildablePackage.Concrete.concreteExecution_walk_order
    BuildablePackage.Concrete.concreteExecution_memory_walk_order
    BuildablePackage.Concrete.concreteExecution_rowsBound
    data73_generated OptimizedStrictFullPackage.Concrete.f73_primeField (lmb := lmb)

end Concrete

#print axioms stateTagChar_def_unchanged
#print axioms inputs_stateTagChar_is_encoding_extra
#print axioms independent_forward
#print axioms independent_hgt_inhabits_stateTagChar
#print axioms independent_converse
#print axioms independent_iff
#print axioms assembled_char_pos
#print axioms stateTagChar_iff_assembled
#print axioms iff_requires_positive_char
#print axioms computeStateTag_cons
#print axioms paper_opcode_set_is_cons_at_eleven
#print axioms stateTagChar_fails_at_char_eleven
#print axioms overlay_is_with_stateTagChar
#print axioms overlay_reads_hgt
#print axioms overlay_eq_of_char
#print axioms overlay_eq_caller_by_proof_irrelevance
#print axioms overlay_inhabits_from_independent_forward
#print axioms inputs_is_fifteen_fields
#print axioms packageOf_signature_unchanged
#print axioms packageOfPaperChar_eq
#print axioms packageOf_still_takes_named_inputs_after_paper_char
#print axioms residual_q_eq_ringChar_is_execution_pin
#print axioms eleven_lt_does_not_give_q_eq
#print axioms data_still_names_q_eq_ringChar
#print axioms residualPremises_eta_still_four
#print axioms independent_goldilocks_p_gt_eleven
#print axioms goldilocks_p_ne_f97_q
#print axioms goldilocks_p_ne_f73_q
#print axioms overlay_preserves_io
#print axioms overlay_preserves_cubic
#print axioms overlay_preserves_walk
#print axioms overlay_commutes_walk_sample
#print axioms overlay_commutes_fibre_alphaM
#print axioms overlay_commutes_composed
#print axioms overlay_commutes_fold2
#print axioms ao96_overlay_still_only_walk_pair
#print axioms sampled_of_paper_char_reads_named_io
#print axioms remaining_named_after_paper_char
#print axioms computeChallenges_are_folds_9_11_36
#print axioms packageOfPaperChar_fibre_accepts_still_forall_ag
#print axioms packageOf_fibre_accepts_still_forall_ag
#print axioms packageOfPaperChar_not_forall_omega
#print axioms nmr_axis_is_not_opcode_tag
#print axioms censusRecordPremises_eta_still_five
#print axioms memoryRecordPremises_eta_still_two
#print axioms dataOfCensusAtConsumed_still_names_remaining_extras
#print axioms released_builder_still_takes_hzero
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Concrete.f73_char_gt_eleven
#print axioms Concrete.f73_overlay_inhabits_from_hgt
#print axioms Concrete.f73_overlay_preserves_io
#print axioms Concrete.f73_q_eq_ringChar_stays_named
#print axioms Concrete.f73_packageOf_signature_unchanged
#print axioms Concrete.f73_not_forall_omega

end
end Nock.RedTeam.Batch121
