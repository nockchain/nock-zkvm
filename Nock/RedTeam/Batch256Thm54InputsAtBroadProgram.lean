/-
  Nock/RedTeam/Batch256Thm54InputsAtBroadProgram.lean

  **The Theorem-5.4 statement at the SECOND generator program — eight of the eleven compute
  states — with `claimedResult = result`.**

  Its own "Not claimed" list opens with that being *the dominant weakness in
  the evidence base*, and says of the broad program that `inputsOfCarrier` is `∀ E` so nothing
  blocks it but no term exists.  This module is that term.

  The remaining links are `Inputs`, `buildFullPackage`, the statement
  and the committed claim, and all four are here, over exactly `Batch232.bp_buildable` and
  `Batch232.bp_data` — no new carrier, no new `Data`.

  **The three arithmetic side conditions, recomputed for THIS program.**  `GY` §4 spent
  `2 ^ 8 ≤ 2 ^ 8`, both record columns `≤ 255`, and
  `ioFailureUnionBound 8 255 255 769³ < (769³)²`.  Two of the three numbers are different here and
  one is not:

  | condition | Tier A | broad program |
  |---|---|---|
  | table orbit height | `2 ^ 8 ≤ 2 ^ 8` | `2 ^ 8 ≤ 2 ^ 8` — same orbit |
  | request column | `13` records | `≤ 51` (`Batch231.bp_accAt_le`) |
  | response column | `≤ 184` rows | `≤ 227` rows (`bp_memRowsLen`) |
  | union bound | `ioFailureUnionBound 8 255 255 769³ < (769³)²` | same ceiling, both columns still fit |

  The response column is the one that moved, and it moved by `43` — well inside the `255` ceiling
  the carrier's own `memoryIOCapacity` field forces at `orbit.h = 8`.  So **no bound failed and no
  larger `hOrb` or `Ksz` was needed**: `2 ^ 8 = 256` still dominates `227 + 1`, and `Ksz = 64`
  still sits between `max (accAt) (2·kMem) = 51` and `ringChar K = 769`.  Reported as a
  measurement of this program, not as a bound on arbitrary programs.

  **`hz : computeChallenges = ⟨0,0⟩` is the verifier's compiler FOLD tuple**
  (`challenge9`/`challenge11`/`challenge36`, `OptimizedComputeCollisionBound.lean:515`), **not**
  the RLC coin vector.

  **Scope.**  One program, one configuration — `GaloisField 769 3`, seed `φ(8)`, `α = φ(4)`, coins
  `(0, 0, 1)`, `Ksz = 64`, `Λ = 22`, table orbit `h = 8`, strict package orbit
  `StrictOrbitDomain F 3 8` of order `768`.  The capstone type
  `optimizedFullStrictNockVMROM_of_package` and the `11+1+2` accounting are untouched; `Gen.lean`
  is unedited; no §J box moves.
-/
import Mathlib.Tactic.IntervalCases
import Nock.RedTeam.Batch246Thm54InputsAtGeneratedCarrier
import Nock.NockVMROM.Thm54.TraceGen.GenCarrierInputs
import Nock.NockVMROM.Thm54.TraceGen.GenClaimedResult
import Nock.NockVMROM.Thm54.TraceGen.GenStatement
import Nock.NockVMROM.Thm54.TraceGen.GenTierAInputsPrep
import Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLayout
import Nock.NockVMROM.Thm54.BuildableAxisWitness
import Nock.RedTeam.Batch232Thm54BroadProgramData
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

namespace Nock.RedTeam.Batch256

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK

noncomputable section




/-! ## 1. The `Inputs` wall does not bind this carrier either

`GenStatement.no_basis_fin3_field_self` empties `Inputs E` whenever `F = K`.  This carrier is the
same cubic tower Tier A's is — `F = ZMod 769`, `K = GaloisField 769 3` — so the basis exists. -/

theorem b256_finrank : Module.finrank DF DK = 3 := DotConfig769.finrank_cubic

theorem b256_basis_exists : Nonempty (Module.Basis (Fin 3) DF DK) :=
  ⟨DotConfig769.basis⟩

/-! ## 2. `Data` at the broad carrier, retyped at `bp_buildable`

`Batch232.bp_data` is `genData` at the broad program and `Batch232.bp_buildable` is
`genBuildableOfProgram` at the same arguments, so the two agree by definition.  Stating it with the
ascription is the check: if the carrier the `Data` commits were a different execution, this would
not elaborate. -/

/-- **`HonestCommitment.Data` over exactly `Batch232.bp_buildable`.** -/
def bpData : Data Batch232.bp_buildable := Batch232.bp_data

/-! ## 3. The three arithmetic side conditions, at THIS program's numbers -/

/-- The broad carrier's table orbit is the same `2 ^ 8` one Tier A uses. -/
theorem b256_orbit_h : Batch232.bp_buildable.cfg.orbit.h = 8 := rfl

/-- The strict package orbit (`StrictOrbitDomain F 3 8`, base-field order `3 · 256 = 768`) is at
least as tall as the table orbit. -/
theorem b256_hOrbCap : 2 ^ Batch232.bp_buildable.cfg.orbit.h ≤ 2 ^ 8 := by
  rw [b256_orbit_h]

/-- The request column fits the `255` ceiling, from the carrier's own `programIOCapacity`.  The
program's actual column is `accAt (airReorder bpTree) 17 ≤ 51` (`Batch231.bp_accAt_le`). -/
theorem b256_hreq : Batch232.bp_buildable.exec.derivedRequestIO.length ≤ 255 := by
  have h := Batch232.bp_buildable.programIOCapacity
  rw [b256_orbit_h] at h
  norm_num at h
  omega

/-- The response column likewise, from `memoryIOCapacity`.  Here it is the number that moved:
`227` memory rows against Tier A's `184`, and `227 + 1 ≤ 256` still holds. -/
theorem b256_hresp : Batch232.bp_buildable.exec.derivedResponseIO.length ≤ 255 := by
  have h := Batch232.bp_buildable.memoryIOCapacity
  rw [b256_orbit_h] at h
  norm_num at h
  omega

/-- The counted IO failure mass at the capacity ceiling, against `|K|² = 769⁶`:
`828 439 209 747 480 < 206 803 573 429 178 881`.  (`GY` §4's prose gives `1821720 < 454756609`
for the same condition at Tier A; that is the union bound with the `Fintype.card K` factor dropped
on the left and `|K|` rather than `|K|²` on the right.  The Lean condition is unchanged and both
programs satisfy it; only the recorded decimal was wrong.) -/
theorem b256_hcard :
    RecordCarrier.honestIOBound 255 255 (Fintype.card DK) < Fintype.card (DK × DK) := by
  rw [RecordCarrier.honestIOBound_eq, Fintype.card_prod, DotConfig769.card_K]
  norm_num

/-! ## 4. `Inputs` at the broad generated carrier -/

/-- **`BuildableChips.Inputs` inhabited over `Batch232.bp_buildable`.**  Second program, and the
first at which `inputsOfCarrier` has been consumed anywhere but Tier A. -/
theorem b256_interCard :
    2 * ((executionInterRecords Batch232.bp_buildable).requests.length +
      (executionInterRecords Batch232.bp_buildable).responses.length) + 1 <
        Fintype.card DK :=
  executionInterRecords_card_lt_of_memRows Batch232.bp_buildable (by
    have hmem : Batch232.bp_buildable.cfg.memRows = 227 :=
      bp_memRowsLen _ _ _
    have hq : Fintype.card DK = 769 ^ 3 := DotConfig769.card_K
    rw [hmem, hq]
    norm_num)

theorem bp_honestVer :
    ∀ row ∈ Batch232.bp_buildable.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  unfold Batch232.bp_buildable
  exact genBuildableOfProgram_honestVer (F := DF) (q := 769) (Λ := 22)
    DotConfig769.seedZ DotConfig769.alphaA
    DotConfig769.seedZ_ne_zero DotConfig769.two_ne_zero 0 0 1
    Batch231.bpChal Batch231.bp_hinp Batch231.bp_hmi
    64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit])
    (genComputeSkeleton_bp 0)
    Batch231.bp_seedGood_at769
    (bp_computeCoins _ _)
    (by norm_num) Batch231.bp_air_traceConfined
    Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch231.bp_accAt_le; omega)
    (by have := Batch231.bp_accAt_le; omega)
    Batch232.bp_hKsz2
    Batch231.bp_hb (by norm_num) DotConfig769.ringChar_K.symm Batch231.bp_haxis
    (not_mem_badSeeds_of_pairs _ _
      (bp_pairs_sep DotConfig769.seedZ Batch231.bp_ringChar_gt_two
        (Batch231.bp_sepSeed_one_two _) _))
    Batch231.bp_hout
    Batch232.bp_hKszChar Batch232.bp_hprogCap Batch232.bp_hmemCap Batch231.bp_hlt


def bpInputs : Inputs Batch232.bp_buildable :=
  inputsOfCarrier Batch232.bp_buildable DotConfig769.stateTagChar DotConfig769.basis
    DotConfig769.strictOrbit b256_hOrbCap 255 b256_hreq b256_hresp
    b256_hcard
    2 2 5 (fun j => (j : DF) + 1) 0
    (interCard_of_unionBound Batch232.bp_buildable
      (by
        have : Batch232.bp_buildable.cfg.memRows = 227 :=
          bp_memRowsLen _ _ _
        omega) b256_hcard)
    bp_honestVer

theorem b256_challenges : bpInputs.computeChallenges = default := rfl

theorem b256_hOrb : bpInputs.hOrb = 8 := rfl

theorem b256_walkOrder :
    2 ≤ Batch232.bp_buildable.cfg.compRows →
      Batch232.bp_buildable.cfg.compRows ≤ orderOf bpInputs.computeWalkAlpha := fun _ => by
  have hα : bpInputs.computeWalkAlpha = (2 : DK) := rfl
  have hrows : Batch232.bp_buildable.cfg.compRows = 17 :=
    Batch231.bp_genComputeRows_len _ _
  rw [hα, hrows]
  have hcast : (2 : DK) = (algebraMap DF DK).toMonoidHom (2 : DF) :=
    (map_natCast (algebraMap DF DK) 2).symm
  rw [hcast, orderOf_injective (algebraMap DF DK).toMonoidHom
    (RingHom.injective (algebraMap DF DK)) (2 : DF)]
  exact Batch246.goldilocks769_two_base_order_ge 17 (by norm_num)

theorem b256_memoryWalkOrder :
    2 ≤ Batch232.bp_buildable.cfg.memRows →
      Batch232.bp_buildable.cfg.memRows ≤ orderOf bpInputs.memoryWalkAlpha := fun _ => by
  have hα : bpInputs.memoryWalkAlpha = (2 : DK) := rfl
  have hrows : Batch232.bp_buildable.cfg.memRows = 227 :=
    bp_memRowsLen _ _ _
  rw [hα, hrows]
  have hcast : (2 : DK) = (algebraMap DF DK).toMonoidHom (2 : DF) :=
    (map_natCast (algebraMap DF DK) 2).symm
  rw [hcast, orderOf_injective (algebraMap DF DK).toMonoidHom
    (RingHom.injective (algebraMap DF DK)) (2 : DF)]
  have : orderOf (2 : DF) = 384 :=
    Nock.NockVMROM.Thm54.TraceGen.DotConfig769.goldilocks769_two_order
  omega

/-- The record sample the IO coins were chosen against is the carrier's own derived pair. -/
theorem b256_records :
    executionRecords Batch232.bp_buildable =
      ⟨Batch232.bp_buildable.exec.derivedRequestIO,
        Batch232.bp_buildable.exec.derivedResponseIO⟩ :=
  rfl

/-- Non-vacuity: the chosen coins really are outside the joint counted failure event. -/
theorem b256_ioCoins_good :
    (bpInputs.ioCoins.gamma, bpInputs.ioCoins.pole) ∉
      IOFailureEvent (executionRecords Batch232.bp_buildable) :=
  ioCoinsOfCarrier_good Batch232.bp_buildable 255 b256_hreq b256_hresp
    b256_hcard

/-! ## 5. The package and the released statement -/


theorem bp_prl : RowLayout.PairedRecordLayout Batch232.bp_buildable.exec := by
  unfold Batch232.bp_buildable
  exact genBuildableOfProgram_pairedRecordLayout (F := DF) (q := 769) (Λ := 22)
    DotConfig769.seedZ DotConfig769.alphaA
    DotConfig769.seedZ_ne_zero DotConfig769.two_ne_zero 0 0 1
    Batch231.bpChal Batch231.bp_hinp Batch231.bp_hmi
    64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit])
    (genComputeSkeleton_bp 0)
    Batch231.bp_seedGood_at769
    (bp_computeCoins _ _)
    (by norm_num) Batch231.bp_air_traceConfined
    Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch231.bp_accAt_le; omega)
    (by have := Batch231.bp_accAt_le; omega)
    Batch232.bp_hKsz2
    Batch231.bp_hb (by norm_num) DotConfig769.ringChar_K.symm Batch231.bp_haxis
    (not_mem_badSeeds_of_pairs _ _
      (bp_pairs_sep DotConfig769.seedZ Batch231.bp_ringChar_gt_two
        (Batch231.bp_sepSeed_one_two _) _))
    Batch231.bp_hout
    Batch232.bp_hKszChar Batch232.bp_hprogCap Batch232.bp_hmemCap Batch231.bp_hlt

theorem b256_hmore : BuildableAxisWitness.LaterSeedZeros Batch232.bp_buildable :=
  Batch232.bp_laterSeedZeros

/-- The package's `rowsBound` at the broad program (`17·3 < 769`, `≤ 256 < 769`). -/
theorem b256_hrows :
    3 * Batch232.bp_buildable.cfg.compRows < ringChar DK ∧
      Batch232.bp_buildable.cfg.memRows < ringChar DK := by
  have h1 : Batch232.bp_buildable.cfg.compRows ≤ 2 ^ DotConfig769.executionOrbit.h :=
    Batch231.bp_hcomp
  have h2 : Batch232.bp_buildable.cfg.memRows ≤ 2 ^ DotConfig769.executionOrbit.h :=
    Batch231.bp_hmem
  norm_num [DotConfig769.executionOrbit] at h1 h2
  rw [DotConfig769.ringChar_K]
  constructor <;> omega

theorem b256_generated :
    GeneratedField.ClaimGenerated DK (commitmentResidualOfZero bpData).verifier.raw.claim
      (commitmentResidualOfZero bpData).Λ := by
  have hc : (commitmentResidualOfZero bpData).verifier.raw.claim =
      ⟨bpSubject, bpFormula, bpResult⟩ :=
    publicClaim_genComputeNodes _ _ _ _ _ _ (genComputeSkeleton_bp (K := DK) 0)
  refine GeneratedField.claimGenerated_of_eq (congrArg P8PublicClaim.subject hc)
    (congrArg P8PublicClaim.formula hc) ?_
  exact ⟨6, _, _, 6, bpResult, genComputeSkeleton_bp (K := DK) 0,
    by rw [DotConfig769.ringChar_K]; exact bp_evalGBy (by norm_num),
    (leafBound_of_traceConfined Batch231.bp_air_traceConfined).trans (le_of_eq rfl)⟩

/-- The constructed Theorem-5.4 package at the broad generated carrier. -/
def bpPackage : OptimizedFullStrictNockVMROMPackage DF DK bpInputs.hOrb :=
  buildFullPackage Batch232.bp_buildable bpInputs
    (commitmentResidualOfZero bpData) b256_challenges bp_prl
    (hmore := b256_hmore) (hord := b256_walkOrder) (hordM := b256_memoryWalkOrder) (hrows := b256_hrows)
    (hgenF := b256_generated) (hF := DotConfig769.dot_primeField)

/-- **The released fourteen-field Theorem-5.4 statement, at the eight-state generated program.** -/
theorem bpStatement
    (hax : FormRAxisBound bpPackage.optimized.sampled
      bpPackage.optimized.basis)
    (hbasis : FormRBasis bpPackage.optimized.basis)
    (hwidth : FormRWidth DF) :
    OptimizedFullStrictThm54Statement bpPackage :=
  Nock.NockVMROM.Thm54.TraceGen.statement_of_generated_residual
    bpData bpInputs b256_challenges bp_prl
    (hmore := b256_hmore) (hord := b256_walkOrder) (hordM := b256_memoryWalkOrder) (hrows := b256_hrows)
    (hgenF := b256_generated) (hF := DotConfig769.dot_primeField)
    hax hbasis hwidth

/-! ## 6. Read off the assembled package -/

theorem b256_package_q : bpPackage.q = 769 := rfl

theorem b256_package_ioStrategy :
    bpPackage.ioStrategy =
      finiteIOStrategy Batch232.bp_buildable bpInputs := rfl

theorem b256_package_honestSeed : bpPackage.honestSeed = DotConfig769.seedZ := rfl

/-! ## 7. -/

/-- The package's verifier claim is the committed skeleton's public claim. -/
theorem b256_verifier_claim :
    bpPackage.optimized.verifier.raw.claim =
      (commitmentResidualOfZero bpData).commitment.skeleton.publicClaim :=
  (commitmentResidualOfZero bpData).claim_eq.symm

/-- **The committed claim is the broad program's own triple.** -/
theorem b256_claim_triple :
    bpPackage.optimized.verifier.raw.claim =
      ⟨bpSubject, bpFormula, bpResult⟩ := by
  rw [b256_verifier_claim]
  exact publicClaim_genComputeNodes (K := DK) DotConfig769.seedZ DotConfig769.alphaA 0 0 1 _
    (genComputeSkeleton_bp 0)

/-- **`claimedResult = result`** at the broad program. -/
theorem b256_claimedResult :
    bpPackage.optimized.verifier.raw.claim.result = bpResult := by
  rw [b256_claim_triple]

/-- And `bpResult` is what the reference evaluator returns on the committed subject and formula. -/
theorem b256_claim_evalN :
    Nock.evalN 6 bpSubject bpFormula = some bpResult :=
  genComputeSkeleton_evalN (K := DK) (genComputeSkeleton_bp 0)

theorem b256_claim_Holds : (bpPackage.optimized.verifier.raw.claim).Holds := by
  rw [b256_verifier_claim]
  exact publicClaim_Holds (K := DK) DotConfig769.seedZ DotConfig769.alphaA 0 0 1 _
    (genComputeSkeleton_bp 0)

/-! ## 8. What the numbers actually are at this program

`GY` §4's receipts were read at Tier A's thirteen-record column and `184`-row memory table.  These
are the same measurements here, and they are the reason to believe the capacity certificates are
not vacuous: the compute domain carries `17` of `256` nodes and the memory domain `227` of `256`. -/

/-- The request column is **22** records — the seventeen rows' `recordCount` sum
(`cons·3 + s7 + s0·2 + s8 + s5 + s1·7 + s4 + s3` = `3 + 2 + 4 + 2 + 2 + 7 + 1 + 1`).  Tier A's is
`13`. -/
theorem b256_accAt_eq_22 :
    accAt (airReorder (bpTree (K := DK)))
        (bfsRows (airReorder (bpTree (K := DK)))).length = 22 := by
  rw [airReorder_bpTree, bp_air_rowsLen]
  simp only [accAt, bp_air_bfsRows, List.getElem?_cons_zero, List.getElem?_cons_succ]
  simp [Nock.Framework.recordCount, bpTreeAir, bp7TreeAir, bpR1TreeAir, bp7CTree,
    bpOp1Tree, bp8TreeAir, bpR2Tree, bp8CTree, bp5Tree, bpR3Tree, bp4Tree, bp3Tree,
    skelNode, genSkelCons, genSkelOp7, genSkelOp8, genSkelOp5, genSkelOp4, genSkelOp3,
    genSkelOp1, genSkelOp0]

/-- Read off the assembled carrier: its request IO column really has those `22` entries. -/
theorem b256_requestIO_length : Batch232.bp_buildable.exec.derivedRequestIO.length = 22 := by
  have h := genExactExecution_derivedRequestIO_length (F := DF) DotConfig769.seedZ
    DotConfig769.alphaA Batch231.bpChal 64 DotConfig769.executionOrbit
    (by norm_num [DotConfig769.executionOrbit]) 0 0 1 (bpTree (K := DK))
    (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
      (memInputs DotConfig769.seedZ) (bpTree (K := DK)))
    Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem
  rw [b256_accAt_eq_22] at h
  exact h

/-- The `Nodup` field is therefore a claim about a **22**-element list, not a one- or zero-element
one. -/
theorem b256_requestNodup : Batch232.bp_buildable.exec.derivedRequestIO.Nodup :=
  Batch232.bp_buildable.requestNodup

/-- The compute active domain carries `17` of the orbit's `256` nodes. -/
theorem b256_compRows : Batch232.bp_buildable.cfg.compRows = 17 :=
  Batch231.bp_genComputeRows_len _ _

/-- The memory table is `227` rows against Tier A's `184` — the number that moved. -/
theorem b256_memRows : Batch232.bp_buildable.cfg.memRows = 227 :=
  bp_memRowsLen _ _ _

/-- **The paper's `M + 2L` memory budget at this program**: `227`, and it is the
carrier's own `memRows` by `recordCountBalance`, not a separate obligation. -/
theorem b256_memoryBudget :
    RowLayout.memoryM Batch232.bp_buildable.exec
        + 2 * RowLayout.memoryL Batch232.bp_buildable.exec = 227 := by
  rw [← Batch232.bp_buildable.memoryRows_eq_M_add_two_mul_L]
  exact b256_memRows

/-- And the `Inputs` field that consumes it — the second active-domain certificate, at `227 ≤ 256`
rather than Tier A's `184 ≤ 256`. -/
theorem b256_memoryCapacity :
    RowLayout.memoryM Batch232.bp_buildable.exec
        + 2 * RowLayout.memoryL Batch232.bp_buildable.exec ≤ 2 ^ bpInputs.hOrb :=
  bpInputs.activeDomains.memoryCapacity

/-- **The one bound with little slack, and it is a field-level ceiling rather than an `hOrb`
choice.**  `227 + 1 ≤ 256` holds with `28` rows to spare.  `OrbitDomain` requires
`orderOf ω = 2 ^ h` (`OrbitDomain.lean:31`), and the 2-adic valuation of `|K*| = 769³ - 1` is that
of `768 = 2^8 · 3`, so no `ω` in this field has order `2 ^ 9`.  A program with `28` more memory
rows than this one therefore needs a different **field**, not a larger `hOrb`. -/
theorem b256_memory_headroom :
    Batch232.bp_buildable.cfg.memRows + 1 + 28 = 2 ^ 8 := by
  rw [b256_memRows]; norm_num

/-- The field-level ceiling itself: `2 ^ 9 ∤ 769³ - 1`, so `h ≤ 8` at `q = 769` however `ω` is
chosen. -/
theorem b256_no_taller_orbit : ¬ (2 ^ 9 ∣ 769 ^ 3 - 1) := by norm_num

/-! ## 9. The claim is read off a `cons` root, which Tier A never had

Tier A's committed compute tree is rooted at an `.s6` row, so `publicClaim_genComputeNodes` had
only ever been exercised through `genSkelOp6`'s root triple.  This program's root is the outer
autocons, so the committed subject/formula/evaluation are read off `genSkelCons` — and the
`airReorder` root is a `cons` node, which `airNeedsSwap` leaves unswapped, whereas Tier A's `.s6`
root is swapped. -/

theorem b256_root_state :
    (bpTree (K := DK)).label.skel.state = ComputeTable.State.cons := rfl

theorem b256_air_root_state :
    (airReorder (bpTree (K := DK))).label.skel.state = ComputeTable.State.cons := by
  rw [airReorder_bpTree]; rfl

/-- The committed node tree's root is that same `cons` row — the node the public claim is read
from. -/
theorem b256_committed_root_state :
    (ComputeNode.skel bpData.computeNodes.label).state = ComputeTable.State.cons := by
  show (ComputeNode.skel
    (genComputeNodes DotConfig769.seedZ DotConfig769.alphaA 0 0 1
      (bpTree (K := DK))).label).state = _
  rw [genComputeNodes_label_skel]
  exact b256_root_state

/-! ## 10. What the capstone actually consumes: an eight-state `Data`

§3 says the `Inputs` layer carries no state-conditioned premise.  `CommitmentResidual E`
(`BuildablePackage.lean:67`) does — `slotSemantics`, `recordEquations`, `census`,
`sizeWindowBound`, `scan`, `shapeMatch`, `rowFrame` are all quantified over the committed
skeleton's rows — and `bpPackage`'s residual is `commitmentResidualOfZero bpData`, i.e. it is
`Batch232.bp_data`'s copies of those fields.  So the state coverage that reaches the capstone is
exactly `genData`'s at this program, and these three definitional identities are what make that a
fact rather than an inference: the committed node trees really are the generator's output on
`bpTree`, and the committed rows really are the carrier's execution.

`Batch233.bp_supplies_the_seven` is the state list (`s0, s3, s4, s5, s7, s8, cons` — the seven Tier
A misses), and `GG` §4's `SkeletonAxisRange` OP0 conjunct — vacuous at Tier A for want of an `.s0`
row — is non-vacuous here, since `bpTree` has two. -/

theorem b256_committed_computeNodes :
    bpData.computeNodes =
      genComputeNodes DotConfig769.seedZ DotConfig769.alphaA 0 0 1 (bpTree (K := DK)) := rfl

theorem b256_committed_memoryNodes :
    bpData.memoryNodes =
      genMemoryNodes DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
        (memInputs DotConfig769.seedZ) (bpTree (K := DK)) := rfl

/-- The structure's own field: the committed compute rows are the carrier's compute tree. -/
theorem b256_compute_rows :
    mapNTree ComputeNode.row bpData.computeNodes = Batch232.bp_buildable.exec.computeTree :=
  bpData.compute_rows

/-- And the memory side likewise. -/
theorem b256_memory_rows :
    bpData.memoryNodes.map (mapNTree MemoryNode.row) =
      Batch232.bp_buildable.execA.memoryForest :=
  bpData.memory_rows

/-- The residual the package consumes carries this program's leaf window. -/
theorem b256_residual_Λ : (commitmentResidualOfZero bpData).Λ = 22 := rfl

end

end Nock.RedTeam.Batch256

#print axioms Nock.RedTeam.Batch256.b256_basis_exists
#print axioms Nock.RedTeam.Batch256.bpData
#print axioms Nock.RedTeam.Batch256.b256_hOrbCap
#print axioms Nock.RedTeam.Batch256.b256_hreq
#print axioms Nock.RedTeam.Batch256.b256_hresp
#print axioms Nock.RedTeam.Batch256.b256_hcard
#print axioms Nock.RedTeam.Batch256.bpInputs
#print axioms Nock.RedTeam.Batch256.b256_ioCoins_good
#print axioms Nock.RedTeam.Batch256.bpPackage
#print axioms Nock.RedTeam.Batch256.bpStatement
#print axioms Nock.RedTeam.Batch256.b256_verifier_claim
#print axioms Nock.RedTeam.Batch256.b256_claim_triple
#print axioms Nock.RedTeam.Batch256.b256_claimedResult
#print axioms Nock.RedTeam.Batch256.b256_claim_evalN
#print axioms Nock.RedTeam.Batch256.b256_claim_Holds
#print axioms Nock.RedTeam.Batch256.b256_accAt_eq_22
#print axioms Nock.RedTeam.Batch256.b256_requestIO_length
#print axioms Nock.RedTeam.Batch256.b256_requestNodup
#print axioms Nock.RedTeam.Batch256.b256_compRows
#print axioms Nock.RedTeam.Batch256.b256_memRows
#print axioms Nock.RedTeam.Batch256.b256_memoryBudget
#print axioms Nock.RedTeam.Batch256.b256_memoryCapacity
#print axioms Nock.RedTeam.Batch256.b256_committed_root_state
#print axioms Nock.RedTeam.Batch256.b256_memory_headroom
#print axioms Nock.RedTeam.Batch256.b256_no_taller_orbit
#print axioms Nock.RedTeam.Batch256.b256_committed_computeNodes
#print axioms Nock.RedTeam.Batch256.b256_compute_rows
#print axioms Nock.RedTeam.Batch256.b256_memory_rows
#print axioms Nock.RedTeam.Batch256.b256_residual_Λ
