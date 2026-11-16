/-
  Nock/RedTeam/Batch246Thm54InputsAtGeneratedCarrier.lean

  **`BuildableChips.Inputs` inhabited at the GENERATED carrier, and the Theorem-5.4 statement
  applied there.**

  Both entries close
  with the same "Not claimed" line: `Inputs`, `buildFullPackage` and the statement are untouched. This module supplies the missing second argument.

  `statement_of_generated_residual` (`TraceGen/GenStatement.lean:111`) takes a `Data E`, an
  `Inputs E` and `hz : I.computeChallenges = default`, and yields
  `OptimizedFullStrictThm54Statement (buildFullPackage E I (commitmentResidualOfZero D) hz)`.  It
  is **not** re-proved here — it is applied, at `E := Batch221.b221Buildable` and
  `D := Batch192.b192Data`.

  **The `Inputs` wall does not bind this carrier.**  `GenStatement.lean:120-131` records that
  `Inputs E` needs `basis : Basis (Fin 3) F K`, so an execution over `F = K` has provably
  uninhabited `Inputs` (`no_basis_fin3_field_self`).  Here `F = ZMod 769` and
  `K = GaloisField 769 3` with `finrank F K = 3` (`DotConfig769.finrank_cubic`), so the basis
  exists — `b246_basis_exists` records the check rather than trusting the arithmetic.

  **`computeChallenges = default` is the compiler FOLD tuple, not the RLC coin vector.**
  `FinalComputeChallengeTuple K` carries `challenge9`, `challenge11`, `challenge36`
  (`OptimizedComputeCollisionBound.lean:515`); the compute RLC coins are
  `ComputeTable.Inputs.a/b/c` (`ComputeTable.lean:158`), which sit on the carrier's
  `ChallengeVector` and are `(0, 0, 0)` here for an unrelated reason (`Batch180.dot_computeCoins`
  proves `ComputeCoinsGeneric` at Tier A for **every** `a b c`).

  **Scope.**  One program, one configuration — Tier A over `GaloisField 769 3`, seed `φ(8)`,
  `α = φ(4)`, coins `(0,0,0)`, `Ksz = 64`, `Λ = 22`, table orbit `h = 8`, strict package orbit
  `StrictOrbitDomain F 3 8` of order `768`.  The capstone type
  `optimizedFullStrictNockVMROM_of_package` and the `11+1+2` accounting are untouched, and
  **`claimedResult = result` IS established** — §6 below, via
  `GenClaimedResult.publicClaim_genComputeNodes` and the residual's own `claim_eq`.

  -- the paper
-/
import Mathlib.Tactic.IntervalCases
import Nock.NockVMROM.Thm54.TraceGen.GenCarrierInputs
import Nock.NockVMROM.Thm54.TraceGen.GenClaimedResult
import Nock.NockVMROM.Thm54.TraceGen.GenStatement
import Nock.NockVMROM.Thm54.TraceGen.GenTierAInputsPrep
import Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLayout
import Nock.NockVMROM.Thm54.TraceGen.GenTierAStatement
import Nock.RedTeam.Batch180Thm54GenericSemanticDataAtTierA
import Nock.RedTeam.Batch192Thm54DataAtTierA
import Nock.RedTeam.Batch216Thm54SemanticCoverageAtTierA
import Nock.RedTeam.Batch221Thm54BuildableAtTierA

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch246

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.RedTeam

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK

noncomputable section



/-! ## 1. The `Inputs` wall, checked rather than assumed

`GenStatement.no_basis_fin3_field_self` empties `Inputs` whenever `F = K`.  This carrier has
`finrank F K = 3`, so the basis the wall is about actually exists. -/

theorem b246_finrank : Module.finrank DF DK = 3 := DotConfig769.finrank_cubic

theorem b246_basis_exists : Nonempty (Module.Basis (Fin 3) DF DK) :=
  ⟨DotConfig769.basis⟩

/-! ## 2. The three arithmetic side conditions `inputsOfCarrier` spends

-/

/-- The generated carrier's table orbit is the `2^8` one. -/
theorem b246_orbit_h : Batch221.b221Buildable.cfg.orbit.h = 8 := rfl

/-- The strict package orbit (order `e·2^h = 3·256 = 768`) is at least as tall as the table
orbit, so the two active-domain prefixes fit. -/
theorem b246_hOrbCap : 2 ^ Batch221.b221Buildable.cfg.orbit.h ≤ 2 ^ 8 := by
  rw [b246_orbit_h]


theorem b246_hreq : Batch221.b221Buildable.exec.derivedRequestIO.length ≤ 255 := by
  rw [Batch221.b221_requestIO_length]
  norm_num

/-- The response column fits below the table orbit, by the carrier's own `memoryIOCapacity`. -/
theorem b246_hresp : Batch221.b221Buildable.exec.derivedResponseIO.length ≤ 255 := by
  have h := Batch221.b221Buildable.memoryIOCapacity
  rw [b246_orbit_h] at h
  norm_num at h
  omega

/-- The counted IO failure mass at the capacity ceiling, against `|K|² = 769⁶` (the 31st: the
honest budget covers the nine- and the ten-slot events, `RecordCarrier.honestIOBound`). -/
theorem b246_hcard :
    RecordCarrier.honestIOBound 255 255 (Fintype.card DK) < Fintype.card (DK × DK) := by
  rw [RecordCarrier.honestIOBound_eq, Fintype.card_prod, DotConfig769.card_K]
  norm_num

/-! ## 3. `Inputs` at the generated carrier -/


theorem b246_interCard :
    2 * ((executionInterRecords Batch221.b221Buildable).requests.length +
      (executionInterRecords Batch221.b221Buildable).responses.length) + 1 <
        Fintype.card DK :=
  executionInterRecords_card_lt_of_memRows Batch221.b221Buildable (by
    have hmem : Batch221.b221Buildable.cfg.memRows = 184 := by
      rw [Batch221.b221_cfg]
      exact Batch180.dot_memRowsLen
    have hq : Fintype.card DK = 769 ^ 3 := DotConfig769.card_K
    rw [hmem, hq]
    norm_num)


theorem b246_honestVer :
    ∀ row ∈ Batch221.b221Buildable.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  change ∀ row ∈ Batch216.b216Exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
  exact honestVer_of_bindsAt Batch216.b216Binds

def b246Inputs : Inputs Batch221.b221Buildable :=
  inputsOfCarrier Batch221.b221Buildable DotConfig769.stateTagChar DotConfig769.basis
    DotConfig769.strictOrbit b246_hOrbCap 255 b246_hreq b246_hresp
    b246_hcard
    2 2 5 (fun j => (j : DF) + 1) 0
    (interCard_of_unionBound Batch221.b221Buildable
      (by
        have h184 : Batch221.b221Buildable.cfg.memRows = 184 := by
          rw [Batch221.b221_cfg]
          exact Batch180.dot_memRowsLen
        rw [h184]
        norm_num) b246_hcard)
    b246_honestVer

theorem b246_challenges : b246Inputs.computeChallenges = default := rfl

theorem b246_hOrb : b246Inputs.hOrb = 8 := rfl

theorem goldilocks769_two_pow_ne_one :
    ∀ k : ℕ, 0 < k → k < 17 → (2 : DF) ^ k ≠ 1 := by
  intro k hk0 hk
  revert hk0
  interval_cases k <;> decide

theorem goldilocks769_two_base_order_ge (n : ℕ) (hn : n ≤ 17) :
    n ≤ orderOf (2 : DF) := by
  refine le_of_not_gt fun hlt => ?_
  have hfin : IsOfFinOrder (2 : DF) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨768, by norm_num, by decide⟩
  have hpos : 0 < orderOf (2 : DF) :=
    Nat.pos_of_ne_zero fun h0 => (orderOf_eq_zero_iff.mp h0) hfin
  exact goldilocks769_two_pow_ne_one (orderOf (2 : DF)) hpos
    (hlt.trans_le hn) (pow_orderOf_eq_one _)

/-- `2` in Goldilocks (`𝔽₇₆₉`) has order `384`.  Any fixture with at most
`17` compute rows therefore sits below `orderOf 2` after the cubic embedding. -/
theorem b246_two_order_ge (n : ℕ) (hn : n ≤ 17) :
    n ≤ orderOf (2 : DK) := by
  have hcast : (2 : DK) = (algebraMap DF DK).toMonoidHom (2 : DF) :=
    (map_natCast (algebraMap DF DK) 2).symm
  rw [hcast, orderOf_injective (algebraMap DF DK).toMonoidHom
    (RingHom.injective (algebraMap DF DK)) (2 : DF)]
  exact goldilocks769_two_base_order_ge n hn

theorem b246_walkOrder :
    2 ≤ Batch221.b221Buildable.cfg.compRows →
      Batch221.b221Buildable.cfg.compRows ≤ orderOf b246Inputs.computeWalkAlpha := fun _ => by
  have hα : b246Inputs.computeWalkAlpha = (2 : DK) := rfl
  have hrows : Batch221.b221Buildable.cfg.compRows = 8 := by
    rw [Batch221.b221_cfg]; exact Batch180.dot_compRowsLen
  rw [hα, hrows]
  exact b246_two_order_ge 8 (by norm_num)

theorem b246_memoryWalkOrder :
    2 ≤ Batch221.b221Buildable.cfg.memRows →
      Batch221.b221Buildable.cfg.memRows ≤ orderOf b246Inputs.memoryWalkAlpha := fun _ => by
  have hα : b246Inputs.memoryWalkAlpha = (2 : DK) := rfl
  have hrows : Batch221.b221Buildable.cfg.memRows = 184 := by
    rw [Batch221.b221_cfg]; exact Batch180.dot_memRowsLen
  rw [hα, hrows]
  have hcast : (2 : DK) = (algebraMap DF DK).toMonoidHom (2 : DF) :=
    (map_natCast (algebraMap DF DK) 2).symm
  rw [hcast, orderOf_injective (algebraMap DF DK).toMonoidHom
    (RingHom.injective (algebraMap DF DK)) (2 : DF)]
  have : orderOf (2 : DF) = 384 :=
    DotConfig769.goldilocks769_two_order
  omega

/-- The record sample the IO coins were chosen against is the carrier's own derived pair. -/
theorem b246_records :
    executionRecords Batch221.b221Buildable =
      ⟨Batch221.b221Buildable.exec.derivedRequestIO,
        Batch221.b221Buildable.exec.derivedResponseIO⟩ :=
  rfl

/-- Non-vacuity: the coins really are outside the joint counted failure event, on a
thirteen-record request column (`Batch221.b221_requestIO_length`). -/
theorem b246_ioCoins_good :
    (b246Inputs.ioCoins.gamma, b246Inputs.ioCoins.pole) ∉
      IOFailureEvent (executionRecords Batch221.b221Buildable) :=
  ioCoinsOfCarrier_good Batch221.b221Buildable 255 b246_hreq b246_hresp
    b246_hcard

/-! ## 4. The package and the released statement

`statement_of_generated_residual` is applied, not re-proved.  `D` is `Batch192.b192Data`, the
`Data` over this very carrier, so the committed half is the generator's own honest commitment. -/



theorem b246_hmore : BuildableAxisWitness.LaterSeedZeros Batch221.b221Buildable :=
  Batch221.b221_laterSeedZeros

theorem b246_prl : RowLayout.PairedRecordLayout Batch221.b221Buildable.exec := by
  rw [Batch221.b221_exec]
  exact genExactExecution_pairedRecordLayout (F := DF) Batch216.b216Chal 64
    executionOrbit Batch216.b216_horb seedZ alphaA 0 0 0 (memInputs seedZ)
    (dotTree (K := DK)) Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
    -- 28th: state agreement of the a-bearing rows (the row encode needs it, `encodeRow_pub`)
    (by
      intro row hrow
      erw [genExactExecutionA_memoryRows] at hrow
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hrow
      exact genThreadedMemory_state seedZ alphaA (memInputs seedZ) (genComputeSkeleton_dot 0) n hn)
    (honestVer_of_bindsAt Batch216.b216Binds)

/-- H1.5b Part 2a: the package's `rowsBound` at the generated carrier (both `≤ 256`, `3·256 < 769`). -/
theorem b246_hrows :
    3 * Batch221.b221Buildable.cfg.compRows < ringChar DK ∧
      Batch221.b221Buildable.cfg.memRows < ringChar DK := by
  have h1 : Batch221.b221Buildable.cfg.compRows ≤ 2 ^ DotConfig769.executionOrbit.h :=
    Batch216.b216_comp_le
  have h2 : Batch221.b221Buildable.cfg.memRows ≤ 2 ^ DotConfig769.executionOrbit.h :=
    Batch216.b216_mem_le
  norm_num [DotConfig769.executionOrbit] at h1 h2
  rw [DotConfig769.ringChar_K]
  constructor <;> omega


theorem b246_generated :
    GeneratedField.ClaimGenerated DK (commitmentResidualOfZero Batch192.b192Data).verifier.raw.claim
      (commitmentResidualOfZero Batch192.b192Data).Λ := by
  have hc : (commitmentResidualOfZero Batch192.b192Data).verifier.raw.claim =
      ⟨dotSubject, dotFormula, dotResult⟩ :=
    publicClaim_genComputeNodes _ _ _ _ _ _ (genComputeSkeleton_dot (K := DK) 0)
  exact GeneratedField.claimGenerated_of_eq (congrArg P8PublicClaim.subject hc)
    (congrArg P8PublicClaim.formula hc) (DotConfig769.dot_program_generated _ (le_of_eq rfl))

/-- The constructed Theorem-5.4 package at the generated carrier. -/
def b246Package : OptimizedFullStrictNockVMROMPackage DF DK b246Inputs.hOrb :=
  buildFullPackage Batch221.b221Buildable b246Inputs
    (commitmentResidualOfZero Batch192.b192Data) b246_challenges b246_prl
    (hmore := b246_hmore) (hord := b246_walkOrder)
    (hordM := b246_memoryWalkOrder) (hrows := b246_hrows)
    (hgenF := b246_generated) (hF := DotConfig769.dot_primeField)

/-- **The released fourteen-field Theorem-5.4 statement, at the generated carrier.** -/
theorem b246Statement
    (hax : FormRAxisBound b246Package.optimized.sampled
      b246Package.optimized.basis)
    (hbasis : FormRBasis b246Package.optimized.basis)
    (hwidth : FormRWidth DF) :
    OptimizedFullStrictThm54Statement b246Package :=
  Nock.NockVMROM.Thm54.TraceGen.statement_of_generated_residual
    Batch192.b192Data b246Inputs b246_challenges b246_prl
    (hmore := b246_hmore) (hord := b246_walkOrder)
    (hordM := b246_memoryWalkOrder) (hrows := b246_hrows)
    (hgenF := b246_generated) (hF := DotConfig769.dot_primeField) hax hbasis hwidth

/-! ## 5. Read off the assembled package

The package cannot have selected a different execution: its chained language and its IO strategy
are the ones `buildFullPackage` derives from this carrier. -/

theorem b246_package_q : b246Package.q = 769 := rfl

theorem b246_package_ioStrategy :
    b246Package.ioStrategy = finiteIOStrategy Batch221.b221Buildable b246Inputs := rfl

theorem b246_package_honestSeed : b246Package.honestSeed = DotConfig769.seedZ := rfl

/-! ## 6.

The released package carries no field literally named `claimedResult`; the object is the committed
`P8PublicClaim` its verifier holds, and `CommitmentResidual.claim_eq` identifies that with the
committed skeleton's `publicClaim`.  `GenClaimedResult` supplies the generic half; here it is read
at this program, against `dotResult` and against the reference evaluator. -/

/-- The package's verifier claim is the committed skeleton's public claim — the residual's own
`claim_eq`, at the assembled package. -/
theorem b246_verifier_claim :
    b246Package.optimized.verifier.raw.claim =
      (commitmentResidualOfZero Batch192.b192Data).commitment.skeleton.publicClaim :=
  (commitmentResidualOfZero Batch192.b192Data).claim_eq.symm

/-- **The committed claim is the program's own triple.** -/
theorem b246_claim_triple :
    b246Package.optimized.verifier.raw.claim =
      ⟨dotSubject, dotFormula, dotResult⟩ := by
  rw [b246_verifier_claim]
  exact publicClaim_genComputeNodes (K := DK) DotConfig769.seedZ DotConfig769.alphaA 0 0 0 _
    (genComputeSkeleton_dot 0)

/-- **`claimedResult = result`.**  The package's claimed result is `dotResult`. -/
theorem b246_claimedResult :
    b246Package.optimized.verifier.raw.claim.result = dotResult := by
  rw [b246_claim_triple]

/-- And `dotResult` is what the reference evaluator returns, so the claim is not merely internally
consistent — `P8PublicClaim.Holds` is the paper's genuine-evaluator predicate. -/
theorem b246_claim_evalN :
    Nock.evalN 4 dotSubject dotFormula =
      some dotResult :=
  genComputeSkeleton_evalN (K := DK) (genComputeSkeleton_dot 0)

theorem b246_claim_Holds : (b246Package.optimized.verifier.raw.claim).Holds := by
  rw [b246_verifier_claim]
  exact publicClaim_Holds (K := DK) DotConfig769.seedZ DotConfig769.alphaA 0 0 0 _
    (genComputeSkeleton_dot 0)

end

end Nock.RedTeam.Batch246

#print axioms Nock.RedTeam.Batch246.b246_basis_exists
#print axioms Nock.RedTeam.Batch246.b246_hOrbCap
#print axioms Nock.RedTeam.Batch246.b246_hreq
#print axioms Nock.RedTeam.Batch246.b246_hresp
#print axioms Nock.RedTeam.Batch246.b246_hcard
#print axioms Nock.RedTeam.Batch246.b246Inputs
#print axioms Nock.RedTeam.Batch246.b246_ioCoins_good
#print axioms Nock.RedTeam.Batch246.b246Package
#print axioms Nock.RedTeam.Batch246.b246Statement
#print axioms Nock.RedTeam.Batch246.b246_verifier_claim
#print axioms Nock.RedTeam.Batch246.b246_claim_triple
#print axioms Nock.RedTeam.Batch246.b246_claimedResult
#print axioms Nock.RedTeam.Batch246.b246_claim_evalN
#print axioms Nock.RedTeam.Batch246.b246_claim_Holds
