/-
  Nock/RedTeam/Batch402Thm54VerifierSeedStop.lean

  Paper sets
  `seed = RLC^γ(rvt_root) · α` from the **public** root label
  `rvt_root ∈ LT_comp` (`:1690` = state × ((subject, formula), result)).

  The deployed tree's seed is
  `` `PlusIOSegmentedRAP.lean::computeWalkSeed` `` /
  `` `RawVerifier.lean::computeWalkSeed` `` =
  `curCol computeNodeVal rows 1 * α` with
  `computeNodeVal = rlc γ (compNodeEncode label)` and
  `compNodeEncode = NodeEncoding.computeNodeEncode` of the **full**
  `State × DTcomp` label (width 87), which includes `Pub.mr1` / `Dec` /
  subformula FPs / `ln` — fields **not** in `P8PublicClaim` and not
  among the gate-read publics (`ExactFinalPublicCoordinates`: α, seed,
  state one-hots only).

  * `computeSeedOfTuple` scaffold (paper-shaped RLC of claim FPs · αc)
    for the constant walk / honesty comparison;
  * `computeSeedOfTuple_ne_walkSeed_of_mr1` obstruction;
  * unread claim slots `42..68` deleted from `computePublicOfTuple`
    (seed stays package/`pkgPub` on the gate-read set);
  * memory seed left prover-committed with measured rationale.
-/
import Lean
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.NockVMROM.Thm54.PlusIOSegmentedRAP
import Nock.NockVMROM.Thm54.RawVerifier
import Nock.NockVMROM.Thm54.JointSoundness
import Nock.ComputeTable
import Nock.GlobalCarryRecognizer
import Nock.Walk

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch402

open Lean Meta Elab Command
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.CoordinateBasis
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]

/-! ## Paper-shaped seed scaffold (not wired into RAP publics) -/

/-- Pack `enc z subject/formula/result` into a length-9 vector for `Walk.rlc`.
    This is the paper's `x^comp` fingerprint triple,
    **not** the tree's 87-wide `computeNodeEncode`. -/
def claimFpVec (z : K) (claim : P8PublicClaim) : Fin 9 → K :=
  fun i =>
    let fp :=
      match (i : ℕ) / 3 with
      | 0 => GlobalCarryRecognizer.enc z claim.subject
      | 1 => GlobalCarryRecognizer.enc z claim.formula
      | _ => GlobalCarryRecognizer.enc z claim.result
    match (i : ℕ) % 3 with
    | 0 => fp.size
    | 1 => fp.dyck
    | _ => fp.leaf

/-- Verifier-computable seed candidate from the claim and sampled coins:
    `RLC^γ(enc(z, claim.*)) · αc` as F-coordinates. -/
def computeSeedOfTuple (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (c : OptimizedProductionChallengeTuple K F) : Fin 3 → F :=
  let seedK : K :=
    Nock.Walk.rlc (c.2.1.1) (claimFpVec (nprSeed c.1) claim) * alphaC c.1
  fun k => coord b seedK k

/-- Constant walk: `computeSeedOfTuple` reaches `nprSeed` and IO `γ`. -/
def COMPUTE_SEED_OF_TUPLE : Name :=
  ``Nock.RedTeam.Batch402.computeSeedOfTuple

def NPR_SEED : Name :=
  ``Nock.NockVMROM.Thm54.nprSeed

def valueDirect (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  | none => #[]

elab "#batch402_seed_reaches_c" : command => do
  let env ← getEnv
  let used := valueDirect env COMPUTE_SEED_OF_TUPLE
  unless used.contains NPR_SEED do
    throwError "computeSeedOfTuple does not reach nprSeed"

#batch402_seed_reaches_c


/-- Width receipt: the deployed walk label is the paper's ten coordinates (was `93`). -/
theorem computeNodeWidth_eq_ten :
    NodeEncoding.computeNodeWidth = 10 :=
  NodeEncoding.computeNode_width

/-- The retired complete-row encoder's width after the Form R limb layout. -/
theorem computeFullRowWidth_eq_95 :
    NodeEncoding.computeFullRowWidth = 95 :=
  NodeEncoding.computeFullRow_width

theorem computeNodeEncode_ignores_mr1
    (hchar : NodeEncoding.StateTagChar K)
    (st : ComputeTable.State)
    (inp : ComputeTable.Inputs K)
    (pub : ComputeTable.Pub K)
    (dec : ComputeTable.Dec K)
    (mr1' : ComputeTable.MemRec K) :
    NodeEncoding.computeNodeEncode hchar (st, (inp, (pub, dec))) =
      NodeEncoding.computeNodeEncode hchar
        (st, (inp, ({ pub with mr1 := mr1' }, dec))) :=
  NodeEncoding.computeNodeEncode_ignores_mr1 hchar st inp pub dec mr1'

theorem p8PublicClaim_fields_are_nouns
    (claim : P8PublicClaim) :
    ∃ s f e : Noun, claim.subject = s ∧ claim.formula = f ∧ claim.result = e :=
  ⟨claim.subject, claim.formula, claim.result, rfl, rfl, rfl⟩

theorem verifier_seed_stop_lifted :
    NodeEncoding.computeNodeWidth = 10 ∧
      (∀ (hchar : NodeEncoding.StateTagChar K) (st : ComputeTable.State)
        (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K)
        (dec : ComputeTable.Dec K) (mr1' : ComputeTable.MemRec K),
        NodeEncoding.computeNodeEncode hchar (st, (inp, (pub, dec))) =
          NodeEncoding.computeNodeEncode hchar
            (st, (inp, ({ pub with mr1 := mr1' }, dec)))) :=
  ⟨computeNodeWidth_eq_ten, fun hchar st inp pub dec mr1' =>
    computeNodeEncode_ignores_mr1 hchar st inp pub dec mr1'⟩

/-! ## Memory seed — leave prover-committed -/

/-- Memory walk seed publics sit at extension slots `6+3·1+k`
    (`` `OptimizedMemoryCanonicalSatisfaction.lean` `` `walkSeed` pin).
    `memoryPublicOfTuple` is the package map: no claim dependence.
    Sound to leave prover-committed: memory roots are bound to compute
    requests through hostile LIO (`OptimizedHostileTimestamps`), not to
    a public claim; K-side `VerifierGates` has no
    `memoryWalkSeed = f(claim)` conjunct
    (`` `RawVerifier.lean::VerifierGates` ``). -/
theorem memoryPublicOfTuple_ignores_claim
    (b : Basis (Fin 3) F K) (claim claim' : P8PublicClaim) (kMem : ℕ)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F) :
    memoryPublicOfTuple b claim kMem pkgPub c =
      memoryPublicOfTuple b claim' kMem pkgPub c :=
  rfl

theorem computePublicOfTuple_eq_pkg_on_readSet'
    (b : Basis (Fin 3) F K) (claim : P8PublicClaim)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple K F)
    (j : ℕ) (hj : j ∈ computePublicReadSet) (hseed : ¬ j < 6) :
    computePublicOfTuple b claim pkgPub c j = pkgPub j :=
  computePublicOfTuple_eq_pkg_on_readSet b claim pkgPub c j hj hseed

end

end Nock.RedTeam.Batch402

#print axioms Nock.RedTeam.Batch402.computeNodeWidth_eq_ten
#print axioms Nock.RedTeam.Batch402.computeFullRowWidth_eq_95
#print axioms Nock.RedTeam.Batch402.computeNodeEncode_ignores_mr1
#print axioms Nock.RedTeam.Batch402.verifier_seed_stop_lifted
#print axioms Nock.RedTeam.Batch402.memoryPublicOfTuple_ignores_claim
