/-
  Nock/NockVMROM/Thm54/StandaloneVerifierData.lean

  **The verifier data `V`, the prover
  messages `m` over `repartitionedChronology`, and the chips `chipsOf V m c` — with NO package.**

  * `VerifierData F K h`: the claim, the received-then-checked sizes `N, M, kMem, Ksz`, the basis,
    the orbit and the two row-node maps.  The CHECKS of §1.2 (row budget, `rowsBound`, IO window,
    `FormRBasis`, `hp`/`hp64`/`PrimeFieldElems`, node injectivity/adjacency) are the separate `Prop`
    `VerifierData.Checks V`, so that the chips (which read none of them) and `ofPackage` need no
    hypothesis; a soundness statement takes `V.Checks` as its hypothesis.
  * The
    generic layer knows only: a width, a column-round map, a B0 message type `Msg0`, a B2 message
    type `Msg2`, and a constructor reading `(V, msg0, requests, msg2, c)`.  Nothing here outside
    `currentMemFamily` reads the current memory chip's internals (its public layout, width 205).
  * `Messages F K MF`: compute columns at width 309, memory columns at `MF.width`, the compute
    last-row state (B0, publics 31..41), the compute B0 rest map `restC`, the memory B0 message,
    `requests : Tuple12 → K` (B2, read by BOTH chips: compute publics 6..8, and whatever slots the
    memory family assigns), the memory B2 message.
  * `pubC`, `chipsOf`, `AcceptsV`, `StagedV`.
  * `currentMemFamily`: the landed twelve-coin memory chip as one instance (`Msg0 := ℕ → F` the
    memory B0 rest map, `Msg2 := K` the memory seed at publics 9..11, `requests` at 12..14).
  * `ofPackage P`, `msgsOf P`, and `chipsOf_ofPackage`: the package is an instance,
    `chipsOf (ofPackage P) (msgsOf P) c = (pkgComputeChipAt309 P (forget12 c), Pkg12.memoryChipAt12 P c)`.
    **Not `rfl`**: a THEOREM, by `funext` on the two public maps through the package pins
    (`computeRequestsPins`, `computePublicPins`, `memoryCoordinatePins.requests`) and one hypothesis
    `hst` (the package's root-row state is `rootStateOfFormula` of the claim's formula — N4; the
    package type does not force it, generated packages satisfy it, and it is exactly the premise
    `computeChipAt_honest_of_chalVal` already carries).

  The design's `pubC`/`pubM` are `0` off the slots they
  name.  Here those slots are a B0 prover message (`restC`, and `currentMemFamily`'s `Msg0`): the
  package's own public maps are arbitrary at every unpinned slot, so a `0` default makes
  `chipsOf_ofPackage` false without a slot-level public read-set congruence of both chips (not
  available; the compute instrument does not reduce by `rfl` over `allGates309`).  The theorem
  `∀ m, …` over these messages is STRONGER than at the `0` verifier (it is the instance
  `restC := 0`), and the slots a B0 rest map supplies are exactly the ones the package leaves
  unpinned, which every landed `∀ package` theorem already quantifies over.  The verifier-owned
  slots are unchanged: compute `0..5` (`computePublicOfTuple`), `20..30` (`rootStateOneHot`), memory
  `6..8` (`memoryPublicOfTuple12`).

  No window quantity (`Λ`, `programLeafBound`, `leafBoundF`) enters any definition here.
-/
import Nock.NockVMROM.Thm54.GeneratedField
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.BelowDefs.Unhosted309Events
import Nock.NockVMROM.Thm54.P8Core.PartAMemoryChip12

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.StandaloneVerifier

open Nock Nock.Framework Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.PartA12
open Module
open scoped Polynomial

noncomputable section

/-- The twelve-coin challenge tuple (`repartitionedChronology`'s coins). -/
abbrev Tuple12 (K F : Type) [Fintype K] [Fintype F] := OptimizedProductionChallengeTuple12 K F

/-! ## 1. Verifier data -/

section Data

variable (F K : Type) [Field F] [Field K] [Algebra F K]

/-- The claim `X`,
the prover-sent sizes `N, M, kMem, Ksz` (B0; checked by `Checks`), the verifier constants `basis`,
`orbit` and the row-node maps.  `hN`/`hM` are here because the chip constructors take them. -/
structure VerifierData (h : ℕ) where
  claim : P8PublicClaim
  N : ℕ
  M : ℕ
  kMem : ℕ
  Ksz : ℕ
  hN : 0 < N
  hM : 0 < M
  basis : Basis (Fin 3) F K
  orbit : StrictOrbitDomain F 3 h
  computeNodes : Fin N → F
  memoryNodes : Fin M → F

variable {F K}

/-- Row budget, `rowsBound` (hrows (a′)), the IO window (`:1450`,
`hKszChar`), the Form R basis and width (`FormRWidth_of_hp64`), and the row-node shape of the
package's `computeNodes_injective` / `computeAdjacentOrbit` / `memoryNodes_injective` /
`memoryOrbitAligned`. -/
structure VerifierData.Checks {h : ℕ} (V : VerifierData F K h) : Prop where
  hcap : V.N ≤ 2 ^ h ∧ V.M ≤ 2 ^ h
  hrows : 3 * V.N < ringChar K ∧ V.M < ringChar K
  hkMem : 2 * V.kMem ≤ V.Ksz
  hKsz : V.Ksz < ringChar K
  hbasis : OptimizedComputeFinalTrace.FormRBasis V.basis
  hp : 25 ≤ ringChar F
  hp64 : ringChar F < 2 ^ 64
  hF : GeneratedField.PrimeFieldElems F
  computeNodes_injective : Function.Injective V.computeNodes
  computeAdjacentOrbit : ∀ (i : Fin V.N) (hi : (i : ℕ) + 1 < V.N),
    V.computeNodes ⟨(i : ℕ) + 1, hi⟩ = V.orbit.ω * V.computeNodes i
  memoryNodes_injective : Function.Injective V.memoryNodes
  memoryAdjacentOrbit : ∀ (i : Fin V.M) (hi : (i : ℕ) + 1 < V.M),
    V.memoryNodes ⟨(i : ℕ) + 1, hi⟩ = V.memoryNodes i * V.orbit.ω

end Data

/-! ## 2. The memory chip as a parameter -/

section Family

variable (F K : Type) [Field F] [Field K] [Algebra F K] [Fintype K] [Fintype F]

/-- `Msg0` is the family's B0 (coin-free) prover message, `Msg2` its B2
message (any function of the twelve coins); `requests` is shared with the compute chip. -/
structure MemChipFamily (h : ℕ) where
  width : ℕ
  colRound : Fin width → ℕ
  Msg0 : Type
  Msg2 : Type
  chip : VerifierData F K h → Msg0 → K → Msg2 → Tuple12 K F → FixedPreprocessingRAP F
  chip_width : ∀ V x r y c, (chip V x r y c).rap.w = width

end Family

/-! ## 3. Prover messages over `repartitionedChronology` -/

section Messages

variable (F K : Type) [Field F] [Field K] [Algebra F K] [Fintype K] [Fintype F]

/-- The columns are coin-indexed and
constrained by `StagedV`; `lastState`, `restC`, `memMsg0` are B0 constants (by type);
`requests` and `memMsg2` are B2. -/
structure Messages {h : ℕ} (MF : MemChipFamily F K h) where
  Qc : Tuple12 K F → Fin 309 → F[X]
  Qm : Tuple12 K F → Fin MF.width → F[X]
  lastState : Fin 11 → F
  /-- B0: every compute public slot the verifier does not own and no other message names. -/
  restC : ℕ → F
  memMsg0 : MF.Msg0
  /-- B2: the shared IO terminal, compute publics `6..8` and the memory family's slots. -/
  requests : Tuple12 K F → K
  memMsg2 : Tuple12 K F → MF.Msg2

end Messages

section Chips

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]

def rootStateOneHot (formula : Noun) (j : Fin 11) : F :=
  if j = OptimizedComputeCodec.stateIndex (ComputeWalkSeed.rootStateOfFormula formula) then 1 else 0

/-- Slots `0..5` are then overwritten by `computePublicOfTuple`. -/
def pubC {h : ℕ} {MF : MemChipFamily F K h} (V : VerifierData F K h) (m : Messages F K MF)
    (c : Tuple12 K F) : ℕ → F :=
  fun j =>
    if h1 : 6 ≤ j ∧ j < 9 then coord V.basis (m.requests c) ⟨j - 6, by omega⟩
    else if h2 : 20 ≤ j ∧ j < 31 then rootStateOneHot V.claim.formula ⟨j - 20, by omega⟩
    else if h3 : 31 ≤ j ∧ j < 42 then m.lastState ⟨j - 31, by omega⟩
    else m.restC j

def chipsOf {h : ℕ} {MF : MemChipFamily F K h} (V : VerifierData F K h) (m : Messages F K MF)
    (c : Tuple12 K F) : FixedPreprocessingRAP F × FixedPreprocessingRAP F :=
  (Unhosted309.computeChipAt309 V.hN V.computeNodes V.basis
      (DeployedChipFamily.computePublicOfTuple V.basis V.claim (pubC V m c) (forget12 c))
      V.orbit (forget12 c),
   MF.chip V m.memMsg0 (m.requests c) (m.memMsg2 c) c)

theorem chipsOf_fst_width {h : ℕ} {MF : MemChipFamily F K h} (V : VerifierData F K h)
    (m : Messages F K MF) (c : Tuple12 K F) : (chipsOf V m c).1.rap.w = 309 := rfl

theorem chipsOf_snd_width {h : ℕ} {MF : MemChipFamily F K h} (V : VerifierData F K h)
    (m : Messages F K MF) (c : Tuple12 K F) : (chipsOf V m c).2.rap.w = MF.width :=
  MF.chip_width _ _ _ _ _

/-- **Acceptance at the standalone verifier**: both chips at `c` accept the messages' columns. -/
structure AcceptsV {h : ℕ} {MF : MemChipFamily F K h} (V : VerifierData F K h)
    (m : Messages F K MF) (c : Tuple12 K F) : Prop where
  compute : RAP.SatisfiesWithPreprocessing (chipsOf V m c).1
    (fun j => m.Qc c (Fin.cast (chipsOf_fst_width V m c) j))
  memory : RAP.SatisfiesWithPreprocessing (chipsOf V m c).2
    (fun j => m.Qm c (Fin.cast (chipsOf_snd_width V m c) j))

/-- `requests`/`memMsg2` are B2 (unconstrained), the rest are constants. -/
def StagedV {h : ℕ} {MF : MemChipFamily F K h} (m : Messages F K MF) : Prop :=
  Staged12 (K := K) (F := F) (fun j : Fin 309 => RepartitionedStaging.newComputeColRound j) m.Qc ∧
    Staged12 (K := K) (F := F) MF.colRound m.Qm

end Chips

/-! ## 4. The current memory chip as one family -/

section Current

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]

/-- The current memory chip's public map before its walk block: `9..11` the seed message,
`12..14` `requests`, the B0 rest map elsewhere (`6..8` are then overwritten by
`memoryPublicOfTuple12`). -/
def pubMCurrent {h : ℕ} (V : VerifierData F K h) (rest : ℕ → F) (requests seed : K) : ℕ → F :=
  fun j =>
    if h1 : 9 ≤ j ∧ j < 12 then coord V.basis seed ⟨j - 9, by omega⟩
    else if h2 : 12 ≤ j ∧ j < 15 then coord V.basis requests ⟨j - 12, by omega⟩
    else rest j

/-- **The landed twelve-coin memory chip as a `MemChipFamily`.** -/
def currentMemFamily (h : ℕ) : MemChipFamily F K h where
  width := 205
  colRound := fun j => RepartitionedStaging.newMemoryColRound j
  Msg0 := ℕ → F
  Msg2 := K
  chip := fun V rest req seed c =>
    DeployedChipFamily12.memoryChipAt12 V.hM V.memoryNodes V.basis
      (memoryPublicOfTuple12 V.basis V.claim V.kMem (pubMCurrent V rest req seed) c)
      V.orbit c V.kMem
  chip_width := fun _ _ _ _ _ => namedFinalMemoryRAP12_w _ _ _ _ _ _ _

end Current

end

end Nock.NockVMROM.Thm54.StandaloneVerifier
