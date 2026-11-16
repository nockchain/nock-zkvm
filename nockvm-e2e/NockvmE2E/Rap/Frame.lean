/-
RAP-PORT, part 2: the syntactic TWIN of our staged-RAP soundness frame.

The nockvm library is Lean 4.31 (`the nockvm library`) and cannot be imported here. The definitions below are
transcribed from it (source file:line on each); no the nockvm library theorem is re-proved — the nockvm library's pointwise
soundness is the HYPOTHESIS `SoundG` of the bridge.

Abbreviation: `MSF` = `Nock/NockVMROM/Thm54/P8Core/SVFrame/MemSoundnessFamily.lean`,
`SAG` = `Nock/NockVMROM/Thm54/P8Core/SVFrameG/StandaloneG.lean`.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace NockvmE2E.Rap

/-! ## 1. Coins (MSF:100-106) -/

/-- `MSF:100` `CoinFrame`: `n` coins and the block after which each is sampled. -/
structure CoinFrame where
  n : ℕ
  sampledAfter : Fin n → ℕ

/-- `MSF:105` `Coins`. -/
abbrev Coins (Φ : CoinFrame) (K : Type) := Fin Φ.n → K

/-- `MSF:109-111` `StagedCols`: a column of round `r` reads only coins sampled after blocks `< r`. -/
def StagedCols (Φ : CoinFrame) {K : Type} {ι β : Type*} (colRound : ι → ℕ)
    (Q : Coins Φ K → ι → β) : Prop :=
  ∀ j χ χ', (∀ i : Fin Φ.n, Φ.sampledAfter i < colRound j → χ i = χ' i) → Q χ j = Q χ' j

/-- `MSF:119-121` `ReadsOnC`: `f` reads only the coins in `dep`. -/
def ReadsOnC (Φ : CoinFrame) {K : Type} {β : Type*} (dep : Finset (Fin Φ.n))
    (f : Coins Φ K → β) : Prop :=
  ∀ χ χ' : Coins Φ K, (∀ j ∈ dep, χ j = χ' j) → f χ = f χ'

/-! ## 2. Priced summands (MSF:485-504) -/

/-- `MSF:485-493` `BadSummand`, verbatim. -/
structure BadSummand (Φ : CoinFrame) (K : Type) [Fintype K] [DecidableEq K] (Tr : Type)
    (Staged : (Coins Φ K → Tr) → Prop) where
  coins : Finset (Fin Φ.n)
  dep : Finset (Fin Φ.n)
  disj : Disjoint coins dep
  badSet : Tr → Coins Φ K → Finset (coins → K)
  weight : ℕ
  card_le : ∀ tr χ, (badSet tr χ).card ≤ weight
  readsOn : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ dep (fun χ => badSet (Q χ) χ)

/-- `MSF:495-499` `BadSummand.mem`. -/
def BadSummand.mem {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {Tr : Type}
    {Staged : (Coins Φ K → Tr) → Prop} (s : BadSummand Φ K Tr Staged) (tr : Tr) (χ : Coins Φ K) :
    Prop :=
  (fun i : s.coins => χ i) ∈ s.badSet tr χ

/-- `MSF:502-504` `epsilonOf`: `Σ weight / |𝕂|^|coins|`. -/
def epsilonOf {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {Tr : Type}
    {Staged : (Coins Φ K → Tr) → Prop} (summands : List (BadSummand Φ K Tr Staged)) : ℚ :=
  (summands.map fun s => (s.weight : ℚ) / ((Fintype.card K : ℚ) ^ s.coins.card)).sum

/-! ## 3. Traces as columns

Trunk's `Traces F C S := (Fin C.width → F[X]) × (∀ t, Fin (S.table t).width → F[X])` (`MSF:509`) with
`TracesStaged` = `StagedCols` on every table (`MSF:513-516`). The twin flattens the tables into one
column index `ι` with one round map `colRound` (the Nock adapter is the `Sum`/`Sigma` reindexing,
plus the restriction of `F[X]` to a finite degree-bounded value type `β`). -/

/-- Traces: one value per column. -/
abbrev Tr (ι β : Type) := ι → β

/-- `MSF:513-516` `TracesStaged`, on the flattened columns. -/
def TracesStaged (Φ : CoinFrame) {K : Type} {ι β : Type} (colRound : ι → ℕ)
    (Q : Coins Φ K → Tr ι β) : Prop :=
  StagedCols Φ colRound Q

/-! ## 4. `StandaloneG`'s statement shape (SAG:23-62)

`StandaloneG` quantifies over `V : VerifierData` with `V.Checks` (Nock: `P8PublicClaim`,
`StrictOrbitDomain`, …), `AcceptsG` (two `RAP.SatisfiesWithPreprocessing`), and `HoldsF`. For ONE fixed
checked verifier datum these enter only as the four parameters of `RapStatement`; nothing below is
Nock-specific. `M0` is `CC.Msg0 × MC.Msg0` (`msg0C`, `msg0M`, round 0); `Mfin` is
`(Fin nAcc → Kio) × MC.Msg2` evaluated at the full coin vector (`requests χ`, `msg2M χ`, which
`MessagesG` leaves unstaged, i.e. sent after every coin). -/

/-- The verifier-side data of `StandaloneG` at one fixed checked datum `V`. -/
structure RapStatement (Φ : CoinFrame) (K : Type) [Fintype K] [DecidableEq K] (ι β : Type)
    (colRound : ι → ℕ) where
  /-- Round-0 auxiliary prover message (`SAG:26-27` `msg0C`, `msg0M`). -/
  M0 : Type
  /-- Final prover message, after all coins (`SAG:28-29` `requests χ`, `msg2M χ`). -/
  Mfin : Type
  /-- `SAG:42-45` `allSummandsG V x y joint`. -/
  summands : M0 → List (BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound))
  /-- `SAG:35-40` `AcceptsG V msg χ`, as a function of the messages and coins. -/
  Accepts : M0 → Tr ι β → Mfin → Coins Φ K → Prop
  /-- `HoldsF (ringChar K) V.claim`. -/
  Holds : Prop

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ}

/-- `SAG:23-31` `MessagesG`: a (deterministic) prover strategy. -/
structure Messages (R : RapStatement Φ K ι β colRound) where
  m0 : R.M0
  Q : Coins Φ K → Tr ι β
  fin : Coins Φ K → R.Mfin

open Classical in
/-- `SAG:50-55` `StandaloneG.soundness` at the fixed datum (completeness omitted: not used here;
the nockvm library opens `Classical.propDecidable` locally, `SAG:17`). -/
def StandaloneGShape (R : RapStatement Φ K ι β colRound) : Prop :=
  ∀ msg : Messages R, TracesStaged Φ colRound msg.Q →
    ((Finset.univ.filter fun χ : Coins Φ K =>
        R.Accepts msg.m0 (msg.Q χ) (msg.fin χ) χ ∧ ¬ R.Holds).card : ℚ) /
        Fintype.card (Coins Φ K) ≤ epsilonOf (R.summands msg.m0)

/-- **`SAG:64-68` the `hsound` premise of `standaloneG_of_sound`** — the pointwise obligation the nockvm library
proves per instance (`hsoundVSQ`, `hsoundVSQH`), and the hypothesis of the bridge. -/
def SoundG (R : RapStatement Φ K ι β colRound) : Prop :=
  ∀ (m0 : R.M0) (tr : Tr ι β) (fin : R.Mfin) (χ : Coins Φ K),
    R.Accepts m0 tr fin χ → (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → R.Holds

/-! ## 5. Column-locality (twin of `RoundFibredSoundness.lean:574-588` `ColumnLocal.CommittedBy`,
strengthened) -/

/-- Summand `s` is local at block `b`: its priced coins are exactly block-`b` coins, its read coins are
sampled by block `b`, and its bad set reads only columns committed by round `b` and coins in `dep`. -/
structure Local (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)) (b : ℕ) : Prop where
  coins_block : ∀ i ∈ s.coins, Φ.sampledAfter i = b
  dep_le : ∀ i ∈ s.dep, Φ.sampledAfter i ≤ b
  congr : ∀ (tr tr' : Tr ι β) (χ χ' : Coins Φ K), (∀ j, colRound j ≤ b → tr j = tr' j) →
    (∀ i ∈ s.dep, χ i = χ' i) → s.badSet tr χ = s.badSet tr' χ'

end NockvmE2E.Rap
