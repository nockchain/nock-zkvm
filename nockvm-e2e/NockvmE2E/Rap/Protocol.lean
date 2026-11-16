/-
RAP-PORT, part 3a: a staged RAP as an Interaction protocol in Quang Dao's
fixed-round presentation `StateRestoration.protocol rounds`,
`Interaction/Oracle/Security/StateRestoration.lean:36-55`), so that the bridge lands directly in the premises
of `singleSalt_knowledge_soundness` (`FiatShamir/SingleSaltSecurity.lean:218`). 

Rounds: `[M0 | Unit]`, then for `r = 0 … nb-1` `[Cols r | Block r]` (round-`r` columns as one oracle message,
then the coins sampled after round `r`), then `[Mfin | Unit]`. Generic in the frame; nothing Nock-specific.
-/
import NockvmE2E.Rap.Frame
import ArkLib.Interaction.Oracle.Security.StateRestorationBudget

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration

namespace NockvmE2E.Rap

variable {Φ : CoinFrame} {K : Type} {ι β : Type} {colRound : ι → ℕ}

/-- The columns committed in round `r`. -/
abbrev Cols (colRound : ι → ℕ) (β : Type) (r : ℕ) := {j : ι // colRound j = r} → β

/-- The coin block sampled after round `r`. -/
abbrev Block (Φ : CoinFrame) (K : Type) (r : ℕ) := {i : Fin Φ.n // Φ.sampledAfter i = r} → K

/-- Write round `r`'s columns into a trace. -/
def setCols (r : ℕ) (c : Cols colRound β r) (tr : Tr ι β) : Tr ι β :=
  fun j => if h : colRound j = r then c ⟨j, h⟩ else tr j

/-- Write block `r`'s coins into a coin vector. -/
def setBlock (r : ℕ) (c : Block Φ K r) (χ : Coins Φ K) : Coins Φ K :=
  fun i => if h : Φ.sampledAfter i = r then c ⟨i, h⟩ else χ i

theorem setCols_of_ne {r : ℕ} (c : Cols colRound β r) (tr : Tr ι β) {j : ι} (h : colRound j ≠ r) :
    setCols r c tr j = tr j := by simp [setCols, h]

theorem setBlock_of_ne {r : ℕ} (c : Block Φ K r) (χ : Coins Φ K) {i : Fin Φ.n}
    (h : Φ.sampledAfter i ≠ r) : setBlock r c χ i = χ i := by simp [setBlock, h]

/-- A round whose challenge is trivial (`Unit`): the `M0` round and the final-message round. -/
def unitRound (M : Type) [DecidableEq M] [Finite M] (I : OracleInterface M) : Round where
  Message := M
  Challenge := Unit
  interface := I
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance

section Rounds

variable (Φ K colRound β) [Fintype K] [DecidableEq K] [SampleableType K]
  [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

/-- Column round `r`: the round-`r` columns as one oracle message, then block `r`. -/
noncomputable def colRoundR (I : (r : ℕ) → OracleInterface (Cols colRound β r)) (r : ℕ) : Round where
  Message := Cols colRound β r
  Challenge := Block Φ K r
  interface := I r
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance

/-- Column rounds `r, r+1, …, r+k-1`, then the final-message round. -/
noncomputable def colRounds (I : (r : ℕ) → OracleInterface (Cols colRound β r)) (fin : Round) :
    ℕ → ℕ → List Round
  | _, 0 => [fin]
  | r, k + 1 => colRoundR Φ K β colRound I r :: colRounds I fin (r + 1) k

/-- **The staged-RAP protocol's rounds**: `[M0 | Unit] :: [Cols 0 | Block 0] :: … :: [Mfin | Unit]`. -/
noncomputable def rapRounds (M0 Mfin : Type) [DecidableEq M0] [Finite M0] [DecidableEq Mfin] [Finite Mfin]
    (I0 : OracleInterface M0) (I : (r : ℕ) → OracleInterface (Cols colRound β r))
    (Ifin : OracleInterface Mfin) (nb : ℕ) : List Round :=
  unitRound M0 I0 :: colRounds Φ K β colRound I (unitRound Mfin Ifin) 0 nb

theorem colRounds_length (I : (r : ℕ) → OracleInterface (Cols colRound β r)) (fin : Round) :
    ∀ r k, (colRounds Φ K β colRound I fin r k).length = k + 1
  | _, 0 => rfl
  | r, k + 1 => by simp [colRounds, colRounds_length I fin (r + 1) k]

end Rounds

end NockvmE2E.Rap
