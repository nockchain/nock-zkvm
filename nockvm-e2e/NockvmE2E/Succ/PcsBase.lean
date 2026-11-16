/-
the base class `PcsBase` of
"compiled soundness" for a polynomial commitment scheme, over the DEEP claim interface.

* `DeepRap`: the VM/RAP/DEEP side of one argument: exactly the explicit binders of `rap_fri_merkle_sound_deep`
  that mention neither FRI, Merkle nor the adversary (`P A R0 Rest RestV e nb hR0 hlink hnb hRest errOld herr0`).
* `PcsBase`: for every DEEP-RAP input `D` and parameters `pp` with `ParamsOk`, every adversary `A` inside the
  instance's budget has `bad D pp A ≤ ε D pp Q`, where `bad` is the probability, in the instance's random-oracle
  game, of "accepted ∧ ¬ R0.Holds". The game is NOT a field: `bad` is the instance's own `Pr{…}` expression
  (a data field), and every instance proves `bad = Pr{…}` by `rfl` (`FriParams.bad_eq`), so `bad := 0` cannot
  pass review; the instances are the vacuity witnesses (`PcsFri`, `PcsIop`).
-/
import NockvmE2E.Succ.FriDeep

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open scoped NNReal ENNReal

namespace NockvmE2E.Succ.Pcs

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep

section Base

variable (Φ : CoinFrame) (F B : Type) [NonBinaryField F] [Fintype F] [DecidableEq F]
  [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B] [SampleableType F] [Inhabited F]

/-- **The VM/RAP/DEEP side of one argument.** The obligations (`hR0 hlink hnb hRest herr0`) are the ones the J-8
chain discharges (`exec_e2e_J8`). -/
structure DeepRap where
  ι : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  colRound : ι → ℕ
  n : ℕ
  P : DeepParams Φ F ι (Fin (2 ^ n) → B) colRound
  r : ℕ
  [hr : NeZero r]
  A : AirShape P r
  R0 : RapStatement Φ F ι (Fin (2 ^ n) → B) colRound
  Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ F → Prop
  RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ F → Prop
  m : ℕ
  e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq
  nb : ℕ
  hR0 : RapInput R0 nb
  hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
    (∀ i, ∀ x ∈ P.H, Polynomial.eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ
  hnb : P.R + 1 < nb
  hRest : ∀ m0 (tr : DeepTr P) fin χ, RestV m0 fin χ →
    SatClaims (deepOI P) tr (deepClaims P A R0 χ fin) → Rest m0 tr fin.1 χ
  errOld : ℕ → ℝ≥0∞
  herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r

attribute [instance] DeepRap.fι DeepRap.dι DeepRap.hr

/-- **`PcsBase`: compiled soundness of a PCS over the DEEP claim interface**.
`Q = (Q_FS, Q_H, V, Pn)`: fresh Fiat–Shamir keys, hash queries, opened-claims count, node budget. -/
class PcsBase where
  /-- Instance parameters (FRI: `k s d l θ δ ε |Dg| enc md L G ω` and the instances they carry; lattice: its own). -/
  Params : DeepRap Φ F B → Type 1
  /-- The side conditions on the parameters (FRI: `hN hδ htoPoly hε hdom`). -/
  ParamsOk : (D : DeepRap Φ F B) → Params D → Prop
  /-- Adversaries of the compiled protocol's random-oracle game. -/
  Adv : (D : DeepRap Φ F B) → Params D → Type 1
  /-- The adversary's budget. -/
  Budget : (D : DeepRap Φ F B) → (pp : Params D) → Adv D pp → ℕ → ℕ → ℕ → ℕ → Prop
  /-- `Pr[accepted ∧ ¬ D.R0.Holds]` in the instance's game. -/
  bad : (D : DeepRap Φ F B) → (pp : Params D) → Adv D pp → ℝ≥0∞
  /-- The soundness error. -/
  ε : (D : DeepRap Φ F B) → Params D → ℕ → ℕ → ℕ → ℕ → ℝ≥0∞
  /-- **Compiled soundness.** -/
  sound : ∀ (D : DeepRap Φ F B) (pp : Params D), ParamsOk D pp → ∀ (A : Adv D pp) Q_FS Q_H V Pn,
    Budget D pp A Q_FS Q_H V Pn → bad D pp A ≤ ε D pp Q_FS Q_H V Pn

end Base

end NockvmE2E.Succ.Pcs

#print axioms NockvmE2E.Succ.Pcs.PcsBase.sound
