/-
: `friMerklePcs`, the `PcsBase` instance of batched FRI on RS
codes with Merkle-committed column blocks and FRI folds. Its `sound` field is `rap_fri_merkle_sound_deep`
(Merkle/E2E.lean:134), repackaged (not re-proved); `friMerkle_numbers` is `rap_fri_merkle_sound_deep_numbers`
(`E2E.lean:213`) restated as `ε ≤ 2^-82`.
-/
import NockvmE2E.Succ.PcsBase
import NockvmE2E.Merkle.E2E

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec
open MerkleTreeMultiExtractability
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain ProximityGap CoreDefinitions
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

namespace NockvmE2E.Succ.Pcs

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort
  NockvmE2E.FriPort.Batched NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
open NockvmE2E.Merkle NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good NockvmE2E.Merkle.SoundnessWorld
  NockvmE2E.Merkle.SoundnessCoupling NockvmE2E.Merkle.BadBound
open NockvmE2E.Merkle.RapFriQ NockvmE2E.Succ.Numbers

variable {Φ : CoinFrame} {F B : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
  [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B] [SampleableType F] [Inhabited F]

/-- **FRI + RS + Merkle parameters** (the FRI/Merkle binders of `rap_fri_merkle_sound_deep`, with the instances
they carry). -/
structure FriParams (D : DeepRap Φ F B) where
  k : ℕ
  ω : SmoothCosetFftDomain D.n F
  s : Fin (k + 1) → ℕ+
  d : ℕ+
  l : ℕ
  θ : ℝ
  δ : ℝ≥0
  ε : ℝ≥0
  S : Type
  [fS : Fintype S]
  [nS : Nonempty S]
  [sS : SampleableType S]
  G : CoreDefinitions.Generator S (Fin (D.m + 1)) F
  Dg : Type
  [fDg : Finite Dg]
  [dDg : DecidableEq Dg]
  [sDg : SampleableType Dg]
  [iDg : Inhabited Dg]
  enc : F ↪ Dg
  md : PointMaskData D.P.colRoundX (Fin (2 ^ D.n)) B Dg
  L : NockvmE2E.Merkle.Fri.FriLeaves (ω := ω) s
  [dM0 : DecidableEq (D.P.statement D.R0 D.Rest).M0]
  [fM0 : Finite (D.P.statement D.R0 D.Rest).M0]
  [dMf : DecidableEq (friPlan (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e).Mfin]
  [fMf : Finite (friPlan (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e).Mfin]
  [sCh : ∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
  I0 : OracleInterface (D.P.statement D.R0 D.Rest).M0
  I : (r : ℕ) → OracleInterface (Cols D.P.colRoundX (Fin (2 ^ D.n) → B) r)
  Ifin : OracleInterface (friPlan (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e).Mfin
  /-- the FRI domain is large enough for the degree bound (a proof argument of `cLocal`) -/
  hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ D.n

namespace FriParams

attribute [instance] fS nS sS fDg dDg sDg iDg

/-- Bring the instance fields of `pp` into scope. -/
local macro "friInsts% " pp:term " in " b:term : term =>
  `(letI := ($pp).fS; letI := ($pp).nS; letI := ($pp).sS; letI := ($pp).fDg; letI := ($pp).dDg
    letI := ($pp).sDg; letI := ($pp).iDg; letI := ($pp).dM0; letI := ($pp).fM0; letI := ($pp).dMf
    letI := ($pp).fMf; letI := ($pp).sCh; $b)

variable {D : DeepRap Φ F B}

/-- The side conditions: `hN hδ htoPoly hε` of `rap_fri_merkle_sound_deep`. -/
def Ok (pp : FriParams D) : Prop :=
  (friBound pp.s pp.d + 1 ≤ 2 ^ D.n) ∧
  (pp.δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb pp.ω) (friBound pp.s pp.d + 1) : Set (Fin (2 ^ D.n) → F))) ∧
  (D.P.toPoly = udDecodeB pp.ω pp.δ (friBound pp.s pp.d)) ∧
  (ProximityGap.caError pp.G
      (ReedSolomon.code (pp.ω : Fin (2 ^ D.n) ↪ F) (2 ^ (∑ i, (pp.s i).1) * pp.d)).carrier pp.δ pp.δ ≤ pp.ε)

/-- The combined Merkle mask of the compiled protocol. -/
noncomputable def ms (pp : FriParams D) : MRounds pp.Dg :=
  friInsts% pp in
  msC (ω := pp.ω) D.P D.A D.R0 D.Rest D.RestV D.e pp.I0 pp.I pp.Ifin D.nb pp.s pp.d pp.l pp.Dg pp.enc pp.md pp.L
    (S := pp.S)

/-- **Adversaries of the compiled game**: the Merkle node-query model, the guard schedule and a
`SuccinctAdversaryK`, over a free query type / statement / salt / witness type. -/
structure FriAdv (pp : FriParams D) where
  Query : Type
  [dQ : DecidableEq Query]
  Statement : Type
  Salt : Type
  W : Type
  [dSt : DecidableEq Statement]
  [dSa : DecidableEq Salt]
  model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels pp.ms)) pp.Dg
  guards : GuardSchedule (Statement × Salt) PUnit (compiledRoundsK pp.Dg (OpenAll pp.Dg (merkleSkels pp.ms)) pp.ms)
  adv : SuccinctAdversaryK pp.Dg (OpenAll pp.Dg (merkleSkels pp.ms)) Query Statement Salt W pp.ms

attribute [instance] FriAdv.dQ FriAdv.dSt FriAdv.dSa

variable {pp : FriParams D}

/-- The adversary's budget: `hFS hH hterm hconfig` of `rap_fri_merkle_sound_deep`. -/
def Budget (A : FriAdv pp) (Q_FS Q_H V Pn : ℕ) : Prop :=
  FsBound (Q := A.Query)
    (∅ : (ofFn (KC pp.Dg (OpenAll pp.Dg (merkleSkels pp.ms)) A.Statement A.Salt pp.ms)).QueryCache)
    Q_FS (verifiedFS A.guards A.adv) ∧
  IsQueryBoundP A.adv
    (@isHashQuery A.Query pp.Dg _ (KC pp.Dg (OpenAll pp.Dg (merkleSkels pp.ms)) A.Statement A.Salt pp.ms)) Q_H ∧
  (∀ (roots : List pp.Dg) (h : roots.length = (merkleSkels pp.ms).length)
      (op : OpenAll pp.Dg (merkleSkels pp.ms))
      (logs : Fin (merkleSkels pp.ms).length → MerkleTreeExtractor.QueryLog A.Query pp.Dg),
      claimsQueryCount (mkClaims (merkleSkels pp.ms) roots h op logs) ≤ V) ∧
  (∀ tag, (mconfig (merkleSkels pp.ms)).nodeBudget tag ≤ Pn)

/-- `Pr[accepted ∧ ¬ Holds]` in the hash-compiled game. -/
noncomputable def bad (A : FriAdv pp) : ℝ≥0∞ :=
  friInsts% pp in
  Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK A.guards
        (merkleCheck (merkleSkels pp.ms) A.model id)
        (cLocal D.P D.A D.R0 D.Rest D.RestV D.e pp.I0 pp.I pp.Ifin D.nb pp.s pp.d pp.l pp.G pp.Dg pp.enc pp.md pp.L
          pp.hdom (OpenAll pp.Dg (merkleSkels pp.ms)) id) A.adv) ∅}[
      match j.1.1 with | none => False | some (z, _, _) => z.1 ∉ {_x : A.Statement | D.R0.Holds}]

/-- The error: `rapFriEps` at `Q_FS` plus the multi-checkpoint Merkle ROM term over `|Dg|`. -/
noncomputable def eps (pp : FriParams D) (Q_FS Q_H V Pn : ℕ) : ℝ≥0∞ :=
  friInsts% pp in
  rapFriEps D.P D.A D.R0 D.Rest D.RestV D.e pp.I0 pp.I pp.Ifin D.nb pp.s pp.d pp.l D.errOld pp.θ pp.δ pp.ε Q_FS +
    (multiCheckpointROMErrorNumerator (((merkleSkels pp.ms).length * (Q_FS + 1)) * Pn)
      ((merkleSkels pp.ms).length * (Q_FS + 1)) V Q_H : ℝ≥0∞) * (Nat.card pp.Dg : ℝ≥0∞)⁻¹

end FriParams

/-- **`friMerklePcs`**: batched FRI on RS codes with Merkle-committed column blocks and FRI folds. `sound` is
`rap_fri_merkle_sound_deep`, by `exact` (not re-proved). -/
noncomputable instance friMerklePcs : PcsBase Φ F B where
  Params := FriParams
  ParamsOk _ pp := FriParams.Ok pp
  Adv _ pp := FriParams.FriAdv pp
  Budget _ pp A := FriParams.Budget A
  bad _ pp A := FriParams.bad A
  ε _ pp := FriParams.eps pp
  sound D pp hok A Q_FS Q_H V Pn hb := by
    obtain ⟨hN, hδ, htoPoly, hε⟩ := hok
    obtain ⟨hFS, hH, hterm, hconfig⟩ := hb
    cases pp
    rename_i k ω s d l θ δ ε S fS nS sS G Dg fDg dDg sDg iDg enc md L dM0 fM0 dMf fMf sCh I0 I Ifin hdom
    have h := rap_fri_merkle_sound_deep (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e I0 I Ifin D.nb s d l
      G Dg enc md L hdom A.model A.guards D.hR0 D.hlink D.hnb D.hRest D.errOld D.herr0
      θ δ hN hδ htoPoly ε hε A.adv Q_FS Q_H V Pn hFS hH hterm hconfig
    unfold FriParams.bad
    refine le_trans (prEvent_mono _ _ _ ?_) h
    rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
    · exact hb
    · exact hb

namespace FriParams

variable {D : DeepRap Φ F B}

/-- **Bad-event unfolding**: `friMerklePcs.bad` is literally the hash-compiled `Pr[accepted ∧ ¬Holds]` of
`rap_fri_merkle_sound_deep`. -/
theorem bad_eq (pp : FriParams D) (A : FriAdv pp) :
    (PcsBase.bad (self := friMerklePcs) D pp A) = FriParams.bad A := rfl

/-- `friMerklePcs.ε` is the right-hand side of `rap_fri_merkle_sound_deep`. -/
theorem eps_eq (pp : FriParams D) (Q_FS Q_H V Pn : ℕ) :
    (PcsBase.ε (self := friMerklePcs) D pp Q_FS Q_H V Pn) = FriParams.eps pp Q_FS Q_H V Pn := rfl

/-- **The J-8 numbers** (`rap_fri_merkle_sound_deep_numbers`): `l = 170`, `θ = δ = 31/64`, powers generator of
degree `m` on `S = F`, `ε = m·2^n/|F|`. -/
noncomputable def numbers (D : DeepRap Φ F B) {k : ℕ} (ω : SmoothCosetFftDomain D.n F)
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (Dg : Type) [Finite Dg] [DecidableEq Dg] [SampleableType Dg] [Inhabited Dg]
    (enc : F ↪ Dg) (md : PointMaskData D.P.colRoundX (Fin (2 ^ D.n)) B Dg)
    (L : NockvmE2E.Merkle.Fri.FriLeaves (ω := ω) s)
    [DecidableEq (D.P.statement D.R0 D.Rest).M0] [Finite (D.P.statement D.R0 D.Rest).M0]
    [DecidableEq (friPlan (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e).Mfin]
    [Finite (friPlan (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e).Mfin]
    [∀ j, SampleableType ((pSpec k (ω := ω) s 170).Challenge j)]
    (I0 : OracleInterface (D.P.statement D.R0 D.Rest).M0)
    (I : (r : ℕ) → OracleInterface (Cols D.P.colRoundX (Fin (2 ^ D.n) → B) r))
    (Ifin : OracleInterface (friPlan (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e).Mfin)
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ D.n) : FriParams D where
  k := k
  ω := ω
  s := s
  d := d
  l := 170
  θ := 31 / 64
  δ := 31 / 64
  ε := ((D.m * ((2 ^ D.n : ℝ≥0) / Fintype.card F) : ℝ≥0))
  S := F
  G := univariatePowersGenerator F D.m
  Dg := Dg
  enc := enc
  md := md
  L := L
  I0 := I0
  I := I
  Ifin := Ifin
  hdom := hdom

end FriParams

open FriParams in
/-- **The e2e figure, through `PcsBase`**: with the J-8 numbers (`FriParams.numbers`) the compiled game's bad
event has probability `≤ 2^-82`. This is `rap_fri_merkle_sound_deep_numbers` (`E2E.lean:213`) by `exact`. -/
theorem friMerkle_numbers (D : DeepRap Φ F B) {k : ℕ} (ω : SmoothCosetFftDomain D.n F)
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (Dg : Type) [Finite Dg] [DecidableEq Dg] [SampleableType Dg] [Inhabited Dg]
    (enc : F ↪ Dg) (md : PointMaskData D.P.colRoundX (Fin (2 ^ D.n)) B Dg)
    (L : NockvmE2E.Merkle.Fri.FriLeaves (ω := ω) s)
    [DecidableEq (D.P.statement D.R0 D.Rest).M0] [Finite (D.P.statement D.R0 D.Rest).M0]
    [DecidableEq (friPlan (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e).Mfin]
    [Finite (friPlan (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e).Mfin]
    [∀ j, SampleableType ((pSpec k (ω := ω) s 170).Challenge j)]
    (I0 : OracleInterface (D.P.statement D.R0 D.Rest).M0)
    (I : (r : ℕ) → OracleInterface (Cols D.P.colRoundX (Fin (2 ^ D.n) → B) r))
    (Ifin : OracleInterface (friPlan (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e).Mfin)
    (hs : ∀ i, s i = 1) (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ D.n) (hn : D.n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F) (hm : D.m + 1 ≤ 2 ^ 12)
    (htoPoly : D.P.toPoly = udDecodeB ω (31 / 64) (friBound s d))
    (hns : D.P.ns ≤ 2 ^ 20) (hD : D.P.D.card ≤ 2 ^ 32) (hH : D.P.H.card ≤ 2 ^ 32) (hnq : D.P.nq + 1 ≤ 2 ^ 8)
    (herrOld : ∀ r, D.errOld r ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞)) (hnb30 : D.nb ≤ 30)
    (hDg : goldilocks ^ 4 ≤ Nat.card Dg)
    (pp : FriParams D)
    (hpp : pp = FriParams.numbers D ω s d Dg enc md L I0 I Ifin
      (by have : 2 ^ (∑ j, (s j).val) * d.val ≤ 64 * (2 ^ (∑ j, (s j).val) * d.val) := by omega
          exact this.trans hrate))
    (A : FriAdv pp) (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hb : FriParams.Budget A Q_FS Q_H V Pn) :
    FriParams.bad A ≤ (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  subst hpp
  obtain ⟨hFS, hHq, hterm, hconfig⟩ := hb
  unfold FriParams.bad
  have h := rap_fri_merkle_sound_deep_numbers (ω := ω) D.P D.A D.R0 D.Rest D.RestV D.e I0 I Ifin D.nb s d Dg enc md L
    A.model A.guards D.hR0 D.hlink D.hnb D.hRest D.errOld D.herr0 hs hrate hn hF hm htoPoly hns hD hH hnq
    herrOld hnb30 hDg A.adv Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
  · exact hb
  · exact hb

end NockvmE2E.Succ.Pcs

#print axioms NockvmE2E.Succ.Pcs.friMerklePcs
#print axioms NockvmE2E.Succ.Pcs.friMerkle_numbers
#print axioms NockvmE2E.Succ.Pcs.FriParams.bad_eq
#print axioms NockvmE2E.Succ.Pcs.FriParams.eps_eq
