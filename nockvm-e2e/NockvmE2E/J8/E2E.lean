/-
**the e2e theorem for every J-8-shaped interface instance.**
`rap_fri_merkle_sound_deep_J` and `_numbers` (`≤ 2^-82`): `rap_fri_merkle_sound_deep(_numbers)` (`Merkle/E2E`)
with its RAP-side arguments (`P`, `A`, `R0`, `Rest`, `RestV`, `hR0`, `hlink`, `hnb`, `hRest`, `errOld`, `herr0`,
`htoPoly`, `e`'s type, and the caps `hns`, `hD`, `hH`, `hnq`, `hm`, `herrOld`, `hnb30`) discharged from
`J : RapAirJ B K` (+ `PubRead J`, proposed interface fields); the protocol/adversary arguments stay variables.
-/
import NockvmE2E.J8.Deep
import NockvmE2E.Merkle.E2E

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec
open MerkleTreeMultiExtractability
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.RapFriQ

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort
  NockvmE2E.FriPort.Batched NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
open NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld SoundnessCoupling BadBound
open NockvmE2E.J8

/-- The constant round error `2^-155` (J-8's `epsJ8X_lt_155_census32` through `J.eps`). -/
noncomputable def errJ : ℕ → ℝ≥0∞ := fun _ => ENNReal.ofReal (1 / 2 ^ 155)

theorem errJ_le : ∀ r, errJ r ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  intro r
  unfold errJ
  rw [ENNReal.ofReal, ENNReal.coe_le_coe, Real.toNNReal_le_iff_le_coe]
  push_cast
  norm_num

section Gen

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable [SampleableType F] [Inhabited F]
variable (J : RapAirJ B F) [NeZero J.r] (pr : PubRead J)
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ) (δ : ℝ≥0)
variable (hNH : friBound s d ≤ J.H.card) (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card)


variable {m : ℕ} (e : Fin (m + 1) ≃ (J.ι0 × Fin J.r) ⊕ Fin ((deepParamsJ J pr ω δ (friBound s d) hNH hpd)).nq)
variable [DecidableEq (((deepParamsJ J pr ω δ (friBound s d) hNH hpd)).statement (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd)).M0] [Finite (((deepParamsJ J pr ω δ (friBound s d) hNH hpd)).statement (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd)).M0]
  [DecidableEq (friPlan (ω := ω) (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e).Mfin] [Finite (friPlan (ω := ω) (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e).Mfin]
  (I0 : OracleInterface (((deepParamsJ J pr ω δ (friBound s d) hNH hpd)).statement (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd)).M0)
  (I : (r : ℕ) → OracleInterface (Cols ((deepParamsJ J pr ω δ (friBound s d) hNH hpd)).colRoundX (Fin (2 ^ n) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ω) (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e).Mfin)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] [SampleableType Dg] [Inhabited Dg] (enc : F ↪ Dg)
  (md : PointMaskData ((deepParamsJ J pr ω δ (friBound s d) hNH hpd)).colRoundX (Fin (2 ^ n)) B Dg) (L : Fri.FriLeaves (ω := ω) s)
variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
variable {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]


/-- **`rap_fri_merkle_sound_deep` for every interface instance `J`** (all RAP-side arguments discharged from
`J`; `hω` says the LDE domain lies in the base field, `hNH`/`hpd` the degree facts on `J.H` and the fixed columns). -/
theorem rap_fri_merkle_sound_deep_J (hω : ∀ i, domEmb ω i ∈ Set.range (algebraMap B F))
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S))))) Dg)
    (guards : GuardSchedule (Statement × Salt) PUnit
      (compiledRoundsK Dg (OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S))))) ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S)))))
    (θ : ℝ)
    (hN : friBound s d + 1 ≤ 2 ^ n)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (friBound s d + 1) : Set (Fin (2 ^ n) → F)))
    (ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    (A' : SuccinctAdversaryK Dg (OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S))))) Query Statement Salt W ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S))))
    (Q_FS Q_H V Pn : ℕ)
    (hFS : FsBound (Q := Query) (∅ : (ofFn (KC Dg (OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S))))) Statement Salt ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S))))).QueryCache)
      Q_FS (verifiedFS guards A'))
    (hH : IsQueryBoundP A' (@isHashQuery Query Dg _ (KC Dg (OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S))))) Statement Salt ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S))))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S)))).length) (op : OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S)))))
      (logs : Fin (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S)))).length → MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount (mkClaims (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S)))) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S))))).nodeBudget tag ≤ Pn) :
    Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK guards
        (merkleCheck (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S)))) model id)
        (cLocal (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l G Dg enc md L hdom (OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S))))) id) A') ∅}[
      match j.1.1 with | none => False | some (z, _, _) => z.1 ∉ {_x : Statement | ((R0J J pr ω δ (friBound s d))).Holds}] ≤
    rapFriEps (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l errJ θ δ ε Q_FS +
      (multiCheckpointROMErrorNumerator (((merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S)))).length * (Q_FS + 1)) * Pn)
        ((merkleSkels ((msC (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l Dg enc md L (S := S)))).length * (Q_FS + 1)) V Q_H : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹ := by
  have hnbJ : (deepParamsJ J pr ω δ (friBound s d) hNH hpd).R + 1 < 4 := by show 2 + 1 < 4; norm_num
  have h := rap_fri_merkle_sound_deep (deepParamsJ J pr ω δ (friBound s d) hNH hpd) (airJ J pr ω δ (friBound s d) hNH hpd) (R0J J pr ω δ (friBound s d)) (RestJ J pr ω δ (friBound s d) hNH hpd) (RestVJ J pr ω δ (friBound s d) hNH hpd) e I0 I Ifin 4 s d l G Dg enc md L hdom model guards
    (rapInput_rapJ _ _) (hlink_J J pr ω δ (friBound s d) hNH hpd) hnbJ
    (hRest_J J pr ω δ (friBound s d) hNH hpd) errJ
    (fun _ r => roundBound_rapJ_le _ _ _ r) θ δ hN hδ
    (tp_eq ω hω hN hδ) ε hε A' Q_FS Q_H V Pn hFS hH hterm hconfig
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
  · exact hb
  · exact hb

end Gen


section Num

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable [SampleableType F] [Inhabited F]
variable (J : RapAirJ B F) [NeZero J.r] (pr : PubRead J)
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (hNH : friBound s d ≤ J.H.card) (hpd : ∀ j c, J.pre j = some c → c.natDegree ≤ J.H.card)


variable {m : ℕ} (e : Fin (m + 1) ≃ (J.ι0 × Fin J.r) ⊕ Fin ((deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).nq)
variable [DecidableEq (((deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).statement (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).M0] [Finite (((deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).statement (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).M0]
  [DecidableEq (friPlan (ω := ω) (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e).Mfin] [Finite (friPlan (ω := ω) (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e).Mfin]
  (I0 : OracleInterface (((deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).statement (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).M0)
  (I : (r : ℕ) → OracleInterface (Cols ((deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).colRoundX (Fin (2 ^ n) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ω) (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e).Mfin)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s 170).Challenge j)]
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] [SampleableType Dg] [Inhabited Dg] (enc : F ↪ Dg)
  (md : PointMaskData ((deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).colRoundX (Fin (2 ^ n)) B Dg) (L : Fri.FriLeaves (ω := ω) s)
variable {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]


open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers in
/-- **The e2e figure for every interface instance: `≤ 2^-82`.** `rap_fri_merkle_sound_deep_numbers` at `J`:
the RAP-side arguments and the caps `hns hD hH hnq hm herrOld hnb30` are discharged from `J` (`J.cap_*`,
`J.eps`); what remains is the field/FRI shape (`hs hrate hn hF hω hNH hpd`), the digest size and the
protocol/adversary arguments. -/
theorem rap_fri_merkle_sound_deep_J_numbers (hω : ∀ i, domEmb ω i ∈ Set.range (algebraMap B F))
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F))))) Dg)
    (guards : GuardSchedule (Statement × Salt) PUnit
      (compiledRoundsK Dg (OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F))))) ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F)))))
    (hs : ∀ i, s i = 1) (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) (hn : n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F)
    (hDg : goldilocks ^ 4 ≤ Nat.card Dg)
    (A' : SuccinctAdversaryK Dg (OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F))))) Query Statement Salt W ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F))))
    (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hFS : FsBound (Q := Query) (∅ : (ofFn (KC Dg (OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F))))) Statement Salt ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F))))).QueryCache)
      Q_FS (verifiedFS guards A'))
    (hHq : IsQueryBoundP A' (@isHashQuery Query Dg _ (KC Dg (OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F))))) Statement Salt ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F))))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F)))).length) (op : OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F)))))
      (logs : Fin (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F)))).length → MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount (mkClaims (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F)))) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F))))).nodeBudget tag ≤ Pn) :
    Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK guards
        (merkleCheck (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F)))) model id)
        (cLocal (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 (univariatePowersGenerator F m) Dg enc md L
          (by have : 2 ^ (∑ j, (s j).val) * d.val ≤ 64 * (2 ^ (∑ j, (s j).val) * d.val) := by omega
              exact this.trans hrate)
          (OpenAll Dg (merkleSkels ((msC (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d 170 Dg enc md L (S := F))))) id) A') ∅}[
      match j.1.1 with | none => False | some (z, _, _) => z.1 ∉ {_x : Statement | ((R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d))).Holds}] ≤
    (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  have hr : 64 * friBound s d ≤ 2 ^ n := hrate
  have hN1 : 0 < friBound s d := by unfold friBound; positivity
  have hN : friBound s d + 1 ≤ 2 ^ n := by omega
  have hδ : (31 / 64 : ℝ≥0) ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (friBound s d + 1) : Set (Fin (2 ^ n) → F)) :=
    relUDR_rs_ge _ _ (by rw [Fintype.card_fin]; omega)
  have hm : m + 1 ≤ 2 ^ 12 := by
    have h1 := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at h1
    have h2 := J.cap_m
    have h3 : (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd).nq = 3 * (J.d - 1) := rfl
    rw [h3] at h1
    omega
  have hD : ((deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).D.card ≤ 2 ^ 32 := by
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by norm_num) hn
  have hH : ((deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).H.card ≤ 2 ^ 32 := by
    show (HK J).card ≤ _
    rw [card_HK]
    exact J.cap_H.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hnq : ((deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd)).nq + 1 ≤ 2 ^ 8 := by
    have := J.cap_d
    show 3 * (J.d - 1) + 1 ≤ _
    omega
  have hnbJ : (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd).R + 1 < 4 := by
    show 2 + 1 < 4; norm_num
  have h := rap_fri_merkle_sound_deep_numbers (deepParamsJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (airJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (R0J J pr ω (31 / 64 : ℝ≥0) (friBound s d)) (RestJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) (RestVJ J pr ω (31 / 64 : ℝ≥0) (friBound s d) hNH hpd) e I0 I Ifin 4 s d Dg enc md L model guards
    (rapInput_rapJ _ _) (hlink_J J pr ω (31 / 64) (friBound s d) hNH hpd) hnbJ
    (hRest_J J pr ω (31 / 64) (friBound s d) hNH hpd) errJ
    (fun _ r => roundBound_rapJ_le _ _ _ r) hs hrate hn hF hm (tp_eq ω hω hN hδ) J.cap_ns hD hH hnq errJ_le
    (by norm_num) hDg A' Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
  · exact hb
  · exact hb

end Num

end NockvmE2E.Merkle.RapFriQ
