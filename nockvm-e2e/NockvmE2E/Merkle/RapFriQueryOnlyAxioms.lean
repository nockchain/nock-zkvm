/-
Axiom guard for `Merkle/RapFriQueryOnly.lean`, and the hclear-shape check: `rapFri_hclear_deep`
is fed to the `hclear` argument of `merkle_singleSalt_soundness` (all other arguments are variables).
-/
import NockvmE2E.Merkle.RapFriQueryOnly
import NockvmE2E.Merkle.Soundness

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

section HclearShape

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable [SampleableType F] [Inhabited F]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ F ι (Fin (2 ^ n) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ F ι (Fin (2 ^ n) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ F → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ F → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ω) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ω) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ n) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ω) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] [SampleableType Dg] [Inhabited Dg] (enc : F ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ n)) B Dg) (L : Fri.FriLeaves (ω := ω) s)
variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
variable (Op : Type) [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]

/-- **The shape check.** `rapFri_hclear_deep` is exactly the `hclear` argument of
`merkle_singleSalt_soundness` at `ms := msC`, `accepts := cAcceptB`, `localAccepts := cLocal`,
`L := {_ | R0.Holds}`, `εFS := rapFriEps …`; every other argument is a variable. -/
theorem hclear_shape_check (hpos : 0 < (merkleSkels (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L
      (S := S))).length)
    (decode : Op → OpenAll Dg (merkleSkels (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S))))
    (model : MerkleTreeExtractability.NodeQueryModel Query
      (MAddress (merkleSkels (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)))) Dg)
    (guards : GuardSchedule (Statement × Salt) PUnit
      (compiledRoundsK Dg Op (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S))))
    (hR0 : RapInput R0 nb)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, Polynomial.eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < nb)
    (hRest : ∀ m0 (tr : DeepTr P) fin χ, RestV m0 fin χ →
      SatClaims (deepOI P) tr (deepClaims P A R0 χ fin) → Rest m0 tr fin.1 χ)
    (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r)
    (θ : ℝ) (δ : ℝ≥0)
    (hN : friBound s d + 1 ≤ 2 ^ n)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (friBound s d + 1) : Set (Fin (2 ^ n) → F)))
    (htoPoly : P.toPoly = udDecodeB ω δ (friBound s d))
    (ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    (A' : SuccinctAdversaryK Dg Op Query Statement Salt W
      (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)))
    (Q_FS Q_H V Pn : ℕ)
    (hFS : FsBound (Q := Query) (∅ : (ofFn (KC Dg Op Statement Salt
        (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)))).QueryCache) Q_FS
      (verifiedFS guards A'))
    (hH : IsQueryBoundP A' (@isHashQuery Query Dg _ (KC Dg Op Statement Salt
      (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels
        (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S))).length) (op : Op)
      (logs : Fin (merkleSkels (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S))).length →
        MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount (mkClaims (merkleSkels (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L
        (S := S))) roots h (decode op) logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels
      (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)))).nodeBudget tag ≤ Pn) :
    Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK guards
        (merkleCheck (merkleSkels (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S))) model decode)
        (cLocal P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op decode) A') ∅}[
      match j.1.1 with | none => False | some (z, _, _) => z.1 ∉ {_x : Statement | R0.Holds}] ≤
    rapFriEps P A R0 Rest RestV e I0 I Ifin nb s d l errOld θ δ ε Q_FS +
      (multiCheckpointROMErrorNumerator
        (((merkleSkels (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S))).length *
          (Q_FS + 1)) * Pn)
        ((merkleSkels (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S))).length *
          (Q_FS + 1)) V Q_H : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹ :=
  by
  have h := merkle_singleSalt_soundness (Statement := Statement) (Salt := Salt) (W := W)
    (msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)) hpos decode model guards
    (cAcceptB P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom)
    (cLocal P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op decode)
    (rapFri_queryOnly P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op decode)
    {_x : Statement | R0.Holds} (rapFriEps P A R0 Rest RestV e I0 I Ifin nb s d l errOld θ δ ε)
    (fun B Q hQ => by
      refine le_trans (prEvent_mono _ _ _ ?_)
        (rapFri_hclear_deep P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom Op hR0
          hlink hnb hRest errOld herr0 θ δ hN hδ htoPoly ε hε guards B Q hQ)
      rintro ⟨⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩, _⟩ hb
      · exact hb
      · exact hb)
    A' Q_FS Q_H V Pn hFS hH hterm hconfig
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
  · exact hb
  · exact hb

end HclearShape

end NockvmE2E.Merkle.RapFriQ

open NockvmE2E.Merkle.RapFriQ

#print axioms NockvmE2E.Merkle.Fri.queryBad_congr₂
#print axioms NockvmE2E.Merkle.Fri.queryBad_congr_of_rel₂
#print axioms NockvmE2E.Merkle.Fri.friAccepts'_congr_stmt
#print axioms PointMaskData
#print axioms perfectPointData
#print axioms CoversR
#print axioms finalOfBK_agree
#print axioms bmask
#print axioms msC
#print axioms baseRounds_msC
#print axioms pairedRoundsK_msC
#print axioms readSet
#print axioms cAcceptB
#print axioms combined_deep_congr
#print axioms CoversC
#print axioms xsC
#print axioms cLocal
#print axioms rapFri_queryOnly
#print axioms castPath_cons_congr
#print axioms castPath_append_right
#print axioms pairAccepts_cAcceptB_imp
#print axioms rapFriEps
#print axioms rapFri_hclear_deep
#print axioms hclear_shape_check
#print axioms Witness.wColEquiv
#print axioms Witness.wLeaf
#print axioms Witness.witnessMd
#print axioms Witness.witnessMd_get
