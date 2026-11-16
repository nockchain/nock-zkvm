/-
Merkle (B) e2e row 4: `rap_fri_merkle_sound_deep`, the hash-compiled
RAP + DEEP + batched FRI soundness (Merkle trees on the column blocks and the FRI folds), from
`merkle_singleSalt_soundness` with `hlocal := rapFri_queryOnly`, `hclear := rapFri_hclear_deep`.
-/
import NockvmE2E.Merkle.RapFriQueryOnlyAxioms
import NockvmE2E.Merkle.E2ENumbers

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
variable {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]


/-! ## 1. At least one merkle round -/

theorem merkleSkels_rapMerkleMask_length (md : RapP.RapMaskData colRound (β := Fin (2 ^ n) → B) B Dg)
    (Mfin : Type) [Finite Mfin] [DecidableEq Mfin] (I : (r : ℕ) → OracleInterface (Cols colRound (Fin (2 ^ n) → B) r))
    (Ifin : OracleInterface Mfin) :
    ∀ r k : ℕ, (merkleSkels (RapP.rapMerkleMask Φ F md Mfin I Ifin r k)).length = k
  | _, 0 => rfl
  | r, k + 1 => by
      simp only [RapP.rapMerkleMask, merkleSkels, List.length_cons]
      rw [merkleSkels_rapMerkleMask_length md Mfin I Ifin r.succ k]

local notation "MS" => msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L (S := S)

theorem hpos_msC (hnb : P.R + 1 < nb) : 0 < (merkleSkels (MS)).length := by
  unfold msC RapP.rapMask bmask
  rw [MA.merkleSkels_append]
  simp only [merkleSkels, List.length_append]
  rw [merkleSkels_rapMerkleMask_length]
  omega


theorem merkleSkels_friMerkleMask_length : ∀ i c (h : i + c = k),
    (merkleSkels (Fri.friMerkleMask s d l L Dg enc i c h)).length = c
  | _, 0, _ => rfl
  | i, c + 1, h => by
      simp only [Fri.friMerkleMask, merkleSkels, List.length_cons]
      rw [merkleSkels_friMerkleMask_length i.succ c (by omega)]

theorem length_msC : (merkleSkels (MS)).length = nb + k := by
  unfold msC RapP.rapMask bmask
  rw [MA.merkleSkels_append]
  simp only [merkleSkels, List.length_append, Fri.friMask]
  rw [merkleSkels_rapMerkleMask_length, merkleSkels_friMerkleMask_length]


/-- **`rapFriEps` is the right-hand side of `rap_fri_sound_deep`** (checked by `exact`: the two terms are
syntactically equal after unfolding the definition). -/
theorem rap_fri_sound_deep_eps {nb : ℕ} (hR0 : RapInput R0 nb)
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
    {Statement GlobalSalt W : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit
      (cRounds (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb
        (ω := ω) (S := S) s d l))
    (adversary : SingleSaltAdversary Statement GlobalSalt W
      (cRounds (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb
        (ω := ω) (S := S) s d l))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (cRounds (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb
          (ω := ω) (S := S) s d l) guards
        (cAccept (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb s d l m G
          (fun _ tr fin χ => deepStmt (ω := ω) P A R0 e tr fin χ) hdom) adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ ¬ R0.Holds] ≤
      rapFriEps P A R0 Rest RestV e I0 I Ifin nb s d l errOld θ δ ε Q :=
  rap_fri_sound_deep (ω := ω) P A R0 Rest RestV e I0 I Ifin s d l G hR0 hlink hnb hRest errOld herr0 hdom θ δ
    hN hδ htoPoly ε hε guards adversary Q queryBound

/-! ## 2. The theorem -/

/-- **e2e-ni: hash-compiled RAP + DEEP + batched FRI.** The columns of the trace blocks `r < nb` (the DEEP
quotient chunks are block `P.R + 1`) and the FRI folds are Merkle-committed; the combined mask is
`msC = rapMask ++ bmask`, `Op = OpenAll Dg (merkleSkels msC)`, `decode = id`. The bound is the right-hand side of
`rap_fri_sound_deep` at `Q_FS` (`rapFriEps`) plus the multi-checkpoint Merkle ROM term over `|Dg|`. -/
theorem rap_fri_merkle_sound_deep
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels (MS))) Dg)
    (guards : GuardSchedule (Statement × Salt) PUnit
      (compiledRoundsK Dg (OpenAll Dg (merkleSkels (MS))) (MS)))
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
    (A' : SuccinctAdversaryK Dg (OpenAll Dg (merkleSkels (MS))) Query Statement Salt W (MS))
    (Q_FS Q_H V Pn : ℕ)
    (hFS : FsBound (Q := Query) (∅ : (ofFn (KC Dg (OpenAll Dg (merkleSkels (MS))) Statement Salt (MS))).QueryCache)
      Q_FS (verifiedFS guards A'))
    (hH : IsQueryBoundP A' (@isHashQuery Query Dg _ (KC Dg (OpenAll Dg (merkleSkels (MS))) Statement Salt (MS))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels (MS)).length) (op : OpenAll Dg (merkleSkels (MS)))
      (logs : Fin (merkleSkels (MS)).length → MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount (mkClaims (merkleSkels (MS)) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (MS))).nodeBudget tag ≤ Pn) :
    Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK guards
        (merkleCheck (merkleSkels (MS)) model id)
        (cLocal P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom (OpenAll Dg (merkleSkels (MS))) id) A') ∅}[
      match j.1.1 with | none => False | some (z, _, _) => z.1 ∉ {_x : Statement | R0.Holds}] ≤
    rapFriEps P A R0 Rest RestV e I0 I Ifin nb s d l errOld θ δ ε Q_FS +
      (multiCheckpointROMErrorNumerator (((merkleSkels (MS)).length * (Q_FS + 1)) * Pn)
        ((merkleSkels (MS)).length * (Q_FS + 1)) V Q_H : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹ := by
  have h := hclear_shape_check P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc md L hdom (OpenAll Dg (merkleSkels (MS)))
    (hpos_msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc md L hnb) id model guards hR0 hlink hnb hRest errOld
    herr0 θ δ hN hδ htoPoly ε hε A' Q_FS Q_H V Pn hFS hH hterm hconfig
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
  · exact hb
  · exact hb

end HclearShape

/-! ## 3. The numbers -/

section Numbers

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
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s 170).Challenge j)]
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] [SampleableType Dg] [Inhabited Dg] (enc : F ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ n)) B Dg) (L : Fri.FriLeaves (ω := ω) s)
variable {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]



local notation "MS" => msC P A R0 Rest RestV e I0 I Ifin nb s d 170 Dg enc md L (S := F)

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers in
/-- **The e2e figure (hash-compiled RAP + DEEP + batched FRI): `≤ 2^-82`.** The parameters of
`rap_fri_sound_deep_numbers` (`l = 170`, `θ = δ = 31/64`, powers generator of degree `m`, `ε = m·2^n/|F|`) with
digests `|Dg| ≥ p^4`, `Q_FS, Q_H ≤ 2^64`, `V ≤ 2^32`. -/
theorem rap_fri_merkle_sound_deep_numbers
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels (MS))) Dg)
    (guards : GuardSchedule (Statement × Salt) PUnit
      (compiledRoundsK Dg (OpenAll Dg (merkleSkels (MS))) (MS)))
    (hR0 : RapInput R0 nb)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, Polynomial.eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < nb)
    (hRest : ∀ m0 (tr : DeepTr P) fin χ, RestV m0 fin χ →
      SatClaims (deepOI P) tr (deepClaims P A R0 χ fin) → Rest m0 tr fin.1 χ)
    (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r)
    (hs : ∀ i, s i = 1) (hrate : 64 * (2 ^ (∑ j, (s j).val) * d.val) ≤ 2 ^ n) (hn : n ≤ 32)
    (hF : goldilocks ^ 3 ≤ Fintype.card F) (hm : m + 1 ≤ 2 ^ 12)
    (htoPoly : P.toPoly = udDecodeB ω (31 / 64) (friBound s d))
    (hns : P.ns ≤ 2 ^ 20) (hD : P.D.card ≤ 2 ^ 32) (hH : P.H.card ≤ 2 ^ 32) (hnq : P.nq + 1 ≤ 2 ^ 8)
    (herrOld : ∀ r, errOld r ≤ (((2 ^ 150)⁻¹ : ℝ≥0) : ℝ≥0∞)) (hnb30 : nb ≤ 30)
    (hDg : goldilocks ^ 4 ≤ Nat.card Dg)
    (A' : SuccinctAdversaryK Dg (OpenAll Dg (merkleSkels (MS))) Query Statement Salt W (MS))
    (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hFS : FsBound (Q := Query) (∅ : (ofFn (KC Dg (OpenAll Dg (merkleSkels (MS))) Statement Salt (MS))).QueryCache)
      Q_FS (verifiedFS guards A'))
    (hHq : IsQueryBoundP A' (@isHashQuery Query Dg _ (KC Dg (OpenAll Dg (merkleSkels (MS))) Statement Salt (MS))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels (MS)).length) (op : OpenAll Dg (merkleSkels (MS)))
      (logs : Fin (merkleSkels (MS)).length → MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount (mkClaims (merkleSkels (MS)) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (MS))).nodeBudget tag ≤ Pn) :
    Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK guards
        (merkleCheck (merkleSkels (MS)) model id)
        (cLocal P A R0 Rest RestV e I0 I Ifin nb s d 170 (univariatePowersGenerator F m) Dg enc md L
          (by have : 2 ^ (∑ j, (s j).val) * d.val ≤ 64 * (2 ^ (∑ j, (s j).val) * d.val) := by omega
              exact this.trans hrate)
          (OpenAll Dg (merkleSkels (MS))) id) A') ∅}[
      match j.1.1 with | none => False | some (z, _, _) => z.1 ∉ {_x : Statement | R0.Holds}] ≤
    (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  have hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n :=
    (by omega : 2 ^ (∑ j, (s j).val) * d.val ≤ 64 * (2 ^ (∑ j, (s j).val) * d.val)).trans hrate
  have hr : 64 * friBound s d ≤ 2 ^ n := hrate
  have hN1 : 0 < friBound s d := by unfold friBound; positivity
  have hN : friBound s d + 1 ≤ 2 ^ n := by omega
  have hδ : (31 / 64 : ℝ≥0) ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (friBound s d + 1) : Set (Fin (2 ^ n) → F)) :=
    relUDR_rs_ge _ _ (by rw [Fintype.card_fin]; omega)
  have hε := caError_powers_numbers (ω := ω) m (N := 2 ^ (∑ i, (s i).1) * d)
    (by positivity) hrate
  have h := rap_fri_merkle_sound_deep P A R0 Rest RestV e I0 I Ifin nb s d 170
    (univariatePowersGenerator F m) Dg enc md L hdom model guards hR0 hlink hnb hRest errOld herr0
    (31 / 64) (31 / 64) hN hδ htoPoly _ hε A' Q_FS Q_H V Pn hFS hHq hterm hconfig
  refine le_trans (prEvent_mono _ _ _ ?_) (h.trans ?_)
  · rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
    · exact hb
    · exact hb
  have hk : k + 1 ≤ 26 := by
    have hsum : (∑ j, (s j).val) = k + 1 := by simp [hs]
    by_contra hc
    have h1 : 2 ^ 27 ≤ 2 ^ (∑ j, (s j).val) := by
      rw [hsum]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ n ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hn
    have h3 : 1 ≤ d.val := d.pos
    have : 2 ^ 27 ≤ 2 ^ (∑ j, (s j).val) * d.val := h1.trans (Nat.le_mul_of_pos_right _ h3)
    omega
  have hlen : (merkleSkels (MS)).length ≤ 61 := by
    rw [length_msC]; omega
  exact E2ENumbers.e2e_total_le P A R0 Rest RestV e I0 I Ifin nb s d hnb errOld hs hrate hn hF hm hns hD hH hnq
    herrOld hnb30 Q_FS hQFS Q_H V (merkleSkels (MS)).length Pn hQH hV hlen hDg

/-- The two copies of the right-hand side agree: `E2ENumbers.rapFriEps` is `RapFriQ.rapFriEps` at
`l = 170`, `θ = δ = 31/64`. -/
theorem rapFriEps_unify (errOld : ℕ → ℝ≥0∞) (ε : ℝ≥0) (Q : ℕ) :
    E2ENumbers.rapFriEps (ω := ω) P A R0 Rest RestV e I0 I Ifin nb s d errOld ε Q =
      rapFriEps P A R0 Rest RestV e I0 I Ifin nb s d 170 errOld (31 / 64 : ℝ) ((31 / 64 : ℝ≥0)) ε Q := rfl

end Numbers



/-! ## 4. Non-vacuity: a `PointMaskData` with empty trailing blocks (the DEEP shape) over a non-trivial field -/

end NockvmE2E.Merkle.RapFriQ

namespace NockvmE2E.Merkle.RapFriQ.NonVac

open NockvmE2E.Rap BinaryTree

/-- Leaf data over a one-point type is unique, for every skeleton. -/
def leafDataUnit : (s : Skeleton) → Unique (LeafData PUnit s)
  | .leaf => ⟨⟨.leaf PUnit.unit⟩, fun x => by cases x with | leaf a => rfl⟩
  | .internal l r =>
      haveI := leafDataUnit l
      haveI := leafDataUnit r
      ⟨⟨.internal default default⟩, fun x => by
        cases x with | internal a b => congr 1 <;> exact Subsingleton.elim _ _⟩

/-- The leaf type of block `r`: `F` below the bound `N`, a point above it. -/
abbrev FBlk (F : Type) (N r : ℕ) : Type := if r < N then F else PUnit

/-- `get` commutes with the casts of the leaf type. -/
theorem cast_get_leafCast {A B : Type} (h : A = B) {s : Skeleton} (x : LeafData A s) (i : SkeletonLeafIndex s) :
    cast h (x.get i) = (cast (congrArg (fun T => LeafData T s) h) x).get i := by
  subst h; rfl

/-- Block `r`: columns × positions, row-major through `E`, as the leaves of a perfect tree. -/
noncomputable def blockEq {ι : Type} (colRound : ι → ℕ) (Pt F : Type) (r m : ℕ)
    (E : {c : ι // colRound c = r} × Pt ≃ Fin (2 ^ m)) :
    Cols colRound (Pt → F) r ≃ LeafData F (Skeleton.perfect m) :=
  (Equiv.curry _ _ _).symm.trans ((Equiv.arrowCongr E (Equiv.refl F)).trans
    ((Equiv.arrowCongr (SkeletonLeafIndex.perfectEquiv m) (Equiv.refl F)).trans
      (LeafData.equivIndexFun (Skeleton.perfect m)).symm))

theorem blockEq_get {ι : Type} (colRound : ι → ℕ) (Pt F : Type) (r m : ℕ)
    (E : {c : ι // colRound c = r} × Pt ≃ Fin (2 ^ m)) (w : Cols colRound (Pt → F) r)
    (c : {c : ι // colRound c = r}) (x : Pt) :
    (blockEq colRound Pt F r m E w).get (SkeletonLeafIndex.perfectEquiv m (E (c, x))) = w c x := by
  show (LeafData.ofFun _ _).get _ = _
  rw [LeafData.get_ofFun]
  simp [Equiv.arrowCongr, Equiv.curry]

/-- **A `PointMaskData` whose blocks `r ≥ N` are empty** (every column lies below `N`): the DEEP shape
(`colRoundX = Sum.elim colRound (fun _ => P.R + 1)`, `N = P.R + 2`). Blocks below `N` are perfect trees on
`2 ^ m r` leaves numbered by `E r`; the empty blocks have the one-point leaf type. -/
noncomputable def boundedPointMd {ι Pt F Dg : Type} (colRound : ι → ℕ) (N : ℕ) (hlt : ∀ c, colRound c < N)
    (m : ℕ → ℕ) (E : ∀ r, r < N → ({c : ι // colRound c = r} × Pt ≃ Fin (2 ^ m r)))
    (ne : Nonempty F) (enc : F ↪ Dg) : PointMaskData colRound Pt F Dg where
  skel r := Skeleton.perfect (m r)
  FB r := FBlk F N r
  words r :=
    if h : r < N then
      (blockEq colRound Pt F r (m r) (E r h)).trans
        (Equiv.cast (congrArg (fun T => LeafData T (Skeleton.perfect (m r))) (if_pos h).symm))
    else
      haveI : Unique (LeafData (FBlk F N r) (Skeleton.perfect (m r))) := by
        rw [FBlk, if_neg h]; exact leafDataUnit _
      haveI : Unique (Cols colRound (Pt → F) r) :=
        ⟨⟨fun c => absurd (hlt c.1) (by rw [c.2]; exact h)⟩, fun f => funext fun c =>
          absurd (hlt c.1) (by rw [c.2]; exact h)⟩
      Equiv.ofUnique _ _
  ne r := by
    by_cases h : r < N
    · rw [FBlk, if_pos h]; exact ne
    · rw [FBlk, if_neg h]; exact ⟨PUnit.unit⟩
  enc r := by
    by_cases h : r < N
    · have e : FBlk F N r = F := if_pos h
      exact (Equiv.cast e).toEmbedding.trans enc
    · have e : FBlk F N r = PUnit := if_neg h
      exact (Equiv.cast e).toEmbedding.trans ⟨fun _ => enc ne.some, fun a b _ => Subsingleton.elim a b⟩
  hF r c := if_pos (by have := hlt c.1; rw [← c.2]; exact this)
  pos r cx := SkeletonLeafIndex.perfectEquiv (m r) ((if h : r < N then E r h else
    absurd (hlt cx.1.1) (by rw [cx.1.2]; exact h)) cx)
  get_pos r w c x := by
    have h : r < N := by have := hlt c.1; rw [← c.2]; exact this
    simp only [dif_pos h, Equiv.trans_apply, Equiv.cast_apply]
    rw [← cast_get_leafCast (if_pos h).symm, cast_cast, ← blockEq_get colRound Pt F r (m r) (E r h) w c x]
    exact cast_eq _ _

/-- **The mask data for a DEEP statement**: every column of `P.colRoundX` lies in a block `< P.R + 2`
(`P.hcol`), so the blocks `r ≥ P.R + 2` are empty. -/
noncomputable def deepPointMd {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
    {colRound : ι → ℕ} (P : DeepParams Φ K ι β colRound) {Pt F Dg : Type}
    (m : ℕ → ℕ) (E : ∀ r, r < P.R + 2 → ({c : ι ⊕ Fin P.nq // P.colRoundX c = r} × Pt ≃ Fin (2 ^ m r)))
    (ne : Nonempty F) (enc : F ↪ Dg) : PointMaskData P.colRoundX Pt F Dg :=
  boundedPointMd P.colRoundX (P.R + 2) (fun c => by
    rcases c with c | c
    · have := P.hcol c; simp only [DeepParams.colRoundX, Sum.elim_inl]; omega
    · simp [DeepParams.colRoundX]) m E ne enc

/-- A DEEP-shaped column layout: `R = 0`, two trace columns in block `0`, one quotient chunk in block `R + 1 = 1`
(`Sum.elim colRound (fun _ => R + 1)`); every block `r ≥ 2` is empty. -/
def dCol : Bool ⊕ Fin 1 → ℕ := Sum.elim (fun _ => 0) (fun _ => 0 + 1)

/-- Sizes of the perfect trees: block `0` has `2 columns × 2 positions = 2^2` leaves, block `1` has `2^1`. -/
def dM (r : ℕ) : ℕ := if r = 0 then 2 else 1

noncomputable def dE (r : ℕ) (_ : r < 2) : {c : Bool ⊕ Fin 1 // dCol c = r} × Fin 2 ≃ Fin (2 ^ dM r) :=
  Fintype.equivOfCardEq (by
    have : r = 0 ∨ r = 1 := by omega
    rcases this with rfl | rfl <;> decide)

/-- **Non-vacuity (a)**: a `PointMaskData` of the DEEP shape (blocks `r ≥ 2` empty) over the non-trivial
field `Bool` (digests `Bool`). Before Step 0 no such term existed. -/
noncomputable def dMd : PointMaskData dCol (Fin 2) Bool Bool :=
  boundedPointMd dCol 2 (fun c => by rcases c with c | c <;> simp [dCol]) dM dE ⟨true⟩
    (Function.Embedding.refl Bool)

theorem dMd_block_empty : IsEmpty {c : Bool ⊕ Fin 1 // dCol c = 5} :=
  ⟨fun ⟨c, h⟩ => by rcases c with c | c <;> simp [dCol] at h⟩

theorem dMd_FB_empty : dMd.FB 5 = PUnit := rfl

theorem dMd_FB_trace : dMd.FB 0 = Bool := rfl

end NockvmE2E.Merkle.RapFriQ.NonVac

namespace NockvmE2E.Merkle.RapFriQ

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort
  NockvmE2E.FriPort.Batched NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
open NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld SoundnessCoupling BadBound

section Instantiated

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
  (m' : ℕ → ℕ) (E : ∀ r, r < P.R + 2 → ({c : ι ⊕ Fin P.nq // P.colRoundX c = r} × Fin (2 ^ n) ≃ Fin (2 ^ m' r)))
  (ne : Nonempty B) (encB : B ↪ Dg) (L : Fri.FriLeaves (ω := ω) s)
variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
variable {Query : Type} [DecidableEq Query]
  {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt]



local notation "MS" => msC P A R0 Rest RestV e I0 I Ifin nb s d l Dg enc (NonVac.deepPointMd P m' E ne encB) L (S := S)

/-- **Non-vacuity (b)**: `rap_fri_merkle_sound_deep` instantiated at the mask data `deepPointMd` (built from the
block sizes and numberings `E`, a nonempty field, the codec). What remains a variable: the DEEP parameters `P`
and the RAP statement (no toy `DeepParams` exists), the guards, the query model and the adversary, and the
hypotheses `hR0 … hconfig`. -/
theorem rap_fri_merkle_sound_deep_of_blocks
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels (MS))) Dg)
    (guards : GuardSchedule (Statement × Salt) PUnit
      (compiledRoundsK Dg (OpenAll Dg (merkleSkels (MS))) (MS)))
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
    (A' : SuccinctAdversaryK Dg (OpenAll Dg (merkleSkels (MS))) Query Statement Salt W (MS))
    (Q_FS Q_H V Pn : ℕ)
    (hFS : FsBound (Q := Query) (∅ : (ofFn (KC Dg (OpenAll Dg (merkleSkels (MS))) Statement Salt (MS))).QueryCache)
      Q_FS (verifiedFS guards A'))
    (hH : IsQueryBoundP A' (@isHashQuery Query Dg _ (KC Dg (OpenAll Dg (merkleSkels (MS))) Statement Salt (MS))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels (MS)).length) (op : OpenAll Dg (merkleSkels (MS)))
      (logs : Fin (merkleSkels (MS)).length → MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount (mkClaims (merkleSkels (MS)) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (MS))).nodeBudget tag ≤ Pn) :
    Pr{let j ← randomOracleLoggedRun (succinctAcceptedExecutionK guards
        (merkleCheck (merkleSkels (MS)) model id)
        (cLocal P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc (NonVac.deepPointMd P m' E ne encB) L hdom (OpenAll Dg (merkleSkels (MS))) id) A') ∅}[
      match j.1.1 with | none => False | some (z, _, _) => z.1 ∉ {_x : Statement | R0.Holds}] ≤
    rapFriEps P A R0 Rest RestV e I0 I Ifin nb s d l errOld θ δ ε Q_FS +
      (multiCheckpointROMErrorNumerator (((merkleSkels (MS)).length * (Q_FS + 1)) * Pn)
        ((merkleSkels (MS)).length * (Q_FS + 1)) V Q_H : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹ := by
  have h := rap_fri_merkle_sound_deep P A R0 Rest RestV e I0 I Ifin nb s d l G Dg enc (NonVac.deepPointMd P m' E ne encB) L hdom model guards hR0 hlink hnb hRest errOld herr0 θ δ hN hδ htoPoly ε hε A' Q_FS Q_H V Pn hFS hH hterm hconfig
  refine le_trans (prEvent_mono _ _ _ ?_) h
  rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
  · exact hb
  · exact hb

end Instantiated

end NockvmE2E.Merkle.RapFriQ
