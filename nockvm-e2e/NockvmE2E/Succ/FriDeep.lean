/-
the DEEP instance of `Succ/Fri.rap_fri_sound`.

Committed data are WORDS on FRI's evaluation domain, `β = Fin (2^n) → F` (ideal oracles, no Merkle).
The frame's reading of a word as a polynomial is unique decoding at FRI's degree bound,
`P.toPoly = udDecode ω δ N` (`N = 2^{Σ s}·d`). The verifier opens the trace columns at `ζ·off k` and
the quotient chunks at `ζ` (`deepPlan`), checks the DEEP identity on the opened values, checks that every
opening point is off the domain (`OffDom`), and runs batched FRI on the DEEP quotient words
`(f_{col j} − val j)/(X − pt j)` (`deepStmt`). The opening claims themselves are NOT checked: they
follow (`deep_hbind`) from FRI's input language via `Deep/UDFri.deep_of_inputRelation`.

* Step 1 (degree off-by-one): `udDecode_natDegree_lt` — the decoded polynomial has `natDegree < N + 1`;
  `udDecode_le_card` — with `N ≤ |H|` this is the frame's `hβ` (`natDegree ≤ |H|`, weakened from `< |H|` ), so a `DeepParams` with `toPoly = udDecode` exists whenever `N ≤ |H|`, e.g. `N = |H| = 2^h` with
  any folding `Σs ≤ h` (`udDecode_lt_card` kept for `N + 1 ≤ |H|`). `udDecode_eq` — inside the unique-decoding
  radius, `udDecode` returns THE close polynomial.
* `deep_hbind`: the bridge hypothesis `hbind` of `rap_fri_sound`, discharged.
* `rap_fri_sound_deep`: the end-to-end bound for the DEEP-extended RAP with batched FRI.
-/
import NockvmE2E.Succ.Fri
import NockvmE2E.Succ.Deep
import NockvmE2E.Deep.UDFri

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

namespace NockvmE2E.Succ.FriDeep

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort.Batched

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}

/-! ## 1. Unique decoding at FRI's bound, and the degree bridge -/

open Classical in
/-- Unique decoding of a word at degree `< N + 1` and radius `δ` (any choice; `0` if none). -/
noncomputable def udDecode (ω : SmoothCosetFftDomain n F) (δ : ℝ≥0) (N : ℕ) (w : Fin (2 ^ n) → F) : F[X] :=
  if h : ∃ p : F[X], p.natDegree < N + 1 ∧ ∃ S : Finset (Fin (2 ^ n)), Dense δ S ∧ Agree (domEmb ω) w p S
  then h.choose else 0

/-- A base-field word read as an `F`-word (G2: the committed words are `B`-valued, FRI runs on this). -/
def liftW (w : Fin (2 ^ n) → B) : Fin (2 ^ n) → F := fun i => algebraMap B F (w i)

/-- Unique decoding of a `B`-word through `liftW` (`toPoly` of the base-word frame). -/
noncomputable def udDecodeB (ω : SmoothCosetFftDomain n F) (δ : ℝ≥0) (N : ℕ) (w : Fin (2 ^ n) → B) : F[X] :=
  udDecode ω δ N (liftW w)

theorem udDecode_natDegree_lt (δ : ℝ≥0) (N : ℕ) (w : Fin (2 ^ n) → F) :
    (udDecode ω δ N w).natDegree < N + 1 := by
  unfold udDecode
  split_ifs with h
  · exact h.choose_spec.1
  · rw [natDegree_zero]; exact Nat.succ_pos _

/-- **Step 1, the degree bridge.** FRI's bound `N` gives `natDegree < N + 1`; the frame wants
`natDegree < |H|`. They meet iff `N + 1 ≤ |H|` (`udDecode_le_card`: `N ≤ |H|` suffices for `hβ`, which is `≤ |H|` since ). -/
theorem udDecode_lt_card (δ : ℝ≥0) {N : ℕ} {H : Finset F} (hH : N + 1 ≤ H.card) (w : Fin (2 ^ n) → F) :
    (udDecode ω δ N w).natDegree < H.card :=
  lt_of_lt_of_le (udDecode_natDegree_lt δ N w) hH

/-- The frame's `hβ` (`natDegree ≤ |H|`) for `udDecode` at any FRI bound `N ≤ |H|`. -/
theorem udDecode_le_card (δ : ℝ≥0) {N : ℕ} {H : Finset F} (hH : N ≤ H.card) (w : Fin (2 ^ n) → F) :
    (udDecode ω δ N w).natDegree ≤ H.card :=
  Nat.le_of_lt_succ (lt_of_lt_of_le (udDecode_natDegree_lt δ N w) (Nat.succ_le_succ hH))

/-- `hβ` for the base-word reading `udDecodeB`. -/
theorem udDecodeB_le_card (δ : ℝ≥0) {N : ℕ} {H : Finset F} (hH : N ≤ H.card) (w : Fin (2 ^ n) → B) :
    (udDecodeB ω δ N w).natDegree ≤ H.card :=
  udDecode_le_card δ hH _

/-- Inside the unique-decoding radius, `udDecode` returns the close polynomial. -/
theorem udDecode_eq {δ : ℝ≥0} {N : ℕ} (hN : N + 1 ≤ 2 ^ n)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (N + 1) : Set (Fin (2 ^ n) → F)))
    {w : Fin (2 ^ n) → F} {p : F[X]} (hp : p.natDegree < N + 1) {S : Finset (Fin (2 ^ n))}
    (hS : Dense δ S) (hA : Agree (domEmb ω) w p S) : udDecode ω δ N w = p := by
  have hex : ∃ p : F[X], p.natDegree < N + 1 ∧
      ∃ S : Finset (Fin (2 ^ n)), Dense δ S ∧ Agree (domEmb ω) w p S := ⟨p, hp, S, hS, hA⟩
  unfold udDecode
  simp only [hex, ↓reduceDIte]
  obtain ⟨hq, S', hS', hA'⟩ := hex.choose_spec
  have hM : N + 1 ≤ Fintype.card (Fin (2 ^ n)) := by rwa [Fintype.card_fin]
  exact eq_of_agree (domEmb ω) (domEmb ω).injective hq hp hA' hA
    (card_inter_ge (by have := card_add_of_le_relUDR (domEmb ω) hM hδ hS' hS; omega))

/-! ## 2. The DEEP batched-FRI statement and the bridge -/

section Bridge

variable {Φ : CoinFrame} {ι : Type} [Fintype ι] {colRound : ι → ℕ}
  (P : DeepParams Φ F ι (Fin (2 ^ n) → B) colRound) {r : ℕ} (A : AirShape P r)
  (R0 : RapStatement Φ F ι (Fin (2 ^ n) → B) colRound) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)

/-- The column of batched opening `j`. -/
def colOf (j : Fin (m + 1)) : ι ⊕ Fin P.nq :=
  Sum.elim (fun ck => Sum.inl ck.1) (fun q => Sum.inr q) (e j)

/-- The point of batched opening `j`: `ζ·off k` (trace) or `ζ` (chunk). -/
def ptOf (χ : Coins Φ F) (j : Fin (m + 1)) : F :=
  Sum.elim (fun ck => A.pt ck.1 ck.2 (χ P.z)) (fun _ => χ P.z) (e j)

/-- The claimed value of batched opening `j`. -/
def valOf (fin : DeepFin P (r := r) R0) (j : Fin (m + 1)) : F :=
  Sum.elim (fun ck => fin.2.1 ck) (fun q => fin.2.2 q) (e j)

/-- Every opening point is off FRI's domain (a verifier check). -/
def OffDom (χ : Coins Φ F) : Prop := ∀ j i, ω i ≠ ptOf P A e χ j

/-- **The DEEP batched-FRI statement**: the DEEP quotient words of the committed words. -/
noncomputable def deepStmt (tr : DeepTr P) (fin : DeepFin P (r := r) R0) (χ : Coins Φ F) : BStmt ω m :=
  ((), fun j x => deepWord (⇑ω) (liftW (tr (colOf P e j))) (ptOf P A e χ j) (valOf P R0 e fin j)
    (ω.equivToFinset.symm x))

/-- **The bridge (`hbind` of `rap_fri_sound`).** If every opening point is off the domain, every column
is opened (`r ≠ 0`), `toPoly` is unique decoding at FRI's bound, and the DEEP quotient words are in batched
FRI's input language, then every DEEP claim is true for the committed words. -/
theorem deep_hbind {s : Fin (k + 1) → ℕ+} {d : ℕ+} {δ : ℝ≥0} [NeZero r]
    (hN : friBound s d + 1 ≤ 2 ^ n)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb ω) (friBound s d + 1) : Set (Fin (2 ^ n) → F)))
    (htoPoly : P.toPoly = udDecodeB ω δ (friBound s d))
    (tr : DeepTr P) (fin : DeepFin P (r := r) R0) (χ : Coins Φ F) (hoff : OffDom (ω := ω) P A e χ)
    (hmem : deepStmt (ω := ω) P A R0 e tr fin χ ∈ (inputRelation (ω := ω) s d m δ).language) :
    SatClaims (deepOI P) tr (deepClaims P A R0 χ fin) := by
  obtain ⟨sw, hsw, hsw1⟩ := hmem
  have hcov : Function.Surjective (colOf P e) := by
    intro c
    rcases c with c | q
    · exact ⟨e.symm (Sum.inl (c, 0)), by simp [colOf]⟩
    · exact ⟨e.symm (Sum.inr q), by simp [colOf]⟩
  have hwords : ∀ j i, sw.1.2 j (ω.equivToFinset i) =
      deepWord (⇑ω) (liftW (tr (colOf P e j))) (ptOf P A e χ j) (valOf P R0 e fin j) i := by
    intro j i
    rw [hsw1]
    show deepWord (⇑ω) (liftW (tr (colOf P e j))) (ptOf P A e χ j) (valOf P R0 e fin j)
      (ω.equivToFinset.symm (ω.equivToFinset i)) = _
    rw [Equiv.symm_apply_apply]
  obtain ⟨Pc, ⟨S, hS, hA⟩, hdeg, hop, _⟩ := deep_of_inputRelation (colOf P e) (ptOf P A e χ)
    (valOf P R0 e fin) (fun c => liftW (tr c)) hcov hoff hN hδ sw hsw hwords
  have hdec : ∀ c, P.toPoly (tr c) = Pc c := fun c => by
    rw [htoPoly]; exact udDecode_eq hN hδ (hdeg c) hS (hA c)
  have key : ∀ j, eval (ptOf P A e χ j) (P.toPoly (tr (colOf P e j))) = valOf P R0 e fin j :=
    fun j => by rw [hdec]; exact hop j
  intro c hc
  unfold deepClaims at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨ck, _, rfl⟩ := List.mem_map.mp hc
    have := key (e.symm (Sum.inl ck))
    simp only [colOf, ptOf, valOf, Equiv.apply_symm_apply, Sum.elim_inl] at this
    exact this
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hc
    have := key (e.symm (Sum.inr q))
    simp only [colOf, ptOf, valOf, Equiv.apply_symm_apply, Sum.elim_inr] at this
    exact this

end Bridge

/-! ## 3. The end-to-end theorem -/

section Sound

variable [SampleableType F] [Inhabited F] [Inhabited B]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ F ι (Fin (2 ^ n) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ F ι (Fin (2 ^ n) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ F → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ F → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)

/-- The DEEP plan with the off-domain check added to the residual check. -/
noncomputable abbrev friPlan : OpenPlan (P.statement R0 Rest) (deepCS P) :=
  deepPlan P A R0 Rest (fun m0 fin χ => OffDom (ω := ω) P A e χ ∧ RestV m0 fin χ)

variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ω) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ω) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ n) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ω) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)

/-- **the DEEP + batched FRI instance of the shared theorem.** The staged RAP `R0` extended by
DEEP (`P.statement R0 Rest`), committed as words on FRI's domain (ideal oracles, NO Merkle), the
openings at `ζ·off k` / `ζ` proven by batched FRI on the DEEP quotient words, one single-salt FS game.
For every guard schedule and every single-salt adversary with at most `Q` fresh keys:
`Pr[accepted ∧ ¬Holds] ≤ Q·(max_j rapErr_j ⊔ (ε ⊔ max_j cErr_j)) + (Σ_j rapErr_j + (ε + Σ_i foldErr_i + (1−min θ δ)^l))`,
where `rapErr` is the RAP+DEEP per-round error of `rap_succinct_sound_deep` (`errDeep P errOld`: the old
error plus `ε_α` at round `R`, `ε_ζ` at round `R+1`) and the rest is F4's batched-FRI bound.
Hypotheses beyond `rap_succinct_sound_deep`: `toPoly` is unique decoding at FRI's bound
(`htoPoly`; such a `P` exists whenever `N ≤ |H|`, `udDecode_le_card`), `N + 1 ≤ 2^n`, `δ ≤ relUDR`,
and FRI's generator bound `hε`. -/
theorem rap_fri_sound_deep {nb : ℕ} (hR0 : RapInput R0 nb)
    (hlink : ∀ m0 (tr : DeepTr P) fin χ, Rest m0 tr fin χ →
      (∀ i, ∀ x ∈ P.H, eval x (P.Cp χ (P.restr tr) i) = 0) → R0.Accepts m0 (P.restr tr) fin χ)
    (hnb : P.R + 1 < nb)
    (hRest : ∀ m0 (tr : DeepTr P) fin χ, RestV m0 fin χ →
      SatClaims (deepOI P) tr (deepClaims P A R0 χ fin) → Rest m0 tr fin.1 χ)
    (errOld : ℕ → ℝ≥0∞) (herr0 : ∀ m0 r, roundBound R0 blkOf m0 r ≤ errOld r)
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (θ : ℝ) (δ : ℝ≥0)
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
      Q * (Finset.univ.sup (rapErrors (Rok (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e))
            I0 I Ifin nb (errDeep P errOld)) ⊔
          ((ε : ℝ≥0∞) ⊔ Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)))) +
        (∑ j, rapErrors (Rok (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e))
            I0 I Ifin nb (errDeep P errOld) j +
          ((ε : ℝ≥0∞) +
            (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞))) := by
  have hC : Certificate (P.statement R0 Rest) blkOf nb :=
    certificate_deep P R0 Rest hlink blkOf nb (certificate_of_input hR0) hnb blkOf
      (fun _ _ _ => rfl) (blkOf_sAlpha P) (blkOf_sZeta P)
  have hl : Link (P.statement R0 Rest) (deepCS P) (friPlan (ω := ω) P A R0 Rest RestV e) :=
    link_deepPlan P A R0 Rest _ (fun m0 tr fin χ h hs => hRest m0 tr fin χ h.2 hs)
  exact rap_fri_sound (θ := θ) hC hl (errDeep P errOld)
    (fun m0 r => by
      refine (roundBound_deep P R0 Rest m0 r).le.trans ?_
      unfold errDeep
      gcongr
      exact herr0 m0 r)
    (fun _ tr fin χ hcheck hmem =>
      deep_hbind P A R0 e hN hδ htoPoly tr fin χ hcheck.2.1 hmem)
    ε hε guards adversary Q queryBound

end Sound

end NockvmE2E.Succ.FriDeep
