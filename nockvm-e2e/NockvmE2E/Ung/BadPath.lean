/-
the "bad accepted path" bound for an ARBITRARY path-local predicate
`Bad m0 tr χ` on the round-0 message, the extracted trace and the coins. Same proof as `rap_succinct_noncanon`
(`Ung/Positive.lean`, which is `Bad := non-canonical`); the hypothesis is the pointwise
"accepted ∧ off every summand ⇒ ¬ Bad", exactly the shape of `SoundG` with `Holds := ¬ Bad`.
-/
import NockvmE2E.Ung.Positive

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped ENNReal

namespace NockvmE2E.Ung

open NockvmE2E.Rap NockvmE2E.Succ

/-! ## Bad accepted paths are soundness failures (generalises `rap_succinct_noncanon` of `Positive.lean`) -/

section BadAt

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ) (Bad : R.M0 → Tr ι β → Coins Φ K → Prop)

/-- A path is BAD for the predicate `Bad` on (round-0 message, extracted trace, coins). -/
def BadAt (path : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) : Prop :=
  Bad path.1 (fun j => CS.ext ((sFinal R CS plan I0 I Ifin nb path).1 j))
    (sFinal R CS plan I0 I Ifin nb path).2.1

/-- The statement whose acceptance is "succinct-accepted, extraction succeeded, AND `Bad`"; `Holds` is
`False`, so every acceptance is a soundness failure. -/
abbrev badStmt : RapStatement Φ K ι CS.Com colRound :=
  { succStmt R CS plan (fun m0 coms fin χ => okAccepts R CS plan m0 coms fin χ ∧
      Bad m0 (fun j => CS.ext (coms j)) χ) with Holds := False }

variable {R CS plan I0 I Ifin nb Bad}

theorem finalOf_bad : ∀ (r k : ℕ) (tr : Tr ι CS.Com) (χ : Coins Φ K)
    (path : (protocol (colRounds Φ K CS.Com colRound I
      (finRound (badStmt R CS plan Bad) Ifin) r k)).tree.ExecutionPath),
    finalOf (badStmt R CS plan Bad) I Ifin r k tr χ path =
      finalOf (succStmt R CS plan (succAccepts R CS plan)) I Ifin r k tr χ path
  | _, 0, _, _, _ => rfl
  | r, k + 1, tr, χ, path => by
    rw [finalOf, finalOf]
    exact finalOf_bad (r + 1) k _ _ path.2.2

theorem rapAccepts_bad_iff (p : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) :
    rapAccepts (badStmt R CS plan Bad) I0 I Ifin nb p ↔
      rapAccepts (sStmt R CS plan) I0 I Ifin nb p ∧ ¬ ExtFailAt R CS plan I0 I Ifin nb p ∧
        BadAt R CS plan I0 I Ifin nb Bad p := by
  unfold rapAccepts
  rw [finalOf_bad]
  unfold ExtFailAt BadAt sFinal
  simp only [badStmt, succStmt, okAccepts, not_not]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

theorem roundBound_bad (m0 : R.M0) (r : ℕ) :
    roundBound (badStmt R CS plan Bad) blkOf m0 r = roundBound R blkOf m0 r := by
  simp only [roundBound, List.map_map]
  rfl

/-- `badStmt` satisfies the bridge's `Certificate`: with `AirDet`, an accepted non-canonical path off all
summands is impossible (`SoundG` with `Holds = False`). -/
theorem certificate_bad (hC : Certificate R blkOf nb) (hl : Link R CS plan)
    (hD : ∀ (m0 : R.M0) (tr : Tr ι β) (fin : R.Mfin) (χ : Coins Φ K), R.Accepts m0 tr fin χ →
      (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → ¬ Bad m0 tr χ) :
    Certificate (badStmt R CS plan Bad) blkOf nb where
  sound m0 coms fin χ hacc hall := by
    obtain ⟨hok, hnd⟩ := hacc
    have hA := hl m0 _ fin χ hok.1.2 hok.2
    exact hD m0 _ (plan.finOf fin) χ hA
      (fun s hs hm => hall (pullS CS s) (List.mem_map_of_mem hs) hm) hnd
  local_ m0 s' hs' := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
    exact local_pullS CS (hC.local_ m0 s hs)
  blk_lt m0 s' hs' := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
    exact hC.blk_lt m0 s hs

variable (R CS plan I0 I Ifin nb Bad)

/-- **No non-canonical accepted path** (single path): with `AirDet`, the probability that an adversary with ≤ `Q`
fresh keys gets an accepted path that is non-canonical is at most the `rap_succinct_sound` bound. -/
theorem rap_succinct_badpath (hC : Certificate R blkOf nb) (hl : Link R CS plan)
    (hD : ∀ (m0 : R.M0) (tr : Tr ι β) (fin : R.Mfin) (χ : Coins Φ K), R.Accepts m0 tr fin χ →
      (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → ¬ Bad m0 tr χ)
    (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    {Statement GlobalSalt Witness : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness (sRounds R CS plan I0 I Ifin nb))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q)
    (εCS : ℝ≥0∞)
    (hCS : Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS plan I0 I Ifin nb) guards (sAccept R CS plan I0 I Ifin nb) adversary) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ ExtFailAt R CS plan I0 I Ifin nb p] ≤ εCS) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS plan I0 I Ifin nb) guards (sAccept R CS plan I0 I Ifin nb) adversary) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ BadAt R CS plan I0 I Ifin nb Bad p] ≤
      Q * Finset.univ.sup (sErrors R CS plan I0 I Ifin nb err) +
        ∑ j, sErrors R CS plan I0 I Ifin nb err j + εCS := by
  classical
  let Rnd := badStmt R CS plan Bad
  have hCnd : Certificate Rnd blkOf nb := certificate_bad hC hl hD
  have herr' : ∀ m0 r, roundBound Rnd blkOf m0 r ≤ err r := fun m0 r => by
    rw [roundBound_bad]; exact herr m0 r
  let accND : (Statement × GlobalSalt) → (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath →
      Bool := fun _ path => decide (rapAccepts Rnd I0 I Ifin nb path)
  have hsplit := pr_accept_split_ev guards accND (sAccept R CS plan I0 I Ifin nb) adversary
    (fun _ p => BadAt R CS plan I0 I Ifin nb Bad p)
    (fun _ p => ExtFailAt R CS plan I0 I Ifin nb p) (fun z p hacc hnc => by
      by_cases hs : ExtFailAt R CS plan I0 I Ifin nb p
      · exact Or.inr hs
      · have h1 : rapAccepts (sStmt R CS plan) I0 I Ifin nb p := of_decide_eq_true hacc
        exact Or.inl (decide_eq_true ((rapAccepts_bad_iff p).mpr ⟨h1, hs, hnc⟩)))
  refine hsplit.trans (add_le_add ?_ hCS)
  have hrap := rap_singleSalt_knowledge_soundness (R := Rnd) (blk := blkOf) (I0 := I0) (I := I)
    (Ifin := Ifin) (nb := nb) hCnd err herr' guards adversary Set.univ
  have cost := singleSalt_query_cost guards accND (rapErrors Rnd I0 I Ifin nb err) adversary
  have keys := expectedSingleSaltAdversaryKeys_le_queryBound adversary Q queryBound
  refine le_trans (prEvent_mono _ _ _ ?_) (hrap.trans (cost.1.trans ?_))
  · rintro ⟨⟨⟨_ | ⟨z, p, w⟩, _⟩, _⟩, _⟩ ⟨x, hx⟩
    · simp at hx
    · exact ⟨Set.mem_univ _, trivial, fun h => h⟩
  · rw [mul_comm (Q : ℝ≥0∞)]
    exact add_le_add (mul_le_mul' le_rfl keys) cost.2

end BadAt

end NockvmE2E.Ung
