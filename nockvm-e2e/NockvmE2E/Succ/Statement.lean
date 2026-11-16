/-
SUCC-0, part 2: "RAP ⇒ succinct argument" with the commitment scheme `CS` as a
parameter (`Succ/Commitment.lean`), over the Rap frame twin and Quang Dao's single-salt Fiat–Shamir.

The succinct protocol (`sRounds`) is the staged-RAP protocol of `Rap/Protocol.lean` in which every column
is replaced by its commitment (`Cols colRound CS.Com r`), and the final message `plan.Mfin` carries the
full verifier's final message, the opened values and the opening proof. Coins are sampled after each
round's commitment, and the only message after the last coins is the final one, which no summand reads
(summands see `m0`, columns and coins only) —  (c) holds by construction. The public claim is
the fixed `R` (with its publics) and the round-0 message is the first transcript entry, absorbed before
χ₀ ; the theorem is for a FIXED claim (non-adaptive statement).

* `rap_succinct_sound` (PROVED, generic in `CS`): for every single-salt adversary with ≤ `Q` fresh keys,
  `Pr[succinct verifier accepts ∧ ¬ Holds] ≤ Q · max_j errs j + Σ_j errs j + ε_CS`, where `errs` is the
  per-round RAP error (the part of `epsilonOf` priced on each coin block, `rapErrors`) and `ε_CS` bounds
  the CS failure event "accepted ∧ the extracted trace violates an accepted opening" (`hCS`) in the same
  experiment. Proof: the accepted runs split into extraction successes — where the extracted trace
  (`CS.ext` of the commitments, fixed when sent) passes the FULL verifier (`Link`) and the RAP bridge
  `rap_singleSalt_knowledge_soundness` applies to the pulled-back summands — and `ExtFail`.
* `rap_succinct_sound_perfect`: `ε_CS = 0` for a perfectly extractable `CS` (proved: `hCS` holds with 0).
* `rap_succinct_complete`, `rap_succinct_complete_count` (PROVED): honest commit + honest opening; the
  succinct rejection mass is at most the RAP-level honest rejection mass `ε_c`.
* `rap_succinct_sound_deep` (PROVED): the IOP form (`iopCS`, honest oracle access, `ε_CS = 0`) for the
  DEEP-extended RAP `P.statement R0 Rest`, composing `certificate_deep` and `rap_singleSalt_knowledge_soundness`;
  the DEEP error `ε_DEEP` appears explicitly at rounds `R`, `R+1` (`roundBound_deep`).
-/
import NockvmE2E.Succ.Commitment
import NockvmE2E.Succ.Local
import NockvmE2E.Rap.DeepCert

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped ENNReal

namespace NockvmE2E.Succ

open NockvmE2E.Rap

/-! ## 1. A union bound between two terminal checks of the same single-salt run -/

section Split

variable {rounds : List Round} {Statement GlobalSalt Witness : Type}
  [DecidableEq Statement] [DecidableEq GlobalSalt]

/-- Changing the terminal check from `acc₂` to `acc₁` costs at most the mass of the accepted runs on
which `acc₂` holds but `acc₁` fails because of `fail`. The underlying run is the same
(`singleSaltAcceptedExecution_loggedRun`). -/
theorem pr_accept_split (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (acc₁ acc₂ : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds) (B : Prop)
    (fail : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Prop)
    (h : ∀ z p, acc₂ z p = true → acc₁ z p = true ∨ fail z p) :
    Pr{let joint ← (randomOracleLoggedRun
        (singleSaltAcceptedExecution rounds guards acc₂ adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ B] ≤
      Pr{let joint ← (randomOracleLoggedRun
        (singleSaltAcceptedExecution rounds guards acc₁ adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ B] +
      Pr{let joint ← (randomOracleLoggedRun
        (singleSaltAcceptedExecution rounds guards acc₂ adversary) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ fail z p] := by
  rw [singleSaltAcceptedExecution_loggedRun guards acc₂, singleSaltAcceptedExecution_loggedRun guards acc₁,
    prEvent_map, prEvent_map, prEvent_map]
  refine le_trans (prEvent_mono _ _ _ ?_) (prEvent_or_le _ _ _)
  rintro ⟨⟨⟨sel, log⟩, log'⟩, cache⟩ ⟨⟨x, hx⟩, hB⟩
  simp only [acceptSingleSaltResult] at hx ⊢
  rcases sel with _ | ⟨z, p, w⟩
  · simp at hx
  · have hacc : acc₂ z p = true := by
      by_contra hn; simp [Option.filter, hn] at hx
    rcases h z p hacc with h1 | h2
    · exact Or.inl ⟨⟨(z, p, w), by simp [Option.filter, h1]⟩, hB⟩
    · exact Or.inr ⟨z, p, w, by simp [Option.filter, hacc], h2⟩

end Split

/-! ## 2. The succinct statement over the frame -/

section Frame

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}

/-- A summand pulled back along the extractor: it reads the extracted columns `ext ∘ coms`. -/
def pullS (CS : CommitScheme β O) (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)) :
    BadSummand Φ K (Tr ι CS.Com) (TracesStaged Φ colRound) where
  coins := s.coins
  dep := s.dep
  disj := s.disj
  badSet tr χ := s.badSet (fun j => CS.ext (tr j)) χ
  weight := s.weight
  card_le _ _ := s.card_le _ _
  readsOn Q hQ := s.readsOn (fun χ j => CS.ext (Q χ j))
    (fun j χ χ' h => congrArg CS.ext (hQ j χ χ' h))

theorem local_pullS (CS : CommitScheme β O) {s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)}
    {b : ℕ} (h : Local s b) : Local (pullS CS s) b where
  coins_block := h.coins_block
  dep_le := h.dep_le
  congr tr tr' χ χ' ht hc :=
    h.congr (fun j => CS.ext (tr j)) (fun j => CS.ext (tr' j)) χ χ' (fun j hj => congrArg CS.ext (ht j hj)) hc

/-- What the succinct verifier opens: the claims (points from the coins, values from the final message),
the opening proof, its residual check on the opened values, and the full verifier's final message. -/
structure OpenPlan (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) where
  Mfin : Type
  claims : R.M0 → Mfin → Coins Φ K → Claims O ι
  pf : Mfin → CS.Pf
  check : R.M0 → Mfin → Coins Φ K → Prop
  finOf : Mfin → R.Mfin

variable (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)

/-- The statement over commitments with acceptance `A`; summands pulled back along `CS.ext`. -/
abbrev succStmt (A : R.M0 → Tr ι CS.Com → plan.Mfin → Coins Φ K → Prop) :
    RapStatement Φ K ι CS.Com colRound where
  M0 := R.M0
  Mfin := plan.Mfin
  summands m0 := (R.summands m0).map (pullS CS)
  Accepts := A
  Holds := R.Holds

/-- **The succinct verifier**: the opening check and the residual check on the opened values. -/
def succAccepts (m0 : R.M0) (coms : Tr ι CS.Com) (fin : plan.Mfin) (χ : Coins Φ K) : Prop :=
  CS.verify coms (plan.claims m0 fin χ) (plan.pf fin) ∧ plan.check m0 fin χ

/-- The succinct verifier on runs where extraction succeeded. -/
def okAccepts (m0 : R.M0) (coms : Tr ι CS.Com) (fin : plan.Mfin) (χ : Coins Φ K) : Prop :=
  succAccepts R CS plan m0 coms fin χ ∧ SatClaims O (fun j => CS.ext (coms j)) (plan.claims m0 fin χ)

/-- **The link** (per instance; the abstract form of `Deep/UDLink.accepts_of_deep`): the residual check and
true openings of a trace make the FULL verifier accept that trace. -/
def Link : Prop :=
  ∀ m0 (tr : Tr ι β) fin χ, plan.check m0 fin χ → SatClaims O tr (plan.claims m0 fin χ) →
    R.Accepts m0 tr (plan.finOf fin) χ

/-- **The RAP-level inputs**: the pointwise `hsound` premise of `standaloneG_of_sound`
(`SoundG`), each summand priced in ONE sampling round with its reads no later (`OneRound`), every round
among the `nb` sampled ones, and `|K| ≥ 2`. Column-locality is derived (`local_of_readsOn`). -/
structure RapInput (nb : ℕ) : Prop where
  sound : SoundG R
  card : 1 < Fintype.card K
  oneRound : ∀ m0, ∀ s ∈ R.summands m0, OneRound s
  blk_lt : ∀ m0, ∀ s ∈ R.summands m0, blkOf s < nb

variable {R CS plan}

theorem certificate_of_input {nb : ℕ} (h : RapInput R nb) : Certificate R blkOf nb where
  sound := h.sound
  local_ m0 s hs := local_of_readsOn h.card s (h.oneRound m0 s hs)
  blk_lt := h.blk_lt

theorem certificate_ok {nb : ℕ} (hC : Certificate R blkOf nb) (hl : Link R CS plan) :
    Certificate (succStmt R CS plan (okAccepts R CS plan)) blkOf nb where
  sound m0 coms fin χ hacc hall :=
    hC.sound m0 _ (plan.finOf fin) χ (hl m0 _ fin χ hacc.1.2 hacc.2)
      (fun s hs hm => hall (pullS CS s) (List.mem_map_of_mem hs) hm)
  local_ m0 s' hs' := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
    exact local_pullS CS (hC.local_ m0 s hs)
  blk_lt m0 s' hs' := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
    exact hC.blk_lt m0 s hs

theorem roundBound_succ (A : R.M0 → Tr ι CS.Com → plan.Mfin → Coins Φ K → Prop) (m0 : R.M0) (r : ℕ) :
    roundBound (succStmt R CS plan A) blkOf m0 r = roundBound R blkOf m0 r := by
  simp only [roundBound, List.map_map]
  rfl

/-! ### Completeness  -/

/-- Honest commitments of staged columns are staged. -/
theorem staged_commit {Q : Coins Φ K → Tr ι β} (hQ : TracesStaged Φ colRound Q) :
    TracesStaged Φ colRound (fun χ j => CS.commit (Q χ j)) :=
  fun j χ χ' h => congrArg CS.commit (hQ j χ χ' h)

/-- The honest succinct final message `honest m0 tr fin χ` opens what the full verifier accepts. -/
def HonestPlan (honest : R.M0 → Tr ι β → R.Mfin → Coins Φ K → plan.Mfin) : Prop :=
  ∀ m0 tr fin χ, R.Accepts m0 tr fin χ →
    plan.check m0 (honest m0 tr fin χ) χ ∧
    SatClaims O tr (plan.claims m0 (honest m0 tr fin χ) χ) ∧
    plan.pf (honest m0 tr fin χ) = CS.prove tr (plan.claims m0 (honest m0 tr fin χ) χ)

/-- **Completeness, pointwise**: honest commitment + honest opening pass the succinct verifier wherever the
full verifier accepts the honest trace. -/
theorem rap_succinct_complete {honest : R.M0 → Tr ι β → R.Mfin → Coins Φ K → plan.Mfin}
    (hh : HonestPlan honest) {m0 : R.M0} {tr : Tr ι β} {fin : R.Mfin} {χ : Coins Φ K}
    (hacc : R.Accepts m0 tr fin χ) :
    succAccepts R CS plan m0 (fun j => CS.commit (tr j)) (honest m0 tr fin χ) χ := by
  obtain ⟨hc, hs, hp⟩ := hh m0 tr fin χ hacc
  exact ⟨by rw [hp]; exact CS.complete tr _ hs, hc⟩

open Classical in
/-- **Completeness **: if the honest RAP prover `msg` is accepted off a bad coin set of mass
`ε_c`, the honest succinct prover (commit each column, open honestly) is rejected with mass `≤ ε_c`. -/
theorem rap_succinct_complete_count {honest : R.M0 → Tr ι β → R.Mfin → Coins Φ K → plan.Mfin}
    (hh : HonestPlan honest) (msg : Messages R) (εc : ℚ)
    (hεc : ((Finset.univ.filter fun χ : Coins Φ K => ¬ R.Accepts msg.m0 (msg.Q χ) (msg.fin χ) χ).card : ℚ) /
      Fintype.card (Coins Φ K) ≤ εc) :
    ((Finset.univ.filter fun χ : Coins Φ K => ¬ succAccepts R CS plan msg.m0
        (fun j => CS.commit (msg.Q χ j)) (honest msg.m0 (msg.Q χ) (msg.fin χ) χ) χ).card : ℚ) /
      Fintype.card (Coins Φ K) ≤ εc := by
  refine le_trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) hεc
  exact_mod_cast Finset.card_le_card (fun χ hχ => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    exact fun ha => hχ (rap_succinct_complete hh ha))

end Frame

/-! ## 3. Soundness -/

section Sound

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ)

/-- The succinct protocol's rounds: `[M0 | Unit] :: [commitments of round r | coins of block r] :: [final | Unit]`. -/
noncomputable abbrev sRounds : List Round :=
  rapRounds Φ K CS.Com colRound R.M0 plan.Mfin I0 I Ifin nb

/-- The succinct statement (its `Accepts` is the succinct verifier). -/
abbrev sStmt := succStmt R CS plan (succAccepts R CS plan)

/-- The per-round errors (`0` at the two `Unit` rounds). -/
noncomputable abbrev sErrors (err : ℕ → ℝ≥0∞) : RoundErrors (sRounds R CS plan I0 I Ifin nb) :=
  rapErrors (sStmt R CS plan) I0 I Ifin nb err

/-- The succinct verifier's terminal check. -/
noncomputable def sAccept {Input : Type} (_ : Input)
    (path : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) : Bool :=
  open Classical in decide (rapAccepts (sStmt R CS plan) I0 I Ifin nb path)

/-- What an accepted path wrote: commitments, coins, final message. -/
def sFinal (path : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) :
    Tr ι CS.Com × Coins Φ K × plan.Mfin :=
  finalOf (sStmt R CS plan) I Ifin 0 nb (fun _ => default) (fun _ => default) path.2.2

/-- **The CS failure on a path**: the extracted trace violates the claims the path opened. -/
def ExtFailAt (path : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) : Prop :=
  ¬ SatClaims O (fun j => CS.ext ((sFinal R CS plan I0 I Ifin nb path).1 j))
    (plan.claims path.1 (sFinal R CS plan I0 I Ifin nb path).2.2 (sFinal R CS plan I0 I Ifin nb path).2.1)

variable {R CS plan I0 I Ifin nb}

/-- `finalOf` reads only the message types, not the acceptance. -/
theorem finalOf_succ (A B : R.M0 → Tr ι CS.Com → plan.Mfin → Coins Φ K → Prop) :
    ∀ (r k : ℕ) (tr : Tr ι CS.Com) (χ : Coins Φ K)
      (path : (protocol (colRounds Φ K CS.Com colRound I
        (finRound (succStmt R CS plan A) Ifin) r k)).tree.ExecutionPath),
      finalOf (succStmt R CS plan A) I Ifin r k tr χ path =
        finalOf (succStmt R CS plan B) I Ifin r k tr χ path
  | _, 0, _, _, _ => rfl
  | r, k + 1, tr, χ, path => by
    rw [finalOf, finalOf]
    exact finalOf_succ A B (r + 1) k _ _ path.2.2

/-- The extraction-success verifier = the succinct verifier and no CS failure. -/
theorem rapAccepts_ok_iff (p : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) :
    rapAccepts (succStmt R CS plan (okAccepts R CS plan)) I0 I Ifin nb p ↔
      rapAccepts (sStmt R CS plan) I0 I Ifin nb p ∧ ¬ ExtFailAt R CS plan I0 I Ifin nb p := by
  unfold rapAccepts ExtFailAt sFinal
  rw [finalOf_succ (okAccepts R CS plan) (succAccepts R CS plan)]
  exact ⟨fun h => ⟨h.1, not_not.mpr h.2⟩, fun h => ⟨h.1, not_not.mp h.2⟩⟩

/-- **`rap_succinct_sound`** (generic in the commitment scheme). -/
theorem rap_succinct_sound (hC : Certificate R blkOf nb) (hl : Link R CS plan) (err : ℕ → ℝ≥0∞)
    (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
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
        (∃ x, joint.1.1.1 = some x) ∧ ¬ R.Holds] ≤
      Q * Finset.univ.sup (sErrors R CS plan I0 I Ifin nb err) +
        ∑ j, sErrors R CS plan I0 I Ifin nb err j + εCS := by
  classical
  let Rok := succStmt R CS plan (okAccepts R CS plan)
  have hCok : Certificate Rok blkOf nb := certificate_ok hC hl
  have herr' : ∀ m0 r, roundBound Rok blkOf m0 r ≤ err r := fun m0 r => by
    rw [roundBound_succ]; exact herr m0 r
  let accOk : (Statement × GlobalSalt) → (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath →
      Bool := fun _ path => decide (rapAccepts Rok I0 I Ifin nb path)
  have hsplit := pr_accept_split guards accOk (sAccept R CS plan I0 I Ifin nb) adversary (¬ R.Holds)
    (fun _ p => ExtFailAt R CS plan I0 I Ifin nb p) (fun z p hacc => by
      by_cases hs : ExtFailAt R CS plan I0 I Ifin nb p
      · exact Or.inr hs
      · have h1 : rapAccepts (sStmt R CS plan) I0 I Ifin nb p := of_decide_eq_true hacc
        exact Or.inl (decide_eq_true ((rapAccepts_ok_iff p).mpr ⟨h1, hs⟩)))
  refine hsplit.trans (add_le_add ?_ hCS)
  -- the extraction-success part: the RAP bridge on the pulled-back summands
  have hrap := rap_singleSalt_knowledge_soundness (R := Rok) (blk := blkOf) (I0 := I0) (I := I)
    (Ifin := Ifin) (nb := nb) hCok err herr' guards adversary Set.univ
  have cost := singleSalt_query_cost guards accOk (rapErrors Rok I0 I Ifin nb err) adversary
  have keys := expectedSingleSaltAdversaryKeys_le_queryBound adversary Q queryBound
  refine le_trans (prEvent_mono _ _ _ ?_) (hrap.trans (cost.1.trans ?_))
  · rintro ⟨⟨⟨_ | ⟨z, p, w⟩, _⟩, _⟩, _⟩ ⟨⟨x, hx⟩, hH⟩
    · simp at hx
    · exact ⟨Set.mem_univ _, trivial, hH⟩
  · rw [mul_comm (Q : ℝ≥0∞)]
    exact add_le_add (mul_le_mul' le_rfl keys) cost.2

/-- **Perfect extractability gives `ε_CS = 0`**: the CS failure event has probability `0`. -/
theorem extFail_zero (hP : CS.PerfectlyExtractable)
    {Statement GlobalSalt Witness : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness (sRounds R CS plan I0 I Ifin nb)) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS plan I0 I Ifin nb) guards (sAccept R CS plan I0 I Ifin nb) adversary) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ ExtFailAt R CS plan I0 I Ifin nb p] = 0 := by
  classical
  rw [singleSaltAcceptedExecution_loggedRun, prEvent_map]
  refine prEvent_eq_zero_of_forall_not _ _ ?_
  rintro ⟨⟨⟨_ | ⟨z, p, w⟩, _⟩, _⟩, _⟩ ⟨z', p', w', hx, hf⟩
  · simp [acceptSingleSaltResult] at hx
  · simp only [acceptSingleSaltResult] at hx
    have hacc : sAccept R CS plan I0 I Ifin nb z p = true := by
      by_contra hn; simp [Option.filter, hn] at hx
    have hpp : p = p' := by
      simp only [Option.filter, hacc, ite_true, Option.some.injEq, Prod.mk.injEq] at hx
      exact hx.2.1
    subst hpp
    exact hf (hP _ _ _ (of_decide_eq_true hacc).1)

/-- **`rap_succinct_sound` at a perfectly extractable CS** (`ε_CS = 0`). -/
theorem rap_succinct_sound_perfect (hP : CS.PerfectlyExtractable) (hC : Certificate R blkOf nb)
    (hl : Link R CS plan) (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    {Statement GlobalSalt Witness : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness (sRounds R CS plan I0 I Ifin nb))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS plan I0 I Ifin nb) guards (sAccept R CS plan I0 I Ifin nb) adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ ¬ R.Holds] ≤
      Q * Finset.univ.sup (sErrors R CS plan I0 I Ifin nb err) +
        ∑ j, sErrors R CS plan I0 I Ifin nb err j := by
  have h := rap_succinct_sound hC hl err herr guards adversary Q queryBound 0
    (extFail_zero hP guards adversary).le
  rwa [add_zero] at h

end Sound

end NockvmE2E.Succ
