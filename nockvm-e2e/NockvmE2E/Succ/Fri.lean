/-
the staged RAP with its openings checked by
batched FRI, in ONE single-salt Fiat–Shamir game.

Protocol: `cRounds = sRounds ++ batchedRounds`: the succinct RAP rounds of `Succ/Statement.lean` at the
IOP commitment `iopCS O` (commitments = the committed data, ideal oracles, NO Merkle), followed by the
batching round and FRI's rounds. The verifier `cAccept` checks the plan's residual check on the
opened values (`plan.check`) and batched FRI on the statement `bstmt` the RAP transcript determines
(for DEEP: the DEEP quotient words of the committed words). It does NOT check the opening claims
themselves: that is what FRI is for. The one bridge hypothesis is `hbind`: on a transcript passing
`plan.check`, membership of `bstmt` in batched FRI's input language makes the claims true
(`Deep/UDFri.deep_of_inputRelation` + unique decoding, discharged for DEEP in `Succ/FriDeep.lean`).

* `rap_fri_sound` (generic in the RAP, the oracle interface `O` and the plan):
  `Pr[accepted ∧ ¬Holds] ≤ Q·(max_j rapErr_j ⊔ (ε ⊔ max_j cErr_j)) + (Σ_j rapErr_j + (ε + Σ foldErr + (1−min θ δ)^l))`.

The extractor (`cExt`) is `App.appExt` of the RAP extractor of the extraction-success statement
`Rok` (the RAP pulled back along `ext = id`, accepting iff the plan's check and the claims hold) and,
per prefix path, either the constant RAP terminal state (when `bstmt ∈ L`) or FRI's batched extractor
`consExt` (when `bstmt ∉ L`, whose input state is then false).
-/
import NockvmE2E.Succ.Append
import NockvmE2E.Succ.Statement
import NockvmE2E.FriPort.BatchedSoundness

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec ProtocolSpec
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

namespace NockvmE2E.Succ.FriC

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Succ.App NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Lift NockvmE2E.Lift.Alternating

section

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  [Inhabited β]
  (R : RapStatement Φ K ι β colRound) (plan : OpenPlan R (iopCS O))
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound β r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ)

variable {F : Type} [NonBinaryField F] [Fintype F] [SampleableType F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l m : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)

/-- The extraction-success statement: the RAP over the committed (= extracted, `ext = id`) data,
accepting iff the plan's check holds and the claims are true. -/
abbrev Rok : RapStatement Φ K ι β colRound :=
  succStmt R (iopCS O) plan (okAccepts R (iopCS O) plan)

/-- The RAP prefix rounds (`= sRounds R (iopCS O) plan …`). -/
noncomputable abbrev r1 : List Round := rounds (Rok R plan) I0 I Ifin nb

/-- **The combined protocol**: the succinct RAP rounds, then batched FRI. -/
noncomputable abbrev cRounds : List Round :=
  r1 R plan I0 I Ifin nb ++ batchedRounds (ω := ω) (S := S) s d l

/-- What the RAP prefix of a path wrote: traces, coins, final message. -/
def fin1 (p : (protocol (r1 R plan I0 I Ifin nb)).tree.ExecutionPath) :
    Tr ι β × Coins Φ K × plan.Mfin :=
  finalOf (Rok R plan) I Ifin 0 nb (fun _ => default) (fun _ => default) p.2.2

variable (bstmt : R.M0 → Tr ι β → plan.Mfin → Coins Φ K → BStmt ω m)

/-- The batched-FRI statement a RAP prefix determines. -/
def stmtOf (p : (protocol (r1 R plan I0 I Ifin nb)).tree.ExecutionPath) : BStmt ω m :=
  bstmt p.1 (fin1 R plan I0 I Ifin nb p).1 (fin1 R plan I0 I Ifin nb p).2.2
    (fin1 R plan I0 I Ifin nb p).2.1

/-- **The combined verifier**: the plan's residual check on the RAP prefix, and batched FRI on the
statement it determines. -/
noncomputable def cAccept (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) {Input Salt : Type}
    (z : Input × Salt)
    (p : (protocol (cRounds R plan I0 I Ifin nb (ω := ω) (S := S) s d l)).tree.ExecutionPath) : Bool :=
  open Classical in
  decide (plan.check (fstPath (r1 R plan I0 I Ifin nb) p).1
      (fin1 R plan I0 I Ifin nb (fstPath (r1 R plan I0 I Ifin nb) p)).2.2
      (fin1 R plan I0 I Ifin nb (fstPath (r1 R plan I0 I Ifin nb) p)).2.1) &&
    batchedAccepts s d l m G hdom (stmtOf R plan I0 I Ifin nb m bstmt (fstPath (r1 R plan I0 I Ifin nb) p), z.2)
      (sndPath (r1 R plan I0 I Ifin nb) p)

/-- The RAP terminal proposition on a prefix (`rapExtractor_terminal`). -/
def T1 (p : (protocol (r1 R plan I0 I Ifin nb)).tree.ExecutionPath) : Prop :=
  St (Rok R plan) blkOf p.1 (fin1 R plan I0 I Ifin nb p).1 (fin1 R plan I0 I Ifin nb p).2.1 (0 + nb)

/-- The RAP extractor of `Rok`. -/
noncomputable abbrev E1 : RoundExtractor (protocol (r1 R plan I0 I Ifin nb)).tree (ks R.Holds) :=
  rapExtractor (Rok R plan) blkOf I0 I Ifin nb

theorem E1_terminal (p : (protocol (r1 R plan I0 I Ifin nb)).tree.ExecutionPath) :
    (E1 R plan I0 I Ifin nb).terminalState p = ks (T1 R plan I0 I Ifin nb p) :=
  rapExtractor_terminal p

/-- The witness map at the junction (all witnesses are `PUnit`). -/
def junction (p : (protocol (r1 R plan I0 I Ifin nb)).tree.ExecutionPath) :
    ((E1 R plan I0 I Ifin nb).terminalState p).Witness :=
  (E1_terminal R plan I0 I Ifin nb p).symm ▸ PUnit.unit

variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (θ : ℝ) (δ : ℝ≥0)

open Classical in
/-- **The suffix extractor** on a RAP prefix `p`: the constant RAP terminal state if the FRI statement
is in the input language, else FRI's batched extractor (input state "statement ∈ L", false here). -/
noncomputable def sufExt (p : (protocol (r1 R plan I0 I Ifin nb)).tree.ExecutionPath) :
    RoundExtractor (protocol (batchedRounds (ω := ω) (S := S) s d l)).tree
      ((E1 R plan I0 I Ifin nb).terminalState p) :=
  if stmtOf R plan I0 I Ifin nb m bstmt p ∈ (inputRelation (ω := ω) s d m δ).language then
    reroot (constExt (T1 R plan I0 I Ifin nb p) _) _ (fun _ => junction R plan I0 I Ifin nb p)
  else
    reroot (consExt (friAlt (ω := ω) s d l) (batchRound S)
      (stmtOf R plan I0 I Ifin nb m bstmt p ∈ (inputRelation (ω := ω) s d m δ).language)
      (fun cs => friState s d l (round_bound hdom) θ δ
        (combinedStmt s m G cs (stmtOf R plan I0 I Ifin nb m bstmt p)))) _
      (fun _ => junction R plan I0 I Ifin nb p)

/-- **The combined extractor.** -/
noncomputable def cExt :
    RoundExtractor (protocol (cRounds R plan I0 I Ifin nb (ω := ω) (S := S) s d l)).tree (ks R.Holds) :=
  appExt (r1 R plan I0 I Ifin nb) (E1 R plan I0 I Ifin nb)
    (sufExt R plan I0 I Ifin nb s d l m G bstmt hdom θ δ)

/-- The batched errors: `ε` at the batching round, FRI's challenge errors after. -/
noncomputable def e2 (ε : ℝ≥0∞) : RoundErrors (batchedRounds (ω := ω) (S := S) s d l) :=
  fun j => Fin.cases ε ((friAlt (ω := ω) s d l).roundErrors
    (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))) j

variable {R plan I0 I Ifin nb s d l m G bstmt hdom θ δ}

theorem sufExt_preserving (p : (protocol (r1 R plan I0 I Ifin nb)).tree.ExecutionPath) :
    (sufExt R plan I0 I Ifin nb s d l m G bstmt hdom θ δ (S := S) p).IsProverPreserving
      (protocol (batchedRounds (ω := ω) (S := S) s d l)).roles := by
  unfold sufExt
  split_ifs with h
  · exact reroot_preserving _ _ _
      (fun _ hT => holds_of_eq_ks (E1_terminal R plan I0 I Ifin nb p) _ hT) (constExt_preserving _ _)
  · exact reroot_preserving _ _ _ (fun _ hL => absurd hL h)
      (consExt_preserving _ _ _ _ (fun cs m' hm tr msg hafter => by
        by_contra hb
        exact Verifier.badEventState_prover_next _ _ m' hm _ tr hb msg hafter))

theorem sufExt_bounded (ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    (p : (protocol (r1 R plan I0 I Ifin nb)).tree.ExecutionPath) :
    (sufExt R plan I0 I Ifin nb s d l m G bstmt hdom θ δ (S := S) p).IsLocallyBounded
      (protocol (batchedRounds (ω := ω) (S := S) s d l)).roles
      (roundErrorSchedule (batchedRounds (ω := ω) (S := S) s d l) (e2 (ω := ω) s d l θ δ (S := S) ε)) := by
  unfold sufExt
  split_ifs with h
  · exact reroot_bounded _ _ _ _ (constExt_bounded _ _ _)
  · refine reroot_bounded _ _ _ _ ?_
    refine consExt_bounded (friAlt (ω := ω) s d l) (batchRound S) _ _ (ε : ℝ≥0∞)
      (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))
      (le_trans (prEvent_mono _ _ _ (fun c hc => hc.2))
        (le_trans (prEvent_mono _ _ _ ?_) (batching_error s d m G hdom δ ε hε _ h)))
      (fun cs => friState_challengeLaw_all s d l (round_bound hdom) θ δ _) _ rfl (fun _ => rfl)
    intro c hc
    rcases hc with hc | ⟨_, hi, _⟩
    · exact mem_inputLanguage_of_proximity s d hdom δ _ hc
    · exact absurd hi (Nat.not_lt_zero _)

theorem cExt_terminal (p : (protocol (cRounds R plan I0 I Ifin nb (ω := ω) (S := S) s d l)).tree.ExecutionPath) :
    (cExt R plan I0 I Ifin nb s d l m G bstmt hdom θ δ).terminalState p =
      (sufExt R plan I0 I Ifin nb s d l m G bstmt hdom θ δ (S := S)
        (fstPath (r1 R plan I0 I Ifin nb) p)).terminalState (sndPath (r1 R plan I0 I Ifin nb) p) :=
  appExt_terminal _ _ _ p

/-- The suffix terminal law, at an arbitrary prefix `p1` and suffix `p2`. -/
theorem sufExt_ks (hC : Certificate R blkOf nb) (hl : Link R (iopCS O) plan)
    (hbind : ∀ m0 tr fin χ, plan.check m0 fin χ →
      bstmt m0 tr fin χ ∈ (inputRelation (ω := ω) s d m δ).language →
      SatClaims O tr (plan.claims m0 fin χ))
    {Salt : Type} (salt : Salt) (p1 : (protocol (r1 R plan I0 I Ifin nb)).tree.ExecutionPath)
    (p2 : (protocol (batchedRounds (ω := ω) (S := S) s d l)).tree.ExecutionPath) :
    ∃ P : Prop, ((open Classical in decide (plan.check p1.1 (fin1 R plan I0 I Ifin nb p1).2.2
        (fin1 R plan I0 I Ifin nb p1).2.1) &&
        batchedAccepts s d l m G hdom (stmtOf R plan I0 I Ifin nb m bstmt p1, salt) p2) = true → P) ∧
      (sufExt R plan I0 I Ifin nb s d l m G bstmt hdom θ δ (S := S) p1).terminalState p2 = ks P := by
  classical
  unfold sufExt
  split_ifs with h
  · refine ⟨T1 R plan I0 I Ifin nb p1, fun hacc => ?_,
      (reroot_terminal _ _ _ _).trans (constExt_terminal _ _ _)⟩
    have hacc1 := (Bool.and_eq_true _ _).mp hacc
    have hcheck := of_decide_eq_true hacc1.1
    have hsat := hbind _ _ _ _ hcheck h
    have hCok := certificate_ok hC hl
    have hok : (Rok R plan).Accepts p1.1 (fin1 R plan I0 I Ifin nb p1).1
        (fin1 R plan I0 I Ifin nb p1).2.2 (fin1 R plan I0 I Ifin nb p1).2.1 :=
      ⟨⟨hsat, hcheck⟩, hsat⟩
    unfold T1
    by_cases hf : ∃ s ∈ (Rok R plan).summands p1.1,
        s.mem (fin1 R plan I0 I Ifin nb p1).1 (fin1 R plan I0 I Ifin nb p1).2.1
    · obtain ⟨s, hs, hm⟩ := hf
      exact Or.inr ⟨s, hs, by have := hCok.blk_lt _ s hs; omega, hm⟩
    · push Not at hf
      exact Or.inl (hCok.sound _ _ _ _ hok hf)
  · refine ⟨friState s d l (round_bound hdom) θ δ
        (combinedStmt s m G p2.2.1 (stmtOf R plan I0 I Ifin nb m bstmt p1))
        (Fin.last _) ((friAlt (ω := ω) s d l).pathTranscript p2.2.2), fun hacc => ?_,
      (reroot_terminal _ _ _ _).trans (consExt_terminalState _ _ _ _ _)⟩
    have hacc2 := ((Bool.and_eq_true _ _).mp hacc).2
    exact Or.inr ⟨queryChallenge s l, (queryChallenge s l).1.isLt,
      (badEvent_query s d l (round_bound hdom) θ _ _).mpr
        ((friAccepts_iff s d l hdom
          (combinedStmt s m G p2.2.1 (stmtOf R plan I0 I Ifin nb m bstmt p1), salt) p2.2.2).mp hacc2)⟩

/-- **The terminal law**: the combined terminal state is some `ks P`, and `P` holds on accepted paths. -/
theorem cExt_ks (hC : Certificate R blkOf nb) (hl : Link R (iopCS O) plan)
    (hbind : ∀ m0 tr fin χ, plan.check m0 fin χ →
      bstmt m0 tr fin χ ∈ (inputRelation (ω := ω) s d m δ).language →
      SatClaims O tr (plan.claims m0 fin χ))
    {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (cRounds R plan I0 I Ifin nb (ω := ω) (S := S) s d l)).tree.ExecutionPath) :
    ∃ P : Prop, (cAccept R plan I0 I Ifin nb s d l m G bstmt hdom z p = true → P) ∧
      (cExt R plan I0 I Ifin nb s d l m G bstmt hdom θ δ).terminalState p = ks P := by
  rw [cExt_terminal]
  exact sufExt_ks hC hl hbind z.2 _ _

theorem sum_e2 (ε : ℝ≥0∞) :
    ∑ j, e2 (ω := ω) s d l θ δ (S := S) ε j =
      ε + (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞) := by
  show ∑ j : Fin ((friAlt (ω := ω) s d l).rounds.length + 1), e2 (ω := ω) s d l θ δ (S := S) ε j = _
  rw [Fin.sum_univ_succ]
  simp only [e2, Fin.cases_zero, Fin.cases_succ]
  rw [(friAlt (ω := ω) s d l).sum_roundErrors, ← ENNReal.ofNNReal_finsetSum, sum_challengeError]

theorem sup_e2_le (ε : ℝ≥0∞) :
    Finset.univ.sup (e2 (ω := ω) s d l θ δ (S := S) ε) ≤
      ε ⊔ Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)) := by
  refine Finset.sup_le (fun i _ => ?_)
  refine Fin.cases ?_ (fun t => ?_) i
  · exact le_sup_left
  · simp only [e2, Fin.cases_succ]
    exact le_sup_of_le_right (by
      rw [← (friAlt (ω := ω) s d l).sup_roundErrors]
      exact Finset.le_sup (f := (friAlt (ω := ω) s d l).roundErrors _) (Finset.mem_univ t))

/-- **the FRI instance (generic form).** The staged RAP at the IOP commitment (ideal oracles,
no Merkle), with its opening claims replaced by batched FRI on `bstmt` (one single-salt FS game,
`cRounds = sRounds ++ batchedRounds`): for every guard schedule and every single-salt adversary with
at most `Q` fresh keys,
`Pr[accepted ∧ ¬Holds] ≤ Q·(max rapErr ⊔ (ε ⊔ max cErr)) + (Σ rapErr + (ε + Σ foldErr + (1−min θ δ)^l))`.
Inputs: the RAP certificate `hC`, the plan's `Link`, the per-round bound `herr`, FRI's generator bound
`hε`, and `hbind` (the plan's check + `bstmt ∈ L` ⇒ the claims hold). -/
theorem rap_fri_sound (hC : Certificate R blkOf nb) (hl : Link R (iopCS O) plan)
    (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    (hbind : ∀ m0 tr fin χ, plan.check m0 fin χ →
      bstmt m0 tr fin χ ∈ (inputRelation (ω := ω) s d m δ).language →
      SatClaims O tr (plan.claims m0 fin χ))
    (ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {Statement GlobalSalt W : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit
      (cRounds R plan I0 I Ifin nb (ω := ω) (S := S) s d l))
    (adversary : SingleSaltAdversary Statement GlobalSalt W
      (cRounds R plan I0 I Ifin nb (ω := ω) (S := S) s d l))
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (cRounds R plan I0 I Ifin nb (ω := ω) (S := S) s d l) guards
        (cAccept R plan I0 I Ifin nb s d l m G bstmt hdom) adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ ¬ R.Holds] ≤
      Q * (Finset.univ.sup (rapErrors (Rok R plan) I0 I Ifin nb err) ⊔
          ((ε : ℝ≥0∞) ⊔ Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)))) +
        (∑ j, rapErrors (Rok R plan) I0 I Ifin nb err j +
          ((ε : ℝ≥0∞) +
            (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞))) := by
  classical
  have hCok := certificate_ok hC hl
  have herr' : ∀ m0 r, roundBound (Rok R plan) blkOf m0 r ≤ err r := fun m0 r => by
    rw [roundBound_succ]; exact herr m0 r
  have h := singleSalt_knowledge_soundness_queryBound guards
    (cAccept R plan I0 I Ifin nb s d l m G bstmt hdom)
    (appErr (r1 R plan I0 I Ifin nb) (rapErrors (Rok R plan) I0 I Ifin nb err)
      (e2 (ω := ω) s d l θ δ (S := S) (ε : ℝ≥0∞))) adversary
    (fun _ => ks R.Holds) (fun _ => cExt R plan I0 I Ifin nb s d l m G bstmt hdom θ δ) Set.univ
    (fun _ _ => appExt_preserving _ _ _ (rapExtractor_preserving hCok)
      (fun p => sufExt_preserving p))
    (fun _ _ => appExt_bounded _ _ _ _ _ (rapExtractor_bounded hCok err herr')
      (fun p => sufExt_bounded ε hε p))
    (fun _ _ => R.Holds) (fun _ _ _ => True)
    (fun z p _ => Classical.choice (by
      obtain ⟨P, _, hP⟩ := cExt_ks (θ := θ) (δ := δ) hC hl hbind z p
      exact ⟨hP ▸ PUnit.unit⟩))
    (fun _ _ => Iff.rfl)
    (fun z p _ hacc _ => by
      obtain ⟨P, hPa, hP⟩ := cExt_ks (θ := θ) (δ := δ) hC hl hbind z p
      exact holds_of_eq_ks hP _ (hPa hacc))
    Q queryBound
  rw [sum_appErr, sum_e2] at h
  refine le_trans (prEvent_mono _ _ _ ?_) (h.trans ?_)
  · rintro ⟨⟨⟨_ | ⟨z, p, w⟩, _⟩, _⟩, _⟩ ⟨⟨x, hx⟩, hH⟩
    · simp at hx
    · exact ⟨Set.mem_univ _, trivial, hH⟩
  · refine add_le_add_left (mul_le_mul' le_rfl ?_) _
    exact (sup_appErr_le _ _ _).trans (sup_le_sup_left (sup_e2_le _) _)

end

end NockvmE2E.Succ.FriC
