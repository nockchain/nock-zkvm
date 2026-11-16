/-
Merkle (B) e2e row 2: the RAP + DEEP + batched FRI
soundness for the PAIRED protocol `pairedRoundsK Dg (rapMask …) ++ (batchRound S :: friAltP.rounds)`.

There is no black-box reduction from the paired to the base protocol (a paired adversary varies the
roots and so re-draws challenges), so the extractor chain of `Succ/Fri.lean` is rebuilt on the paired
rounds, by the same method as W4A (FRI) and W4C (RAP alone):
`cExtP = appExt (rapExtractorP …) sufExtP`, with `sufExtP` the constant RAP terminal state or `consExt`
on `friAltP`. The theorem is over any round list `Rl` equal to the append, any acceptance `acc` that
implies `CAccP` on the cast path (`rap_fri_paired_sound`), and the DEEP instance reuses `deep_inputs`,
`link_deepPlan`, `deep_hbind` verbatim (`rap_fri_paired_sound_deep`).
-/
import NockvmE2E.Merkle.RapPaired
import NockvmE2E.Merkle.FriGlue
import NockvmE2E.Succ.FriDeep

open OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.RapFri

open NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Succ.App NockvmE2E.Succ.FriC NockvmE2E.FriPort
  NockvmE2E.FriPort.Batched NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Merkle

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
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B F] [Inhabited B]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l m : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)
variable {LF Dg : Type} [Finite Dg] [DecidableEq Dg] (md : RapP.RapMaskData colRound (β := β) LF Dg)

/-- The paired RAP prefix rounds: `pairedRoundsK Dg (rapMask …)`. -/
noncomputable abbrev r1P : List Round :=
  pairedRoundsK Dg (RapP.rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)

/-- The paired suffix rounds: the batching round, then FRI's paired rounds. -/
noncomputable abbrev r2P : List Round :=
  batchRound S :: (NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg).rounds

/-- What the paired RAP prefix of a path wrote: traces, coins, final message. -/
def fin1P (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg))).tree.ExecutionPath) :
    Tr ι β × Coins Φ K × plan.Mfin :=
  RapP.finalOfPK md (Rok R plan) I Ifin 0 nb (fun _ => default) (fun _ => default) p.2.2

variable (bstmt : R.M0 → Tr ι β → plan.Mfin → Coins Φ K → BStmt ω m)

/-- The batched-FRI statement a paired RAP prefix determines. -/
def stmtOfP (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg))).tree.ExecutionPath) : BStmt ω m :=
  bstmt p.1 (fin1P R plan I0 I Ifin nb md p).1 (fin1P R plan I0 I Ifin nb md p).2.2
    (fin1P R plan I0 I Ifin nb md p).2.1

/-- The RAP terminal proposition on a paired prefix. -/
def T1P (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg))).tree.ExecutionPath) : Prop :=
  St (Rok R plan) blkOf p.1 (fin1P R plan I0 I Ifin nb md p).1 (fin1P R plan I0 I Ifin nb md p).2.1 (0 + nb)

/-- The paired RAP extractor of `Rok`. -/
noncomputable abbrev E1P : RoundExtractor (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg))).tree (ks R.Holds) :=
  RapP.rapExtractorP md (Rok R plan) blkOf I0 I Ifin nb

theorem E1P_terminal (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg))).tree.ExecutionPath) :
    (E1P R plan I0 I Ifin nb md).terminalState p = ks (T1P R plan I0 I Ifin nb md p) :=
  RapP.rapExtractorP_terminal (md := md) (R := Rok R plan) (blk := blkOf) p

/-- The witness map at the junction (all witnesses are `PUnit`). -/
def junctionP (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg))).tree.ExecutionPath) :
    ((E1P R plan I0 I Ifin nb md).terminalState p).Witness :=
  (E1P_terminal R plan I0 I Ifin nb md p).symm ▸ PUnit.unit

variable (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (θ : ℝ) (δ : ℝ≥0)

open Classical in
/-- **The paired suffix extractor** on a paired RAP prefix `p`: the constant RAP terminal state if the
FRI statement is in the input language, else the batched extractor of `friAltP` (`consExt`). -/
noncomputable def sufExtP (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg))).tree.ExecutionPath) :
    RoundExtractor (protocol (r2P s d l (ω := ω) (S := S) (Dg := Dg))).tree
      ((E1P R plan I0 I Ifin nb md).terminalState p) :=
  if stmtOfP R plan I0 I Ifin nb m md bstmt p ∈ (inputRelation (ω := ω) s d m δ).language then
    reroot (constExt (T1P R plan I0 I Ifin nb md p) _) _ (fun _ => junctionP R plan I0 I Ifin nb md p)
  else
    reroot (consExt (NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg) (batchRound S)
      (stmtOfP R plan I0 I Ifin nb m md bstmt p ∈ (inputRelation (ω := ω) s d m δ).language)
      (fun cs => friState s d l (round_bound hdom) θ δ
        (combinedStmt s m G cs (stmtOfP R plan I0 I Ifin nb m md bstmt p)))) _
      (fun _ => junctionP R plan I0 I Ifin nb md p)

/-- **The combined paired extractor.** -/
noncomputable def cExtP :
    RoundExtractor (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg) ++ r2P s d l (ω := ω) (S := S) (Dg := Dg))).tree
      (ks R.Holds) :=
  appExt (r1P R plan I0 I Ifin nb md (Dg := Dg)) (E1P R plan I0 I Ifin nb md)
    (sufExtP R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ)

/-- The batched errors of the paired suffix: `ε` at the batching round, FRI's challenge errors after. -/
noncomputable def e2P (ε : ℝ≥0∞) : RoundErrors (r2P s d l (ω := ω) (S := S) (Dg := Dg)) :=
  fun j => Fin.cases ε ((NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg).roundErrors
    (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))) j

variable {R plan I0 I Ifin nb s d l m G bstmt hdom θ δ md}

theorem sufExtP_preserving (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg))).tree.ExecutionPath) :
    (sufExtP R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ (S := S) p).IsProverPreserving
      (protocol (r2P s d l (ω := ω) (S := S) (Dg := Dg))).roles := by
  unfold sufExtP
  split_ifs with h
  · exact reroot_preserving _ _ _
      (fun _ hT => holds_of_eq_ks (E1P_terminal R plan I0 I Ifin nb md p) _ hT) (constExt_preserving _ _)
  · exact reroot_preserving _ _ _ (fun _ hL => absurd hL h)
      (consExt_preserving _ _ _ _ (fun cs m' hm tr msg hafter => by
        by_contra hb
        exact Verifier.badEventState_prover_next _ _ m' hm _ tr hb msg hafter))

theorem sufExtP_bounded (ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg))).tree.ExecutionPath) :
    (sufExtP R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ (S := S) p).IsLocallyBounded
      (protocol (r2P s d l (ω := ω) (S := S) (Dg := Dg))).roles
      (roundErrorSchedule (r2P s d l (ω := ω) (S := S) (Dg := Dg))
        (e2P (ω := ω) s d l θ δ (S := S) (Dg := Dg) ε)) := by
  unfold sufExtP
  split_ifs with h
  · exact reroot_bounded _ _ _ _ (constExt_bounded _ _ _)
  · refine reroot_bounded _ _ _ _ ?_
    refine consExt_bounded (NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg) (batchRound S) _ _ (ε : ℝ≥0∞)
      (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞))
      (le_trans (prEvent_mono _ _ _ (fun c hc => hc.2))
        (le_trans (prEvent_mono _ _ _ ?_) (batching_error s d m G hdom δ ε hε _ h)))
      (fun cs => friState_challengeLaw_all s d l (round_bound hdom) θ δ _) _ rfl (fun _ => rfl)
    intro c hc
    rcases hc with hc | ⟨_, hi, _⟩
    · exact mem_inputLanguage_of_proximity s d hdom δ _ hc
    · exact absurd hi (Nat.not_lt_zero _)

theorem cExtP_terminal
    (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg) ++ r2P s d l (ω := ω) (S := S) (Dg := Dg))).tree.ExecutionPath) :
    (cExtP R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ).terminalState p =
      (sufExtP R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ (S := S)
        (fstPath (r1P R plan I0 I Ifin nb md (Dg := Dg)) p)).terminalState
          (sndPath (r1P R plan I0 I Ifin nb md (Dg := Dg)) p) :=
  appExt_terminal _ _ _ p

variable (R plan I0 I Ifin nb s d l m G bstmt hdom θ δ md)

/-- The FRI acceptance of a path of the paired FRI rounds: `queryBad` on the decoded legacy transcript. -/
def QOk (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (stmt : FriStmt (ω := ω) s)
    (path : (protocol (NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg).rounds).tree.ExecutionPath) : Prop :=
  queryBad s d l (round_bound hdom) (initialOracle s stmt)
    (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega)
      ((NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg).pathTranscript path))

theorem QOk_iff {Salt : Type} (z : FriStmt (ω := ω) s × Salt)
    (path : (protocol (NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg).rounds).tree.ExecutionPath) :
    NockvmE2E.Merkle.Fri.friAcceptsP s d l Dg hdom z path = true ↔ QOk s d l hdom z.1 path := by
  classical
  unfold NockvmE2E.Merkle.Fri.friAcceptsP QOk
  exact decide_eq_true_iff

/-- **What the paired combined verifier decides** on a path of `r1P ++ r2P`: the plan's residual check
on the paired RAP prefix, and FRI's query check on the decoded `friAltP` transcript of the combined
statement the prefix determines. -/
def CAccP (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg) ++ r2P s d l (ω := ω) (S := S) (Dg := Dg))).tree.ExecutionPath) :
    Prop :=
  plan.check (fstPath (r1P R plan I0 I Ifin nb md (Dg := Dg)) p).1
      (fin1P R plan I0 I Ifin nb md (fstPath (r1P R plan I0 I Ifin nb md (Dg := Dg)) p)).2.2
      (fin1P R plan I0 I Ifin nb md (fstPath (r1P R plan I0 I Ifin nb md (Dg := Dg)) p)).2.1 ∧
    QOk (Dg := Dg) s d l hdom
      (combinedStmt s m G (sndPath (r1P R plan I0 I Ifin nb md (Dg := Dg)) p).2.1
        (stmtOfP R plan I0 I Ifin nb m md bstmt (fstPath (r1P R plan I0 I Ifin nb md (Dg := Dg)) p)))
      (sndPath (r1P R plan I0 I Ifin nb md (Dg := Dg)) p).2.2

/-- The suffix terminal law at an arbitrary paired prefix `p1` and suffix `p2`. -/
theorem sufExtP_ks (hC : Certificate R blkOf nb) (hl : Link R (iopCS O) plan)
    (hbind : ∀ m0 tr fin χ, plan.check m0 fin χ →
      bstmt m0 tr fin χ ∈ (inputRelation (ω := ω) s d m δ).language →
      SatClaims O tr (plan.claims m0 fin χ))
    (p1 : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg))).tree.ExecutionPath)
    (p2 : (protocol (r2P s d l (ω := ω) (S := S) (Dg := Dg))).tree.ExecutionPath) :
    ∃ P : Prop, ((plan.check p1.1 (fin1P R plan I0 I Ifin nb md p1).2.2 (fin1P R plan I0 I Ifin nb md p1).2.1 ∧
        QOk (Dg := Dg) s d l hdom (combinedStmt s m G p2.2.1 (stmtOfP R plan I0 I Ifin nb m md bstmt p1))
          p2.2.2) → P) ∧
      (sufExtP R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ (S := S) p1).terminalState p2 = ks P := by
  classical
  unfold sufExtP
  split_ifs with h
  · refine ⟨T1P R plan I0 I Ifin nb md p1, fun hacc => ?_,
      (reroot_terminal _ _ _ _).trans (constExt_terminal _ _ _)⟩
    have hcheck := hacc.1
    have hsat := hbind _ _ _ _ hcheck h
    have hCok := certificate_ok hC hl
    have hok : (Rok R plan).Accepts p1.1 (fin1P R plan I0 I Ifin nb md p1).1
        (fin1P R plan I0 I Ifin nb md p1).2.2 (fin1P R plan I0 I Ifin nb md p1).2.1 :=
      ⟨⟨hsat, hcheck⟩, hsat⟩
    unfold T1P
    by_cases hf : ∃ s ∈ (Rok R plan).summands p1.1,
        s.mem (fin1P R plan I0 I Ifin nb md p1).1 (fin1P R plan I0 I Ifin nb md p1).2.1
    · obtain ⟨s, hs, hm⟩ := hf
      exact Or.inr ⟨s, hs, by have := hCok.blk_lt _ s hs; omega, hm⟩
    · push Not at hf
      exact Or.inl (hCok.sound _ _ _ _ hok hf)
  · refine ⟨friState s d l (round_bound hdom) θ δ
        (combinedStmt s m G p2.2.1 (stmtOfP R plan I0 I Ifin nb m md bstmt p1))
        (Fin.last _) ((NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg).pathTranscript p2.2.2), fun hacc => ?_,
      (reroot_terminal _ _ _ _).trans (consExt_terminalState _ _ _ _ _)⟩
    exact Or.inr ⟨queryChallenge s l, (queryChallenge s l).1.isLt,
      (badEvent_query s d l (round_bound hdom) θ _ _).mpr hacc.2⟩

/-- **The terminal law of the paired chain**: the combined terminal state is some `ks P`, and `P` holds
whenever `CAccP` does. -/
theorem cExtP_ks (hC : Certificate R blkOf nb) (hl : Link R (iopCS O) plan)
    (hbind : ∀ m0 tr fin χ, plan.check m0 fin χ →
      bstmt m0 tr fin χ ∈ (inputRelation (ω := ω) s d m δ).language →
      SatClaims O tr (plan.claims m0 fin χ))
    (p : (protocol (r1P R plan I0 I Ifin nb md (Dg := Dg) ++ r2P s d l (ω := ω) (S := S) (Dg := Dg))).tree.ExecutionPath) :
    ∃ P : Prop, (CAccP R plan I0 I Ifin nb s d l m G md bstmt hdom p → P) ∧
      (cExtP R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ).terminalState p = ks P := by
  rw [cExtP_terminal]
  exact sufExtP_ks R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ hC hl hbind _ _

theorem sum_e2P (ε : ℝ≥0∞) :
    ∑ j, e2P (ω := ω) s d l θ δ (S := S) (Dg := Dg) ε j =
      ε + (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞) := by
  show ∑ j : Fin ((NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg).rounds.length + 1),
      e2P (ω := ω) s d l θ δ (S := S) (Dg := Dg) ε j = _
  rw [Fin.sum_univ_succ]
  simp only [e2P, Fin.cases_zero, Fin.cases_succ]
  rw [(NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg).sum_roundErrors, ← ENNReal.ofNNReal_finsetSum,
    sum_challengeError]

theorem sup_e2P_le (ε : ℝ≥0∞) :
    Finset.univ.sup (e2P (ω := ω) s d l θ δ (S := S) (Dg := Dg) ε) ≤
      ε ⊔ Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)) := by
  refine Finset.sup_le (fun i _ => ?_)
  refine Fin.cases ?_ (fun t => ?_) i
  · exact le_sup_left
  · simp only [e2P, Fin.cases_succ]
    exact le_sup_of_le_right (by
      rw [← (NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg).sup_roundErrors]
      exact Finset.le_sup (f := (NockvmE2E.Merkle.Fri.friAltP (ω := ω) s d l Dg).roundErrors _)
        (Finset.mem_univ t))

/-- **for the paired protocol (generic form).** The staged RAP at the IOP commitment whose column
blocks are merkle (`rapMask`, paired rounds carry the roots), followed by batched FRI on the paired
rounds of `friAltP`, in ONE single-salt FS game on any round list `Rl` equal to the append. For every
guard schedule, every single-salt adversary with at most `Q` fresh keys, and every acceptance `acc` that
implies `CAccP` on the cast path:
`Pr[accepted ∧ ¬Holds] ≤` the right-hand side of `rap_fri_sound`. -/
theorem rap_fri_paired_sound (hC : Certificate R blkOf nb) (hl : Link R (iopCS O) plan)
    (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    (hbind : ∀ m0 tr fin χ, plan.check m0 fin χ →
      bstmt m0 tr fin χ ∈ (inputRelation (ω := ω) s d m δ).language →
      SatClaims O tr (plan.claims m0 fin χ))
    (ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {Statement GlobalSalt W : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (Rl : List Round)
    (eR : r1P R plan I0 I Ifin nb md (Dg := Dg) ++ r2P s d l (ω := ω) (S := S) (Dg := Dg) = Rl)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit Rl)
    (acc : Statement × GlobalSalt → (protocol Rl).tree.ExecutionPath → Bool)
    (hacc : ∀ z p, acc z p = true →
      CAccP R plan I0 I Ifin nb s d l m G md bstmt hdom (NockvmE2E.Merkle.Fri.castPath eR.symm p))
    (adversary : SingleSaltAdversary Statement GlobalSalt W Rl)
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution Rl guards acc adversary) ∅)}[
        (∃ x, joint.1.1.1 = some x) ∧ ¬ R.Holds] ≤
      Q * (Finset.univ.sup (rapErrors (Rok R plan) I0 I Ifin nb err) ⊔
          ((ε : ℝ≥0∞) ⊔ Finset.univ.sup (fun j => (challengeError (ω := ω) s d l θ δ j : ℝ≥0∞)))) +
        (∑ j, rapErrors (Rok R plan) I0 I Ifin nb err j +
          ((ε : ℝ≥0∞) +
            (((∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l : ℝ≥0) : ℝ≥0∞))) := by
  classical
  subst eR
  have hCok := certificate_ok hC hl
  have herr' : ∀ m0 r, roundBound (Rok R plan) blkOf m0 r ≤ err r := fun m0 r => by
    rw [roundBound_succ]; exact herr m0 r
  have h := singleSalt_knowledge_soundness_queryBound guards acc
    (appErr (r1P R plan I0 I Ifin nb md (Dg := Dg)) (fun j => RapP.rapErrs nb err j)
      (e2P (ω := ω) s d l θ δ (S := S) (Dg := Dg) (ε : ℝ≥0∞))) adversary
    (fun _ => ks R.Holds) (fun _ => cExtP R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ) Set.univ
    (fun _ _ => appExt_preserving _ _ _ (RapP.rapExtractorP_preserving hCok)
      (fun p => sufExtP_preserving p))
    (fun _ _ => appExt_bounded _ _ _ _ _ (RapP.rapExtractorP_bounded hCok err herr')
      (fun p => sufExtP_bounded ε hε p))
    (fun _ _ => R.Holds) (fun _ _ _ => True)
    (fun z p _ => Classical.choice (by
      obtain ⟨P, _, hP⟩ := cExtP_ks R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ hC hl hbind p
      exact ⟨hP ▸ PUnit.unit⟩))
    (fun _ _ => Iff.rfl)
    (fun z p _ hacc' _ => by
      obtain ⟨P, hPa, hP⟩ := cExtP_ks R plan I0 I Ifin nb s d l m G md bstmt hdom θ δ hC hl hbind p
      exact holds_of_eq_ks hP _ (hPa (hacc z p hacc')))
    Q queryBound
  rw [sum_appErr, sum_e2P] at h
  have hlen1 : (r1P R plan I0 I Ifin nb md (Dg := Dg)).length = nb + 2 := by
    show (pairedRoundsK Dg (RapP.rapMask Φ K md R.M0 plan.Mfin I0 I Ifin nb)).length = nb + 2
    rw [RapP.pairedRoundsK_rapMask]
    exact RapP.rapPairedRounds_length ..
  have hlen2 : (rounds (Rok R plan) I0 I Ifin nb).length = nb + 2 :=
    RapP.rapRounds_length ..
  obtain ⟨hs, hsum⟩ := RapP.sup_sum_cast (hlen1.trans hlen2.symm) (fun j => RapP.rapErrs nb err j)
  refine le_trans (prEvent_mono _ _ _ ?_) (h.trans ?_)
  · rintro ⟨⟨⟨_ | ⟨z, p, w⟩, _⟩, _⟩, _⟩ ⟨⟨x, hx⟩, hH⟩
    · simp at hx
    · exact ⟨Set.mem_univ _, trivial, hH⟩
  · rw [hsum]
    refine add_le_add (mul_le_mul' le_rfl ?_) le_rfl
    exact (sup_appErr_le _ _ _).trans (sup_le_sup (le_of_eq hs) (sup_e2P_le s d l θ δ _))

end

/-! ## The DEEP instance -/

section Deep

open NockvmE2E.Deep NockvmE2E.Succ.FriDeep

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
  (Ifin : OracleInterface (friPlan (ω := ω) P A R0 Rest RestV e).Mfin)
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)
variable {LF Dg : Type} [Finite Dg] [DecidableEq Dg]
  (md : RapP.RapMaskData P.colRoundX (β := Fin (2 ^ n) → B) LF Dg)

/-- **DEEP + batched FRI, for the PAIRED protocol** (column blocks and FRI folds carry their
Merkle root). The hypotheses and the bound are those of `rap_fri_sound_deep` (`Succ/FriDeep.lean:193`),
the bound expression being the same term; the game is on any round list `Rl` equal to
`pairedRoundsK Dg (rapMask …) ++ (batchRound S :: friAltP.rounds)`, with any acceptance `acc` implying
`CAccP` on the cast path. -/
theorem rap_fri_paired_sound_deep {nb : ℕ} (hR0 : RapInput R0 nb)
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
    (Rl : List Round)
    (eR : r1P (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb md (Dg := Dg) ++
      r2P s d l (ω := ω) (S := S) (Dg := Dg) = Rl)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit Rl)
    (acc : Statement × GlobalSalt → (protocol Rl).tree.ExecutionPath → Bool)
    (hacc : ∀ z p, acc z p = true →
      CAccP (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb s d l m G md
        (fun _ tr fin χ => deepStmt (ω := ω) P A R0 e tr fin χ) hdom (NockvmE2E.Merkle.Fri.castPath eR.symm p))
    (adversary : SingleSaltAdversary Statement GlobalSalt W Rl)
    (Q : ℕ) (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution Rl guards acc adversary) ∅)}[
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
  exact rap_fri_paired_sound (R := P.statement R0 Rest) (plan := friPlan (ω := ω) P A R0 Rest RestV e)
    (I0 := I0) (I := I) (Ifin := Ifin) (nb := nb) (s := s) (d := d) (l := l) (m := m) (G := G) (md := md)
    (bstmt := fun _ tr fin χ => deepStmt (ω := ω) P A R0 e tr fin χ) (hdom := hdom) (θ := θ) (δ := δ)
    hC hl (errDeep P errOld)
    (fun m0 r => by
      refine (roundBound_deep P R0 Rest m0 r).le.trans ?_
      unfold errDeep
      gcongr
      exact herr0 m0 r)
    (fun _ tr fin χ hcheck hmem =>
      deep_hbind P A R0 e hN hδ htoPoly tr fin χ hcheck.2.1 hmem)
    ε hε Rl eR guards acc hacc adversary Q queryBound

theorem rhs_agree {A B A' B' : ℝ≥0∞} (_ : A ≤ B) (_ : A' ≤ B') (h : B = B') : True := trivial

/-- **Check that the paired bound is the same expression** as `rap_fri_sound_deep`'s: the two bounds are
unified (by `rfl`) from the instances of the two theorems at the same parameters. -/
theorem rhs_check {nb : ℕ} (hR0 : RapInput R0 nb)
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
    (guardsL : GuardSchedule (Statement × GlobalSalt) PUnit
      (cRounds (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb
        (ω := ω) (S := S) s d l))
    (advL : SingleSaltAdversary Statement GlobalSalt W
      (cRounds (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb
        (ω := ω) (S := S) s d l))
    (Q : ℕ) (qbL : ∀ phase ∈ support (randomOracleLoggedRun advL.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit
      (r1P (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb md (Dg := Dg) ++
        r2P s d l (ω := ω) (S := S) (Dg := Dg)))
    (acc : Statement × GlobalSalt → (protocol
      (r1P (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb md (Dg := Dg) ++
        r2P s d l (ω := ω) (S := S) (Dg := Dg))).tree.ExecutionPath → Bool)
    (hacc : ∀ z p, acc z p = true →
      CAccP (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb s d l m G md
        (fun _ tr fin χ => deepStmt (ω := ω) P A R0 e tr fin χ) hdom
        (NockvmE2E.Merkle.Fri.castPath (Eq.refl _).symm p))
    (adversary : SingleSaltAdversary Statement GlobalSalt W
      (r1P (P.statement R0 Rest) (friPlan (ω := ω) P A R0 Rest RestV e) I0 I Ifin nb md (Dg := Dg) ++
        r2P s d l (ω := ω) (S := S) (Dg := Dg)))
    (qb : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) : True :=
  rhs_agree
    (NockvmE2E.Succ.FriDeep.rap_fri_sound_deep (P := P) (A := A) (R0 := R0) (Rest := Rest) (RestV := RestV)
      (e := e) (I0 := I0) (I := I) (Ifin := Ifin) (s := s) (d := d) (l := l) (G := G)
      hR0 hlink hnb hRest errOld herr0 hdom θ δ hN hδ htoPoly ε hε guardsL advL Q qbL)
    (rap_fri_paired_sound_deep (P := P) (A := A) (R0 := R0) (Rest := Rest) (RestV := RestV)
      (e := e) (I0 := I0) (I := I) (Ifin := Ifin) (s := s) (d := d) (l := l) (G := G) (md := md)
      hR0 hlink hnb hRest errOld herr0 hdom θ δ hN hδ htoPoly ε hε _ rfl guards acc hacc adversary Q qb)
    rfl

end Deep

end NockvmE2E.Merkle.RapFri
