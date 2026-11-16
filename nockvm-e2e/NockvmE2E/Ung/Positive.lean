/-
the POSITIVE theorem `rap_succinct_unique`.

Part A (this section): the single-path "no non-canonical accepted path" bound. With `AirDet` (a canonical
round-0 message `m0₀` and trace `tr₀`), an accepted path whose extracted columns are not `tr₀` (or whose round-0
message is not `m0₀`) is a soundness failure: it is the SAME bridge as `rap_succinct_sound`
(`rap_singleSalt_knowledge_soundness`) applied to the statement `ndStmt` — the succinct statement whose
acceptance additionally demands non-canonicity and whose `Holds` is `False`.
-/
import NockvmE2E.Ung.Defs
import NockvmE2E.Ung.AirDet

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped ENNReal

namespace NockvmE2E.Ung

open NockvmE2E.Rap NockvmE2E.Succ

/-! ## A. A path-dependent union bound between two terminal checks -/

section Split

variable {rounds : List Round} {Statement GlobalSalt Witness : Type}
  [DecidableEq Statement] [DecidableEq GlobalSalt]

/-- `pr_accept_split` with a PATH-DEPENDENT event `E` (new lemma; the old one is unchanged). -/
theorem pr_accept_split_ev (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (acc₁ acc₂ : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (adversary : SingleSaltAdversary Statement GlobalSalt Witness rounds)
    (E fail : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Prop)
    (h : ∀ z p, acc₂ z p = true → E z p → acc₁ z p = true ∨ fail z p) :
    Pr{let joint ← (randomOracleLoggedRun
        (singleSaltAcceptedExecution rounds guards acc₂ adversary) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ E z p] ≤
      Pr{let joint ← (randomOracleLoggedRun
        (singleSaltAcceptedExecution rounds guards acc₁ adversary) ∅)}[
        ∃ x, joint.1.1.1 = some x] +
      Pr{let joint ← (randomOracleLoggedRun
        (singleSaltAcceptedExecution rounds guards acc₂ adversary) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ fail z p] := by
  rw [singleSaltAcceptedExecution_loggedRun guards acc₂, singleSaltAcceptedExecution_loggedRun guards acc₁,
    prEvent_map, prEvent_map, prEvent_map]
  refine le_trans (prEvent_mono _ _ _ ?_) (prEvent_or_le _ _ _)
  rintro ⟨⟨⟨sel, log⟩, log'⟩, cache⟩ ⟨z, p, w, hx, hE⟩
  simp only [acceptSingleSaltResult] at hx ⊢
  rcases sel with _ | ⟨z', p', w'⟩
  · simp at hx
  · simp only [Option.filter] at hx
    split_ifs at hx with hacc
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    rcases h z' p' hacc hE with h1 | h2
    · exact Or.inl ⟨(z', p', w'), by simp [Option.filter, h1]⟩
    · exact Or.inr ⟨z', p', w', by simp [Option.filter, hacc], h2⟩

end Split

/-! ## B. Non-canonical accepted paths are soundness failures -/

section NonCanon

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ) (m0₀ : R.M0) (tr₀ : Tr ι β)

/-- A path is NON-CANONICAL: its round-0 message is not `m0₀`, or the columns extracted from its commitments
are not `tr₀`. -/
def NonCanon (path : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) : Prop :=
  path.1 ≠ m0₀ ∨ (fun j => CS.ext ((sFinal R CS plan I0 I Ifin nb path).1 j)) ≠ tr₀

/-- The statement whose acceptance is "succinct-accepted, extraction succeeded, AND non-canonical"; `Holds` is
`False`, so every acceptance is a soundness failure. -/
abbrev ndStmt : RapStatement Φ K ι CS.Com colRound :=
  { succStmt R CS plan (fun m0 coms fin χ => okAccepts R CS plan m0 coms fin χ ∧
      (m0 ≠ m0₀ ∨ (fun j => CS.ext (coms j)) ≠ tr₀)) with Holds := False }

variable {R CS plan I0 I Ifin nb m0₀ tr₀}

theorem finalOf_nd : ∀ (r k : ℕ) (tr : Tr ι CS.Com) (χ : Coins Φ K)
    (path : (protocol (colRounds Φ K CS.Com colRound I
      (finRound (ndStmt R CS plan m0₀ tr₀) Ifin) r k)).tree.ExecutionPath),
    finalOf (ndStmt R CS plan m0₀ tr₀) I Ifin r k tr χ path =
      finalOf (succStmt R CS plan (succAccepts R CS plan)) I Ifin r k tr χ path
  | _, 0, _, _, _ => rfl
  | r, k + 1, tr, χ, path => by
    rw [finalOf, finalOf]
    exact finalOf_nd (r + 1) k _ _ path.2.2

theorem rapAccepts_nd_iff (p : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) :
    rapAccepts (ndStmt R CS plan m0₀ tr₀) I0 I Ifin nb p ↔
      rapAccepts (sStmt R CS plan) I0 I Ifin nb p ∧ ¬ ExtFailAt R CS plan I0 I Ifin nb p ∧
        NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p := by
  unfold rapAccepts
  rw [finalOf_nd]
  unfold ExtFailAt NonCanon sFinal
  simp only [ndStmt, succStmt, okAccepts, not_not]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

theorem roundBound_nd (m0 : R.M0) (r : ℕ) :
    roundBound (ndStmt R CS plan m0₀ tr₀) blkOf m0 r = roundBound R blkOf m0 r := by
  simp only [roundBound, List.map_map]
  rfl

/-- `ndStmt` satisfies the bridge's `Certificate`: with `AirDet`, an accepted non-canonical path off all
summands is impossible (`SoundG` with `Holds = False`). -/
theorem certificate_nd (hC : Certificate R blkOf nb) (hl : Link R CS plan)
    (hD : ∀ (m0 : R.M0) (tr : Tr ι β) (fin : R.Mfin) (χ : Coins Φ K), R.Accepts m0 tr fin χ →
      (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → m0 = m0₀ ∧ tr = tr₀) :
    Certificate (ndStmt R CS plan m0₀ tr₀) blkOf nb where
  sound m0 coms fin χ hacc hall := by
    obtain ⟨hok, hnd⟩ := hacc
    have hA := hl m0 _ fin χ hok.1.2 hok.2
    obtain ⟨h1, h2⟩ := hD m0 _ (plan.finOf fin) χ hA
      (fun s hs hm => hall (pullS CS s) (List.mem_map_of_mem hs) hm)
    exact hnd.elim (fun h => h h1) (fun h => h h2)
  local_ m0 s' hs' := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
    exact local_pullS CS (hC.local_ m0 s hs)
  blk_lt m0 s' hs' := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
    exact hC.blk_lt m0 s hs

variable (R CS plan I0 I Ifin nb m0₀ tr₀)

/-- **No non-canonical accepted path** (single path): with `AirDet`, the probability that an adversary with ≤ `Q`
fresh keys gets an accepted path that is non-canonical is at most the `rap_succinct_sound` bound. -/
theorem rap_succinct_noncanon (hC : Certificate R blkOf nb) (hl : Link R CS plan)
    (hD : ∀ (m0 : R.M0) (tr : Tr ι β) (fin : R.Mfin) (χ : Coins Φ K), R.Accepts m0 tr fin χ →
      (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → m0 = m0₀ ∧ tr = tr₀)
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
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p] ≤
      Q * Finset.univ.sup (sErrors R CS plan I0 I Ifin nb err) +
        ∑ j, sErrors R CS plan I0 I Ifin nb err j + εCS := by
  classical
  let Rnd := ndStmt R CS plan m0₀ tr₀
  have hCnd : Certificate Rnd blkOf nb := certificate_nd hC hl hD
  have herr' : ∀ m0 r, roundBound Rnd blkOf m0 r ≤ err r := fun m0 r => by
    rw [roundBound_nd]; exact herr m0 r
  let accND : (Statement × GlobalSalt) → (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath →
      Bool := fun _ path => decide (rapAccepts Rnd I0 I Ifin nb path)
  have hsplit := pr_accept_split_ev guards accND (sAccept R CS plan I0 I Ifin nb) adversary
    (fun _ p => NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p)
    (fun _ p => ExtFailAt R CS plan I0 I Ifin nb p) (fun z p hacc hnc => by
      by_cases hs : ExtFailAt R CS plan I0 I Ifin nb p
      · exact Or.inr hs
      · have h1 : rapAccepts (sStmt R CS plan) I0 I Ifin nb p := of_decide_eq_true hacc
        exact Or.inl (decide_eq_true ((rapAccepts_nd_iff p).mpr ⟨h1, hs, hnc⟩)))
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

end NonCanon


/-! ## C. Two accepted paths: the swapped adversary and the transfer lemmas -/

section Two

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ)
  {Statement GlobalSalt : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]

theorem ro_pure {D α : Type} {R' : D → Type} [DecidableEq D] [∀ d, SampleableType (R' d)] (a : α)
    (cache : (OracleSpec.ofFn R').QueryCache) :
    randomOracleLoggedRun (pure a : OracleComp (unifSpec + OracleSpec.ofFn R') α) cache =
      pure ((a, []), cache) := by
  simp [randomOracleLoggedRun]

/-- The swapped adversary: run `adversary`, FS-verify its first proof inside its own phase (the same
verification queries), and output the SECOND proof as the selected one. -/
noncomputable def swapAdv
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt) :
    SingleSaltAdversary Statement GlobalSalt PUnit (sRounds R CS plan I0 I Ifin nb) := do
  let sel ← adversary
  match sel with
  | none => pure none
  | some (x, (salt, msgs), (salt', msgs')) => do
      let p ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
        (publicStoppedVerify (sRounds R CS plan I0 I Ifin nb) guards (x, salt) msgs)
      match p with
      | none => pure none
      | some _ => pure (some (x, (salt', msgs'), PUnit.unit))

theorem wql_fst {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (mx : OracleComp spec α) :
    Prod.fst <$> mx.withQueryLog = mx := by
  unfold withQueryLog
  rw [QueryImpl.fst_map_run_withLogging, simulateQ_ofLift_eq_self]

theorem wql_bind_fst {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type} (mx : OracleComp spec α)
    (k : α → OracleComp spec β) : (mx.withQueryLog >>= fun p => k p.1) = mx >>= k := by
  rw [← bind_map_left Prod.fst, wql_fst]

theorem swap_eq
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt) :
    (fun r => r.1.map fun x => (x.1, x.2.1)) <$>
        singleSaltExecution (sRounds R CS plan I0 I Ifin nb) guards
          (swapAdv R CS plan I0 I Ifin nb guards adversary) =
      (fun o => o.map Prod.snd) <$> twoAcceptExecution R CS plan I0 I Ifin nb guards adversary := by
  unfold twoAcceptExecution swapAdv
  simp only [singleSaltExecution, withQueryLog_bind, map_eq_pure_bind, bind_assoc, pure_bind]
  refine bind_congr fun x => ?_
  rcases x with ⟨_ | ⟨x, ⟨salt, msgs⟩, ⟨salt', msgs'⟩⟩, log⟩
  · simp
  · simp only [withQueryLog_bind, map_eq_pure_bind, bind_assoc, pure_bind]
    symm
    rw [← wql_bind_fst]
    refine bind_congr fun q => ?_
    rcases q with ⟨_ | v, l⟩
    · simp
    · simp
      rfl


/-- The second stage of `twoAcceptExecution`. -/
noncomputable def stage2
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (r : Option ((Statement × GlobalSalt) × (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath ×
        SaltedProof GlobalSalt (sRounds R CS plan I0 I Ifin nb)) ×
      QueryLog (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))) :
    OracleComp (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
      (Option (((Statement × GlobalSalt) × (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) ×
        ((Statement × GlobalSalt) × (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath))) :=
  match r.1 with
  | none => pure none
  | some (z, p, (salt', msgs')) => do
      let p' ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
        (publicStoppedVerify (sRounds R CS plan I0 I Ifin nb) guards (z.1, salt') msgs')
      pure (p'.map fun q => ((z, p), ((z.1, salt'), q)))

theorem two_eq_bind
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt) :
    twoAcceptExecution R CS plan I0 I Ifin nb guards adversary =
      singleSaltExecution (sRounds R CS plan I0 I Ifin nb) guards adversary >>=
        stage2 R CS plan I0 I Ifin nb guards := rfl


theorem pr_two_first_le
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt)
    (P : (Statement × GlobalSalt) → (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath → Prop) :
    Pr{let joint ← (randomOracleLoggedRun
        (twoAcceptExecution R CS plan I0 I Ifin nb guards adversary) ∅)}[
        ∃ z p z' p', joint.1.1 = some ((z, p), (z', p')) ∧
          sAccept R CS plan I0 I Ifin nb z p = true ∧ P z p] ≤
      Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS plan I0 I Ifin nb) guards (sAccept R CS plan I0 I Ifin nb) adversary) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ P z p] := by
  rw [singleSaltAcceptedExecution_loggedRun, prEvent_map, two_eq_bind, randomOracleLoggedRun_bind]
  refine le_trans (prEvent_bind_le_prEvent_of_forall_eq_zero _ _
    (fun a : (((Option ((Statement × GlobalSalt) × (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath ×
        SaltedProof GlobalSalt (sRounds R CS plan I0 I Ifin nb)) ×
      QueryLog (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))) ×
      QueryLog (oracleSpec (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))) ×
      (oracleSpec (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb)).QueryCache) =>
      ∃ z p w, a.1.1.1 = some (z, p, w) ∧ sAccept R CS plan I0 I Ifin nb z p = true ∧ P z p) _ ?_) ?_
  · intro a ha
    obtain ⟨⟨⟨sel, l1⟩, l2⟩, cache⟩ := a
    rcases sel with _ | ⟨z, p0, salt', msgs'⟩
    · rw [prEvent_map]
      refine prEvent_eq_zero_of_forall_mem_support _ _ ?_
      intro x hx hev
      simp only [stage2, ro_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨_, _, _, _, h, _⟩ := hev
      simp at h
    · rw [prEvent_map]
      refine prEvent_eq_zero_of_forall_mem_support _ _ ?_
      intro x hx hev
      simp only [stage2, map_eq_pure_bind, randomOracleLoggedRun_bind, support_bind, Set.mem_iUnion,
        ro_pure, support_pure, Set.mem_singleton_iff] at hx
      obtain ⟨i, _, i1, hi1, rfl⟩ := hx
      obtain ⟨z1, p1, z', p', h1, h2, h3⟩ := hev
      simp only [hi1, Option.map_eq_some_iff] at h1
      obtain ⟨q, _, hq⟩ := h1
      simp only [Prod.mk.injEq] at hq
      obtain ⟨⟨rfl, rfl⟩, _⟩ := hq
      exact ha ⟨_, _, _, rfl, h2, h3⟩
  · refine le_of_eq (prEvent_congr _ _ _ ?_)
    rintro ⟨⟨⟨sel, log⟩, log'⟩, cache⟩
    simp only [acceptSingleSaltResult]
    constructor
    · rintro ⟨z, p, w, hx, hs, hP⟩
      refine ⟨z, p, w, ?_, hP⟩
      simp [Option.filter, hx, hs]
    · rintro ⟨z, p, w, hx, hP⟩
      rcases sel with _ | ⟨z', p', w'⟩
      · simp [Option.filter] at hx
      · simp only [Option.filter] at hx
        split_ifs at hx with hacc
        simp only [Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl, rfl⟩ := hx
        exact ⟨_, _, _, rfl, hacc, hP⟩

theorem pr_two_second_le
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt)
    (P : (Statement × GlobalSalt) → (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath → Prop) :
    Pr{let joint ← (randomOracleLoggedRun
        (twoAcceptExecution R CS plan I0 I Ifin nb guards adversary) ∅)}[
        ∃ z p z' p', joint.1.1 = some ((z, p), (z', p')) ∧
          sAccept R CS plan I0 I Ifin nb z' p' = true ∧ P z' p'] ≤
      Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS plan I0 I Ifin nb) guards (sAccept R CS plan I0 I Ifin nb)
        (swapAdv R CS plan I0 I Ifin nb guards adversary)) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ P z p] := by
  classical
  let F : Option ((Statement × GlobalSalt) × (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) →
      Prop := fun o => ∃ z' p', o = some (z', p') ∧ sAccept R CS plan I0 I Ifin nb z' p' = true ∧ P z' p'
  calc _ ≤ Pr{let joint ← (randomOracleLoggedRun
          (twoAcceptExecution R CS plan I0 I Ifin nb guards adversary) ∅)}[F (joint.1.1.map Prod.snd)] := by
        refine prEvent_mono _ _ _ ?_
        rintro joint ⟨z, p, z', p', h1, h2, h3⟩
        exact ⟨z', p', by simp [h1], h2, h3⟩
    _ = Pr{let joint ← (randomOracleLoggedRun ((fun o => o.map Prod.snd) <$>
          twoAcceptExecution R CS plan I0 I Ifin nb guards adversary) ∅)}[F joint.1.1] := by
        rw [randomOracleLoggedRun_map, prEvent_map]
    _ = Pr{let joint ← (randomOracleLoggedRun ((fun r => r.1.map fun x => (x.1, x.2.1)) <$>
          singleSaltExecution (sRounds R CS plan I0 I Ifin nb) guards
          (swapAdv R CS plan I0 I Ifin nb guards adversary)) ∅)}[F joint.1.1] := by
        rw [swap_eq]
    _ = Pr{let joint ← (randomOracleLoggedRun (singleSaltExecution (sRounds R CS plan I0 I Ifin nb) guards
          (swapAdv R CS plan I0 I Ifin nb guards adversary)) ∅)}[
          F (joint.1.1.1.map fun x => (x.1, x.2.1))] := by
        rw [randomOracleLoggedRun_map, prEvent_map]
    _ ≤ _ := by
        rw [singleSaltAcceptedExecution_loggedRun, prEvent_map]
        refine prEvent_mono _ _ _ ?_
        rintro ⟨⟨⟨sel, log⟩, log'⟩, cache⟩ ⟨z, p, h1, h2, h3⟩
        rcases sel with _ | ⟨z', p', w'⟩
        · simp at h1
        · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          exact ⟨z', p', w', by simp [acceptSingleSaltResult, Option.filter, h2], h3⟩

end Two


/-! ## C'. The swapped adversary has at most `Q + (nb + 2)` fresh keys -/

/-- One oracle call writes at most one hash-log entry. -/
theorem ro_query_log {D : Type} {R' : D → Type} [DecidableEq D] [∀ d, SampleableType (R' d)]
    (t : (unifSpec + OracleSpec.ofFn R').Domain) (cache : (OracleSpec.ofFn R').QueryCache)
    (x) (hx : x ∈ support (randomOracleLoggedRun
      (liftM ((unifSpec + OracleSpec.ofFn R').query t) :
        OracleComp (unifSpec + OracleSpec.ofFn R') _) cache)) : x.1.2.length ≤ 1 := by
  rcases t with n | d
  · rw [randomOracleLoggedRun_uniformQuery, support_map] at hx
    obtain ⟨u, _, rfl⟩ := hx
    simp
  · rw [randomOracleLoggedRun_hashQuery, support_map] at hx
    obtain ⟨u, _, rfl⟩ := hx
    simp

/-- A computation with total query bound `n` writes at most `n` hash-log entries. -/
theorem ro_log_len {D : Type} {R' : D → Type} [DecidableEq D] [∀ d, SampleableType (R' d)] {α : Type}
    (oa : OracleComp (unifSpec + OracleSpec.ofFn R') α) :
    ∀ (n : ℕ), IsTotalQueryBound oa n → ∀ (cache : (OracleSpec.ofFn R').QueryCache),
      ∀ x ∈ support (randomOracleLoggedRun oa cache), x.1.2.length ≤ n := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro n _ cache x hx
      rw [ro_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; simp
  | query_bind t k ih =>
      intro n hn cache x hx
      rw [isTotalQueryBound_query_bind_iff] at hn
      rw [randomOracleLoggedRun_bind, support_bind] at hx
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at hx
      obtain ⟨p, hp, q, hq, rfl⟩ := hx
      have h1 := ro_query_log t cache p hp
      have h2 := ih _ _ (hn.2 p.1.1) p.2 q hq
      simp only [List.length_append]
      omega

theorem isTotalQueryBound_pure' {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (a : α) (n : ℕ) :
    IsTotalQueryBound (pure a : OracleComp spec α) n :=
  (isTotalQueryBound_zero_iff.mpr ⟨a, rfl⟩).mono (Nat.zero_le n)

/-- The stopped verifier makes at most one hash query per round. -/
theorem mapped_bound {Input : Type} {allRounds : List Round} :
    ∀ (rounds : List Round) (guards : GuardSchedule Input PUnit rounds) (z : Input)
      (msgs : PublicMessages rounds)
      (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
      (preserve : ∀ key, (embed key).Challenge = key.Challenge),
      IsTotalQueryBound (simulateQ (restorationQueries Input PUnit allRounds)
        (mappedStoppedComplete rounds guards z msgs embed preserve)) rounds.length
  | [], _, _, _, _, _ => by
      simp only [mappedStoppedComplete, simulateQ_pure]
      exact isTotalQueryBound_pure' _ _
  | round :: rounds, (guard, next), z, (message, messages), embed, preserve => by
      rw [mappedStoppedComplete]
      by_cases hg : guard z message PUnit.unit = true
      · simp only [hg, Bool.not_true, Bool.false_eq_true, ite_false]
        simp only [simulateQ_bind, simulateQ_liftM_query, simulateQ_pure]
        show IsTotalQueryBound (liftM ((unifSpec + oracleSpec Input PUnit allRounds).query
          (.inr (embed (Key.here z message PUnit.unit)))) >>= _) _
        rw [isTotalQueryBound_query_bind_iff]
        refine ⟨Nat.succ_pos _, fun u => ?_⟩
        simp only [List.length_cons, Nat.add_sub_cancel]
        have h := mapped_bound rounds (next message PUnit.unit (cast (preserve (Key.here z message PUnit.unit)) u))
          z messages (fun key => embed (Key.later message PUnit.unit key))
          (fun key => preserve (Key.later message PUnit.unit key))
        simpa using isTotalQueryBound_bind h (fun _ => isTotalQueryBound_pure' _ 0)
      · simp only [Bool.not_eq_true] at hg
        simp only [hg, Bool.not_false, ite_true, simulateQ_pure]
        exact isTotalQueryBound_pure' _ _

theorem verify_bound {Input : Type} {rounds : List Round} (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (msgs : PublicMessages rounds) :
    IsTotalQueryBound (simulateQ (restorationQueries Input PUnit rounds)
      (publicStoppedVerify rounds guards z msgs)) rounds.length := by
  rw [publicStoppedVerify_eq_with, publicStoppedVerifyWith_eq_mapped]
  exact mapped_bound rounds guards z msgs id (fun _ => rfl)

section Keys

open NockvmE2E.Rap NockvmE2E.Succ

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ)
  {Statement GlobalSalt : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]

theorem swap_keys_le
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt) (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    ∀ phase ∈ support
      (randomOracleLoggedRun (swapAdv R CS plan I0 I Ifin nb guards adversary).withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q + (sRounds R CS plan I0 I Ifin nb).length := by
  intro x hx
  unfold swapAdv at hx
  rw [withQueryLog_bind, randomOracleLoggedRun_bind, support_bind] at hx
  simp only [Set.mem_iUnion, support_map, Set.mem_image] at hx
  obtain ⟨a, ha, q, hq, rfl⟩ := hx
  rw [randomOracleLoggedRun_map, support_map] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  have hlen : q'.1.2.length ≤ (sRounds R CS plan I0 I Ifin nb).length := by
    refine ro_log_len _ _ ?_ a.2 q' hq'
    rw [isTotalQueryBound_withQueryLog_iff]
    rcases a.1.1.1 with _ | ⟨x, ⟨salt, msgs⟩, ⟨salt', msgs'⟩⟩
    · exact isTotalQueryBound_pure' _ _
    · have h := isTotalQueryBound_bind (verify_bound guards (x, salt) msgs)
        (ob := fun p => match p with
          | none => (pure none : OracleComp (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit
              (sRounds R CS plan I0 I Ifin nb)) _)
          | some _ => pure (some (x, (salt', msgs'), PUnit.unit))) (n₂ := 0)
        (fun p => by cases p <;> exact isTotalQueryBound_pure' _ _)
      exact h
  have h1 := queryBound a ha
  simp only [freshKeysOfLog, List.map_append, List.toFinset_append] at h1 ⊢
  calc _ ≤ _ := Finset.card_union_le _ _
    _ ≤ Q + (sRounds R CS plan I0 I Ifin nb).length :=
      add_le_add h1 (le_trans (List.toFinset_card_le _) (by simpa using hlen))

theorem sRounds_length : (sRounds R CS plan I0 I Ifin nb).length = nb + 2 := by
  simp [sRounds, rapRounds, colRounds_length]

end Keys
/-! ## D. `rap_succinct_unique` -/

section Final

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ)
  {Statement GlobalSalt : Type} [DecidableEq Statement] [DecidableEq GlobalSalt]

/-- Two canonical accepted paths with different projections are a uniqueness failure (`Collide`). -/
theorem uniqFail_of_canon {m0₀ : R.M0} {tr₀ : Tr ι β} [UC : UniqueCommitment β O (CS := CS)]
    {p p' : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath}
    (h1 : ¬ NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p) (h2 : ¬ NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p')
    (hne : proj R CS plan I0 I Ifin nb p ≠ proj R CS plan I0 I Ifin nb p') :
    UniqFailAt R CS plan I0 I Ifin nb p p' := by
  classical
  simp only [NonCanon, not_or, not_not] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  by_contra hno
  apply hne
  have hcoms : (sFinal R CS plan I0 I Ifin nb p).1 = (sFinal R CS plan I0 I Ifin nb p').1 := by
    funext j
    have hext : CS.ext ((sFinal R CS plan I0 I Ifin nb p).1 j) =
        CS.ext ((sFinal R CS plan I0 I Ifin nb p').1 j) := by
      have e1 := congrFun h1b j
      have e2 := congrFun h2b j
      rw [e1, e2]
    rcases UC.unique_com _ _ hext with h | h
    · exact h
    · exact absurd (Or.inl ⟨j, h⟩) hno
  simp only [proj, h1a, h2a, hcoms]

variable {R CS plan I0 I Ifin nb}

/-- **`rap_succinct_unique`** (generic in the commitment scheme): the positive ungrindability bound.
For a RAP with `AirDet`, a `UniqueCommitment` instance, a `Certificate` and a `Link`, two accepted
proofs of the same statement have different projections (round-0 message and commitments) with probability at most
  `(Q·M + S + εCS₁) + (Q₂·M + S + εCS₂) + εuniq`,
where `M = max_j sErrors j`, `S = Σ_j sErrors j` (the `rap_succinct_sound` terms), `Q` bounds the fresh keys of
the adversary, `Q₂` those of the SWAPPED adversary `swapAdv` (the adversary plus the FS verification of its first
proof, whose second path is the one being bounded: `Q₂ ≤ Q + (nb + 2)` is not proved here, see the report),
`εCS₁ εCS₂` are the extraction-failure bounds (`hCS`) for the two adversaries and `εuniq` is `huniq`.
Proof: `AirDet` makes every accepted extracted trace canonical off a soundness failure
(`rap_succinct_noncanon`, once per path); two canonical paths with different projections are a `Collide`. -/
theorem rap_succinct_unique [UC : UniqueCommitment β O (CS := CS)]
    (hC : Certificate R blkOf nb) (hl : Link R CS plan) (hD : AirDet R)
    (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt)
    (Q Q₂ : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q)
    (queryBound₂ : ∀ phase ∈ support
      (randomOracleLoggedRun (swapAdv R CS plan I0 I Ifin nb guards adversary).withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q₂)
    (εCS₁ εCS₂ εuniq : ℝ≥0∞)
    (hCS₁ : Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS plan I0 I Ifin nb) guards (sAccept R CS plan I0 I Ifin nb) adversary) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ ExtFailAt R CS plan I0 I Ifin nb p] ≤ εCS₁)
    (hCS₂ : Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS plan I0 I Ifin nb) guards (sAccept R CS plan I0 I Ifin nb)
        (swapAdv R CS plan I0 I Ifin nb guards adversary)) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ ExtFailAt R CS plan I0 I Ifin nb p] ≤ εCS₂)
    (huniq : HUniq R CS plan I0 I Ifin nb guards adversary εuniq) :
    Pr{let joint ← (randomOracleLoggedRun
        (twoAcceptExecution R CS plan I0 I Ifin nb guards adversary) ∅)}[
        TwoAcceptDistinctProj R CS plan I0 I Ifin nb joint.1.1] ≤
      (Q * Finset.univ.sup (sErrors R CS plan I0 I Ifin nb err) +
        ∑ j, sErrors R CS plan I0 I Ifin nb err j + εCS₁) +
      (Q₂ * Finset.univ.sup (sErrors R CS plan I0 I Ifin nb err) +
        ∑ j, sErrors R CS plan I0 I Ifin nb err j + εCS₂) + εuniq := by
  classical
  obtain ⟨m0₀, tr₀, hD⟩ := hD
  -- pointwise: E ⊆ A1 ∨ A2 ∨ F
  have hsplit : ∀ joint : Option (((Statement × GlobalSalt) ×
        (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath) ×
        ((Statement × GlobalSalt) × (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath)),
      TwoAcceptDistinctProj R CS plan I0 I Ifin nb joint →
        ((∃ z p z' p', joint = some ((z, p), (z', p')) ∧ sAccept R CS plan I0 I Ifin nb z p = true ∧
            NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p) ∨
          (∃ z p z' p', joint = some ((z, p), (z', p')) ∧ sAccept R CS plan I0 I Ifin nb z' p' = true ∧
            NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p')) ∨
        (∃ z p z' p', joint = some ((z, p), (z', p')) ∧ sAccept R CS plan I0 I Ifin nb z p = true ∧
          sAccept R CS plan I0 I Ifin nb z' p' = true ∧ UniqFailAt R CS plan I0 I Ifin nb p p') := by
    rintro joint ⟨z, p, z', p', hj, _, hacc, hacc', hne⟩
    by_cases h1 : NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p
    · exact Or.inl (Or.inl ⟨z, p, z', p', hj, hacc, h1⟩)
    · by_cases h2 : NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p'
      · exact Or.inl (Or.inr ⟨z, p, z', p', hj, hacc', h2⟩)
      · exact Or.inr ⟨z, p, z', p', hj, hacc, hacc', uniqFail_of_canon R CS plan I0 I Ifin nb h1 h2 hne⟩
  refine le_trans (prEvent_mono _ _ _ (fun x hx => hsplit x.1.1 hx)) (le_trans (prEvent_or_le _ _ _)
    (add_le_add (le_trans (prEvent_or_le _ _ _) (add_le_add ?_ ?_)) huniq))
  · refine le_trans (pr_two_first_le R CS plan I0 I Ifin nb guards adversary
      (fun _ p => NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p)) ?_
    exact rap_succinct_noncanon R CS plan I0 I Ifin nb m0₀ tr₀ hC hl hD err herr guards adversary Q queryBound
      εCS₁ hCS₁
  · refine le_trans (pr_two_second_le R CS plan I0 I Ifin nb guards adversary
      (fun _ p => NonCanon R CS plan I0 I Ifin nb m0₀ tr₀ p)) ?_
    exact rap_succinct_noncanon R CS plan I0 I Ifin nb m0₀ tr₀ hC hl hD err herr guards
      (swapAdv R CS plan I0 I Ifin nb guards adversary) Q₂ queryBound₂ εCS₂ hCS₂

/-- **`rap_succinct_unique` with the single query bound `Q`**: the swapped adversary's keys are `≤ Q + (nb + 2)`
(`swap_keys_le`: the verification of the first proof adds one key per round). -/
theorem rap_succinct_unique_Q [UC : UniqueCommitment β O (CS := CS)]
    (hC : Certificate R blkOf nb) (hl : Link R CS plan) (hD : AirDet R)
    (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement GlobalSalt)
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q)
    (εCS₁ εCS₂ εuniq : ℝ≥0∞)
    (hCS₁ : Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS plan I0 I Ifin nb) guards (sAccept R CS plan I0 I Ifin nb) adversary) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ ExtFailAt R CS plan I0 I Ifin nb p] ≤ εCS₁)
    (hCS₂ : Pr{let joint ← (randomOracleLoggedRun (singleSaltAcceptedExecution
        (sRounds R CS plan I0 I Ifin nb) guards (sAccept R CS plan I0 I Ifin nb)
        (swapAdv R CS plan I0 I Ifin nb guards adversary)) ∅)}[
        ∃ z p w, joint.1.1.1 = some (z, p, w) ∧ ExtFailAt R CS plan I0 I Ifin nb p] ≤ εCS₂)
    (huniq : HUniq R CS plan I0 I Ifin nb guards adversary εuniq) :
    Pr{let joint ← (randomOracleLoggedRun
        (twoAcceptExecution R CS plan I0 I Ifin nb guards adversary) ∅)}[
        TwoAcceptDistinctProj R CS plan I0 I Ifin nb joint.1.1] ≤
      (Q * Finset.univ.sup (sErrors R CS plan I0 I Ifin nb err) +
        ∑ j, sErrors R CS plan I0 I Ifin nb err j + εCS₁) +
      ((Q + (nb + 2) : ℕ) * Finset.univ.sup (sErrors R CS plan I0 I Ifin nb err) +
        ∑ j, sErrors R CS plan I0 I Ifin nb err j + εCS₂) + εuniq := by
  have hk := swap_keys_le R CS plan I0 I Ifin nb guards adversary Q queryBound
  rw [sRounds_length] at hk
  exact rap_succinct_unique hC hl hD err herr guards adversary Q (Q + (nb + 2)) queryBound hk εCS₁ εCS₂ εuniq
    hCS₁ hCS₂ huniq

/-- **`rap_succinct_unique` at the IOP instance** (`iopCS`: the commitment is the data; `εCS = εuniq = 0`).
The only instance for which `unique_com` holds unconditionally (`iopUnique`). -/
theorem rap_succinct_unique_iop [Fintype β] [DecidableEq β] [Inhabited β]
    (plan : OpenPlan R (iopCS O)) [DecidableEq plan.Mfin] [Finite plan.Mfin]
    (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound β r))
    (Ifin : OracleInterface plan.Mfin) (nb : ℕ)
    (hC : Certificate R blkOf nb) (hl : Link R (iopCS O) plan) (hD : AirDet R)
    (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R (iopCS O) plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R (iopCS O) plan I0 I Ifin nb Statement GlobalSalt)
    (Q Q₂ : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q)
    (queryBound₂ : ∀ phase ∈ support
      (randomOracleLoggedRun (swapAdv R (iopCS O) plan I0 I Ifin nb guards adversary).withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q₂) :
    Pr{let joint ← (randomOracleLoggedRun
        (twoAcceptExecution R (iopCS O) plan I0 I Ifin nb guards adversary) ∅)}[
        TwoAcceptDistinctProj R (iopCS O) plan I0 I Ifin nb joint.1.1] ≤
      (Q * Finset.univ.sup (sErrors R (iopCS O) plan I0 I Ifin nb err) +
        ∑ j, sErrors R (iopCS O) plan I0 I Ifin nb err j) +
      (Q₂ * Finset.univ.sup (sErrors R (iopCS O) plan I0 I Ifin nb err) +
        ∑ j, sErrors R (iopCS O) plan I0 I Ifin nb err j) := by
  letI : UniqueCommitment β O (CS := iopCS O) := iopUnique O
  have hu : HUniq R (iopCS O) plan I0 I Ifin nb guards adversary 0 := by
    refine le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)
    rintro joint ⟨z, p, z', p', _, _, _, hf⟩
    rcases hf with ⟨j, hj⟩ | ⟨_, _, hj⟩ <;> exact hj
  have h := rap_succinct_unique hC hl hD err herr guards adversary Q Q₂ queryBound queryBound₂ 0 0 0
    (extFail_zero (iopCS_perfect O) guards adversary).le
    (extFail_zero (iopCS_perfect O) guards (swapAdv R (iopCS O) plan I0 I Ifin nb guards adversary)).le hu
  simpa only [add_zero] using h

/-- **IOP instance with the single query bound**: `εCS = εuniq = 0`, keys of the swapped adversary `≤ Q + (nb + 2)`. -/
theorem rap_succinct_unique_iop_Q [Fintype β] [DecidableEq β] [Inhabited β]
    (plan : OpenPlan R (iopCS O)) [DecidableEq plan.Mfin] [Finite plan.Mfin]
    (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound β r))
    (Ifin : OracleInterface plan.Mfin) (nb : ℕ)
    (hC : Certificate R blkOf nb) (hl : Link R (iopCS O) plan) (hD : AirDet R)
    (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit (sRounds R (iopCS O) plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R (iopCS O) plan I0 I Ifin nb Statement GlobalSalt)
    (Q : ℕ)
    (queryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let joint ← (randomOracleLoggedRun
        (twoAcceptExecution R (iopCS O) plan I0 I Ifin nb guards adversary) ∅)}[
        TwoAcceptDistinctProj R (iopCS O) plan I0 I Ifin nb joint.1.1] ≤
      (Q * Finset.univ.sup (sErrors R (iopCS O) plan I0 I Ifin nb err) +
        ∑ j, sErrors R (iopCS O) plan I0 I Ifin nb err j) +
      ((Q + (nb + 2) : ℕ) * Finset.univ.sup (sErrors R (iopCS O) plan I0 I Ifin nb err) +
        ∑ j, sErrors R (iopCS O) plan I0 I Ifin nb err j) := by
  have hk := swap_keys_le R (iopCS O) plan I0 I Ifin nb guards adversary Q queryBound
  rw [sRounds_length] at hk
  exact rap_succinct_unique_iop plan I0 I Ifin nb hC hl hD err herr guards adversary Q (Q + (nb + 2))
    queryBound hk

end Final


end NockvmE2E.Ung
