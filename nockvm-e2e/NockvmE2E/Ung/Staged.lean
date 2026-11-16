/-
**`rap_succinct_unique_staged`** — the positive ungrindability theorem
for STAGED RAPs (columns that depend on coins sampled after earlier commitments, e.g. every J-8 chip), under a FIXED
salt (`GlobalSalt := Unit`; the nonce is part of the statement, (d)).

Route. Two paths of `twoAcceptExecution` are cached in ONE random-oracle cache (`two_cached`), so with the same
statement and salt, two paths that share the first `n` rounds (messages) have the same first `n` challenges
(`chal_at`). A path is BAD if its round-0 message or some round-`n` extracted column differs from the canonical one
(`BadC`); the probability of an accepted bad path is the `rap_succinct_sound`-shaped bound
(`rap_succinct_badpath`, once for each of the two paths, the second through the swapped adversary exactly as in
`rap_succinct_unique`). If neither path is bad, then by induction over the rounds: shared prefix => equal coins
(cache) => equal canonical round-`n` columns (`canTr_congr`) => equal commitments (`unique_com`, or a `Collide`) =>
shared round `n+1` prefix. At the last round the commitments (hence `proj`) coincide.
-/
import NockvmE2E.Ung.StagedCanon
import NockvmE2E.Ung.StagedPath
import NockvmE2E.Ung.BadPath

set_option autoImplicit false
set_option linter.unusedSectionVars false

open OracleComp OracleSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open scoped ENNReal

namespace NockvmE2E.Ung

open NockvmE2E.Rap NockvmE2E.Succ

section Det

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ)

/-- **The deterministic core.** Two paths cached in one cache for the same statement, neither bad, with no
`Collide` among their commitments, have the same projection. -/
theorem proj_eq_of_good [UC : UniqueCommitment β O (CS := CS)] [Nonempty (Tr ι β)] {m0₀ : R.M0}
    {Input : Type} [DecidableEq Input] (z : Input)
    (c : (oracleSpec Input PUnit (sRounds R CS plan I0 I Ifin nb)).QueryCache)
    {p p' : (protocol (sRounds R CS plan I0 I Ifin nb)).tree.ExecutionPath}
    (hp : PathCached c (sRounds R CS plan I0 I Ifin nb) z id (fun _ => rfl) p)
    (hp' : PathCached c (sRounds R CS plan I0 I Ifin nb) z id (fun _ => rfl) p')
    (h1 : ¬ BadAt R CS plan I0 I Ifin nb (BadC R m0₀ nb) p)
    (h2 : ¬ BadAt R CS plan I0 I Ifin nb (BadC R m0₀ nb) p')
    (hno : ¬ UniqFailAt R CS plan I0 I Ifin nb p p') :
    proj R CS plan I0 I Ifin nb p = proj R CS plan I0 I Ifin nb p' := by
  classical
  unfold BadAt BadC at h1 h2
  push Not at h1 h2
  obtain ⟨hm1, hc1⟩ := h1
  obtain ⟨hm2, hc2⟩ := h2
  have hm : p.1 = p'.1 := hm1.trans hm2.symm
  have key : ∀ n, n ≤ nb → PEq (sRounds R CS plan I0 I Ifin nb) (n + 1) p p' := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨hm, Subsingleton.elim (α := PUnit) _ _, pEq_zero _ _ _⟩
    | succ n ih =>
        intro hn
        have h := ih (by omega)
        have hPE : PEq (colRounds Φ K CS.Com colRound I (finRound (sStmt R CS plan) Ifin) 0 nb) n p.2.2 p'.2.2 :=
          h.2.2
        have hA := finalOf_agree (sStmt R CS plan) I Ifin nb 0 n (by omega) (fun _ => default)
          (fun _ => default) (fun _ => default) (fun _ => default) p.2.2 p'.2.2 hPE
          (fun _ _ => rfl) (fun _ _ => rfl)
        have hcom : ∀ j, colRound j = n →
            (sFinal R CS plan I0 I Ifin nb p).1 j = (sFinal R CS plan I0 I Ifin nb p').1 j := by
          intro j hj
          have hext : CS.ext ((sFinal R CS plan I0 I Ifin nb p).1 j) =
              CS.ext ((sFinal R CS plan I0 I Ifin nb p').1 j) := by
            have e1 := hc1 n (by omega) j hj
            have e2 := hc2 n (by omega) j hj
            have hcan := canTr_congr R n p.1
              (tr := fun j => CS.ext ((sFinal R CS plan I0 I Ifin nb p).1 j))
              (tr' := fun j => CS.ext ((sFinal R CS plan I0 I Ifin nb p').1 j))
              (χ := (sFinal R CS plan I0 I Ifin nb p).2.1) (χ' := (sFinal R CS plan I0 I Ifin nb p').2.1)
              (fun j hj => congrArg CS.ext (hA.1 j (by omega)))
              (fun i hi => hA.2 i (by omega))
            rw [e1, hcan, e2, ← hm]
          rcases UC.unique_com _ _ hext with h | h
          · exact h
          · exact absurd (Or.inl ⟨j, h⟩) hno
        have hM : MAt (sRounds R CS plan I0 I Ifin nb) (n + 1) p p' :=
          finalOf_msg (sStmt R CS plan) I Ifin nb 0 n (by omega) (fun _ => default) (fun _ => default)
            (fun _ => default) (fun _ => default) p.2.2 p'.2.2 (fun j hj => by
              have hj' : colRound j = n := by omega
              by_contra hne
              exact hne (hcom j hj'))
        exact (pEq_succ _ (n + 1) p p').mpr ⟨h, hM, chal_at c _ z id _ (n + 1) p p' hp hp' h hM⟩
  have hfin := key nb le_rfl
  have hPE : PEq (colRounds Φ K CS.Com colRound I (finRound (sStmt R CS plan) Ifin) 0 nb) nb p.2.2 p'.2.2 :=
    hfin.2.2
  have hA := finalOf_agree (sStmt R CS plan) I Ifin nb 0 nb le_rfl (fun _ => default)
    (fun _ => default) (fun _ => default) (fun _ => default) p.2.2 p'.2.2 hPE
    (fun _ _ => rfl) (fun _ _ => rfl)
  unfold proj
  rw [hm]
  congr 1
  funext j
  exact hA.1 j (by omega)

end Det

section Final

variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι β : Type}
  {colRound : ι → ℕ} {O : OracleInterface β}
  [SampleableType K] [Inhabited K] [Fintype ι] [DecidableEq ι]
  (R : RapStatement Φ K ι β colRound) (CS : CommitScheme β O) (plan : OpenPlan R CS)
  [Fintype CS.Com] [DecidableEq CS.Com] [Inhabited CS.Com]
  [DecidableEq R.M0] [Finite R.M0] [DecidableEq plan.Mfin] [Finite plan.Mfin]
  (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound CS.Com r))
  (Ifin : OracleInterface plan.Mfin) (nb : ℕ)
  {Statement : Type} [DecidableEq Statement]

variable {R CS plan I0 I Ifin nb}

/-- **`rap_succinct_unique_staged`** (generic in the commitment scheme, FIXED salt `GlobalSalt := Unit`): the
positive ungrindability bound for a STAGED RAP. Hypotheses as `rap_succinct_unique` with `AirDetStaged R` (round-wise,
coin-dependent columns allowed) in place of `AirDet R`:
  `Pr[TwoAcceptDistinctProj] ≤ (Q·M + S + εCS₁) + (Q₂·M + S + εCS₂) + εuniq`. -/
theorem rap_succinct_unique_staged [UC : UniqueCommitment β O (CS := CS)]
    (hC : Certificate R blkOf nb) (hl : Link R CS plan) (hD : AirDetStaged R)
    (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    (guards : GuardSchedule (Statement × Unit) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement Unit)
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
  haveI : Nonempty (Tr ι β) := ⟨fun _ => CS.ext default⟩
  obtain ⟨⟨m0₀, hm0⟩, hcol⟩ := hD
  have hBad : ∀ (m0 : R.M0) (tr : Tr ι β) (fin : R.Mfin) (χ : Coins Φ K), R.Accepts m0 tr fin χ →
      (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → ¬ BadC R m0₀ nb m0 tr χ :=
    fun m0 tr fin χ ha hs => badC_sound R hm0 hcol m0 tr fin χ ha hs
  have hsplit : ∀ x ∈ support (randomOracleLoggedRun
        (twoAcceptExecution R CS plan I0 I Ifin nb guards adversary) ∅),
      TwoAcceptDistinctProj R CS plan I0 I Ifin nb x.1.1 →
        ((∃ z p z' p', x.1.1 = some ((z, p), (z', p')) ∧ sAccept R CS plan I0 I Ifin nb z p = true ∧
            BadAt R CS plan I0 I Ifin nb (BadC R m0₀ nb) p) ∨
          (∃ z p z' p', x.1.1 = some ((z, p), (z', p')) ∧ sAccept R CS plan I0 I Ifin nb z' p' = true ∧
            BadAt R CS plan I0 I Ifin nb (BadC R m0₀ nb) p')) ∨
        (∃ z p z' p', x.1.1 = some ((z, p), (z', p')) ∧ sAccept R CS plan I0 I Ifin nb z p = true ∧
          sAccept R CS plan I0 I Ifin nb z' p' = true ∧ UniqFailAt R CS plan I0 I Ifin nb p p') := by
    intro x hx hE
    obtain ⟨z, p, z', p', hj, hz, hacc, hacc', hne⟩ := hE
    by_cases h1 : BadAt R CS plan I0 I Ifin nb (BadC R m0₀ nb) p
    · exact Or.inl (Or.inl ⟨z, p, z', p', hj, hacc, h1⟩)
    · by_cases h2 : BadAt R CS plan I0 I Ifin nb (BadC R m0₀ nb) p'
      · exact Or.inl (Or.inr ⟨z, p, z', p', hj, hacc', h2⟩)
      · by_cases hu : UniqFailAt R CS plan I0 I Ifin nb p p'
        · exact Or.inr ⟨z, p, z', p', hj, hacc, hacc', hu⟩
        · exfalso
          apply hne
          obtain ⟨hc1, hc2⟩ := two_cached R CS plan I0 I Ifin nb guards adversary x hx z p z' p' hj
          have hzz : z = z' := Prod.ext hz (Subsingleton.elim _ _)
          subst hzz
          exact proj_eq_of_good R CS plan I0 I Ifin nb z x.2 hc1 hc2 h1 h2 hu
  refine le_trans (prEvent_mono_of_support _ _ _ (fun x hx => hsplit x hx)) (le_trans (prEvent_or_le _ _ _)
    (add_le_add (le_trans (prEvent_or_le _ _ _) (add_le_add ?_ ?_)) huniq))
  · refine le_trans (pr_two_first_le R CS plan I0 I Ifin nb guards adversary
      (fun _ p => BadAt R CS plan I0 I Ifin nb (BadC R m0₀ nb) p)) ?_
    exact rap_succinct_badpath R CS plan I0 I Ifin nb (BadC R m0₀ nb) hC hl hBad err herr guards adversary Q
      queryBound εCS₁ hCS₁
  · refine le_trans (pr_two_second_le R CS plan I0 I Ifin nb guards adversary
      (fun _ p => BadAt R CS plan I0 I Ifin nb (BadC R m0₀ nb) p)) ?_
    exact rap_succinct_badpath R CS plan I0 I Ifin nb (BadC R m0₀ nb) hC hl hBad err herr guards
      (swapAdv R CS plan I0 I Ifin nb guards adversary) Q₂ queryBound₂ εCS₂ hCS₂

/-- **`rap_succinct_unique_staged` with the single query bound `Q`** (`Q₂ := Q + (nb + 2)`, `swap_keys_le`). -/
theorem rap_succinct_unique_staged_Q [UC : UniqueCommitment β O (CS := CS)]
    (hC : Certificate R blkOf nb) (hl : Link R CS plan) (hD : AirDetStaged R)
    (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    (guards : GuardSchedule (Statement × Unit) PUnit (sRounds R CS plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R CS plan I0 I Ifin nb Statement Unit)
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
  exact rap_succinct_unique_staged hC hl hD err herr guards adversary Q (Q + (nb + 2)) queryBound hk εCS₁ εCS₂
    εuniq hCS₁ hCS₂ huniq

/-- **The `iopCS` instance** (`εCS = εuniq = 0`): the only instance for which `unique_com` holds unconditionally. -/
theorem rap_succinct_unique_staged_iop [Fintype β] [DecidableEq β] [Inhabited β]
    (plan : OpenPlan R (iopCS O)) [DecidableEq plan.Mfin] [Finite plan.Mfin]
    (I0 : OracleInterface R.M0) (I : (r : ℕ) → OracleInterface (Cols colRound β r))
    (Ifin : OracleInterface plan.Mfin) (nb : ℕ)
    (hC : Certificate R blkOf nb) (hl : Link R (iopCS O) plan) (hD : AirDetStaged R)
    (err : ℕ → ℝ≥0∞) (herr : ∀ m0 r, roundBound R blkOf m0 r ≤ err r)
    (guards : GuardSchedule (Statement × Unit) PUnit (sRounds R (iopCS O) plan I0 I Ifin nb))
    (adversary : TwoProofAdversary R (iopCS O) plan I0 I Ifin nb Statement Unit)
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
  letI : UniqueCommitment β O (CS := iopCS O) := iopUnique O
  have hu : HUniq R (iopCS O) plan I0 I Ifin nb guards adversary 0 := by
    refine le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)
    rintro joint ⟨z, p, z', p', _, _, _, hf⟩
    rcases hf with ⟨j, hj⟩ | ⟨_, _, hj⟩ <;> exact hj
  have h := rap_succinct_unique_staged_Q hC hl hD err herr guards adversary Q queryBound 0 0 0
    (extFail_zero (iopCS_perfect O) guards adversary).le
    (extFail_zero (iopCS_perfect O) guards (swapAdv R (iopCS O) plan I0 I Ifin nb guards adversary)).le hu
  simpa only [add_zero] using h

end Final

end NockvmE2E.Ung
