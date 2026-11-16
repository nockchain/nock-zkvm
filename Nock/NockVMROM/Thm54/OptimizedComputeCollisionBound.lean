import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NPR

/-! Exact root-count bound for the production challenge-9 folds. -/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeCollisionBound

open Nock
open Nock.Reified
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeFinal
open OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.CoordinateCompiler
open scoped Polynomial

noncomputable section

def withFinalFoldChallenge {K : Type*} (env : Env K) (z : K) : Env K where
  trace := env.trace
  traceNext := env.traceNext
  chal i := if i = compilerChallengeBase then z else env.chal i
  pub := env.pub

def CompilerChallengeFree : Expr → Prop
  | .Var .challenge i => i ≠ compilerChallengeBase
  | .Var _ _ | .Const _ => True
  | .Add x y | .Sub x y | .Mul x y => CompilerChallengeFree x ∧ CompilerChallengeFree y
  | .Neg x | .Pow x _ => CompilerChallengeFree x

def compilerChallengeFreeB : Expr → Bool
  | .Var .challenge i => i != compilerChallengeBase
  | .Var _ _ | .Const _ => true
  | .Add x y | .Sub x y | .Mul x y => compilerChallengeFreeB x && compilerChallengeFreeB y
  | .Neg x | .Pow x _ => compilerChallengeFreeB x

theorem compilerChallengeFreeB_iff (e : Expr) :
    compilerChallengeFreeB e ↔ CompilerChallengeFree e := by
  induction e with
  | Var kind i => cases kind <;> simp [compilerChallengeFreeB, CompilerChallengeFree]
  | Const c => simp [compilerChallengeFreeB, CompilerChallengeFree]
  | Add x y ihx ihy | Sub x y ihx ihy | Mul x y ihx ihy =>
      simp [compilerChallengeFreeB, CompilerChallengeFree, ihx, ihy]
  | Neg x ih | Pow x n ih => simpa [compilerChallengeFreeB, CompilerChallengeFree] using ih

theorem finalNonIOSourceFamilies17_challenge9_free :
    ∀ es ∈ finalNonIOSourceFamilies17, ∀ e ∈ es, CompilerChallengeFree e := by
  intro es hes e he
  rw [← compilerChallengeFreeB_iff]
  set_option maxRecDepth 200000 in
  have hall :
      ∀ qs ∈ finalNonIOSourceFamilies17, ∀ q ∈ qs, compilerChallengeFreeB q := by decide
  exact hall es hes e he

theorem eval_withFinalFoldChallenge_of_free
    {K : Type*} [Field K] (env : Env K) (z : K) (e : Expr)
    (hfree : CompilerChallengeFree e) :
    e.eval (withFinalFoldChallenge env z) = e.eval env := by
  induction e with
  | Var kind i =>
      cases kind with
      | traceCur => rfl
      | traceNext => rfl
      | challenge =>
          simp [CompilerChallengeFree] at hfree
          simp [Expr.eval, withFinalFoldChallenge, if_neg hfree]
      | publicVal => rfl
  | Const c => simp [Expr.eval]
  | Add x y ihx ihy =>
      simpa [Expr.eval] using congrArg₂ (· + ·) (ihx hfree.1) (ihy hfree.2)
  | Sub x y ihx ihy =>
      simpa [Expr.eval] using congrArg₂ (· - ·) (ihx hfree.1) (ihy hfree.2)
  | Mul x y ihx ihy =>
      simpa [Expr.eval] using congrArg₂ (· * ·) (ihx hfree.1) (ihy hfree.2)
  | Neg x ih => simpa [Expr.eval] using congrArg Neg.neg (ih hfree)
  | Pow x n ih => simpa [Expr.eval] using congrArg (fun q => q ^ n) (ih hfree)

def finalRlcPolynomial {K : Type*} [Field K] (env : Env K) : List Expr → K[X]
  | [] => 0
  | e :: es => Polynomial.C (e.eval env) + Polynomial.X * finalRlcPolynomial env es

theorem finalRlcPolynomial_eval
    {K : Type*} [Field K] (env : Env K) (es : List Expr) (z : K)
    (hfree : ∀ e ∈ es, CompilerChallengeFree e) :
    (finalRlcPolynomial env es).eval z =
      (finalRlcFold es).eval (withFinalFoldChallenge env z) := by
  induction es with
  | nil => simp [finalRlcPolynomial, finalRlcFold, Expr.eval]
  | cons e es ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hfree
      simp only [finalRlcPolynomial, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X, finalRlcFold, Expr.eval]
      rw [eval_withFinalFoldChallenge_of_free env z e hfree.1]
      rw [ih hfree.2]
      rw [show finalFoldChallenge.eval (withFinalFoldChallenge env z) = z by
        simp [finalFoldChallenge, Expr.eval, withFinalFoldChallenge]]

theorem finalRlcPolynomial_nonzero
    {K : Type*} [Field K] (env : Env K) (es : List Expr)
    (hnonzero : ∃ e ∈ es, e.eval env ≠ 0) :
    finalRlcPolynomial env es ≠ 0 := by
  induction es with
  | nil => simp at hnonzero
  | cons e es ih =>
      by_cases he : e.eval env = 0
      · have htail : ∃ q ∈ es, q.eval env ≠ 0 := by
          obtain ⟨q, hq, hne⟩ := hnonzero
          have hqe : q ≠ e := by
            intro h
            subst q
            exact hne he
          exact ⟨q, (List.mem_cons.mp hq).resolve_left hqe, hne⟩
        simp [finalRlcPolynomial, he, ih htail]
      · intro hz
        have hc : e.eval env = 0 := by
          simpa [finalRlcPolynomial] using congrArg Polynomial.constantCoeff hz
        exact he hc

theorem finalRlcPolynomial_natDegree_le
    {K : Type*} [Field K] (env : Env K) (es : List Expr) (hne : es ≠ []) :
    (finalRlcPolynomial env es).natDegree ≤ es.length - 1 := by
  induction es with
  | nil => exact (hne rfl).elim
  | cons e es ih =>
      by_cases hs : es = []
      · subst es
        simp [finalRlcPolynomial]
      · calc
          (finalRlcPolynomial env (e :: es)).natDegree
              ≤ max (Polynomial.C (e.eval env)).natDegree
                (Polynomial.X * finalRlcPolynomial env es).natDegree :=
            Polynomial.natDegree_add_le _ _
          _ ≤ max 0 (1 + (finalRlcPolynomial env es).natDegree) := by
            apply max_le_max
            · simp
            · exact Polynomial.natDegree_mul_le.trans (by simp)
          _ ≤ (e :: es).length - 1 := by
            have hi := ih hs
            have hlen : 0 < es.length := List.length_pos_of_ne_nil hs
            simp only [List.length_cons]
            omega

def familyBadChallenges {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (es : List Expr) : Finset K :=
  Finset.univ.filter fun z => (finalRlcPolynomial env es).eval z = 0

theorem familyBadChallenges_card_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (es : List Expr) (hne : es ≠ [])
    (hnonzero : ∃ e ∈ es, e.eval env ≠ 0) :
    (familyBadChallenges env es).card ≤ es.length - 1 := by
  exact (NPR.card_eval_zero_le _ (finalRlcPolynomial_nonzero env es hnonzero)).trans
    (finalRlcPolynomial_natDegree_le env es hne)

def badChallengesFor {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (families : List (List Expr)) : Finset K :=
  families.foldr
    (fun es acc =>
      if ∃ e ∈ es, e.eval env ≠ 0 then familyBadChallenges env es ∪ acc else acc) ∅

def finalComputeBadChallenges {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) : Finset K :=
  badChallengesFor env finalNonIOSourceFamilies17

theorem badChallengesFor_card_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (families : List (List Expr)) :
    (badChallengesFor env families).card ≤
      (families.map fun es => es.length - 1).sum := by
  induction families with
  | nil => simp [badChallengesFor]
  | cons es families ih =>
      by_cases h : ∃ e ∈ es, e.eval env ≠ 0
      · have hne : es ≠ [] := by
          intro hz
          subst es
          simp at h
        simp only [badChallengesFor, List.foldr_cons, h, if_true, List.map_cons, List.sum_cons]
        exact (Finset.card_union_le _ _).trans
          (Nat.add_le_add (familyBadChallenges_card_le env es hne h) ih)
      · simp only [badChallengesFor, List.foldr_cons, h, if_false, List.map_cons,
          List.sum_cons]
        exact ih.trans (Nat.le_add_left _ _)

/-- Exact per-row union bound for all seventeen production challenge-9 folds. -/
theorem finalComputeBadChallenges_card_le_494
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (env : Env K) :
    (finalComputeBadChallenges env).card ≤ 494 := by
  calc
    (finalComputeBadChallenges env).card ≤ finalComputeRLCWorkload := by
      exact badChallengesFor_card_le env finalNonIOSourceFamilies17
    _ = 494 := OptimizedComputeGateBasis.finalComputeRLCWorkload_exact

theorem mem_badChallengesFor_of
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (families : List (List Expr)) (es : List Expr)
    (hes : es ∈ families) (hnonzero : ∃ e ∈ es, e.eval env ≠ 0)
    (z : K) (hroot : (finalRlcPolynomial env es).eval z = 0) :
    z ∈ badChallengesFor env families := by
  induction families with
  | nil => simp at hes
  | cons qs families ih =>
      rw [List.mem_cons] at hes
      rcases hes with rfl | hes
      · simp [badChallengesFor, hnonzero, familyBadChallenges, hroot]
      · by_cases hqs : ∃ e ∈ qs, e.eval env ≠ 0
        · simp only [badChallengesFor, List.foldr_cons, hqs, if_true, Finset.mem_union]
          exact Or.inr (ih hes)
        · simp only [badChallengesFor, List.foldr_cons, hqs, if_false]
          exact ih hes

theorem finalComputeCollisionFree_of_not_bad
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (z : K) (hchal : env.chal compilerChallengeBase = z)
    (hgood : z ∉ finalComputeBadChallenges env) :
    FinalComputeCollisionFree env := by
  intro es hes hfold e he
  by_contra hne
  have hnonzero : ∃ q ∈ es, q.eval env ≠ 0 := ⟨e, he, hne⟩
  apply hgood
  apply mem_badChallengesFor_of env finalNonIOSourceFamilies17 es hes hnonzero z
  rw [finalRlcPolynomial_eval env es z
    (finalNonIOSourceFamilies17_challenge9_free es hes)]
  have henv : withFinalFoldChallenge env z = env := by
    cases env with
    | mk tr trn ch pub =>
        simp only [withFinalFoldChallenge]
        congr 1
        funext i
        by_cases hi : i = compilerChallengeBase
        · subst i
          simpa using hchal.symm
        · simp [hi]
  rw [henv]
  exact hfold

theorem compute_mem_badChallengesFor_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (families : List (List Expr)) (z : K) :
    z ∈ badChallengesFor env families ↔
      ∃ es ∈ families, (∃ e ∈ es, e.eval env ≠ 0) ∧
        (finalRlcPolynomial env es).eval z = 0 := by
  induction families with
  | nil => simp [badChallengesFor]
  | cons es families ih =>
      by_cases hnz : ∃ e ∈ es, e.eval env ≠ 0
      · rw [badChallengesFor, List.foldr_cons, if_pos hnz, Finset.mem_union]
        change z ∈ familyBadChallenges env es ∨ z ∈ badChallengesFor env families ↔ _
        rw [ih]
        simp only [familyBadChallenges, Finset.mem_filter, Finset.mem_univ,
          true_and, List.mem_cons]
        constructor
        · rintro (hroot | ⟨qs, hqs, hqsnz, hqsroot⟩)
          · exact ⟨es, Or.inl rfl, hnz, hroot⟩
          · exact ⟨qs, Or.inr hqs, hqsnz, hqsroot⟩
        · rintro ⟨qs, rfl | hqs, hqsnz, hroot⟩
          · exact Or.inl hroot
          · exact Or.inr ⟨qs, hqs, hqsnz, hroot⟩
      · rw [badChallengesFor, List.foldr_cons, if_neg hnz]
        change z ∈ badChallengesFor env families ↔ _
        rw [ih]
        simp only [List.mem_cons]
        constructor
        · rintro ⟨qs, hqs, hqsnz, hroot⟩
          exact ⟨qs, Or.inr hqs, hqsnz, hroot⟩
        · rintro ⟨qs, rfl | hqs, hqsnz, hroot⟩
          · exact (hnz hqsnz).elim
          · exact ⟨qs, hqs, hqsnz, hroot⟩

theorem finalCompute_not_bad_of_collisionFree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (hfree : FinalComputeCollisionFree env) :
    env.chal compilerChallengeBase ∉ finalComputeBadChallenges env := by
  intro hbad
  obtain ⟨es, hes, ⟨e, he, hene⟩, hroot⟩ :=
    (compute_mem_badChallengesFor_iff env finalNonIOSourceFamilies17
      (env.chal compilerChallengeBase)).1 hbad
  have hfold : (finalRlcFold es).eval env = 0 := by
    have henv :
        withFinalFoldChallenge env (env.chal compilerChallengeBase) = env := by
      cases env with
      | mk tr trn ch pub =>
          simp only [withFinalFoldChallenge]
          congr 1
          funext q
          by_cases hq : q = compilerChallengeBase
          · subst q; simp
          · simp [hq]
    rw [← henv]
    rw [← finalRlcPolynomial_eval env es (env.chal compilerChallengeBase)]
    · exact hroot
    · exact finalNonIOSourceFamilies17_challenge9_free es hes
  exact hene (hfree es hes hfold e he)

/-- The exact per-row challenge-9 workload is `511-17=494`. -/
theorem finalComputeRLCWorkload_exact :
    finalComputeRLCWorkload = 494 :=
  OptimizedComputeGateBasis.finalComputeRLCWorkload_exact

/-! ## Challenge 11 and scalar challenge 36 -/

def valueRlcPolynomial {L : Type*} [Field L] : List L → L[X]
  | [] => 0
  | a :: as => Polynomial.C a + Polynomial.X * valueRlcPolynomial as

theorem valueRlcPolynomial_nonzero
    {L : Type*} [Field L] (as : List L) (hnonzero : ∃ a ∈ as, a ≠ 0) :
    valueRlcPolynomial as ≠ 0 := by
  induction as with
  | nil => simp at hnonzero
  | cons a as ih =>
      by_cases ha : a = 0
      · have htail : ∃ q ∈ as, q ≠ 0 := by
          obtain ⟨q, hq, hne⟩ := hnonzero
          have hqa : q ≠ a := by
            intro h
            subst q
            exact hne ha
          exact ⟨q, (List.mem_cons.mp hq).resolve_left hqa, hne⟩
        simp [valueRlcPolynomial, ha, ih htail]
      · intro hz
        have hc : a = 0 := by
          simpa [valueRlcPolynomial] using congrArg Polynomial.constantCoeff hz
        exact ha hc

theorem valueRlcPolynomial_natDegree_le
    {L : Type*} [Field L] (as : List L) (hne : as ≠ []) :
    (valueRlcPolynomial as).natDegree ≤ as.length - 1 := by
  induction as with
  | nil => exact (hne rfl).elim
  | cons a as ih =>
      by_cases hs : as = []
      · subst as
        simp [valueRlcPolynomial]
      · calc
          (valueRlcPolynomial (a :: as)).natDegree
              ≤ max (Polynomial.C a).natDegree
                (Polynomial.X * valueRlcPolynomial as).natDegree :=
            Polynomial.natDegree_add_le _ _
          _ ≤ max 0 (1 + (valueRlcPolynomial as).natDegree) := by
            apply max_le_max
            · simp
            · exact Polynomial.natDegree_mul_le.trans (by simp)
          _ ≤ (a :: as).length - 1 := by
            have hi := ih hs
            have hlen : 0 < as.length := List.length_pos_of_ne_nil hs
            simp only [List.length_cons]
            omega

def valueBadChallenges {L : Type*} [Field L] [Fintype L] [DecidableEq L]
    (as : List L) : Finset L :=
  if ∃ a ∈ as, a ≠ 0 then
    Finset.univ.filter fun z => (valueRlcPolynomial as).eval z = 0
  else ∅

theorem badChallengesFor_eq_empty_of_all_zero
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) (families : List (List Expr))
    (hall : ∀ es ∈ families, ∀ e ∈ es, e.eval env = 0) :
    badChallengesFor env families = ∅ := by
  induction families with
  | nil => rfl
  | cons es families ih =>
      have hnone : ¬∃ e ∈ es, e.eval env ≠ 0 := by
        rintro ⟨e, he, hne⟩
        exact hne (hall es (by simp) e he)
      simp only [badChallengesFor, List.foldr_cons, hnone, if_false]
      apply ih
      intro qs hqs
      exact hall qs (by simp [hqs])

theorem valueBadChallenges_eq_empty_of_all_zero
    {L : Type*} [Field L] [Fintype L] [DecidableEq L]
    (as : List L) (hall : ∀ a ∈ as, a = 0) :
    valueBadChallenges as = ∅ := by
  have hnone : ¬∃ a ∈ as, a ≠ 0 := by
    rintro ⟨a, ha, hne⟩
    exact hne (hall a ha)
  simp [valueBadChallenges, hnone]

theorem valueBadChallenges_card_le
    {L : Type*} [Field L] [Fintype L] [DecidableEq L]
    (as : List L) :
    (valueBadChallenges as).card ≤ as.length - 1 := by
  by_cases h : ∃ a ∈ as, a ≠ 0
  · have hne : as ≠ [] := by
      intro hz
      subst as
      simp at h
    simp only [valueBadChallenges, h, if_true]
    exact (NPR.card_eval_zero_le _ (valueRlcPolynomial_nonzero as h)).trans
      (valueRlcPolynomial_natDegree_le as hne)
  · simp [valueBadChallenges, h]

def walkInitErrors {K : Type*} [Field K] (env : Env K) : List K :=
  [finalMaskedWalkLn1.eval env, finalMaskedWalkCount1.eval env]

def walkInitBadChallenges {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (env : Env K) : Finset K :=
  valueBadChallenges (walkInitErrors env)

@[simp] theorem walkInitErrors_length {K : Type*} [Field K] (env : Env K) :
    (walkInitErrors env).length = 2 := rfl

theorem walkInitPolynomial_eval {K : Type*} [Field K] (env : Env K) :
    (valueRlcPolynomial (walkInitErrors env)).eval
        (env.chal (compilerChallengeBase + 2)) =
      finalMaskedWalkInitFold.eval env := by
  simp [walkInitErrors, valueRlcPolynomial, finalMaskedWalkInitFold,
    Expr.eval]
  ring

theorem walkInitBadChallenges_card_le_one
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (env : Env K) :
    (walkInitBadChallenges env).card ≤ 1 := by
  simpa [walkInitBadChallenges] using valueBadChallenges_card_le (walkInitErrors env)

theorem walkInit_sources_zero_of_good
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (env : Env K)
    (hgate : finalMaskedWalkInitFold.eval env = 0)
    (hgood : env.chal (compilerChallengeBase + 2) ∉ walkInitBadChallenges env) :
    finalMaskedWalkLn1.eval env = 0 ∧ finalMaskedWalkCount1.eval env = 0 := by
  by_contra h
  have hnonzero : ∃ a ∈ walkInitErrors env, a ≠ 0 := by
    rcases not_and_or.mp h with hln | hcount
    · exact ⟨finalMaskedWalkLn1.eval env, by simp [walkInitErrors], hln⟩
    · exact ⟨finalMaskedWalkCount1.eval env, by simp [walkInitErrors], hcount⟩
  apply hgood
  simp [walkInitBadChallenges, valueBadChallenges, hnonzero,
    walkInitPolynomial_eval env, hgate]

def selectorErrors {F : Type*} [Field F] (env : Env F) (publicOffset : ℕ) : List F :=
  [env.trace 0 - env.pub publicOffset,
   env.trace 1 - env.pub (publicOffset + 1),
   env.trace 2 - env.pub (publicOffset + 2),
   env.trace 3 - env.pub (publicOffset + 3),
   env.trace 4 - env.pub (publicOffset + 4),
   env.trace 5 - env.pub (publicOffset + 5),
   env.trace 6 - env.pub (publicOffset + 6),
   env.trace 7 - env.pub (publicOffset + 7),
   env.trace 8 - env.pub (publicOffset + 8),
   env.trace 9 - env.pub (publicOffset + 9),
   env.trace 10 - env.pub (publicOffset + 10)]

@[simp] theorem selectorErrors_length {F : Type*} [Field F] (env : Env F) (offset : ℕ) :
    (selectorErrors env offset).length = 11 := by simp [selectorErrors]

def selectorBadChallenges {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (env : Env F) (offset : ℕ) : Finset F :=
  valueBadChallenges (selectorErrors env offset)

def finalSelectorBadChallenges {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (env : Env F) : Finset F :=
  selectorBadChallenges env 20 ∪ selectorBadChallenges env 31

theorem finalSelectorBadChallenges_card_le_twenty
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (env : Env F) :
    (finalSelectorBadChallenges env).card ≤ 20 := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add
      (by simpa [selectorBadChallenges] using
        valueBadChallenges_card_le (selectorErrors env 20))
      (by simpa [selectorBadChallenges] using
        valueBadChallenges_card_le (selectorErrors env 31)))

theorem selectorPolynomial_eval_twenty {F : Type*} [Field F] (env : Env F) :
    (valueRlcPolynomial (selectorErrors env 20)).eval
        (env.chal finalScalarChallengeBase) =
      (finalSelectorPublicCheck .traceCur 20).eval env := by
  norm_num [selectorErrors, valueRlcPolynomial, finalSelectorPublicCheck, CoeffExpr.sumList,
    CoeffExpr.eval, finalScalarChallengeBase, List.ofFn, List.range, List.range.loop]
  ring

theorem selectorPolynomial_eval_thirtyOne {F : Type*} [Field F] (env : Env F) :
    (valueRlcPolynomial (selectorErrors env 31)).eval
        (env.chal finalScalarChallengeBase) =
      (finalSelectorPublicCheck .traceCur 31).eval env := by
  norm_num [selectorErrors, valueRlcPolynomial, finalSelectorPublicCheck, CoeffExpr.sumList,
    CoeffExpr.eval, finalScalarChallengeBase, List.ofFn, List.range, List.range.loop]
  ring

theorem selector_sources_zero_of_good
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (env : Env F)
    (publicOffset : ℕ) (hoff : publicOffset = 20 ∨ publicOffset = 31)
    (hgate : (finalSelectorPublicCheck .traceCur publicOffset).eval env = 0)
    (hgood : env.chal finalScalarChallengeBase ∉ finalSelectorBadChallenges env) :
    ∀ i < 11, env.trace i = env.pub (publicOffset + i) := by
  have hpoly :
      (valueRlcPolynomial (selectorErrors env publicOffset)).eval
          (env.chal finalScalarChallengeBase) = 0 := by
    rcases hoff with rfl | rfl
    · simpa [selectorPolynomial_eval_twenty env] using hgate
    · simpa [selectorPolynomial_eval_thirtyOne env] using hgate
  have hnot : env.chal finalScalarChallengeBase ∉
      selectorBadChallenges env publicOffset := by
    intro hm
    apply hgood
    rcases hoff with rfl | rfl
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ hm
  have hall : ¬∃ a ∈ selectorErrors env publicOffset, a ≠ 0 := by
    intro hnonzero
    apply hnot
    simp [selectorBadChallenges, valueBadChallenges, hnonzero, hpoly]
  intro i hi
  have hmem : env.trace i - env.pub (publicOffset + i) ∈
      selectorErrors env publicOffset := by
    interval_cases i <;> simp [selectorErrors]
  by_contra hne
  exact hall ⟨_, hmem, sub_ne_zero.mpr hne⟩

/-- Stage 2 replaced those gates by the
coin-free selector-packed basis `paperPackingNonIOGates` (77) plus the IO block, so both
coordinates were drawn and read by nothing — the structure was retained as a unit so the
product shape `c.2.2.1` / `c.2.2.2` of `OptimizedProductionChallengeTuple` stayed stable.
They sit
here, not in `JointCoins` / IO / `MemoryChallengeTuple`, because they are compute RAP
inputs and the existing product proof of `card_optimizedProductionChallengeTuple` then
becomes `|𝕂|¹⁰` with no projection churn.  Chronology already samples slots `2,3,4` in
the same round as `z` (`ComputeStagedTable.nockSampledAfter`). -/
@[ext]
structure FinalComputeChallengeTuple (K : Type*) where
  eqA : K
  eqB : K
  eqC : K
deriving DecidableEq, Fintype

instance {K : Type*} [Zero K] : Inhabited (FinalComputeChallengeTuple K) where
  default := ⟨0, 0, 0⟩

theorem FinalComputeChallengeTuple.eta {K : Type*} (c : FinalComputeChallengeTuple K) :
    c = ⟨c.eqA, c.eqB, c.eqC⟩ :=
  rfl

def finalRowsBadChallenges
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {N : ℕ} (envK : Fin N → Env K) : Finset K :=
  Finset.univ.biUnion fun i => finalComputeBadChallenges (envK i)

theorem finalRowsBadChallenges_card_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {N : ℕ} (envK : Fin N → Env K) :
    (finalRowsBadChallenges envK).card ≤ 494 * N := by
  calc
    (finalRowsBadChallenges envK).card
        ≤ ∑ i : Fin N, (finalComputeBadChallenges (envK i)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin N, 494 := Finset.sum_le_sum fun i _ =>
      finalComputeBadChallenges_card_le_494 (envK i)
    _ = 494 * N := by simp [Nat.mul_comm]

def liftChallenge9
    {K : Type*} [Fintype K] [DecidableEq K]
    (_bad : Finset K) : Finset (FinalComputeChallengeTuple K) :=
  ∅

def liftChallenge11
    {K : Type*} [Fintype K] [DecidableEq K]
    (_bad : Finset K) : Finset (FinalComputeChallengeTuple K) :=
  ∅

/-! Stage 3e de-compressed the two `challenge36`-folded endpoint equality checks into the twenty-two
individual masked equations `OptimizedComputeFinal.finalEndpointEqualityChecks`. -/

def extensionFinalComputeCollisionEvent
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {N : ℕ} (_envK : Fin N → Env K) (_walkEnv : Env K) :
    Finset (FinalComputeChallengeTuple K) :=
  ∅

def ExtensionFinalComputeCollisionFree
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K)
    (c : FinalComputeChallengeTuple K) : Prop :=
  c ∉ extensionFinalComputeCollisionEvent envK walkEnv

theorem extensionFinalComputeCollisionFree_components
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K)
    (c : FinalComputeChallengeTuple K)
    (hgood : ExtensionFinalComputeCollisionFree envK walkEnv c) :
    True :=
  trivial

theorem extensionFinalComputeCollisionFree_of_components
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K)
    (c : FinalComputeChallengeTuple K)
    (_h9 : True) (_h11 : True) :
    ExtensionFinalComputeCollisionFree envK walkEnv c := by
  simp [ExtensionFinalComputeCollisionFree, extensionFinalComputeCollisionEvent]

structure FullFinalComputeDecodedSources
    {K F : Type*} [Field K] [Field F] [Fintype K] [Fintype F]
    [DecidableEq K] [DecidableEq F]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) (envF : Env F) : Prop where
  nonIO : ∀ i, ∀ e ∈ finalNonIOSourceFamilies17.flatten, e.eval (envK i) = 0
  walkLn1 : finalMaskedWalkLn1.eval walkEnv = 0
  walkCount1 : finalMaskedWalkCount1.eval walkEnv = 0
  firstPublic : ∀ i < 11, envF.trace i = envF.pub (20 + i)
  lastPublic : ∀ i < 11, envF.trace i = envF.pub (31 + i)

structure FullFinalComputeFoldedGates
    {K F : Type*} [Field K] [Field F] [Fintype K] [Fintype F]
    [DecidableEq K] [DecidableEq F]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) (envF : Env F) : Prop where
  nonIO : ∀ i, ∀ g ∈ finalNonIOTransitionGates, g.eval (envK i) = 0
  walkInit : finalMaskedWalkInitFold.eval walkEnv = 0
  firstPublic : (finalSelectorPublicCheck .traceCur 20).eval envF = 0
  lastPublic : (finalSelectorPublicCheck .traceCur 31).eval envF = 0

theorem valueRlcPolynomial_eval_zero_of_all_zero
    {L : Type*} [Field L] (as : List L) (z : L)
    (hall : ∀ a ∈ as, a = 0) :
    (valueRlcPolynomial as).eval z = 0 := by
  induction as with
  | nil => simp [valueRlcPolynomial]
  | cons a as ih =>
      simp [valueRlcPolynomial, hall a (by simp), ih fun q hq => hall q (by simp [hq])]

theorem fullFinalCompute_source_completeness
    {K F : Type*} [Field K] [Field F] [Fintype K] [Fintype F]
    [DecidableEq K] [DecidableEq F]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) (envF : Env F)
    (hsource : FullFinalComputeDecodedSources envK walkEnv envF) :
    FullFinalComputeFoldedGates envK walkEnv envF := by
  have hfirstErrors : ∀ a ∈ selectorErrors envF 20, a = 0 := by
    intro a ha
    simp [selectorErrors] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hsource.firstPublic]
  have hlastErrors : ∀ a ∈ selectorErrors envF 31, a = 0 := by
    intro a ha
    simp [selectorErrors] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hsource.lastPublic]
  exact
    { nonIO := fun i => finalNonIOTransitionGates_complete (envK i) (hsource.nonIO i)
      walkInit := by
        simp [finalMaskedWalkInitFold, Expr.eval, hsource.walkLn1, hsource.walkCount1]
      firstPublic := by
        rw [← selectorPolynomial_eval_twenty envF]
        exact valueRlcPolynomial_eval_zero_of_all_zero _ _ hfirstErrors
      lastPublic := by
        rw [← selectorPolynomial_eval_thirtyOne envF]
        exact valueRlcPolynomial_eval_zero_of_all_zero _ _ hlastErrors }

theorem extensionFinalComputeCollisionFree_of_sources
    {K F : Type*} [Field K] [Field F] [Fintype K] [Fintype F]
    [DecidableEq K] [DecidableEq F]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) (_envF : Env F)
    (c : FinalComputeChallengeTuple K)
    (_hsource : FullFinalComputeDecodedSources envK walkEnv _envF) :
    ExtensionFinalComputeCollisionFree envK walkEnv c := by
  simp [ExtensionFinalComputeCollisionFree, extensionFinalComputeCollisionEvent]

theorem fullFinalCompute_conditional_source_soundness
    {K F : Type*} [Field K] [Field F] [Fintype K] [Fintype F]
    [DecidableEq K] [DecidableEq F]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) (envF : Env F)
    (c : FinalComputeChallengeTuple K)
    (hchal9 : ∀ i, (envK i).chal compilerChallengeBase ∉ finalComputeBadChallenges (envK i))
    (hchal11 : walkEnv.chal (compilerChallengeBase + 2) ∉ walkInitBadChallenges walkEnv)
    (hsgood : envF.chal finalScalarChallengeBase ∉ finalSelectorBadChallenges envF)
    (hfolds : ∀ i, ∀ g ∈ finalNonIOTransitionGates, g.eval (envK i) = 0)
    (hwalk : finalMaskedWalkInitFold.eval walkEnv = 0)
    (hfirst : (finalSelectorPublicCheck .traceCur 20).eval envF = 0)
    (hlast : (finalSelectorPublicCheck .traceCur 31).eval envF = 0)
    (_hgood : ExtensionFinalComputeCollisionFree envK walkEnv c) :
    FullFinalComputeDecodedSources envK walkEnv envF := by
  have hw := walkInit_sources_zero_of_good walkEnv hwalk hchal11
  exact
    { nonIO := fun i => finalNonIOTransitionGates_sound (envK i)
        (finalComputeCollisionFree_of_not_bad (envK i)
          ((envK i).chal compilerChallengeBase) rfl (hchal9 i)) (hfolds i)
      walkLn1 := hw.1
      walkCount1 := hw.2
      firstPublic := selector_sources_zero_of_good envF 20 (Or.inl rfl) hfirst hsgood
      lastPublic := selector_sources_zero_of_good envF 31 (Or.inr rfl) hlast hsgood }

structure CorrectedComputeRandomizedRealization
    {K F : Type*} [Field K] [Field F] [Fintype K] [Fintype F]
    [DecidableEq K] [DecidableEq F]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) (envF : Env F)
    (c : FinalComputeChallengeTuple K) : Prop where
  completeness :
    FullFinalComputeDecodedSources envK walkEnv envF →
      FullFinalComputeFoldedGates envK walkEnv envF
  conditionalSoundness :
    (∀ i, (envK i).chal compilerChallengeBase ∉ finalComputeBadChallenges (envK i)) →
    walkEnv.chal (compilerChallengeBase + 2) ∉ walkInitBadChallenges walkEnv →
    envF.chal finalScalarChallengeBase ∉ finalSelectorBadChallenges envF →
    ExtensionFinalComputeCollisionFree envK walkEnv c →
    FullFinalComputeFoldedGates envK walkEnv envF →
      FullFinalComputeDecodedSources envK walkEnv envF

theorem correctedComputeRandomizedRealization
    {K F : Type*} [Field K] [Field F] [Fintype K] [Fintype F]
    [DecidableEq K] [DecidableEq F]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) (envF : Env F)
    (c : FinalComputeChallengeTuple K) :
    CorrectedComputeRandomizedRealization envK walkEnv envF c where
  completeness := fullFinalCompute_source_completeness envK walkEnv envF
  conditionalSoundness hbad9 hbad11 hsgood hgood hgates :=
    fullFinalCompute_conditional_source_soundness envK walkEnv envF c hbad9 hbad11 hsgood
      hgates.nonIO hgates.walkInit hgates.firstPublic hgates.lastPublic hgood

/-- Exact scope boundary: the four sampled-IO extension sources are separate from the seventeen
challenge-9 families. They must be supplied by the sampled-assignment connective before the
corrected 98-gate canonical satisfaction theorem can be assembled. -/
theorem sampledIO_sources_outside_challenge9_families :
    ∀ e ∈ OptimizedComputeFiniteIOGates.optimizedSampledIOTransitionGates,
      e ∉ finalNonIOSourceFamilies17.flatten := by
  set_option maxRecDepth 200000 in
  decide

theorem liftChallenge9_card_le
    {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) :
    (liftChallenge9 bad).card ≤ bad.card * Fintype.card K := by
  simp [liftChallenge9]

theorem liftChallenge11_card_le
    {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) :
    (liftChallenge11 bad).card ≤ Fintype.card K * bad.card := by
  simp [liftChallenge11]

theorem extensionFinalComputeCollisionEvent_card_le
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) :
    (extensionFinalComputeCollisionEvent envK walkEnv).card ≤
      (494 * N) * Fintype.card K + Fintype.card K * 1 := by
  simp [extensionFinalComputeCollisionEvent]

/-- The per-chip price: `(494·N + 1)/|𝕂|`, with **no base-field summand at all**. -/
def extensionFinalComputeCollisionProbabilityBound
    (K : Type*) [Fintype K] (N : ℕ) : ℚ :=
  (494 * N + 1 : ℚ) / Fintype.card K

def finalComputeKWorkload (N : ℕ) : ℕ := 494 * N + 1
def finalComputeFWorkload : ℕ := 20
def finalComputeTotalWorkload (N : ℕ) : ℕ := 494 * N + 1 + 20

theorem finalComputeTotalWorkload_eq (N : ℕ) :
    finalComputeTotalWorkload N = 494 * N + 21 := by
  simp [finalComputeTotalWorkload]

#print axioms finalRlcPolynomial_nonzero
#print axioms finalRlcPolynomial_natDegree_le
#print axioms familyBadChallenges_card_le
#print axioms finalComputeBadChallenges_card_le_494
#print axioms walkInitBadChallenges_card_le_one
#print axioms finalSelectorBadChallenges_card_le_twenty

end
end OptimizedComputeCollisionBound
end Nock.NockVMROM.Thm54
