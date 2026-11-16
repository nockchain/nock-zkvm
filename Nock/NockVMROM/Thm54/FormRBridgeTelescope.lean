/-
  Nock/NockVMROM/Thm54/FormRBridgeTelescope.lean

  Additive; nothing existing is
  retyped; nothing consumes this yet.

  The memory chip's Form R
  accumulators (`pt.indicator` = `pw`, `pt.counts`) are `𝕂` roles.  This module proves, for ANY row
  data `pub : ℕ → Pub K` (1-indexed) that satisfies, row by row,

  * the row's state is the decoded state (`memRowStateOf`, selectors `0..2`);
  * `MemoryTable.eqBlk`;
  * the BFS child link along the followed edges (`lc` / `rc` = the child row's `pt`);
  * the row's `λ` is one `l`;
  * read / verify rows carry `ts = α ^ natLift reqIdx`;
  * read rows carry `(T, C') = (l ^ mm e, (C'poly n (cc e)).eval l)` at their exponent `e`;
  * children sit strictly later, inside the table;

  that the accumulators telescope to the bivariate evaluation of the decoded Form R polynomials:
  `biv α l (formRPw n mm (tree i)) = (pub i).pt.indicator` and
  `biv α l (formRCounts n mm cc (tree i)) = (pub i).pt.counts`, `biv α l P = (P.map (eval l)).eval α`
  (`telescope`).

  Rule 8(b): every theorem here holds for every row datum (it is pure algebra over the listed
  hypotheses); none mentions a trace, an acceptance or an event.
-/
import Nock.NockVMROM.Thm54.DecodedLambdaEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.FormRBridge

open scoped Classical BigOperators Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.RedTeam.Batch575
open Polynomial

noncomputable section

/-! ## 1. Bivariate evaluation -/

section Biv
variable {K : Type} [Field K]

/-- `P(α, l)`: coefficients (polynomials in `Y`) at `Y = l`, then the outer variable at `α`. -/
def biv (α l : K) (P : Polynomial (Polynomial K)) : K := (P.map (evalRingHom l)).eval α

theorem biv_add (α l : K) (P Q : Polynomial (Polynomial K)) :
    biv α l (P + Q) = biv α l P + biv α l Q := by
  simp [biv]

theorem biv_sub (α l : K) (P Q : Polynomial (Polynomial K)) :
    biv α l (P - Q) = biv α l P - biv α l Q := by
  simp [biv]

theorem biv_C_mul (α l : K) (a : Polynomial K) (P : Polynomial (Polynomial K)) :
    biv α l (C a * P) = a.eval l * biv α l P := by
  simp [biv]

theorem biv_C_mul_X_pow (α l : K) (a : Polynomial K) (e : ℕ) :
    biv α l (C a * X ^ e) = a.eval l * α ^ e := by
  simp [biv]

theorem biv_zero (α l : K) : biv α l 0 = 0 := by simp [biv]

theorem eval_Y (l : K) : (Y : Polynomial K).eval l = l := by simp [Y]

theorem eval_scale (l : K) (n : ℕ) : (scale (K := K) n).eval l = l ^ (n - 1) := by
  simp [scale, Y]

theorem eval_Tpoly (l : K) (m : ℕ) : (Tpoly (K := K) m).eval l = l ^ m := by
  simp [Tpoly, Y]

/-- Coefficient form of `biv` below a degree bound (`Polynomial.eval_eq_sum_range'`). -/
theorem biv_eq_sum_range (α l : K) (P : Polynomial (Polynomial K)) (E : ℕ)
    (hE : ∀ k, E < k → P.coeff k = 0) :
    biv α l P = ∑ k ∈ Finset.range (E + 1), α ^ k * (P.coeff k).eval l := by
  have hdeg : (P.map (evalRingHom l)).natDegree < E + 1 := by
    refine Nat.lt_succ_of_le ?_
    refine (natDegree_map_le).trans ?_
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    exact hE k (by exact_mod_cast hk)
  unfold biv
  rw [eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_map, coe_evalRingHom, mul_comm]

/-- **The envelope is `biv`** once every coefficient above `E` vanishes. -/
theorem envelope_eq_biv (α l : K) (P : Polynomial (Polynomial K)) (E : ℕ)
    (hE : ∀ k, E < k → P.coeff k = 0) :
    formREnvelope P E α l = biv α l P := by
  rw [biv_eq_sum_range α l P E hE]
  rfl

end Biv

/-! ## 2. Exponent bounds on `MTree` -/

section ExpBound
variable {K : Type} [Field K]

/-- Every read / verify exponent of `t` is `≤ E`. -/
def ExpLe (E : ℕ) (t : MTree K) : Prop := ∀ e, E < e → readCount e t = 0 ∧ verifyCount e t = 0

theorem expLe_halt (E : ℕ) : ExpLe E (.halt : MTree K) := fun _ _ => ⟨rfl, rfl⟩

theorem expLe_decompose {E : ℕ} {L R : MTree K} (hL : ExpLe E L) (hR : ExpLe E R) :
    ExpLe E (.decompose L R) := fun e he => by
  simp [readCount, verifyCount, (hL e he).1, (hL e he).2, (hR e he).1, (hR e he).2]

theorem expLe_read {E e' : ℕ} {ch : MTree K} (he' : e' ≤ E) (h : ExpLe E ch) :
    ExpLe E (.read e' ch) := fun e he => by
  have hne : e' ≠ e := by omega
  simp [readCount, verifyCount, hne, (h e he).1, (h e he).2]

theorem expLe_verify {E e' : ℕ} {a : K} {ch : MTree K} (he' : e' ≤ E) (h : ExpLe E ch) :
    ExpLe E (.verify e' a ch) := fun e he => by
  have hne : e' ≠ e := by omega
  simp [readCount, verifyCount, hne, (h e he).1, (h e he).2]

/-- Coefficients of `formRCounts` above an exponent bound vanish (`absent_coeff`). -/
theorem formRCounts_coeff_eq_zero_of_expLe (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool)
    {E : ℕ} {t : MTree K} (h : ExpLe E t) :
    ∀ k, E < k → (formRCounts n mm cc t).coeff k = 0 := fun k hk =>
  absent_coeff n mm cc k t (h k hk).1 (h k hk).2

end ExpBound

/-! ## 3. The telescope over the decoded tree -/

section Telescope
variable {F K : Type} [Field F] [Field K] [DecidableEq F] {M : ℕ}
variable (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ)

/-- The decoded state of 1-indexed row `i` (`memRowStateOf` of base row `i − 1`). -/
def stAt (i : ℕ) (h : 1 ≤ i ∧ i ≤ M) : MState := memRowStateOf (envsF ⟨i - 1, by omega⟩)

/-- The decoded exponent of 1-indexed row `i`. -/
def expAt (i : ℕ) (h : 1 ≤ i ∧ i ≤ M) : ℕ := rowExp envsF ⟨i - 1, by omega⟩

/-- **The row hypotheses of the telescope** (all per 1-indexed row `1 ≤ i ≤ M`). -/
structure TelescopeRows (pub : ℕ → Pub K) (inp : ℕ → Inputs K) (α l : K) (n : ℕ)
    (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) : Prop where
  /-- The row's state is the decoded state. -/
  st : ∀ i (h : 1 ≤ i ∧ i ≤ M), (pub i).st = stAt envsF i h
  /-- `eqBlk` (the per-row Form R recurrences). -/
  eqBlk : ∀ i (h : 1 ≤ i ∧ i ≤ M), MemoryTable.eqBlk (inp i) (pub i)
  /-- One `λ` on every row. -/
  lam : ∀ i (h : 1 ≤ i ∧ i ≤ M), (pub i).lambda = l
  /-- The followed left child is the row's `lc`. -/
  link1 : ∀ i (h : 1 ≤ i ∧ i ≤ M), 1 ≤ foOfMem envsF i →
    (pub i).lc = (pub (childIdx envsF kroots i 1)).pt
  /-- The followed right child is the row's `rc`. -/
  link2 : ∀ i (h : 1 ≤ i ∧ i ≤ M), 2 ≤ foOfMem envsF i →
    (pub i).rc = (pub (childIdx envsF kroots i 2)).pt
  /-- Children sit strictly later, inside the table. -/
  order : ∀ i (h : 1 ≤ i ∧ i ≤ M) (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ foOfMem envsF i →
    i < childIdx envsF kroots i ℓ ∧ childIdx envsF kroots i ℓ ≤ M
  /-- Read / verify rows carry `ts = α ^ e` at their decoded exponent. -/
  ts : ∀ i (h : 1 ≤ i ∧ i ≤ M), (stAt envsF i h = .read_root ∨ stAt envsF i h = .verify_child) →
    (pub i).mem.ts = α ^ expAt envsF i h
  /-- Read rows carry the located certificate's `(T, C')` at `λ`. -/
  axis : ∀ i (h : 1 ≤ i ∧ i ≤ M), stAt envsF i h = .read_root →
    (pub i).mem.axis = l ^ mm (expAt envsF i h)
  cprime : ∀ i (h : 1 ≤ i ∧ i ≤ M), stAt envsF i h = .read_root →
    (pub i).cprime = (C'poly (K := K) n (cc (expAt envsF i h))).eval l
  /-- The scale exponent is the certificate width (`formRN_sub_one` at `n = formRN K`). -/
  scale : MemoryTable.pwScaleExp K = n - 1

variable {envsF kroots}
variable {pub : ℕ → Pub K} {inp : ℕ → Inputs K} {α l : K} {n : ℕ}
  {mm : ℕ → ℕ} {cc : ℕ → ℕ → Bool}

/-- **THE TELESCOPE.**  On every row, the memory chip's Form R accumulators are the bivariate
evaluation at `(α, λ)` of the decoded tree's `formRPw` / `formRCounts`. -/
theorem telescope (H : TelescopeRows envsF kroots pub inp α l n mm cc) :
    ∀ i (h : 1 ≤ i ∧ i ≤ M),
      biv α l (formRPw n mm (decodedMTreeOfEnvs envsK envsF kroots i)) = (pub i).pt.indicator ∧
      biv α l (formRCounts n mm cc (decodedMTreeOfEnvs envsK envsF kroots i)) =
        (pub i).pt.counts := by
  have key : ∀ i, (1 ≤ i ∧ i ≤ M) →
      biv α l (formRPw n mm (decodedMTreeOfEnvs envsK envsF kroots i)) = (pub i).pt.indicator ∧
      biv α l (formRCounts n mm cc (decodedMTreeOfEnvs envsK envsF kroots i)) =
        (pub i).pt.counts := by
    refine measure_induction (M := M) _ fun i ih h => ?_
    have hfo := foOfMem_eq envsF i h
    have hst := H.st i h
    have hE := H.eqBlk i h
    have hlam := H.lam i h
    have hsc := H.scale
    -- the followed child `ℓ` (when `ℓ ≤ fo`) is a later in-range row, and its subtree is the child's
    have hchild : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ foOfMem envsF i →
        (if i < childIdx envsF kroots i ℓ then
            decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i ℓ) else .halt) =
          decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i ℓ) ∧
        (1 ≤ childIdx envsF kroots i ℓ ∧ childIdx envsF kroots i ℓ ≤ M) ∧
        i < childIdx envsF kroots i ℓ := by
      intro ℓ h1 h2
      obtain ⟨hlt, hle⟩ := H.order i h ℓ h1 h2
      exact ⟨if_pos hlt, ⟨by omega, hle⟩, hlt⟩
    rw [decodedMTreeOfEnvs, dif_pos h]
    unfold stAt at hst
    rcases hs : memRowStateOf (envsF ⟨i - 1, by omega⟩) with _ | _ | _ | _
    · -- decompose
      rw [hs] at hfo hst
      simp only [MemoryTable.fanoutMem] at hfo
      obtain ⟨hc1, hr1, hlt1⟩ := hchild 1 le_rfl (by omega)
      obtain ⟨hc2, hr2, hlt2⟩ := hchild 2 (by omega) (by omega)
      obtain ⟨ihp1, ihc1⟩ := ih _ hlt1 h.1 h.2 hr1
      obtain ⟨ihp2, ihc2⟩ := ih _ hlt2 h.1 h.2 hr2
      have hl1 := H.link1 i h (by omega)
      have hl2 := H.link2 i h (by omega)
      have hb : MemoryTable.eqBlk (inp i) (pub i) := hE
      simp only [MemoryTable.eqBlk, hst] at hb
      obtain ⟨_, hind, hcnt, _⟩ := hb
      rw [hc1, hc2]
      refine ⟨?_, ?_⟩
      · simp only [formRPw]
        rw [biv_C_mul, biv_add, ihp1, ihp2, eval_Y, hind, hl1, hl2, hlam]
      · simp only [formRCounts]
        rw [biv_add, biv_add, biv_add, biv_C_mul, biv_add, ihc1, ihc2, ihp1, ihp2, hcnt, hl1, hl2,
          hlam]
        simp [Polynomial.eval_sub, eval_Y]
    · -- halt
      rw [hs] at hst
      have hb : MemoryTable.eqBlk (inp i) (pub i) := hE
      simp only [MemoryTable.eqBlk, hst] at hb
      obtain ⟨_, _, hind, hcnt, _⟩ := hb
      simp only [formRPw, formRCounts, biv_zero]
      exact ⟨hind.symm, hcnt.symm⟩
    · -- read_root
      rw [hs] at hfo hst
      simp only [MemoryTable.fanoutMem] at hfo
      obtain ⟨hc1, hr1, hlt1⟩ := hchild 1 le_rfl (by omega)
      obtain ⟨ihp1, ihc1⟩ := ih _ hlt1 h.1 h.2 hr1
      have hl1 := H.link1 i h (by omega)
      have hsr : stAt envsF i h = .read_root := by unfold stAt; exact hs
      have hts := H.ts i h (Or.inl hsr)
      have hax := H.axis i h hsr
      have hcp := H.cprime i h hsr
      have hb : MemoryTable.eqBlk (inp i) (pub i) := hE
      simp only [MemoryTable.eqBlk, hst] at hb
      obtain ⟨_, _, hind, hcnt, _, _⟩ := hb
      rw [hc1]
      unfold expAt at hts hax hcp
      refine ⟨?_, ?_⟩
      · simp only [formRPw]
        rw [biv_sub, biv_C_mul_X_pow, ihp1, hind, hl1, hlam, hts, hax, hsc]
        simp only [Polynomial.eval_mul, eval_scale, eval_Tpoly]
        try ring
      · simp only [formRCounts]
        rw [biv_sub, biv_C_mul_X_pow, ihc1, hcnt, hl1, hts, hax, hcp]
        try simp only [Polynomial.eval_mul, eval_Tpoly]
    · -- verify_child
      rw [hs] at hfo hst
      simp only [MemoryTable.fanoutMem] at hfo
      obtain ⟨hc1, hr1, hlt1⟩ := hchild 1 le_rfl (by omega)
      obtain ⟨ihp1, ihc1⟩ := ih _ hlt1 h.1 h.2 hr1
      have hl1 := H.link1 i h (by omega)
      have hsv : stAt envsF i h = .verify_child := by unfold stAt; exact hs
      have hts := H.ts i h (Or.inr hsv)
      have hb : MemoryTable.eqBlk (inp i) (pub i) := hE
      simp only [MemoryTable.eqBlk, hst] at hb
      obtain ⟨_, _, hind, hcnt, _, _⟩ := hb
      rw [hc1]
      unfold expAt at hts
      refine ⟨?_, ?_⟩
      · simp only [formRPw]
        rw [biv_add, biv_C_mul_X_pow, ihp1, hind, hl1, hlam, hts, hsc, eval_scale]
      · simp only [formRCounts]
        rw [biv_add, biv_C_mul_X_pow, ihc1, hcnt, hl1, hlam, hts, hsc, eval_scale]
  exact key

/-- Decoded exponents bounded on the read / verify rows ⇒ the decoded tree's exponents are. -/
theorem expLe_tree {E : ℕ}
    (hexp : ∀ i (h : 1 ≤ i ∧ i ≤ M),
      (stAt envsF i h = .read_root ∨ stAt envsF i h = .verify_child) → expAt envsF i h ≤ E) :
    ∀ i, ExpLe E (decodedMTreeOfEnvs envsK envsF kroots i) := by
  refine measure_induction (M := M) _ fun i ih => ?_
  by_cases h : 1 ≤ i ∧ i ≤ M
  · have hfo := foOfMem_eq envsF i h
    have hchild : ∀ ℓ, ℓ ≤ foOfMem envsF i → 1 ≤ ℓ →
        ExpLe E (if i < childIdx envsF kroots i ℓ then
            decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF kroots i ℓ) else .halt) := by
      intro ℓ h2 h1
      split_ifs with hlt
      · exact ih _ hlt h.1 h.2
      · exact expLe_halt E
    rw [decodedMTreeOfEnvs, dif_pos h]
    rcases hs : memRowStateOf (envsF ⟨i - 1, by omega⟩) with _ | _ | _ | _
    · rw [hs] at hfo
      simp only [MemoryTable.fanoutMem] at hfo
      exact expLe_decompose (hchild 1 (by omega) le_rfl) (hchild 2 (by omega) (by omega))
    · exact expLe_halt E
    · rw [hs] at hfo
      simp only [MemoryTable.fanoutMem] at hfo
      have he := hexp i h (Or.inl (by unfold stAt; exact hs))
      exact expLe_read he (hchild 1 (by omega) le_rfl)
    · rw [hs] at hfo
      simp only [MemoryTable.fanoutMem] at hfo
      have he := hexp i h (Or.inr (by unfold stAt; exact hs))
      exact expLe_verify he (hchild 1 (by omega) le_rfl)
  · rw [tree_out envsK envsF kroots i h]; exact expLe_halt E

end Telescope

/-! ## 4. The root corollary: outside the decoded event, a zero accumulator forces `P_r = 0` -/

section Root
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [Fintype F] [DecidableEq F] {N M : ℕ}
variable (envsC : Fin N → Env K) (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ)

/-- A guarded root polynomial whose envelope vanishes at `(α, l)` puts `(α, l)` in its root set. -/
theorem decodedRootPoly_eq_zero_of_not_bad (r : ℕ) (α l : K)
    (hexp : ExpLe (decodedEnvelopeDeg N) (decodedMTreeOfEnvs envsK envsF kroots r))
    (hzero : biv α l (decodedRootPoly envsC envsK envsF kroots r) = 0)
    (hout : (α, l) ∉ decodedRootBad envsC envsK envsF kroots r) :
    decodedRootPoly envsC envsK envsF kroots r = 0 := by
  have hcoef := formRCounts_coeff_eq_zero_of_expLe (formRN K) (decodedShift envsC)
    (decodedBits envsC) hexp
  unfold decodedRootPoly at hzero ⊢
  by_cases hg : formRGuard (decodedRootPoly envsC envsK envsF kroots r) (decodedEnvelopeDeg N)
  · exfalso
    apply hout
    unfold decodedRootBad
    rw [if_pos hg]
    unfold decodedRootPoly
    simp only [formRRootBad, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [envelope_eq_biv α l _ _ hcoef]
    exact hzero
  · ext k : 1
    by_cases hk : k ≤ decodedEnvelopeDeg N
    · by_contra hne
      exact hg ⟨k, hk, hne⟩
    · rw [coeff_zero]
      exact hcoef k (by omega)

/-- **Root corollary at the event**: a tuple outside `decodedLambdaEventOfEnvs` whose `(αM, λ)`
evaluates every root's decoded polynomial to `0` has every root's decoded polynomial `0`. -/
theorem roots_zero_of_not_event (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hout : c ∉ decodedLambdaEventOfEnvs envsC envsK envsF kroots)
    (hexp : ∀ r, ExpLe (decodedEnvelopeDeg N) (decodedMTreeOfEnvs envsK envsF kroots r))
    (hzero : ∀ r ∈ Finset.Icc 1 kroots,
      biv (alphaM c.1) c.2.2.2.lambda
        (decodedRootPoly envsC envsK envsF kroots r) = 0) :
    ∀ r ∈ Finset.Icc 1 kroots, decodedRootPoly envsC envsK envsF kroots r = 0 := by
  intro r hr
  refine decodedRootPoly_eq_zero_of_not_bad envsC envsK envsF kroots r _ _ (hexp r) (hzero r hr) ?_
  intro hbad
  apply hout
  simp only [decodedLambdaEventOfEnvs, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion]
  exact ⟨r, hr, hbad⟩

end Root

end

end Nock.NockVMROM.Thm54.FormRBridge

#print axioms Nock.NockVMROM.Thm54.FormRBridge.telescope
#print axioms Nock.NockVMROM.Thm54.FormRBridge.envelope_eq_biv
#print axioms Nock.NockVMROM.Thm54.FormRBridge.roots_zero_of_not_event
