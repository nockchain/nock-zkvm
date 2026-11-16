/-
  NockvmE2E/Exec/E2ELinksFri.lean   (proof-only)

  The FRI half of the links: the transcript projections of `toFriPath (sndB (q0P id p))` and the discharge of
  `FriLinkAt` (`SF.Link` = hγ hx hα hCF hP, and `hdeg`).
-/
import NockvmE2E.Exec.E2EEmbed

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.E2EFri

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E

/-! ## 1. `hγ` -/

/-- an element of order `2^n` (`n ≥ 1`) in a field has `γ^(2^(n-1)) = -1` -/
theorem neg_one_of_order {F : Type} [Field F] (u : Fˣ) (n : ℕ) (hn : 1 ≤ n) (ho : orderOf u = 2 ^ n) :
    ((u : Fˣ) : F) ^ 2 ^ (n - 1) = -1 := by
  have h1 : (u ^ 2 ^ (n - 1)) * (u ^ 2 ^ (n - 1)) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    rw [show n - 1 + 1 = n by omega, ← ho]; exact pow_orderOf_eq_one u
  have h2 : u ^ 2 ^ (n - 1) ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [ho] at this
    have := Nat.le_of_dvd (Nat.two_pow_pos _) this
    have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) (show n - 1 < n by omega)
    omega
  have h3 := congrArg (fun v : Fˣ => (v : F)) h1
  have h4 : ((u ^ 2 ^ (n - 1) : Fˣ) : F) ≠ 1 := fun h => h2 (Units.ext h)
  simp only [Units.val_mul, Units.val_one] at h3
  rcases mul_self_eq_one_iff.mp h3 with h | h
  · exact absurd h h4
  · simpa using h

theorem hγ_of_flat (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hok : FlatOk XI H FS zF π)
    (hn32 : XI.nD ≤ 32) (hn1 : 1 ≤ XI.nD) :
    homV.ψ XI.dGen ^ 2 ^ (XI.nD - 1) = -1 := by
  have h := flatOk_dGen XI H FS zF π hok
  show psiV XI.dGen ^ _ = _
  rw [h]
  exact neg_one_of_order _ _ hn1 (orderOf_zeta hn32)

/-- non-vacuity of `hγ`'s shape at `nD = 5`: in the base field `Gold` (`gZ^(2^27)` is a 32nd root) and in `KC` for the instance's `ζ_5`.
(A kernel `decide` on `Gold` would unfold `2^27` multiplications; the statement is the instance's `gZ_pow_2_31_eq` instead.) -/
example : (NockvmE2E.Exec.gZ ^ 2 ^ (32 - 5)) ^ 2 ^ (5 - 1) = -1 := by
  rw [← pow_mul, show 2 ^ (32 - 5) * 2 ^ (5 - 1) = 2 ^ 31 by norm_num]; exact NockvmE2E.Exec.gZ_pow_2_31_eq
example : ((zeta 5 : KCˣ) : KC) ^ 2 ^ (5 - 1) = -1 :=
  neg_one_of_order _ _ (by norm_num) (orderOf_zeta (by norm_num))
example : (2 : ZMod 17) ^ 2 ^ (3 - 1) = -1 := by decide

/-! ## 2. the unary transcript property of the FRI legacy transcript -/

section Proj
open NockvmE2E.FriPort NockvmE2E.Merkle.Fri NockvmE2E.Lift NockvmE2E.Exec.Cover

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

/-- **the property of one legacy entry** that the audited transcript projections read: fold challenge `i` is `αd i`, the final message
is `pfd`, the query vector is `xsd`, and the word `f_{i+1}` is `Wd i` at every point satisfying `Sel i` -/
def QT (αd : Fin (k + 1) → F) (pfd : CompPoly.CPolynomial F) (xsd : Fin l → (ω.subdomain 0).toFinset)
    (Sel : ∀ i : Fin k, wordDom (ω := ω) s i.val → Prop) (Wd : ∀ i : Fin k, wordDom (ω := ω) s i.val → F)
    (j : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) (m : (pSpec k (ω := ω) s l).«Type» j) : Prop :=
  (∀ i : Fin (k + 1), ∀ h : j = (foldChallenge (ω := ω) s l i).val,
    cast (foldChallenge_type s l i) (xp h m) = αd i) ∧
  (∀ h : j = (finalMessage (ω := ω) s l).val, cast (finalMessage_type s l) (xp h m) = pfd) ∧
  (∀ h : j = (queryChallenge (ω := ω) s l).val, cast (queryChallenge_type s l) (xp h m) = xsd) ∧
  (∀ i : Fin k, ∀ h : j = (nonfinalMessage (ω := ω) s l i).val, ∀ y, Sel i y →
    (cast (nonfinalMessage_type s l i) (xp h m) : wordDom (ω := ω) s i.val → F) y = Wd i y)

variable {s d l} {αd : Fin (k + 1) → F} {pfd : CompPoly.CPolynomial F} {xsd : Fin l → (ω.subdomain 0).toFinset}
  {Sel : ∀ i : Fin k, wordDom (ω := ω) s i.val → Prop} {Wd : ∀ i : Fin k, wordDom (ω := ω) s i.val → F}

theorem QT_fold (j : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) (m : (pSpec k (ω := ω) s l).«Type» j)
    (i0 : Fin (k + 1)) (hj : j.val = 2 * i0.val)
    (hm : ∀ h : j = (foldChallenge (ω := ω) s l i0).val, cast (foldChallenge_type s l i0) (xp h m) = αd i0) :
    QT s l αd pfd xsd Sel Wd j m := by
  have hk := friLength (k := k)
  refine ⟨fun i h => ?_, fun h => ?_, fun h => ?_, fun i h => ?_⟩
  · have hi : i = i0 := Fin.ext (by have := congrArg Fin.val h; simp only [foldChallenge_val] at this; omega)
    subst hi; exact hm h
  · exact absurd (congrArg Fin.val h) (by simp only [finalMessage_val]; omega)
  · exact absurd (congrArg Fin.val h) (by simp only [queryChallenge_val]; omega)
  · exact absurd (congrArg Fin.val h) (by simp only [nonfinalMessage_val]; omega)

theorem QT_query (j : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) (m : (pSpec k (ω := ω) s l).«Type» j)
    (hj : j.val = 2 * k + 2)
    (hm : ∀ h : j = (queryChallenge (ω := ω) s l).val, cast (queryChallenge_type s l) (xp h m) = xsd) :
    QT s l αd pfd xsd Sel Wd j m := by
  have hk := friLength (k := k)
  refine ⟨fun i h => ?_, fun h => ?_, hm, fun i h => ?_⟩
  · exact absurd (congrArg Fin.val h) (by simp only [foldChallenge_val]; omega)
  · exact absurd (congrArg Fin.val h) (by simp only [finalMessage_val]; omega)
  · exact absurd (congrArg Fin.val h) (by simp only [nonfinalMessage_val]; omega)

theorem QT_final (j : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) (m : (pSpec k (ω := ω) s l).«Type» j)
    (hj : j.val = 2 * k + 1)
    (hm : ∀ h : j = (finalMessage (ω := ω) s l).val, cast (finalMessage_type s l) (xp h m) = pfd) :
    QT s l αd pfd xsd Sel Wd j m := by
  have hk := friLength (k := k)
  refine ⟨fun i h => ?_, hm, fun h => ?_, fun i h => ?_⟩
  · exact absurd (congrArg Fin.val h) (by simp only [foldChallenge_val]; omega)
  · exact absurd (congrArg Fin.val h) (by simp only [queryChallenge_val]; omega)
  · exact absurd (congrArg Fin.val h) (by simp only [nonfinalMessage_val]; omega)

theorem QT_word (j : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) (m : (pSpec k (ω := ω) s l).«Type» j)
    (i0 : Fin k) (hj : j.val = 2 * i0.val + 1)
    (hm : ∀ h : j = (nonfinalMessage (ω := ω) s l i0).val, ∀ y, Sel i0 y →
      (cast (nonfinalMessage_type s l i0) (xp h m) : wordDom (ω := ω) s i0.val → F) y = Wd i0 y) :
    QT s l αd pfd xsd Sel Wd j m := by
  have hk := friLength (k := k)
  refine ⟨fun i h => ?_, fun h => ?_, fun h => ?_, fun i h => ?_⟩
  · exact absurd (congrArg Fin.val h) (by simp only [foldChallenge_val]; omega)
  · exact absurd (congrArg Fin.val h) (by simp only [finalMessage_val]; omega)
  · exact absurd (congrArg Fin.val h) (by simp only [queryChallenge_val]; omega)
  · have hi : i = i0 := Fin.ext (by have := congrArg Fin.val h; simp only [nonfinalMessage_val] at this; omega)
    subst hi; exact hm h

end Proj

/-! ## 3. the tail induction (on `c` in `friMerkleMask i c`) -/

section Tail
open NockvmE2E.FriPort NockvmE2E.Merkle.Fri NockvmE2E.Lift NockvmE2E.Exec.Cover NockvmE2E.Exec.SL NockvmE2E.Exec.Layout

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : FriLeaves (ω := ω) s) (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg)
  (Op : Type) [Finite Op] [DecidableEq Op]

/-- the opened digest at every selected leaf of FRI word `i` is the codec image of the flat leaf value `lvK i (leafNum t)` (B6-1b) -/
def ValF (lvK : ℕ → ℕ → F) : (i c : ℕ) → (h : i + c = k) →
    OpenAll Dg (merkleSkels (friMerkleMask s d l L Dg enc i c h)) → Prop
  | _, 0, _, _ => True
  | i, c + 1, h, (o, os) =>
      (∀ t (hs : o.selector.get t = true), selectedValueAt o.values t hs = enc (lvK i (leafNum t))) ∧
        ValF lvK i.succ c (by omega) os

/-- the challenge codecs of the folding rounds read the fold challenge as `decA` of the flat limbs -/
def CodOK (decA : List ℕ → F) : (i c : ℕ) → (h : i + c = k) → MDec (friMerkleMask s d l L Dg enc i c h) → Prop
  | _, 0, _, _ => True
  | i, c + 1, h, (cc, ds) =>
      (∀ x, cast (foldChallenge_type (ω := ω) s l ⟨i + 1, by omega⟩)
        (xp (a := ⟨2 * i + 2, by have := friLength (k := k); omega⟩) (b := (foldChallenge (ω := ω) s l ⟨i + 1, by omega⟩).val)
          (Fin.ext (by simp only [foldChallenge_val]; omega)) (cc.decC x)) = decA x) ∧
        CodOK decA i.succ c (by omega) ds

/-- the final polynomial of a compiled path (the clear message of the last round) -/
def finPolyOf : (i c : ℕ) → (h : i + c = k) →
    (protocol (compiledRoundsK Dg Op (friMerkleMask s d l L Dg enc i c h))).tree.ExecutionPath → CompPoly.CPolynomial F
  | i, 0, h, p => cast (finalMessage_type (ω := ω) s l)
      (xp (a := ⟨2 * i + 1, by have := friLength (k := k); omega⟩) (b := (finalMessage (ω := ω) s l).val)
        (Fin.ext (by simp only [finalMessage_val]; omega)) p.1.1)
  | i, c + 1, h, p => finPolyOf i.succ c (by omega) p.2.2

theorem finPoly_deg : (c i : ℕ) → (h : i + c = k) →
    (p : (protocol (compiledRoundsK Dg Op (friMerkleMask s d l L Dg enc i c h))).tree.ExecutionPath) →
    (finPolyOf s d l L Dg enc Op i c h p).natDegree < d.val
  | 0, i, h, p => by
      subst h
      simpa [finPolyOf, xp, cast_cast] using p.1.2 rfl
  | c + 1, i, h, p => finPoly_deg c i.succ (by omega) p.2.2

/-- a word's value at a selected leaf, from `Agrees` and the digest link -/
theorem word_at (lvK : ℕ → ℕ → F) (i : Fin k) (h : 2 * i.val + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)
    (o : BatchOpening Dg (L.skel i)) (q1 : FriMsg (ω := ω) s d l i.val h)
    (hA : o.values.map (codecDec ⟨0⟩ enc) = selectedValues (friWords s d l L i h q1) o.selector)
    (hv : ∀ t (hs : o.selector.get t = true), selectedValueAt o.values t hs = enc (lvK i.val (leafNum t)))
    (y : wordDom (ω := ω) s i.val) (hy : o.selector.get ((L.idx i).symm y) = true) :
    friMsgEquivFun s d l i.val h i.2 q1 y = lvK i.val (leafNum ((L.idx i).symm y)) := by
  have e1 := friWords_get s d l L i h q1 ((L.idx i).symm y)
  rw [Equiv.apply_symm_apply] at e1
  rw [← e1, ← selectedValueAt_selectedValues ((L.idx i).symm y) (friWords s d l L i h q1) o.selector hy, ← hA,
    selectedValueAt_map, hv _ hy, codecDec_enc]

theorem msg_cast_eq (i : Fin k) (hh : 2 * i.val + 1 < (Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)
    (h : (⟨2 * i.val + 1, hh⟩ : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) = (nonfinalMessage (ω := ω) s l i).val)
    (mm : FriMsg (ω := ω) s d l i.val hh) :
    (cast (nonfinalMessage_type s l i) (xp h mm.1) : wordDom (ω := ω) s i.val → F) =
      friMsgEquivFun s d l i.val hh i.2 mm := by
  apply eq_of_heq
  refine (cast_heq _ _).trans ((cast_heq _ _).trans ?_)
  exact (cast_heq _ _).symm

/-- the selector set and the leaf values of FRI word `i`, as predicates on the word's domain -/
abbrev SelT (Qs : ℕ → ℕ → Prop) : ∀ i : Fin k, wordDom (ω := ω) s i.val → Prop :=
  fun i y => Qs i.val (leafNum ((L.idx i).symm y))
abbrev WdT (lvK : ℕ → ℕ → F) : ∀ i : Fin k, wordDom (ω := ω) s i.val → F :=
  fun i y => lvK i.val (leafNum ((L.idx i).symm y))

/-- **the tail projection**: along a base path `q` agreeing with the compiled path `p` and the openings `os`, every entry of the
legacy transcript has the `QT` property for the data (fold challenges = `decA` of the flat limbs, the final polynomial of `p`, the query
vector of `p`, the words at the selected leaves = the flat leaf values) -/
theorem tail_StepRel (dY' : List ℕ → Dg) (ω0 : Op) (ch : ℕ → List ℕ) (decA : List ℕ → F)
    (lvK : ℕ → ℕ → F) (Qs : ℕ → ℕ → Prop) :
    ∀ (c i : ℕ) (h : i + c = k) (ds : MDec (friMerkleMask s d l L Dg enc i c h))
      (os : OpenAll Dg (merkleSkels (friMerkleMask s d l L Dg enc i c h)))
      (p : (protocol (compiledRoundsK Dg Op (friMerkleMask s d l L Dg enc i c h))).tree.ExecutionPath)
      (q : (protocol (baseRounds Dg (friMerkleMask s d l L Dg enc i c h))).tree.ExecutionPath)
      (pfd : CompPoly.CPolynomial F) (xsd : Fin l → (ω.subdomain 0).toFinset),
      Agrees (friMerkleMask s d l L Dg enc i c h) os p q →
      SelF s d l L Dg enc Qs i c h os → ValF s d l L Dg enc lvK i c h os → CodOK s d l L Dg enc decA i c h ds →
      (∀ t, t < c + 1 → (encPathD (compiledRoundsK Dg Op (friMerkleMask s d l L Dg enc i c h))
        (mDecs dY' (friMerkleMask s d l L Dg enc i c h) ds ω0) p).getD t [] = ch (8 + i + t)) →
      pfd = finPolyOf s d l L Dg enc Op i c h p → xsd = XsOf s d l L Dg enc Op i c h p →
      StepRel (friAlt (ω := ω) s d l)
        (fun j m _ => QT s l (fun w : Fin (k + 1) => decA (ch (7 + w.val))) pfd xsd (SelT s L Qs) (WdT s L lvK) j m) i (c + 1)
        (by have := friAlt_r (ω := ω) s d l; omega)
        (toTail s d l L Dg enc i c h q) (toTail s d l L Dg enc i c h q)
  | 0, i, h, ds, os, p, q, pfd, xsd, hAg, hSel, hVal, hcod, hch, hpf, hxs => by
      obtain ⟨hm, hc, -⟩ := hAg
      have hk := friLength (k := k)
      refine ⟨QT_final _ _ (by simp only []; omega) fun h' => ?_, QT_query _ _ (by simp only []; omega) fun h' => ?_, trivial⟩
      · rw [hpf]; simp only [finPolyOf]; rw [hm]; rfl
      · rw [hxs]; simp only [XsOf]; rw [hc]; rfl
  | c + 1, i, h, (cc, ds), (o, os), p, q, pfd, xsd, hAg, hSel, hVal, hcod, hch, hpf, hxs => by
      obtain ⟨hc, hw, hrest⟩ := hAg
      obtain ⟨hs1, hs2⟩ := hSel
      obtain ⟨hv1, hv2⟩ := hVal
      obtain ⟨hc1, hc2⟩ := hcod
      have hk := friLength (k := k)
      refine ⟨QT_word _ _ ⟨i, by omega⟩ rfl fun h' y hy => ?_,
        QT_fold _ _ ⟨i + 1, by omega⟩ (by simp only []; omega) fun h' => ?_,
        tail_StepRel dY' ω0 ch decA lvK Qs c i.succ (by omega) ds os p.2.2 q.2.2 pfd xsd hrest hs2 hv2 hc2 ?_ hpf hxs⟩
      · exact (congrFun (msg_cast_eq s d l ⟨i, by omega⟩ _ h' q.1) y).trans
          (word_at s d l L Dg enc lvK ⟨i, by omega⟩ _ o q.1 hw hv1 y (hs1 _ hy))
      · have e0 : cc.encC p.2.1 = ch (8 + i) := hch 0 (by omega)
        have e1 : p.2.1 = cc.decC (ch (8 + i)) := by
          rw [← cc.decC_encC p.2.1]; exact congrArg cc.decC e0
        have e1' : (toTail s d l L Dg enc i (c + 1) h q).snd.fst = cc.decC (ch (8 + i)) := hc.symm.trans e1
        rw [e1']
        refine (hc1 (ch (8 + i))).trans ?_
        exact congrArg decA (congrArg ch (by simp only []; omega))
      · intro t ht
        exact (hch (t + 1) (by omega)).trans (congrArg ch (by omega))

end Tail

/-! ## 4. reading the projections off the legacy transcript -/

section Read
open NockvmE2E.FriPort NockvmE2E.Merkle.Fri NockvmE2E.Lift NockvmE2E.Exec.SF

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (l : ℕ)

/-- the committed word `f_{i+1}` of the audited history at a point is the legacy message `nonfinalMessage i` at that point -/
theorem committedWord_nf (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ) (i : Fin k)
    (y : wordDom (ω := ω) s i.val) :
    committedWord s (qO s l f tr) ⟨i.val + 1, by omega⟩ y =
      (cast (nonfinalMessage_type s l i) (tr.read (nonfinalMessage (ω := ω) s l i).val
        (by simp only [Fin.val_succ, queryChallenge_val, nonfinalMessage_val]; have := friLength (k := k); omega)) :
        wordDom (ω := ω) s i.val → F) y := by
  unfold qO
  rw [committedWord_queryHistory]
  unfold readWord
  simp only [Nat.add_one_ne_zero, ↓reduceDIte]
  erw [cast_fun_apply]
  rfl

/-- the four projections of the audited history/challenges/query vector, from the `QT` property of every entry of the legacy transcript -/
theorem proj_of_QT {αd : Fin (k + 1) → F} {pfd : CompPoly.CPolynomial F} {xsd : Fin l → (ω.subdomain 0).toFinset}
    {Sel : ∀ i : Fin k, wordDom (ω := ω) s i.val → Prop} {Wd : ∀ i : Fin k, wordDom (ω := ω) s i.val → F}
    (f : (ω.subdomain 0).toFinset → F) (T : (pSpec k (ω := ω) s l).Transcript (Fin.last _))
    (hq : ∀ (j : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) (h : j.val < (Fin.last _).val),
      QT s l αd pfd xsd Sel Wd j (T.read j h)) :
    let tr := Transcript.restrict (a := (queryChallenge (ω := ω) s l).val.succ) (b := Fin.last _)
      (by simp only [Fin.val_succ, Fin.val_last]; omega) T
    (∀ i, qA s l tr i = αd i) ∧ qX s l tr = xsd ∧ finalPolynomial s (qO s l f tr) = pfd ∧
      ∀ (i : Fin k) y, Sel i y → committedWord s (qO s l f tr) ⟨i.val + 1, by omega⟩ y = Wd i y := by
  intro tr
  have hk := friLength (k := k)
  refine ⟨fun i => ?_, ?_, ?_, fun i y hy => ?_⟩
  · exact (hq _ (by simp only [Fin.val_last, foldChallenge_val]; omega)).1 i rfl
  · exact (hq _ (by simp only [Fin.val_last, queryChallenge_val]; omega)).2.2.1 rfl
  · unfold qO
    rw [finalPolynomial_queryHistory]
    exact (hq _ (by simp only [Fin.val_last, finalMessage_val]; omega)).2.1 rfl
  · rw [committedWord_nf s l f tr i y]
    exact (hq _ (by simp only [Fin.val_last, nonfinalMessage_val]; omega)).2.2.2 i rfl y hy

end Read

/-! ## 5. the whole FRI mask: head round, then the tail -/

section Whole
open NockvmE2E.FriPort NockvmE2E.Merkle.Fri NockvmE2E.Lift NockvmE2E.Exec.Cover NockvmE2E.Exec.SL NockvmE2E.Exec.Layout NockvmE2E.Exec.SF

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (L : FriLeaves (ω := ω) s) (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : F ↪ Dg)
  (Op : Type) [Finite Op] [DecidableEq Op]

/-- **the FRI transcript projection** (the dependent-type core): along a base path `qm` of the FRI mask that agrees with the compiled
path `pm` and its openings `os`, EVERY entry of the legacy transcript `friTranscript (toFriPath qm)` has the `QT` property:
fold challenge `w` = `decA (ch (7 + w))`, the final message = `finPolyOf pm`, the query vector = `XsOf pm`, and word `f_{i+1}` at a point
of `Qs`-marked leaves = `lvK i (leaf)`.  Remaining inputs: the challenge encodings `hch` (`ch` = the verifier's `chalsOf`, by `fs_chal_dec`),
the codec facts `hcod0`/`hcod`, the digest link `hVal` (B6-1b's openings) and the selector link `hSel` (`hsel`). -/
theorem fri_QT (dY' : List ℕ → Dg) (ω0 : Op) (ch : ℕ → List ℕ) (decA : List ℕ → F) (lvK : ℕ → ℕ → F) (Qs : ℕ → ℕ → Prop)
    (dsm : MDec (friMask s d l L Dg enc))
    (os : OpenAll Dg (merkleSkels (friMask s d l L Dg enc)))
    (pm : (protocol (compiledRoundsK Dg Op (friMask s d l L Dg enc))).tree.ExecutionPath)
    (qm : (protocol (baseRounds Dg (friMask s d l L Dg enc))).tree.ExecutionPath)
    (hAg : Agrees (friMask s d l L Dg enc) os pm qm)
    (hSel : SelF s d l L Dg enc Qs 0 k (by omega) os) (hVal : ValF s d l L Dg enc lvK 0 k (by omega) os)
    (hcod0 : ∀ x, cast (foldChallenge_type (ω := ω) s l ⟨0, by omega⟩)
      (xp (a := ⟨0, by have := friLength (k := k); omega⟩) (b := (foldChallenge (ω := ω) s l ⟨0, by omega⟩).val)
        (Fin.ext (by simp only [foldChallenge_val])) (dsm.1.decC x)) = decA x)
    (hcod : CodOK s d l L Dg enc decA 0 k (by omega) dsm.2)
    (hch : ∀ t, t < k + 2 → (encPathD (compiledRoundsK Dg Op (friMask s d l L Dg enc))
      (mDecs dY' (friMask s d l L Dg enc) dsm ω0) pm).getD t [] = ch (7 + t)) :
    ∀ (j : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) (h : j.val < (Fin.last _).val),
      QT s l (fun w : Fin (k + 1) => decA (ch (7 + w.val)))
        (finPolyOf s d l L Dg enc Op 0 k (by omega) pm.2.2) (XsOf s d l L Dg enc Op 0 k (by omega) pm.2.2)
        (SelT s L Qs) (WdT s L lvK) j (Transcript.read (m := Fin.last _) (friTranscript s d l (toFriPath s d l L Dg enc qm)) j h) := by
  have hk := friLength (k := k)
  obtain ⟨hc0, hc1, hrest⟩ := hAg
  refine pathTranscript_rel (friAlt (ω := ω) s d l)
    (fun j m _ => QT s l (fun w : Fin (k + 1) => decA (ch (7 + w.val)))
        (finPolyOf s d l L Dg enc Op 0 k (by omega) pm.2.2) (XsOf s d l L Dg enc Op 0 k (by omega) pm.2.2)
        (SelT s L Qs) (WdT s L lvK) j m)
    (toFriPath s d l L Dg enc qm) (toFriPath s d l L Dg enc qm) ?_ ?_
  · refine QT_fold _ _ ⟨0, by omega⟩ rfl fun h' => ?_
    have e0 : dsm.1.encC pm.2.1 = ch 7 := hch 0 (by omega)
    have e1 : pm.2.1 = dsm.1.decC (ch 7) := by
      rw [← dsm.1.decC_encC pm.2.1]; exact congrArg dsm.1.decC e0
    have e1' : (toFriPath s d l L Dg enc qm).snd.fst = dsm.1.decC (ch 7) := hc1.symm.trans e1
    rw [e1']
    exact hcod0 (ch 7)
  · exact tail_StepRel s d l L Dg enc Op dY' ω0 ch decA lvK Qs k 0 (by omega) dsm.2 os pm.2.2 qm.2.2 _ _ hrest hSel hVal hcod
      (fun t ht => (hch (t + 1) (by omega)).trans (congrArg ch (by omega))) rfl rfl

end Whole

/-! ## 6. `FriLinkAt` from the transcript property -/

section LinkAt
open NockvmE2E.FriPort NockvmE2E.Merkle.Fri NockvmE2E.Lift NockvmE2E.Exec.SF NockvmE2E.Merkle.RapFriQ

variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)
variable [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]

omit [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)] in
theorem committedFunction_zero (f : (ω.subdomain 0).toFinset → KC)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ) (y : (ω.subdomain 0).toFinset) :
    committedFunction s (qO s l f tr) (Fin.castSucc 0) y.val = f y := by
  have hy' : y.val ∈ (ω.subdomain (foldingPrefix s (Fin.castSucc (0 : Fin (k + 1))))).toFinset := by
    have h0 : foldingPrefix s (Fin.castSucc (0 : Fin (k + 1))) = 0 := by simp [foldingPrefix, finRangeTo]
    rw [h0]; exact y.2
  have := committedFunction_castSucc s (qO s l f tr) 0 ⟨y.val, hy'⟩
  simp only at this
  rw [this]
  unfold qO
  rw [committedWord_queryHistory]
  unfold readWord
  simp only [Fin.val_zero, ↓reduceDIte]
  erw [cast_fun_apply]
  rfl

/-- **`FriLinkAt` from the `QT` property of the legacy transcript** (the data links `hx hα hP hdeg` are statements about the data `xsd αd pfd`;
`hW`/`hW0` say that every read index of word `w` is a point of the word's domain at which the data / the initial oracle has the flat value) -/
theorem friLinkAt_of_QT {Salt : Type} (zS : FriStmt (ω := ω) s × Salt)
    (path : (protocol (friRounds (ω := ω) s d l)).tree.ExecutionPath)
    (αd : Fin (k + 1) → KC) (pfd : CompPoly.CPolynomial KC) (xsd : Fin l → (ω.subdomain 0).toFinset)
    (Sel : ∀ i : Fin k, wordDom (ω := ω) s i.val → Prop) (Wd : ∀ i : Fin k, wordDom (ω := ω) s i.val → KC)
    (hq : ∀ (j : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)) (h : j.val < (Fin.last _).val),
      QT s l αd pfd xsd Sel Wd j (Transcript.read (m := Fin.last _) (friTranscript s d l path) j h))
    (c γ : KC) (pos : Fin l → ℕ) (W : ℕ → ℕ → KC) (Pf : KC → KC) (αN : ℕ → KC)
    (hγ : γ ^ 2 ^ (n - 1) = -1)
    (hx : ∀ j, (xsd j).val = c * γ ^ pos j) (hα : ∀ i : Fin (k + 1), αd i = αN i.val)
    (hP : ∀ y, pfd.eval y = Pf y) (hdeg : pfd.natDegree < d.val)
    (hW : ∀ j (i : Fin k) g, Rd n (pos j) (i.val + 1) g →
      ∃ y : wordDom (ω := ω) s i.val, y.val = Yp c γ (i.val + 1) g ∧ Sel i y ∧ Wd i y = W (i.val + 1) g)
    (hW0 : ∀ j g, Rd n (pos j) 0 g →
      ∃ y : (ω.subdomain 0).toFinset, y.val = Yp c γ 0 g ∧ initialOracle s zS.1 y = W 0 g) :
    FriLinkAt s d l zS path c γ pos W Pf αN := by
  have hk := friLength (k := k)
  obtain ⟨f1, f2, f3, f4⟩ := proj_of_QT s l (initialOracle s zS.1) (friTranscript s d l path) hq
  refine ⟨⟨hγ, fun j => ?_, fun i => ?_, ?_, fun y => ?_⟩, ?_⟩
  · rw [f2]; exact hx j
  · rw [f1 i]; exact hα i
  · intro j w hw g hg
    rcases Nat.eq_zero_or_pos w.val with h0 | hpos
    · have hw0 : w = Fin.castSucc (0 : Fin (k + 1)) := Fin.ext h0
      subst hw0
      obtain ⟨y, hy, hyW⟩ := hW0 j g hg
      have e : (Fin.castSucc (0 : Fin (k + 1))).val = 0 := rfl
      simp only [e]
      rw [← hy, committedFunction_zero]
      exact hyW
    · obtain ⟨wv, hwv⟩ := w
      obtain ⟨iv, rfl⟩ : ∃ iv, wv = iv + 1 := ⟨wv - 1, by simp at hpos; omega⟩
      simp only at hw hg
      obtain ⟨y, hy, hsel, hWd⟩ := hW j ⟨iv, by omega⟩ g hg
      simp only at hy ⊢
      rw [← hy]
      have := committedFunction_castSucc s (qO s l (initialOracle s zS.1) (Transcript.restrict (b := Fin.last _) (by simp only [Fin.val_succ, Fin.val_last]; omega) (friTranscript s d l path))) ⟨iv + 1, by omega⟩ y
      exact this.trans ((f4 ⟨iv, by omega⟩ y hsel).trans hWd)
  · rw [f3]; exact hP y
  · rw [f3]; exact hdeg

end LinkAt

/-! ## 7. the instance: FRI words `w ≥ 1` (`hW`) -/

section Inst
open NockvmE2E.FriPort NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx

/-- the flat value (in `KC`) of leaf `t` of FRI tree `4 + i` -/
noncomputable def lvK (XI : ExecInst) (π : FlatProof) (i t : ℕ) : KC :=
  homV.φ (friAtV π.vals (4 + i) (lb (selsOf XI π)[4 + i]! t))

theorem pt_val (n : ℕ) (hn : n ≤ 32) (m m' : ℕ) (hmn : m < n) (hm : m = m') (u : Fin (2 ^ (n - m))) :
    (((smoothDomain n hn).subdomain m).equivToFinset u).val =
      Yp (algebraMap (ZMod NockvmE2E.Exec.p) KC 7) ((zeta n : KCˣ) : KC) m' u.val := by
  subst hm
  rw [CosetFftDomain.equivToFinset_apply]
  show (smoothDomain n hn).subdomain m u = _
  rw [sub_apply n hn m hmn, Yp, ← pow_mul]

theorem hW_inst (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hok : FlatOk XI H FS zF π)
    (hn32 : XI.nD ≤ 32) (j : Fin XI.l) (i : Fin XI.k) (g : ℕ) (hg : Rd XI.nD (π.pos[j.1]!) (i.val + 1) g) :
    ∃ y : wordDom (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) i.val,
      y.val = Yp (psiV XI.dShift) (psiV XI.dGen) (i.val + 1) g ∧
      QF XI π i.val (leafNum (((LX XI hn32).idx i).symm y)) ∧
      lvK XI π i.val (leafNum (((LX XI hn32).idx i).symm y)) =
        homV.φ (Wf XI (word0Of XI FS zF π) (faV π.vals (selsOf XI π)) (fbV π.vals (selsOf XI π)) (i.val + 1) g) := by
  obtain ⟨hk1, hsz⟩ := flat_shape XI H FS zF π hok
  have hshift : XI.dShift = 7 := (flatOk_params XI H FS zF π hok).1
  have hgen := flatOk_dGen XI H FS zF π hok
  have hm := msum1 XI.k i.val i.2
  have hi2 : i.val + 2 ≤ XI.nD := by omega
  obtain ⟨hg1, hg2⟩ := hg
  let u : Fin (2 ^ (XI.nD - ∑ j ∈ finRangeTo (XI.k + 1) (i.val + 1), (((fun _ : Fin (XI.k + 1) => (1 : ℕ+)) j : ℕ+) : ℕ))) :=
    ⟨g, by rw [hm]; exact hg1⟩
  refine ⟨((smoothDomain XI.nD hn32).subdomain _).equivToFinset u, ?_, ?_⟩
  · show _ = Yp (psiV XI.dShift) (psiV XI.dGen) _ _
    rw [psiV_shift XI hshift, hgen]
    exact pt_val XI.nD hn32 _ _ (by omega) hm u
  · have hleaf := LX_leafNum XI hn32 i.val i.2 hi2 (((smoothDomain XI.nD hn32).subdomain _).equivToFinset u)
    have hu := congrArg Fin.val (Equiv.symm_apply_apply (((smoothDomain XI.nD hn32).subdomain _).equivToFinset) u)
    have hB : (((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i.val + 1), (1 : ℕ))).equivToFinset.symm
      (((smoothDomain XI.nD hn32).subdomain _).equivToFinset u)).val = g := hu
    have hC : (((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i.val + 1), ((1 : ℕ+) : ℕ))).equivToFinset.symm
      (((smoothDomain XI.nD hn32).subdomain _).equivToFinset u)).val = g := hu
    have hleaf2 : leafNum (((LX XI hn32).idx i).symm (((smoothDomain XI.nD hn32).subdomain _).equivToFinset u)) =
        2 * (g % 2 ^ (XI.nD - i.val - 2)) + g / 2 ^ (XI.nD - i.val - 2) :=
      hleaf.trans (congrArg₂ (fun a b : ℕ => 2 * (a % 2 ^ (XI.nD - i.val - 2)) + b / 2 ^ (XI.nD - i.val - 2)) hB hC)
    clear hleaf hu hB hC
    have hpos : 0 < 2 ^ (XI.nD - i.val - 2) := Nat.two_pow_pos _
    have hdiv : g / 2 ^ (XI.nD - i.val - 2) < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [← pow_succ, show XI.nD - i.val - 2 + 1 = XI.nD - (i.val + 1) by omega]
      exact hg1
    have hg2' : g % 2 ^ (XI.nD - i.val - 2) = π.pos[j.1]! % 2 ^ (XI.nD - i.val - 2) := by
      rw [show XI.nD - i.val - 2 = XI.nD - (i.val + 1) - 1 by omega]; exact hg2
    have hmem : π.pos[j.1]! ∈ π.pos.toList := by
      have : j.1 < π.pos.size := by rw [hsz]; exact j.2
      rw [getElem!_pos π.pos j.1 this]; simp
    refine ⟨?_, ?_⟩
    · show _ ∈ (selsOf XI π)[4 + i.val]!.toList
      rw [hleaf2, selsF XI π i.val i.2]
      have := mem_treeSel_fri XI (4 + i.val) π.pos (by omega) (π.pos[j.1]!) hmem _ hdiv
      rw [show XI.nD - (4 + i.val - 3) - 1 = XI.nD - i.val - 2 by omega, ← hg2'] at this
      exact this
    · unfold lvK
      rw [hleaf2]
      unfold Wf
      simp only [Nat.add_one_ne_zero, ite_false]
      have h34 : 3 + (i.val + 1) = 4 + i.val := by omega
      by_cases hlt : g < 2 ^ (XI.nD - i.val - 2)
      · rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, show XI.nD - (i.val + 1) - 1 = XI.nD - i.val - 2 by omega, ]
        simp only [hlt, ite_true, faV, h34, Nat.add_zero]
      · have hd1 : g / 2 ^ (XI.nD - i.val - 2) = 1 := Nat.div_eq_of_lt_le (by omega) (by
          have e2 : 2 ^ (XI.nD - (i.val + 1)) = 2 * 2 ^ (XI.nD - i.val - 2) := by
            rw [← pow_succ']; congr 1; omega
          omega)
        have hm1 : g % 2 ^ (XI.nD - i.val - 2) = g - 2 ^ (XI.nD - i.val - 2) := by
          have := Nat.mod_add_div g (2 ^ (XI.nD - i.val - 2)); rw [hd1] at this; omega
        rw [hd1, hm1, show XI.nD - (i.val + 1) - 1 = XI.nD - i.val - 2 by omega, ]
        simp only [hlt, ite_false, fbV, h34]

end Inst

/-! ## 8. the combined mask: split along `RM ++ BM` and the closed `hF` -/

section Split
open NockvmE2E.Merkle.MA NockvmE2E.Exec.SL
variable {Dg : Type} [Finite Dg] [DecidableEq Dg] {Op : Type} [Finite Op] [DecidableEq Op]

/-- `q0Of` commutes with the split of a compiled path along an append -/
theorem sndB_q0Of : (a b : MRounds Dg) → (os : OpenAll Dg (merkleSkels (a ++ b))) →
    (p : (protocol (compiledRoundsK Dg Op (a ++ b))).tree.ExecutionPath) →
    sndB Dg a b (q0Of (a ++ b) os p) = q0Of b (sndOpen a b os) (sndK Dg Op a b p)
  | [], _, _, _ => rfl
  | ⟨_, .clear⟩ :: a, b, os, p => sndB_q0Of a b os p.2.2
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (o, os), p => sndB_q0Of a b os p.2.2

end Split

/-! ## 10. FRI word 0: the initial oracle is the verifier's batched input word -/

section Word0
open NockvmE2E.FriPort NockvmE2E.FriPort.Batched NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Rap NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriDeep
  BatchedFri.Spec BatchedFri.Spec.BatchingRound

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+)
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ n) → B) colRound) {r : ℕ} (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ n) → B) colRound) {m : ℕ} (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)

/-- the initial oracle of `combinedStmt` at a domain point is the verifier's batched word `φ (deepWordS …)` (`SF.input_word_eq`, with the
generator link `hG` and the read-index facts `hops`/canonicity named) -/
theorem initialOracle_combined {S : Type} (G : CoreDefinitions.Generator S (Fin (m + 1)) KC) (csS : S) (cs : KC)
    (hG : ∀ i : Fin (m + 1), G csS i = cs ^ (i : ℕ))
    (XI : ExecInst) (pts : Array VF.K3) (ops : List (ℕ × ℕ × VF.K3 × VF.K3)) (baseAt : ℕ → ℕ → VF.G)
    (tr : DeepTr P) (fin : DeepFin P (r := r) R0) (χ : Coins Φ KC) (idx : Fin (2 ^ n))
    (y : (ω.subdomain 0).toFinset) (hy : y.val = ω idx)
    (hω : ω idx = homV.ψ XI.dShift * homV.ψ XI.dGen ^ (idx : ℕ))
    (hops : List.Forall₂ (fun (o : ℕ × ℕ × VF.K3 × VF.K3) (j : Fin (m + 1)) =>
      o.2.1 < XI.r + 2 ∧ homV.φ o.2.2.1 = cs ^ (j : ℕ) ∧ homV.φ pts[o.2.1]! = ptOf P A e χ j ∧
      homV.φ o.2.2.2 = valOf P R0 e fin j ∧ homV.ψ (baseAt o.1 idx) = liftW (tr (colOf P e j)) idx)
      ops (List.finRange (m + 1)))
    (hops_can : ∀ o ∈ ops, homV.C o.2.2.1 ∧ homV.C o.2.2.2 ∧ homV.Cg (baseAt o.1 idx))
    (hpts_can : ∀ p, p < XI.r + 2 → homV.C pts[p]!) :
    initialOracle s (combinedStmt s m G csS (deepStmt (ω := ω) P A R0 e tr fin χ)) y
      = homV.φ (deepWordS XI pts ops baseAt idx) := by
  have hy' : y.val ∈ (ω.subdomain (∑ j' ∈ finRangeTo (k + 1) (0 : Fin 1).1, (s j').1)).toFinset := by
    have h0 : (∑ j' ∈ finRangeTo (k + 1) (0 : Fin 1).1, (s j').1) = 0 := by simp [finRangeTo]
    rw [h0]; exact y.2
  have hv : initialDomainPoint (s := s) (0 : Fin 1) ⟨y.val, hy'⟩ = ω.equivToFinset idx := by
    apply Subtype.ext
    show y.val = ω idx
    exact hy
  have key := input_word_eq P A R0 e s homV XI pts ops baseAt tr fin χ cs idx ⟨y.val, hy'⟩ hv hω hops hops_can hpts_can
  rw [key]
  unfold initialOracle combinedStmt
  erw [cast_fun_apply (e := (by simp [finRangeTo] : (∑ j' ∈ finRangeTo (k + 1) (0 : Fin 1).1, (s j').1) = 0))]
  unfold combinedOracle
  dsimp only
  congr 1
  apply List.map_congr_left
  intro i _
  rw [hG]

end Word0

section Append
open NockvmE2E.Merkle.MA
variable {Dg : Type} [Finite Dg] [DecidableEq Dg] {Op : Type} [Finite Op] [DecidableEq Op] (dY' : List ℕ → Dg) (ω0 : Op)

/-- the challenge encodings of the suffix mask are those of the whole path, shifted by the prefix length (turns `fs_chal_dec` for the
whole combined path into the `hch` of `fri_QT`) -/
theorem encPathD_append_getD : (a b : MRounds Dg) → (da : MDec a) → (db : MDec b) →
    (p : (protocol (compiledRoundsK Dg Op (a ++ b))).tree.ExecutionPath) → (t : ℕ) →
    (encPathD (compiledRoundsK Dg Op (a ++ b)) (mDecs dY' (a ++ b) (mdAppend a b da db) ω0) p).getD (a.length + t) [] =
      (encPathD (compiledRoundsK Dg Op b) (mDecs dY' b db ω0) (sndK Dg Op a b p)).getD t []
  | [], b, da, db, p, t => by simp [mdAppend, sndK]
  | ⟨_, .clear⟩ :: a, b, (d, da), db, p, t => by
      rw [List.length_cons, show a.length + 1 + t = (a.length + t) + 1 by omega]
      exact encPathD_append_getD a b da db p.2.2 t
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (c, da), db, p, t => by
      rw [List.length_cons, show a.length + 1 + t = (a.length + t) + 1 by omega]
      exact encPathD_append_getD a b da db p.2.2 t

end Append

/-! ## 9. `FriLinkAt` of the closed J-8 context -/

section Closed

open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri

variable (XI : ExecInst) (H : HFn) (FS : FSFn) (zF : List Nat) (π : FlatProof) (hv : verifyFlat XI H FS zF π = true)

set_option hygiene false in
local notation "ωS" => smoothDomain XI.nD (nD_le_of_verify XI H FS zF π hv)
set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra B KC] [Inhabited B]
variable [SampleableType KC] [Inhabited KC]
variable {Φ : CoinFrame} {ι : Type} [Fintype ι] [DecidableEq ι] {colRound : ι → ℕ}
  (P : DeepParams Φ KC ι (Fin (2 ^ XI.nD) → B) colRound) {r : ℕ} [NeZero r] (A : AirShape P r)
  (R0 : RapStatement Φ KC ι (Fin (2 ^ XI.nD) → B) colRound)
  (Rest : R0.M0 → DeepTr P → R0.Mfin → Coins Φ KC → Prop)
  (RestV : R0.M0 → DeepFin P (r := r) R0 → Coins Φ KC → Prop) {m : ℕ}
  (e : Fin (m + 1) ≃ (ι × Fin r) ⊕ Fin P.nq)
variable [DecidableEq (P.statement R0 Rest).M0] [Finite (P.statement R0 Rest).M0]
  [DecidableEq (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin] [Finite (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin]
  (I0 : OracleInterface (P.statement R0 Rest).M0)
  (I : (r : ℕ) → OracleInterface (Cols P.colRoundX (Fin (2 ^ XI.nD) → B) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin) (nb : ℕ)
variable (d : ℕ+)
variable [∀ j, SampleableType ((pSpec XI.k (ω := ωS) s1 XI.l).Challenge j)]
variable {S : Type} [Fintype S] [Nonempty S] [SampleableType S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) KC)
variable (Dg : Type) [Finite Dg] [DecidableEq Dg] (enc : KC ↪ Dg)
  (md : PointMaskData P.colRoundX (Fin (2 ^ XI.nD)) B Dg) (L : Fri.FriLeaves (ω := ωS) s1)
variable (Op : Type) [Finite Op] [DecidableEq Op]

set_option hygiene false in
local notation "MC" => msC P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (S := S)
set_option hygiene false in
local notation "RM" => RapP.rapMask Φ KC md.toRapMaskData (P.statement R0 Rest).M0
  (friPlan (ω := ωS) P A R0 Rest RestV e).Mfin I0 I Ifin nb
set_option hygiene false in
local notation "BM" => bmask (S := S) s1 d XI.l Dg enc L

/-- the challenges of the verifier as a function of the round index -/
noncomputable def chV : ℕ → List ℕ := fun i => (chalsOf XI FS zF π)[i]!

/-- the `w = 0` read link: every read index of word 0 is a point of the initial domain at which the audited initial oracle (the batched
`combinedStmt` word) is the verifier's `word0Of` -/
def W0Link (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath) : Prop :=
  ∀ (j : Fin XI.l) g, Rd XI.nD (π.pos[j.1]!) 0 g →
    ∃ y : ((ωS).subdomain 0).toFinset, y.val = Yp (homV.ψ XI.dShift) (homV.ψ XI.dGen) 0 g ∧
      initialOracle s1 ((combinedStmt s1 m G (MA.sndB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.1
        (deepStmt (ω := ωS) P A R0 e
          (trQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
          (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
          (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)))), z.2).1 y =
        homV.φ (Wf XI (word0Of XI FS zF π) (faV π.vals (selsOf XI π)) (fbV π.vals (selsOf XI π)) 0 g)

/-- **`hF` of `ClosedLinksL`** (the FRI link `FriLinkAt`) from the verifier's acceptance.  Everything is derived (the transcript projections, `hγ`,
`hx` from `hxs`, `hα`, `hP`, `hdeg`, `hCF` for `w ≥ 1` through `LX_leafNum`) except the NAMED inputs:
* `hxs`, `hselF` (= `ClosedLinksL.hxs`, `.hsel.2`); `hvalF` (opened digest = `enc` of the flat leaf value; B6-1b `openAllOf`);
* `hch` (the encoded challenges of the FRI rounds of `p` are the verifier's `chalsOf`: `fs_chal_dec`), `hcod0`/`hcod` (the FRI challenge codecs read
  the limbs as `toKV ∘ K3.ofLimbs`);
* `hPdec` (the final-message decoder is Horner of `pfinal`); `hW0` (the `w = 0` read: the initial oracle at a read index is `word0Of`; from
  `SF.input_word_eq`, see `hW0_of_ops`). -/
theorem friLinkAt_of_flat (hok : FlatOk XI H FS zF π)
    (hL : L = LX XI (nD_le_of_verify XI H FS zF π hv))
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (hxs : ∀ j, (xsC P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op p j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ π.pos[j.1]!)
    (hselF : SelF s1 d XI.l L Dg enc (QF XI π) 0 XI.k (by omega) (MA.sndOpen (RM) (BM) (decode (pathRootsK Dg Op (MC) p).2)))
    (hvalF : ValF s1 d XI.l L Dg enc (lvK XI π) 0 XI.k (by omega) (MA.sndOpen (RM) (BM) (decode (pathRootsK Dg Op (MC) p).2)))
    (dY' : List ℕ → Dg) (ω0 : Op) (dsm : MDec (friMask s1 d XI.l L Dg enc))
    (hch : ∀ t, t < XI.k + 2 → (encPathD (compiledRoundsK Dg Op (friMask s1 d XI.l L Dg enc))
      (mDecs dY' (friMask s1 d XI.l L Dg enc) dsm ω0) (MA.sndK Dg Op (RM) (BM) p).2.2).getD t [] = chV XI FS zF π (7 + t))
    (hcod0 : ∀ x, cast (foldChallenge_type (ω := ωS) s1 XI.l ⟨0, by omega⟩)
      (xp (a := ⟨0, by have := friLength (k := XI.k); omega⟩) (b := (foldChallenge (ω := ωS) s1 XI.l ⟨0, by omega⟩).val)
        (Fin.ext (by simp only [foldChallenge_val])) (dsm.1.decC x)) = toKV (VF.K3.ofLimbs x))
    (hcod : CodOK s1 d XI.l L Dg enc (fun x => toKV (VF.K3.ofLimbs x)) 0 XI.k (by omega) dsm.2)
    (hPdec : ∀ y, (finPolyOf s1 d XI.l L Dg enc Op 0 XI.k (by omega) (MA.sndK Dg Op (RM) (BM) p).2.2.2.2).eval y =
      hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size y)
    (hW0 : W0Link XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d G Dg enc md L Op decode z p) :
    FriLinkAt s1 d XI.l
      ((combinedStmt s1 m G (MA.sndB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.1
        (deepStmt (ω := ωS) P A R0 e
          (trQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
          (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))
          (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p))), z.2))
      (Fri.toFriPath s1 d XI.l L Dg enc (MA.sndB Dg (RM) (BM) (q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p)).2.2)
      (homV.ψ XI.dShift) (homV.ψ XI.dGen) (fun j => π.pos[j.1]!)
      (fun w i => homV.φ (SF.Wf XI (word0Of XI FS zF π) (faV π.vals (selsOf XI π)) (fbV π.vals (selsOf XI π)) w i))
      (SF.hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size) (fun i => homV.φ (alphasOf XI FS zF π)[i]!) := by
  have hn32 := nD_le_of_verify XI H FS zF π hv
  obtain ⟨hk1, hsz⟩ := flat_shape XI H FS zF π hok
  unfold W0Link at hW0
  unfold q0P at hW0 ⊢
  rw [sndB_q0Of] at hW0 ⊢
  have hQT := fri_QT s1 d XI.l L Dg enc Op dY' ω0 (chV XI FS zF π) (fun x => toKV (VF.K3.ofLimbs x)) (lvK XI π) (QF XI π) dsm
    (MA.sndOpen (RM) (BM) (decode (pathRootsK Dg Op (MC) p).2)) (MA.sndK Dg Op (RM) (BM) p).2.2
    (q0Of (friMask s1 d XI.l L Dg enc) (MA.sndOpen (RM) (BM) (decode (pathRootsK Dg Op (MC) p).2)) (MA.sndK Dg Op (RM) (BM) p).2.2)
    (agree_q0 (BM) (MA.sndOpen (RM) (BM) (decode (pathRootsK Dg Op (MC) p).2)) (MA.sndK Dg Op (RM) (BM) p)).2.2
    hselF hvalF hcod0 hcod hch
  refine friLinkAt_of_QT s1 d XI.l _ _ _ _ _ _ _ hQT _ _ _ _ _ _ (hγ_of_flat XI H FS zF π hok hn32 (by omega)) hxs ?_ hPdec
    (finPoly_deg s1 d XI.l L Dg enc Op XI.k 0 (by omega) _) ?_ hW0
  · intro i
    show toKV (VF.K3.ofLimbs (chV XI FS zF π (7 + i.val))) = toKV (alphasOf XI FS zF π)[i.val]!
    unfold alphasOf chV
    rw [getElem!_pos _ i.1 (by simp; omega)]
    simp
  · intro j i g hg
    subst hL
    exact hW_inst XI H FS zF π hok hn32 j i g hg

set_option hygiene false in
local notation "Q0" => q0P P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L Op decode p

/-- **`W0Link` from the batched-opening list** (`SF.input_word_eq`): for every read index `g` of word 0, the opening list is the `e`-enumeration
(`hopsU`: coefficients `cs^j`, points, claimed values and RAP base values at `g`), with the generator link `hG` and canonicity (`hcanO`, `hcanP`,
read off `allCanon`; not derived here). `hopsU`'s base-value clause is where `mdX_leafNum` + `hrkV` (/) enter. -/
theorem w0link_of_ops (hok : FlatOk XI H FS zF π)
    (decode : Op → OpenAll Dg (merkleSkels (MC))) {Input Salt : Type} (z : Input × Salt)
    (p : (protocol (compiledRoundsK Dg Op (MC))).tree.ExecutionPath)
    (hG : ∀ i : Fin (m + 1), G (MA.sndB Dg (RM) (BM) (Q0)).2.1 i = toKV (csOf XI FS zF π) ^ (i : ℕ))
    (hopsU : ∀ (g : ℕ) (hg : g < 2 ^ XI.nD), List.Forall₂ (fun (o : ℕ × ℕ × VF.K3 × VF.K3) (j : Fin (m + 1)) =>
      o.2.1 < XI.r + 2 ∧ homV.φ o.2.2.1 = toKV (csOf XI FS zF π) ^ (j : ℕ) ∧
        homV.φ (openPts XI (zetaOf XI FS zF π))[o.2.1]! = ptOf P A e (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)) j ∧
        homV.φ o.2.2.2 = valOf P R0 e (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)) j ∧
        homV.ψ (baseAtOf XI π o.1 g) = liftW ((trQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)) (colOf P e j)) ⟨g, hg⟩)
      (openingList XI (csOf XI FS zF π) π.vT π.vQ).toList (List.finRange (m + 1)))
    (hcanO : ∀ g, ∀ o ∈ (openingList XI (csOf XI FS zF π) π.vT π.vQ).toList,
      homV.C o.2.2.1 ∧ homV.C o.2.2.2 ∧ homV.Cg (baseAtOf XI π o.1 g))
    (hcanP : ∀ q, q < XI.r + 2 → homV.C (openPts XI (zetaOf XI FS zF π))[q]!) :
    W0Link XI H FS zF π hv P A R0 Rest RestV e I0 I Ifin nb d G Dg enc md L Op decode z p := by
  intro j g hg
  have hn32 := nD_le_of_verify XI H FS zF π hv
  have hshift : XI.dShift = 7 := (flatOk_params XI H FS zF π hok).1
  have hgen := flatOk_dGen XI H FS zF π hok
  have hg1 : g < 2 ^ XI.nD := by simpa using hg.1
  have hnD : 0 < XI.nD := by have := (flat_shape XI H FS zF π hok).1; omega
  let u : Fin (2 ^ (XI.nD - 0)) := ⟨g, by simpa using hg1⟩
  have hy : ((((ωS).subdomain 0).equivToFinset u).val) = Yp (homV.ψ XI.dShift) (homV.ψ XI.dGen) 0 g := by
    show _ = Yp (psiV XI.dShift) (psiV XI.dGen) 0 g
    rw [psiV_shift XI hshift, hgen]
    exact pt_val XI.nD hn32 0 0 hnD rfl u
  have hω : ωS ⟨g, hg1⟩ = homV.ψ XI.dShift * homV.ψ XI.dGen ^ g := by
    show _ = psiV XI.dShift * psiV XI.dGen ^ g
    rw [psiV_shift XI hshift, hgen, Inst.smoothDomain_apply]
  have hy2 : ((((ωS).subdomain 0).equivToFinset u).val) = ωS ⟨g, hg1⟩ := by
    rw [hy, hω]; simp [Yp]
  refine ⟨((ωS).subdomain 0).equivToFinset u, hy, ?_⟩
  have := initialOracle_combined s1 P A R0 e G (MA.sndB Dg (RM) (BM) (Q0)).2.1 (toKV (csOf XI FS zF π)) hG XI
    (openPts XI (zetaOf XI FS zF π)) (openingList XI (csOf XI FS zF π) π.vT π.vQ).toList (baseAtOf XI π)
    (trQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0))
    (finMQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0))
    (chiQ P A R0 Rest RestV e I0 I Ifin nb s1 d XI.l Dg enc md L (Q0)) ⟨g, hg1⟩ _ hy2 hω (hopsU g hg1) (hcanO g) hcanP
  refine this.trans ?_
  unfold Wf word0Of
  simp only [ite_true]
  rw [deepWord_eq]

end Closed


#print axioms hγ_of_flat
#print axioms fri_QT
#print axioms friLinkAt_of_QT
#print axioms hW_inst
#print axioms initialOracle_combined
#print axioms friLinkAt_of_flat
#print axioms w0link_of_ops
#print axioms encPathD_append_getD
#print axioms sndB_q0Of

end NockvmE2E.Exec.E2EFri
