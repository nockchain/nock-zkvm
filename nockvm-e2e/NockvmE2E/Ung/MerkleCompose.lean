/-
composing the standalone Merkle negative theorem with the
commitment slot `UniqueCommitment` of `Succ/Commitment.lean` (the slot `rap_succinct_unique` takes as hypothesis).

MODEL. A "word commitment" is any `CommitScheme β O` whose commitments are collision-free roots `rt w` of a word
`w : ℕ → α` (window `i < 2^n`) and whose extractor DECODES the committed word (`ext (rt w) = dec w`), with `commit b`
the root of the codeword `enc b`; `dec` corrects a single-symbol error (`dec (enc b with one position changed) = b`:
unique decoding radius ≥ 1 symbol, as for Reed–Solomon with δ < 1/2). The openings/`verify`/`prove` fields are
IRRELEVANT to the theorems below (they only use `commit`, `ext`, `ext_commit`).
`merkleCS` is a concrete instance over the Merkle tree of `MerkleNegative.lean` (abstract hash with `Inj`), so
the hypotheses are satisfiable (`toy_*` at the end: repetition code over `Bool`, free hash).

RESULTS.
* `no_unique_of_wordCommit`: for every `UniqueCommitment` instance on such a scheme, `Collide` holds on EVERY pair
  (honest root of `b`, root of `b`'s codeword with one position changed). In particular `Collide` is never empty:
  `unique_com` cannot hold with `Collide = False`; `εuniq` cannot be small unless the experiment avoids all such pairs.
* `merkle_compose`: together with `merkle_ungrind_negative` (flipped word accepted on its own FS query set with
  probability ≥ 1 − l/2^n, under a different root): each such Collide pair is realised by an ACCEPTED proof with
  probability ≥ 1 − l/2^n. This is the standalone-model statement of "ε_uniq ≥ 1 − l/N".
NOT proved here (see UNG-B-REPORT): `¬ Ungrindable guards ε` over `sRounds`/`twoAcceptExecution` — it needs a concrete
`TwoProofAdversary` and the OracleComp probability of its FS query set, and no bridge between `prob` (the counting
measure of `MerkleNegative`) and `Pr{… ← randomOracleLoggedRun …}` exists.
-/
import NockvmE2E.Ung.Defs
import NockvmE2E.Ung.MerkleNegative

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NockvmE2E.Ung

open NockvmE2E.Succ

section Abstract

variable {α β : Type} {O : OracleInterface β} (CS : CommitScheme β O)

/-- **Every `UniqueCommitment` on a word commitment declares the one-flip pairs `Collide`.** -/
theorem no_unique_of_wordCommit [UC : UniqueCommitment β O (CS := CS)]
    {n : ℕ} (enc : β → ℕ → α) (dec : (ℕ → α) → β) (rt : (ℕ → α) → CS.Com)
    (hcommit : ∀ b, CS.commit b = rt (enc b))
    (hrt : ∀ w w', rt w = rt w' → ∀ i, i < 2 ^ n → w i = w' i)
    (hext : ∀ w, CS.ext (rt w) = dec w)
    (hdec : ∀ b j a, dec (Function.update (enc b) j a) = b)
    (b : β) {j : ℕ} (hj : j < 2 ^ n) {a : α} (ha : a ≠ enc b j) :
    rt (Function.update (enc b) j a) ≠ CS.commit b ∧
      UC.Collide (CS.commit b) (rt (Function.update (enc b) j a)) := by
  have hne : rt (Function.update (enc b) j a) ≠ CS.commit b := by
    intro e
    have := hrt _ _ (e.trans (hcommit b)) j hj
    simp at this
    exact ha this
  refine ⟨hne, ?_⟩
  have hx : CS.ext (CS.commit b) = CS.ext (rt (Function.update (enc b) j a)) := by
    rw [CS.ext_commit, hext, hdec]
  rcases UC.unique_com _ _ hx with h | h
  · exact absurd h.symm hne
  · exact h

/-- `Collide` can never be empty on a word commitment with a non-degenerate flip. -/
theorem collide_nonempty_of_wordCommit [UC : UniqueCommitment β O (CS := CS)]
    {n : ℕ} (enc : β → ℕ → α) (dec : (ℕ → α) → β) (rt : (ℕ → α) → CS.Com)
    (hcommit : ∀ b, CS.commit b = rt (enc b))
    (hrt : ∀ w w', rt w = rt w' → ∀ i, i < 2 ^ n → w i = w' i)
    (hext : ∀ w, CS.ext (rt w) = dec w)
    (hdec : ∀ b j a, dec (Function.update (enc b) j a) = b)
    (b : β) {j : ℕ} (hj : j < 2 ^ n) {a : α} (ha : a ≠ enc b j) :
    ∃ c c', UC.Collide c c' :=
  ⟨_, _, (no_unique_of_wordCommit CS enc dec rt hcommit hrt hext hdec b hj ha).2⟩

end Abstract

/-! ### A concrete Merkle word commitment -/

section Concrete

variable {α Y β : Type} {O : OracleInterface β} [Nonempty α]

open Classical in
/-- A word with the given root, if any (else an arbitrary word). -/
noncomputable def wordOf (L : α → Y) (H : Y → Y → Y) (n : ℕ) (c : Y) : ℕ → α :=
  if h : ∃ w : ℕ → α, root L H n w 0 = c then h.choose else fun _ => Classical.arbitrary α

theorem wordOf_root {L : α → Y} {H : Y → Y → Y} (hI : Inj L H) (n : ℕ) (w : ℕ → α) :
    ∀ i, i < 2 ^ n → wordOf L H n (root L H n w 0) i = w i := by
  classical
  intro i hi
  have h : ∃ w' : ℕ → α, root L H n w' 0 = root L H n w 0 := ⟨w, rfl⟩
  have := root_inj hI n _ _ 0 h.choose_spec i hi
  simpa [wordOf, h] using this

/-- The data of a Merkle word commitment: hash with `Inj`, depth, a code (`enc`) with a decoder `dec` that depends
only on the window and corrects one changed position. -/
structure MerkleData (α Y β : Type) where
  L : α → Y
  H : Y → Y → Y
  n : ℕ
  hI : Inj L H
  enc : β → ℕ → α
  dec : (ℕ → α) → β
  dec_enc : ∀ b, dec (enc b) = b
  dec_win : ∀ w w', (∀ i, i < 2 ^ n → w i = w' i) → dec w = dec w'
  dec_flip : ∀ b j a, dec (Function.update (enc b) j a) = b

/-- The Merkle commitment scheme: `Com` = root, `commit b` = root of `enc b`, `ext` = decode the (unique) word under
the root. The opening fields are the trivial ones (irrelevant for uniqueness). -/
@[instance_reducible] noncomputable def merkleCS (D : MerkleData α Y β) (O : OracleInterface β) : CommitScheme β O where
  Com := Y
  Pf := Unit
  commit b := root D.L D.H D.n (D.enc b) 0
  ext c := D.dec (wordOf D.L D.H D.n c)
  ext_commit b := by
    exact (D.dec_win _ _ (wordOf_root D.hI D.n (D.enc b))).trans (D.dec_enc b)
  prove _ _ := ()
  verify _ _ _ := True
  complete _ _ _ := trivial

/-- **No `UniqueCommitment` instance on the Merkle word commitment has an empty `Collide`**: every one-flip pair collides. -/
theorem merkle_no_unique {O : OracleInterface β} (D : MerkleData α Y β) [UC : UniqueCommitment β O (CS := merkleCS D O)]
    (b : β) {j : ℕ} (hj : j < 2 ^ D.n) {a : α} (ha : a ≠ D.enc b j) :
    root D.L D.H D.n (Function.update (D.enc b) j a) 0 ≠ root D.L D.H D.n (D.enc b) 0 ∧
      UC.Collide (root D.L D.H D.n (D.enc b) 0) (root D.L D.H D.n (Function.update (D.enc b) j a) 0) := by
  have := no_unique_of_wordCommit (merkleCS D O) (n := D.n) D.enc D.dec
    (fun w => root D.L D.H D.n w 0) (fun _ => rfl)
    (fun w w' e i hi => by simpa using root_inj D.hI D.n w w' 0 e i hi)
    (fun w => D.dec_win _ _ (wordOf_root D.hI D.n w))
    D.dec_flip b hj ha
  exact this

open Classical in
/-- **Composition with the probability form**: for the honest codeword `w = enc b` and the flipped word, (i) the roots
differ, (ii) every `UniqueCommitment` must declare the pair `Collide`, (iii) the honest proof is accepted on every
query set and the flipped word on its own FS query set with probability `≥ 1 − l/2^n` (`merkle_ungrind_negative`). -/
theorem merkle_compose (D : MerkleData α Y β) [UC : UniqueCommitment β O (CS := merkleCS D O)]
    (chk : Finset ℕ → (ℕ → α) → Prop) (hloc : Local chk) (b : β)
    (hhon : ∀ S : Finset ℕ, (∀ i ∈ S, i < 2 ^ D.n) → chk S (D.enc b)) (l : ℕ) (j : Fin (2 ^ D.n)) {a : α} (ha : a ≠ D.enc b j) :
    UC.Collide (root D.L D.H D.n (D.enc b) 0) (root D.L D.H D.n (Function.update (D.enc b) j a) 0) ∧
      (∀ s : Fin l → Fin (2 ^ D.n), AccHonest D.L D.H D.n chk (D.enc b) (qset s)) ∧
      1 - (l : ℚ) / (2 ^ D.n : ℕ) ≤
        prob l (2 ^ D.n) (fun s => AccHonest D.L D.H D.n chk (Function.update (D.enc b) j a) (qset s)) := by
  have h1 := (merkle_no_unique (O := O) D b j.isLt ha).2
  have h2 := merkle_ungrind_negative D.hI chk hloc D.n l (D.enc b) hhon j ha
  exact ⟨h1, h2.2.1, h2.2.2⟩

end Concrete

/-! ### Non-vacuity: repetition code over `Bool` on 4 positions, free hash -/

/-- Majority decoding over the window `0..3`. -/
def majDec (w : ℕ → Bool) : Bool := decide (2 < (List.range 4).countP w)

/-- The toy Merkle data: `enc b = (b,b,b,b)`, free (injective) hash, majority decoder. -/
def toyData : MerkleData Bool (FreeTree Bool) Bool where
  L := FreeTree.leaf
  H := FreeTree.node
  n := 2
  hI := inj_free Bool
  enc b := fun _ => b
  dec := majDec
  dec_enc b := by cases b <;> decide
  dec_win w w' h := by
    have : (List.range 4).countP w = (List.range 4).countP w' :=
      List.countP_congr (fun i hi => by simp [h i (by simpa using hi)])
    simp [majDec, this]
  dec_flip b j a := by
    rcases lt_or_ge j 4 with h | h
    · interval_cases j <;> cases b <;> cases a <;> decide
    · have h1 : (List.range 4).countP (Function.update (fun _ : ℕ => b) j a) =
          (List.range 4).countP (fun _ => b) :=
        List.countP_congr (fun i hi => by
          rw [Function.update_of_ne (by simp at hi; omega)])
      simp only [majDec, h1]
      cases b <;> decide

/-- The toy scheme has a one-flip pair, so no `UniqueCommitment` instance on it has an empty `Collide`. -/
theorem toy_no_unique {O : OracleInterface Bool} [UC : UniqueCommitment Bool O (CS := merkleCS toyData O)] :
    ∃ c c', UC.Collide c c' :=
  ⟨_, _, (merkle_no_unique (O := O) toyData (j := 3) false (by decide) (a := true) (by simp [toyData])).2⟩

end NockvmE2E.Ung
