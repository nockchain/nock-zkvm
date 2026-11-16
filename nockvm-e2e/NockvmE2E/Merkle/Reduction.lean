/-
Merkle (B) file 4: the observer state and memo, the reduction `B`, memo stability.
-/
import NockvmE2E.Merkle.Rename

open OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Merkle.Reduction

open NockvmE2E.Merkle

section Obs

variable {Y : Type} [Finite Y] [DecidableEq Y] {Op : Type} [Finite Op] [DecidableEq Op]
  (Query Statement Salt : Type)

/-- Observer state of the instrumented real world: the hash log in A's raw query order, the number
of FS answers so far, the memo `(z, rootPrefix, root) ↦ (checkpoint index, hash-log snapshot)`
(entries are never overwritten), and the set of FS keys seen. -/
structure Obs (Y : Type) where
  log : List (Query × Y)
  nck : ℕ
  memo : (Statement × Salt) × List Y × Y → Option (ℕ × List (Query × Y))

variable {Query Statement Salt}

/-- The empty observer state. -/
def Obs.init : Obs Query Statement Salt Y := ⟨[], 0, fun _ => none⟩

variable [DecidableEq Statement] [DecidableEq Salt]

/-- Insert unless present: entries are never overwritten. -/
def memoAdd {V : Type} (m : (Statement × Salt) × List Y × Y → Option V)
    (k : (Statement × Salt) × List Y × Y) (v : V) : (Statement × Salt) × List Y × Y → Option V :=
  fun k' => if k' = k then (m k').or (some v) else m k'

/-- Insert several entries (same value, same input). -/
def addEntries {V : Type} (z : Statement × Salt) (es : List (List Y × Y))
    (v : V) (m : (Statement × Salt) × List Y × Y → Option V) :
    (Statement × Salt) × List Y × Y → Option V :=
  es.foldl (fun m e => memoAdd m (z, e) v) m

/-- `m'` keeps every entry of `m`. -/
def Extends {V : Type} (m m' : (Statement × Salt) × List Y × Y → Option V) : Prop :=
  ∀ k v, m k = some v → m' k = some v

theorem Extends.refl {V : Type} (m : (Statement × Salt) × List Y × Y → Option V) : Extends m m :=
  fun _ _ h => h

theorem Extends.trans {V : Type} {m m' m'' : (Statement × Salt) × List Y × Y → Option V}
    (h : Extends m m') (h' : Extends m' m'') : Extends m m'' :=
  fun k v hk => h' k v (h k v hk)

theorem memoAdd_extends {V : Type} (m : (Statement × Salt) × List Y × Y → Option V) (k v) :
    Extends m (memoAdd m k v) := by
  intro k' w h
  unfold memoAdd
  split_ifs with hk
  · simp [h]
  · exact h

theorem memoAdd_isSome {V : Type} (m : (Statement × Salt) × List Y × Y → Option V) (k v) :
    memoAdd m k v k ≠ none := by
  simp [memoAdd, Option.or]
  cases m k <;> simp

theorem addEntries_extends {V : Type} (z : Statement × Salt) (es : List (List Y × Y)) (v : V)
    (m : (Statement × Salt) × List Y × Y → Option V) : Extends m (addEntries z es v m) := by
  induction es generalizing m with
  | nil => exact Extends.refl m
  | cons e es ih => exact (memoAdd_extends m _ v).trans (ih _)

theorem addEntries_defined {V : Type} (z : Statement × Salt) (es : List (List Y × Y)) (v : V)
    (m : (Statement × Salt) × List Y × Y → Option V) :
    ∀ e ∈ es, addEntries z es v m (z, e) ≠ none := by
  induction es generalizing m with
  | nil => simp
  | cons e' es ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · intro h0
      have := memoAdd_isSome m (z, e) v
      cases hm : memoAdd m (z, e) v (z, e) with
      | none => exact this hm
      | some w =>
        have h3 := addEntries_extends z es v (memoAdd m (z, e) v) _ w hm
        rw [show addEntries z (e :: es) v m = addEntries z es v (memoAdd m (z, e) v) from rfl,
          h3] at h0
        cases h0
    · exact ih _ e he

/-- The memo entries a compiled FS key makes defined: (root prefix, root) of each merkle round in
the key's prefix. Mirrors `translateK`. -/
def keyEntries : (ms : MRounds Y) → List Y →
    Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms) → List (List Y × Y)
  | [], _, _ => []
  | ⟨_, .clear⟩ :: _, _, .inl _ => []
  | ⟨_, .clear⟩ :: ms, pre, .inr (_, _, k) => keyEntries ms pre k
  | ⟨_, .merkle _ _ _ _ _⟩ :: _, pre, .inl (_, root, _) => [(pre, root)]
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, pre, .inr (root, _, k) => (pre, root) :: keyEntries ms (pre ++ [show Y from root]) k

variable (Y Op) (ms : MRounds Y)

/-- The observer: hash answers are logged in raw order; an FS answer takes a checkpoint (the current
hash-log snapshot) for every root prefix of the key not yet in the memo. -/
def obsStep : Obs Query Statement Salt Y →
    (t : Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)) →
    Sum.elim (fun _ : Query => Y) Key.Challenge t → Obs Query Statement Salt Y
  | s, .inl q, a => { s with log := s.log ++ [(q, show Y from a)] }
  | s, .inr d, _ =>
      { s with nck := s.nck + 1,
               memo := addEntries d.input (keyEntries ms [] d) (s.nck, s.log) s.memo }

variable {Y Op ms}

/-- The word the memo assigns to `(z, pre, root)`: the extraction `ext` applied to the snapshot
of its checkpoint (`[]` if none). `ext` is the (hash-log ↦ word) extractor, supplied by Phases. -/
def memoWords (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)
    (s : Obs Query Statement Salt Y) (r : Round) (hr : Nonempty r.Message) (z : Statement × Salt)
    (pre : List Y) (root : Y) : r.Message :=
  ext r hr pre (match s.memo (z, pre, root) with | some (_, h) => h | none => []) root

theorem memoWords_congr (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)
    {s s' : Obs Query Statement Salt Y} {r : Round} {hr : Nonempty r.Message} {z pre root}
    (h : s.memo (z, pre, root) = s'.memo (z, pre, root)) :
    memoWords ext s r hr z pre root = memoWords ext s' r hr z pre root := by
  unfold memoWords
  rw [h]

theorem obsStep_hash_memo (s : Obs Query Statement Salt Y) (q : Query) (a : Y) :
    (obsStep Y Op ms s (.inl q) a).memo = s.memo := rfl

theorem obsStep_extends (s : Obs Query Statement Salt Y)
    (t : Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
    (a : Sum.elim (fun _ : Query => Y) Key.Challenge t) :
    Extends s.memo (obsStep Y Op ms s t a).memo := by
  rcases t with q | d
  · exact Extends.refl _
  · exact addEntries_extends _ _ _ _

/-- After an FS answer at `d`, all memo entries of `d` are defined, and stay defined. -/
theorem obsStep_defined (s : Obs Query Statement Salt Y)
    (d : Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms))
    (a : Key.Challenge d) :
    ∀ e ∈ keyEntries ms [] d, (obsStep Y Op ms s (.inr d) a).memo (d.input, e) ≠ none :=
  addEntries_defined _ _ _ _

theorem Extends.eq_of_ne {V : Type} {m m' : (Statement × Salt) × List Y × Y → Option V}
    (h : Extends m m') {k} (hk : m k ≠ none) : m k = m' k := by
  cases hm : m k with
  | none => exact absurd hm hk
  | some w => exact (h k w hm).symm

variable (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)

/-- **Memo stability.** A key whose memo entries are all defined at `s` is translated identically
at every later state `s'` (entries are never overwritten). -/
theorem translateK_stable (s s' : Obs Query Statement Salt Y) (hext : Extends s.memo s'.memo) :
    ∀ (ms : MRounds Y) (pre : List Y)
      (d : Key (Statement × Salt) PUnit (compiledRoundsK Y Op ms)),
      (∀ e ∈ keyEntries ms pre d, s.memo (d.input, e) ≠ none) →
      translateK Y Op ms (memoWords ext s') pre d = translateK Y Op ms (memoWords ext s) pre d
  | [], _, _, _ => rfl
  | ⟨_, .clear⟩ :: _, _, .inl _, _ => rfl
  | ⟨_, .clear⟩ :: ms, pre, .inr (_, _, k), h => by
      simp only [translateK]
      rw [translateK_stable s s' hext ms pre k h]
  | ⟨r, .merkle _ _ ne _ we⟩ :: _, pre, .inl (z, root, _), h => by
      have := hext.eq_of_ne (h (pre, root) (by simp [keyEntries]))
      have e1 : memoWords ext s' r (merkle_nonempty ne we) z pre root =
          memoWords ext s r (merkle_nonempty ne we) z pre root :=
        memoWords_congr ext (r := r) (z := z) this.symm
      simp only [translateK]
      rw [e1]
  | ⟨r, .merkle _ _ ne _ we⟩ :: ms, pre, .inr (root, _, k), h => by
      have h1 := hext.eq_of_ne (h (pre, root) (by simp [keyEntries]))
      have h2 : ∀ e ∈ keyEntries ms (pre ++ [show Y from root]) k, s.memo (k.input, e) ≠ none :=
        fun e he => h e (by simp [keyEntries, he])
      simp only [translateK]
      have e1 : memoWords ext s' r (merkle_nonempty ne we) k.input pre root =
          memoWords ext s r (merkle_nonempty ne we) k.input pre root :=
        memoWords_congr ext (r := r) h1.symm
      rw [translateK_stable s s' hext ms _ k h2, e1]

end Obs

/-! ## The reduction B -/

section Reduction

variable {Y : Type} [Finite Y] [DecidableEq Y] [SampleableType Y] {Op : Type} [Finite Op]
  [DecidableEq Op] {Query : Type} [DecidableEq Query] {Statement Salt W : Type}
  [DecidableEq Statement] [DecidableEq Salt] {ms : MRounds Y}
  (ext : (r : Round) → Nonempty r.Message → List Y → List (Query × Y) → Y → r.Message)

/-- Compiled messages ↦ paired messages (word read from `words`, root kept). -/
def pairMsgs {Input : Type} (z : Input) (words : (r : Round) → Nonempty r.Message → Input → List Y → Y → r.Message) :
    (ms : MRounds Y) → List Y → PublicMessages (compiledRoundsK Y Op ms) →
    PublicMessages (pairedRoundsK Y ms)
  | [], _, _ => PUnit.unit
  | ⟨_, .clear⟩ :: ms, pre, (m, rest) => (m, pairMsgs z words ms pre rest)
  | ⟨r, .merkle _ _ ne _ we⟩ :: ms, pre, (root, rest) =>
      ((words r (merkle_nonempty ne we) z pre root, root), pairMsgs z words ms (pre ++ [show Y from root]) rest)

/-- The (root prefix, root) entries of the merkle rounds of a compiled proof. -/
def rootEntries : (ms : MRounds Y) → List Y → PublicMessages (compiledRoundsK Y Op ms) →
    List (List Y × Y)
  | [], _, _ => []
  | ⟨_, .clear⟩ :: ms, pre, (_, rest) => rootEntries ms pre rest
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, pre, (root, rest) =>
      (pre, root) :: rootEntries ms (pre ++ [show Y from root]) rest

/-- B's local simulation of A: coins forwarded, hash lazily with B's own coins, FS key `d` from a local
cache else B's FS oracle at `translateK … (memoWords ext s) [] d`. -/
noncomputable def bImplK :=
  Rename.bImpl (RH := fun _ : Query => Y) (R := Key.Challenge)
    (R' := (Key.Challenge : Key (Statement × Salt) PUnit (pairedRoundsK Y ms) → Type))
    (obsStep Y Op ms (Query := Query) (Statement := Statement) (Salt := Salt))
    (fun s => translateK Y Op ms (memoWords ext s) [])
    (untranslateK Y Op ms)
    (fun s d d' h => untranslate_translateK Y Op ms (memoWords ext s) [] d d' h)
    (fun d' => (untranslate_challengeK Y Op ms d').symm)

/-- The end-of-A observer state: checkpoints for the roots of A's final proof. -/
def finalObs (s : Obs Query Statement Salt Y) (z : Statement × Salt)
    (msgs : PublicMessages (compiledRoundsK Y Op ms)) : Obs Query Statement Salt Y :=
  { s with memo := addEntries z (rootEntries ms [] msgs) (s.nck, s.log) s.memo }

/-- **The reduction B**, a `SingleSaltAdversary` on the paired protocol. It runs A under `bImplK`,
then reads the words of A's roots from the end-of-A memo. Its witness is A's witness together with
the final observer state (A's view: hash log and memo). -/
noncomputable def reductionB
    (A : SuccinctAdversaryK Y Op Query Statement Salt W ms) :
    SingleSaltAdversary Statement Salt (W × Obs Query Statement Salt Y) (pairedRoundsK Y ms) := do
  let r ← (simulateQ (bImplK (Op := Op) ext) A).run (Obs.init, ∅, ∅)
  match r with
  | (none, _) => pure none
  | (some (statement, (salt, msgs), w), st) =>
      let s := finalObs (ms := ms) (Op := Op) st.1 (statement, salt) msgs
      pure (some (statement,
        (salt, pairMsgs (Op := Op) (statement, salt) (memoWords ext s) ms [] msgs), (w, s)))

/-- The renaming lemma for B's simulation (instance of `evalDist_adaptiveRenameK` at `memoWords`). -/
theorem reduction_rename {α : Type}
    (oa : OracleComp (SuccinctSpecK Y Op Query Statement Salt ms) α) (s₀ : Obs Query Statement Salt Y) :
    letI : MeasurableSpace (α × Obs Query Statement Salt Y) := ⊤
    𝒟[(fun z => (z.1.1.1, z.1.1.2.1)) <$>
        randomOracleLoggedRun ((simulateQ (bImplK (Op := Op) ext) oa).run (s₀, ∅, ∅)) ∅] =
      𝒟[(fun z => (z.1, z.2.1)) <$>
        (simulateQ (Rename.realImpl (obsStep Y Op ms)) oa).run (s₀, ∅)] :=
  Rename.evalDist_adaptiveRenameK ms (memoWords ext) (obsStep Y Op ms) oa s₀

end Reduction

end NockvmE2E.Merkle.Reduction
