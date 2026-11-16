/-
: everything about the terminal openings round.

* `Finite` / `DecidableEq` for `BatchOpening Y s` (the openings round needs a finite message).
* `OpenAll`: one `BatchOpening` per merkle round; `Op` decodes to it.
* the codec `F ↪ Y` with `dec := Function.invFun enc`.
* `merkleCheck`: the hash-oracle check, `verifyOpeningClaims` on claims that carry the roots only,
  with its root-only lemma.
* `Agrees` / `QueryOnly`: the local check of the succinct verifier reads the words only through
  the opened values (decoded), at the selected positions.
-/
import NockvmE2E.Merkle.Compiled
import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Game

open BinaryTree InductiveMerkleTree OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration

namespace NockvmE2E.Merkle

/-! ## Finiteness and decidable equality of batch openings -/

section FiniteOpening

variable {α : Type}

theorem finite_leafData [Finite α] : ∀ s : Skeleton, Finite (LeafData α s)
  | .leaf =>
      Finite.of_surjective (fun a : α => (LeafData.leaf a : LeafData α .leaf)) (by
        intro x; cases x with | leaf a => exact ⟨a, rfl⟩)
  | .internal l r =>
      haveI := finite_leafData l
      haveI := finite_leafData r
      Finite.of_surjective
        (fun p : LeafData α l × LeafData α r => (LeafData.internal p.1 p.2 : LeafData α (.internal l r)))
        (by intro x; cases x with | internal a b => exact ⟨(a, b), rfl⟩)

instance instFiniteLeafData [Finite α] (s : Skeleton) : Finite (LeafData α s) := finite_leafData s

def decEqLeafData [DecidableEq α] : (s : Skeleton) → DecidableEq (LeafData α s)
  | .leaf, .leaf a, .leaf b =>
      if h : a = b then isTrue (by rw [h]) else isFalse (fun e => h (by cases e; rfl))
  | .internal l r, .internal a₁ b₁, .internal a₂ b₂ =>
      letI := decEqLeafData l
      letI := decEqLeafData r
      if h : a₁ = a₂ ∧ b₁ = b₂ then isTrue (by rw [h.1, h.2])
      else isFalse (fun e => h (by cases e; exact ⟨rfl, rfl⟩))

instance instDecEqLeafData [DecidableEq α] (s : Skeleton) : DecidableEq (LeafData α s) :=
  decEqLeafData s

theorem finite_selectedValues [Finite α] :
    ∀ {s : Skeleton} (sel : LeafData Bool s), Finite (SelectedValues α sel)
  | _, .leaf true => (inferInstance : Finite α)
  | _, .leaf false => (inferInstance : Finite PUnit.{1})
  | _, .internal l r =>
      haveI := finite_selectedValues l
      haveI := finite_selectedValues r
      (inferInstance : Finite (SelectedValues α l × SelectedValues α r))

instance instFiniteSelectedValues [Finite α] {s : Skeleton} (sel : LeafData Bool s) :
    Finite (SelectedValues α sel) := finite_selectedValues sel

def decEqSelectedValues [DecidableEq α] :
    ∀ {s : Skeleton} (sel : LeafData Bool s), DecidableEq (SelectedValues α sel)
  | _, .leaf true => (inferInstance : DecidableEq α)
  | _, .leaf false => (inferInstance : DecidableEq PUnit.{1})
  | _, .internal l r =>
      letI := decEqSelectedValues l
      letI := decEqSelectedValues r
      (inferInstance : DecidableEq (SelectedValues α l × SelectedValues α r))

instance instDecEqSelectedValues [DecidableEq α] {s : Skeleton} (sel : LeafData Bool s) :
    DecidableEq (SelectedValues α sel) := decEqSelectedValues sel

/-- Code of a batch proof: a finite type with decidable equality that the proof injects into
(the hypotheses `hr`/`hl` are propositions and are dropped). -/
def BPCode (α : Type) : {s : Skeleton} → LeafData Bool s → Type
  | _, .leaf true => PUnit
  | _, .leaf false => Empty
  | _, .internal l r => (BPCode α l × BPCode α r) ⊕ ((α × BPCode α l) ⊕ (α × BPCode α r))

theorem finite_bpCode [Finite α] : ∀ {s : Skeleton} (sel : LeafData Bool s), Finite (BPCode α sel)
  | _, .leaf true => (inferInstance : Finite PUnit.{1})
  | _, .leaf false => (inferInstance : Finite Empty)
  | _, .internal l r =>
      haveI := finite_bpCode l
      haveI := finite_bpCode r
      (inferInstance : Finite ((BPCode α l × BPCode α r) ⊕ ((α × BPCode α l) ⊕ (α × BPCode α r))))

instance instFiniteBPCode [Finite α] {s : Skeleton} (sel : LeafData Bool s) :
    Finite (BPCode α sel) := finite_bpCode sel

def decEqBPCode [DecidableEq α] : ∀ {s : Skeleton} (sel : LeafData Bool s), DecidableEq (BPCode α sel)
  | _, .leaf true => (inferInstance : DecidableEq PUnit.{1})
  | _, .leaf false => (inferInstance : DecidableEq Empty)
  | _, .internal l r =>
      letI := decEqBPCode l
      letI := decEqBPCode r
      (inferInstance : DecidableEq ((BPCode α l × BPCode α r) ⊕ ((α × BPCode α l) ⊕ (α × BPCode α r))))

instance instDecEqBPCode [DecidableEq α] {s : Skeleton} (sel : LeafData Bool s) :
    DecidableEq (BPCode α sel) := decEqBPCode sel

def _root_.InductiveMerkleTree.BatchProof.code : {s : Skeleton} → {sel : LeafData Bool s} → BatchProof α sel → BPCode α sel
  | _, _, .leaf => PUnit.unit
  | _, _, .internalBoth pl pr => .inl (pl.code, pr.code)
  | _, _, .pruneRight _ y pl => .inr (.inl (y, pl.code))
  | _, _, .pruneLeft _ y pr => .inr (.inr (y, pr.code))

theorem _root_.InductiveMerkleTree.BatchProof.code_injective {s : Skeleton} {sel : LeafData Bool s} :
    Function.Injective (BatchProof.code : BatchProof α sel → BPCode α sel) := by
  intro p
  induction p with
  | leaf => intro q _; cases q; rfl
  | internalBoth pl pr ihl ihr =>
      intro q h
      cases q with
      | internalBoth ql qr =>
          have h' := Prod.mk.inj (Sum.inl.inj h)
          rw [ihl h'.1, ihr h'.2]
      | pruneRight _ _ _ => exact (Sum.inl_ne_inr h).elim
      | pruneLeft _ _ _ => exact (Sum.inl_ne_inr h).elim
  | pruneRight hr y pl ih =>
      intro q h
      cases q with
      | internalBoth _ _ => exact (Sum.inr_ne_inl h).elim
      | pruneRight _ y' ql =>
          have h' := Prod.mk.inj (Sum.inl.inj (Sum.inr.inj h))
          rw [h'.1, ih h'.2]
      | pruneLeft _ _ _ => exact (Sum.inl_ne_inr (Sum.inr.inj h)).elim
  | pruneLeft hl y pr ih =>
      intro q h
      cases q with
      | internalBoth _ _ => exact (Sum.inr_ne_inl h).elim
      | pruneRight _ _ _ => exact (Sum.inr_ne_inl (Sum.inr.inj h)).elim
      | pruneLeft _ y' qr =>
          have h' := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj h))
          rw [h'.1, ih h'.2]

/-- Code of a batch opening. -/
def _root_.InductiveMerkleTree.BatchOpening.code {s : Skeleton} (o : BatchOpening α s) :
    (sel : LeafData Bool s) × (SelectedValues α sel × BPCode α sel) :=
  ⟨o.selector, (o.values, o.proof.code)⟩

theorem _root_.InductiveMerkleTree.BatchOpening.code_injective {s : Skeleton} :
    Function.Injective (BatchOpening.code : BatchOpening α s → _) := by
  rintro ⟨sel, v, p⟩ ⟨sel', v', p'⟩ h
  simp only [BatchOpening.code, Sigma.mk.injEq] at h
  obtain ⟨rfl, hvp⟩ := h
  have h' := Prod.mk.inj (eq_of_heq hvp)
  rw [h'.1, BatchProof.code_injective h'.2]

instance instFiniteBatchOpening [Finite α] (s : Skeleton) : Finite (BatchOpening α s) :=
  Finite.of_injective _ BatchOpening.code_injective

instance instDecEqBatchOpening [DecidableEq α] (s : Skeleton) : DecidableEq (BatchOpening α s) :=
  BatchOpening.code_injective.decidableEq

end FiniteOpening


/-! ## Codec `F ↪ Y` -/

section Codec

variable {F Y : Type}

/-- Decoder of the leaf codec: `Function.invFun enc` (arbitrary off the image). -/
noncomputable def codecDec (ne : Nonempty F) (enc : F ↪ Y) : Y → F :=
  have := ne
  Function.invFun enc

theorem codecDec_enc (ne : Nonempty F) (enc : F ↪ Y) (x : F) : codecDec ne enc (enc x) = x := by
  unfold codecDec
  have := ne
  exact Function.leftInverse_invFun enc.injective x

end Codec

/-! ## Openings of a masked protocol -/

section Openings

variable {Y : Type}

/-- Skeletons of the merkle rounds, in order. -/
def merkleSkels : MRounds Y → List Skeleton
  | [] => []
  | ⟨_, .clear⟩ :: ms => merkleSkels ms
  | ⟨_, .merkle skel _ _ _ _⟩ :: ms => skel :: merkleSkels ms

theorem merkleSkels_length [Finite Y] [DecidableEq Y] (ms : MRounds Y) :
    (merkleSkels ms).length = merkleCount Y ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      obtain ⟨r, k⟩ := m
      cases k
      · exact ih
      · exact congrArg (· + 1) ih

/-- One batch opening per merkle round. -/
def OpenAll (Y : Type) : List Skeleton → Type
  | [] => PUnit
  | s :: l => BatchOpening Y s × OpenAll Y l

instance instFiniteOpenAll [Finite Y] : (skels : List Skeleton) → Finite (OpenAll Y skels)
  | [] => (inferInstance : Finite PUnit.{1})
  | s :: l =>
      haveI := instFiniteOpenAll l
      (inferInstance : Finite (BatchOpening Y s × OpenAll Y l))

def decEqOpenAll [DecidableEq Y] : (skels : List Skeleton) → DecidableEq (OpenAll Y skels)
  | [] => (inferInstance : DecidableEq PUnit.{1})
  | s :: l =>
      letI := decEqOpenAll l
      (inferInstance : DecidableEq (BatchOpening Y s × OpenAll Y l))

instance instDecEqOpenAll [DecidableEq Y] (skels : List Skeleton) : DecidableEq (OpenAll Y skels) :=
  decEqOpenAll skels

/-- The `j`-th opening. -/
def OpenAll.get : (skels : List Skeleton) → OpenAll Y skels →
    (j : Fin skels.length) → BatchOpening Y (skels.get j)
  | _ :: _, (o, _), ⟨0, _⟩ => o
  | _ :: l, (_, os), ⟨j + 1, h⟩ => OpenAll.get l os ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- Merkle addresses: the round tag together with the internal node (domain separation). -/
abbrev MAddress (skels : List Skeleton) : Type :=
  (j : Fin skels.length) × SkeletonInternalIndex (skels.get j)

/-- VCVio configuration of a masked protocol: tag `j` = `j`-th merkle round. -/
def mconfig (skels : List Skeleton) :
    MerkleTreeMultiExtractability.Configuration (Fin skels.length) (MAddress skels) where
  skeleton j := skels.get j
  addressKey j i := ⟨j, i⟩

variable {Query : Type}

/-- Opening claims for the `j`-th merkle root and opening; the checkpoint log is a free parameter
(the verifier never reads it, see `bits_verifyOpeningClaims_relog`). -/
def mkClaims (skels : List Skeleton) (roots : List Y) (h : roots.length = skels.length)
    (ops : OpenAll Y skels) (logs : Fin skels.length → MerkleTreeExtractor.QueryLog Query Y) :
    List (MerkleTreeMultiExtractability.OpeningClaim Query Y (mconfig skels)) :=
  List.ofFn fun j =>
    { tag := j
      checkpoint := { root := roots.get (j.cast h.symm), cumulativeLog := logs j }
      opening := OpenAll.get skels ops j }

/-- The Merkle check of the succinct verifier: all `k` openings verify against the roots, through
VCVio's `verifyOpeningClaims` (hash oracle only). -/
def merkleCheck [DecidableEq Y] {Op : Type} (skels : List Skeleton)
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress skels) Y)
    (decode : Op → OpenAll Y skels) (roots : List Y) (op : Op) :
    OracleComp (Query →ₒ Y) Bool :=
  if h : roots.length = skels.length then
    (fun attempts => attempts.all fun a => a.2.accepted) <$>
      MerkleTreeMultiExtractability.verifyOpeningClaims model
        (mkClaims skels roots h (decode op) fun _ => [])
  else pure false

/-- Acceptance bits of evaluated claims. -/
def acceptBits {Cfg Address : Type} {config : MerkleTreeMultiExtractability.Configuration Cfg Address}
    (attempts : List (MerkleTreeMultiExtractability.AnyEvaluatedOpeningClaim Cfg Query Address Y
      config)) : List Bool :=
  attempts.map fun a => a.2.accepted

/-- Root-only: re-labelling the checkpoint logs of the claims does not change the acceptance bits
of `verifyOpeningClaims` (it reads each checkpoint through its root only). -/
theorem bits_verifyOpeningClaims_relog [DecidableEq Y] {Cfg Address : Type}
    {config : MerkleTreeMultiExtractability.Configuration Cfg Address}
    (model : MerkleTreeExtractability.NodeQueryModel Query Address Y)
    (L : MerkleTreeMultiExtractability.OpeningClaim Query Y config →
      MerkleTreeExtractor.QueryLog Query Y) :
    (claims : List (MerkleTreeMultiExtractability.OpeningClaim Query Y config)) →
    acceptBits <$> MerkleTreeMultiExtractability.verifyOpeningClaims model
        (claims.map fun c => { c with checkpoint := { c.checkpoint with cumulativeLog := L c } }) =
      acceptBits <$> MerkleTreeMultiExtractability.verifyOpeningClaims model claims
  | [] => by simp [MerkleTreeMultiExtractability.verifyOpeningClaims, acceptBits]
  | c :: cs => by
      have ih := bits_verifyOpeningClaims_relog model L cs
      simp only [List.map_cons, MerkleTreeMultiExtractability.verifyOpeningClaims, map_bind, map_pure]
      refine bind_congr fun accepted => ?_
      have ih' := congrArg (fun m => (fun l => accepted :: l) <$> m) ih
      simpa [acceptBits] using ih'


/-- Root-only lemma for the Merkle check: the claims built by `mkClaims` verify identically for
every choice of checkpoint logs. In particular `merkleCheck` reads the roots and the openings
only, never an extraction log. -/
theorem bits_mkClaims_root_only [DecidableEq Y] (skels : List Skeleton)
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress skels) Y)
    (roots : List Y) (h : roots.length = skels.length) (ops : OpenAll Y skels)
    (logs : Fin skels.length → MerkleTreeExtractor.QueryLog Query Y) :
    acceptBits <$> MerkleTreeMultiExtractability.verifyOpeningClaims model
        (mkClaims skels roots h ops logs) =
      acceptBits <$> MerkleTreeMultiExtractability.verifyOpeningClaims model
        (mkClaims skels roots h ops fun _ => []) := by
  have : mkClaims skels roots h ops logs =
      (mkClaims (Query := Query) skels roots h ops (fun _ => [])).map fun c =>
        { c with checkpoint := { c.checkpoint with cumulativeLog := logs c.tag } } := by
    simp [mkClaims, List.map_ofFn, Function.comp_def]
  rw [this]
  exact bits_verifyOpeningClaims_relog model _ _

theorem merkleCheck_of_length [DecidableEq Y] {Op : Type} (skels : List Skeleton)
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress skels) Y)
    (decode : Op → OpenAll Y skels) (roots : List Y) (op : Op) (h : roots.length = skels.length) :
    merkleCheck skels model decode roots op =
      (fun bits => bits.all id) <$> (acceptBits <$>
        MerkleTreeMultiExtractability.verifyOpeningClaims model
          (mkClaims skels roots h (decode op) fun _ => [])) := by
  simp [merkleCheck, h, acceptBits]

theorem merkleCheck_of_length_ne [DecidableEq Y] {Op : Type} (skels : List Skeleton)
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress skels) Y)
    (decode : Op → OpenAll Y skels) (roots : List Y) (op : Op) (h : roots.length ≠ skels.length) :
    merkleCheck skels model decode roots op = pure false := by
  simp [merkleCheck, h]

end Openings

/-! ## The local check reads words only through opened values -/

section QueryOnly

variable {Y : Type} [Finite Y] [DecidableEq Y] {Op : Type} [Finite Op] [DecidableEq Op]

/-- A compiled path `p` and an in-the-clear path `q` agree: clear messages and all challenges are
equal, and for each merkle round the decoded opened values equal the word at the selected leaves. -/
def Agrees : (ms : MRounds Y) → OpenAll Y (merkleSkels ms) →
    (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath →
    (protocol (baseRounds Y ms)).tree.ExecutionPath → Prop
  | [], _, _, _ => True
  | ⟨_, .clear⟩ :: ms, os, p, q => p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ Agrees ms os p.2.2 q.2.2
  | ⟨_, .merkle _ _ ne enc words⟩ :: ms, (o, os), p, q =>
      p.2.1 = q.2.1 ∧
        o.values.map (codecDec ne enc) = selectedValues (words q.1) o.selector ∧
        Agrees ms os p.2.2 q.2.2

/-- The local check of the succinct verifier is *query-only* relative to the in-the-clear check:
if it accepts a compiled path, then the in-the-clear check accepts every path that agrees with it,
i.e. that carries the same clear messages and challenges and, at the opened positions, the decoded
opened values. -/
def QueryOnly {Input : Type} (ms : MRounds Y) (decode : Op → OpenAll Y (merkleSkels ms))
    (accepts : Input → (protocol (baseRounds Y ms)).tree.ExecutionPath → Bool)
    (localAccepts : Input → (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath → Bool) :
    Prop :=
  ∀ (z : Input) (p : (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath)
    (q : (protocol (baseRounds Y ms)).tree.ExecutionPath),
    Agrees ms (decode (pathRootsK Y Op ms p).2) p q → localAccepts z p = true → accepts z q = true

/-- Query-only is exactly what turns "the local check accepted" into "the paired check accepts"
once the words agree. -/
theorem QueryOnly.accepts_of_agrees {Input : Type} {ms : MRounds Y}
    {decode : Op → OpenAll Y (merkleSkels ms)}
    {accepts : Input → (protocol (baseRounds Y ms)).tree.ExecutionPath → Bool}
    {localAccepts : Input → (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath → Bool}
    (h : QueryOnly ms decode accepts localAccepts) (z : Input)
    (p : (protocol (compiledRoundsK Y Op ms)).tree.ExecutionPath)
    (q : (protocol (baseRounds Y ms)).tree.ExecutionPath)
    (hag : Agrees ms (decode (pathRootsK Y Op ms p).2) p q) (hl : localAccepts z p = true) :
    accepts z q = true := h z p q hag hl

end QueryOnly

end NockvmE2E.Merkle
