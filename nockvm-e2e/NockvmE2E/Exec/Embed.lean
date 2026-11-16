/-
  NockvmE2E/Exec/Embed.lean   (proof-only, may import Mathlib/ArkLib; not in the exe closure)

  Layer A: a fixed complete table `g` of the random oracle's FS half, and
  * L1  `publicStoppedVerify_trueGuards` : accept-all guards, `publicStoppedVerify` under the table returns the path
        "messages interleaved with the table's answers on the keys of the rounds" (`pathOfG`);
  * L2  per-round codecs and the flat reading of the table (`flat_challenge_eq`).
-/
import NockvmE2E.Merkle.SoundnessCoupling
import NockvmE2E.FriPort.Accepts

open OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.Emb

open NockvmE2E.Merkle NockvmE2E.Merkle.SoundnessCoupling NockvmE2E.FriPort

/-! ## Evaluation against a total table -/

section TabEval

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- the result of `oa` when every query is answered by `f` (`none` where `f` has no answer) -/
def tabEval (f : (t : ι) → Option (spec.Range t)) {α : Type} : OracleComp spec α → Option α
  | .pure a => some a
  | .queryBind t k => match f t with
    | some v => tabEval f (k v)
    | none => none

theorem tabEval_query_bind (f : (t : ι) → Option (spec.Range t)) {α : Type} (t : ι)
    (k : spec.Range t → OracleComp spec α) :
    tabEval f (liftM (spec.query t) >>= k) = match f t with
      | some v => tabEval f (k v)
      | none => none := by
  rw [show (liftM (spec.query t) >>= k : OracleComp spec α) = OracleComp.queryBind t k from rfl,
    tabEval]
  rfl

theorem tabEval_pure (f : (t : ι) → Option (spec.Range t)) {α : Type} (a : α) :
    tabEval f (pure a : OracleComp spec α) = some a := rfl

theorem tabEval_liftM_query (f : (t : ι) → Option (spec.Range t)) (t : ι) :
    tabEval f (liftM (spec.query t) : OracleComp spec _) = f t := by
  have := tabEval_query_bind f t (fun v => (pure v : OracleComp spec (spec.Range t)))
  rw [bind_pure] at this
  rw [this]
  rcases f t with _ | v <;> rfl

theorem tabEval_bind (f : (t : ι) → Option (spec.Range t)) {α β : Type} (oa : OracleComp spec α)
    (h : α → OracleComp spec β) :
    tabEval f (oa >>= h) = (tabEval f oa).bind fun x => tabEval f (h x) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [bind_assoc, tabEval_query_bind, tabEval_query_bind]
    rcases f t with _ | v
    · rfl
    · exact ih v

end TabEval

/-! ## L1: the path of a table under accept-all guards -/

section L1

variable {Input : Type} {allRounds : List Round}

/-- The path read off a complete FS table `g` (answers of the key of round `i`), for messages `ms`. -/
def pathOfG (g : (key : Key Input PUnit allRounds) → key.Challenge) :
    (rounds : List Round) → (z : Input) → PublicMessages rounds →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    (protocol rounds).tree.ExecutionPath
  | [], _, _, _, _ => PUnit.unit
  | _ :: rounds, z, (message, messages), embed, preserve =>
      ⟨message, cast (preserve (Key.here z message PUnit.unit)) (g (embed (Key.here z message PUnit.unit))),
        pathOfG g rounds z messages (fun key => embed (Key.later message PUnit.unit key))
          (fun key => preserve (Key.later message PUnit.unit key))⟩

/-- A complete table as an evaluation table. -/
def fsTab (g : (key : Key Input PUnit allRounds) → key.Challenge) :
    (key : Key Input PUnit allRounds) → Option ((oracleSpec Input PUnit allRounds).Range key) :=
  fun key => some (g key)

theorem mapped_trueGuards (g : (key : Key Input PUnit allRounds) → key.Challenge) :
    ∀ (rounds : List Round) (z : Input) (msgs : PublicMessages rounds)
      (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
      (preserve : ∀ key, (embed key).Challenge = key.Challenge),
      tabEval (fsTab g) (mappedStoppedComplete rounds (trueGuards rounds) z msgs embed preserve) =
        some (some (pathOfG g rounds z msgs embed preserve))
  | [], z, msgs, embed, preserve => by
      simp [mappedStoppedComplete, tabEval_pure, pathOfG]
  | round :: rounds, z, (message, messages), embed, preserve => by
      have ih := mapped_trueGuards g rounds z messages
        (fun key => embed (Key.later message PUnit.unit key))
        (fun key => preserve (Key.later message PUnit.unit key))
      simp only [mappedStoppedComplete, trueGuards, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [tabEval_bind]
      rw [tabEval_liftM_query]
      simp only [fsTab, Option.bind_some]
      rw [tabEval_bind, ih]
      simp only [Option.bind_some, tabEval_pure]
      rfl

end L1

/-! ### L1 at the compiled spec: routing the FS summand -/

section L1K

variable {Dg : Type} [Finite Dg] [DecidableEq Dg] {Op : Type} [Finite Op] [DecidableEq Op]
  {Query : Type} {Statement Salt : Type} {ms : MRounds Dg}

/-- The evaluation table of a total table `gAll` on `Query ⊕ Key` (the unif summand has no answer). -/
def tabK (gAll : (d : Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK Dg Op ms)) →
      succinctRange Dg Op Query Statement Salt ms d) :
    (t : (unifSpec + OracleSpec.ofFn (succinctRange Dg Op Query Statement Salt ms)).Domain) →
      Option ((unifSpec + OracleSpec.ofFn (succinctRange Dg Op Query Statement Salt ms)).Range t)
  | .inl _ => none
  | .inr d => some (gAll d)

theorem tabK_route (gAll : (d : Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK Dg Op ms)) →
      succinctRange Dg Op Query Statement Salt ms d) {α : Type}
    (oa : OracleComp (oracleSpec (Statement × Salt) PUnit (compiledRoundsK Dg Op ms)) α) :
    tabEval (tabK gAll) (simulateQ (fsQueriesK (Query := Query)) oa) =
      tabEval (fsTab (fun key => gAll (.inr key))) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [tabEval_pure]
  | query_bind t k ih =>
    have h1 : simulateQ (fsQueriesK (Query := Query)) (liftM (OracleSpec.query t) >>= k) =
      (liftM ((SuccinctSpecK Dg Op Query Statement Salt ms).query (.inr (.inr t))) :
        OracleComp (SuccinctSpecK Dg Op Query Statement Salt ms) _) >>= fun r =>
          simulateQ (fsQueriesK (Query := Query)) (k r) := by
      simp only [simulateQ_bind, simulateQ_liftM_query]
      rfl
    rw [h1, tabEval_query_bind, tabEval_query_bind]
    simp only [tabK, fsTab]
    exact ih _

/-- **L1.** With accept-all guards the public stopped verifier never stops: under a fixed total table it
returns the path of messages interleaved with the table's answers on the keys of the rounds. -/
theorem publicStoppedVerify_trueGuards
    (gAll : (d : Query ⊕ Key (Statement × Salt) PUnit (compiledRoundsK Dg Op ms)) →
      succinctRange Dg Op Query Statement Salt ms d)
    (z : Statement × Salt) (msgs : PublicMessages (compiledRoundsK Dg Op ms)) :
    tabEval (tabK gAll) (simulateQ (fsQueriesK (Query := Query))
        (publicStoppedVerify (compiledRoundsK Dg Op ms) (trueGuards _) z msgs)) =
      some (some (pathOfG (fun key => gAll (.inr key)) (compiledRoundsK Dg Op ms) z msgs id (fun _ => rfl))) := by
  rw [publicStoppedVerify_eq_with, publicStoppedVerifyWith_eq_mapped, tabK_route]
  exact mapped_trueGuards (fun key => gAll (.inr key)) _ z msgs id (fun _ => rfl)

end L1K


/-! ## L3a: `merkleCheck` under a fixed hash table -/

section L3a

open MerkleTreeMultiExtractability MerkleTreeBatchExtractability

variable {Dg : Type} [DecidableEq Dg] {Query : Type} {Address : Type}

/-- the root a batch opening reconstructs when node queries are answered by `h` -/
def rootUnder (h : Query → Dg) (model : MerkleTreeExtractability.NodeQueryModel Query Address Dg)
    {s : BinaryTree.Skeleton} (key : BinaryTree.SkeletonInternalIndex s → Address) (o : InductiveMerkleTree.BatchOpening Dg s) : Dg :=
  AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
    (fun a l r => h (model.mkQuery (key a) (l, r))) o.values o.proof

theorem tabEval_getPutative (h : Query → Dg) (model : MerkleTreeExtractability.NodeQueryModel Query Address Dg) :
    {s : BinaryTree.Skeleton} → (key : BinaryTree.SkeletonInternalIndex s → Address) →
    {sel : BinaryTree.LeafData Bool s} → (v : InductiveMerkleTree.SelectedValues Dg sel) →
    (pf : InductiveMerkleTree.BatchProof Dg sel) →
    tabEval (spec := Query →ₒ Dg) (fun q => some (h q))
      (AddressedMerkleTree.getPutativeBatchRootAddressedM
        (fun a l r => (liftM ((Query →ₒ Dg).query (model.mkQuery (key a) (l, r))) : OracleComp (Query →ₒ Dg) Dg)) v pf) =
      some (AddressedMerkleTree.getPutativeBatchRootAddressedWithHash
        (fun a l r => h (model.mkQuery (key a) (l, r))) v pf)
  | _, key, _, v, .leaf => rfl
  | _, key, _, v, .internalBoth pl pr => by
      simp only [AddressedMerkleTree.getPutativeBatchRootAddressedM,
        AddressedMerkleTree.getPutativeBatchRootAddressedWithHash, tabEval_bind]
      rw [tabEval_getPutative h model (fun a => key (.ofLeft a)) v.1 pl]
      simp only [Option.bind_some]
      rw [tabEval_getPutative h model (fun a => key (.ofRight a)) v.2 pr]
      simp only [Option.bind_some]
      rw [tabEval_liftM_query]
  | _, key, _, v, .pruneRight _ rr pl => by
      simp only [AddressedMerkleTree.getPutativeBatchRootAddressedM,
        AddressedMerkleTree.getPutativeBatchRootAddressedWithHash, tabEval_bind]
      rw [tabEval_getPutative h model (fun a => key (.ofLeft a)) v.1 pl]
      simp only [Option.bind_some]
      rw [tabEval_liftM_query]
  | _, key, _, v, .pruneLeft _ ll pr => by
      simp only [AddressedMerkleTree.getPutativeBatchRootAddressedM,
        AddressedMerkleTree.getPutativeBatchRootAddressedWithHash, tabEval_bind]
      rw [tabEval_getPutative h model (fun a => key (.ofRight a)) v.2 pr]
      simp only [Option.bind_some]
      rw [tabEval_liftM_query]

theorem tabEval_verifyOpening (h : Query → Dg) (model : MerkleTreeExtractability.NodeQueryModel Query Address Dg)
    {s : BinaryTree.Skeleton} (key : BinaryTree.SkeletonInternalIndex s → Address) (root : Dg)
    (o : InductiveMerkleTree.BatchOpening Dg s) :
    tabEval (spec := Query →ₒ Dg) (fun q => some (h q)) (verifyOpening model key root o) =
      some (rootUnder h model key o == root) := by
  unfold verifyOpening AddressedMerkleTree.verifyBatchProofAddressedM
  rw [tabEval_bind, tabEval_getPutative]
  simp only [Option.bind_some, tabEval_pure]
  rfl

theorem tabEval_claims (h : Query → Dg) (model : MerkleTreeExtractability.NodeQueryModel Query Address Dg)
    {Cfg : Type} {config : Configuration Cfg Address} :
    (claims : List (OpeningClaim Query Dg config)) →
    tabEval (spec := Query →ₒ Dg) (fun q => some (h q))
      ((fun attempts => attempts.all fun a => a.2.accepted) <$> verifyOpeningClaims model claims) =
      some (claims.all fun c => rootUnder h model (config.addressKey c.tag) c.opening == c.checkpoint.root)
  | [] => by
      simp [verifyOpeningClaims, tabEval_pure, map_pure]
  | c :: cs => by
      have ih := tabEval_claims h model cs
      rw [map_eq_bind_pure_comp, tabEval_bind] at ih ⊢
      simp only [verifyOpeningClaims, bind_assoc, tabEval_bind, tabEval_verifyOpening, Option.bind_some]
      rcases hv : tabEval (spec := Query →ₒ Dg) (fun q => some (h q)) (verifyOpeningClaims model cs) with _ | x
      · simp [hv] at ih
      · simp only [hv, Option.bind_some, tabEval_pure, Function.comp] at ih ⊢
        simp only [Option.some.injEq] at ih
        simp [List.all_cons, ih]

/-- **L3a.** Under a fixed hash table `h`, `merkleCheck` accepts iff every tree's reconstructed root (the VCVio
addressed putative root with node digest `h (mkQuery ⟨j, a⟩ (l, r))`) equals the corresponding root. -/
theorem tabEval_merkleCheck (h : Query → Dg) (skels : List BinaryTree.Skeleton)
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress skels) Dg) {Op : Type}
    (decode : Op → OpenAll Dg skels) (roots : List Dg) (op : Op) (hl : roots.length = skels.length) :
    tabEval (spec := Query →ₒ Dg) (fun q => some (h q)) (merkleCheck skels model decode roots op) =
      some ((List.ofFn fun j : Fin skels.length =>
        rootUnder h model (fun a => (⟨j, a⟩ : MAddress skels)) (OpenAll.get skels (decode op) j) ==
          roots.get (j.cast hl.symm)).all id) := by
  unfold merkleCheck
  rw [dif_pos hl, tabEval_claims]
  rw [Option.some.injEq]
  simp only [mkClaims, mconfig]
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true, List.mem_ofFn]

end L3a

/-! ## L2: per-round codecs and the flat reading of the FS table -/

section L2

variable {Input : Type}

/-- Flat codec of one round: message encoding (injective), challenge encoding/decoding. -/
structure RCodec (r : Round) where
  encM : r.Message → List ℕ
  encC : r.Challenge → List ℕ
  decC : List ℕ → r.Challenge
  decC_encC : ∀ c, decC (encC c) = c
  encM_inj : Function.Injective encM

/-- codecs of a round list -/
def Codecs : List Round → Type
  | [] => Unit
  | r :: rs => RCodec r × Codecs rs

/-- the key as (statement encoding, messages `m_1 … m_i`) -/
def encKeyP (encZ : Input → List ℕ) : (rounds : List Round) → Codecs rounds →
    Key Input PUnit rounds → List ℕ × List (List ℕ)
  | [], _, k => nomatch k
  | _ :: _, (c, _), .inl (z, m, _) => (encZ z, [c.encM m])
  | _ :: rs, (c, cs), .inr (m, _, k) =>
      ((encKeyP encZ rs cs k).1, c.encM m :: (encKeyP encZ rs cs k).2)

/-- the flat key the verifier hands to the FS oracle: `z :: m_1 :: … :: m_i` -/
def encKey (encZ : Input → List ℕ) (rounds : List Round) (cs : Codecs rounds) (k : Key Input PUnit rounds) :
    List (List ℕ) := (encKeyP encZ rounds cs k).1 :: (encKeyP encZ rounds cs k).2

theorem encKeyP_len : (rounds : List Round) → (cs : Codecs rounds) → (encZ : Input → List ℕ) →
    (k : Key Input PUnit rounds) → 1 ≤ (encKeyP encZ rounds cs k).2.length
  | [], _, _, k => nomatch k
  | _ :: _, (c, _), _, .inl _ => by simp [encKeyP]
  | _ :: rs, (c, cs), encZ, .inr (m, _, k) => by simp [encKeyP]

/-- challenge encoding / decoding at the round of a key -/
def encChal : (rounds : List Round) → Codecs rounds → (k : Key Input PUnit rounds) → k.Challenge → List ℕ
  | [], _, k => nomatch k
  | _ :: _, (c, _), .inl _ => c.encC
  | _ :: rs, (_, cs), .inr (_, _, k) => encChal rs cs k

def decChal : (rounds : List Round) → Codecs rounds → (k : Key Input PUnit rounds) → List ℕ → k.Challenge
  | [], _, k => nomatch k
  | _ :: _, (c, _), .inl _ => c.decC
  | _ :: rs, (_, cs), .inr (_, _, k) => decChal rs cs k

theorem decChal_encChal : (rounds : List Round) → (cs : Codecs rounds) → (k : Key Input PUnit rounds) →
    (c : k.Challenge) → decChal rounds cs k (encChal rounds cs k c) = c
  | [], _, k, _ => nomatch k
  | _ :: _, (cd, _), .inl _, c => cd.decC_encC c
  | _ :: rs, (_, cs), .inr (_, _, k), c => decChal_encChal rs cs k c

theorem encKeyP_injective (encZ : Input → List ℕ) (hz : Function.Injective encZ) :
    (rounds : List Round) → (cs : Codecs rounds) → Function.Injective (encKeyP encZ rounds cs)
  | [], _, k, _, _ => nomatch k
  | r :: rs, (c, cs), .inl (z, m, ⟨⟩), .inl (z', m', ⟨⟩), h => by
      simp only [encKeyP, Prod.mk.injEq, List.cons.injEq, and_true] at h
      rw [hz h.1, c.encM_inj h.2]
  | r :: rs, (c, cs), .inl (z, m, ⟨⟩), .inr (m', ⟨⟩, k'), h => by
      have := encKeyP_len rs cs encZ k'
      have h2 := congrArg (fun p => p.2.length) h
      simp only [encKeyP, List.length_cons, List.length_nil] at h2
      omega
  | r :: rs, (c, cs), .inr (m, ⟨⟩, k), .inl (z', m', ⟨⟩), h => by
      have := encKeyP_len rs cs encZ k
      have h2 := congrArg (fun p => p.2.length) h
      simp only [encKeyP, List.length_cons, List.length_nil] at h2
      omega
  | r :: rs, (c, cs), .inr (m, ⟨⟩, k), .inr (m', ⟨⟩, k'), h => by
      simp only [encKeyP, Prod.mk.injEq, List.cons.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      rw [c.encM_inj h2, encKeyP_injective encZ hz rs cs (Prod.ext h1 h3)]

theorem encKey_injective (encZ : Input → List ℕ) (hz : Function.Injective encZ)
    (rounds : List Round) (cs : Codecs rounds) : Function.Injective (encKey encZ rounds cs) := by
  intro k k' h
  simp only [encKey, List.cons.injEq] at h
  exact encKeyP_injective encZ hz rounds cs (Prod.ext h.1 h.2)

/-- The table's FS half read as a flat oracle on flat keys (`[]` off the image of `encKey`). -/
noncomputable def FSof (encZ : Input → List ℕ) (rounds : List Round) (cs : Codecs rounds)
    (g : (k : Key Input PUnit rounds) → k.Challenge) (x : List (List ℕ)) : List ℕ :=
  open Classical in
  if h : ∃ k, encKey encZ rounds cs k = x then encChal rounds cs h.choose (g h.choose) else []

theorem FSof_key (encZ : Input → List ℕ) (hz : Function.Injective encZ) (rounds : List Round)
    (cs : Codecs rounds) (g : (k : Key Input PUnit rounds) → k.Challenge) (k : Key Input PUnit rounds) :
    FSof encZ rounds cs g (encKey encZ rounds cs k) = encChal rounds cs k (g k) := by
  have h : ∃ k', encKey encZ rounds cs k' = encKey encZ rounds cs k := ⟨k, rfl⟩
  unfold FSof
  rw [dif_pos h]
  have := encKey_injective encZ hz rounds cs h.choose_spec
  rw [this]

/-- the keys the verifier queries, one per round -/
def keysOf (z : Input) : (rounds : List Round) → PublicMessages rounds → List (Key Input PUnit rounds)
  | [], _ => []
  | _ :: rs, (m, ms) => Key.here z m PUnit.unit :: (keysOf z rs ms).map (Key.later m PUnit.unit)

/-- the path of a table (own-rounds version of `pathOfG`) -/
def pathOf (z : Input) : (rounds : List Round) → (g : (k : Key Input PUnit rounds) → k.Challenge) →
    PublicMessages rounds → (protocol rounds).tree.ExecutionPath
  | [], _, _ => PUnit.unit
  | _ :: rs, g, (m, ms) =>
      ⟨m, g (Key.here z m PUnit.unit), pathOf z rs (fun k => g (Key.later m PUnit.unit k)) ms⟩

theorem pathOfG_eq_pathOf {allRounds : List Round} (g : (key : Key Input PUnit allRounds) → key.Challenge) (z : Input) :
    (rounds : List Round) → (ms : PublicMessages rounds) →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    pathOfG g rounds z ms embed preserve =
      pathOf z rounds (fun k => cast (preserve k) (g (embed k))) ms
  | [], _, _, _ => rfl
  | r :: rs, (m, ms), embed, preserve => by
      simp only [pathOfG, pathOf]
      rw [pathOfG_eq_pathOf g z rs ms]
      rfl

/-- the encodings of the challenges of a path -/
def encPath : (rounds : List Round) → Codecs rounds → (protocol rounds).tree.ExecutionPath → List (List ℕ)
  | [], _, _ => []
  | _ :: rs, (c, cs), p => c.encC p.2.1 :: encPath rs cs p.2.2

/-- the encodings of the messages -/
def encMsgs : (rounds : List Round) → Codecs rounds → PublicMessages rounds → List (List ℕ)
  | [], _, _ => []
  | _ :: rs, (c, cs), (m, ms) => c.encM m :: encMsgs rs cs ms

theorem encPath_pathOf (z : Input) : (rounds : List Round) → (cs : Codecs rounds) →
    (g : (k : Key Input PUnit rounds) → k.Challenge) → (ms : PublicMessages rounds) →
    encPath rounds cs (pathOf z rounds g ms) =
      (keysOf z rounds ms).map (fun k => encChal rounds cs k (g k))
  | [], _, _, _ => rfl
  | r :: rs, (c, cs), g, (m, ms) => by
      simp only [encPath, pathOf, keysOf, List.map_cons, List.map_map]
      rw [encPath_pathOf z rs cs (fun k => g (Key.later m PUnit.unit k)) ms]
      rfl

theorem keys_flatP (encZ : Input → List ℕ) (z : Input) : (rounds : List Round) → (cs : Codecs rounds) →
    (ms : PublicMessages rounds) →
    (keysOf z rounds ms).map (encKeyP encZ rounds cs) =
      (List.range rounds.length).map fun i => (encZ z, (encMsgs rounds cs ms).take (i + 1))
  | [], _, _ => rfl
  | r :: rs, (c, cs), (m, ms) => by
      have ih := keys_flatP encZ z rs cs ms
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [keysOf, List.map_cons, List.map_map, encMsgs, List.take_succ_cons, List.take_zero]
      refine congrArg₂ _ (by simp [encKeyP]) ?_
      have h2 : (encKeyP encZ (r :: rs) (c, cs) ∘ Key.later m PUnit.unit) =
          (fun p => (p.1, c.encM m :: p.2)) ∘ encKeyP encZ rs cs := by
        funext k; rfl
      rw [h2, ← List.map_map, ih, List.map_map]
      rfl

theorem keys_flat (encZ : Input → List ℕ) (z : Input) (rounds : List Round) (cs : Codecs rounds)
    (ms : PublicMessages rounds) :
    (keysOf z rounds ms).map (encKey encZ rounds cs) =
      (List.range rounds.length).map fun i => encZ z :: (encMsgs rounds cs ms).take (i + 1) := by
  have h := keys_flatP encZ z rounds cs ms
  have h2 : encKey encZ rounds cs = (fun p : List ℕ × List (List ℕ) => p.1 :: p.2) ∘ encKeyP encZ rounds cs := rfl
  rw [h2, ← List.map_map, h, List.map_map]
  rfl

/-- **L2 (`flat_challenge_eq`).** The challenge encodings the flat verifier recomputes, `FS (z :: m_1 .. m_i)` for each round
`i`, are exactly the encodings of the path's challenges; hence (`decC_encC`) they decode to them. -/
theorem flat_challenge_eq (encZ : Input → List ℕ) (hz : Function.Injective encZ) (rounds : List Round)
    (cs : Codecs rounds) (g : (k : Key Input PUnit rounds) → k.Challenge) (z : Input)
    (ms : PublicMessages rounds) :
    encPath rounds cs (pathOf z rounds g ms) =
      (List.range rounds.length).map fun i =>
        FSof encZ rounds cs g (encZ z :: (encMsgs rounds cs ms).take (i + 1)) := by
  have h1 : ((List.range rounds.length).map fun i =>
        FSof encZ rounds cs g (encZ z :: (encMsgs rounds cs ms).take (i + 1))) =
      ((List.range rounds.length).map fun i => encZ z :: (encMsgs rounds cs ms).take (i + 1)).map
        (FSof encZ rounds cs g) := by rw [List.map_map]; rfl
  rw [h1, ← keys_flat, List.map_map, encPath_pathOf]
  exact List.map_congr_left fun k _ => (FSof_key encZ hz rounds cs g k).symm

end L2

end NockvmE2E.Exec.Emb

open NockvmE2E.Exec.Emb in
#print axioms publicStoppedVerify_trueGuards
open NockvmE2E.Exec.Emb in
#print axioms tabEval_merkleCheck
open NockvmE2E.Exec.Emb in
#print axioms flat_challenge_eq
open NockvmE2E.Exec.Emb in
#print axioms encKey_injective
open NockvmE2E.Exec.Emb in
#print axioms pathOfG_eq_pathOf
