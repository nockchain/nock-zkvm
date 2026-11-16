/-
  NockvmE2E/Exec/E2EEmbed.lean   (proof-only)

  The embedding of a flat proof into the audited compiled protocol, in the random-oracle model:
  digests `dgOf/dgFlat`, node-query codec `encQ/decQ` (heap numbering), decode-based flat views `Hof`/`FSdec` of a total
  table, per-round decoders (`RDec`/`MDec`, PARAMETRIC in the clear rounds' message types and in the column layout), the flat
  message list -> `PublicMessages` map `embedMsgs`, the embedded openings (`openAllOf`, empty block = one-leaf opening),
  `goSk_map`, `merkle_embed`, `hsel_embed`.
-/
import NockvmE2E.Exec.Embed
import NockvmE2E.Exec.SoundCover

open BinaryTree InductiveMerkleTree OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.E2E

open NockvmE2E.Merkle NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.Emb


/-- Opened values per column: the verifier's own `V.vTLen`); kept as an alias so callers of `E2E.vTLen` keep working. -/
abbrev vTLen (XI : ExecInst) (c : ℕ) : ℕ := V.vTLen XI c

/-! ## 1. digests -/

/-- the audited digest type at J-8 -/
abbrev DgJ8 : Type := Fin 5 → ZMod NockvmE2E.Exec.p

instance : NeZero NockvmE2E.Exec.p := ⟨(Fact.out : Nat.Prime NockvmE2E.Exec.p).ne_zero⟩

theorem PN_eq : NockvmE2E.Exec.VF.PN = NockvmE2E.Exec.p := by
  unfold NockvmE2E.Exec.VF.PN NockvmE2E.Exec.p; norm_num

/-- a flat digest (5 limbs) as an audited digest (missing limbs read as 0) -/
def dgOf (l : List ℕ) : DgJ8 := fun i => ((l.getD i.1 0 : ℕ) : ZMod NockvmE2E.Exec.p)
/-- an audited digest as 5 canonical limbs -/
def dgFlat (d : DgJ8) : List ℕ := List.ofFn fun i => (d i).val

theorem dgOf_dgFlat (d : DgJ8) : dgOf (dgFlat d) = d := by
  funext i
  fin_cases i <;> simp [dgOf, dgFlat]

theorem dgFlat_length (d : DgJ8) : (dgFlat d).length = 5 := by simp [dgFlat]

theorem dgOk_dgFlat (d : DgJ8) : dgOk (dgFlat d) = true := by
  simp only [dgOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, NockvmE2E.Exec.VF.based, decide_eq_true_eq]
  refine ⟨dgFlat_length d, fun x hx => ?_⟩
  simp only [dgFlat, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [PN_eq]; exact ZMod.val_lt _

theorem dgFlat_dgOf (l : List ℕ) (h : dgOk l = true) : dgFlat (dgOf l) = l := by
  simp only [dgOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, NockvmE2E.Exec.VF.based, decide_eq_true_eq] at h
  obtain ⟨hl, hb⟩ := h
  apply List.ext_getElem (by simp [dgFlat, hl])
  intro i h1 h2
  have h5 : i < 5 := by omega
  simp only [dgFlat, dgOf, List.getElem_ofFn, ZMod.val_natCast, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]
  exact Nat.mod_eq_of_lt (by rw [← PN_eq]; exact hb _ (List.getElem_mem h2))

/-- the all-zero digest (what the flat view answers off the image of the codec) -/
def dgZero : List ℕ := [0, 0, 0, 0, 0]

/-! ## 2. node queries -/

section Heap
open NockvmE2E.Exec.SM

/-- depth and path number of an internal node -/
def sdepth : {s : Skeleton} → SkeletonInternalIndex s → ℕ
  | _, .ofInternal => 0
  | _, .ofLeft a => sdepth a + 1
  | _, .ofRight a => sdepth a + 1

def snum : {s : Skeleton} → SkeletonInternalIndex s → ℕ
  | _, .ofInternal => 0
  | _, .ofLeft a => snum a
  | _, .ofRight a => snum a + 2 ^ sdepth a

theorem snum_lt : ∀ {s : Skeleton} (a : SkeletonInternalIndex s), snum a < 2 ^ sdepth a
  | _, .ofInternal => by simp [snum, sdepth]
  | _, .ofLeft a => by
      have := snum_lt a; simp only [snum, sdepth, pow_succ]; omega
  | _, .ofRight a => by
      have := snum_lt a; simp only [snum, sdepth, pow_succ]; omega

theorem heapIdx_eq : ∀ {s : Skeleton} (a : SkeletonInternalIndex s) (n : ℕ),
    heapIdx a n = n * 2 ^ sdepth a + snum a
  | _, .ofInternal, n => by simp [heapIdx, sdepth, snum]
  | _, .ofLeft a, n => by
      rw [heapIdx, heapIdx_eq a]; simp only [sdepth, snum, pow_succ]; ring
  | _, .ofRight a, n => by
      rw [heapIdx, heapIdx_eq a]; simp only [sdepth, snum, pow_succ]; ring

theorem sdn_inj : ∀ {s : Skeleton} (a b : SkeletonInternalIndex s), sdepth a = sdepth b → snum a = snum b → a = b
  | _, .ofInternal, .ofInternal, _, _ => rfl
  | _, .ofInternal, .ofLeft _, h, _ => by simp [sdepth] at h
  | _, .ofInternal, .ofRight _, h, _ => by simp [sdepth] at h
  | _, .ofLeft _, .ofInternal, h, _ => by simp [sdepth] at h
  | _, .ofRight _, .ofInternal, h, _ => by simp [sdepth] at h
  | _, .ofLeft a, .ofLeft b, h1, h2 => by
      simp only [sdepth, snum, Nat.add_right_cancel_iff] at h1 h2
      rw [sdn_inj a b h1 h2]
  | _, .ofRight a, .ofRight b, h1, h2 => by
      simp only [sdepth, snum, Nat.add_right_cancel_iff] at h1 h2
      rw [h1] at h2
      rw [sdn_inj a b h1 (by omega)]
  | _, .ofLeft a, .ofRight b, h1, h2 => by
      simp only [sdepth, snum, Nat.add_right_cancel_iff] at h1 h2
      have := snum_lt a
      rw [h1] at this; omega
  | _, .ofRight a, .ofLeft b, h1, h2 => by
      simp only [sdepth, snum, Nat.add_right_cancel_iff] at h1 h2
      have := snum_lt b
      rw [← h1] at this; omega

/-- heap numbering (root `1`) is injective on the internal nodes of a skeleton -/
theorem heapIdx_inj {s : Skeleton} (a b : SkeletonInternalIndex s) (h : heapIdx a 1 = heapIdx b 1) : a = b := by
  rw [heapIdx_eq, heapIdx_eq] at h
  simp only [one_mul] at h
  have ha := snum_lt a
  have hb := snum_lt b
  have hd : sdepth a = sdepth b := by
    rcases lt_trichotomy (sdepth a) (sdepth b) with h1 | h1 | h1
    · have : 2 ^ (sdepth a + 1) ≤ 2 ^ sdepth b := Nat.pow_le_pow_right (by omega) h1
      rw [pow_succ] at this; omega
    · exact h1
    · have : 2 ^ (sdepth b + 1) ≤ 2 ^ sdepth a := Nat.pow_le_pow_right (by omega) h1
      rw [pow_succ] at this; omega
  rw [hd] at h
  exact sdn_inj a b hd (by omega)

/-- all internal nodes of a skeleton -/
def allIdx : (s : Skeleton) → List (SkeletonInternalIndex s)
  | .leaf => []
  | .internal l r =>
      SkeletonInternalIndex.ofInternal :: ((allIdx l).map SkeletonInternalIndex.ofLeft ++
        (allIdx r).map SkeletonInternalIndex.ofRight)

theorem mem_allIdx : ∀ {s : Skeleton} (a : SkeletonInternalIndex s), a ∈ allIdx s
  | _, .ofInternal => by simp [allIdx]
  | _, .ofLeft a => by
      simp only [allIdx, List.mem_cons, List.mem_append, List.mem_map]
      exact Or.inr (Or.inl ⟨a, mem_allIdx a, rfl⟩)
  | _, .ofRight a => by
      simp only [allIdx, List.mem_cons, List.mem_append, List.mem_map]
      exact Or.inr (Or.inr ⟨a, mem_allIdx a, rfl⟩)

theorem find_uniq {α : Type} (p : α → Bool) (a : α) (hp : p a = true) (hu : ∀ b, p b = true → b = a) :
    ∀ L : List α, a ∈ L → L.find? p = some a
  | [], h => by simp at h
  | x :: xs, h => by
      by_cases hx : p x = true
      · rw [List.find?_cons_of_pos hx]; simp [hu x hx]
      · have hx' : p x = false := by simpa using hx
        have hne : a ∈ xs := by
          rcases List.mem_cons.mp h with rfl | h
          · exact absurd hp hx
          · exact h
        rw [List.find?_cons_of_neg hx]; exact find_uniq p a hp hu xs hne

variable {skels : List Skeleton}

/-- the node queries of the audited model: address and children -/
abbrev NQuery (skels : List Skeleton) : Type := MAddress skels × (DgJ8 × DgJ8)

/-- the identity node-query model -/
def idModel (skels : List Skeleton) : MerkleTreeExtractability.NodeQueryModel (NQuery skels) (MAddress skels) DgJ8 where
  view := ⟨fun q => q.1, fun q => q.2⟩
  mkQuery a lr := (a, lr)
  address_mkQuery _ _ := rfl
  input_mkQuery _ _ := rfl

/-- flat encoding of a node query: `[tagNode, tree, heap number] ++ left ++ right` -/
def encQ (skels : List Skeleton) : NQuery skels → List ℕ
  | (⟨j, a⟩, (l, r)) => [tagNode, j.1, heapIdx a 1] ++ dgFlat l ++ dgFlat r

/-- its partial inverse -/
def decQ (skels : List Skeleton) : List ℕ → Option (NQuery skels)
  | tag :: j :: i :: rest =>
      if tag = tagNode then
        if hj : j < skels.length then
          ((allIdx (skels.get ⟨j, hj⟩)).find? (fun a => heapIdx a 1 == i)).map
            fun a => ((⟨⟨j, hj⟩, a⟩ : MAddress skels), (dgOf (rest.take 5), dgOf (rest.drop 5)))
        else none
      else none
  | _ => none

theorem decQ_encQ (skels : List Skeleton) (q : NQuery skels) : decQ skels (encQ skels q) = some q := by
  obtain ⟨⟨j, a⟩, l, r⟩ := q
  have hf : (allIdx (skels.get j)).find? (fun b => heapIdx b 1 == heapIdx a 1) = some a :=
    find_uniq _ a (by simp) (fun b hb => heapIdx_inj b a (by simpa using hb)) _ (mem_allIdx a)
  have h1 : (dgFlat l ++ dgFlat r).take 5 = dgFlat l := List.take_left' (dgFlat_length l)
  have h2 : (dgFlat l ++ dgFlat r).drop 5 = dgFlat r := List.drop_left' (dgFlat_length l)
  simp only [encQ, decQ, List.cons_append, List.nil_append, h1, h2, dgOf_dgFlat, hf, j.2]
  rfl

/-- the flat hash oracle of a total table `h` on node queries (zero digest off the image) -/
def Hof (skels : List Skeleton) (h : NQuery skels → DgJ8) (x : List ℕ) : List ℕ :=
  match decQ skels x with
  | some q => dgFlat (h q)
  | none => dgZero

theorem Hof_encQ (skels : List Skeleton) (h : NQuery skels → DgJ8) (q : NQuery skels) :
    Hof skels h (encQ skels q) = dgFlat (h q) := by
  simp [Hof, decQ_encQ]

theorem dgOk_Hof (skels : List Skeleton) (h : NQuery skels → DgJ8) (x : List ℕ) : dgOk (Hof skels h x) = true := by
  unfold Hof; split
  · exact dgOk_dgFlat _
  · decide +kernel

end Heap

/-! ## 3. per-round decoders and the decode-based flat view of the FS table

Nothing here fixes the clear rounds' message types or the column layout: the decoders are parameters. -/

section Dec

/-- challenge codec of a round -/
structure CCodec (r : Round) where
  encC : r.Challenge → List ℕ
  decC : List ℕ → r.Challenge
  decC_encC : ∀ c, decC (encC c) = c

/-- decoder of one round: flat message -> message, plus the challenge codec -/
structure RDec (r : Round) extends CCodec r where
  decM : List ℕ → r.Message

def Decs : List Round → Type
  | [] => Unit
  | r :: rs => RDec r × Decs rs

/-- the messages decoded from the flat message list (missing entries read as `[]`) -/
def decMsgs : (rounds : List Round) → Decs rounds → List (List ℕ) → PublicMessages rounds
  | [], _, _ => PUnit.unit
  | _ :: rs, (d, ds), fm => (d.decM (fm.headD []), decMsgs rs ds fm.tail)

/-- "the messages `ms` are decoded from `fm`, as far as `fm` goes" -/
def MsgsDec : (rounds : List Round) → Decs rounds → List (List ℕ) → PublicMessages rounds → Prop
  | [], _, _, _ => True
  | _ :: rs, (d, ds), fm, (m, ms) => (fm ≠ [] → m = d.decM (fm.headD [])) ∧ MsgsDec rs ds fm.tail ms

theorem decMsgs_dec : (rounds : List Round) → (ds : Decs rounds) → (fm : List (List ℕ)) →
    MsgsDec rounds ds fm (decMsgs rounds ds fm)
  | [], _, _ => trivial
  | _ :: rs, (d, ds), fm => ⟨fun _ => rfl, decMsgs_dec rs ds fm.tail⟩

variable {Input : Type}

/-- the key `z, m_1, .., m_n` decoded from a flat key (`none` when there is no message) -/
def decKeyA (z : Input) : (rounds : List Round) → Decs rounds → List (List ℕ) → Option (Key Input PUnit rounds)
  | [], _, _ => none
  | _ :: _, (d, _), [m] => some (Key.here z (d.decM m) PUnit.unit)
  | _ :: rs, (d, ds), m :: m' :: ms => (decKeyA z rs ds (m' :: ms)).map (Key.later (d.decM m) PUnit.unit)
  | _ :: _, _, [] => none

def encChalD : (rounds : List Round) → Decs rounds → (k : Key Input PUnit rounds) → k.Challenge → List ℕ
  | [], _, k => nomatch k
  | _ :: _, (d, _), .inl _ => d.encC
  | _ :: rs, (_, ds), .inr (_, _, k) => encChalD rs ds k

/-- **the decode-based flat view of the FS table** `g`: parse the flat key, encode the table's answer -/
def FSdec (rounds : List Round) (ds : Decs rounds) (decZ : List ℕ → Input)
    (g : (k : Key Input PUnit rounds) → k.Challenge) (x : List (List ℕ)) : List ℕ :=
  match x with
  | zF :: ms => match decKeyA (decZ zF) rounds ds ms with
      | some k => encChalD rounds ds k (g k)
      | none => []
  | [] => []

def encPathD : (rounds : List Round) → Decs rounds → (protocol rounds).tree.ExecutionPath → List (List ℕ)
  | [], _, _ => []
  | _ :: rs, (d, ds), p => d.encC p.2.1 :: encPathD rs ds p.2.2

theorem encPathD_pathOf (z : Input) : (rounds : List Round) → (ds : Decs rounds) →
    (g : (k : Key Input PUnit rounds) → k.Challenge) → (ms : PublicMessages rounds) →
    encPathD rounds ds (pathOf z rounds g ms) = (keysOf z rounds ms).map (fun k => encChalD rounds ds k (g k))
  | [], _, _, _ => rfl
  | r :: rs, (d, ds), g, (m, ms) => by
      simp only [encPathD, pathOf, keysOf, List.map_cons, List.map_map]
      rw [encPathD_pathOf z rs ds (fun k => g (Key.later m PUnit.unit k)) ms]
      rfl

theorem decKeyA_keysOf (z : Input) : (rounds : List Round) → (ds : Decs rounds) → (fm : List (List ℕ)) →
    (ms : PublicMessages rounds) → MsgsDec rounds ds fm ms → (i : ℕ) → i < fm.length →
    decKeyA z rounds ds (fm.take (i + 1)) = (keysOf z rounds ms)[i]?
  | [], _, fm, _, _, i, hi => by
      simp [decKeyA, keysOf]
  | r :: rs, (d, ds), [], _, _, i, hi => by simp at hi
  | r :: rs, (d, ds), m0 :: fm', (m, ms), ⟨h1, h2⟩, 0, hi => by
      have := h1 (by simp)
      simp only [List.headD_cons] at this
      subst this
      simp [decKeyA, keysOf]
  | r :: rs, (d, ds), m0 :: fm', (m, ms), ⟨h1, h2⟩, i + 1, hi => by
      have hi' : i < fm'.length := by simpa using hi
      have := h1 (by simp)
      simp only [List.headD_cons] at this
      subst this
      have ih := decKeyA_keysOf z rs ds fm' ms h2 i hi'
      have hne : fm'.take (i + 1) ≠ [] := by
        simp only [ne_eq, List.take_eq_nil_iff]; intro h; rcases h with h | h <;> [omega; (subst h; simp at hi')]
      obtain ⟨m1, fm'', hh⟩ := List.exists_cons_of_ne_nil hne
      simp only [List.take_succ_cons, hh, decKeyA]
      rw [hh] at ih
      simp [keysOf, ih, List.getElem?_map]

/-- **`fs_chal_dec`**: the flat view of the table answers, at the flat key of round `i`, the encoding of the path's challenge `i`
(only `decZ ∘ encZ = id` is needed; no injectivity of any message encoding). `ms` need only be decoded from `fm` as far as `fm` goes. -/
theorem fs_chal_dec (encZ : Input → List ℕ) (decZ : List ℕ → Input) (hz : ∀ x, decZ (encZ x) = x)
    (rounds : List Round) (ds : Decs rounds) (g : (k : Key Input PUnit rounds) → k.Challenge) (z : Input)
    (fm : List (List ℕ)) (ms : PublicMessages rounds) (hm : MsgsDec rounds ds fm ms) (i : ℕ) (hi : i < fm.length) :
    (encPathD rounds ds (pathOf z rounds g ms)).getD i [] = FSdec rounds ds decZ g (encZ z :: fm.take (i + 1)) := by
  rw [encPathD_pathOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  dsimp only [FSdec]
  rw [hz, decKeyA_keysOf z rounds ds fm ms hm i hi]
  cases (keysOf z rounds ms)[i]? <;> rfl

end Dec

/-! ## 4. decoders of a masked protocol, `embedMsgs` -/

section Mask

variable {Yd : Type} [Finite Yd] [DecidableEq Yd] (dY : List ℕ → Yd) {Op : Type} [Finite Op] [DecidableEq Op]

/-- decoder data of a mask: a full `RDec` for each clear round, only the challenge codec for each merkle round
(its message is the root, decoded by `dY`) -/
def MDec : MRounds Yd → Type
  | [] => Unit
  | ⟨r, .clear⟩ :: ms => RDec r × MDec ms
  | ⟨r, .merkle _ _ _ _ _⟩ :: ms => CCodec r × MDec ms

/-- the decoder of the opening round: the opening is a constant `ω` (never read from the flat message) -/
def openRDec (ω : Op) : RDec (openingRound Op) where
  encC _ := []
  decC _ := ()
  decC_encC _ := rfl
  decM _ := ω

/-- decoders of the compiled rounds of a mask -/
def mDecs : (ms : MRounds Yd) → MDec ms → Op → Decs (compiledRoundsK Yd Op ms)
  | [], _, ω => (openRDec ω, ())
  | ⟨_, .clear⟩ :: ms, (d, ds), ω => (d, mDecs ms ds ω)
  | ⟨r, .merkle _ _ _ _ _⟩ :: ms, (c, ds), ω => (({ toCCodec := ⟨c.encC, c.decC, c.decC_encC⟩, decM := dY } : RDec (rootRound Yd r)), mDecs ms ds ω)

/-- **`embedMsgs`**: the public messages of the compiled rounds of a mask, decoded from the flat message list
(`fm.[i]` is round `i`'s message; the opening round carries `ω`) -/
def embedMsgs (ms : MRounds Yd) (ds : MDec ms) (ω : Op) (fm : List (List ℕ)) :
    PublicMessages (compiledRoundsK Yd Op ms) :=
  decMsgs _ (mDecs dY ms ds ω) fm

/-- the flat messages of the merkle rounds, in order, as digests -/
def merkleMsgs : (ms : MRounds Yd) → List (List ℕ) → List Yd
  | [], _ => []
  | ⟨_, .clear⟩ :: ms, fm => merkleMsgs ms fm.tail
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, fm => dY (fm.headD []) :: merkleMsgs ms fm.tail

/-- the roots (and the opening) of the path of the embedded messages, for any table -/
theorem pathRootsK_embed {Input : Type} (z : Input) : (ms : MRounds Yd) → (ds : MDec ms) → (ω : Op) →
    (fm : List (List ℕ)) → (g : (k : Key Input PUnit (compiledRoundsK Yd Op ms)) → k.Challenge) →
    pathRootsK Yd Op ms (pathOf z (compiledRoundsK Yd Op ms) g (embedMsgs dY ms ds ω fm)) = (merkleMsgs dY ms fm, ω)
  | [], _, _, _, _ => rfl
  | ⟨_, .clear⟩ :: ms, (d, ds), ω, fm, g =>
      pathRootsK_embed z ms ds ω fm.tail _
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, (c, ds), ω, fm, g => by
      have := pathRootsK_embed z ms ds ω fm.tail (fun k => g (Key.later (dY (fm.headD [])) PUnit.unit k))
      exact congrArg (fun x : List Yd × Op => (dY (fm.headD []) :: x.1, x.2)) this

/-- the opening-round decoder is never reached: a different `ω` changes no earlier message -/
theorem embedMsgs_dec : (ms : MRounds Yd) → (ds : MDec ms) → (ω ω0 : Op) → (fm : List (List ℕ)) →
    fm.length ≤ ms.length →
    MsgsDec _ (mDecs dY ms ds ω0) fm (embedMsgs dY ms ds ω fm)
  | [], _, _, _, fm, hl => by
      have : fm = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst this; exact ⟨fun h => absurd rfl h, trivial⟩
  | ⟨_, .clear⟩ :: ms, (d, ds), ω, ω0, fm, hl =>
      ⟨fun _ => rfl, embedMsgs_dec ms ds ω ω0 fm.tail (by simp at hl ⊢; omega)⟩
  | ⟨_, .merkle _ _ _ _ _⟩ :: ms, (c, ds), ω, ω0, fm, hl =>
      ⟨fun _ => rfl, embedMsgs_dec ms ds ω ω0 fm.tail (by simp at hl ⊢; omega)⟩

/-- appending decoders -/
def mdAppend : (a b : MRounds Yd) → MDec a → MDec b → MDec (a ++ b)
  | [], _, _, db => db
  | ⟨_, .clear⟩ :: a, b, (d, da), db => (d, mdAppend a b da db)
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, (c, da), db => (c, mdAppend a b da db)

theorem merkleMsgs_append : (a b : MRounds Yd) → (fm : List (List ℕ)) →
    merkleMsgs dY (a ++ b) fm = merkleMsgs dY a fm ++ merkleMsgs dY b (fm.drop a.length)
  | [], _, _ => by simp [merkleMsgs]
  | ⟨_, .clear⟩ :: a, b, fm => by
      simp only [List.cons_append, merkleMsgs, merkleMsgs_append a b fm.tail, List.length_cons]
      cases fm <;> simp
  | ⟨_, .merkle _ _ _ _ _⟩ :: a, b, fm => by
      simp only [List.cons_append, merkleMsgs, merkleMsgs_append a b fm.tail, List.length_cons]
      cases fm <;> simp

end Mask

/-! ## 5. embedded openings -/

section Open
open NockvmE2E.Exec.SM

/-- the flat data of one tree's opening, over digests `D`: membership test, leaf digest, frontier, and the committed root `dflt`
(an EMPTY block, one leaf with nothing selected, is opened by the one-leaf opening of `dflt`: zero hash queries) -/
structure FTree (D : Type) where
  isSel : ℕ → Bool
  lv : ℕ → D
  sb : List D
  dflt : D

/-- an opening of every skeleton, with `d` at leaf 0 (only reached for a skeleton that is a single leaf) -/
def junkOpeningD {D : Type} (d : D) : (s : Skeleton) → BatchOpening D s
  | .leaf => ⟨.leaf true, d, .leaf⟩
  | .internal l r =>
      ⟨.internal (junkOpeningD d l).selector (junkOpeningD d r).selector,
        ((junkOpeningD d l).values, (junkOpeningD d r).values),
        .internalBoth (junkOpeningD d l).proof (junkOpeningD d r).proof⟩

/-- `SM.mkOpening` with the junk fallback `dflt` -/
def mkOpeningD {D : Type} (t : FTree D) (s : Skeleton) : BatchOpening D s :=
  match mkProof (selOf t.isSel s 0) t.sb with
  | some (pr, []) => ⟨selOf t.isSel s 0, valsOf t.lv s (selOf t.isSel s 0) 0, pr⟩
  | _ => junkOpeningD t.dflt s

theorem mkOpeningD_eq {D : Type} (t : FTree D) (s : Skeleton) (pr : BatchProof D (selOf t.isSel s 0))
    (h : mkProof (selOf t.isSel s 0) t.sb = some (pr, [])) :
    mkOpeningD t s = ⟨selOf t.isSel s 0, valsOf t.lv s (selOf t.isSel s 0) 0, pr⟩ := by
  unfold mkOpeningD; rw [h]

/-- the empty block: nothing selected on a single leaf, the opening is the one-leaf opening of the root -/
theorem mkOpeningD_leaf {D : Type} (t : FTree D) (h : t.isSel 0 = false) :
    mkOpeningD t .leaf = ⟨.leaf true, t.dflt, .leaf⟩ := by
  have h0 : mkProof (selOf t.isSel .leaf 0) t.sb = none := by show mkProof (LeafData.leaf (t.isSel 0)) t.sb = none; rw [h]; rfl
  unfold mkOpeningD
  split
  · rename_i pr heq; rw [h0] at heq; cases heq
  · rfl

/-- one `BatchOpening` per skeleton, from the flat tree data in order -/
def openAllOf {D : Type} [Inhabited D] : (skels : List Skeleton) → List (FTree D) → OpenAll D skels
  | [], _ => PUnit.unit
  | s :: l, ts =>
      (mkOpeningD (ts.headD ⟨fun _ => false, fun _ => default, [], default⟩) s, openAllOf l ts.tail)

theorem get_openAllOf {D : Type} [Inhabited D] : (skels : List Skeleton) → (ts : List (FTree D)) →
    (j : Fin skels.length) →
    OpenAll.get skels (openAllOf skels ts) j =
      mkOpeningD (ts.getD j.1 ⟨fun _ => false, fun _ => default, [], default⟩) (skels.get j)
  | _ :: _, ts, ⟨0, _⟩ => by cases ts <;> rfl
  | _ :: l, ts, ⟨j + 1, h⟩ => by
      have := get_openAllOf l ts.tail ⟨j, Nat.lt_of_succ_lt_succ h⟩
      show OpenAll.get l (openAllOf l ts.tail) ⟨j, _⟩ = _
      rw [this]; cases ts <;> rfl

/-- `goSk` commutes with a digest map `f` that is compatible with the node hash on the digests satisfying `Ok` -/
theorem goSk_map {D E : Type} (f : D → E) (Ok : D → Prop) (nh : ℕ → D → D → D) (nh' : ℕ → E → E → E)
    (has : ℕ → ℕ → Bool) (isSel : ℕ → Bool) (lv : ℕ → D) (lv' : ℕ → E)
    (hlv : ∀ i, Ok (lv i) ∧ lv' i = f (lv i))
    (hnh : ∀ idx l r, Ok l → Ok r → Ok (nh idx l r) ∧ nh' idx (f l) (f r) = f (nh idx l r)) :
    ∀ (s : Skeleton) (idx lo : ℕ) (sb : List D), (∀ d ∈ sb, Ok d) →
      goSk nh' has isSel lv' s idx lo (sb.map f) =
        (goSk nh has isSel lv s idx lo sb).map (fun x => (f x.1, x.2.map f)) ∧
      ∀ r rest, goSk nh has isSel lv s idx lo sb = some (r, rest) → Ok r ∧ ∀ d ∈ rest, Ok d := by
  intro s
  induction s with
  | leaf =>
      intro idx lo sb hsb
      simp only [goSk]
      by_cases h : isSel lo = true
      · refine ⟨by simp [h, (hlv lo).2], fun r rest hr => ?_⟩
        simp [h] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨(hlv lo).1, hsb⟩
      · simp [h]
  | internal l r ihl ihr =>
      intro idx lo sb hsb
      simp only [goSk]
      rcases hA : has lo (lo + l.leafCount) <;> rcases hB : has (lo + l.leafCount) (lo + l.leafCount + r.leafCount) <;>
        simp only []
      · simp
      · cases sb with
        | nil => simp
        | cons sib sb' =>
          have hs' : ∀ d ∈ sb', Ok d := fun d hd => hsb d (List.mem_cons_of_mem _ hd)
          have hsib : Ok sib := hsb sib (List.mem_cons_self ..)
          obtain ⟨e1, o1⟩ := ihr (2 * idx + 1) (lo + l.leafCount) sb' hs'
          simp only [List.map_cons, e1]
          cases hr : goSk nh has isSel lv r (2 * idx + 1) (lo + l.leafCount) sb' with
          | none => simp
          | some x =>
            obtain ⟨b, s1⟩ := x
            obtain ⟨ob, os⟩ := o1 b s1 hr
            obtain ⟨h1, h2⟩ := hnh idx sib b hsib ob
            refine ⟨by simp [h2], ?_⟩
            intro r' rest hr'
            simp at hr'
            obtain ⟨rfl, rfl⟩ := hr'
            exact ⟨h1, os⟩
      · cases sb with
        | nil => simp
        | cons sib sb' =>
          have hs' : ∀ d ∈ sb', Ok d := fun d hd => hsb d (List.mem_cons_of_mem _ hd)
          have hsib : Ok sib := hsb sib (List.mem_cons_self ..)
          obtain ⟨e1, o1⟩ := ihl (2 * idx) lo sb' hs'
          simp only [List.map_cons, e1]
          cases hr : goSk nh has isSel lv l (2 * idx) lo sb' with
          | none => simp
          | some x =>
            obtain ⟨a, s1⟩ := x
            obtain ⟨oa, os⟩ := o1 a s1 hr
            obtain ⟨h1, h2⟩ := hnh idx a sib oa hsib
            refine ⟨by simp [h2], ?_⟩
            intro r' rest hr'
            simp at hr'
            obtain ⟨rfl, rfl⟩ := hr'
            exact ⟨h1, os⟩
      · obtain ⟨e1, o1⟩ := ihl (2 * idx) lo sb hsb
        cases hr : goSk nh has isSel lv l (2 * idx) lo sb with
        | none => simp [e1, hr]
        | some x =>
          obtain ⟨a, s1⟩ := x
          obtain ⟨oa, os⟩ := o1 a s1 hr
          obtain ⟨e2, o2⟩ := ihr (2 * idx + 1) (lo + l.leafCount) s1 os
          simp only [e1, hr, Option.map_some, Option.bind_some, e2]
          cases hr2 : goSk nh has isSel lv r (2 * idx + 1) (lo + l.leafCount) s1 with
          | none => simp [hr2, e2]
          | some y =>
            obtain ⟨b, s2⟩ := y
            obtain ⟨ob, os2⟩ := o2 b s2 hr2
            obtain ⟨h1, h2⟩ := hnh idx a b oa ob
            refine ⟨by simp [h2, e2, hr2], ?_⟩
            intro r' rest hr'
            simp [hr, hr2] at hr'
            obtain ⟨h3, h4⟩ := hr'
            subst h3 h4
            exact ⟨h1, os2⟩

end Open

/-! ## 6. one embedded tree -/

section Tree
open NockvmE2E.Exec.SM

/-- the audited tree data of a flat tree -/
def ftreeOf (sel : Array ℕ) (leaf : ℕ → Dg5) (sibs : List Dg5) (root : Dg5) : FTree DgJ8 where
  isSel i := sel[lb sel i]? == some i
  lv i := dgOf (leaf (lb sel i))
  sb := sibs.map dgOf
  dflt := dgOf root

/-- **one non-empty tree**: if the flat `goRoot` accepted (consumed all `sibs`, returned `root`), the embedded opening has the dense
selector of the verifier's selection and the audited putative root under the table `h` is `dgOf root`. -/
theorem embed_tree (skels : List Skeleton) (h : NQuery skels → DgJ8) (j : Fin skels.length) (sp : TSpec) (hw : WfSpec sp)
    (hs : skels.get j = skelOf sp sp.total sp.total) (hsp1 : 1 ≤ sp.total) (sel : Array ℕ)
    (hsel : sel.toList.Pairwise (· < ·)) (leaf : ℕ → Dg5) (sibs : Array Dg5) (root : Dg5)
    (hcl : ∀ i, dgOk (leaf i) = true) (hsb : ∀ d ∈ sibs.toList, dgOk d = true)
    (hgo : goRoot (Hof skels h) sp j.1 sel leaf sibs 1 0 sp.total 0 = some (root, sibs.size)) :
    (mkOpeningD (ftreeOf sel leaf sibs.toList root) (skels.get j)).selector =
        selOf (ftreeOf sel leaf sibs.toList root).isSel (skels.get j) 0 ∧
      rootUnder (Query := NQuery skels) h (idModel skels) (fun a => (⟨j, a⟩ : MAddress skels))
        (mkOpeningD (ftreeOf sel leaf sibs.toList root) (skels.get j)) = dgOf root := by
  obtain ⟨_, _, hg⟩ := goRootF_goSk (Hof skels h) sp hw j.1 sel leaf sibs sp.total 1 0 sp.total 0 root sibs.size hsp1
    le_rfl (Nat.zero_le _) hgo
  have hd : List.drop sibs.size sibs.toList = [] := by simp
  rw [List.drop_zero, hd, ← hs] at hg
  obtain ⟨hm1, hm2⟩ := goSk_map dgOf (fun d => dgOk d = true) (fun i l r => Hof skels h ([tagNode, j.1, i] ++ l ++ r))
    (fun i L R => dgOf (Hof skels h ([tagNode, j.1, i] ++ dgFlat L ++ dgFlat R)))
    (fun a b => decide (lb sel a < lb sel b)) (fun i => sel[lb sel i]? == some i) (fun i => leaf (lb sel i))
    (fun i => dgOf (leaf (lb sel i))) (fun i => ⟨hcl _, rfl⟩)
    (fun idx l r hl hr => ⟨dgOk_Hof _ _ _, by simp only [dgFlat_dgOf _ hl, dgFlat_dgOf _ hr]⟩)
    (skels.get j) 1 0 sibs.toList hsb
  rw [hg] at hm1
  simp only [Option.map_some, List.map_nil] at hm1
  obtain ⟨pr, hpr, hroot⟩ := goSk_sound
    (fun i L R => dgOf (Hof skels h ([tagNode, j.1, i] ++ dgFlat L ++ dgFlat R)))
    (fun a b => decide (lb sel a < lb sel b)) (fun i => sel[lb sel i]? == some i)
    (fun i => dgOf (leaf (lb sel i))) (hhas_lb sel hsel) (skels.get j) 1 0 (sibs.toList.map dgOf) (dgOf root) []
    hm1
  have hopen := mkOpeningD_eq (ftreeOf sel leaf sibs.toList root) (skels.get j) pr hpr
  refine ⟨by rw [hopen], ?_⟩
  rw [hopen]
  unfold rootUnder
  rw [← hroot]
  congr 1
  funext a l r
  show h (⟨j, a⟩, (l, r)) = _
  have := Hof_encQ skels h (⟨j, a⟩, (l, r))
  rw [show [tagNode, j.1, heapIdx a 1] ++ dgFlat l ++ dgFlat r = encQ skels (⟨j, a⟩, (l, r)) from rfl, this,
    dgOf_dgFlat]

/-- an EMPTY block (a single-leaf skeleton, nothing selected) is opened by the one-leaf opening of its root: root by `rfl`,
no hash query -/
theorem embed_empty (skels : List Skeleton) (h : NQuery skels → DgJ8) (s : Skeleton) (hs : s = .leaf)
    (key : SkeletonInternalIndex s → MAddress skels) (t : FTree DgJ8) (h0 : t.isSel 0 = false) :
    rootUnder (Query := NQuery skels) h (idModel skels) key (mkOpeningD t s) = t.dflt := by
  subst hs
  rw [mkOpeningD_leaf t h0]
  rfl

end Tree

/-! ## 7. the flat proof's trees, and `merkle_embed` -/

section Flat
open NockvmE2E.Exec.SM NockvmE2E.Exec.Cover

/-- the skeleton of tree `j` as the flat verifier reads it (`MerkleRootOk`) -/
def skelFlat (XI : ExecInst) (j : ℕ) : Skeleton :=
  let sp := if j < 4 then ragSpec (blockLayout XI).1[j]! (2 ^ (XI.nD - 1)) else friSpec (2 ^ (XI.nD - (j - 3)))
  skelOf sp sp.total sp.total

/-- the flat data of tree `j` of a proof: its own selection, leaves, frontier and root -/
def ftree (XI : ExecInst) (π : FlatProof) (j : ℕ) : FTree DgJ8 :=
  ftreeOf ((selsOf XI π)[j]!)
    (fun r => if j < 4 then [(π.vals[j]!)[r]!, 0, 0, 0, 0]
      else [(π.vals[j]!)[3 * r]!, (π.vals[j]!)[3 * r + 1]!, (π.vals[j]!)[3 * r + 2]!, 0, 0])
    (π.sibs[j]!).toList π.roots[j]!

/-- **`embedOpen`** (flat part): the trees of tree-numbers `0 .. 4+k-1` -/
def flatTrees (XI : ExecInst) (π : FlatProof) : List (FTree DgJ8) := (List.range (4 + XI.k)).map (ftree XI π)

theorem ftree_getD (XI : ExecInst) (π : FlatProof) (j : ℕ) (hj : j < 4 + XI.k) :
    (flatTrees XI π).getD j ⟨fun _ => false, fun _ => default, [], default⟩ = ftree XI π j := by
  simp [flatTrees, List.getD_eq_getElem?_getD, List.getElem?_map, hj]

theorem arr_get_lt {a : Array (Array ℕ)} (h : ∀ v ∈ a, ∀ x ∈ v, x < NockvmE2E.Exec.p) (j r : ℕ) :
    (a[j]!)[r]! < NockvmE2E.Exec.p := by
  have hp : 0 < NockvmE2E.Exec.p := (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
  by_cases hj : j < a.size
  · rw [getElem!_pos a j hj]
    by_cases hr : r < a[j].size
    · rw [getElem!_pos a[j] r hr]; exact h _ (Array.getElem_mem hj) _ (Array.getElem_mem hr)
    · rw [getElem!_neg a[j] r hr]; simpa using hp
  · rw [getElem!_neg a j hj]; show (#[] : Array ℕ)[r]! < _; simp [hp]

theorem sibs_ok {XI : ExecInst} {z : List ℕ} {π : FlatProof} (h : allCanon XI z π = true) (j : ℕ) :
    ∀ d ∈ (π.sibs[j]!).toList, dgOk d = true := by
  unfold allCanon at h
  simp only [Bool.and_eq_true] at h
  have hs := h.2
  intro d hd
  by_cases hj : j < π.sibs.size
  · rw [getElem!_pos π.sibs j hj] at hd
    have := (arr_all_iff _ _).mp hs _ (Array.getElem_mem hj)
    exact (arr_all_iff _ _).mp this d (Array.mem_toList_iff.mp hd)
  · rw [getElem!_neg π.sibs j hj] at hd; exact absurd hd (by intro h; exact List.not_mem_nil h)

/-- **`merkle_embed` (per tree)**: for every tree `j` of the audited skeleton list, the embedded opening reconstructs
`dgOf π.roots[j]` under the table's node hash (empty blocks included: by `rfl`, no query). -/
theorem tree_embed (XI : ExecInst) (FS : FSFn) (zF : List ℕ) (π : FlatProof) (skels : List Skeleton)
    (h : NQuery skels → DgJ8) (hok : FlatOk XI (Hof skels h) FS zF π) (hlen : skels.length = 4 + XI.k)
    (hsk : ∀ j (hj : j < skels.length), skels.get ⟨j, hj⟩ = skelFlat XI j) (j : Fin skels.length) :
    rootUnder (Query := NQuery skels) h (idModel skels) (fun a => (⟨j, a⟩ : MAddress skels))
        (OpenAll.get skels (openAllOf skels (flatTrees XI π)) j) = dgOf π.roots[j.1]! ∧
      (¬ (j.1 < 4 ∧ (blockLayout XI).1[j.1]! = 0) →
        (OpenAll.get skels (openAllOf skels (flatTrees XI π)) j).selector =
          selOf (ftree XI π j.1).isSel (skels.get j) 0) := by
  have hj4 : j.1 < 4 + XI.k := hlen ▸ j.2
  rw [get_openAllOf, ftree_getD XI π j.1 hj4]
  by_cases hne : ¬ (j.1 < 4 ∧ (blockLayout XI).1[j.1]! = 0)
  · have hc := flatOk_trees XI (Hof skels h) FS zF π hok j.1 (List.mem_range.mpr hj4)
    obtain ⟨_, hgo⟩ := treeCheck_root XI (Hof skels h) π _ _ _ j.1 hc hne
    have hW : 1 ≤ (blockLayout XI).1[j.1]! ∨ ¬ j.1 < 4 := by
      by_cases h4 : j.1 < 4
      · left; by_contra h1; exact hne ⟨h4, by omega⟩
      · right; exact h4
    have hsp : WfSpec (if j.1 < 4 then ragSpec (blockLayout XI).1[j.1]! (2 ^ (XI.nD - 1))
        else friSpec (2 ^ (XI.nD - (j.1 - 3)))) ∧
        1 ≤ (if j.1 < 4 then ragSpec (blockLayout XI).1[j.1]! (2 ^ (XI.nD - 1))
          else friSpec (2 ^ (XI.nD - (j.1 - 3)))).total := by
      by_cases h4 : j.1 < 4
      · have h1 := hW.resolve_right (by simpa using h4)
        simp only [h4, ite_true]
        refine ⟨wf_ragSpec _ _ h1, ?_⟩
        simp only [ragSpec]
        exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (by omega)) h1
      · simp only [h4, ite_false]
        exact ⟨wf_friSpec _, by simp only [friSpec]; exact Nat.two_pow_pos _⟩
    have hlim := flatOk_limbs XI (Hof skels h) FS zF π hok
    have hcl : ∀ r, dgOk (if j.1 < 4 then [(π.vals[j.1]!)[r]!, 0, 0, 0, 0]
        else [(π.vals[j.1]!)[3 * r]!, (π.vals[j.1]!)[3 * r + 1]!, (π.vals[j.1]!)[3 * r + 2]!, 0, 0]) = true := by
      intro r
      have hb := fun a b => decide_eq_true (arr_get_lt (a := π.vals) (fun v hv x hx => hlim.2.2.2 v hv x hx) a b)
      have hz : NockvmE2E.Exec.VF.based 0 = true := by simp [NockvmE2E.Exec.VF.based, PN_eq]; exact (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
      split <;> simp [dgOk, NockvmE2E.Exec.VF.based, PN_eq, arr_get_lt (a := π.vals) hlim.2.2.2, hz] <;>
        exact (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
    obtain ⟨h1, h2⟩ := embed_tree skels h j _ hsp.1 (hsk j.1 j.2) hsp.2 _ (selsOf_pw XI π j.1 hj4) _ _ _ hcl
      (sibs_ok (flatOk_allCanon XI _ FS zF π hok) j.1) (by simpa using hgo)
    exact ⟨h2, fun _ => h1⟩
  · have hne' : j.1 < 4 ∧ (blockLayout XI).1[j.1]! = 0 := by simpa using hne
    refine ⟨?_, fun h' => absurd hne' h'⟩
    have hsel : (selsOf XI π)[j.1]! = #[] := by
      rw [selsR XI π j.1 hne'.1]; unfold treeSel; simp [Wb, hne'.1, hne'.2]
    have hleaf : skels.get j = .leaf := by
      rw [hsk j.1 j.2]; unfold skelFlat; simp [hne'.1, hne'.2, ragSpec, skelOf]
    refine (embed_empty skels h _ hleaf _ _ ?_).trans ?_
    · simp [ftree, ftreeOf, hsel]
    · rfl

/-- the roots of the flat proof as audited digests, in merkle-round order -/
def rootsOf (π : FlatProof) : List DgJ8 := π.roots.toList.map dgOf

/-- **`merkle_embed`**: under any total hash table `h`, the audited `merkleCheck` (identity model, decode `id`) accepts the embedded
openings against the embedded roots, with ZERO queries on empty blocks. -/
theorem merkle_embed (XI : ExecInst) (FS : FSFn) (zF : List ℕ) (π : FlatProof) (skels : List Skeleton)
    (h : NQuery skels → DgJ8) (hok : FlatOk XI (Hof skels h) FS zF π) (hlen : skels.length = 4 + XI.k)
    (hsk : ∀ j (hj : j < skels.length), skels.get ⟨j, hj⟩ = skelFlat XI j) :
    tabEval (spec := NQuery skels →ₒ DgJ8) (fun q => some (h q))
      (merkleCheck skels (idModel skels) id (rootsOf π) (openAllOf skels (flatTrees XI π))) = some true := by
  have hrs : π.roots.size = 4 + XI.k := by
    obtain ⟨_, _, _, _, h5, _⟩ := hok
    simp only [Bool.and_eq_true, beq_iff_eq] at h5
    exact h5.1.1
  have hl : (rootsOf π).length = skels.length := by simp [rootsOf, hrs, hlen]
  rw [tabEval_merkleCheck h skels (idModel skels) id _ _ hl]
  congr 1
  simp only [List.all_eq_true, List.mem_ofFn, id]
  rintro _ ⟨j, rfl⟩
  have := (tree_embed XI FS zF π skels h hok hlen hsk j).1
  try simp only [id] at this ⊢
  rw [this]
  have hj : j.1 < π.roots.size := by rw [hrs, ← hlen]; exact j.2
  simp [rootsOf, List.getElem_map, getElem!_pos π.roots j.1 hj]
  rfl

end Flat

/-! ## 8. `hsel_embed`, generic part: the selector link of the embedded openings (empty blocks vacuous) -/

section Sel
open NockvmE2E.Exec.SM NockvmE2E.Exec.Cover NockvmE2E.Merkle.MA NockvmE2E.Exec.Layout NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] [SampleableType K]
  {ι Pt F : Type} {colRound : ι → ℕ} [Fintype ι] [DecidableEq ι] [Fintype Pt] [DecidableEq Pt] [Fintype F] [DecidableEq F]
  (md : PointMaskData colRound Pt F DgJ8) (R : RapStatement Φ K ι (Pt → F) colRound) [DecidableEq R.Mfin] [Finite R.Mfin]
  (I : (r : ℕ) → OracleInterface (Cols colRound (Pt → F) r)) (Ifin : OracleInterface R.Mfin)

/-- the RAP blocks `r, r+1, ..`: tree `b` is good for `Q` (it opens every leaf `Q b` marks) or `Q b` marks nothing -/
theorem selR_openAll (Q : ℕ → ℕ → Prop) : (k r : ℕ) → (ts : List (FTree DgJ8)) →
    (∀ b, r ≤ b → b < r + k → ∀ i, Q b (leafNum i) →
      (mkOpeningD (ts.getD (b - r) ⟨fun _ => false, fun _ => default, [], default⟩) (md.skel b)).selector.get i = true) →
    SelR md R I Ifin Q r k (openAllOf _ ts)
  | 0, _, _, _ => trivial
  | k + 1, r, ts, h => ⟨fun i hi => by
        have := h r le_rfl (by omega) i hi
        cases ts <;> simpa using this,
      selR_openAll Q k r.succ ts.tail (fun b hb1 hb2 i hi => by
        have := h b (by omega) (by omega) i hi
        have e : b - r = (b - (r + 1)) + 1 := by omega
        rw [e] at this
        cases ts <;> simpa using this)⟩

end Sel

/-! ## 9. non-vacuity (kernel) -/

example : dgFlat (dgOf [1, 2, 3, 4, 5]) = [1, 2, 3, 4, 5] := dgFlat_dgOf _ (by decide +kernel)
example (d : DgJ8) : dgOf (dgFlat d) = d := dgOf_dgFlat d
/-- the node-query codec round-trips at a concrete address, by evaluation -/
example : (decQ [Skeleton.internal .leaf .leaf]
    (encQ [Skeleton.internal .leaf .leaf]
      (⟨⟨0, by decide⟩, .ofInternal⟩, ((fun _ => 1 : DgJ8), (fun _ => 2 : DgJ8))))).isSome = true := by decide +kernel
/-- the empty-block root is the committed root by `rfl` (no hash query) -/
example (h : NQuery [Skeleton.leaf] → DgJ8) (d : DgJ8) :
    rootUnder (Query := NQuery [Skeleton.leaf]) h (idModel _) (fun a => (⟨⟨0, by decide⟩, a⟩ : MAddress [Skeleton.leaf]))
      (mkOpeningD ⟨fun _ => false, fun _ => d, [], d⟩ Skeleton.leaf) = d := rfl

end NockvmE2E.Exec.E2E

open NockvmE2E.Exec.E2E in
#print axioms decQ_encQ
open NockvmE2E.Exec.E2E in
#print axioms fs_chal_dec
open NockvmE2E.Exec.E2E in
#print axioms pathRootsK_embed
open NockvmE2E.Exec.E2E in
#print axioms goSk_map
open NockvmE2E.Exec.E2E in
#print axioms embed_tree
open NockvmE2E.Exec.E2E in
#print axioms tree_embed
open NockvmE2E.Exec.E2E in
#print axioms merkle_embed
open NockvmE2E.Exec.E2E in
#print axioms selR_openAll
