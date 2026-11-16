/-
  NockvmE2E/Exec/PubExe.lean   (executed, Mathlib-free, TOTAL, no proofs)

  Port of J-8's `checkPubJ8E` (lean-cand `Nock/V1J8/PubExe.lean`, via the Rust twin `nockvm-air/src/pub_eq.rs`) over the verifier's own
  field types `VF.K3` (and `K6 = K3[sqrt 7]` here).  The eight conjuncts of `PubEqJ8`, in `checkPubJ8E` order.

  Entry point: `pubCheck inp L slotOf : Array K3 → Array G → Bool`, to be stored in `ExecInst.pubCheck` (signature of the instance interface):
   * first argument  = the verifier's coin slots (`coins0 ++ coins1 ++ derived`, `Verify.lean` (iv)); frame coin `i` (0..18) is read at
     `slots[slotOf[i]]` (`slotOf` = inverse of the prover's `order`, i.e. the `posOf` of `FlatProver.verifierChip`; identity if the frame
     order is the slot order);
   * second argument = the concatenated per-table publics; table `t`'s slice is `pub[L.bases[t] ..< L.bases[t] + L.lens[t]]`, tables in the
     order compute, cell, walkJ8, jet, atom, walkAtom (Rust `PubSet`).  The compute chip's 33 publics are base values; every other chip's are
     K-values, 3 limbs each (`kv f i = f[3i..3i+3]`), exactly as in `pub_eq.rs`.
   * `PubIn` = instance data the verifier holds: claim cell nouns (with rank halves; serial read from the compute label publics) and the
     registry pins.
  Any out-of-range slice / slot / index, a malformed noun, or a wrong claim label kind gives `false`.
  Difference from the Lean original: nouns are token lists (as in the Rust port, hence also the J-9 big-atom claim branch); the
  `Iff`/spec sections are not ported; `check_compute_derived` of the Rust file (alphaW / seed recomputation, pad, claim atoms) is NOT part of Lean `checkPubJ8E`;  it is ported as `computeDerivedOk`, a ninth conjunct (a lemma `pubCheck = true -> checkPubJ8E` just drops it).
-/
import NockvmE2E.Exec.VField
set_option autoImplicit false

namespace NockvmE2E.Exec.PE
open NockvmE2E.Exec.VF

/-- `K' = K[sqrt 7]`, `re + im sqrt 7` (the Lean `K6`). -/
structure K6 where
  re : K3
  im : K3
  deriving Inhabited, BEq

namespace K6
def zero : K6 := ⟨K3.zero, K3.zero⟩
def one : K6 := ⟨K3.one, K3.zero⟩
def base (x : G) : K6 := ⟨K3.ofG x, K3.zero⟩
def add (a b : K6) : K6 := ⟨K3.add a.re b.re, K3.add a.im b.im⟩
def mul (a b : K6) : K6 :=
  ⟨K3.add (K3.mul a.re b.re) (K3.smul seven (K3.mul a.im b.im)), K3.add (K3.mul a.re b.im) (K3.mul a.im b.re)⟩
/-- `0⁻¹ = 0` (as `K3.inv`). -/
def inv0 (a : K6) : K6 :=
  let n := K3.inv (K3.sub (K3.mul a.re a.re) (K3.smul seven (K3.mul a.im a.im)))
  ⟨K3.mul a.re n, K3.neg (K3.mul a.im n)⟩
end K6

/-! ## Noun fingerprint `E(z, y)` -/

/-- A noun in prefix-token form (`cell` then left then right). -/
inductive Tok where
  | cell : Tok
  | atom : Nat → Tok

structure Fp3 where
  size : K6
  dyck : K6
  leaf : K6

/-- little-endian base-2^32 limbs (fuel-bounded; the fuel is ample) -/
def limbsAux : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n == 0 then [] else (n % 4294967296) :: limbsAux f (n / 4294967296)
def limbs32 (n : Nat) : List Nat := limbsAux (n.log2 / 32 + 2) n

/-- `a0 + y (a1 + y (a2 + ..))` -/
def hornerL (y : K6) : List Nat → K6
  | [] => K6.zero
  | a :: l => K6.add (K6.base (UInt64.ofNat a)) (K6.mul y (hornerL y l))

/-- `leafVal y n`: `n` if `n < p`, else the limb polynomial at `y`. -/
def leafE (y : K6) (n : Nat) : K6 :=
  if n < PN then K6.base (UInt64.ofNat n) else hornerL y (limbs32 n)

def encStep (z zinv y : K6) (st : Option (List Fp3)) (t : Tok) : Option (List Fp3) :=
  match st, t with
  | none, _ => none
  | some s, .atom n => some (⟨z, K6.zero, leafE y n⟩ :: s)
  | some (a :: b :: s), .cell =>
    let s2 := K6.mul a.size a.size
    some (⟨K6.mul a.size b.size,
           K6.add (K6.add (K6.mul z a.dyck) (K6.mul s2 zinv)) (K6.mul s2 b.dyck),
           K6.add a.leaf (K6.mul a.size b.leaf)⟩ :: s)
  | some _, .cell => none

/-- `E(z, y)` of a noun given as prefix tokens (right-to-left stack machine); `none` if malformed. -/
def enc (z y : K6) (toks : List Tok) : Option Fp3 :=
  match toks.reverse.foldl (encStep z z.inv0 y) (some []) with
  | some [e] => some e
  | _ => none

/-- `[size, dyck, leaf, lo + hi sqrt 7, idx]` -/
def claimVec (e : Fp3) (idx hi lo : Nat) : List K6 :=
  [e.size, e.dyck, e.leaf, ⟨K3.ofG (UInt64.ofNat lo), K3.ofG (UInt64.ofNat hi)⟩, K6.base (UInt64.ofNat idx)]

/-- `compress (γ, ρ) v = ρ + Σ γ^c v_c` -/
def compress (g rho : K6) (v : List K6) : K6 :=
  (v.foldl (fun (st : K6 × K6) x => (K6.add st.1 (K6.mul st.2 x), K6.mul st.2 g)) (rho, K6.one)).1

/-! ## Inputs -/

/-- a claim cell noun (`key` = claim position 0/1/2) or a registry pin (`key` = id): noun tokens, serial (ignored for claim cells), rank halves -/
structure NounRec where
  key : Nat
  noun : List Tok
  idx : Nat
  hi : Nat
  lo : Nat

/-- a J-9 AL primitive record: id, ALU op code (`RealIOJ9AL.primCode`), the cell-table index `idxP` and the rank limbs `rkP` of `primC op` -/
structure PrimRec where
  id : Nat
  code : Nat
  idx : Nat
  hi : Nat
  lo : Nat
  deriving Repr, BEq

structure PubIn where
  claimCells : List NounRec
  pins : List NounRec
  /-- claim positions that are plain atoms: `(k, value)` (`compute[2k] = 0`, `compute[2k+1] = value`; Rust `claim_atoms`) -/
  atoms : List (Nat × Nat) := []
  /-- J-9 AL primitive table (`prims`); empty for J-8 / J-9 A (and then not serialised) -/
  prims : List PrimRec := []
  /-- the J chip's call sequence (template ids, one block per call, in order); empty for every family (and then not serialised) -/
  calls : List Nat := []

/-- the six tables' public slices (compute: 33 base values; others: K-values, 3 limbs each) -/
structure PubSet where
  compute : Array G
  cell : Array G
  walkJ8 : Array G
  jet : Array G
  atom : Array G
  walkAtom : Array G

/-- slice layout in the concatenated publics: tables in the order compute, cell, walkJ8, jet, atom, walkAtom -/
structure PubLayout where
  bases : Array Nat
  lens : Array Nat
  /-- `present[t] = false`: the table has no rows (omitted from the proof); its publics are the constant 0 (S4-RESULT step 3) -/
  present : Array Bool := Array.replicate 6 true

/-- number of public limbs of each table (compute, cell, walkJ8, jet, atom, walkAtom) -/
def tabLens : Array Nat := #[33, 18, 24, 12, 36, 24]

/-- PubExe table index of a chip id -/
def tabOfId (id : String) : Option Nat :=
  if id == "computeChipVCLHX" then some 0 else if id == "cellChipHQKW" then some 1 else if id == "walkChipJ8" then some 2
  else if id == "jetChipJ8" then some 3 else if id == "atomChipHQL" then some 4 else if id == "walkChipHQK" then some 5 else none

def kv (f : Array G) (i : Nat) : Option K3 :=
  if 3 * i + 3 ≤ f.size then some ⟨f[3 * i]!, f[3 * i + 1]!, f[3 * i + 2]!⟩ else none
def pp (f : Array G) (i : Nat) : Option K6 := do
  let a ← kv f i
  let b ← kv f (i + 1)
  pure ⟨a, b⟩

def pubHQ : Nat := 4   -- cell `CellHQ.pubHQ`, atom likewise
def pubXQ : Nat := 4
def pubPQ : Nat := 6
def pubMI : Nat := 8
def pubMB : Nat := 6
def pubC : Nat := 10

/-- pin-consume key `tlF [2, id, 1, idx]` as eight base values -/
def pinConsKey (id idx : Nat) : List K6 :=
  [id, 1, idx, 0, 0, 0, 0, 2].map fun v => K6.base (UInt64.ofNat v)

/-- The coin-derived compute publics (Rust `check_compute_derived` / Lean `pubVJ8E`, NOT a conjunct of `checkPubJ8E`): K-value 2 = `αW`
(frame coin 13), K-value 3 = seed `αW · Σ_q γW^q lift(label_q)` (`γW` = coin 14), `label` = publics `0..6`; the pad `12..15` and nothing
beyond 33 (`x.size = 33`); the claim atoms against the label. -/
def computeDerivedOk (inp : PubIn) (coins : Array K3) (x : Array G) : Bool :=
  let aw := coins[13]!
  let gw := coins[14]!
  let sum := ((List.range 6).foldl (fun (st : K3 × K3) q => (K3.add st.1 (K3.mul st.2 (K3.ofG x[q]!)), K3.mul st.2 gw)) (K3.zero, K3.one)).1
  let seed := K3.mul aw sum
  x.size == 33 && (⟨x[6]!, x[7]!, x[8]!⟩ : K3) == aw && (⟨x[9]!, x[10]!, x[11]!⟩ : K3) == seed &&
    x[12]! == 0 && x[13]! == 0 && x[14]! == 0 &&
    inp.atoms.all (fun (k, v) => k < 3 && x[2 * k]! == 0 && x[2 * k + 1]! == UInt64.ofNat v)

/-- `checkPubJ8E`, frame-ordered coins (`coins.size ≥ 19`). -/
def checkPubEq (inp : PubIn) (coins : Array K3) (ps : PubSet) : Bool :=
  let coinAt (i : Nat) : K3 := coins[i]!
  let pair (a b : Nat) : K6 := ⟨coinAt a, coinAt b⟩
  let z := pair 2 3
  let y := pair 17 18
  let gh := pair 11 15
  let rh := pair 12 16
  let gv := pair 4 6
  let rv := pair 5 7
  let x := ps.compute
  let c3 (lo : Nat) : K3 := ⟨x[lo]!, x[lo + 1]!, x[lo + 2]!⟩
  let rho3 : K6 := ⟨c3 15, c3 21⟩
  let rho4 : K6 := ⟨c3 18, c3 24⟩
  let rhoS : K6 := ⟨c3 27, c3 30⟩
  let label (j : Nat) : Nat := x[j]!.toNat
  let claimRec (c : NounRec) : Option (List K6) := do
    let big := match c.noun with
      | [.atom n] => decide (n ≥ PN)
      | _ => false
    let kind := if big then 2 else 1
    if c.key > 2 || label (2 * c.key) != kind then none else
    let e ← enc z y c.noun
    pure (claimVec e (label (2 * c.key + 1)) (if big then 0 else c.hi) (if big then 0 else c.lo))
  let pinRec (q : NounRec) : Option (List K6) := do
    let e ← enc z y q.noun
    pure (claimVec e q.idx q.hi q.lo)
  let r : Option Bool := do
    if coins.size < 19 || x.size < 33 then none else
    let cr ← inp.claimCells.mapM claimRec
    let pr ← inp.pins.mapM pinRec
    let sClaim := (cr ++ pr).foldl (fun s r => K6.add s (compress gv rv r).inv0) K6.zero
    let sPin := inp.pins.foldl (fun s q => K6.add s (compress gh rh (pinConsKey q.key q.idx)).inv0) K6.zero
    let w0 ← pp ps.walkJ8 pubXQ
    let j2 ← pp ps.jet 2
    let ch ← pp ps.cell pubHQ
    let w1 ← pp ps.walkJ8 pubPQ
    let j0 ← pp ps.jet 0
    let aMI ← pp ps.atom pubMI
    let v1 ← pp ps.walkAtom pubPQ
    let c0 ← pp ps.cell 0
    let aMB ← pp ps.atom pubMB
    let aHQ ← pp ps.atom pubHQ
    let aC ← pp ps.atom pubC
    let v0 ← pp ps.walkAtom pubXQ
    let a0 ← kv ps.atom 0
    let a1 ← kv ps.atom 1
    let a2 ← kv ps.atom 2
    let a3 ← kv ps.atom 3
    let c2 ← kv ps.cell 2
    let c3' ← kv ps.cell 3
    let wk0 ← kv ps.walkJ8 0
    let wk1 ← kv ps.walkJ8 1
    let va0 ← kv ps.walkAtom 0
    let va1 ← kv ps.walkAtom 1
    pure (computeDerivedOk inp coins x &&
          K6.add rho3 (K6.add w0 j2) == ch &&
          rho4 == w1 &&
          K6.add (K6.add rhoS sPin) j0 == K6.add aMI v1 &&
          sClaim == K6.add c0 aMB &&
          aHQ == K6.add aC v0 &&
          (a0.isZero && a1.isZero) &&
          (c2 == wk0 && c3' == wk1) &&
          (a2 == va0 && a3 == va1))
  r.getD false

/-- the verifier-facing `pubCheck : Array K3 → Array G → Bool` (coin slots, concatenated publics) -/
def pubCheck (inp : PubIn) (L : PubLayout) (slotOf : Array Nat) : Array K3 → Array G → Bool :=
  fun slots pub =>
    let sl (t : Nat) : Array G :=
      if L.present[t]! then pub.extract L.bases[t]! (L.bases[t]! + L.lens[t]!) else Array.replicate L.lens[t]! 0
    let okShape := L.bases.size == 6 && L.lens.size == 6 && L.present.size == 6 && L.lens == tabLens &&
      (List.range 6).all (fun t => !L.present[t]! || L.bases[t]! + L.lens[t]! ≤ pub.size) &&
      slotOf.size ≥ 19 && (List.range 19).all (fun i => slotOf[i]! < slots.size)
    okShape &&
      checkPubEq inp ((List.range 19).toArray.map fun i => slots[slotOf[i]!]!)
        ⟨sl 0, sl 1, sl 2, sl 3, sl 4, sl 5⟩

/-! ## Self-test on the real J-8 toy1 fixture

Data: `nockvm-air/tests/fixtures/emitted/traces/trace-toy1/{coins.json, *.trace.json public_flat}` (the six chips' publics and the 19 frame
coins from the Lean run that produced `pubeq.json` with `check_pub_ok = true`; claim position 1 = `[1 0]`, idx 0, rank (hi 0, lo 1), no pins). -/

/-- toy1 coins (frame order, 3 limbs each, flat) -/
def toy1Coins : Array G := #[3030632083300626929, 12621687930754020383, 18376295826984431726, 13735873168727403526, 15266144396566876934, 5089656088372607341, 15303389253752907778, 1629288447749834759, 18382256154188666749, 12996625924102003392, 11516610897029151394, 1503985089980178109, 10806993408725259798, 17981591565803753990, 6234040392462763318, 10755751544773015801, 15842281129260141825, 10915420003237768794, 10099063599941562202, 13767507936966655681, 4944940155522005032, 15542315276807174799, 16828937529292445907, 17147683428230266622, 13254380772047329492, 12694102926183808077, 14885334358390052848, 15891965834127865352, 10513885209925630328, 12379099042552919021, 7747595814781209573, 80490711109857896, 16875352555167393320, 3547486251154144704, 14930562234987900388, 6731186873704452699, 1631454210838015092, 10657362057340409834, 9802778022178089371, 9369978809102794228, 17785540978558047423, 1958150635707650088, 1466610918243632971, 13051146581928621646, 15336854618463749637, 11886786087877517045, 15460027283664516223, 4499105341767812915, 12314781461217927183, 2473349024650191903, 6677388626566940949, 5273385574918961237, 11294436758048491751, 5056676044081306922, 7823996169395911220, 1795278204622611363, 6315528322655581532]
def toy1PubCompute : Array G := #[0, 0, 1, 0, 0, 0, 9369978809102794228, 17785540978558047423, 1958150635707650088, 2241539311126473126, 15042455378703216410, 14529763099955853251, 0, 0, 0, 3562629925021956140, 8441995867279620852, 9652578797319299241, 0, 0, 0, 13893204388980020161, 9276798996503284993, 8515237293990254256, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def toy1PubCell : Array G := #[12299689115366496763, 7643473421489086167, 2677094934827029750, 6285531058894964169, 14560871594354725418, 4128345785025600890, 12329491478037837136, 11504856170394024326, 2387398862114844041, 16247951437384130519, 11246197425391964491, 4345450732531950799, 7125259850043912280, 16883991734559241704, 858413525224014161, 9339664708545456001, 106853923591985665, 17030474587980508512]
def toy1PubWalkJ8 : Array G := #[12329491478037837136, 11504856170394024326, 2387398862114844041, 16247951437384130519, 11246197425391964491, 4345450732531950799, 0, 0, 0, 0, 0, 0, 3562629925021956140, 8441995867279620852, 9652578797319299241, 13893204388980020161, 9276798996503284993, 8515237293990254256, 0, 0, 0, 0, 0, 0]
def toy1PubJet : Array G := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def toy1PubAtom : Array G := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def toy1PubWalkAtom : Array G := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def toy1Slots : Array K3 :=
  (List.range 19).toArray.map fun i => ⟨toy1Coins[3 * i]!, toy1Coins[3 * i + 1]!, toy1Coins[3 * i + 2]!⟩
def toy1Pubs : Array (Array G) := #[toy1PubCompute, toy1PubCell, toy1PubWalkJ8, toy1PubJet, toy1PubAtom, toy1PubWalkAtom]
def toy1Claim : PubIn :=
  ⟨[⟨1, [.cell, .atom 1, .atom 0], 0, 0, 1⟩], [], [(0, 0), (2, 0)], [], []⟩
def layoutOf (ps : Array (Array G)) : PubLayout :=
  ⟨(ps.foldl (fun (st : Array Nat × Nat) a => (st.1.push st.2, st.2 + a.size)) (#[], 0)).1, ps.map (·.size), Array.replicate 6 true⟩
def concatPubs (ps : Array (Array G)) : Array G := ps.foldl (· ++ ·) #[]
def idSlots : Array Nat := (List.range 19).toArray

def checkWith (inp : PubIn) (slots : Array K3) (ps : Array (Array G)) : Bool :=
  pubCheck inp (layoutOf ps) idSlots slots (concatPubs ps)

/-- change limb `j` of table `t` -/
def tweak (ps : Array (Array G)) (t j : Nat) : Array (Array G) :=
  ps.set! t (ps[t]!.set! j (ps[t]![j]! + 1))

/-- honest accepts; each dishonest variant (a public of every conjunct, a coin, the claim, a shape error) rejects -/
def pubExeSelftest : Bool :=
  checkWith toy1Claim toy1Slots toy1Pubs &&
  -- slot permutation: slots reversed, slotOf = inverse
  pubCheck toy1Claim (layoutOf toy1Pubs) ((List.range 19).toArray.map (18 - ·)) toy1Slots.reverse (concatPubs toy1Pubs) &&
  -- c0 / c1 / c2 / c3 / c4 publics, c5 (atom pub 0), c6 (cell pub 2), c7 (atom pub 2)
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 1 12) &&       -- cell pubHQ: conjunct 0
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 2 18) &&       -- walkJ8 pubPQ: conjunct 1
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 0 27) &&       -- compute rhoS: conjunct 2
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 1 0) &&        -- cell pub 0: conjunct 3
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 4 30) &&       -- atom pubC: conjunct 4
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 4 0) &&        -- atom pub 0 nonzero: conjunct 5
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 1 6) &&        -- cell pub 2 vs walk pub 0: conjunct 6
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 5 0) &&        -- walkAtom pub 0 vs atom pub 2: conjunct 7
  -- a coin (z1)
  !(pubCheck toy1Claim (layoutOf toy1Pubs) idSlots (toy1Slots.set! 2 (K3.add toy1Slots[2]! K3.one)) (concatPubs toy1Pubs)) &&
  -- wrong claim: rank half, noun, serial label
  !checkWith ⟨[⟨1, [.cell, .atom 1, .atom 0], 0, 0, 2⟩], [], [(0, 0), (2, 0)], [], []⟩ toy1Slots toy1Pubs &&
  !checkWith ⟨[⟨1, [.cell, .atom 1, .atom 1], 0, 0, 1⟩], [], [(0, 0), (2, 0)], [], []⟩ toy1Slots toy1Pubs &&
  !checkWith ⟨[⟨1, [.cell, .atom 1], 0, 0, 1⟩], [], [(0, 0), (2, 0)], [], []⟩ toy1Slots toy1Pubs &&
  !checkWith ⟨[⟨0, [.cell, .atom 1, .atom 0], 0, 0, 1⟩], [], [(0, 0), (2, 0)], [], []⟩ toy1Slots toy1Pubs &&
  -- a spurious pin changes conjunct 2/3
  !checkWith ⟨[⟨1, [.cell, .atom 1, .atom 0], 0, 0, 1⟩], [⟨5, [.atom 7], 3, 0, 0⟩], [(0, 0), (2, 0)], [], []⟩ toy1Slots toy1Pubs &&
  -- shape: layout out of range, too few slots
  !pubCheck toy1Claim ⟨(layoutOf toy1Pubs).bases, (layoutOf toy1Pubs).lens.set! 5 99, Array.replicate 6 true⟩ idSlots toy1Slots (concatPubs toy1Pubs) &&
  !pubCheck toy1Claim (layoutOf toy1Pubs) idSlots (toy1Slots.extract 0 18) (concatPubs toy1Pubs) &&
  -- derived compute publics (alphaW limb, seed limb, pad, a claim atom) are pinned too
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 0 6) &&
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 0 9) &&
  !checkWith toy1Claim toy1Slots (tweak toy1Pubs 0 13) &&
  !checkWith ⟨[⟨1, [.cell, .atom 1, .atom 0], 0, 0, 1⟩], [], [(0, 0), (2, 5)], [], []⟩ toy1Slots toy1Pubs &&
  -- an absent table (walkAtom, all-zero publics) is the same as 24 zeros present
  pubCheck toy1Claim ⟨(layoutOf toy1Pubs).bases, (layoutOf toy1Pubs).lens, #[true, true, true, true, true, false]⟩ idSlots toy1Slots
    (concatPubs (toy1Pubs.extract 0 5))

end NockvmE2E.Exec.PE
