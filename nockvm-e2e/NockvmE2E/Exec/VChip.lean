/-
  NockvmE2E/Exec/VChip.lean   (Mathlib-free, pure)

  The pure (structural, total) twin of `FlatProver.verifierChip` (FlatProver.lean): the verifier's chip = the emitted chip with the coin slots renumbered
  to `after0 ++ after1` and the gamma'-power derived slots expanded to DAG nodes over the coins.  `FlatProver.verifierChip` now calls `verifierChipT`
  (option (a)), so the chip JSON the prover writes IS `verifierChipT` of the emitted chip; the semantics (`DagSemV.evalDagK_verifierChipT`) is proved there.
  Pieces are separate defs so that the proofs can name them.
-/
import NockvmE2E.Exec.AuxFill
set_option autoImplicit false

namespace NockvmE2E.Exec.VC
open NockvmE2E.Exec.Tr NockvmE2E.Exec.Aux

/-- renumber coins by `f`, shift `.ref` by `shift` (structural twin of the `partial` `FlatProver.mapEx`) -/
def mapExT (f : Nat → Ex) (shift : Nat) : Ex → Ex
  | .chal i => f i
  | .ref i => .ref (i + shift)
  | .add a b => .add (mapExT f shift a) (mapExT f shift b)
  | .sub a b => .sub (mapExT f shift a) (mapExT f shift b)
  | .mul a b => .mul (mapExT f shift a) (mapExT f shift b)
  | .neg a => .neg (mapExT f shift a)
  | .pow a n => .pow (mapExT f shift a) n
  | .var k i => .var k i
  | .cF v => .cF v
  | .extVar k e => .extVar k e

/-- the verifier's slot order: round-0 coins, then the later ones -/
def orderOf (coinMeta : Array (Nat × Nat)) : Array Nat :=
  (coinMeta.filter (·.2 == 0)).map (·.1) ++ (coinMeta.filter (·.2 != 0)).map (·.1)

/-- the distinct (re, im) coin pairs of the derived slots, in first-occurrence order -/
def pairsOf (ders : Array Der) : Array (Nat × Nat) :=
  ders.foldl (fun (acc : Array (Nat × Nat)) d => if acc.contains (d.re, d.im) then acc else acc.push (d.re, d.im)) #[]

/-- the largest power asked of the pair (re, im) -/
def mpOf (ders : Array Der) (re im : Nat) : Nat :=
  ders.foldl (fun m d => if d.re == re && d.im == im then max m d.power else m) 0

/-- the nodes `(1,0), γ'^1, …, γ'^mp` of one pair (`rp`, `ip` = verifier slots of the re/im coins), absolute refs from `base` -/
def dblock (rp ip base : Nat) : Nat → Array Ex
  | 0 => #[.cF 1, .cF 0]
  | p + 1 =>
    dblock rp ip base p ++
      #[.add (.mul (.ref (base + 2 * p)) (.chal rp)) (.mul (.cF 7) (.mul (.ref (base + 2 * p + 1)) (.chal ip))),
        .add (.mul (.ref (base + 2 * p)) (.chal ip)) (.mul (.ref (base + 2 * p + 1)) (.chal rp))]

/-- one pair's block appended to the derived nodes; `seen` records `(re, im, base, mp)` -/
def dnStep (ders : Array Der) (coinMeta : Array (Nat × Nat)) (st : Array Ex × Array (Nat × Nat × Nat × Nat)) (p : Nat × Nat) :
    Array Ex × Array (Nat × Nat × Nat × Nat) :=
  let mp := mpOf ders p.1 p.2
  let rp := ((orderOf coinMeta).findIdx? (· == p.1)).getD 0
  let ip := ((orderOf coinMeta).findIdx? (· == p.2)).getD 0
  (st.1 ++ dblock rp ip st.1.size mp, st.2.push (p.1, p.2, st.1.size, mp))

/-- the derived nodes and `seen = (re, im, base, mp)` per pair -/
def dnSeen (ders : Array Der) (coinMeta : Array (Nat × Nat)) : Array Ex × Array (Nat × Nat × Nat × Nat) :=
  (pairsOf ders).foldl (dnStep ders coinMeta) (#[], #[])

/-- `(slot, node index)` of a derived slot (`none` only if its pair is not in `seen`, which never happens) -/
def drefEntry (seen : Array (Nat × Nat × Nat × Nat)) (d : Der) : Option (Nat × Nat) :=
  (seen.find? (fun s => s.1 == d.re && s.2.1 == d.im)).map fun s =>
    (d.slot, s.2.2.1 + 2 * d.power + (if d.isRe then 0 else 1))

/-- `(slot, node index)` of every derived slot -/
def drefOf (ders : Array Der) (seen : Array (Nat × Nat × Nat × Nat)) : Array (Nat × Nat) :=
  ders.filterMap (drefEntry seen)

/-- the coin renumbering of the verifier chip: coin → its slot; derived slot → its node; anything else → the `.chal 63` fallback -/
def fOf (order : Array Nat) (dref : Array (Nat × Nat)) (i : Nat) : Ex :=
  match order.findIdx? (· == i) with
  | some p => .chal p
  | none => match dref.find? (·.1 == i) with
    | some (_, r) => .ref r
    | none => .chal 63

/-- The verifier's chip (pure).  Returns the chip and the max degree. -/
def verifierChipT (ch : Chip) (ders : Array Der) (coinMeta : Array (Nat × Nat)) : Chip × Nat :=
  let dnS := dnSeen ders coinMeta
  let f := fOf (orderOf coinMeta) (drefOf ders dnS.2)
  let m := dnS.1.size
  let cons := ch.cons.map fun c => { c with e := mapExT f m c.e }
  let dmax := cons.foldl (fun a c => max a c.deg) 1
  ({ ch with shared := dnS.1 ++ ch.shared.map (mapExT f m), cons := cons, sharedK := #[], consK := #[] }, dmax)

/-- structural equality of expressions (`Ex` derives only `Inhabited`) -/
def exEqB : Ex → Ex → Bool
  | .var k i, .var k' i' => k == k' && i == i'
  | .cF v, .cF v' => v == v'
  | .add a b, .add a' b' => exEqB a a' && exEqB b b'
  | .sub a b, .sub a' b' => exEqB a a' && exEqB b b'
  | .mul a b, .mul a' b' => exEqB a a' && exEqB b b'
  | .neg a, .neg a' => exEqB a a'
  | .pow a n, .pow a' n' => exEqB a a' && n == n'
  | .extVar k e, .extVar k' e' => k == k' && e == e'
  | .chal i, .chal i' => i == i'
  | .ref i, .ref i' => i == i'
  | _, _ => false

theorem exEqB_iff (a b : Ex) : exEqB a b = true ↔ a = b := by
  induction a generalizing b <;> cases b <;> simp_all [exEqB]

end NockvmE2E.Exec.VC
