/-
  NockvmE2E/Exec/PubExe9.lean   (executed, Mathlib-free, TOTAL)

  The J-9 A twin of `PE.checkPubEq` / `PE.pubCheck` over EIGHT tables (compute, cell, walkJ8, jet, atom, walkAtom, axis, split),
  public lengths `33, 18, 24, 12, 36, 24, 12, 6` (= `famJ9A` / `pubLens9A`; axis 4 K-slots `pubAXs=0, pubAXp=2`, split 2 K-slots `pubSPs=0`).
  Differences from J-8 (nock `PubEq9A`, InstJ9A.lean:310): conjunct 1 `rho4 + axis[pubAXp] = walkJ8[pubPQ]`, conjunct 2 adds the axis
  service `axis[pubAXs]` on the left and the split terminal `split[pubSPs]` on the right.  Claim records, big-atom branch and the
  coin-derived compute publics are those of `PE` (`claimRec` already has the J-9 big branch, kind 2, rank (0,0)).
  Absent axis / split tables (`L.present = false`) read as zeros.
-/
import NockvmE2E.Exec.PubExeG
set_option autoImplicit false

namespace NockvmE2E.Exec.PE
open NockvmE2E.Exec.VF

structure PubSet9 where
  compute : Array G
  cell : Array G
  walkJ8 : Array G
  jet : Array G
  atom : Array G
  walkAtom : Array G
  axis : Array G
  split : Array G

/-- public limbs of each table (compute, cell, walkJ8, jet, atom, walkAtom, axis, split) -/
def tabLens9 : Array Nat := #[33, 18, 24, 12, 36, 24, 12, 6]

def pubAXs : Nat := 0
def pubAXp : Nat := 2
def pubSPs : Nat := 0

/-- `PubEq9A` + the coin-derived compute publics, frame-ordered coins (`coins.size ≥ 19`) -/
def checkPubEq9 (inp : PubIn) (coins : Array K3) (ps : PubSet9) : Bool :=
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
    let axp ← pp ps.axis pubAXp
    let axs ← pp ps.axis pubAXs
    let sps ← pp ps.split pubSPs
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
          K6.add rho4 axp == w1 &&
          K6.add (K6.add (K6.add rhoS sPin) j0) axs == K6.add (K6.add aMI v1) sps &&
          sClaim == K6.add c0 aMB &&
          aHQ == K6.add aC v0 &&
          (a0.isZero && a1.isZero) &&
          (c2 == wk0 && c3' == wk1) &&
          (a2 == va0 && a3 == va1))
  r.getD false

def chk8 (inp : PubIn) (co : Array K3) (ps : Array (Array G)) : Bool :=
  checkPubEq9 inp co ⟨ps[0]!, ps[1]!, ps[2]!, ps[3]!, ps[4]!, ps[5]!, ps[6]!, ps[7]!⟩

/-- the J-9 A verifier public check: eight tables -/
def pubCheck9 (inp : PubIn) (L : PubLayout) (slotOf : Array Nat) : Array K3 → Array G → Bool :=
  pubCheckG 8 tabLens9 chk8 inp L slotOf

/-! ## Executed accept / reject.  The chips-absent J-9 A vector: the J-8 toy1 vector with axis, split slices all zero (axOn = spOn = false). -/

def zeros (n : Nat) : Array G := Array.replicate n 0
def toy9Pubs : Array (Array G) := toy1Pubs ++ #[zeros 12, zeros 6]

def layoutOf9 (ps : Array (Array G)) : PubLayout := ⟨(layoutOf ps).bases, (layoutOf ps).lens, Array.replicate 8 true⟩

def check9 (inp : PubIn) (slots : Array K3) (ps : Array (Array G)) : Bool :=
  pubCheck9 inp (layoutOf9 ps) idSlots slots (concatPubs ps)

/-- balanced nonzero axis/split vector: axis `axs = sps = (1,0,0)` (K-value 0 of axis and split, base value 1 in limb 0), `axp = 0` -/
def toy9On : Array (Array G) :=
  (toy9Pubs.set! 6 ((zeros 12).set! 0 1)).set! 7 ((zeros 6).set! 0 1)

def tweak9 (ps : Array (Array G)) (t j : Nat) : Array (Array G) := tweak ps t j

def pubExe9Selftest : Bool :=
  check9 toy1Claim toy1Slots toy9Pubs &&
  -- axis service alone (unbalanced) rejects; split alone rejects; both balanced accepts
  !check9 toy1Claim toy1Slots (tweak9 toy9Pubs 6 0) &&
  !check9 toy1Claim toy1Slots (tweak9 toy9Pubs 7 0) &&
  check9 toy1Claim toy1Slots toy9On &&
  -- tampering the balanced vector rejects
  !check9 toy1Claim toy1Slots (tweak9 toy9On 6 1) &&
  !check9 toy1Claim toy1Slots (tweak9 toy9On 7 0) &&
  -- axis path slot: unbalanced against walkJ8 pubPQ
  !check9 toy1Claim toy1Slots (tweak9 toy9Pubs 6 6) &&
  !check9 toy1Claim toy1Slots (tweak9 toy9Pubs 6 9) &&
  !check9 toy1Claim toy1Slots (tweak9 toy9Pubs 7 5) &&
  -- the J-8 conjuncts remain: cell pub, compute rhoS, coin, claim
  !check9 toy1Claim toy1Slots (tweak9 toy9Pubs 1 12) &&
  !check9 toy1Claim toy1Slots (tweak9 toy9Pubs 0 27) &&
  !(pubCheck9 toy1Claim (layoutOf9 toy9Pubs) idSlots (toy1Slots.set! 2 (K3.add toy1Slots[2]! K3.one)) (concatPubs toy9Pubs)) &&
  !check9 ⟨[⟨1, [.cell, .atom 1, .atom 1], 0, 0, 1⟩], [], [(0, 0), (2, 0)], [], []⟩ toy1Slots toy9Pubs &&
  -- shape: wrong table count (six tables), wrong axis length, too few slots
  !check9 toy1Claim toy1Slots toy1Pubs &&
  !check9 toy1Claim toy1Slots (toy9Pubs.set! 6 (zeros 11)) &&
  !pubCheck9 toy1Claim (layoutOf9 toy9Pubs) idSlots (toy1Slots.extract 0 18) (concatPubs toy9Pubs) &&
  -- absent axis and split (present = false): zero-filled, same as present zeros
  pubCheck9 toy1Claim ⟨(layoutOf9 toy9Pubs).bases, (layoutOf9 toy9Pubs).lens, #[true, true, true, true, true, true, false, false]⟩ idSlots
    toy1Slots (concatPubs (toy9Pubs.extract 0 6)) &&
  -- big atom claim: an unmatched kind-2 record against a small-atom label rejects
  !check9 ⟨[⟨1, [.atom 18446744069414584321], 0, 0, 1⟩], [], [(0, 0), (2, 0)], [], []⟩ toy1Slots toy9Pubs

/-- the executed J-9 A selftest, kernel-checked -/
theorem pubExe9Selftest_true : pubExe9Selftest = true := by decide +kernel

end NockvmE2E.Exec.PE

#print axioms NockvmE2E.Exec.PE.pubExe9Selftest_true
