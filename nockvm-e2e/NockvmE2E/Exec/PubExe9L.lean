/-
  NockvmE2E/Exec/PubExe9L.lean   (executed, Mathlib-free, TOTAL)

  The J-9 AL twin of `PE.pubCheck9` over NINE tables (the eight of J-9 A, then the ALU with 18 public limbs = 6 K3 slots: `pubALv = 0`, `pubALs = 2`,
  `pubALx = 4`, two K3 each).  The three changed conjuncts are those of nock `checkPubJ9ALE` (V1J9AL/CheckJ9AL.lean:163-178):
  * hGx : `rho3 + (walkJ8[pubXQ] + jet[2] + alu[pubALx]) = cell[pubHQ]`;
  * hGS : `rhoS + Σ pinCons + Σ pinRg + Σ pinOp + jet[0] + axis[pubAXs] + alu[pubALs] = atom[pubMI] + walkAtom[pubPQ] + split[pubSPs]`
          (`pinRg = (id,1,idx,0,0,0,0,7)`, `pinOp = (id,code,0,0,0,0,0,6)` at challenges `(γH, ρH)`);
  * hsumC' : `alu[pubALv] + Σ claimRecs ++ pinRecs ++ primRecs = cell[0] + atom[pubMB]`, primRec = `claimVec (enc (primToks code)) idx hi lo` at `(γV, ρV)`.
  An unknown op code (`primToks code = none`) rejects.  Absent ALU (`present = false`) reads as zeros (`sliceG`).
-/
import NockvmE2E.Exec.PubExe9
import NockvmE2E.Exec.PrimToks
set_option autoImplicit false

namespace NockvmE2E.Exec.PE
open NockvmE2E.Exec.VF

def pubALv : Nat := 0
def pubALs : Nat := 2
def pubALx : Nat := 4

/-- public limbs of each table (compute, cell, walkJ8, jet, atom, walkAtom, axis, split, alu) -/
def tabLens9L : Array Nat := #[33, 18, 24, 12, 36, 24, 12, 6, 18]

/-- the primitive pin vector `(id, 1, idx, 0, 0, 0, 0, 7)` (ALU keyRg) -/
def pinRgKey (id idx : Nat) : List K6 :=
  [id, 1, idx, 0, 0, 0, 0, 7].map fun v => K6.base (UInt64.ofNat v)
/-- the primitive op record `(id, code, 0, 0, 0, 0, 0, 6)` -/
def pinOpKey (id code : Nat) : List K6 :=
  [id, code, 0, 0, 0, 0, 0, 6].map fun v => K6.base (UInt64.ofNat v)

/-- `checkPubJ9ALE` over frame-ordered coins (`coins.size ≥ 19`) and the nine slices -/
def checkPubEq9L (inp : PubIn) (coins : Array K3) (ps : PubSet9) (al : Array G) : Bool :=
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
  let primRec (q : PrimRec) : Option (List K6) := do
    let e ← enc z y (← primToks q.code)
    pure (claimVec e q.idx q.hi q.lo)
  let r : Option Bool := do
    if coins.size < 19 || x.size < 33 then none else
    let cr ← inp.claimCells.mapM claimRec
    let pr ← inp.pins.mapM pinRec
    let qr ← inp.prims.mapM primRec
    let sClaim := (cr ++ pr ++ qr).foldl (fun s r => K6.add s (compress gv rv r).inv0) K6.zero
    let sPin := inp.pins.foldl (fun s q => K6.add s (compress gh rh (pinConsKey q.key q.idx)).inv0) K6.zero
    let sRg := inp.prims.foldl (fun s q => K6.add s (compress gh rh (pinRgKey q.id q.idx)).inv0) K6.zero
    let sOp := inp.prims.foldl (fun s q => K6.add s (compress gh rh (pinOpKey q.id q.code)).inv0) K6.zero
    let w0 ← pp ps.walkJ8 pubXQ
    let j2 ← pp ps.jet 2
    let ch ← pp ps.cell pubHQ
    let w1 ← pp ps.walkJ8 pubPQ
    let axp ← pp ps.axis pubAXp
    let axs ← pp ps.axis pubAXs
    let sps ← pp ps.split pubSPs
    let alv ← pp al pubALv
    let als ← pp al pubALs
    let alx ← pp al pubALx
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
          K6.add rho3 (K6.add (K6.add w0 j2) alx) == ch &&
          K6.add rho4 axp == w1 &&
          K6.add (K6.add (K6.add (K6.add (K6.add rhoS sPin) (K6.add sRg sOp)) j0) axs) als == K6.add (K6.add aMI v1) sps &&
          K6.add alv sClaim == K6.add c0 aMB &&
          aHQ == K6.add aC v0 &&
          (a0.isZero && a1.isZero) &&
          (c2 == wk0 && c3' == wk1) &&
          (a2 == va0 && a3 == va1))
  r.getD false

def chk9L (inp : PubIn) (co : Array K3) (ps : Array (Array G)) : Bool :=
  checkPubEq9L inp co ⟨ps[0]!, ps[1]!, ps[2]!, ps[3]!, ps[4]!, ps[5]!, ps[6]!, ps[7]!⟩ ps[8]!

/-- the J-9 AL verifier public check: nine tables -/
def pubCheck9L (inp : PubIn) (L : PubLayout) (slotOf : Array Nat) : Array K3 → Array G → Bool :=
  pubCheckG 9 tabLens9L chk9L inp L slotOf

end NockvmE2E.Exec.PE
