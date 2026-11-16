/-
  NockvmE2E/Exec/VerifyMain.lean   (executed, Mathlib-free)

  `verifyExe := verifyFlat X tip5H tip5FS` (Tip5 from `Exec/Tip5Core`), the CLI, and a small TEST PROVER for a toy instance
  (|H| = 4 real rows with a preprocessed `isLast` column and a public column, |D| = 2^5, one committed FRI word, 4 queries).
    nockvm-e2e-verify selftest                       -- toy proof: ACCEPT + 3 tampers REJECT (+ JSON round trip)
    nockvm-e2e-verify verify <inst.json> <proof.json> -- proof.json carries "z" (statement limbs) next to the FlatProof fields
  Run under a memory cap.
-/
import NockvmE2E.Exec.Verify
import NockvmE2E.Exec.Tip5Core
import NockvmE2E.Exec.Tip5Fast
import NockvmE2E.Exec.J8ShapeB
import NockvmE2E.Exec.J8ShapeX
import NockvmE2E.Exec.MaskOk
import NockvmE2E.Exec.VerifyOnline
set_option autoImplicit false

namespace NockvmE2E.Exec.V
open Lean NockvmE2E.Exec.VF NockvmE2E.Exec.J

def tip5H : HFn := Tip5Core.hashVarlen
def tip5FS : FSFn := fun key nl =>
  match key with
  | [] => []
  | z :: ms =>
    Tip5Core.squeeze (ms.foldl (fun s m => Tip5Core.absorb s Tip5Core.tMsg m)
      (Tip5Core.absorb (Tip5Core.hashVarlen [Tip5Core.tIni]) Tip5Core.tIn z)) nl
def verifyExe (X : ExecInst) (z : List Nat) (π : FlatProof) : Bool := verifyFlat X tip5H tip5FS z π
def verifyExeE (X : ExecInst) (z : List Nat) (π : FlatProof) : Except String Unit := verifyFlatE X tip5H tip5FS z π

/-! ### toy prover (untrusted test code) -/
section Toy

def padd (a b : Array G) : Array G := (Array.range (max a.size b.size)).map fun i => VF.add (a.getD i 0) (b.getD i 0)
def pneg (a : Array G) : Array G := a.map VF.neg
def pmul (a b : Array G) : Array G := Id.run do
  let mut r : Array G := Array.replicate (a.size + b.size - 1) 0
  for i in [0:a.size] do
    for j in [0:b.size] do
      r := r.modify (i + j) (VF.add · (VF.mul a[i]! b[j]!))
  return r
def peval (p : Array G) (x : G) : G := p.foldr (fun c acc => VF.add (VF.mul acc x) c) 0
def interp (xs ys : Array G) : Array G := Id.run do
  let mut r : Array G := #[0]
  for i in [0:xs.size] do
    let mut basis : Array G := #[1]
    let mut den : G := 1
    for j in [0:xs.size] do
      if j != i then
        basis := pmul basis #[VF.neg xs[j]!, 1]
        den := VF.mul den (VF.sub xs[i]! xs[j]!)
    r := padd r (basis.map (VF.mul (VF.mul ys[i]! (VF.inv den))))
  return r
/-- divide by the monic base polynomial `z` -/
def divMonic (num : Array K3) (z : Array G) : Array K3 × Array K3 := Id.run do
  let zd := z.size - 1
  let mut rem := num
  let mut q : Array K3 := Array.replicate (num.size + 1 - z.size) K3.zero
  for ii in [0:num.size + 1 - z.size] do
    let i := num.size - z.size - ii
    let c := rem[i + zd]!
    q := q.set! i c
    for j in [0:z.size] do
      rem := rem.modify (i + j) fun x => K3.sub x (K3.smul z[j]! c)
  return (q, rem)

partial def fullRoot (H : HFn) (sp : TSpec) (j : Nat) (leaf : Nat → Dg5) (idx lo cnt : Nat) : Dg5 :=
  if cnt == 1 then leaf lo else
  let L := sp.split cnt
  H ([tagNode, j, idx] ++ fullRoot H sp j leaf (2 * idx) lo L ++ fullRoot H sp j leaf (2 * idx + 1) (lo + L) (cnt - L))

/-- frontier digests (pre-order) of the pruned opening of `sel` -/
partial def openGo (H : HFn) (sp : TSpec) (j : Nat) (leaf : Nat → Dg5) (sel : Array Nat) (idx lo cnt : Nat) : Array Dg5 :=
  if cnt == 1 then #[] else
  let L := sp.split cnt
  let a := lb sel lo
  let b := lb sel (lo + L)
  let c := lb sel (lo + cnt)
  if b > a && c > b then openGo H sp j leaf sel (2 * idx) lo L ++ openGo H sp j leaf sel (2 * idx + 1) (lo + L) (cnt - L)
  else if b > a then #[fullRoot H sp j leaf (2 * idx + 1) (lo + L) (cnt - L)] ++ openGo H sp j leaf sel (2 * idx) lo L
  else #[fullRoot H sp j leaf (2 * idx) lo L] ++ openGo H sp j leaf sel (2 * idx + 1) (lo + L) (cnt - L)

def toyH : Array G := (Array.range 4).map fun i => VF.pow (VF.pow (VF.pow 7 (2 ^ 32 - 1)) (2 ^ 30)) i
def toyT : Array G := #[0, 1, 0, 1]
def toyLast : Array G := interp toyH #[0, 0, 0, 1]

/-- columns: c0 = trace bit `t` (block 0), c1 = preprocessed `isLast`, c2 = public `s` (block 2, constant polynomial).
Constraints: `t (t-1)`; `(1 - isLast_cur)(t_next + t_cur - 1)`; `s (s-1)` (public bit). -/
def toyChip : Tr.Chip :=
  let t := Tr.Ex.var 0 0
  let tn := Tr.Ex.var 1 0
  let isl := Tr.Ex.var 0 1
  let s := Tr.Ex.var 2 0
  let one := Tr.Ex.cF 1
  let mk (e : Tr.Ex) : Tr.Con := { kind := 0, round := 0, deg := 2, e := e }
  { id := "toy", shared := #[], colRound := #[0, 0, 0], sharedK := #[], consK := #[false, false, false], baseCols := 3, width := 3,
    cons := #[mk (.mul t (.sub t one)), mk (.mul (.sub one isl) (.add tn (.sub t one))), mk (.mul s (.sub s one))] }

def toyInst : ExecInst :=
  let g32 := VF.pow 7 (2 ^ 32 - 1)
  { nD := 5, dShift := 7, dGen := VF.pow g32 (2 ^ 27), hN := 4, hGen := VF.pow g32 (2 ^ 30), hShift := 1
    r := 2, k := 1, d := 1, l := 4, nc := 3, nq := 3
    colKind := #[0, 1, 2], blockOf := #[0, 0, 2, 3, 3, 3], pre := #[#[], toyLast, #[]], pubOf := #[2]
    ppt := ⟨11, 5, 2⟩, nCoins := #[0, 0], derived := #[],
    tabs := #[{ hN := 4, col0 := 0, nc := 3, npub := 1, pubBase := 0, chip := toyChip }], pubMode := 1, pubTest := fun _ p => p[0]! ≤ 1 }

/-- the honest toy prover; `tamper`: 0 none, 1 corrupt FRI word 1 (all hashes consistent), 2 claim a wrong trace opening `vT[0][0]`. -/
def toyProve (X : ExecInst) (tamper : Nat) (pub0 : G) (z : List Nat) : FlatProof := Id.run do
  let H := tip5H
  let FS := tip5FS
  let nD := X.nD
  let N := 2 ^ nD
  let half0 := N / 2
  let k := X.k
  let (W, _) := blockLayout X
  let mut msgs : Array (List Nat) := #[[], [], [0, 0, 0, 0, 0], [], [], [], [], []]
  let chalAt (ms : Array (List Nat)) (i : Nat) : List Nat := FS (z :: (ms.extract 0 (i + 1)).toList) (roundNl X i)
  let polys : Array (Array G) := #[interp toyH toyT, toyLast, #[pub0]]
  let ptsD : Array G := (Array.range N).map fun i => VF.mul X.dShift (VF.pow X.dGen i)
  let mut lde : Array (Array G) := (polys.map fun p => ptsD.map (peval p)) ++ Array.replicate 3 #[]
  let colsOf (b : Nat) : Array Nat := (Array.range (X.nc + X.nq)).filter fun c => X.blockOf[c]! == b
  let ragLeaf (ld : Array (Array G)) (b : Nat) (p : Nat) : Dg5 :=
    let g := p / (2 * W[b]!)
    let rem := p % (2 * W[b]!)
    let side := rem / W[b]!
    let col := (colsOf b)[rem % W[b]!]!
    [((ld[col]!)[g + side * half0]!).toNat, 0, 0, 0, 0]
  let rootOfBlock (ld : Array (Array G)) (b : Nat) : Dg5 :=
    if W[b]! == 0 then [0, 0, 0, 0, 0] else
    let sp := ragSpec W[b]! half0
    fullRoot H sp b (ragLeaf ld b) 1 0 sp.total
  msgs := msgs.set! 1 (rootOfBlock lde 0) |>.set! 3 (rootOfBlock lde 2)
  let alpha := K3.ofLimbs (chalAt msgs 3)
  -- quotient Q = (C0 + α C1 + α² C2) / Z_H, committed as base columns Q_0, Q_1, Q_2
  let tpoly := interp toyH toyT
  let tnext := (Array.range tpoly.size).map fun i => VF.mul (tpoly.getD i 0) (VF.pow X.hGen i)
  let c0 := pmul tpoly (padd tpoly #[VF.neg 1])
  let c1 := pmul (padd #[1] (pneg toyLast)) (padd (padd tnext tpoly) #[VF.neg 1])
  let c2 := (pmul #[pub0] #[VF.sub pub0 1])
  let n := 8
  let cK : Array K3 := (Array.range n).map fun j =>
    K3.add (K3.ofG (c0.getD j 0))
      (K3.add (K3.smul (c1.getD j 0) alpha) (K3.smul (c2.getD j 0) (K3.mul alpha alpha)))
  let zpoly := toyH.foldl (fun acc h => pmul acc #[VF.neg h, 1]) #[1]
  let (qK, rem) := divMonic cK zpoly
  assert! (rem.all K3.isZero)
  let qt (t : Nat) : Array G := qK.map fun x => if t == 0 then x.c0 else if t == 1 then x.c1 else x.c2
  let qpolys := (Array.range 3).map qt
  for t in [0:3] do lde := lde.set! (3 + t) (ptsD.map (peval (qpolys[t]!)))
  msgs := msgs.set! 4 (rootOfBlock lde 3)
  let zeta := K3.ofLimbs (chalAt msgs 4)
  let omZ := K3.smul X.hGen zeta
  let tv0 := K3.hornerG tpoly zeta
  let vT : Array (Array K3) :=
    #[#[if tamper == 2 then K3.add tv0 K3.one else tv0, K3.hornerG tpoly omZ],
      #[K3.hornerG toyLast zeta, K3.hornerG toyLast omZ], #[K3.ofG pub0]]
  let vQ : Array K3 := qpolys.map fun q => K3.hornerG q zeta
  msgs := msgs.set! 5 (deepMsg vT vQ)
  let cs := K3.ofLimbs (chalAt msgs 6)
  let pts := openPts X zeta
  let ops := openingList X cs vT vQ
  let mut word : Array K3 := (Array.range N).map (deepWord X pts ops fun c idx => (lde[c]!)[idx]!)
  let mut friWords : Array (Array K3) := #[]
  let mut friRoots : Array Dg5 := #[]
  let mut alphaW := K3.ofLimbs (chalAt msgs 7)
  for w in [0:k + 1] do
    let halfw := 2 ^ (nD - w - 1)
    let mut nxt : Array K3 := #[]
    for g in [0:halfw] do
      nxt := nxt.push (foldK3 word[g]! word[g + halfw]! (yAt X w g) alphaW)
    word := nxt
    if w < k then
      if tamper == 1 then word := word.map fun x => K3.add x K3.one
      let wd := word
      let half' := 2 ^ (nD - w - 2)
      let leaf (p : Nat) : Dg5 :=
        let x := wd[p / 2 + (p % 2) * half']!
        x.limbs ++ [0, 0]
      let sp := friSpec (2 ^ (nD - w - 1))
      let root := fullRoot H sp (4 + w) leaf 1 0 sp.total
      friWords := friWords.push wd
      friRoots := friRoots.push root
      msgs := msgs.push root
      alphaW := K3.ofLimbs (chalAt msgs (8 + w))
  let pfinal : Array K3 := #[word[0]!]
  msgs := msgs.push (pfinal.toList.flatMap K3.limbs)
  let pos : Array Nat := (chalAt msgs (8 + k)).toArray.map (· % N)
  let roots : Array Dg5 := #[msgs[1]!, msgs[2]!, msgs[3]!, msgs[4]!] ++ friRoots
  let mut vals : Array (Array Nat) := #[]
  let mut sibs : Array (Array Dg5) := #[]
  for j in [0:4 + k] do
    let sel := treeSel X (W.getD j 0) j pos
    if j < 4 then
      if W[j]! == 0 then
        vals := vals.push #[]; sibs := sibs.push #[]
      else
        let leaf := ragLeaf lde j
        let sp := ragSpec W[j]! half0
        vals := vals.push (sel.map fun p => (leaf p)[0]!)
        sibs := sibs.push (openGo H sp j leaf sel 1 0 sp.total)
    else
      let w := j - 4
      let wd := friWords[w]!
      let half' := 2 ^ (nD - w - 2)
      let leaf (p : Nat) : Dg5 := (wd[p / 2 + (p % 2) * half']!).limbs ++ [0, 0]
      let sp := friSpec (2 ^ (nD - w - 1))
      vals := vals.push (sel.flatMap fun p => (leaf p).take 3 |>.toArray)
      sibs := sibs.push (openGo H sp j leaf sel 1 0 sp.total)
  return { roots := roots, vT := vT, vQ := vQ, pfinal := pfinal, pos := pos, vals := vals, sibs := sibs }

/-- TWO-table toy: table A = `toyChip` on all 4 orbit points, table B = `toyChip` on the FIRST 2 points of the same orbit (`hN_B = 2 < hN = 4`),
so `mult_B = (ζ - h_2)(ζ - h_3)` is non-trivial. Columns: A = 0 (trace), 1 (isLast), 2 (public); B = 3, 4, 5; quotient 6..8. -/
def toyH2 : Array G := toyH.extract 0 2
def toyLastB : Array G := interp toyH2 #[0, 1]

def toyTabA : TabInst := { hN := 4, col0 := 0, nc := 3, npub := 1, pubBase := 0, chip := toyChip }
def toyTabB : TabInst := { hN := 2, col0 := 3, nc := 3, npub := 1, pubBase := 1, chip := toyChip }

def toyInst2 : ExecInst :=
  let g32 := VF.pow 7 (2 ^ 32 - 1)
  { nD := 5, dShift := 7, dGen := VF.pow g32 (2 ^ 27), hN := 4, hGen := VF.pow g32 (2 ^ 30), hShift := 1
    r := 2, k := 1, d := 1, l := 4, nc := 6, nq := 3
    colKind := #[0, 1, 2, 0, 1, 2], blockOf := #[0, 0, 2, 0, 0, 2, 3, 3, 3], pre := #[#[], toyLast, #[], #[], toyLastB, #[]], pubOf := #[2, 5]
    ppt := ⟨11, 5, 2⟩, nCoins := #[0, 0], derived := #[],
    tabs := #[toyTabA, toyTabB],
    pubMode := 1, pubTest := fun _ p => p[0]! ≤ 1 && p[1]! ≤ 1 }

def toyProve2 (X : ExecInst) (tamper : Nat) (pub0 pub1 : G) (z : List Nat) : FlatProof := Id.run do
  let H := tip5H
  let FS := tip5FS
  let nD := X.nD
  let N := 2 ^ nD
  let half0 := N / 2
  let k := X.k
  let (W, _) := blockLayout X
  let mut msgs : Array (List Nat) := #[[], [], [0, 0, 0, 0, 0], [], [], [], [], []]
  let chalAt (ms : Array (List Nat)) (i : Nat) : List Nat := FS (z :: (ms.extract 0 (i + 1)).toList) (roundNl X i)
  let tA := interp toyH toyT
  let tB := interp toyH2 #[0, 1]
  let polys : Array (Array G) := #[tA, toyLast, #[pub0], tB, toyLastB, #[pub1]]
  let ptsD : Array G := (Array.range N).map fun i => VF.mul X.dShift (VF.pow X.dGen i)
  let mut lde : Array (Array G) := (polys.map fun p => ptsD.map (peval p)) ++ Array.replicate 3 #[]
  let colsOf (b : Nat) : Array Nat := (Array.range (X.nc + X.nq)).filter fun c => X.blockOf[c]! == b
  let ragLeaf (ld : Array (Array G)) (b : Nat) (p : Nat) : Dg5 :=
    let g := p / (2 * W[b]!)
    let rem := p % (2 * W[b]!)
    let side := rem / W[b]!
    let col := (colsOf b)[rem % W[b]!]!
    [((ld[col]!)[g + side * half0]!).toNat, 0, 0, 0, 0]
  let rootOfBlock (ld : Array (Array G)) (b : Nat) : Dg5 :=
    if W[b]! == 0 then [0, 0, 0, 0, 0] else
    let sp := ragSpec W[b]! half0
    fullRoot H sp b (ragLeaf ld b) 1 0 sp.total
  msgs := msgs.set! 1 (rootOfBlock lde 0) |>.set! 3 (rootOfBlock lde 2)
  let alpha := K3.ofLimbs (chalAt msgs 3)
  let shiftP (t : Array G) : Array G := (Array.range t.size).map fun i => VF.mul (t.getD i 0) (VF.pow X.hGen i)
  let cons (t last : Array G) (pub : G) : Array (Array G) :=
    #[pmul t (padd t #[VF.neg 1]), pmul (padd #[1] (pneg last)) (padd (padd (shiftP t) t) #[VF.neg 1]), pmul #[pub] #[VF.sub pub 1]]
  let cA := cons tA toyLast pub0
  let multB := (toyH.extract 2 4).foldl (fun acc h => pmul acc #[VF.neg h, 1]) #[1]
  let cB := (cons tB toyLastB pub1).map (pmul multB)
  let n := 8
  let al (j : Nat) : K3 := K3.pow alpha j
  let cK : Array K3 := (Array.range n).map fun j =>
    (List.range 3).foldl (fun acc i => K3.add acc (K3.smul ((cA[i]!).getD j 0) (al i)))
      ((List.range 3).foldl (fun acc i => K3.add acc (K3.smul ((cB[i]!).getD j 0) (al (3 + i)))) K3.zero)
  let zpoly := toyH.foldl (fun acc h => pmul acc #[VF.neg h, 1]) #[1]
  let (qK, rem) := divMonic cK zpoly
  assert! (rem.all K3.isZero)
  let qt (t : Nat) : Array G := qK.map fun x => if t == 0 then x.c0 else if t == 1 then x.c1 else x.c2
  let qpolys := (Array.range 3).map qt
  for t in [0:3] do lde := lde.set! (6 + t) (ptsD.map (peval (qpolys[t]!)))
  msgs := msgs.set! 4 (rootOfBlock lde 3)
  let zeta := K3.ofLimbs (chalAt msgs 4)
  let omZ := K3.smul X.hGen zeta
  let vT : Array (Array K3) :=
    #[#[K3.hornerG tA zeta, K3.hornerG tA omZ], #[K3.hornerG toyLast zeta, K3.hornerG toyLast omZ], #[K3.ofG pub0],
      #[(if tamper == 2 then K3.add (K3.hornerG tB zeta) K3.one else K3.hornerG tB zeta), K3.hornerG tB omZ], #[K3.hornerG toyLastB zeta, K3.hornerG toyLastB omZ], #[K3.ofG pub1]]
  let vQ : Array K3 := qpolys.map fun q => K3.hornerG q zeta
  msgs := msgs.set! 5 (deepMsg vT vQ)
  let cs := K3.ofLimbs (chalAt msgs 6)
  let pts := openPts X zeta
  let ops := openingList X cs vT vQ
  let mut word : Array K3 := (Array.range N).map (deepWord X pts ops fun c idx => (lde[c]!)[idx]!)
  let mut friWords : Array (Array K3) := #[]
  let mut friRoots : Array Dg5 := #[]
  let mut alphaW := K3.ofLimbs (chalAt msgs 7)
  for w in [0:k + 1] do
    let halfw := 2 ^ (nD - w - 1)
    let mut nxt : Array K3 := #[]
    for g in [0:halfw] do
      nxt := nxt.push (foldK3 word[g]! word[g + halfw]! (yAt X w g) alphaW)
    word := nxt
    if w < k then
      let wd := word
      let half' := 2 ^ (nD - w - 2)
      let leaf (p : Nat) : Dg5 := (wd[p / 2 + (p % 2) * half']!).limbs ++ [0, 0]
      let sp := friSpec (2 ^ (nD - w - 1))
      let root := fullRoot H sp (4 + w) leaf 1 0 sp.total
      friWords := friWords.push wd
      friRoots := friRoots.push root
      msgs := msgs.push root
      alphaW := K3.ofLimbs (chalAt msgs (8 + w))
  let pfinal : Array K3 := #[word[0]!]
  msgs := msgs.push (pfinal.toList.flatMap K3.limbs)
  let pos : Array Nat := (chalAt msgs (8 + k)).toArray.map (· % N)
  let roots : Array Dg5 := #[msgs[1]!, msgs[2]!, msgs[3]!, msgs[4]!] ++ friRoots
  let mut vals : Array (Array Nat) := #[]
  let mut sibs : Array (Array Dg5) := #[]
  for j in [0:4 + k] do
    let sel := treeSel X (W.getD j 0) j pos
    if j < 4 then
      if W[j]! == 0 then
        vals := vals.push #[]; sibs := sibs.push #[]
      else
        let leaf := ragLeaf lde j
        let sp := ragSpec W[j]! half0
        vals := vals.push (sel.map fun p => (leaf p)[0]!)
        sibs := sibs.push (openGo H sp j leaf sel 1 0 sp.total)
    else
      let w := j - 4
      let wd := friWords[w]!
      let half' := 2 ^ (nD - w - 2)
      let leaf (p : Nat) : Dg5 := (wd[p / 2 + (p % 2) * half']!).limbs ++ [0, 0]
      let sp := friSpec (2 ^ (nD - w - 1))
      vals := vals.push (sel.flatMap fun p => (leaf p).take 3 |>.toArray)
      sibs := sibs.push (openGo H sp j leaf sel 1 0 sp.total)
  return { roots := roots, vT := vT, vQ := vQ, pfinal := pfinal, pos := pos, vals := vals, sibs := sibs }

end Toy

def report (name : String) (r : Except String Unit) (want : Bool) : IO Bool := do
  let (got, msg) := match r with | .ok _ => (true, "ACCEPT") | .error e => (false, s!"REJECT ({e})")
  IO.println s!"{name}: {msg}  [{if got == want then "as expected" else "UNEXPECTED"}]"
  pure (got == want)

def selfTest : IO Bool := do
  let X := toyInst
  let z : List Nat := [1, 2, 3]
  let π := toyProve X 0 1 z
  let mut ok := true
  ok := (← report "honest toy proof" (verifyExeE X z π) true) && ok
  -- JSON round trip
  match FlatProof.ofJson π.toJson with
  | .ok π' => ok := (← report "after JSON round trip" (verifyExeE X z π') true) && ok
  | .error e => IO.println s!"json: {e}"; ok := false
  -- tamper 1: a Merkle frontier node of tree 0
  let sib0 := π.sibs[0]![0]!
  let bad := π.sibs.set! 0 (π.sibs[0]!.set! 0 ((sib0.head! + 1) :: sib0.tail!))
  ok := (← report "tamper: Merkle node (tree 0 frontier digest)" (verifyExeE X z { π with sibs := bad }) false) && ok
  -- tamper 2: FRI fold value (prover commits a corrupted word 1; hashes and FS stay consistent)
  ok := (← report "tamper: FRI fold value (word 1)" (verifyExeE X z (toyProve X 1 1 z)) false) && ok
  -- tamper 3: DEEP opening (claimed trace value vT[0][0] wrong; hashes and FS consistent)
  ok := (← report "tamper: DEEP opening vT[0][0]" (verifyExeE X z (toyProve X 2 1 z)) false) && ok
  -- B3V-2: preprocessed (kind 1) columns are committed and opened (r values)
  ok := (← report "tamper (B3V): pre coefficient +1 in the instance" (verifyExeE { X with pre := X.pre.set! 1 (X.pre[1]!.modify 0 (· + 1)) } z π) false) && ok
  ok := (← report "tamper (B3V): vT[pre][1] +1 (proof)" (verifyExeE X z { π with vT := π.vT.set! 1 #[π.vT[1]![0]!, K3.add π.vT[1]![1]! K3.one] }) false) && ok
  ok := (← report "tamper (B3V): vT[pre] shape (empty)" (verifyExeE X z { π with vT := π.vT.set! 1 #[] }) false) && ok
  ok := (← report "tamper (B3V): params hShift = 3" (verifyExeE { X with hShift := 3 } z π) false) && ok
  -- extras
  ok := (← report "tamper: opened leaf value (tree 0)" (verifyExeE X z { π with vals := π.vals.set! 0 (π.vals[0]!.set! 0 (π.vals[0]![0]! + 1)) }) false) && ok
  ok := (← report "tamper: wrong statement z" (verifyExeE X [1, 2, 4] π) false) && ok
  ok := (← report "tamper: residual public relation rejects (pubCheck := false)" (verifyExeE { X with pubMode := 1, pubTest := fun _ _ => false } z π) false) && ok
  -- two tables on one orbit (hN_B = 2 < hN = 4): the multiplier mult_B = (ζ - h_2)(ζ - h_3) is exercised
  let X2 := toyInst2
  let π2 := toyProve2 X2 0 1 1 z
  ok := (← report "two-table toy (hN 4 + 2, one orbit): honest" (verifyExeE X2 z π2) true) && ok
  ok := (← report "two-table toy: table B trace opening wrong" (verifyExeE X2 z (toyProve2 X2 2 1 1 z)) false) && ok
  ok := (← report "two-table toy: hN_B claimed 4 (row count of table B)" (verifyExeE { X2 with tabs := #[toyTabA, { toyTabB with hN := 4 }] } z π2) false) && ok
  ok := (← report "two-table toy: hN_B claimed 3" (verifyExeE { X2 with tabs := #[toyTabA, { toyTabB with hN := 3 }] } z π2) false) && ok
  ok := (← report "two-table toy: pubCheck sees table B's public slice (p[1] = 0 demanded, honest 1)" (verifyExeE { X2 with pubMode := 1, pubTest := fun _ p => p[1]! == 0 } z π2) false) && ok
  ok := (← report "two-table toy: pubCheck sees table A's public slice (p[0] = 1 demanded, honest 1)" (verifyExeE { X2 with pubMode := 1, pubTest := fun _ p => p[0]! == 1 && p[1]! == 1 } z π2) true) && ok
  ok := (← report "two-table toy: tables swapped in the instance" (verifyExeE { X2 with tabs := #[toyTabB, toyTabA] } z π2) false) && ok
  -- canonical limbs: a limb `p + v` for `v` the honest value (VF.add is not a field op there) must be rejected, everywhere
  ok := (← report "tamper: non-canonical limb p+1 (vT public value)" (verifyExeE X z { π with vT := π.vT.set! 2 #[⟨1 + P, 0, 0⟩] }) false) && ok
  ok := (← report "tamper: non-canonical limb p+0 (vT public, c1)" (verifyExeE X z { π with vT := π.vT.set! 2 #[⟨1, P, 0⟩] }) false) && ok
  ok := (← report "tamper: non-canonical limb in vQ" (verifyExeE X z { π with vQ := π.vQ.set! 0 ⟨π.vQ[0]!.c0, P, 0⟩ }) false) && ok
  ok := (← report "tamper: non-canonical Merkle digest limb (root 0 + p)" (verifyExeE X z { π with roots := π.roots.set! 0 ((π.roots[0]!.head! + PN) :: π.roots[0]!.tail!) }) false) && ok
  ok := (← report "tamper: non-canonical opened value (tree 0 + p)" (verifyExeE X z { π with vals := π.vals.set! 0 (π.vals[0]!.set! 0 (π.vals[0]![0]! + PN)) }) false) && ok
  ok := (← report "tamper: non-canonical statement limb (z + p)" (verifyExeE X [1 + PN, 2, 3] π) false) && ok
  ok := (← report "tamper: non-canonical instance limb (dShift 7 + p)" (verifyExeE { X with dShift := 7 + P } z π) false) && ok
  ok := (← report "tamper: non-canonical instance limb (ppt c1 = p)" (verifyExeE { X with ppt := ⟨11, P, 2⟩ } z π) false) && ok
  ok := (← report "tamper: non-canonical DAG literal (cF p in a shared node)" (verifyExeE { X with tabs := #[{ toyTabA with chip := { toyChip with shared := #[.cF P] } }] } z π) false) && ok
  ok := (← report "tamper: non-canonical Fiat-Shamir output limb (FS + p)" (verifyFlatE X tip5H (fun key nl => (tip5FS key nl).map (· + PN)) z π) false) && ok
  -- loader: raw numbers >= p (also >= 2^64, which UInt64 would wrap) are rejected before they reach a carrier
  let rj := (FlatProof.ofJson ((π.toJson).setObjVal! "vQ" (Json.arr #[Json.arr #[natJ (2 ^ 64 + 5), natJ 0, natJ 0]]))) 
  ok := (← report "tamper (loader): vQ limb 2^64+5 (would wrap to 5)" (rj.map fun _ => ()) false) && ok
  ok := (← report "tamper (loader): vQ limb p+5" (FlatProof.ofJson ((π.toJson).setObjVal! "vQ" (Json.arr #[Json.arr #[natJ (PN + 5), natJ 0, natJ 0]])) |>.map fun _ => ()) false) && ok
  -- table layout
  ok := (← report "tamper: table layout (hN_t > hN)" (verifyExeE { X with tabs := X.tabs.map fun t => { t with hN := 8 } } z π) false) && ok
  ok := (← report "tamper: table layout (columns do not add up)" (verifyExeE { X with tabs := X.tabs.map fun t => { t with nc := 2 } } z π) false) && ok
  -- instance parameters (`paramsOk`): canonical limbs, so only the params check can reject these
  ok := (← report "tamper: params (dShift = 8, canonical but not 7)" (verifyExeE { X with dShift := 8 } z π) false) && ok
  ok := (← report "tamper: params (nD = 33 > 32)" (verifyExeE { X with nD := 33 } z π) false) && ok
  ok := (← report "tamper: params (dGen = dGen^2, canonical but not the 2^nD-th root)" (verifyExeE { X with dGen := VF.mul X.dGen X.dGen } z π) false) && ok
  ok := (← report "tamper: params (hGen = 1, order 1 < hN)" (verifyExeE { X with hGen := 1 } z π) false) && ok
  -- public instance data (`inpCanOk`): a claim `lo` = p is not a canonical field element
  ok := (← report "tamper: pubIn claim lo = p (non-canonical instance data)" (verifyExeE { X with pubIn := { claimCells := [⟨0, [], 0, 0, PN⟩], pins := [] } } z π) false) && ok
  ok := (← report "pubIn claim lo = p - 1 (canonical)" (verifyExeE { X with pubIn := { claimCells := [⟨0, [], 0, 0, PN - 1⟩], pins := [] } } z π) true) && ok
  pure ok


/-! ### : verifier key, side proof, online verifier -/

/-- the side proof's own Fiat-Shamir oracle: `tip5FS` with a different initial domain tag -/
def tip5FSfix : FSFn := fun key nl =>
  match key with
  | [] => []
  | z :: ms =>
    Tip5Core.squeeze (ms.foldl (fun s m => Tip5Core.absorb s Tip5Core.tMsg m)
      (Tip5Core.absorb (Tip5Core.hashVarlen [Tip5Core.tIni + 0x100]) Tip5Core.tIn z)) nl

/-- `ζ` of the main proof (the verifier's own derivation: challenge of round 4) -/
def mainZeta (FS : FSFn) (z : List Nat) (π : FlatProof) : K3 :=
  K3.ofLimbs (FS (z :: [[], π.roots[0]!, π.roots[1]!, π.roots[2]!, π.roots[3]!]) 3)

def verifyOnlineExe (vk : VK) (z : List Nat) (π : FlatProof) (πF : FixProof) : Except String Unit :=
  verifyOnlineE vk tip5H tip5FS tip5FSfix z π πF

/-- the honest side proof for a main proof `π` of the statement `z` -/
def proveFixExe (D : VKData) (z : List Nat) (π : FlatProof) (tamperVF : Option (Nat × Nat) := none) : FixProof :=
  let zeta := mainZeta tip5FS z π
  proveFix tip5H tip5FSfix D z (fixCtx π zeta) zeta tamperVF

/-- the J-8 gates of the exe (`verify`), part of the VK setup -/
def j8Gates (X : ExecInst) : IO Bool := do
  if X.l != 170 then
    IO.println s!"REJECT: l != 170 (l = {X.l})"; return false
  if !(NockvmE2E.Exec.J8Shape.j8ShapeOk X) then
    IO.println "REJECT: instance is not J-8 shaped"; return false
  if !(NockvmE2E.Exec.J8Shape.j8ShapeXOk X) then
    IO.println "REJECT: instance fails J-8 shape-X check (nq/npub/blockTab/layout)"; return false
  match NockvmE2E.Exec.MaskOk.hop0Check X with
  | .error e => IO.println s!"REJECT: {e}"; return false
  | .ok _ => return true

def vkJson (vk : VK) (instPath : String) : Json :=
  Json.mkObj [("version", natJ 1), ("root", limbsJ vk.root), ("inst", Json.str instPath)]

def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoMsNow
  pure (r, t1 - t0)

/-- toy-level online tests (no J-8 gates): honest + tampers -/
def onlineToyTests (name : String) (X : ExecInst) (z : List Nat) (π : FlatProof) : IO Bool := do
  match setupData X tip5H with
  | none => IO.println s!"{name}: setup REJECTED the instance"; pure false
  | some D =>
    let πF := proveFixExe D z π
    let vk := D.vk
    let mut ok := true
    ok := (← report s!"{name}: online verifier with VK" (verifyOnlineExe vk z π πF) true) && ok
    ok := (← report s!"{name}: tamper vF[0][0] (value flipped after the fact: FS mismatch)" (verifyOnlineExe vk z π { πF with vF := πF.vF.set! 0 (πF.vF[0]!.set! 0 (K3.add πF.vF[0]![0]! K3.one)) }) false) && ok
    let last := πF.vF.size - 1
    ok := (← report s!"{name}: forged vF[0][0] (consistent FS, honest FRI)" (verifyOnlineExe vk z π (proveFixExe D z π (some (0, 0)))) false) && ok
    ok := (← report s!"{name}: forged vF[last][0] (zh or zout; consistent FS)" (verifyOnlineExe vk z π (proveFixExe D z π (some (last, 0)))) false) && ok
    ok := (← report s!"{name}: wrong vk.root" (verifyOnlineExe { vk with root := (vk.root.head! + 1) :: vk.root.tail! } z π πF) false) && ok
    ok := (← report s!"{name}: flipped VK leaf (opened tree-0 value)" (verifyOnlineExe vk z π { πF with vals := πF.vals.set! 0 (πF.vals[0]!.set! 0 (πF.vals[0]![0]! + 1)) }) false) && ok
    ok := (← report s!"{name}: tampered main vT" (verifyOnlineExe vk z { π with vT := π.vT.set! 0 (π.vT[0]!.set! 0 (K3.add π.vT[0]![0]! K3.one)) } πF) false) && ok
    pure ok

def onlineSelfTest : IO Bool := do
  let z : List Nat := [1, 2, 3]
  let mut ok := true
  ok := (← onlineToyTests "toy" toyInst z (toyProve toyInst 0 1 z)) && ok
  ok := (← onlineToyTests "toy2" toyInst2 z (toyProve2 toyInst2 0 1 1 z)) && ok
  pure ok

/-- full online test on a real J-8 instance + proof: gates, setup, side prover, timings against `verifyFlat`, tampers -/
def onlineRealTest (instPath proofPath : String) : IO Bool := do
  let X ← loadInst instPath
  if !(← j8Gates X) then return false
  let j ← readJson proofPath
  let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
  let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
  let (rf, tf) ← timed fun _ => verifyExeE X z π
  IO.println s!"verifyFlat (old): {match rf with | .ok _ => "ACCEPT" | .error e => s!"REJECT ({e})"} ({tf} ms)"
  let (od, ts) ← timed fun _ => setupData X tip5H
  match od with
  | none => IO.println "setup REJECTED the instance"; pure false
  | some D =>
    IO.println s!"setup: ok, fixed columns {D.vk.cols.size}, root {D.vk.root} ({ts} ms)"
    let (πF, tp) ← timed fun _ => proveFixExe D z π
    IO.println s!"side prover: {tp} ms, fix proof {(FixProof.toJson πF).compress.utf8ByteSize} bytes"
    let vk := D.vk
    let (ro, to) ← timed fun _ => verifyOnlineExe vk z π πF
    let mut ok := (← report "verifyOnline (VK)" ro true)
    IO.println s!"verifyOnline: {to} ms  vs verifyFlat: {tf} ms"
    ok := (← report "tamper vF[0][0] (flipped after the fact: FS mismatch)" (verifyOnlineExe vk z π { πF with vF := πF.vF.set! 0 (πF.vF[0]!.set! 0 (K3.add πF.vF[0]![0]! K3.one)) }) false) && ok
    let last := πF.vF.size - 1
    ok := (← report "forged vF[0][0] (consistent FS, honest FRI)" (verifyOnlineExe vk z π (proveFixExe D z π (some (0, 0)))) false) && ok
    ok := (← report "forged vF[last][0] = zh or zout (consistent FS)" (verifyOnlineExe vk z π (proveFixExe D z π (some (last, 0)))) false) && ok
    ok := (← report "forged vF[0][1] (next-row pre value; consistent FS)" (verifyOnlineExe vk z π (proveFixExe D z π (some (0, 1)))) false) && ok
    ok := (← report "wrong vk.root" (verifyOnlineExe { vk with root := (vk.root.head! + 1) :: vk.root.tail! } z π πF) false) && ok
    ok := (← report "flipped VK leaf (opened tree-0 value)" (verifyOnlineExe vk z π { πF with vals := πF.vals.set! 0 (πF.vals[0]!.set! 0 (πF.vals[0]![0]! + 1)) }) false) && ok
    -- a VK built from a tampered instance (one preprocessed coefficient +1): the honest main proof must not verify under it
    match (List.range X.nc).find? (fun c => X.colKind[c]! == 1 && X.pre[c]!.size > 0) with
    | none => pure ()
    | some c =>
      let Xb := { X with pre := X.pre.set! c (X.pre[c]!.modify 0 (· + 1)) }
      match setupData Xb tip5H with
      | none => IO.println "tampered-pre instance: setup rejected (unexpected)"; ok := false
      | some Db =>
        let πFb := proveFixExe Db z π
        ok := (← report s!"VK from tampered pre (col {c} coef 0 += 1)" (verifyOnlineExe Db.vk z π πFb) false) && ok
    ok := (← report "tampered main vT" (verifyOnlineExe vk z { π with vT := π.vT.set! 0 (π.vT[0]!.set! 0 (K3.add π.vT[0]![0]! K3.one)) } πF) false) && ok
    pure ok

def main (args : List String) : IO UInt32 := do
  match args with
  | ["selftest"] =>
    let ok ← selfTest
    let ok2 ← onlineSelfTest
    let ok := ok && ok2
    IO.println (if ok then "selftest: OK" else "selftest: FAILED")
    pure (if ok then 0 else 1)
  | ["online-test", instPath, proofPath] =>
    let ok ← onlineRealTest instPath proofPath
    IO.println (if ok then "online-test: OK" else "online-test: FAILED")
    pure (if ok then 0 else 1)
  | ["vk-setup", instPath, vkPath] =>
    let X ← loadInst instPath
    if !(← j8Gates X) then return 1
    let t0 ← IO.monoMsNow
    match setupData X tip5H with
    | none => IO.println "REJECT: setup gates fail"; pure 1
    | some D =>
      let strippedPath := vkPath ++ ".inst.json"
      let j ← readJson instPath
      IO.FS.writeFile strippedPath (j.setObjVal! "pre" (Json.arr ((arr (get j "pre")).map fun _ => Json.arr #[]))).compress
      IO.FS.writeFile vkPath (vkJson D.vk strippedPath).compress
      IO.println s!"vk-setup: ok, {D.vk.cols.size} fixed columns, root {D.vk.root} ({(← IO.monoMsNow) - t0} ms)"
      pure 0
  | ["fix-prove", instPath, proofPath, fixPath] =>
    let X ← loadInst instPath
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    match setupData X tip5H with
    | none => IO.println "REJECT: setup gates fail"; pure 1
    | some D =>
      let t0 ← IO.monoMsNow
      let πF := proveFixExe D z π
      IO.FS.writeFile fixPath (FixProof.toJson πF).compress
      IO.println s!"fix-prove: ok ({(← IO.monoMsNow) - t0} ms)"
      pure 0
  | ["verify", "--vk", vkPath, proofPath, fixPath] =>
    let vj ← readJson vkPath
    let X ← loadInst (str (get vj "inst"))
    if X.l != 170 then
      IO.println s!"REJECT: l != 170 (l = {X.l})"
      return 1
    let root ← IO.ofExcept ((limbsE "root" (get vj "root")).mapError IO.userError)
    let vk : VK := { X := X, cols := fixCols X, root := root }
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let πF ← IO.ofExcept ((FixProof.ofJson (← readJson fixPath)).mapError IO.userError)
    let t0 ← IO.monoMsNow
    let r := verifyOnlineExe vk z π πF
    let t1 ← IO.monoMsNow
    match r with
    | .ok _ => IO.println s!"ACCEPT (online, VK; {t1 - t0} ms)"; pure 0
    | .error e => IO.println s!"REJECT: {e} ({t1 - t0} ms)"; pure 1
  | ["verify", instPath, proofPath] =>
    let X ← loadInst instPath
    -- S5: the theorem's `hl` (`l = 170`), next to the gates
    if X.l != 170 then
      IO.println s!"REJECT: l != 170 (l = {X.l})"
      return 1
    if !(NockvmE2E.Exec.J8Shape.j8ShapeOk X) then
      IO.println "REJECT: instance is not J-8 shaped"
      return 1
    if !(NockvmE2E.Exec.J8Shape.j8ShapeXOk X) then
      IO.println "REJECT: instance fails J-8 shape-X check (nq/npub/blockTab/layout)"
      return 1
    match NockvmE2E.Exec.MaskOk.hop0Check X with
    | .error e =>
      IO.println s!"REJECT: {e}"
      return 1
    | .ok _ => pure ()
    let j ← readJson proofPath
    let π ← IO.ofExcept ((FlatProof.ofJson j).mapError IO.userError)
    let z := (← IO.ofExcept ((natsE "z" (get j "z")).mapError IO.userError)).toList
    let t0 ← IO.monoMsNow
    let r := verifyExeE X z π
    let t1 ← IO.monoMsNow
    match r with
    | .ok _ => IO.println s!"ACCEPT ({t1 - t0} ms)"; pure 0
    | .error e => IO.println s!"REJECT: {e} ({t1 - t0} ms)"; pure 1
  | _ =>
    IO.eprintln "usage: nockvm-e2e-verify selftest | verify <inst.json> <proof.json> | vk-setup <inst> <vk.json> | fix-prove <inst> <proof> <fix.json> | verify --vk <vk.json> <proof> <fix.json> | online-test <inst> <proof>"
    pure 2

end NockvmE2E.Exec.V

def main (args : List String) : IO UInt32 := NockvmE2E.Exec.V.main args
