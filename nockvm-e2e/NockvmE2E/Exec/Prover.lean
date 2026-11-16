/-
  NockvmE2E/Exec/Prover.lean   (UNTRUSTED, executed, no proofs)

  The slow prover for the composed RAP + DEEP + FRI + Merkle protocol; data flow as in the executable prover.
  Hash = Tip5Core (Mathlib-free copy of Exec/Tip5, see ProverLink.lean); field = ProverField.
-/
import NockvmE2E.Exec.Tip5Core
import NockvmE2E.Exec.Tip5Fast  -- B-T5F: @[csimp] fast Tip5 for compiled code
import NockvmE2E.Exec.Trace
set_option autoImplicit false

namespace NockvmE2E.Exec.Pv
open Lean NockvmE2E.Exec.PF NockvmE2E.Exec.Tr NockvmE2E.Exec.J NockvmE2E.Exec.Tip5Core

def log2Ceil (n : Nat) : Nat := Id.run do
  let mut h := 0
  while 2 ^ h < n do h := h + 1
  return h

/-! ## Merkle: raw leaves (one base element), Tip5 nodes with (tree id, heap index) address -/

def tNode : Nat := 0x65326510
def tChal : Nat := 0x65326506

structure Tree where
  tid : Nat
  lg : Nat
  leaves : Array F
  lv : Array (Array Nat)   -- lv[j-1]: nodes of height j, five limbs each
  deriving Inhabited

def nodeHash (tid heap : Nat) (l r : List Nat) : List Nat := hashVarlen ([tNode, tid, heap] ++ l ++ r)

def rawDig (v : F) : List Nat := [v.toNat, 0, 0, 0, 0]

def slice5 (a : Array Nat) (i : Nat) : List Nat := (List.range 5).map fun k => a[5 * i + k]!

def Tree.build (tid : Nat) (leaves : Array F) : Tree := Id.run do
  let lg := log2Ceil leaves.size
  let mut lv : Array (Array Nat) := #[]
  let mut prev : Array Nat := #[]
  for j in [1:lg + 1] do
    let cnt := 2 ^ (lg - j)
    let mut cur : Array Nat := Array.mkEmpty (5 * cnt)
    for i in [0:cnt] do
      let l := if j == 1 then rawDig leaves[2 * i]! else slice5 prev (2 * i)
      let r := if j == 1 then rawDig leaves[2 * i + 1]! else slice5 prev (2 * i + 1)
      for x in nodeHash tid (cnt + i) l r do cur := cur.push x
    lv := lv.push cur
    prev := cur
  return { tid := tid, lg := lg, leaves := leaves, lv := lv }

def Tree.root (t : Tree) : List Nat := slice5 t.lv[t.lg - 1]! 0

/-- sibling digests from height `s` (the group subtree root) up to the root -/
def Tree.path (t : Tree) (s g : Nat) : List (List Nat) :=
  (List.range (t.lg - s)).map fun d => slice5 t.lv[s + d - 1]! ((g >>> d) ^^^ 1)

/-- recompute the root from an aligned group of `2^s` leaves `vals` (group `g`) and the path -/
def verifyGroup (root : List Nat) (tid lg s g : Nat) (vals : Array F) (path : List (List Nat)) : Bool := Id.run do
  let mut cur : Array (List Nat) := vals.map rawDig
  for j in [1:s + 1] do
    let cnt := 2 ^ (s - j)
    let mut nx : Array (List Nat) := #[]
    for i in [0:cnt] do
      nx := nx.push (nodeHash tid (2 ^ (lg - j) + g * cnt + i) cur[2 * i]! cur[2 * i + 1]!)
    cur := nx
  let mut d := cur[0]!
  let mut idx := g
  let mut j := s
  for sib in path do
    let heap := 2 ^ (lg - j - 1) + idx / 2
    d := if idx % 2 == 0 then nodeHash tid heap d sib else nodeHash tid heap sib d
    idx := idx / 2
    j := j + 1
  return d == root

/-! ## transcript -/

abbrev FS := IO.Ref (List Nat)

def fsMsg (r : FS) (data : List Nat) : IO Unit := r.modify fun s => absorb s tMsg data
def fsChal (r : FS) (label n : Nat) : IO (List Nat) := do
  let s := absorb (← r.get) tChal [label]
  r.set s
  pure (squeeze s n)
def toE3 (l : List Nat) : E3 := ⟨UInt64.ofNat l[0]!, UInt64.ofNat l[1]!, UInt64.ofNat l[2]!⟩
def strLimbs (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

def logMsg (s : String) : IO Unit := do
  IO.eprintln s!"[{← IO.monoMsNow}ms] {s}"

/-! ## helpers -/

def mkTree (ctr : IO.Ref Nat) (cols : Array (Array F)) (Dn : Nat) : IO (Tree × Nat) := do
  let w := cols.size
  let wp := 2 ^ log2Ceil w
  let half := Dn / 2
  let mut leaves : Array F := Array.replicate (half * 2 * wp) 0
  for ci in [0:w] do
    let col := cols[ci]!
    for q in [0:half] do
      leaves := leaves.set! (q * 2 * wp + ci) col[q]!
      leaves := leaves.set! (q * 2 * wp + wp + ci) col[q + half]!
  let tid ← ctr.modifyGet fun t => (t, t + 1)
  pure (Tree.build tid leaves, wp)

def digJ (d : List Nat) : Json := Json.arr (d.toArray.map natJ)
def e3J (x : E3) : Json := Json.arr (x.limbs.toArray.map natJ)

structure CS where
  coefs : Array (Array F)
  lde : Array (Array F)
  trees : Array (Tree × Nat × Nat)   -- tree, W', #real columns
  blocksJ : Array Json
  deriving Inhabited

def CS.init (w : Nat) : CS := { coefs := Array.replicate w #[], lde := Array.replicate w #[], trees := #[], blocksJ := #[] }

/-- commit the round-`rd` column block of a chip (columns of that round must be final in `tr`): coefficients, coset LDE, Merkle tree, root absorbed -/
def commitRound (fs : FS) (ctr : IO.Ref Nat) (ch : Chip) (tr : Tr) (cs : CS) (rd : Nat) : IO CS := do
  let n := tr.nRows
  let h := log2Ceil (n + 1)
  let Hn := 2 ^ h
  let ld := h + 6
  let Dn := 2 ^ ld
  let bi := (Array.range ch.width).filter fun c => ch.colRound[c]! == rd
  if bi.isEmpty then return cs
  let wH := root h
  let g := root ld
  let mut coefs := cs.coefs
  let mut lde := cs.lde
  for c in bi do
    let cf := intt (tr.cols[c]! ++ Array.replicate (Hn - n) 0) h wH
    coefs := coefs.set! c cf
    lde := lde.set! c (cosetLde cf ld g)
  let (t, wp) ← mkTree ctr (bi.map fun c => lde[c]!) Dn
  fsMsg fs t.root
  logMsg s!"  {ch.id}: committed round {rd} block ({bi.size} cols)"
  pure { coefs := coefs, lde := lde, trees := cs.trees.push (t, wp, bi.size),
         blocksJ := cs.blocksJ.push (Json.mkObj [("round", natJ rd), ("cols", natJ bi.size), ("root", digJ t.root)]) }

/-- `Σ_i α^i C_i` split by constraint kind, then combined with the zero-on-padding multipliers at the point `x` (an `E3`). -/
def combine (ch : Chip) (apow : Array E3) (vals : Array E3) (x : E3) (wpow : Array F) (n Hn : Nat) : E3 := Id.run do
  let mut sr := E3.zero
  let mut st := E3.zero
  for i in [0:ch.cons.size] do
    let t := E3.mul apow[i]! vals[i]!
    if ch.cons[i]!.kind == 0 then sr := E3.add sr t else st := E3.add st t
  let mut m := E3.one
  for i in [n:Hn] do m := E3.mul m (E3.sub x (E3.ofF wpow[i]!))
  let sel := E3.sub x (E3.ofF wpow[n - 1]!)
  return E3.mul m (E3.add sr (E3.mul sel st))

/-- the DEEP identity `Σ α^i M C_i (v) = Z_H(ζ) Σ_j ζ^{j|H|} Σ_t x^t vQ_{j,t}`; returns (lhs, rhs) -/
def identity (ch : Chip) (apow : Array E3) (slots : Array E3) (pub : Array F) (wpow : Array F) (n Hn nq : Nat)
    (z : E3) (cur next : Array E3) (vq : Array E3) : E3 × E3 :=
  let vals := evalCons ch { cur := cur, next := next, pub := pub, chal := slots, bc := ch.baseCols }
  let lhs := combine ch apow vals z wpow n Hn
  let zh := E3.sub (E3.pow z Hn) E3.one
  let zj := E3.pow z Hn
  let rhs := Id.run do
    let mut acc := E3.zero
    let mut pw := E3.one
    for j in [0:nq] do
      let qv := E3.add (E3.add vq[3 * j]! (E3.mul vq[3 * j + 1]! E3.gen)) (E3.mul vq[3 * j + 2]! E3.gen2)
      acc := E3.add acc (E3.mul pw qv)
      pw := E3.mul pw zj
    return E3.mul zh acc
  (lhs, rhs)

def randE3 : IO E3 := do
  let r : IO F := do pure (UInt64.ofNat ((← IO.rand 0 (2 ^ 62)) * 4 + 1 + (← IO.rand 0 3)) % PF.P)
  pure ⟨← r, ← r, ← r⟩

structure Out where
  json : Json
  ok : Bool
  notes : Array String

/-- one chip -/
def proveChip (fs : FS) (ctr : IO.Ref Nat) (ch : Chip) (tr : Tr) (cs : CS) (slots : Array E3) (nQ : Nat) : IO Out := do
  let mut notes : Array String := #[]
  let mut ok := true
  let n := tr.nRows
  let h := log2Ceil (n + 1)
  let Hn := 2 ^ h
  let ld := h + 6
  let Dn := 2 ^ ld
  let wH := root h
  let g := root ld
  logMsg s!"chip {ch.id}: n={n} |H|=2^{h} |D|=2^{ld} width={ch.width} cons={ch.cons.size}"
  for c in ch.cons do
    if c.kind > 1 then throw (IO.userError s!"{ch.id}: boundary/terminal constraint unsupported")
  -- (a) trace satisfies the DAG under the checker's semantics
  match rowCheck ch tr slots with
  | some (ci, r) => notes := notes.push s!"(a) ROW CHECK FAILED: constraint {ci} row {r}"; ok := false
  | none => notes := notes.push "(a) rowcheck (checker semantics): ok"
  -- columns / LDE / round-block commitments were done by `commitRound` (round by round, coins drawn in between)
  let coefs := cs.coefs
  let lde := cs.lde
  let mut xs : Array F := Array.mkEmpty Dn
  let mut x : F := seven
  for _ in [0:Dn] do
    xs := xs.push x
    x := mul x g
  let wpow := Id.run do
    let mut a : Array F := Array.mkEmpty Hn
    let mut w : F := 1
    for _ in [0:Hn] do
      a := a.push w
      w := mul w wH
    return a
  let blocksJ := cs.blocksJ
  let trees := cs.trees
  -- alpha, quotient
  let alpha := toE3 (← fsChal fs 1 3)
  let apow := Id.run do
    let mut a : Array E3 := Array.mkEmpty ch.cons.size
    let mut p := E3.one
    for _ in [0:ch.cons.size] do
      a := a.push p
      p := E3.mul p alpha
    return a
  let nq := ch.cons.foldl (fun m c => max m c.deg) 1
  if nq * Hn > Dn then throw (IO.userError s!"{ch.id}: degree {nq} too large for rate 1/64")
  let zinv := (Array.range 64).map fun t => inv (sub (pow xs[t]! Hn) 1)
  let mut qa : Array F := Array.mkEmpty Dn
  let mut qb : Array F := Array.mkEmpty Dn
  let mut qc : Array F := Array.mkEmpty Dn
  for t in [0:Dn] do
    let cur := lde.map fun c => E3.ofF c[t]!
    let next := lde.map fun c => E3.ofF c[(t + 64) % Dn]!
    let vals := evalCons ch { cur := cur, next := next, pub := tr.pub, chal := slots, bc := ch.baseCols }
    let nv := combine ch apow vals (E3.ofF xs[t]!) wpow n Hn
    let q := E3.smul zinv[t % 64]! nv
    qa := qa.push q.a
    qb := qb.push q.b
    qc := qc.push q.c
  let invSeven := inv seven
  let unc (a : Array F) : Array F := Id.run do
    let c := intt a ld g
    let mut s : F := 1
    let mut o : Array F := Array.mkEmpty Dn
    for i in [0:Dn] do
      o := o.push (mul c[i]! s)
      s := mul s invSeven
    return o
  let qco := #[unc qa, unc qb, unc qc]
  let high := qco.foldl (fun acc a => acc || (a.extract (nq * Hn) Dn).any (· != 0)) false
  if high then
    notes := notes.push s!"(b) QUOTIENT NOT LOW-DEGREE (degree bound {nq}|H| violated: constraints not divisible by Z_H)"
    ok := false
  else notes := notes.push s!"(b) quotient degree < {nq}|H|: ok (divisibility by Z_H)"
  let qcoefs : Array (Array F) := Id.run do
    let mut o := #[]
    for j in [0:nq] do
      for t in [0:3] do o := o.push (qco[t]!.extract (j * Hn) ((j + 1) * Hn))
    return o
  let qlde := qcoefs.map fun cf => cosetLde cf ld g
  let (qt, qwp) ← mkTree ctr qlde Dn
  fsMsg fs qt.root
  logMsg s!"  quotient committed (nq={nq})"
  -- zeta, openings
  let mut z := toE3 (← fsChal fs 2 3)
  if E3.isBase z then z := E3.add z E3.gen
  let zw := E3.mul z (E3.ofF wH)
  let allCoefs := coefs ++ qcoefs
  let nW := ch.width
  let nextCols := nextColsOf ch
  let v0 := allCoefs.map fun cf => horner cf z
  let v1 := nextCols.map fun c => horner coefs[c]! zw
  fsMsg fs ((v0.toList.flatMap E3.limbs) ++ (v1.toList.flatMap E3.limbs))
  -- (c) DEEP identity at zeta
  let nextAt := Id.run do
    let mut a := Array.replicate nW E3.zero
    for i in [0:nextCols.size] do a := a.set! nextCols[i]! v1[i]!
    return a
  let (l0, r0) := identity ch apow slots tr.pub wpow n Hn nq z (v0.extract 0 nW) nextAt (v0.extract nW v0.size)
  if l0 == r0 then notes := notes.push "(c) DEEP identity at zeta: ok" else notes := notes.push "(c) DEEP IDENTITY AT ZETA FAILED"; ok := false
  -- (d) same identity at two random K3 points from the coefficients
  for _ in [0:2] do
    let r ← randE3
    let rw := E3.mul r (E3.ofF wH)
    let cu := coefs.map fun cf => horner cf r
    let nx := (Array.range nW).map fun c => if nextCols.contains c then horner coefs[c]! rw else E3.zero
    let vq := qcoefs.map fun cf => horner cf r
    let (l, rr) := identity ch apow slots tr.pub wpow n Hn nq r cu nx vq
    if l == rr then notes := notes.push "(d) identity at random K3 point: ok" else notes := notes.push "(d) IDENTITY AT RANDOM POINT FAILED"; ok := false
  -- batching
  let gamma := toE3 (← fsChal fs 3 3)
  let nOpen0 := nW + qlde.size
  let ldeAll := lde ++ qlde
  let gp := Id.run do
    let mut a : Array E3 := #[]
    let mut p := E3.one
    for _ in [0:nOpen0 + nextCols.size] do
      a := a.push p
      p := E3.mul p gamma
    return a
  let mut k0 := E3.zero
  for c in [0:nOpen0] do k0 := E3.add k0 (E3.mul gp[c]! v0[c]!)
  let mut k1 := E3.zero
  for i in [0:nextCols.size] do k1 := E3.add k1 (E3.mul gp[nOpen0 + i]! v1[i]!)
  let mut f0 : Array E3 := Array.mkEmpty Dn
  for t in [0:Dn] do
    let mut a0 := E3.zero
    for c in [0:nOpen0] do a0 := E3.add a0 (E3.smul ldeAll[c]![t]! gp[c]!)
    let mut a1 := E3.zero
    for i in [0:nextCols.size] do a1 := E3.add a1 (E3.smul lde[nextCols[i]!]![t]! gp[nOpen0 + i]!)
    let xe := E3.ofF xs[t]!
    f0 := f0.push (E3.add (E3.mul (E3.sub a0 k0) (E3.inv (E3.sub xe z))) (E3.mul (E3.sub a1 k1) (E3.inv (E3.sub xe zw))))
  logMsg "  DEEP word built"
  -- FRI
  let inv2 := inv 2
  let mut layers : Array (Array E3) := #[f0]
  let mut ftrees : Array Tree := #[]
  let mut lx := xs
  let mut lxs : Array (Array F) := #[xs]
  let mut betas : Array E3 := #[]
  let mut rootsJ : Array Json := #[]
  for k in [0:h] do
    let beta := toE3 (← fsChal fs (100 + k) 3)
    betas := betas.push beta
    let cur := layers[k]!
    let half := cur.size / 2
    let mut nxt : Array E3 := Array.mkEmpty half
    for t in [0:half] do
      let a := cur[t]!
      let b := cur[t + half]!
      nxt := nxt.push (E3.add (E3.smul inv2 (E3.add a b)) (E3.mul beta (E3.smul (inv (mul 2 lx[t]!)) (E3.sub a b))))
    lx := (lx.extract 0 half).map fun v => mul v v
    lxs := lxs.push lx
    layers := layers.push nxt
    if k + 1 < h then
      let hh := nxt.size / 2
      let mut lv : Array F := Array.replicate (hh * 8) 0
      for q in [0:hh] do
        let a := nxt[q]!
        let b := nxt[q + hh]!
        for (o, v) in [(0, a.a), (1, a.b), (2, a.c), (3, b.a), (4, b.b), (5, b.c)] do lv := lv.set! (q * 8 + o) v
      let tid ← ctr.modifyGet fun t => (t, t + 1)
      let t := Tree.build tid lv
      ftrees := ftrees.push t
      fsMsg fs t.root
      rootsJ := rootsJ.push (digJ t.root)
  let last := layers[h]!
  let cst := last[0]!
  if last.any (· != cst) then
    notes := notes.push "FRI FINAL LAYER NOT CONSTANT (word not low-degree)"
    ok := false
  fsMsg fs cst.limbs
  logMsg s!"  FRI done ({h} folds, final layer {last.size})"
  -- queries
  let half0 := Dn / 2
  let qs := (← fsChal fs 4 nQ).map (· % half0)
  let sB := fun (wp : Nat) => 1 + log2Ceil wp
  let mut qJ : Array Json := #[]
  let allTrees : Array (Tree × Nat × Nat) := trees.push (qt, qwp, qlde.size)
  for q in qs do
    let mut bJ : Array Json := #[]
    for (t, wp, w) in allTrees do
      let base := q * 2 * wp
      let vals := (Array.range w).map (fun c => t.leaves[base + c]!) ++ (Array.range w).map (fun c => t.leaves[base + wp + c]!)
      bJ := bJ.push (Json.mkObj [("vals", Json.arr (vals.map fun v => natJ v.toNat)), ("path", Json.arr ((t.path (sB wp) q).toArray.map digJ))])
    let mut lJ : Array Json := #[]
    for k in [1:h] do
      let t := ftrees[k - 1]!
      let qk := q % (Dn / 2 ^ k / 2)
      let vals := (Array.range 6).map fun o => t.leaves[qk * 8 + o]!
      lJ := lJ.push (Json.mkObj [("vals", Json.arr (vals.map fun v => natJ v.toNat)), ("path", Json.arr ((t.path 3 qk).toArray.map digJ))])
    qJ := qJ.push (Json.mkObj [("q", natJ q), ("blocks", Json.arr bJ), ("layers", Json.arr lJ)])
  -- (f) merkle paths of the first 2 queries
  let mut pathsOk := true
  for q in qs.take 2 do
    for (t, wp, _) in allTrees do
      let s := sB wp
      let vals := t.leaves.extract (q * 2 * wp) (q * 2 * wp + 2 * wp)
      pathsOk := pathsOk && verifyGroup t.root t.tid t.lg s q vals (t.path s q)
    for k in [1:h] do
      let t := ftrees[k - 1]!
      let qk := q % (Dn / 2 ^ k / 2)
      pathsOk := pathsOk && verifyGroup t.root t.tid t.lg 3 qk (t.leaves.extract (qk * 8) (qk * 8 + 8)) (t.path 3 qk)
  notes := notes.push s!"(f) merkle auth paths (2 queries, all trees): {if pathsOk then "ok" else "FAILED"}"
  if !pathsOk then ok := false
  -- (e) fold consistency + layer-0 recomputation at 2 random positions
  let mut foldOk := true
  for _ in [0:2] do
    let q ← IO.rand 0 (half0 - 1)
    -- layer 0 from the columns directly
    let dir (t : Nat) : E3 := Id.run do
      let xe := E3.ofF xs[t]!
      let mut a := E3.zero
      for c in [0:nOpen0] do a := E3.add a (E3.mul gp[c]! (E3.mul (E3.sub (E3.ofF ldeAll[c]![t]!) v0[c]!) (E3.inv (E3.sub xe z))))
      for i in [0:nextCols.size] do
        a := E3.add a (E3.mul gp[nOpen0 + i]! (E3.mul (E3.sub (E3.ofF lde[nextCols[i]!]![t]!) v1[i]!) (E3.inv (E3.sub xe zw))))
      return a
    if dir q != f0[q]! || dir (q + half0) != f0[q + half0]! then foldOk := false
    for k in [0:h] do
      let nk := layers[k]!.size
      let qk := q % (nk / 2)
      let a := layers[k]![qk]!
      let b := layers[k]![qk + nk / 2]!
      let fv := E3.add (E3.smul inv2 (E3.add a b)) (E3.mul betas[k]! (E3.smul (inv (mul 2 lxs[k]![qk]!)) (E3.sub a b)))
      if fv != layers[k + 1]![qk]! then foldOk := false
    pure ()
  notes := notes.push s!"(e) layer-0 recomputation + fold chain at 2 random positions: {if foldOk then "ok" else "FAILED"}"
  if !foldOk then ok := false
  let json := Json.mkObj [
    ("id", Json.str ch.id), ("n_rows", natJ n), ("log_H", natJ h), ("log_D", natJ ld), ("nq", natJ nq),
    ("blocks", Json.arr blocksJ), ("quotient_root", digJ qt.root), ("zeta", e3J z),
    ("v0", Json.arr (v0.map e3J)), ("v1_cols", Json.arr (nextCols.map natJ)), ("v1", Json.arr (v1.map e3J)),
    ("fri_roots", Json.arr rootsJ), ("fri_const", e3J cst), ("queries", Json.arr qJ)]
  pure { json := json, ok := ok, notes := notes }

end NockvmE2E.Exec.Pv
