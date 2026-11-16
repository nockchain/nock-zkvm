/-
  NockvmE2E/Exec/AuxFill.lean   (UNTRUSTED, executed, no proofs)

  Port of `nockvm-air-rs/nockvm-air/src/aux_fill.rs` (generic aux solver: every round-s K cell is defined by a gate affine in it),
  `fill_publics`, `complete_challenges` (gamma'-power slots), `compute_derived_publics`, and the per-chip hints of
  `nockvm-air-p3/src/fill.rs` (cell links / first_pass, walk-chip cross-chip seeds, cell big-atom seeds).
  Differences from the Rust: no stage-invariant node cache (every equation evaluation re-evaluates the reachable shared nodes);
  all values are E3 (Trace.lean's single interpreter); `Ok(None)` for non-K constraints = `consK`.
-/
import NockvmE2E.Exec.Trace
import Std.Data.HashMap
set_option autoImplicit false

namespace NockvmE2E.Exec.Aux
open Lean NockvmE2E.Exec.PF NockvmE2E.Exec.Tr NockvmE2E.Exec.J Std

instance : Inhabited Tr := ⟨{ nRows := 0, pub := #[], cols := #[] }⟩
instance : Inhabited Chip := ⟨{ id := "", shared := #[], cons := #[], colRound := #[], sharedK := #[], consK := #[], baseCols := 0, width := 0 }⟩

/-! ## read sets -/
def pubBase : Nat := 0x80000000
def mkRd (next ext : Bool) (i : Nat) : Nat := i * 4 + (if ext then 2 else 0) + (if next then 1 else 0)
def rdNext (r : Nat) : Bool := r % 2 == 1
def rdExt (r : Nat) : Bool := (r / 2) % 2 == 1
def rdIdx (r : Nat) : Nat := r / 4

def dedupSort (a : Array Nat) : Array Nat :=
  (a.qsort (· < ·)).foldl (fun r x => if r.back? == some x then r else r.push x) #[]

partial def readsEx (sr : Array (Array Nat)) (e : Ex) (acc : Array Nat) : Array Nat :=
  match e with
  | .var 0 i => acc.push (mkRd false false i)
  | .var 1 i => acc.push (mkRd true false i)
  | .extVar 0 e => acc.push (mkRd false true e)
  | .extVar 1 e => acc.push (mkRd true true e)
  | .extVar _ e => acc.push (mkRd false true (pubBase + e))
  | .ref i => acc ++ sr[i]!
  | .add a b | .sub a b | .mul a b => readsEx sr b (readsEx sr a acc)
  | .neg a | .pow a _ => readsEx sr a acc
  | _ => acc

partial def refsOf (e : Ex) (acc : Array Nat) : Array Nat :=
  match e with
  | .ref i => acc.push i
  | .add a b | .sub a b | .mul a b => refsOf b (refsOf a acc)
  | .neg a | .pow a _ => refsOf a acc
  | _ => acc

def reachOf (ch : Chip) (e : Ex) : Array Nat := Id.run do
  let mut seen := Array.replicate ch.shared.size false
  let mut stack := refsOf e #[]
  while !stack.isEmpty do
    let i := stack.back!
    stack := stack.pop
    if !seen[i]! then
      seen := seen.set! i true
      stack := refsOf ch.shared[i]! stack
  return (Array.range ch.shared.size).filter fun i => seen[i]!

structure Plan where
  reads : Array (Array Nat)
  reach : Array (Array Nat)

def mkPlan (ch : Chip) : Plan := Id.run do
  let mut sr : Array (Array Nat) := #[]
  for s in ch.shared do sr := sr.push (dedupSort (readsEx sr s #[]))
  return { reads := ch.cons.map fun c => dedupSort (readsEx sr c.e #[]), reach := ch.cons.map fun c => reachOf ch c.e }

def evalCon (ch : Chip) (reach : Array Nat) (ci : Nat) (env : Env) : E3 := Id.run do
  let mut memo : Array E3 := Array.replicate ch.shared.size E3.zero
  for i in reach do memo := memo.set! i (ev env memo ch.shared[i]!)
  return ev env memo ch.cons[ci]!.e

def mkEnv (ch : Chip) (rows : Array (Array F)) (t n : Nat) (chal : Array E3) (pub : Array F) : Env :=
  { cur := rows[t]!.map E3.ofF
    next := if t + 1 < n then rows[t + 1]!.map E3.ofF else Array.replicate ch.width E3.zero
    pub := pub, chal := chal, bc := ch.baseCols }

def coord (v : E3) (k : Nat) : F := if k == 0 then v.a else if k == 1 then v.b else v.c

def setCell (env : Env) (intoNext : Bool) (c : Nat) (v : E3) : Env :=
  let b := env.bc + 3 * c
  let setA (a : Array E3) := (a.set! b (E3.ofF v.a)).set! (b + 1) (E3.ofF v.b) |>.set! (b + 2) (E3.ofF v.c)
  if intoNext then { env with next := setA env.next } else { env with cur := setA env.cur }

/-! ## hints -/
structure Link where
  target : Array Nat
  source : Array Nat
  idxCol : Nat
  ptrCol : Nat
  guardCol : Nat
  skipCol : Option Nat
  deriving Inhabited

def Link.applies (l : Link) (row : Array F) : Bool :=
  row[l.guardCol]! == 1 && (l.skipCol.all fun c => row[c]! != 1)

structure Hints where
  firstPass : Array Nat := #[]
  links : Array Link := #[]
  outputPubs : Option (Array Nat) := none
  seeds : Array (Nat × Nat × E3) := #[]

def hintsFor (id : String) : Hints :=
  match id with
  | "cellChipHQKW" =>
    { firstPass := Array.range 18
      links := #[
        ⟨#[6, 7], #[0, 1], 2, 3, 5, some 130⟩, ⟨#[12, 13], #[0, 1], 2, 4, 6, some 131⟩,
        ⟨#[8, 9], #[2, 3], 2, 3, 5, some 130⟩, ⟨#[14, 15], #[2, 3], 2, 4, 6, some 131⟩,
        ⟨#[10, 11], #[4, 5], 2, 3, 5, some 130⟩, ⟨#[16, 17], #[4, 5], 2, 4, 6, some 131⟩] }
  | "computeChipVCLHX" | "computeChipVCLHX9" => { outputPubs := some #[4, 5, 6, 7, 8, 9, 10] }
  | _ => {}

def applies (kind t n : Nat) : Bool :=
  match kind with | 0 => t < n | 2 => t == 0 | 3 => t + 1 == n | _ => t + 1 < n

def prio (kind : Nat) : Nat := match kind with | 0 | 1 => 0 | 2 => 1 | _ => 2

def rowMap (rows : Array (Array F)) (col : Nat) : HashMap Nat Nat := Id.run do
  let mut m : HashMap Nat Nat := {}
  for i in [0:rows.size] do m := m.insert rows[i]![col]!.toNat i
  return m

def topoOrder (rows : Array (Array F)) (links : Array Link) (maps : Array (HashMap Nat Nat)) : Array Nat := Id.run do
  let n := rows.size
  let deps (r : Nat) : Array Nat := Id.run do
    let mut o : Array Nat := #[]
    for k in [0:links.size] do
      let l := links[k]!
      if l.applies rows[r]! then
        match maps[k]!.get? rows[r]![l.ptrCol]!.toNat with
        | some j => o := o.push j
        | none => pure ()
    return o
  let mut state := Array.replicate n 0
  let mut out : Array Nat := #[]
  for k in [0:n] do
    let root := n - 1 - k
    if state[root]! != 0 then continue
    let mut stack : Array (Nat × Array Nat) := #[(root, deps root)]
    state := state.set! root 1
    while !stack.isEmpty do
      let (r, ds) := stack.back!
      match ds.back? with
      | some d =>
        stack := stack.pop.push (r, ds.pop)
        if state[d]! == 0 then
          state := state.set! d 1
          stack := stack.push (d, deps d)
      | none =>
        state := state.set! r 2
        out := out.push r
        stack := stack.pop
  return out

partial def findR (p : Array Nat) (x : Nat) : Nat := if p[x]! == x then x else findR p p[x]!

/-! ## the solver -/

/-- fill the round-`stage` K columns of `ch` in `rows0` (real rows); returns the rows and the number of unsolved cells -/
def fillAux (ch : Chip) (hints : Hints) (rows0 : Array (Array F)) (chal : Array E3) (pub : Array F) (stage : Nat) :
    IO (Array (Array F) × Nat) := do
  let n := rows0.size
  if n == 0 then throw (IO.userError "aux fill: empty trace")
  let plan := mkPlan ch
  let bc := ch.baseCols
  let nExt := (ch.width - bc) / 3
  let isUnk (e : Nat) : Bool := e < nExt && ch.colRound[bc + 3 * e]! == stage
  let physUnk (i : Nat) : Bool := i ≥ bc && isUnk ((i - bc) / 3)
  let mut cand : Array (Array Nat) := Array.replicate nExt #[]
  for ci in [0:ch.cons.size] do
    if ch.cons[ci]!.round > stage then continue
    let rd := plan.reads[ci]!
    if rd.any (fun r => !rdExt r && physUnk (rdIdx r)) then continue
    if !ch.consK[ci]! then continue
    if rd.any (fun r => rdExt r && rdIdx r ≥ pubBase &&
        (match hints.outputPubs with | none => true | some o => o.contains (rdIdx r - pubBase))) then continue
    for r in rd do
      if rdExt r && isUnk (rdIdx r) then
        let e := rdIdx r
        if !cand[e]!.contains ci then cand := cand.modify e (·.push ci)
  let allCands : Array Nat := Id.run do
    let a := (cand.foldl (· ++ ·) #[]).qsort fun x y =>
      let kx := (prio ch.cons[x]!.kind, x); let ky := (prio ch.cons[y]!.kind, y)
      kx.1 < ky.1 || (kx.1 == ky.1 && kx.2 < ky.2)
    return a.foldl (fun r x => if r.back? == some x then r else r.push x) #[]
  let mut rows := rows0
  let mut solved : Array (Array Bool) := Array.replicate n (Array.replicate nExt false)
  for (r, e, v) in hints.seeds do
    if r < n && isUnk e then
      rows := rows.modify r fun a => (a.set! (bc + 3 * e) v.a).set! (bc + 3 * e + 1) v.b |>.set! (bc + 3 * e + 2) v.c
      solved := solved.modify r (·.set! e true)
  let first := hints.firstPass.filter isUnk
  let rest := unknownList nExt isUnk |>.filter fun e => !first.contains e
  let passes : Array (Array Nat × Bool × Bool) :=
    (if first.isEmpty then #[] else #[(first, true, false)]) ++ #[(rest, false, true)]
  let mut lc : HashMap (Nat × Nat × Nat × List Nat) (E3 × Array E3) := {}
  let mut unsolvedN := 0
  let zeroRow := Array.replicate ch.width (0 : F)
  let _ := zeroRow
  for (targets, descending, finalPass) in passes do
    let maps := hints.links.map fun l => rowMap rows l.idxCol
    let order := if descending then topoOrder rows hints.links maps else Array.range n
    for r in order do
      let mut pending : Array Bool := Array.replicate nExt false
      for c in targets do
        if !solved[r]![c]! then pending := pending.set! c true
      if descending then
        for k in [0:hints.links.size] do
          let l := hints.links[k]!
          if !(l.target.all fun c => pending[c]!) then continue
          if !l.applies rows[r]! then continue
          let some j := maps[k]!.get? rows[r]![l.ptrCol]!.toNat | continue
          if !(l.source.all fun c => solved[j]![c]!) then continue
          for q in [0:l.target.size] do
            let t := l.target[q]!
            let s := l.source[q]!
            for kk in [0:3] do
              let v := rows[j]![bc + 3 * s + kk]!
              rows := rows.modify r (·.set! (bc + 3 * t + kk) v)
            solved := solved.modify r (·.set! t true)
            pending := pending.set! t false
      let pendList := fun (p : Array Bool) => (Array.range nExt).filter fun c => p[c]!
      repeat
        -- equations usable now: (constraint, row t, unknown cells at row r)
        let mut eqs : Array (Nat × Nat × Array Nat) := #[]
        for ci in allCands do
          let kind := ch.cons[ci]!.kind
          let ts := if r == 0 then #[r] else #[r, r - 1]
          for t in ts do
            if !applies kind t n then continue
            let mut u : Array Nat := #[]
            let mut ok := true
            for rd in plan.reads[ci]! do
              if !rdExt rd || !(isUnk (rdIdx rd)) then continue
              let i := rdIdx rd
              let row := t + (if rdNext rd then 1 else 0)
              if row ≥ n then continue
              if solved[row]![i]! then continue
              if row == r && pending[i]! then u := u.push i else ok := false
            if ok && !u.isEmpty then eqs := eqs.push (ci, t, dedupSort u)
        let caps := dedupSort (eqs.map fun e => e.2.2.size)
        let mut progress := false
        for cap in caps do
          let eqsC := eqs.filter fun e => e.2.2.size ≤ cap
          let mut comp : Array Nat := Array.range nExt
          for (_, _, u) in eqsC do
            for w in [0:u.size - 1] do
              let a := findR comp u[w]!
              let b := findR comp u[w + 1]!
              if a != b then comp := comp.set! a b
          let pl := pendList pending
          let roots := dedupSort (pl.map (findR comp))
          for root in roots do
            let cells := pl.filter fun c => findR comp c == root
            let eis := (Array.range eqsC.size).filter fun ei => findR comp eqsC[ei]!.2.2[0]! == root
            if eis.isEmpty then continue
            let nc := cells.size
            let mut mat : Array (Array E3) := #[]
            for ei in eis do
              let (ci, t, u) := eqsC[ei]!
              let key := (ci, t, r, u.toList)
              if !lc.contains key then
                let env0 := mkEnv ch rows t n chal pub
                let intoNext := t != r
                let env := u.foldl (fun e c => setCell e intoNext c E3.zero) env0
                let b := evalCon ch plan.reach[ci]! ci env
                let coefs := u.map fun c => E3.sub (evalCon ch plan.reach[ci]! ci (setCell env intoNext c E3.one)) b
                lc := lc.insert key (b, coefs)
              let some (b, coefs) := lc.get? key | continue
              let mut line : Array E3 := Array.replicate (nc + 1) E3.zero
              line := line.set! nc (E3.neg b)
              for q in [0:u.size] do
                let pos := (cells.findIdx? (· == u[q]!)).getD 0
                line := line.set! pos coefs[q]!
              mat := mat.push line
            -- Gauss-Jordan
            let mut pivRow := 0
            let mut pivots : Array (Nat × Nat) := #[]
            for col in [0:nc] do
              let some pr := (List.range' pivRow (mat.size - pivRow)).find? (fun i => mat[i]![col]! != E3.zero) | continue
              let tmp := mat[pivRow]!
              mat := (mat.set! pivRow mat[pr]!).set! pr tmp
              let iv := E3.inv mat[pivRow]![col]!
              mat := mat.modify pivRow (·.map (E3.mul iv))
              for i in [0:mat.size] do
                if i != pivRow && mat[i]![col]! != E3.zero then
                  let f := mat[i]![col]!
                  let pr := mat[pivRow]!
                  mat := mat.modify i fun row => (Array.range (nc + 1)).map fun j => E3.sub row[j]! (E3.mul f pr[j]!)
              pivots := pivots.push (pivRow, col)
              pivRow := pivRow + 1
            let mut sol : Array (Nat × E3) := #[]
            for (pr, pc) in pivots do
              let determined := (List.range nc).all fun j => j == pc || mat[pr]![j]! == E3.zero
              if determined then sol := sol.push (cells[pc]!, mat[pr]![nc]!)
            if sol.isEmpty then continue
            let solvedNow := sol.map (·.1)
            let mut verified := true
            for ei in eis do
              let (ci, t, u) := eqsC[ei]!
              if !(u.all fun c => solvedNow.contains c) then continue
              let intoNext := t != r
              let env := sol.foldl (fun e (c, v) => setCell e intoNext c v) (mkEnv ch rows t n chal pub)
              if evalCon ch plan.reach[ci]! ci env != E3.zero then verified := false
            if !verified then continue
            for (c, v) in sol do
              rows := rows.modify r fun a => (a.set! (bc + 3 * c) v.a).set! (bc + 3 * c + 1) v.b |>.set! (bc + 3 * c + 2) v.c
              solved := solved.modify r (·.set! c true)
              pending := pending.set! c false
            progress := true
          if progress then break
        if (pendList pending).isEmpty || !progress then break
      if finalPass then
        for c in pendList pending do
          solved := solved.modify r (·.set! c true)
          unsolvedN := unsolvedN + 1
          if unsolvedN ≤ 5 then IO.eprintln s!"  aux fill {ch.id} stage {stage}: UNSOLVED cell ext {c} row {r}"
  return (rows, unsolvedN)
where
  unknownList (nExt : Nat) (isUnk : Nat → Bool) : Array Nat := (Array.range nExt).filter isUnk

/-! ## publics, challenges -/

def fillPublics (ch : Chip) (rows : Array (Array F)) (chal : Array E3) (pub0 : Array F) : Array F := Id.run do
  let n := rows.size
  let plan := mkPlan ch
  let npub := pub0.size / 3
  let mut pub := pub0
  let mut known : Array Bool := Array.replicate npub false
  let mut progress := true
  while progress do
    progress := false
    for i in [0:npub] do
      if known[i]! then continue
      let mut found := false
      for ci in [0:ch.cons.size] do
        if found then break
        if !ch.consK[ci]! || !(plan.reads[ci]!.contains (mkRd false true (pubBase + i))) then continue
        if plan.reads[ci]!.any (fun r => rdExt r && rdIdx r ≥ pubBase && rdIdx r != pubBase + i && !(known[rdIdx r - pubBase]!)) then continue
        let ts : Array Nat := match ch.cons[ci]!.kind with
          | 3 => #[n - 1] | 2 => #[0] | 0 => Array.range n | _ => Array.range (n - 1)
        for t in ts do
          if found then break
          let setPub := fun (v : E3) => ((pub.set! (3 * i) v.a).set! (3 * i + 1) v.b).set! (3 * i + 2) v.c
          let b := evalCon ch plan.reach[ci]! ci (mkEnv ch rows t n chal (setPub E3.zero))
          let e1 := evalCon ch plan.reach[ci]! ci (mkEnv ch rows t n chal (setPub E3.one))
          let a := E3.sub e1 b
          if a == E3.zero then continue
          pub := setPub (E3.mul (E3.neg b) (E3.inv a))
          known := known.set! i true
          progress := true
          found := true
  return pub

structure Der where
  slot : Nat
  re : Nat
  im : Nat
  power : Nat
  isRe : Bool

def loadMeta (path : String) : IO (Array Der × Array (Nat × Nat)) := do
  let d ← readJson path
  let ders := (arr (get d "derived_challenges")).map fun j =>
    ({ slot := nat (get j "slot"), re := nat (get j "re_coin"), im := nat (get j "im_coin"), power := nat (get j "power"),
       isRe := str (get j "part") == "re" } : Der)
  let coins := (arr (get (get d "frame") "coins")).map fun j => (nat (get j "index"), nat (get j "sampled_after"))
  pure (ders, coins)

def kprimePow (re im : E3) (power : Nat) : E3 × E3 := Id.run do
  let mut a := E3.one
  let mut b := E3.zero
  let d := E3.ofF 7
  for _ in [0:power] do
    let a' := E3.add (E3.mul a re) (E3.mul d (E3.mul b im))
    let b' := E3.add (E3.mul a im) (E3.mul b re)
    a := a'
    b := b'
  return (a, b)

/-- frame coins (slots `< 64`, E3) -> completed challenge slots (adds the derived gamma'-power slots) -/
def completeSlots (frame : Array E3) (ders : Array Der) : Array E3 := Id.run do
  let mut out := frame
  -- derived slots past the 64-entry frame (the J-9 AL y-powers 41..106) need room; unchanged when every slot fits
  let top := ders.foldl (fun m d => max m (d.slot + 1)) 0
  if top > out.size then out := out ++ Array.replicate (top - out.size) E3.zero
  for d in ders do
    let (a, b) := kprimePow frame[d.re]! frame[d.im]! d.power
    out := out.set! d.slot (if d.isRe then a else b)
  return out

/-- compute publics 6..12 (alphaW = coin 13, seed = alphaW * sum_q gammaW^q label_q) -/
def computeDerived (label : Array F) (slots : Array E3) : Array F := Id.run do
  let aw := slots[13]!
  let gw := slots[14]!
  let mut sum := E3.zero
  let mut pw := E3.one
  for q in [0:6] do
    sum := E3.add sum (E3.mul pw (E3.ofF label[q]!))
    pw := E3.mul pw gw
  let seed := E3.mul aw sum
  return #[aw.a, aw.b, aw.c, seed.a, seed.b, seed.c]

/-! ## per chip, per stage (with the cross-chip seeds of `fill.rs`) -/

def rowsOf (tr : Tr) : Array (Array F) := (Array.range tr.nRows).map fun r => tr.cols.map (·[r]!)

def colsOf (rows : Array (Array F)) (w : Nat) : Array (Array F) := (Array.range w).map fun c => rows.map (·[c]!)

def extOf (ch : Chip) (rows : Array (Array F)) (j e : Nat) : E3 :=
  ⟨rows[j]![ch.baseCols + 3 * e]!, rows[j]![ch.baseCols + 3 * e + 1]!, rows[j]![ch.baseCols + 3 * e + 2]!⟩

def findChip (all : Array (Chip × Tr)) (id : String) : Option (Chip × Tr) := all.find? (·.1.id == id)

/-- fill round `stage` of chip `idx` of `all` (the earlier chips of the batch are already filled for this stage) -/
def fillStage (all : Array (Chip × Tr)) (idx stage : Nat) (frame : Array E3) (ders : Array Der) : IO (Chip × Tr) := do
  let (ch, tr) := all[idx]!
  let slots := completeSlots frame ders
  let rows := rowsOf tr
  let real := rows.size
  let mut pub := tr.pub
  if (ch.id == "computeChipVCLHX" || ch.id == "computeChipVCLHX9") && pub.size ≥ 12 then
    let d := computeDerived (pub.extract 0 6) slots
    for k in [0:6] do pub := pub.set! (6 + k) d[k]!
  let mut hints := hintsFor ch.id
  if stage == 1 then
    if ch.id == "cellChipHQKW" then
      if let some (ach, atr) := findChip all "atomChipHQL" then
        let arows := rowsOf atr
        let byIdx := rowMap arows 2
        let z := #[slots[2]!, slots[3]!]
        for r in [0:real] do
          for (kb, ptr, base) in [(130, 3, 6), (131, 4, 12)] do
            if rows[r]![kb]! != 1 then continue
            let some j := byIdx.get? rows[r]![ptr]!.toNat | continue
            hints := { hints with seeds := hints.seeds ++ #[(r, base, z[0]!), (r, base + 1, z[1]!), (r, base + 2, E3.zero),
              (r, base + 3, E3.zero), (r, base + 4, extOf ach arows j 4), (r, base + 5, extOf ach arows j 5)] }
    let src? := match ch.id with | "walkChipJ8" => some "cellChipHQKW" | "walkChipHQK" => some "atomChipHQL" | _ => none
    if let some sid := src? then
      let some (sch, strc) := findChip all sid | throw (IO.userError s!"{sid} must be in the batch before {ch.id}")
      let srows := rowsOf strc
      let byIdx := rowMap srows 2
      for r in [0:real] do
        if let some j := byIdx.get? rows[r]![3]!.toNat then
          for e in [0:18] do hints := { hints with seeds := hints.seeds.push (r, e, extOf sch srows j e) }
        if let some j := byIdx.get? rows[r]![5]!.toNat then
          for e in [0:6] do hints := { hints with seeds := hints.seeds.push (r, 18 + e, extOf sch srows j e) }
  let (rows', un) ← fillAux ch hints rows slots pub stage
  let nExt := (ch.width - ch.baseCols) / 3
  let hasR2 := (List.range nExt).any fun e => ch.colRound[ch.baseCols + 3 * e]! == 2
  if stage == 2 || !hasR2 then pub := fillPublics ch rows' slots pub
  logMsgA s!"aux fill {ch.id} stage {stage}: {real} rows, unsolved {un}"
  return (ch, { tr with cols := colsOf rows' ch.width, pub := pub })
where
  logMsgA (s : String) : IO Unit := IO.eprintln s

/-- zero the round>=1 columns (so nothing of the fixture's aux leaks into an own-coin run) -/
def stripAux (ch : Chip) (tr : Tr) : Tr :=
  { tr with cols := (Array.range ch.width).map fun c => if ch.colRound[c]! == 0 then tr.cols[c]! else Array.replicate tr.nRows 0 }

end NockvmE2E.Exec.Aux
