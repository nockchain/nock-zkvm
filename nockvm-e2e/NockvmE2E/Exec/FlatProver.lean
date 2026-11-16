/-
  NockvmE2E/Exec/FlatProver.lean   (UNTRUSTED, executed, no proofs)

  The prover that emits exactly the `FlatProof` + `ExecInst` that `Exec/Verify.lean` (`verifyFlat`) reads: D1-D12
  plus L1-L3 of the format notes.  ONE proof for ALL tables: one transcript, one aux fill under the shared coins, each table interpolated
  on its own prefix of the one orbit, one LDE domain for the largest table, quotient = Σ_t S_t / Z_{H_t}.  Shared with the verifier by import: `ragSpec/friSpec/treeSel/blockLayout/
  openPts/openingList/deepWord/foldK3/yAt/roundNl/deepMsg` (so the layout cannot drift).  Hash = `Tip5Core`.
-/
import NockvmE2E.Exec.Verify
import NockvmE2E.Exec.J8ShapeB
import NockvmE2E.Exec.AuxFill
import NockvmE2E.Exec.VChip
import NockvmE2E.Exec.Tip5Core
import NockvmE2E.Exec.PubExe
import NockvmE2E.Exec.ZBind
import NockvmE2E.Exec.FlatF
import NockvmE2E.Exec.PubExe9L
import NockvmE2E.Exec.Tip5Fast  -- B-T5F: @[csimp] fast Tip5 for compiled code
set_option autoImplicit false

namespace NockvmE2E.Exec.FP
open Lean NockvmE2E.Exec.J NockvmE2E.Exec.Tr NockvmE2E.Exec.Aux

abbrev G := UInt64
abbrev Dg5 := List Nat

def e3ofk (x : VF.K3) : PF.E3 := ⟨x.c0, x.c1, x.c2⟩
def k3ofe (x : PF.E3) : VF.K3 := ⟨x.a, x.b, x.c⟩

def tip5H : V.HFn := Tip5Core.hashVarlen
/-- same text as `VerifyMain.tip5FS` -/
def tip5FS : V.FSFn := fun key nl =>
  match key with
  | [] => []
  | z :: ms =>
    Tip5Core.squeeze (ms.foldl (fun s m => Tip5Core.absorb s Tip5Core.tMsg m)
      (Tip5Core.absorb (Tip5Core.hashVarlen [Tip5Core.tIni]) Tip5Core.tIn z)) nl

def logMsg (s : String) : IO Unit := do IO.eprintln s!"[{← IO.monoMsNow}ms] {s}"
def strLimbs (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)
def log2Ceil (n : Nat) : Nat := Id.run do
  let mut h := 0
  while 2 ^ h < n do h := h + 1
  return h

/-- pure parallel map over `[0, n)` in chunks (hashing is the cost) -/
def parRange {α : Type} [Inhabited α] (n chunk : Nat) (f : Nat → α) : Array α := Id.run do
  let nch := (n + chunk - 1) / chunk
  let tasks := (Array.range nch).map fun ci =>
    Task.spawn fun _ => (Array.range (min chunk (n - ci * chunk))).map fun i => f (ci * chunk + i)
  return tasks.foldl (fun acc t => acc ++ t.get) #[]

/-! ## chip transform (L3): the instance DAG the verifier loads -/

def kindName : Nat → String | 0 => "trace_cur" | 1 => "trace_next" | _ => "public_val"

partial def exJ : Ex → Json
  | .ref i => Json.mkObj [("ref", natJ i)]
  | .var k i => Json.mkObj [("var", Json.mkObj [("kind", Json.str (kindName k)), ("index", natJ i)])]
  | .cF v => Json.mkObj [("const_f", Json.str (toString v.toNat))]
  | .add a b => Json.mkObj [("add", Json.arr #[exJ a, exJ b])]
  | .sub a b => Json.mkObj [("sub", Json.arr #[exJ a, exJ b])]
  | .mul a b => Json.mkObj [("mul", Json.arr #[exJ a, exJ b])]
  | .neg a => Json.mkObj [("neg", exJ a)]
  | .pow a n => Json.mkObj [("pow", Json.arr #[exJ a, natJ n])]
  | .extVar k e => Json.mkObj [("ext_var", Json.mkObj [("kind", Json.str (kindName k)), ("ext_index", natJ e)])]
  | .chal i => Json.mkObj [("ext_chal", Json.mkObj [("index", natJ i)])]

/-- The verifier's chip: coin slots renumbered to `after0 ++ after1`; the gamma'-power derived slots (K' powers) expanded to DAG nodes
over the coins (the verifier's `derived` is `VF.K3.pow`, which is not that); B3V-2: the emitted gates are used VERBATIM, no synthetic isLast column and no `(1 - isLast)` factor:
every gate must hold on all of `H_t` with the EXTRAPOLATED next value at the last row. Returns the chip and the max degree.
Since  this is `VC.verifierChipT` (Exec/VChip.lean: pure, structural, Mathlib-free), whose semantics is proved in `Exec/DagSemV.lean`
(`evalDagK_verifierChipT`); the chip JSON written is byte-identical to the former imperative `verifierChip`. -/
def verifierChip (ch : Chip) (ders : Array Der) (coinMeta : Array (Nat × Nat)) : Chip × Nat := VC.verifierChipT ch ders coinMeta

def chipJson (ch : Chip) (colRound : Array Nat) : Json :=
  let cols := (Array.range ch.width).map fun c =>
    Json.mkObj [("round", natJ (colRound.getD c 0)), ("field", Json.mkObj [("base", Json.bool (c < ch.baseCols))])]
  Json.mkObj [("chips", Json.arr #[Json.mkObj [
    ("id", Json.str ch.id), ("shared", Json.arr (ch.shared.map exJ)),
    ("constraints", Json.arr (ch.cons.map fun c =>
      Json.mkObj [("kind", Json.str (if c.kind == 0 then "row" else "transition")), ("round", natJ c.round),
                  ("degree", natJ c.deg), ("expr", exJ c.e)])),
    ("columns", Json.arr cols)]])]

/-! ## interpolation on the n real nodes -/

def interpBasis (nodes : Array G) : Array (Array G) := Id.run do
  let n := nodes.size
  let mut z : Array G := #[1]
  for a in nodes do
    let mut nz : Array G := Array.replicate (z.size + 1) 0
    for i in [0:z.size] do
      nz := nz.modify (i + 1) (PF.add · z[i]!)
      nz := nz.modify i (PF.sub · (PF.mul a z[i]!))
    z := nz
  let mut out : Array (Array G) := Array.mkEmpty n
  for i in [0:n] do
    let a := nodes[i]!
    let mut q : Array G := Array.replicate n 0
    q := q.set! (n - 1) z[n]!
    for t in [0:n - 1] do
      let k := n - 1 - t
      q := q.set! (k - 1) (PF.add z[k]! (PF.mul a q[k]!))
    let mut ev : G := 0
    for t in [0:n] do ev := PF.add (PF.mul ev a) q[n - 1 - t]!
    let w := PF.inv ev
    out := out.push (q.map (PF.mul w))
  return out

def polyAddG (a b : Array G) : Array G :=
  (Array.range (max a.size b.size)).map fun i => PF.add (a.getD i 0) (b.getD i 0)

def interpCol (basis : Array (Array G)) (y : Array G) : Array G := Id.run do
  let n := y.size
  let mut acc : Array G := Array.replicate n 0
  for i in [0:n] do
    let yi := y[i]!
    if yi != 0 then
      let bi := basis[i]!
      for k in [0:n] do acc := acc.modify k (PF.add · (PF.mul yi bi[k]!))
  return acc

/-! ## preprocessed (kind 1) columns, B3V-2 -/

/-- local indices of the preprocessed columns of a chip (kind 1):
compute {17 firstRowMask, 18 lastRowMask}; cell, atom {0, 1}; walk chips {0 firstRowMask, 1 lastRowMask, 2 rootRowMaskW nodes kroots};
jet {0..17} = interpolated registry layout `jetPre`. -/
def preIdxOf (id : String) : Array Nat :=
  -- P9: the three J-9 A chips (= `J9AChips.preIdx9`; equality kernel-checked in `ProverFamCheck`); every J-8 id is untouched
  if id == "computeChipVCLHX9" then #[17, 18]
  else if id == "axisChipJ9" || id == "splitChipJ9" then #[0, 1]
  else if id == "aluChipJ9" then #[0, 1, 2, 3, 4]   -- masks 0, 1 and the preg layout sP, pId, pOp (2..4, from the trace)
  else NockvmE2E.Exec.J8Shape.preIdxJ8 id  -- single source of truth, shared with `j8ShapeOk.preKindOk`

/-- the expected 0/1 row pattern of a mask column (`none` for the jet registry columns, whose values come from the trace: TCB) -/
def preVals (id : String) (pos n kroots : Nat) : Option (Array G) :=
  if id == "jetChipJ8" then none
  else if id == "aluChipJ9" && pos ≥ 2 then none
  else if pos == 0 then some ((Array.range n).map fun i => if i == 0 then 1 else 0)
  else if pos == 1 then some ((Array.range n).map fun i => if i == n - 1 then 1 else 0)
  else some ((Array.range n).map fun i => if i < kroots then 1 else 0)

/-! ## Merkle (shape of `Verify.lean`) -/

def levelsUp (j : Nat) (bot : Array Dg5) (m : Nat) : Array (Array Dg5) := Id.run do
  let mut lv : Array (Array Dg5) := Array.replicate (m + 1) #[]
  lv := lv.set! m bot
  for t in [0:m] do
    let d := m - 1 - t
    let ch := lv[d + 1]!
    lv := lv.set! d (parRange (2 ^ d) 256 fun i => tip5H ([V.tagNode, j, 2 ^ d + i] ++ ch[2 * i]! ++ ch[2 * i + 1]!))
  return lv

partial def subRoot (j : Nat) (leafAt : Nat → G) (idx cnt lo : Nat) : Dg5 :=
  if cnt == 1 then [(leafAt lo).toNat, 0, 0, 0, 0] else
  let L := (cnt + 1) / 2
  tip5H ([V.tagNode, j, idx] ++ subRoot j leafAt (2 * idx) L lo ++ subRoot j leafAt (2 * idx + 1) (cnt - L) (lo + L))

/-- RAP block tree: `half` groups, each = two balanced sub-trees of `W` leaves (side 0 = index g, side 1 = g + half) -/
def ragLevels (j W half : Nat) (cols : Array Nat) (lde : Array (Array G)) : Array (Array Dg5) :=
  let groups := parRange half 8 fun g =>
    let side (s : Nat) : Dg5 :=
      subRoot j (fun r => (lde[cols[r]!]!)[g + s * half]!) (2 * (half + g) + s) W 0
    tip5H ([V.tagNode, j, half + g] ++ side 0 ++ side 1)
  levelsUp j groups (Nat.log2 half)

partial def openGo (sp : V.TSpec) (nodeAt : Nat → Dg5) (sel : Array Nat) (idx lo cnt : Nat) : Array Dg5 :=
  if cnt == 1 then #[] else
  let L := sp.split cnt
  let a := V.lb sel lo
  let b := V.lb sel (lo + L)
  let c := V.lb sel (lo + cnt)
  if b > a && c > b then openGo sp nodeAt sel (2 * idx) lo L ++ openGo sp nodeAt sel (2 * idx + 1) (lo + L) (cnt - L)
  else if b > a then #[nodeAt (2 * idx + 1)] ++ openGo sp nodeAt sel (2 * idx) lo L
  else #[nodeAt (2 * idx)] ++ openGo sp nodeAt sel (2 * idx + 1) (lo + L) (cnt - L)

def nodeAtLv (lv : Array (Array Dg5)) (idx : Nat) : Dg5 :=
  let d := Nat.log2 idx
  (lv[d]!)[idx - 2 ^ d]!

/-! ## claims (L1) -/

def frameOf (vals : List (Nat × PF.E3)) : Array PF.E3 := Id.run do
  let mut a : Array PF.E3 := Array.replicate 64 PF.E3.zero
  for (i, v) in vals do a := a.set! i v
  return a

def fillAll (cur0 : Array (Chip × Tr)) (ders : Array Der) (stage : Nat) (frame : Array PF.E3) : IO (Array (Chip × Tr)) := do
  let mut cur := cur0
  -- P10: the atom table is filled FIRST (the cell chip's big-atom seeds read the atom table's round-1 columns; the walk-atom chip's too);
  -- the others keep their natural order.  Tables keep their index, so the layout is unchanged.
  let atomIdx := (Array.range cur.size).filter fun i => cur[i]!.1.id == "atomChipHQL"
  let order := atomIdx ++ (Array.range cur.size).filter fun i => cur[i]!.1.id != "atomChipHQL"
  for i in order do cur := cur.set! i (← fillStage cur i stage frame ders)
  return cur

/-- an external staged tracegen.  `stage r f cur` returns the tables with the round-`r` columns (r = 1, 2; plus the publics at r = 2)
filled at the coin frame `f` (`framesOf` layout), in place of the generic solver `fillAll`.  `none` everywhere = today's code path. -/
structure StageSrc where
  stage : Nat → Array PF.E3 → Array (Chip × Tr) → IO (Array (Chip × Tr))

/-- the aux fill of stage `stage`: the generic solver unless a `StageSrc` is given -/
def fillWith (src : Option StageSrc) (cur : Array (Chip × Tr)) (ders : Array Der) (stage : Nat) (frame : Array PF.E3) : IO (Array (Chip × Tr)) :=
  match src with
  | none => fillAll cur ders stage frame
  | some s => s.stage stage frame cur

/-- coin frames from the coin values (positions in `after0 ++ after1` order) -/
def framesOf (coinMeta : Array (Nat × Nat)) (v0 v1 : Array PF.E3) : Array PF.E3 × Array PF.E3 :=
  let a0 := coinMeta.filter (·.2 == 0)
  let a1 := coinMeta.filter (·.2 != 0)
  let f1 := frameOf ((List.range a0.size).map fun k => (a0[k]!.1, v0[k]!))
  let f2 := (List.range a1.size).foldl (fun f k => f.set! a1[k]!.1 v1[k]!) f1
  (f1, f2)

/-- claim slots of EVERY table: public slots the in-prover fill leaves at their input value under a dummy coin frame -/
def claimMasks (act : Array (Chip × Tr)) (ders : Array Der) (coinMeta : Array (Nat × Nat)) (src : Option StageSrc := none) : IO (Array (Array Bool)) := do
  let a0 := coinMeta.filter (·.2 == 0)
  let a1 := coinMeta.filter (·.2 != 0)
  let v0 : Array PF.E3 := (Array.range a0.size).map fun k => ⟨UInt64.ofNat (1000 + 17 * k), UInt64.ofNat (2000 + 31 * k), 3000 + 7 * UInt64.ofNat k⟩
  let v1 : Array PF.E3 := (Array.range a1.size).map fun k => ⟨UInt64.ofNat (5000 + 13 * k), UInt64.ofNat (6000 + 29 * k), 7000 + 11 * UInt64.ofNat k⟩
  let (f1, f2) := framesOf coinMeta v0 v1
  let mut cur : Array (Chip × Tr) := act.map fun (ch, tr) => (ch, stripAux ch tr)
  cur ← fillWith src cur ders 1 f1
  cur ← fillWith src cur ders 2 f2
  return (Array.range act.size).map fun i =>
    let p0 := act[i]!.2.pub
    let p1 := cur[i]!.2.pub
    (Array.range p0.size).map fun s => p0[s]! == p1[s]!

/-! ## the prover: ALL tables in one proof -/

structure Result where
  π : V.FlatProof
  X : V.ExecInst
  z : List Nat
  notes : Array String
  ok : Bool
  slotOf : Array Nat
  pubsT : Array (Array G) := #[]   -- P10 debug: the filled publics of each table
  frame2 : Array PF.E3 := #[]      -- P10 debug: the full coin frame (own Fiat-Shamir coins)

/-- P9: the prover-side data of a chip family (the Mathlib-free mirror of `ShapeF.Fam`; `ProverFamCheck` proves `famP8`/`famP9A` agree with `famJ8`/`famJ9A`) -/
structure FamP where
  name : String
  ids : List String
  tabOf : String → Option Nat
  tabLens : Array Nat
  pubMode : Nat

def famP8 : FamP :=
  { name := "j8", ids := ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "jetChipJ8", "atomChipHQL", "walkChipHQK"],
    tabOf := PE.tabOfId, tabLens := PE.tabLens, pubMode := 0 }

def tabOfP9 (id : String) : Option Nat :=
  if id == "computeChipVCLHX9" then some 0 else if id == "cellChipHQKW" then some 1 else if id == "walkChipJ8" then some 2
  else if id == "jetChipJ8" then some 3 else if id == "atomChipHQL" then some 4 else if id == "walkChipHQK" then some 5
  else if id == "axisChipJ9" then some 6 else if id == "splitChipJ9" then some 7 else none

def famP9A : FamP :=
  { name := "j9a", ids := ["computeChipVCLHX9", "cellChipHQKW", "walkChipJ8", "jetChipJ8", "atomChipHQL", "walkChipHQK", "axisChipJ9", "splitChipJ9"],
    tabOf := tabOfP9, tabLens := PE.tabLens9, pubMode := 2 }

/-- the J-9 AL family = `famP9A` + the ALU table 8 (`ProverFamCheck` mirrors `famJ9AL`) -/
def tabOfP9AL (id : String) : Option Nat := if id == "aluChipJ9" then some 8 else tabOfP9 id

def famP9AL : FamP :=
  { name := "j9al", ids := famP9A.ids ++ ["aluChipJ9"], tabOf := tabOfP9AL, tabLens := PE.tabLens9L, pubMode := 3 }

def famP? : String → Option FamP
  | "j8" => some famP8
  | "j9a" => some famP9A
  | "j9al" => some famP9AL
  | _ => none

/-- `tamperPub = some (t, s)`: after the fill, table `t`'s public slot `s` is changed by 1 BEFORE it is committed (a consistent forged proof; the
in-prover self-check then reports REJECT).  `tamperPre = some (t, c, row)`: table `t`'s preprocessed column `c` (local) is changed by 1 at `row`
BEFORE commitment (the committed/opened column differs from the instance's `pre`; the quotient is built from the honest column, so the
proof is otherwise consistent).  `kootsOf id` = the run's `kroots` for walk chip `id`.  `chipPath t` = where table `t`'s verifier DAG is written. -/
def proveAll (act0 : Array (Chip × Tr)) (ders : Array Der) (coinMeta : Array (Nat × Nat)) (prog : String)
    (chipPath : Nat → String) (nQ : Nat) (pubIn : PE.PubIn) (tamperPub : Option (Nat × Nat)) (kootsOf : String → Nat)
    (tamperPre : Option (Nat × Nat × Nat) := none) (fam : FamP := famP8) (aluDers : Array Der := #[]) (stageSrc : Option StageSrc := none) (bindPub : Bool := false) : IO Result := do
  -- `aluDers` (non-empty only for j9al) = `jDers ++ yDers`: used for the fill and the own slots of every table (a superset of `ders`, so the other
  -- tables are unaffected) and for the verifier chip of the ALU ONLY (every other verifier chip keeps `ders`, so its literal is unchanged)
  let dersF : Array Der := if aluDers.isEmpty then ders else aluDers
  let dersOf (id : String) : Array Der := if id == "aluChipJ9" then dersF else ders
  let mut notes : Array String := #[]
  let mut ok := true
  let T := act0.size
  let ns : Array Nat := act0.map (·.2.nRows)
  let Ws : Array Nat := act0.map (·.1.width)
  let npubs : Array Nat := act0.map (·.2.pub.size)
  let hMax := ns.foldl max 1
  let h' := log2Ceil hMax
  let kp1 := max 1 h'
  -- the UNION domain is padded to a power of two (|H| = 2^(k+1)); every H_t keeps its real n_t rows
  let hN := 2 ^ kp1
  let nD := kp1 + 6
  let Dn := 2 ^ nD
  let half0 := Dn / 2
  let k := kp1 - 1
  -- hGen has EXACT order 3·2^kp1 (J-8's `StrictOrbitDomain _ 3 h`, h = kp1): `hGen = (2^kp1-th root) · ω₃`, `ω₃ = 7^((p-1)/3)` a primitive cube root of 1
  let omega3 : G := PF.pow PF.seven ((PF.P.toNat - 1) / 3)
  let hGen := PF.mul (PF.root kp1) omega3
  let hShift : G := 1
  let dGen := PF.root nD
  let dShift : G := 7
  -- every table: its own H_t = the first n_t points of the ONE orbit {hShift * hGen^i}
  let orbit : Array G := Id.run do
    let mut a : Array G := #[]
    let mut x : G := hShift
    for _ in [0:hN] do
      a := a.push x
      x := PF.mul x hGen
    return a
  let nodesT : Array (Array G) := ns.map fun n => orbit.extract 0 n
  let basisT : Array (Array (Array G)) := nodesT.map interpBasis
  logMsg s!"{T} tables: n={ns} width={Ws} pubs={npubs}; |H|={hN} h'={h'} |D|=2^{nD} k={k}"
  -- layout
  let ncT : Array Nat := (Array.range T).map fun t => Ws[t]! + npubs[t]!
  let col0T : Array Nat := (ncT.foldl (fun (st : Array Nat × Nat) c => (st.1.push st.2, st.2 + c)) (#[], 0)).1
  let pubBaseT : Array Nat := (npubs.foldl (fun (st : Array Nat × Nat) c => (st.1.push st.2, st.2 + c)) (#[], 0)).1
  let nc := ncT.foldl (· + ·) 0
  -- L1: statement with the claims
  let masks ← claimMasks act0 dersF coinMeta stageSrc
  logMsg "  PROFILE claim-mask dummy fill (stage 1+2) done"
  -- S1: `bindPub` (j9al / j9alj drivers) prefixes the statement with `zHdr pubIn` (Exec/ZBind.lean), which the verdicts `verdict9LVB` / `verdict9LJVB` check
  let z : List Nat := (if bindPub then NockvmE2E.Exec.ZBind.zHdr pubIn else []) ++ strLimbs prog ++ [0, T] ++ (List.range T).flatMap fun t =>
    let claimsL := (List.range npubs[t]!).flatMap fun s => if masks[t]![s]! then [s, act0[t]!.2.pub[s]!.toNat] else []
    strLimbs act0[t]!.1.id ++ [0, ns[t]!, npubs[t]!] ++ claimsL
  -- chips for the verifier (L3)
  let a0 := coinMeta.filter (·.2 == 0)
  let a1 := coinMeta.filter (·.2 != 0)
  let n0 := a0.size
  let n1 := a1.size
  let order : Array Nat := a0.map (·.1) ++ a1.map (·.1)
  let slotOf : Array Nat := (Array.range 19).map fun i => (order.findIdx? (· == i)).getD 0
  let mut chVs : Array Chip := #[]
  let mut dmaxs : Array Nat := #[]
  for t in [0:T] do
    let (chV0, dmax) := verifierChip act0[t]!.1 (dersOf act0[t]!.1.id) coinMeta
    IO.FS.writeFile (chipPath t) (chipJson chV0 act0[t]!.1.colRound).compress
    chVs := chVs.push (← loadChip (chipPath t))
    dmaxs := dmaxs.push dmax
  let nCh := dmaxs.foldl max 1 - 1
  let nq := 3 * nCh
  let ncq := nc + nq
  let colKind : Array Nat := (Array.range T).flatMap fun t =>
    (Array.range ncT[t]!).map fun c => if c < Ws[t]! then (if (preIdxOf act0[t]!.1.id).contains c then 1 else 0) else 2
  let blockOf : Array Nat := ((Array.range T).flatMap fun t =>
    (Array.range ncT[t]!).map fun c =>
      if c < Ws[t]! then act0[t]!.1.colRound[c]! else 2) ++ Array.replicate nq 3
  -- preprocessed columns: masks from n_t (and the run's kroots for walk col 2); the jet columns from the trace (TCB: the instance is trusted, like the chips)
  let preOf (t : Nat) (c : Nat) : Array G :=
    let id := act0[t]!.1.id
    match (preIdxOf id).findIdx? (· == c) with
    | none => #[]
    | some pos => match preVals id pos ns[t]! (kootsOf id) with
      | some v => interpCol basisT[t]! v
      | none => interpCol basisT[t]! (act0[t]!.2.cols[c]!)
  for t in [0:T] do
    for c in preIdxOf act0[t]!.1.id do
      match preVals act0[t]!.1.id ((preIdxOf act0[t]!.1.id).findIdx? (· == c) |>.getD 0) ns[t]! (kootsOf act0[t]!.1.id) with
      | some v =>
        if v != act0[t]!.2.cols[c]! then
          notes := notes.push s!"PRE MISMATCH: table {t} column {c}: trace differs from the expected mask"; ok := false
      | none => pure ()
      if act0[t]!.1.colRound[c]! != 0 then
        notes := notes.push s!"PRE ROUND: table {t} column {c} is not round 0"; ok := false
  let preHon : Array (Array G) := (Array.range T).flatMap fun t => (Array.range ncT[t]!).map fun c => preOf t c
  let pre : Array (Array G) := preHon
  let pubOf : Array Nat := (Array.range T).flatMap fun t => (Array.range npubs[t]!).map fun s => col0T[t]! + Ws[t]! + s
  let ppt : VF.K3 := ⟨11, 5, 2⟩
  let tabs : Array V.TabInst := (Array.range T).map fun t =>
    { hN := ns[t]!, col0 := col0T[t]!, nc := ncT[t]!, npub := npubs[t]!, pubBase := pubBaseT[t]!, chip := chVs[t]! }
  let layout ← match FlatF.layoutOfTabsF fam.tabOf fam.tabLens tabs with
    | .ok l => pure l
    | .error e => throw (IO.userError e)
  let X : V.ExecInst :=
    { nD := nD, dShift := dShift, dGen := dGen, hN := hN, hGen := hGen, hShift := hShift, r := 2, k := k, d := 1, l := nQ
      nc := nc, nq := nq, colKind := colKind, blockOf := blockOf, pre := pre, pubOf := pubOf, ppt := ppt, nCoins := #[n0, n1],
      derived := #[], tabs := tabs, pubIn := pubIn, pubLay := layout, slotOf := slotOf, pubMode := fam.pubMode }
  let (blW, _) := V.blockLayout X
  let bcols : Array (Array Nat) := (Array.range 4).map fun b =>
    (Array.range ncq).filter fun c => blockOf[c]! == b
  -- state
  let mut coefs : Array (Array G) := Array.replicate ncq #[]
  let mut lde : Array (Array G) := Array.replicate ncq #[]
  let ldeOf (cf : Array G) : Array G := PF.cosetLde cf nD dGen
  let mut cur : Array (Chip × Tr) := act0.map fun (c, t) => (c, stripAux c t)
  let mut msgs : Array (List Nat) := #[[]]
  let chalAt (ms : Array (List Nat)) (i nl : Nat) : List Nat := tip5FS (z :: (ms.extract 0 (i + 1)).toList) nl
  let mut levels : Array (Array (Array Dg5)) := Array.replicate 4 #[]
  let commit (b : Nat) (lde : Array (Array G)) : Dg5 × Array (Array Dg5) :=
    if blW[b]! == 0 then ([0, 0, 0, 0, 0], #[])
    else
      let lv := ragLevels (b : Nat) blW[b]! half0 bcols[b]! lde
      (lv[0]![0]!, lv)
  -- columns `locs` (local indices) of table `t`: interpolate on the table's own prefix, LDE on the one domain D
  let setColsT (t : Nat) (locs : Array Nat) (valsOf : Nat → Array G) (coefs lde : Array (Array G)) : Array (Array G) × Array (Array G) :=
    let cf := parRange locs.size 4 fun i => interpCol basisT[t]! (valsOf locs[i]!)
    let ld := cf.map ldeOf
    ((Array.range locs.size).foldl (fun a i => a.set! (col0T[t]! + locs[i]!) cf[i]!) coefs,
     (Array.range locs.size).foldl (fun a i => a.set! (col0T[t]! + locs[i]!) ld[i]!) lde)
  -- round 0 (the preprocessed columns are committed from the LDE of `X.pre`, not of the trace column)
  for t in [0:T] do
    let r0 := (Array.range Ws[t]!).filter fun c => act0[t]!.1.colRound[c]! == 0 && colKind[col0T[t]! + c]! == 0
    (coefs, lde) := setColsT t r0 (fun c => cur[t]!.2.cols[c]!) coefs lde
    for c in preIdxOf act0[t]!.1.id do
      let g := col0T[t]! + c
      let mut pc := pre[g]!
      match tamperPre with
      | some (tt, tc, row) =>
        if tt == t && tc == c then
          pc := polyAddG pc (basisT[t]![row % ns[t]!]!)
          notes := notes.push s!"TAMPER: table {t} preprocessed column {c} row {row} += 1 before commitment"
      | none => pure ()
      coefs := coefs.set! g pc
      lde := lde.set! g (ldeOf pc)
  logMsg "  PROFILE block0: interpolate+LDE done"
  let (root0, lv0) := commit 0 lde
  levels := levels.set! 0 lv0
  msgs := msgs.push root0
  logMsg s!"  block 0 committed ({blW[0]!} cols)"
  -- coins0, ONE fill of all tables under the shared coins, stage 1
  let c0l := chalAt msgs 1 (3 * n0)
  let v0 : Array PF.E3 := (Array.range n0).map fun p => ⟨UInt64.ofNat c0l[3 * p]!, UInt64.ofNat c0l[3 * p + 1]!, UInt64.ofNat c0l[3 * p + 2]!⟩
  let (f1, _) := framesOf coinMeta v0 (Array.replicate n1 PF.E3.zero)
  cur ← fillWith stageSrc cur dersF 1 f1
  logMsg "  PROFILE aux fill stage 1 done"
  -- round 1
  for t in [0:T] do
    let r1 := (Array.range Ws[t]!).filter fun c => act0[t]!.1.colRound[c]! == 1 && colKind[col0T[t]! + c]! == 0
    (coefs, lde) := setColsT t r1 (fun c => cur[t]!.2.cols[c]!) coefs lde
  logMsg "  PROFILE block1: interpolate+LDE done"
  let (root1, lv1) := commit 1 lde
  levels := levels.set! 1 lv1
  msgs := msgs.push root1
  logMsg s!"  block 1 committed ({blW[1]!} cols)"
  let c1l := chalAt msgs 2 (3 * n1)
  let v1 : Array PF.E3 := (Array.range n1).map fun p => ⟨UInt64.ofNat c1l[3 * p]!, UInt64.ofNat c1l[3 * p + 1]!, UInt64.ofNat c1l[3 * p + 2]!⟩
  let (_, f2) := framesOf coinMeta v0 v1
  cur ← fillWith stageSrc cur dersF 2 f2
  logMsg "  PROFILE aux fill stage 2 done"
  let slotsOwn := completeSlots f2 dersF
  -- round 2 + public columns
  let mut pubsT : Array (Array G) := #[]
  for t in [0:T] do
    let mut trF := cur[t]!.2
    match tamperPub with
    | some (tt, sl) =>
      if tt == t then
        trF := { trF with pub := trF.pub.modify sl (· + 1) }
        notes := notes.push s!"TAMPER: table {t} public slot {sl} += 1 before commitment"
    | none => pure ()
    let r2 := (Array.range Ws[t]!).filter fun c => act0[t]!.1.colRound[c]! == 2 && colKind[col0T[t]! + c]! == 0
    (coefs, lde) := setColsT t r2 (fun c => trF.cols[c]!) coefs lde
    for s in [0:npubs[t]!] do
      coefs := coefs.set! (col0T[t]! + Ws[t]! + s) #[trF.pub[s]!]
      lde := lde.set! (col0T[t]! + Ws[t]! + s) (Array.replicate Dn trF.pub[s]!)
      if masks[t]![s]! && trF.pub[s]! != act0[t]!.2.pub[s]! then
        notes := notes.push s!"CLAIM slot {s} of table {t} changed by the fill"; ok := false
    -- (a) row check of the trace the fill produced (checker semantics) with the original DAG
    match rowCheck act0[t]!.1 trF slotsOwn with
    | some (c, r) => notes := notes.push s!"(a) table {t} ROW CHECK FAILED: constraint {c} row {r}"; ok := false
    | none => notes := notes.push s!"(a) table {t} rowcheck (checker semantics): ok"
    pubsT := pubsT.push trF.pub
  logMsg "  PROFILE block2: interpolate+LDE+rowchecks done"
  let (root2, lv2) := commit 2 lde
  levels := levels.set! 2 lv2
  msgs := msgs.push root2
  logMsg s!"  block 2 committed ({blW[2]!} cols incl. {npubs.foldl (· + ·) 0} public columns)"
  -- alpha, quotient on D:  Q = Σ_t (Σ_i α^{off_t+i} C_{t,i}) / Z_{H_t}   (= Σ_t S_t · mult_t / Z_H)
  let alpha := e3ofk (VF.K3.ofLimbs (chalAt msgs 3 3))
  let offT : Array Nat := (chVs.foldl (fun (st : Array Nat × Nat) c => (st.1.push st.2, st.2 + c.cons.size)) (#[], 0)).1
  let nCons := chVs.foldl (fun a c => a + c.cons.size) 0
  let apow : Array PF.E3 := Id.run do
    let mut a : Array PF.E3 := Array.mkEmpty nCons
    let mut p := PF.E3.one
    for _ in [0:nCons] do
      a := a.push p
      p := PF.E3.mul p alpha
    return a
  let slotsV : Array PF.E3 := (order.map fun i => f2[i]!)
  let ptsD : Array G := Id.run do
    let mut a : Array G := Array.mkEmpty Dn
    let mut x := dShift
    for _ in [0:Dn] do
      a := a.push x
      x := PF.mul x dGen
    return a
  -- 1 / Z_{H_t}(x) on D, once per distinct row count
  let distinctN : Array Nat := ns.foldl (fun a n => if a.contains n then a else a.push n) #[]
  let zinvByN : Array (Array G) := distinctN.map fun n =>
    let nodes := orbit.extract 0 n
    parRange Dn 64 fun i => PF.inv (nodes.foldl (fun acc a => PF.mul acc (PF.sub ptsD[i]! a)) 1)
  let zinvT : Array (Array G) := ns.map fun n => zinvByN[(distinctN.findIdx? (· == n)).getD 0]!
  -- the quotient is built from the HONEST preprocessed columns (differs from `lde` only under `--tamper-pre`)
  let ldeQ := Id.run do
    let mut l := lde
    if tamperPre.isSome then
      for t in [0:T] do
        for c in preIdxOf act0[t]!.1.id do l := l.set! (col0T[t]! + c) (ldeOf preHon[col0T[t]! + c]!)
    return l
  -- next-row values.  `hGen` is NOT in `<dGen>` (order 3·2^kp1), so `(x + shiftS) % Dn` no longer applies: evaluate each trace column at the coset `hGen·D`
  -- (coefficients scaled by `hGen^i`, then the same coset LDE on `D`); `ldeN[g][x] = col_g(hGen · ptsD[x])`
  let coefsQ : Array (Array G) := Id.run do
    let mut cq := coefs
    if tamperPre.isSome then
      for t in [0:T] do
        for c in preIdxOf act0[t]!.1.id do cq := cq.set! (col0T[t]! + c) preHon[col0T[t]! + c]!
    return cq
  let scaleH (cf : Array G) : Array G := Id.run do
    let mut o : Array G := Array.mkEmpty cf.size
    let mut s : G := 1
    for i in [0:cf.size] do
      o := o.push (PF.mul cf[i]! s)
      s := PF.mul s hGen
    return o
  let nxtCols : Array Nat := (Array.range T).flatMap fun t => (Array.range Ws[t]!).map fun c => col0T[t]! + c
  let ldeNL : Array (Array G) := parRange nxtCols.size 4 fun i => ldeOf (scaleH coefsQ[nxtCols[i]!]!)
  let ldeN : Array (Array G) := (Array.range nxtCols.size).foldl (fun a i => a.set! nxtCols[i]! ldeNL[i]!) (Array.replicate nc #[])
  logMsg "  PROFILE next-row coset LDE (hGen·D) done"
  let qrows := parRange Dn 64 fun x =>
    (List.range T).foldl (fun (acc : PF.E3) t =>
      let c0 := col0T[t]!
      let nW1 := Ws[t]!
      let curE : Array PF.E3 := (Array.range nW1).map fun c => PF.E3.ofF (ldeQ[c0 + c]!)[x]!
      let nxtE : Array PF.E3 := (Array.range nW1).map fun c => PF.E3.ofF (ldeN[c0 + c]!)[x]!
      let vals := evalCons chVs[t]! { cur := curE, next := nxtE, pub := pubsT[t]!, chal := slotsV, bc := chVs[t]!.baseCols }
      let s := Id.run do
        let mut s := PF.E3.zero
        for i in [0:vals.size] do s := PF.E3.add s (PF.E3.mul apow[offT[t]! + i]! vals[i]!)
        return s
      PF.E3.add acc (PF.E3.smul zinvT[t]![x]! s)) PF.E3.zero
  let unc (sel : PF.E3 → G) : Array G := Id.run do
    let c := PF.intt (qrows.map sel) nD dGen
    let invSeven := PF.inv 7
    let mut s : G := 1
    let mut o : Array G := Array.mkEmpty Dn
    for i in [0:Dn] do
      o := o.push (PF.mul c[i]! s)
      s := PF.mul s invSeven
    return o
  let qco := #[unc (·.a), unc (·.b), unc (·.c)]
  let high := qco.foldl (fun acc a => acc || (a.extract (nCh * hN) Dn).any (· != 0)) false
  if high then
    notes := notes.push s!"(b) QUOTIENT NOT LOW-DEGREE (bound {nCh}*{hN} violated: constraints not divisible by Z_H)"; ok := false
    -- diagnostic (failure path only): per table, the constraints whose own quotient C_{t,i}/Z_{H_t} is not low-degree
    for t in [0:T] do
      let c0 := col0T[t]!
      let nW1 := Ws[t]!
      let perX : Array (Array PF.E3) := parRange Dn 64 fun x =>
        let curE : Array PF.E3 := (Array.range nW1).map fun c => PF.E3.ofF (ldeQ[c0 + c]!)[x]!
        let nxtE : Array PF.E3 := (Array.range nW1).map fun c => PF.E3.ofF (ldeN[c0 + c]!)[x]!
        evalCons chVs[t]! { cur := curE, next := nxtE, pub := pubsT[t]!, chal := slotsV, bc := chVs[t]!.baseCols }
      let badC := (List.range chVs[t]!.cons.size).filter fun i =>
        [(·.a), (·.b), (·.c)].any fun (sel : PF.E3 → G) =>
          let cf := PF.intt ((Array.range Dn).map fun x => sel (PF.E3.smul zinvT[t]![x]! perX[x]![i]!)) nD dGen
          (cf.extract (nCh * hN) Dn).any (· != 0)
      notes := notes.push s!"DIAG table {t} ({act0[t]!.1.id}): {badC.length} of {chVs[t]!.cons.size} constraints not divisible by Z_H: {badC.take 12}"
  else notes := notes.push s!"(b) quotient degree < {nCh}*{hN}: ok (divisibility by Z_H)"
  let qidx := (Array.range nq).map (nc + ·)
  let qvals (c : Nat) : Array G := (qco[(c - nc) % 3]!).extract (((c - nc) / 3) * hN) (((c - nc) / 3 + 1) * hN)
  let qld := parRange qidx.size 4 fun t => PF.cosetLde (qvals qidx[t]!) nD dGen
  for t in [0:nq] do
    coefs := coefs.set! qidx[t]! (qvals qidx[t]!)
    lde := lde.set! qidx[t]! qld[t]!
  logMsg "  PROFILE block3: constraint eval + quotient interp/LDE done"
  let (root3, lv3) := commit 3 lde
  levels := levels.set! 3 lv3
  msgs := msgs.push root3
  logMsg s!"  block 3 (quotient, {nq} cols) committed"
  -- zeta, openings (one next-row shift omega for every table)
  let zeta := VF.K3.ofLimbs (chalAt msgs 4 3)
  let omZ := VF.K3.smul hGen zeta
  let vT : Array (Array VF.K3) := (Array.range T).flatMap fun t =>
    (Array.range ncT[t]!).map fun c =>
      match colKind[col0T[t]! + c]! with
      | 0 | 1 => #[VF.K3.hornerG coefs[col0T[t]! + c]! zeta, VF.K3.hornerG coefs[col0T[t]! + c]! omZ]
      | 2 => #[VF.K3.ofG pubsT[t]![c - Ws[t]!]!]
      | _ => #[]
  let vQ : Array VF.K3 := (Array.range nq).map fun j => VF.K3.hornerG coefs[nc + j]! zeta
  msgs := msgs.push (V.deepMsg vT vQ)
  msgs := msgs.push []
  let cs := VF.K3.ofLimbs (chalAt msgs 6 3)
  msgs := msgs.push []
  let pts := V.openPts X zeta
  let ops := V.openingList X cs vT vQ
  let ldeAll := lde
  let mut word : Array VF.K3 := parRange Dn 64 fun idx => V.deepWord X pts ops (fun c i => (ldeAll[c]!)[i]!) idx
  logMsg "  DEEP word built"
  let mut friWords : Array (Array VF.K3) := #[]
  let mut friLv : Array (Array (Array Dg5)) := #[]
  let mut alphaW := VF.K3.ofLimbs (chalAt msgs 7 3)
  for w in [0:k + 1] do
    let halfw := 2 ^ (nD - w - 1)
    let wd0 := word
    let aw := alphaW
    let nxt : Array VF.K3 := parRange halfw 256 fun g => V.foldK3 wd0[g]! wd0[g + halfw]! (V.yAt X w g) aw
    word := nxt
    if w < k then
      let wd := word
      let hf := halfw / 2
      let leaves : Array Dg5 := parRange halfw 256 fun p => (wd[p / 2 + (p % 2) * hf]!).limbs ++ [0, 0]
      let lv := levelsUp (4 + w) leaves (nD - w - 1)
      friWords := friWords.push wd
      friLv := friLv.push lv
      msgs := msgs.push lv[0]![0]!
      alphaW := VF.K3.ofLimbs (chalAt msgs (8 + w) 3)
  let cst := word[0]!
  if word.any (· != cst) then
    notes := notes.push "FRI FINAL WORD NOT CONSTANT (batched word not low-degree)"; ok := false
  let pfinal : Array VF.K3 := #[cst]
  msgs := msgs.push (pfinal.toList.flatMap VF.K3.limbs)
  logMsg s!"  FRI done ({k + 1} folds)"
  let pos : Array Nat := (chalAt msgs (8 + k) nQ).toArray.map (· % Dn)
  -- openings
  let mut vals : Array (Array Nat) := #[]
  let mut sibs : Array (Array Dg5) := #[]
  for j in [0:4 + k] do
    let sel := V.treeSel X (blW.getD j 0) j pos
    if j < 4 then
      if blW[j]! == 0 then
        vals := vals.push #[]; sibs := sibs.push #[]
      else
        let Wb := blW[j]!
        vals := vals.push (sel.map fun p => (lde[bcols[j]![(p % (2 * Wb)) % Wb]!]!)[p / (2 * Wb) + ((p % (2 * Wb)) / Wb) * half0]!.toNat)
        let lv := levels[j]!
        sibs := sibs.push (openGo (V.ragSpec Wb half0) (nodeAtLv lv) sel 1 0 (V.ragSpec Wb half0).total)
    else
      let w := j - 4
      let wd := friWords[w]!
      let hf := 2 ^ (nD - w - 2)
      vals := vals.push (sel.flatMap fun p => ((wd[p / 2 + (p % 2) * hf]!).limbs).toArray)
      let lv := friLv[w]!
      let sp := V.friSpec (2 ^ (nD - w - 1))
      sibs := sibs.push (openGo sp (nodeAtLv lv) sel 1 0 sp.total)
  let roots : Array Dg5 := #[msgs[1]!, msgs[2]!, msgs[3]!, msgs[4]!] ++ msgs.extract 8 (8 + k)
  let π : V.FlatProof := { roots := roots, vT := vT, vQ := vQ, pfinal := pfinal, pos := pos, vals := vals, sibs := sibs }
  -- self-check with the verifier of record
  match V.verifyFlatE X tip5H tip5FS z π with
  | .ok _ => notes := notes.push "(v) verifyFlatE (in-process): ACCEPT"
  | .error e => notes := notes.push s!"(v) verifyFlatE (in-process): REJECT ({e})"; ok := false
  return { π := π, X := X, z := z, notes := notes, ok := ok, slotOf := slotOf, pubsT := pubsT, frame2 := f2 }

/-! ## instance JSON -/
def instJson (X : V.ExecInst) (chipPaths : Array String) (pubIn : PE.PubIn) (slotOf : Array Nat) : Json :=
  Json.mkObj [
    ("nD", natJ X.nD), ("dShift", natJ X.dShift.toNat), ("dGen", natJ X.dGen.toNat),
    ("hN", natJ X.hN), ("hGen", natJ X.hGen.toNat), ("hShift", natJ X.hShift.toNat),
    ("r", natJ X.r), ("k", natJ X.k), ("d", natJ X.d), ("l", natJ X.l), ("nc", natJ X.nc), ("nq", natJ X.nq),
    ("colKind", Json.arr (X.colKind.map natJ)), ("blockOf", Json.arr (X.blockOf.map natJ)),
    ("pre", Json.arr (X.pre.map fun a => Json.arr (a.map fun g => natJ g.toNat))),
    ("pubOf", Json.arr (X.pubOf.map natJ)), ("ppt", V.k3J X.ppt), ("nCoins", Json.arr (X.nCoins.map natJ)),
    ("derived", Json.arr #[]),
    ("tabs", Json.arr ((X.tabs.zip chipPaths).map fun (t, p) =>
      Json.mkObj [("hN", natJ t.hN), ("col0", natJ t.col0), ("nc", natJ t.nc), ("npub", natJ t.npub), ("pubBase", natJ t.pubBase),
                  ("chip", Json.str p)])),
    ("pubIn", V.pubInJ pubIn), ("slotOf", Json.arr (slotOf.map natJ))]

end NockvmE2E.Exec.FP
