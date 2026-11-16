/-
  Nock/V1J8/GenAtom.lean

  `genJ8` (B4757, kernel-checked against the example in B4758) and
  `genJ8J` (B4759) are untouched; `genJ8A` is the generator with big atoms (no jet calls).

  `genJ8A R fuel s f χe` runs `genX`, then:
  * **the big atoms** (`bigsOf`): every leaf `≥ p` of the demand roots and of every row's twelve handles (`demandA`'s
    closure, ascending); **the atom cell list** (`acsOf`): each big atom's comb spine (A-1 canonical limbs, the
    right comb `[l₀ [l₁ … [l_{k−2} l_{k−1}]]]`, root → deepest), first occurrence (shared suffixes once), then the
    inert pad row `[0 1]` (NV2);
  * **handles** (`hdlB`): small `(0, v)`, cell `(1, cell serial)`, **big `(2, atom-table serial of its root comb)`**;
    the compute's α-pair limb data `pd = pdX sx` with `sx a d` the atom-table serial of `a`'s spine row at depth `d`;
  * **the cell table** (`cellGenB`, 242 columns): a big-atom child is a WEIGHTED child (`w = 1`) with `kb = 1`
    (columns `130 / 131`), rank `(0, 0)`, serial = the atom root's serial; its validity key `(⟨z, 0, A(y)⟩, 0, idx)`
    is consumed from the atom table's external provide `mb` (g5);
  * **the atom table** (`atomGen`, 349 columns): `cellTemplateHQ`'s columns at the limb coin `y` (`coOfA`), the limb
    bits, `inv_t`, `inv_b`, `mb` (one per cell-table big child), the inc chain (`infoOf`: a slow OP4 record
    `v ↦ v + 1` is a conversion row on `p` when `v = p − 1`, else an inc chain on `v + 1`'s spine from the root while
    the carry runs, each inc row consuming its old row's export record), `mi` (the chain head's compute consumes),
    and the six `𝕂′` roles (inverses, INCLUSIVE prefix accumulators); publics `0..5` (cell part), `6/7` (`mb`),
    `8/9` (`mi`), `10/11` (old-export consumes);
  * **the atom walk** (present iff some OP5 row compares two big atoms): the reads `(comb(a), ax₂)`, `(comb(b), ax₂)`
    of every pair row, one read trie per root comb (`walkGen`), rows in `walkTemplateHQK`'s layout (the OLD depth
    certificate `WalkJ8.certB`), coins `chalsAJ8ZE`; the atom table's `mx` / `mh` gain one per atom-walk row.
  **Scope:** no jet call (`none` otherwise).

  **Multi-limb hardening (completeness fixes, found natively on atoms `≥ 2^64`):**
  * **link order** (`linkOrder`): the atom cell list puts every row `[0 X]` directly before its suffix row `X`.  The
    first-occurrence order broke g7.3′ (`idR = idx + 1`, the carry into a suffix row) whenever the new suffix was a
    row of an EARLIER atom (`[Bm 0 Bm] + 1 = [0 1 Bm]` beside `p = [1 Bm]`; `[Bm Bm 2 4] + 1` beside `[5 3 4]`);
  * **the `p` duplicate** (`acsOfD … dupP`): when the run converts `p − 1 → p` AND `[0 [1 Bm]]` is a row, `[1 Bm]`
    gets a second row (one row cannot be both the conversion row and the linked inc row, g7.0 `inc·conv`); `p`'s
    handle / `mb` / conversion are at the LAST copy (`rootIdx`), comb pointers at the first, and the atom walk's
    ROOT rows at `rootIdx` (`wIdx`, `walkDB`'s `rI`).

  `v = B^66 − 1`) had its carry chain cut at row 64, and
  g7.3′ then forced `inc = 1` on the next row: an honest rejection. `ComplJ8Data.infoOfP` carries
  the same fuel, so `j8DataOf`'s fields stay `rfl` to the generator.

  `infoOf`, `fixOld`, `sxOf`, `atomGen`, `walkGenRowsB` stay (diagnostics, the J-8 cell / walk tables). -/
import Nock.V1J8.GenJ8
import Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J8.Gen

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

/-! ## 1. Big atoms, combs, the atom cell list -/

/-- The right comb of a limb list (`[x, y] ↦ [x y]`). -/
def combOf : List ℕ → Noun
  | [] => .atom 0
  | [x] => .atom x
  | [x, y] => .cell (.atom x) (.atom y)
  | x :: xs => .cell (.atom x) (combOf xs)

/-- The comb spine of a limb list: the comb and every suffix comb of length `≥ 2`, root → deepest. -/
def spineOf : List ℕ → List Noun
  | x :: y :: rest => combOf (x :: y :: rest) :: spineOf (y :: rest)
  | _ => []

/-- The pad row's noun `[0 1]`. -/
def padN : Noun := .cell (.atom 0) (.atom 1)

/-- **The big atoms**: every leaf `≥ p` of the roots and of the rows' twelve handles, once, ascending. -/
def bigsOf (roots : List Noun) (rows : Array RowNX) : List ℕ :=
  ((((roots ++ rows.toList.flatMap rowHandleNounsX).flatMap leavesOf).filter fun a => decide (P ≤ a)).dedup).mergeSort
    (fun a b => decide (a ≤ b))

/-- Append the nouns not yet present. -/
def addNew (acc : List Noun) (ns : List Noun) : List Noun :=
  ns.foldl (fun acc n => if n ∈ acc then acc else acc ++ [n]) acc

/-- The comb of `p = [1, B − 1]`. -/
def combP : Noun := combOf (Nock.Atoms.limbs P)

/-- The link successor of a comb row: `[0 X] ↦ X` when `X` is a cell of `L` (a carry into a suffix row, g7.3′,
or a top-limb overflow into the row `[0 1]`, g7.4, always has a new row `[0 X]` whose suffix `X` must sit at
`idx + 1`). -/
def linkSucc (L : List Noun) : Noun → Option Noun
  | .cell (.atom 0) (.cell a b) => if Noun.cell a b ∈ L then some (.cell a b) else none
  | _ => none

/-- The head of `n`'s link chain: go up through `[0 n]` while it is in `L` (fuel `f`). -/
def linkHead (L : List Noun) : ℕ → Noun → Noun
  | 0, n => n
  | f + 1, n => if Noun.cell (.atom 0) n ∈ L then linkHead L f (.cell (.atom 0) n) else n

/-- The link chain from `n` (fuel `f`). -/
def linkChain (L : List Noun) : ℕ → Noun → List Noun
  | 0, n => [n]
  | f + 1, n => match linkSucc L n with
    | some m => n :: linkChain L f m
    | none => [n]

/-- **The link order.**  Each row `[0 X]` with `X ∈ L` is followed by `X` (every row has at most one link
predecessor `[0 X]` and one link successor, so the links are disjoint paths); rows otherwise in first-occurrence
order.  (The plain first-occurrence order broke g7.3′ when the new suffix was an EARLIER atom's row.) -/
def linkOrder (L : List Noun) : List Noun :=
  L.foldl (fun acc n => if n ∈ acc then acc else acc ++ linkChain L L.length (linkHead L L.length n)) []

/-- **The atom cell list** (spines, link order) and the pad row last; `dupP`: a second row `p = [1, B − 1]` (the
conversion row, `p`'s root) after the linked one (a carry into the suffix `[1, B − 1]` makes that row an INC
row, and one row cannot carry both `inc` and `conv`, g7.0). -/
def acsOfD (bigs : List ℕ) (dupP : Bool) : List Noun :=
  let L := bigs.foldl (fun acc a => addNew acc (spineOf (Nock.Atoms.limbs a))) []
  linkOrder L ++ (if dupP && decide (Noun.cell (.atom 0) combP ∈ L) then [combP] else []) ++ [padN]

def acsOf (bigs : List ℕ) : List Noun := acsOfD bigs false

/-- The last index of `n` in `l` (`0` if absent). -/
def lastIdxOf (l : List Noun) (n : Noun) : ℕ :=
  (((l.zipIdx 0).reverse.find? fun x => x.1 == n).map (·.2)).getD 0

/-- The atom-table serial of a big atom's root comb (for `p`: its LAST row, the conversion row when duplicated). -/
def rootIdx (acsL : List Noun) (a : ℕ) : ℕ :=
  if a = P then lastIdxOf acsL combP else idxOf acsL (combOf (Nock.Atoms.limbs a))

/-- **The handle map with big atoms**: small `(0, v)`, big `(2, root serial)`, cell `(1, serial)`. -/
def hdlB (cs acsL : List Noun) : Noun → ℕ × ℕ
  | .atom v => if v < P then (0, v) else (2, rootIdx acsL v)
  | .cell a b => (1, idxOf cs (.cell a b))

/-- `sx a d`: the atom-table serial of atom `a`'s spine row at depth `d`. -/
def sxOf (acsL : List Noun) (a d : ℕ) : ℕ := idxOf acsL ((spineOf (Nock.Atoms.limbs a)).getD d (.atom 0))

/-- The atom-table root serial of a noun if it is a big atom. -/
def bigIdOf (acsL : List Noun) : Noun → Option ℕ
  | .atom v => if v < P then none else some (rootIdx acsL v)
  | .cell _ _ => none

/-! ## 2. Compute with the α-pair data -/

def baseFnB (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (n j : ℕ) (r : RowNX) : ℕ → ZMod P :=
  fun c => FillX.colXE H pd r (flag (j == 0)) (flag (j + 1 == n)) c

def basesOfB (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (Rn : RunX) : List (ℕ → ZMod P) :=
  (Rn.rows.toList.zipIdx 0).map fun (r, j) => baseFnB H pd Rn.rows.size j r

def compGenB (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (Rn : RunX)
    (χe : CoinsE) : CompOut :=
  let m := mOf c H
  let bs := basesOfB H pd Rn
  let ρ := rhoOfB χe bs
  let ρS := rhoSOf c m ρ χe bs
  ⟨compTable H Rn (pubVJ8E c m ρ ρS χe) χe bs, ρ, ρS, bs⟩

/-! ## 3. The cell table with big children -/

/-- **The data of cell row `j`** (a big child: weighted, rank `0`, the atom root's serial). -/
def cellDB (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (big : Noun → Option ℕ) (cs : List Noun) (n : Noun) (j : ℕ) :
    CellD :=
  let l := hdN' n
  let r := tlN' n
  let pE := encE k.z y n
  let lE := encE k.z y l
  let rE := encE k.z y r
  let idL := if l.isCell then idxOf cs l else (big l).getD 0
  let idR := if r.isCell then idxOf cs r else (big r).getD 0
  let xKey (s : ℕ) : Fin 11 → K6 :=
    ![pE.size, pE.dyck, pE.leaf, lE.size, lE.dyck, lE.leaf, rE.size, rE.dyck, rE.leaf, lq j, lq s]
  { j := j, l := l, r := r, pE := pE, lE := lE, rE := rE, mu := n.internal, muL := l.internal,
    muR := r.internal, idL := idL, idR := idR
    vInv := (compressE k.γ k.ρ ![pE.size, pE.dyck, pE.leaf, rkK n.internal, lq j])⁻¹
    lInv := if l.isCell || (big l).isSome then
      (compressE k.γ k.ρ ![lE.size, lE.dyck, lE.leaf, rkK l.internal, lq idL])⁻¹ else 0
    rInv := if r.isCell || (big r).isSome then
      (compressE k.γ k.ρ ![rE.size, rE.dyck, rE.leaf, rkK r.internal, lq idR])⁻¹ else 0
    x0Inv := (compressE k.γ k.ρ (xKey 0))⁻¹
    x1Inv := (compressE k.γ k.ρ (xKey 1))⁻¹
    ivH := (compressE k.γH k.ρH ![lq j, (hK H l).1, (hK H l).2, (hK H r).1, (hK H r).2])⁻¹ }

/-- **Column `c` of a cell row with big children** (`cellColD`, then `w`, `kb` and the small-atom value columns). -/
def cellColDB (big : Noun → Option ℕ) (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) (c : ℕ) :
    ZMod P :=
  let bL := (big d.l).isSome
  let bR := (big d.r).isSome
  if c = 5 then flag (d.l.isCell || bL) else if c = 6 then flag (d.r.isCell || bR)
  else if c = 7 then (if bL then 0 else (atomV d.l : ZMod P))
  else if c = 8 then (if bR then 0 else (atomV d.r : ZMod P))
  else if c = 130 then flag bL else if c = 131 then flag bR
  else cellColD D mv mx mx1 mh d va xa ha c

/-- **The cell table with big children** (242 columns) and its six publics. -/
def cellGenB (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (big : Noun → Option ℕ) (cs : List Noun)
    (mv mx mx1 mh : Array ℕ) : Array (Array (ZMod P)) × (ℕ → K3) :=
  let D := cs.length
  let ds := (cs.zipIdx 0).map fun (n, j) => cellDB k y H big cs n j
  let vAccs := scanK6 (ds.map (vTermD mv))
  let xAccs := scanK6 (ds.map (xTermD mx mx1))
  let hAccs := scanK6 (ds.map (hTermD mh))
  let tbl := (List.range D).map fun j =>
    let d := ds.getD j (cellDB k y H big cs (.atom 0) j)
    Array.ofFn (n := 242) fun c => cellColDB big D mv mx mx1 mh d (vAccs.getD j 0) (xAccs.getD j 0)
      (hAccs.getD j 0) c
  let vT := lastK6 vAccs
  let xT := lastK6 xAccs
  let hT := lastK6 hAccs
  let pubs : ℕ → K3 := fun j =>
    if j = 0 then vT.re else if j = 1 then vT.im else if j = 2 then xT.re else if j = 3 then xT.im
    else if j = 4 then hT.re else if j = 5 then hT.im else 0
  (tbl.toArray, pubs)

/-- `mb`: one per cell-table child that is a big atom, at the atom root. -/
def mbCounts (acsL cs : List Noun) : Array ℕ :=
  (cs.flatMap fun n => [hdN' n, tlN' n]).foldl (fun a n => match bigIdOf acsL n with
    | some i => bump a i 1
    | none => a) (Array.replicate acsL.length 0)

/-! ## 4. The walk rows (handle map and certificate as parameters) -/

/-- A walk row's node serial, with the ROOT rows (`len = 0`) at `rI` (the atom walk's root of `p` is `p`'s
conversion row when the atom table carries two rows `[1, B − 1]`; interior rows follow the table's `idR` pointers). -/
def wIdx (rI : Noun → ℕ) (cs : List Noun) (w : WRow) : ℕ := if w.len = 0 then rI w.node else idxN cs w.node

/-- One per walk row at its node serial `wIdx` (the atom walk's `mx`, and its `mh` part). -/
def wCounts (rI : Noun → ℕ) (cs : List Noun) (ws : List WRow) : Array ℕ :=
  ws.foldl (fun a w => match w.node with
    | .cell _ _ => bump a (wIdx rI cs w) 1
    | .atom _ => a) (Array.replicate cs.length 0)

def walkDB (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun) (w : WRow) (j : ℕ) : WalkD :=
  let pE := encE k.z y w.node
  let lE := encE k.z y (hdN' w.node)
  let rE := encE k.z y (tlN' w.node)
  let rootE := encE k.z y w.root
  let idx := wIdx rI cs w
  let ridx := rI w.root
  let hl := hK H (hdN' w.node)
  let hr := hK H (tlN' w.node)
  { w := w, j := j, pE := pE, lE := lE, rE := rE, rootE := rootE, idx := idx, ridx := ridx
    xInv := (compressE k.γ k.ρ (![pE.size, pE.dyck, pE.leaf, lE.size, lE.dyck, lE.leaf, rE.size, rE.dyck,
      rE.leaf, lq idx, lq 0] : Fin 11 → K6))⁻¹
    pInvL := (compressE k.γ k.ρ (![rootE.size, rootE.dyck, rootE.leaf, lE.size, lE.dyck, lE.leaf,
      lq (2 * w.pre), lq ridx] : Fin 8 → K6))⁻¹
    pInvR := (compressE k.γ k.ρ (![rootE.size, rootE.dyck, rootE.leaf, rE.size, rE.dyck, rE.leaf,
      lq (2 * w.pre + 1), lq ridx] : Fin 8 → K6))⁻¹
    hXi := (compressE k.γH k.ρH (![lq idx, hl.1, hl.2, hr.1, hr.2] : Fin 5 → K6))⁻¹
    hPLi := (compressE k.γH k.ρH (![lq ridx, lq (2 * w.pre), hl.1, hl.2] : Fin 4 → K6))⁻¹
    hPRi := (compressE k.γH k.ρH (![lq ridx, lq (2 * w.pre + 1), hr.1, hr.2] : Fin 4 → K6))⁻¹ }

/-- **Column `c` of a walk row** at a depth certificate `cert`. -/
def walkColDB (cert : ℕ → ℕ → ℕ) (H : Noun → ℕ × ℕ) (N kr q : ℕ) (d : WalkD) (ln cnt acc : K3)
    (xa pa hxa hpa : K6) (c : ℕ) : ZMod P :=
  if c = 14 then ((cert d.w.len 1 * cert d.w.len 2 : ℕ) : ZMod P)
  else if 15 ≤ c ∧ c < 21 then (cert d.w.len (c - 15) : ZMod P)
  else walkColD H N kr q d ln cnt acc xa pa hxa hpa c

/-- **The walk table** (166 columns per row) and its eight publics, at a handle map and a certificate. -/
def walkGenRowsB (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cert : ℕ → ℕ → ℕ) (cs : List Noun)
    (ws : List WRow) (kr : ℕ) : Array (Array (ZMod P)) × (ℕ → K3) :=
  let N := ws.length
  let ds := (ws.zipIdx 0).map fun (w, j) => walkDB k y H rI cs w j
  let fos := ws.map foW
  let curs := ds.map (curD γ)
  let ccs := childSums α kr fos curs.toArray
  let lca := walkLCA α kr fos ccs curs
  let xAccs := scanK6 (ds.map (·.xInv))
  let pAccs := scanK6 (ds.map pTermD)
  let hxAccs := scanK6 (ds.map (·.hXi))
  let hpAccs := scanK6 (ds.map hPTermD)
  let sfs := scanN fos
  let tbl := (List.range N).map fun j =>
    let d := ds.getD j (walkDB k y H rI cs (ws.getD j ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩) j)
    let v := lca.getD j (0, 0, 0)
    let q : ℕ := kr + sfs.getD j 0 - (j + 1)
    Array.ofFn (n := 166) fun c => walkColDB cert H N kr q d v.1 v.2.1 v.2.2 (xAccs.getD j 0) (pAccs.getD j 0)
      (hxAccs.getD j 0) (hpAccs.getD j 0) c
  let xT := lastK6 xAccs
  let pT := lastK6 pAccs
  let hxT := lastK6 hxAccs
  let hpT := lastK6 hpAccs
  let pubs : ℕ → K3 := fun j =>
    if j = 0 then xT.re else if j = 1 then xT.im else if j = 2 then pT.re else if j = 3 then pT.im
    else if j = 4 then hxT.re else if j = 5 then hxT.im else if j = 6 then hpT.re else if j = 7 then hpT.im else 0
  (tbl.toArray, pubs)

/-! ## 5. The atom table -/

/-- The added per-row data of an atom-table row. -/
structure AInfo where
  inc : Bool
  conv : Bool
  cout : Bool
  idxO : ℕ
  lO : ℕ
  kRO : ℕ
  vRO : ℕ
  mi : ℕ
  mhx : ℕ
deriving Inhabited

def AInfo.z : AInfo := ⟨false, false, false, 0, 0, 0, 0, 0, 0⟩

/-- The right child `(wR, valR)` of an atom-table row's noun. -/
def valROf (acsL : List Noun) (n : Noun) : ℕ × ℕ :=
  match tlN' n with
  | .cell a b => (1, idxOf acsL (.cell a b))
  | .atom v => (0, v)

/-- The slow OP4 operands `v` (with `v + 1 ≥ p`) of the rows, with their consume counts. -/
def incOps (rows : Array RowNX) : List (ℕ × ℕ) :=
  let vs := rows.toList.filterMap fun r => match r.st, r.sf1 with
    | .s4, .atom v => if P ≤ v + 1 then some v else none
    | _, _ => none
  vs.dedup.map fun v => (v, vs.count v)

/-- Set the inc data of one chain from depth `d` (fuel `f`): new spine `ns`, old spine `os`. -/
def incChain (acsL : List Noun) : ℕ → List Noun → List Noun → Array AInfo → Array AInfo
  | 0, _, _, a => a
  | _, [], _, a => a
  | _, _, [], a => a
  | f + 1, n :: ns, o :: os, a =>
    let jn := idxOf acsL n
    let jo := idxOf acsL o
    let lO := atomV (hdN' o)
    let (kRO, vRO) := valROf acsL o
    let cout := decide (lO = Nock.Atoms.B - 1)
    let a := a.modify jn fun x => { x with inc := true, cout := cout, idxO := jo, lO := lO, kRO := kRO, vRO := vRO }
    let a := a.modify jo fun x => { x with mhx := x.mhx + 1 }
    if cout && kRO == 1 then incChain acsL f ns os a else a

/-- The consume count of atom row `j`: the number of inc rows whose old row is `j`. -/
def mhxOf (a : Array AInfo) (j : ℕ) : ℕ := (a.toList.filter fun x => x.inc && x.idxO == j).length

/-- The consume count is therefore recounted from the final inc
rows. -/
def recountMhx (a : Array AInfo) : Array AInfo := a.mapIdx fun j x => { x with mhx := mhxOf a j }

/-- For
`v ≠ P` that is `idxOf (comb v)`, which `incChain` already wrote; for `v = P` it is the LAST copy of `comb P`
(`lastIdxOf`, the conversion copy when `comb P` is duplicated), so only the row `comb (P + 1)` is touched, and only
when it is an inc row. Depth `≥ 1` rows keep `idxOf` (the atom chip's link `rn.idxO = r.vRO`). -/
def fixOld (acsL : List Noun) (rows : Array RowNX) (a : Array AInfo) : Array AInfo :=
  if (incOps rows).any (fun x => x.1 == P) then
    a.modify (idxOf acsL (combOf (Nock.Atoms.limbs (P + 1)))) fun x =>
      if x.inc then { x with idxO := rootIdx acsL P } else x
  else a

/-- **The inc / conversion data of the atom table.** -/
def infoOf (acsL : List Noun) (rows : Array RowNX) : Array AInfo := recountMhx <| fixOld acsL rows <|
  (incOps rows).foldl (fun a (v, c) =>
    if v + 1 = P then
      a.modify (rootIdx acsL P) fun x => { x with conv := true, mi := x.mi + c }
    else
      let a := incChain acsL ((spineOf (Nock.Atoms.limbs v)).length + 1) (spineOf (Nock.Atoms.limbs (v + 1)))
        (spineOf (Nock.Atoms.limbs v)) a
      a.modify (rootIdx acsL (v + 1)) fun x => { x with mi := x.mi + c })
    (Array.replicate acsL.length AInfo.z)

/-- Bit `i` of `n`. -/
def bitZ (n i : ℕ) : ZMod P := if n.testBit i then 1 else 0

/-- `x ∈ 𝔽` as a `K6` scalar. -/
def zq (x : ZMod P) : K6 := g6 (Gold.ofZ x)

/-- The three `𝕂′` denominators of an atom-table row: `mbKey`, `oldKey`, `incKey`. -/
def dMBA (k : Co) (zA : K6) (d : CellD) : K6 := compressE k.γ k.ρ ![zA, 0, d.pE.leaf, 0, lq d.j]
def dCA (k : Co) (ai : AInfo) : K6 := compressE k.γH k.ρH ![lq ai.idxO, 0, lq ai.lO, lq ai.kRO, lq ai.vRO]
def dMIA (k : Co) (ai : AInfo) (j : ℕ) : K6 :=
  compressE k.γH k.ρH ![if ai.conv then 0 else lq 2, if ai.conv then zq (-1) else lq ai.idxO, lq 2, lq j, lq 4]

/-- **Column `c` of an atom-table row** (349 columns). -/
def atomColD (D : ℕ) (mv mx mx1 mh : Array ℕ) (mb : ℕ) (d : CellD) (va xa ha : K6) (ai : AInfo)
    (roles : ℕ → K3) (c : ℕ) : ZMod P :=
  let aL := atomV d.l
  let aR := if d.r.isCell then 0 else atomV d.r
  if c < 130 then cellColD D mv mx mx1 mh d va xa ha c
  else if c < 162 then bitZ aL (c - 130)
  else if c < 194 then bitZ aR (c - 162)
  else if c = 194 then (if d.r.isCell then 0 else (aR : ZMod P)⁻¹)
  else if c = 195 then (aL : ZMod P)⁻¹
  else if c = 196 then (mb : ZMod P)
  else if c = 197 then flag ai.inc else if c = 198 then flag ai.conv else if c = 199 then flag ai.cout
  else if c = 200 then (ai.idxO : ZMod P) else if c = 201 then (ai.lO : ZMod P)
  else if c = 202 then (ai.kRO : ZMod P) else if c = 203 then (ai.vRO : ZMod P)
  else if c = 204 then (ai.mi : ZMod P)
  else if c < 301 then cellColD D mv mx mx1 mh d va xa ha (c - 205 + 134)
  else if c < 313 then cellColD D mv mx mx1 mh d va xa ha (c - 301 + 230)
  else if c < 349 then limbZ (roles ((c - 313) / 3)) ((c - 313) % 3)
  else 0

/-- **The atom table** (349 columns) and its twelve publics. -/
def atomGen (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb mxA mhA : Array ℕ) :
    Array (Array (ZMod P)) × (ℕ → K3) :=
  let k := coOfA χe
  let y := yE χe
  let zA := zE χe
  let D := acsL.length
  let mv := mvCounts acsL ⟨.atom 0, .atom 0, .atom 0⟩
  let mx1 := Array.replicate D 0
  let mh := (Array.range D).map fun j => mhA.getD j 0 + (info.getD j AInfo.z).mhx
  let ds := (acsL.zipIdx 0).map fun (n, j) => cellD k y acsL n j
  let ais := (List.range D).map fun j => info.getD j AInfo.z
  let vAccs := scanK6 (ds.map (vTermD mv))
  let xAccs := scanK6 (ds.map (xTermD mxA mx1))
  let hAccs := scanK6 (ds.map (hTermD mh))
  let iMB := ds.map fun d => (dMBA k zA d)⁻¹
  let iC := ais.map fun ai => (dCA k ai)⁻¹
  let iMI := (ais.zipIdx 0).map fun (ai, j) => (dMIA k ai j)⁻¹
  let aMB := scanK6 ((iMB.zipIdx 0).map fun (v, j) => lq (mb.getD j 0) * v)
  let aC := scanK6 ((iC.zip ais).map fun (v, ai) => (if ai.inc then 1 else 0) * v)
  let aMI := scanK6 ((iMI.zip ais).map fun (v, ai) => lq ai.mi * v)
  let tbl := (List.range D).map fun j =>
    let d := ds.getD j (cellD k y acsL (.atom 0) j)
    let ai := ais.getD j AInfo.z
    let r6 : List K6 := [iMB.getD j 0, aMB.getD j 0, iC.getD j 0, iMI.getD j 0, aMI.getD j 0, aC.getD j 0]
    let roles : ℕ → K3 := fun t => let v := r6.getD (t / 2) 0; if t % 2 = 0 then v.re else v.im
    Array.ofFn (n := 349) fun c => atomColD D mv mxA mx1 mh (mb.getD j 0) d (vAccs.getD j 0) (xAccs.getD j 0)
      (hAccs.getD j 0) ai roles c
  let vT := lastK6 vAccs
  let xT := lastK6 xAccs
  let hT := lastK6 hAccs
  let mbT := lastK6 aMB
  let miT := lastK6 aMI
  let cT := lastK6 aC
  let pubs : ℕ → K3 := fun j =>
    if j = 0 then vT.re else if j = 1 then vT.im else if j = 2 then xT.re else if j = 3 then xT.im
    else if j = 4 then hT.re else if j = 5 then hT.im else if j = 6 then mbT.re else if j = 7 then mbT.im
    else if j = 8 then miT.re else if j = 9 then miT.im else if j = 10 then cT.re else if j = 11 then cT.im else 0
  (tbl.toArray, pubs)

/-! ## 5b. The variant-4 tail pointer

The proofs' honest atom-table data (`ComplJ8Data.j8DataOf`) keys every atom row's right child by ONE per-component
tail pointer `ComplJ8Data.ptrP`: a row `[x comb p]` takes the FIRST copy of `comb p` when `x` lies in the stop-edge
component of `0` (`FirstC`), else the LAST copy; every other row the first copy of its tail.  The functions below are
the executable transcription (`GenPortJ9` proves `ptrE acsL (stopEdges rows) = ptrP P acsL rows`, `infoOfE … =
infoOfP P …`, `sxE … = sxPP P …`).  Routed through: the atom table's cell part (`idR`, `rInv`, `ivH`, `mv`), the inc
chains (`kR_o`, `vR_o`; old key `jo` = LAST copy for `o = comb p`; no `fixOld`), the atom walk's right handle (`hr`,
column 24), and the compute's pair spine serials `sx`.  The atom walk's row serial `idx` stays `wIdx` (the proofs'
`idxRW`), the `p` duplicate stays `acsOfD`'s (`ComplJ8Data.acsP`). -/

/-- The stop edges of one old limb list: `x` with `l.drop d = x :: limbs p`, `x ≠ B − 1`, every shallower limb
`B − 1` (`ComplJ8Data.StopE` at one operand). -/
def stopsOfL (l : List ℕ) : List ℕ :=
  (List.range l.length).filterMap fun d => match l.drop d with
    | x :: t => if t = Nock.Atoms.limbs P ∧ x ≠ Nock.Atoms.B - 1 ∧
        (List.range d).all (fun i => (l.drop i).headD 0 == Nock.Atoms.B - 1) then some x else none
    | [] => none

/-- **The stop edges of the run** (`ComplJ8Data.StopE`): over every slow OP4 operand `v` with `v + 1 ≠ p`. -/
def stopEdges (rows : Array RowNX) : List ℕ :=
  (incOps rows).flatMap fun vc => if vc.1 + 1 = P then [] else stopsOfL (Nock.Atoms.limbs vc.1)

/-- **`FirstC` decided** (`ComplJ8Data.FirstC`): every edge `0, …, x − 1` is a stop edge (the length test first, so
a head near `B` costs nothing). -/
def firstCE (es : List ℕ) (x : ℕ) : Bool := decide (x ≤ es.length) && (List.range x).all (· ∈ es)

/-- **The executable per-component tail pointer** (`ComplJ8Data.ptrP` at the stop edges `es`). -/
def ptrE (acsL : List Noun) (es : List ℕ) (n : Noun) : ℕ :=
  if tlN' n = combP ∧ firstCE es (atomV (hdN' n)) = false then lastIdxOf acsL combP else idxOf acsL (tlN' n)

/-- The row key of an atom-table noun (`ComplJ8Data.keyP`): `comb p` at its LAST copy. -/
def keyE (acsL : List Noun) (n : Noun) : ℕ := if n = combP then lastIdxOf acsL combP else idxOf acsL n

/-- The right child `(wR, valR)` at a pointer (`ComplJ8Data.valROfK`). -/
def valROfE (ptr : Noun → ℕ) (n : Noun) : ℕ × ℕ :=
  match tlN' n with
  | .cell _ _ => (1, ptr n)
  | .atom v => (0, v)

/-- The inc chain at a row key and a tail pointer (`ComplJ8Data.incChainK`). -/
def incChainE (acsL : List Noun) (key ptr : Noun → ℕ) : ℕ → List Noun → List Noun → Array AInfo → Array AInfo
  | 0, _, _, a => a
  | _ + 1, [], _, a => a
  | _ + 1, _ :: _, [], a => a
  | f + 1, n :: ns, o :: os, a =>
    let jn := idxOf acsL n
    let jo := key o
    let lO := atomV (hdN' o)
    let (kRO, vRO) := valROfE ptr o
    let cout := decide (lO = Nock.Atoms.B - 1)
    let a := a.modify jn fun x => { x with inc := true, cout := cout, idxO := jo, lO := lO, kRO := kRO, vRO := vRO }
    let a := a.modify jo fun x => { x with mhx := x.mhx + 1 }
    if cout && kRO == 1 then incChainE acsL key ptr f ns os a else a

/-- **The inc / conversion data at the pointer** (`ComplJ8Data.infoOfP`: keys `keyE`, pointer `ptr`, no `fixOld`). -/
def infoOfE (acsL : List Noun) (ptr : Noun → ℕ) (rows : Array RowNX) : Array AInfo := recountMhx <|
  (incOps rows).foldl (fun a (v, c) =>
    if v + 1 = P then
      a.modify (rootIdx acsL P) fun x => { x with conv := true, mi := x.mi + c }
    else
      let a := incChainE acsL (keyE acsL) ptr ((spineOf (Nock.Atoms.limbs v)).length + 1)
        (spineOf (Nock.Atoms.limbs (v + 1))) (spineOf (Nock.Atoms.limbs v)) a
      a.modify (rootIdx acsL (v + 1)) fun x => { x with mi := x.mi + c })
    (Array.replicate acsL.length AInfo.z)

/-- **The op-5 pair spine serial at the pointer** (`ComplJ8Data.sxPP`; `pdX` reads only depths `≥ 1`). -/
def sxE (ptr : Noun → ℕ) (a e : ℕ) : ℕ := ptr ((spineOf (Nock.Atoms.limbs a)).getD (e - 1) (.atom 0))

/-- **The atom cells' validity multiplicity at the pointer** (`ComplJ8Of.mvA`): left children at `idxOf`, right
children at `ptr`. -/
def mvE (acsL : List Noun) (ptr : Noun → ℕ) : Array ℕ :=
  (Array.range acsL.length).map fun j =>
    (acsL.filter fun y => (hdN' y).isCell && idxOf acsL (hdN' y) == j).length +
      (acsL.filter fun y => (tlN' y).isCell && ptr y == j).length

/-- **An atom-table row's cell data at the pointer**: a cell tail is keyed `idR = ptr n` (`rInv`, `ivH` follow). -/
def cellDE (ptr : Noun → ℕ) (k : Co) (y : K6) (acsL : List Noun) (n : Noun) (j : ℕ) : CellD :=
  let d := cellD k y acsL n j
  if (tlN' n).isCell then
    let idR := ptr n
    { d with
      idR := idR,
      rInv := (compressE k.γ k.ρ ![d.rE.size, d.rE.dyck, d.rE.leaf, rkK (tlN' n).internal, lq idR])⁻¹,
      ivH := (compressE k.γH k.ρH ![lq j, (hK (hdl acsL) d.l).1, (hK (hdl acsL) d.l).2, lq 1, lq idR])⁻¹ }
  else d

/-- **The atom table at the pointer** (`atomGen` with `mvE` and `cellDE`). -/
def atomGenE (ptr : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb mxA mhA : Array ℕ) :
    Array (Array (ZMod P)) × (ℕ → K3) :=
  let k := coOfA χe
  let y := yE χe
  let zA := zE χe
  let D := acsL.length
  let mv := mvE acsL ptr
  let mx1 := Array.replicate D 0
  let mh := (Array.range D).map fun j => mhA.getD j 0 + (info.getD j AInfo.z).mhx
  let ds := (acsL.zipIdx 0).map fun (n, j) => cellDE ptr k y acsL n j
  let ais := (List.range D).map fun j => info.getD j AInfo.z
  let vAccs := scanK6 (ds.map (vTermD mv))
  let xAccs := scanK6 (ds.map (xTermD mxA mx1))
  let hAccs := scanK6 (ds.map (hTermD mh))
  let iMB := ds.map fun d => (dMBA k zA d)⁻¹
  let iC := ais.map fun ai => (dCA k ai)⁻¹
  let iMI := (ais.zipIdx 0).map fun (ai, j) => (dMIA k ai j)⁻¹
  let aMB := scanK6 ((iMB.zipIdx 0).map fun (v, j) => lq (mb.getD j 0) * v)
  let aC := scanK6 ((iC.zip ais).map fun (v, ai) => (if ai.inc then 1 else 0) * v)
  let aMI := scanK6 ((iMI.zip ais).map fun (v, ai) => lq ai.mi * v)
  let tbl := (List.range D).map fun j =>
    let d := ds.getD j (cellDE ptr k y acsL (.atom 0) j)
    let ai := ais.getD j AInfo.z
    let r6 : List K6 := [iMB.getD j 0, aMB.getD j 0, iC.getD j 0, iMI.getD j 0, aMI.getD j 0, aC.getD j 0]
    let roles : ℕ → K3 := fun t => let v := r6.getD (t / 2) 0; if t % 2 = 0 then v.re else v.im
    Array.ofFn (n := 349) fun c => atomColD D mv mxA mx1 mh (mb.getD j 0) d (vAccs.getD j 0) (xAccs.getD j 0)
      (hAccs.getD j 0) ai roles c
  let vT := lastK6 vAccs
  let xT := lastK6 xAccs
  let hT := lastK6 hAccs
  let mbT := lastK6 aMB
  let miT := lastK6 aMI
  let cT := lastK6 aC
  let pubs : ℕ → K3 := fun j =>
    if j = 0 then vT.re else if j = 1 then vT.im else if j = 2 then xT.re else if j = 3 then xT.im
    else if j = 4 then hT.re else if j = 5 then hT.im else if j = 6 then mbT.re else if j = 7 then mbT.im
    else if j = 8 then miT.re else if j = 9 then miT.im else if j = 10 then cT.re else if j = 11 then cT.im else 0
  (tbl.toArray, pubs)

/-- **An atom-walk row at the pointer**: a cell tail's handle is `(1, ptr node)` (`ComplJ9BBalF.kRV9 / vRV9`), in
`hXi` and `hPRi`; the row serial stays `wIdx` (`ComplJ9BAWR.idxRW`). -/
def walkDBE (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun) (w : WRow)
    (j : ℕ) : WalkD :=
  let d := walkDB k y H rI cs w j
  if (tlN' w.node).isCell then
    let hl := hK H (hdN' w.node)
    let hr : K6 × K6 := (lq 1, lq (ptr w.node))
    { d with
      hXi := (compressE k.γH k.ρH (![lq d.idx, hl.1, hl.2, hr.1, hr.2] : Fin 5 → K6))⁻¹,
      hPRi := (compressE k.γH k.ρH (![lq d.ridx, lq (2 * w.pre + 1), hr.1, hr.2] : Fin 4 → K6))⁻¹ }
  else d

/-- **The atom walk at the pointer** (`walkGenRowsB` with `walkDBE`; column 24 of a cell-tail row is `ptr node`). -/
def walkGenRowsBE (ptr : Noun → ℕ) (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ)
    (cert : ℕ → ℕ → ℕ) (cs : List Noun) (ws : List WRow) (kr : ℕ) : Array (Array (ZMod P)) × (ℕ → K3) :=
  let N := ws.length
  let ds := (ws.zipIdx 0).map fun (w, j) => walkDBE ptr k y H rI cs w j
  let fos := ws.map foW
  let curs := ds.map (curD γ)
  let ccs := childSums α kr fos curs.toArray
  let lca := walkLCA α kr fos ccs curs
  let xAccs := scanK6 (ds.map (·.xInv))
  let pAccs := scanK6 (ds.map pTermD)
  let hxAccs := scanK6 (ds.map (·.hXi))
  let hpAccs := scanK6 (ds.map hPTermD)
  let sfs := scanN fos
  let tbl := (List.range N).map fun j =>
    let d := ds.getD j (walkDBE ptr k y H rI cs (ws.getD j ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩) j)
    let v := lca.getD j (0, 0, 0)
    let q : ℕ := kr + sfs.getD j 0 - (j + 1)
    Array.ofFn (n := 166) fun c => if c = 24 ∧ (tlN' d.w.node).isCell then ((ptr d.w.node : ℕ) : ZMod P) else
      walkColDB cert H N kr q d v.1 v.2.1 v.2.2 (xAccs.getD j 0) (pAccs.getD j 0) (hxAccs.getD j 0) (hpAccs.getD j 0) c
  let xT := lastK6 xAccs
  let pT := lastK6 pAccs
  let hxT := lastK6 hxAccs
  let hpT := lastK6 hpAccs
  let pubs : ℕ → K3 := fun j =>
    if j = 0 then xT.re else if j = 1 then xT.im else if j = 2 then pT.re else if j = 3 then pT.im
    else if j = 4 then hxT.re else if j = 5 then hxT.im else if j = 6 then hpT.re else if j = 7 then hpT.im else 0
  (tbl.toArray, pubs)

/-! ## 6. The atom walk reads and the generator -/

/-- **The atom walk's reads**: per OP5 row comparing two big atoms, `(comb(a), ax₂)` and `(comb(b), ax₂)`. -/
def pairReads (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (rows : Array RowNX) : List (Noun × ℕ) :=
  rows.toList.flatMap fun r =>
    if FillX.isPairB H r then
      [(combOf (Nock.Atoms.limbs (atomV r.ftth)), (pd r).1), (combOf (Nock.Atoms.limbs (atomV r.fttt)), (pd r).1)]
    else []

/-- The generator's tables, before assembly (for diagnostics and tampers). -/
structure GenA where
  acsL : List Noun
  info : Array AInfo
  krV : ℕ

/-- **The J-8 tracegen with big atoms.** -/
def genJ8A (R : Nock.Jet.Registry) (fuel : ℕ) (s f : Noun) (χe : CoinsE) : Option InJ8 :=
  match runX R fuel s f with
  | none => none
  | some Rn =>
    if !(noJets Rn.rows) then none else
    let c : P8PublicClaim := ⟨s, f, Rn.res⟩
    let roots := rootsOf c Rn.rows
    let cs := cellsOfRoots roots
    let acsL := acsOfD (bigsOf roots Rn.rows) ((incOps Rn.rows).any fun x => x.1 + 1 = P)
    let H := hdlB cs acsL
    let pt := ptrE acsL (stopEdges Rn.rows)
    let pd := HonestPairX.pdX (sxE pt)
    let comp := compGenB c H pd Rn χe
    let (ws, kr) := walkGen (cs.headD (.atom 0)) (pathReads Rn.rows)
    let mv := mvCounts cs c
    let mx := mxCounts cs ws
    let mx1 := Array.replicate cs.length 0
    let mh := mhCounts cs comp.bases ws
    let k := coOf χe
    let α := chalsMJ8E χe 0
    let γ := chalsMJ8E χe 1
    let (cR, cP) := cellGenB k (yE χe) H (bigIdOf acsL) cs mv mx mx1 mh
    let (wR, wP) := walkGenRowsB k (yE χe) α γ H (idxN cs) HonestK8.certB8 cs ws kr
    let reads := pairReads H pd Rn.rows
    let (vs, krV) := if reads.isEmpty then ([], 0) else walkGen padN reads
    let HA := hdl acsL
    let rIA : Noun → ℕ := fun n => if n = combP then lastIdxOf acsL combP else idxN acsL n
    let (aR, aP) := atomGenE pt χe acsL (infoOfE acsL pt Rn.rows) (mbCounts acsL cs) (wCounts rIA acsL vs)
      (wCounts rIA acsL vs)
    let (vR, vP) : Array (Array (ZMod P)) × (ℕ → K3) := if krV = 0 then (#[Array.replicate 166 0], fun _ => 0)
      else walkGenRowsBE pt (coOfA χe) (yE χe) (chalsAJ8ZE χe 0) (chalsAJ8ZE χe 1) HA rIA WalkJ8.certB acsL vs krV
    let m := max comp.rows.size (max cR.size (max wR.size (max aR.size vR.size)))
    some
      { c := c
        M := { m := mOf c H, ρ := comp.ρ, ρS := comp.ρS, pubsC := cP, pubsW := wP,
               pubsJ := fun _ => 0, pubsA := aP, pubsV := vP }
        χ := χe
        r := budget m
        g := 0
        X := chipOf comp.rows
        C := chipOf cR
        W := chipOf wR
        J := ⟨1, 0, Example.ω6g, fun _ => Fin.elim0⟩
        A := chipOf aR
        V := chipOf vR
        kroots := kr
        krootsV := krV
        lay := Fin.elim0
        Rt := Example.RtG
        regs := []
        ids := []
        idx := fun _ => 0
        rk := fun _ => (0, 0) }

/-! ## 7. Tampers and diagnostics -/

/-- The first row of a chip whose column `c` is nonzero (else `0`). -/
def firstNZ (q : ChipIn) (c : ℕ) : ℕ :=
  (((List.finRange q.n).find? fun i => q.cols c i != 0).map (·.val)).getD 0

/-- **The big-atom tampers** (each must be rejected): a limb, the inc / conversion records, the boundary and
validity provides, the cell `kb` column, the compute `kb` handle column, and (atom walk present) its records. -/
def aTampersOf (I : InJ8) : List (String × InJ8) :=
  let incR := firstNZ I.A 197
  let convR := firstNZ I.A 198
  let kbR := firstNZ I.C 130
  let kbX := ((List.range 12).find? fun h => (List.finRange I.X.n).any fun i => I.X.cols (49 + h) i != 0).getD 0
  let kbXr := firstNZ I.X (49 + kbX)
  let bumpA := fun (j : ℕ) => { I.M with pubsA := (fun j' => if j' = j then I.M.pubsA j + 1 else I.M.pubsA j') }
  [("atom limb: aL + 1 on atom row 0 (bits unchanged)", { I with A := bumpCol I.A 7 0 }),
   ("atom limb bit: bit 0 of aL flipped on atom row 0", { I with A := ⟨I.A.h, I.A.n, I.A.ω,
      fun c i => if c = 130 ∧ (i : ℕ) = 0 then 1 - I.A.cols c i else I.A.cols c i⟩ }),
   (s!"inc record: old limb l_o + 1 on atom row {incR}", { I with A := bumpCol I.A 201 incR }),
   (s!"inc record: old serial idx_o + 1 on atom row {incR}", { I with A := bumpCol I.A 200 incR }),
   (s!"inc record: mi + 1 on atom row {incR}", { I with A := bumpCol I.A 204 incR }),
   ("atom mb public pubsA 6", { I with M := bumpA 6 }),
   ("atom inc public pubsA 8", { I with M := bumpA 8 }),
   (s!"compute kb of handle {kbX} cleared on row {kbXr}", { I with X := ⟨I.X.h, I.X.n, I.X.ω,
      fun c i => if c = 49 + kbX ∧ (i : ℕ) = kbXr then 0 else I.X.cols c i⟩ })] ++
  -- the conversion tamper only where a conversion row exists (else clearing the flag is a no-op)
  (if (List.finRange I.A.n).any (fun i => I.A.cols 198 i != 0) then
    [(s!"conversion flag cleared on atom row {convR}", { I with A := ⟨I.A.h, I.A.n, I.A.ω,
      fun c i => if c = 198 ∧ (i : ℕ) = convR then 0 else I.A.cols c i⟩ })] else []) ++
  -- the cell kb tamper only where a big child exists (else it would be a dead no-op)
  (if (List.finRange I.C.n).any (fun i => I.C.cols 130 i != 0) then
    [(s!"cell kbL cleared on cell row {kbR} (its big left child read as a small atom)", { I with C := ⟨I.C.h, I.C.n,
      I.C.ω, fun c i => if c = 130 ∧ (i : ℕ) = kbR then 0 else I.C.cols c i⟩ })] else []) ++
  (if I.krootsV = 0 then [] else
  [("atom-walk record: left path multiplicity mL + 1 (row 0)", { I with V := bumpCol I.V 10 0 }),
   ("atom-walk record: left child value vL + 1 (row 0)", { I with V := bumpCol I.V 22 0 }),
   ("atom-walk record: prefix pre + 1 (row 0)", { I with V := bumpCol I.V 4 0 }),
   ("atom-walk dispatch krootsV = 0 (absent claimed)", { I with krootsV := 0 }),
   ("atom-walk service public pubsV 6", { I with M := { I.M with pubsV := (fun j =>
      if j = 6 then I.M.pubsV 6 + 1 else I.M.pubsV j) } })])

/-- The failing source gates of a memory table, per row (at most `k` rows). -/
def diagM (Tm : Nock.NockVMROM.Thm54.MonolithicRAP.ChipTemplate (ZMod P)) {n : ℕ} (T : MemX.TabM n) (k : ℕ) :
    List (ℕ × List ℕ) :=
  (((List.finRange n).map fun i =>
    (i.val, ((MemX.srcM Tm).zipIdx 0).filterMap fun (g, j) =>
      if MemX.srcOK Tm.baseCols (T.env Tm i) g then none else some j)).filter fun x => !x.2.isEmpty).take k

/-- The eight public equations, one `Bool` each. -/
def pubParts (I : InJ8) : List Bool :=
  let M := I.M
  let χe := I.χ
  [eq6 (M.ρ 3 + (pp M.pubsW WalkHQ.pubXQ + pp M.pubsJ 2)) (pp M.pubsC CellHQ.pubHQ),
   eq6 (M.ρ 4) (pp M.pubsW WalkHQ.pubPQ),
   eq6 (M.ρS + pp M.pubsJ 0) (pp M.pubsA AtomChipHQ.pubMI + pp M.pubsV WalkHQ.pubPQ),
   eq6 (lsum ((claimRecsJ8E χe I.c M.m).map fun r => (compressE (γVE χe) (ρVE χe) r)⁻¹))
    (pp M.pubsC 0 + pp M.pubsA AtomChipHQ.pubMB),
   eq6 (pp M.pubsA CellHQ.pubHQ) (pp M.pubsA AtomChipHQ.pubC + pp M.pubsV WalkHQ.pubXQ),
   (eq3 (M.pubsA 0) 0 && eq3 (M.pubsA 1) 0),
   (eq3 (M.pubsC 2) (M.pubsW 0) && eq3 (M.pubsC 3) (M.pubsW 1)),
   (eq3 (M.pubsA 2) (M.pubsV 0) && eq3 (M.pubsA 3) (M.pubsV 1))]

/-! ## 8. Kernel facts (cheap, structural) -/

/-- Off big atoms the handle map is `genJ8`'s `hdl`. -/
theorem hdlB_eq_hdl (cs acsL : List Noun) (n : Noun) (hn : bigIdOf acsL n = none) : hdlB cs acsL n = hdl cs n := by
  cases n with
  | atom v =>
    by_cases h : v < P
    · simp [hdlB, hdl, h]
    · simp [bigIdOf, h] at hn
  | cell a b => rfl

/-- A big atom's handle is kind `2` at its root comb's atom-table serial. -/
theorem hdlB_big (cs acsL : List Noun) (v : ℕ) (hv : P ≤ v) : hdlB cs acsL (.atom v) = (2, rootIdx acsL v) := by
  simp [hdlB, Nat.not_lt.mpr hv]

/-- The comb spine starts at the comb. -/
theorem spineOf_head (x y : ℕ) (r : List ℕ) : (spineOf (x :: y :: r)).head? = some (combOf (x :: y :: r)) := rfl

/-- The pad row is the atom table's last row. -/
theorem acsOf_last (bigs : List ℕ) : (acsOf bigs).getLast? = some padN := by
  simp [acsOf, acsOfD]

/-- With the `p` duplicate too, the pad row is the atom table's last row. -/
theorem acsOfD_last (bigs : List ℕ) (d : Bool) : (acsOfD bigs d).getLast? = some padN := by
  simp [acsOfD]

end Nock.V1J8.Gen

#print axioms Nock.V1J8.Gen.hdlB_eq_hdl
#print axioms Nock.V1J8.Gen.hdlB_big
#print axioms Nock.V1J8.Gen.spineOf_head
#print axioms Nock.V1J8.Gen.acsOf_last
#print axioms Nock.V1J8.Gen.acsOfD_last
