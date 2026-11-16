/-
  Nock/V1J8/GenMem.lean

  **The general J-8 memory tracegen (cell KW, walk J8).**

  * **Multiplicities**: `mv` = the claim's cells + the in-table child references; `mx` = one per walk row at its
    node; `mx1 = 0` (no selector-1 consumer without big atoms / jets); `mh` = the compute's export consumes (the
    active `.x` entries of the four slots, read at the row: record head = the cell serial) + one per walk row.
  * **Cell rows** (`cellRowE`, 242 columns) and **walk rows** (`walkRowE`, 166 columns) in the layouts of
    `FillMem.Cell.colZ` / `FillMem.Walk.colZ` (B4751 / B4752), for any cell list and trie forest.
-/
import Nock.V1J8.GenComp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J8.Gen

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.CoordinateCompiler

/-! ## 1. Small helpers -/

def two62 : ℕ := 2 ^ 62

def hdN' : Noun → Noun
  | .cell a _ => a
  | n => n
def tlN' : Noun → Noun
  | .cell _ b => b
  | n => n

def atomV : Noun → ℕ
  | .atom v => v
  | _ => 0

/-- The rank bit `k` (`0.. 61` of `mu % 2^62`, `62..` of `mu / 2^62`). -/
def rankBit (mu k : ℕ) : ℕ := if k < 62 then (if (mu % two62).testBit k then 1 else 0)
  else (if (mu / two62).testBit (k - 62) then 1 else 0)

/-- Inclusive prefix sums of a list of `K6`. -/
def scanK6 (l : List K6) : List K6 :=
  (l.foldl (fun (st : List K6 × K6) x => (st.1 ++ [st.2 + x], st.2 + x)) ([], 0)).1

/-- The last element (or `0`). -/
def lastK6 (l : List K6) : K6 := l.getLastD 0

/-! ## 2. The walk -/

/-- The binary digits of an axis after the leading one, root first. -/
def axisBits (a : ℕ) : List Bool := go a a
where
  go : ℕ → ℕ → List Bool
    | 0, _ => []
    | f + 1, a => if 2 ≤ a then go f (a / 2) ++ [decide (a % 2 = 1)] else []

def sideTails (b : Bool) (T : List (List Bool)) : List (List Bool) :=
  T.filterMap fun t => match t with
    | c :: s => if c = b then some s else none
    | [] => none

def contT (b : Bool) (T : List (List Bool)) : List (List Bool) := (sideTails b T).filter fun s => !s.isEmpty
def contB (b : Bool) (T : List (List Bool)) : Bool := !(contT b T).isEmpty
def multT (b : Bool) (T : List (List Bool)) : ℕ := (sideTails b T).count []

/-- A walk row's data. -/
structure WRow where
  node : Noun
  root : Noun
  pre : ℕ
  len : ℕ
  cL : Bool
  cR : Bool
  mL : ℕ
  mR : ℕ
deriving DecidableEq

inductive TN where
  | mk (w : WRow) (kids : List TN)

def TN.label : TN → WRow
  | .mk w _ => w
def TN.kids : TN → List TN
  | .mk _ ks => ks

/-- The read trie at a node. -/
def trie (root : Noun) : Noun → ℕ → ℕ → List (List Bool) → TN
  | .atom a, pre, len, T => .mk ⟨.atom a, root, pre, len, false, false, multT false T, multT true T⟩ []
  | .cell l r, pre, len, T =>
    .mk ⟨.cell l r, root, pre, len, contB false T, contB true T, multT false T, multT true T⟩
      ((if contB false T then [trie root l (2 * pre) (len + 1) (contT false T)] else []) ++
       (if contB true T then [trie root r (2 * pre + 1) (len + 1) (contT true T)] else []))

/-- Level-order flatten with fuel. -/
def bfsTN : ℕ → List TN → List WRow
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, l@(_ :: _) => l.map TN.label ++ bfsTN k (l.flatMap TN.kids)

/-- The path reads `(root, axis)` of the rows (axis `≥ 2`). -/
def pathReads (rows : Array RowNX) : List (Noun × ℕ) :=
  (rows.toList.flatMap fun r => (consEntriesX r).map fun x => (x.1, x.2.1)).filter fun p => 2 ≤ p.2

/-- Group the reads by root (first occurrence order). -/
def groupReads (rs : List (Noun × ℕ)) : List (Noun × List (List Bool)) :=
  let roots := rs.foldl (fun acc p => if p.1 ∈ acc then acc else acc ++ [p.1]) []
  roots.map fun r => (r, (rs.filter fun p => p.1 = r).map fun p => axisBits p.2)

/-- **The walk forest** (BFS rows and the number of roots). -/
def walkGen (dummy : Noun) (rs : List (Noun × ℕ)) : List WRow × ℕ :=
  let gs := groupReads rs
  let forest : List TN := if gs.isEmpty then [trie dummy dummy 1 0 []] else gs.map fun g => trie g.1 g.1 1 0 g.2
  (bfsTN 70 forest, forest.length)

/-! ## 3. Multiplicities -/

/-- Count the occurrences of a cell serial. -/
def bump (a : Array ℕ) (i m : ℕ) : Array ℕ := if i < a.size then a.modify i (· + m) else a

/-- `mv`: the claim's cells and every in-table child reference. -/
def mvCounts (cs : List Noun) (c : P8PublicClaim) : Array ℕ :=
  let a0 := Array.replicate cs.length 0
  let refs := cs.flatMap fun n => [hdN' n, tlN' n]
  let claim := [c.subject, c.formula, c.result]
  (refs ++ claim).foldl (fun a n => match n with
    | .cell _ _ => bump a (idxOf cs n) 1
    | .atom _ => a) a0

/-- `mx`: one per walk row at its node. -/
def mxCounts (cs : List Noun) (ws : List WRow) : Array ℕ :=
  ws.foldl (fun a w => match w.node with
    | .cell _ _ => bump a (idxOf cs w.node) 1
    | .atom _ => a) (Array.replicate cs.length 0)

/-- The compute's export consumes at one row's environment: `(serial, multiplicity)` of every active `.x` entry. -/
def xConsumes (e : Nock.Reified.Env (ZMod P)) : List (ℕ × ℕ) :=
  (ChipHX.slotsX (F := ZMod P)).flatMap fun S =>
    (S.ents.filter fun x => decide (x.bal = ChipHX.Bal.x)).filterMap fun x =>
      let a := (x.act.eval e).val
      if a = 0 then none
      else match x.rcd with
        | ChipHX.RE.col i :: _ => some ((e.trace i).val, a)
        | _ => none

/-- `mh`: the compute's export consumes + one per walk row. -/
def mhCounts (cs : List Noun) (bs : List (ℕ → ZMod P)) (ws : List WRow) : Array ℕ :=
  let a := bs.foldl (fun a b => (xConsumes (envB b)).foldl (fun a p => bump a p.1 p.2) a) (Array.replicate cs.length 0)
  ws.foldl (fun a w => match w.node with
    | .cell _ _ => bump a (idxOf cs w.node) 1
    | .atom _ => a) a

/-! ## 4. The cell rows -/

/-- The handle of a noun as `K6` scalars `(lq kind, lq value)`. -/
def hK (H : Noun → ℕ × ℕ) (n : Noun) : K6 × K6 := (lq (H n).1, lq (H n).2)

/-- The per-row data of cell row `j` (noun `n`). -/
structure CellD where
  j : ℕ
  l : Noun
  r : Noun
  pE : FPE
  lE : FPE
  rE : FPE
  mu : ℕ
  muL : ℕ
  muR : ℕ
  idL : ℕ
  idR : ℕ
  vInv : K6
  lInv : K6
  rInv : K6
  x0Inv : K6
  x1Inv : K6
  ivH : K6

/-- The rank `(lo, hi)` as a `𝕂′` scalar pair. -/
def rkK (mu : ℕ) : K6 := ⟨g3 (natG (mu % two62)), g3 (natG (mu / two62))⟩

/-- **The data of cell row `j`.** -/
def cellD (k : Co) (y : K6) (cs : List Noun) (n : Noun) (j : ℕ) : CellD :=
  let H := hdl cs
  let l := hdN' n
  let r := tlN' n
  let pE := encE k.z y n
  let lE := encE k.z y l
  let rE := encE k.z y r
  let idL := if l.isCell then idxOf cs l else 0
  let idR := if r.isCell then idxOf cs r else 0
  let xKey (s : ℕ) : Fin 11 → K6 :=
    ![pE.size, pE.dyck, pE.leaf, lE.size, lE.dyck, lE.leaf, rE.size, rE.dyck, rE.leaf, lq j, lq s]
  { j := j, l := l, r := r, pE := pE, lE := lE, rE := rE, mu := n.internal, muL := l.internal,
    muR := r.internal, idL := idL, idR := idR
    vInv := (compressE k.γ k.ρ ![pE.size, pE.dyck, pE.leaf, rkK n.internal, lq j])⁻¹
    lInv := if l.isCell then (compressE k.γ k.ρ ![lE.size, lE.dyck, lE.leaf, rkK l.internal, lq idL])⁻¹ else 0
    rInv := if r.isCell then (compressE k.γ k.ρ ![rE.size, rE.dyck, rE.leaf, rkK r.internal, lq idR])⁻¹ else 0
    x0Inv := (compressE k.γ k.ρ (xKey 0))⁻¹
    x1Inv := (compressE k.γ k.ρ (xKey 1))⁻¹
    ivH := (compressE k.γH k.ρH ![lq j, (hK H l).1, (hK H l).2, (hK H r).1, (hK H r).2])⁻¹ }

def vTermD (mv : Array ℕ) (d : CellD) : K6 := lq (mv.getD d.j 0) * d.vInv - d.lInv - d.rInv
def xTermD (mx mx1 : Array ℕ) (d : CellD) : K6 := lq (mx.getD d.j 0) * d.x0Inv + lq (mx1.getD d.j 0) * d.x1Inv
def hTermD (mh : Array ℕ) (d : CellD) : K6 := lq (mh.getD d.j 0) * d.ivH

/-- The `𝕂′` slot `s` of a cell row (`CellVals.qslot`), the accumulators `va xa` given. -/
def qslotD (d : CellD) (va xa : K6) : ℕ → K6
  | 0 => d.pE.size | 1 => d.pE.dyck | 2 => d.pE.leaf
  | 3 => d.lE.size | 4 => d.lE.dyck | 5 => d.lE.leaf
  | 6 => d.rE.size | 7 => d.rE.dyck | 8 => d.rE.leaf
  | 9 => d.vInv | 10 => d.lInv | 11 => d.rInv | 12 => d.x0Inv | 13 => va | 14 => xa
  | _ => d.x1Inv

/-- The base columns `2.. 128`. -/
def cellBaseD (mv mx mx1 : Array ℕ) (d : CellD) (c : ℕ) : ZMod P :=
  if c = 2 then (d.j : ZMod P) else if c = 3 then (d.idL : ZMod P) else if c = 4 then (d.idR : ZMod P)
  else if c = 5 then flag d.l.isCell else if c = 6 then flag d.r.isCell
  else if c = 7 then (atomV d.l : ZMod P) else if c = 8 then (atomV d.r : ZMod P)
  else if c = 9 then ((d.mu % two62 : ℕ) : ZMod P) else if c = 10 then ((d.mu / two62 : ℕ) : ZMod P)
  else if c = 11 then ((d.muL % two62 : ℕ) : ZMod P) else if c = 12 then ((d.muL / two62 : ℕ) : ZMod P)
  else if c = 13 then ((d.muR % two62 : ℕ) : ZMod P) else if c = 14 then ((d.muR / two62 : ℕ) : ZMod P)
  else if c = 15 then (((d.muL % two62 + d.muR % two62 + 1) / two62 : ℕ) : ZMod P)
  else if c = 16 then (mv.getD d.j 0 : ZMod P) else if c = 17 then (mx.getD d.j 0 : ZMod P)
  else if c < 128 then (rankBit d.mu (c - 18) : ZMod P)
  else (mx1.getD d.j 0 : ZMod P)

/-- **Column `c` of a cell row** (242 columns; `D` rows; accumulators `va xa ha`). -/
def cellColD (D : ℕ) (mv mx mx1 mh : Array ℕ) (d : CellD) (va xa ha : K6) (c : ℕ) : ZMod P :=
  if c = 0 then flag (d.j == 0) else if c = 1 then flag (d.j + 1 == D)
  else if c < 129 then cellBaseD mv mx mx1 d c
  else if c = 129 then (mh.getD d.j 0 : ZMod P)
  else if c < 132 then 0
  else if c = 132 then ((d.muL % two62 + d.muL / two62 : ℕ) : ZMod P)⁻¹
  else if c = 133 then ((d.muR % two62 + d.muR / two62 : ℕ) : ZMod P)⁻¹
  else if c < 230 then
    let ρ := (c - 134) / 3
    limbZ (if ρ % 2 = 0 then (qslotD d va xa (ρ / 2)).re else (qslotD d va xa (ρ / 2)).im) ((c - 134) % 3)
  else if c < 233 then limbZ d.ivH.re (c - 230) else if c < 236 then limbZ d.ivH.im (c - 233)
  else if c < 239 then limbZ ha.re (c - 236) else limbZ ha.im (c - 239)

/-- **The cell table** (242 columns per row) and its six publics. -/
def cellGen (k : Co) (y : K6) (cs : List Noun) (mv mx mx1 mh : Array ℕ) : Array (Array (ZMod P)) × (ℕ → K3) :=
  let D := cs.length
  let ds := (cs.zipIdx 0).map fun (n, j) => cellD k y cs n j
  let vAccs := scanK6 (ds.map (vTermD mv))
  let xAccs := scanK6 (ds.map (xTermD mx mx1))
  let hAccs := scanK6 (ds.map (hTermD mh))
  let tbl := (List.range D).map fun j =>
    let d := ds.getD j (cellD k y cs (.atom 0) j)
    let va := vAccs.getD j 0
    let xa := xAccs.getD j 0
    let ha := hAccs.getD j 0
    Array.ofFn (n := 242) fun c => cellColD D mv mx mx1 mh d va xa ha c
  let vT := lastK6 vAccs
  let xT := lastK6 xAccs
  let hT := lastK6 hAccs
  let pubs : ℕ → K3 := fun j =>
    if j = 0 then vT.re else if j = 1 then vT.im else if j = 2 then xT.re else if j = 3 then xT.im
    else if j = 4 then hT.re else if j = 5 then hT.im else 0
  (tbl.toArray, pubs)

/-! ## 5. The walk rows -/

/-- `rlc γ v = Σ_c γ^c v_c`. -/
def rlcE (γ : K3) (vs : List K3) : K3 :=
  (vs.foldl (fun (st : K3 × K3) v => (st.1 + st.2 * v, st.2 * γ)) (0, 1)).1

/-- The walk label encoding `enc` (15 `𝕂` entries). -/
def encW (p root : FPE) (pre ridx len : ℕ) : List K3 :=
  [p.size.re, p.size.im, p.dyck.re, p.dyck.im, p.leaf.re, p.leaf.im, g3 (natG pre),
   root.size.re, root.size.im, root.dyck.re, root.dyck.im, root.leaf.re, root.leaf.im, g3 (natG ridx),
   g3 (natG len)]

/-- The J-8 walk certificate (`HonestK8.certB8`). -/
def certB (L i : ℕ) : ℕ := HonestK8.certB8 L i

/-- The per-row data of walk row `j`. -/
structure WalkD where
  w : WRow
  j : ℕ
  pE : FPE
  lE : FPE
  rE : FPE
  rootE : FPE
  idx : ℕ
  ridx : ℕ
  xInv : K6
  pInvL : K6
  pInvR : K6
  hXi : K6
  hPLi : K6
  hPRi : K6

/-- The fanout of a walk row. -/
def foW (w : WRow) : ℕ := (if w.cL then 1 else 0) + (if w.cR then 1 else 0)

/-- The serial of a walk node (`D` for an atom). -/
def idxN (cs : List Noun) (n : Noun) : ℕ := match n with | .cell _ _ => idxOf cs n | .atom _ => cs.length

/-- **The data of walk row `j`.** -/
def walkD (k : Co) (y : K6) (cs : List Noun) (w : WRow) (j : ℕ) : WalkD :=
  let H := hdl cs
  let pE := encE k.z y w.node
  let lE := encE k.z y (hdN' w.node)
  let rE := encE k.z y (tlN' w.node)
  let rootE := encE k.z y w.root
  let idx := idxN cs w.node
  let ridx := idxN cs w.root
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

def pTermD (d : WalkD) : K6 := lq d.w.mL * d.pInvL + lq d.w.mR * d.pInvR
def hPTermD (d : WalkD) : K6 := lq d.w.mL * d.hPLi + lq d.w.mR * d.hPRi
def curD (γ : K3) (d : WalkD) : K3 := rlcE γ (encW d.pE d.rootE d.w.pre d.ridx d.w.len)

/-- The fingerprint slots `p l r root` of a walk row. -/
def fpD (d : WalkD) : ℕ → K6
  | 0 => d.pE.size | 1 => d.pE.dyck | 2 => d.pE.leaf | 3 => d.lE.size | 4 => d.lE.dyck | 5 => d.lE.leaf
  | 6 => d.rE.size | 7 => d.rE.dyck | 8 => d.rE.leaf | 9 => d.rootE.size | 10 => d.rootE.dyck | _ => d.rootE.leaf

/-- The `𝕂′` IO slots `xInv pInvL pInvR xAcc pAcc`. -/
def ioD (d : WalkD) (xa pa : K6) : ℕ → K6
  | 0 => d.xInv | 1 => d.pInvL | 2 => d.pInvR | 3 => xa | _ => pa

/-- The handle slots `xi pl pr xa pa`. -/
def hsD (d : WalkD) (hxa hpa : K6) : ℕ → K6
  | 0 => d.hXi | 1 => d.hPLi | 2 => d.hPRi | 3 => hxa | _ => hpa

/-- The `𝕂` roles of a walk row (`ρ < 24` fingerprints, `24 25 26` = `ln cnt acc`, then the IO slots). -/
def wroleD (d : WalkD) (ln cnt acc : K3) (xa pa : K6) (ρ : ℕ) : K3 :=
  if ρ < 24 then (if ρ % 2 = 0 then (fpD d (ρ / 2)).re else (fpD d (ρ / 2)).im)
  else if ρ = 24 then ln else if ρ = 25 then cnt else if ρ = 26 then acc
  else if (ρ - 27) % 2 = 0 then (ioD d xa pa ((ρ - 27) / 2)).re else (ioD d xa pa ((ρ - 27) / 2)).im

/-- **Column `c` of a walk row** (166 columns). -/
def walkColD (H : Noun → ℕ × ℕ) (N kr q : ℕ) (d : WalkD) (ln cnt acc : K3) (xa pa hxa hpa : K6) (c : ℕ) :
    ZMod P :=
  if c = 0 then flag (d.j == 0) else if c = 1 then flag (d.j + 1 == N) else if c = 2 then flag (decide (d.j < kr))
  else if c = 3 then (d.idx : ZMod P) else if c = 4 then (d.w.pre : ZMod P) else if c = 5 then (d.ridx : ZMod P)
  else if c = 6 then (d.w.len : ZMod P) else if c = 7 then flag d.w.cL else if c = 8 then flag d.w.cR
  else if c = 9 then flag (d.w.cL && d.w.cR) else if c = 10 then (d.w.mL : ZMod P)
  else if c = 11 then (d.w.mR : ZMod P)
  else if c = 12 then (q : ZMod P) else if c = 13 then (q : ZMod P)⁻¹
  else if c = 14 then ((certB d.w.len 1 * certB d.w.len 2 : ℕ) : ZMod P)
  else if c < 21 then (certB d.w.len (c - 15) : ZMod P)
  else if c = 21 then ((H (hdN' d.w.node)).1 : ZMod P) else if c = 22 then ((H (hdN' d.w.node)).2 : ZMod P)
  else if c = 23 then ((H (tlN' d.w.node)).1 : ZMod P) else if c = 24 then ((H (tlN' d.w.node)).2 : ZMod P)
  else if c < 136 then limbZ (wroleD d ln cnt acc xa pa ((c - 25) / 3)) ((c - 25) % 3)
  else
    let t := (c - 136) / 3
    limbZ (if t % 2 = 0 then (hsD d hxa hpa (t / 2)).re else (hsD d hxa hpa (t / 2)).im) ((c - 136) % 3)

/-- The walk recurrences `(ln, cnt, acc)` over the rows (`α^kr` the preloaded roots). -/
def walkLCA (α : K3) (kr : ℕ) (fos : List ℕ) (ccs curs : List K3) : List (K3 × K3 × K3) :=
  (((fos.zip ccs).zipIdx 0).foldl (fun (st : List (K3 × K3 × K3) × K3 × K3 × K3) (fc, i) =>
    match st with
    | (out, lnP, cntP, accP) =>
      let ln := if i = 0 then α else α * lnP
      let cnt := if i = 0 then CompX.powK α kr * CompX.powK α fc.1 else cntP * CompX.powK α fc.1
      let acc := if i = 0 then CompX.powK α kr * fc.2
        else accP + cntP * fc.2 - (if i < kr then 0 else ln * curs.getD i 0)
      (out ++ [(ln, cnt, acc)], ln, cnt, acc)) ([], 0, 0, 0)).1

/-- The children sums `cc_j = Σ_{l ≤ fo_j} α^l cur(child_l)` (row `j`'s children start at `kr + Σ_{j'<j} fo`). -/
def childSums (α : K3) (kr : ℕ) (fos : List ℕ) (curs : Array K3) : List K3 :=
  (fos.foldl (fun (st : List K3 × ℕ) f =>
    let cc := ((List.range f).map fun l => CompX.powK α (l + 1) * curs.getD (st.2 + l) 0).foldl (· + ·) 0
    (st.1 ++ [cc], st.2 + f)) ([], kr)).1

/-- Inclusive prefix sums of `ℕ`. -/
def scanN (l : List ℕ) : List ℕ := (l.foldl (fun (st : List ℕ × ℕ) x => (st.1 ++ [st.2 + x], st.2 + x)) ([], 0)).1

/-- **The walk table** (166 columns per row) and its eight publics. -/
def walkGenRows (k : Co) (y : K6) (α γ : K3) (cs : List Noun) (ws : List WRow) (kr : ℕ) :
    Array (Array (ZMod P)) × (ℕ → K3) :=
  let H := hdl cs
  let N := ws.length
  let ds := (ws.zipIdx 0).map fun (w, j) => walkD k y cs w j
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
    let d := ds.getD j (walkD k y cs (ws.getD j ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩) j)
    let v := lca.getD j (0, 0, 0)
    let q : ℕ := kr + sfs.getD j 0 - (j + 1)
    let xa := xAccs.getD j 0
    let pa := pAccs.getD j 0
    let hxa := hxAccs.getD j 0
    let hpa := hpAccs.getD j 0
    Array.ofFn (n := 166) fun c => walkColD H N kr q d v.1 v.2.1 v.2.2 xa pa hxa hpa c
  let xT := lastK6 xAccs
  let pT := lastK6 pAccs
  let hxT := lastK6 hxAccs
  let hpT := lastK6 hpAccs
  let pubs : ℕ → K3 := fun j =>
    if j = 0 then xT.re else if j = 1 then xT.im else if j = 2 then pT.re else if j = 3 then pT.im
    else if j = 4 then hxT.re else if j = 5 then hxT.im else if j = 6 then hpT.re else if j = 7 then hpT.im else 0
  (tbl.toArray, pubs)

end Nock.V1J8.Gen
