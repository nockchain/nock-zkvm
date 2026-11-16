/-
  Nock/V1J8/GenComp.lean

  **The general J-8 compute tracegen.**

  One pass over `genX R fuel s f` (BFS order `bfsForest [t]`, as `HonestTraceX.trX`) gives the 123 compute columns
  of every row:
  * `0.. 68`: `FillX.colXE` (`= HonestCompX.colX`, B4750) at the row's noun row, first / last flags;
  * `69.. 92`: the four `𝕂′` slot inverses `A · D⁻¹` (`Example.invE`, the honest `invV` formula);
  * `93.. 110`: the six accumulators (export / path / service, Re / Im), the EXCLUSIVE prefix sums of the
    per-row terms `termCoord (slots) k` (`HonestTraceX.accV`, through `coord_termVal`);
  * `111.. 122`: the walk columns `ln, count, acc, walk_inv` at BFS row `j + 1` (the closed forms `lnW`, `cntW`,
    `accW` of `HonestTraceX`, computed by their recurrences: `ln₁ = α`, `cnt₁ = α·α^{fo₁}`,
    `acc₁ = α·cs₁`, `acc_{k+1} = acc_k − cur_{k+1}·α^{k+1} + α·cs_{k+1}`, `cs_i = Σ_l chld_{i,l}·α^{l+Sf(i−1)}`).
  The accumulator totals are the compute publics `ρ₃` (export), `ρ₄` (path), `ρ_S` (service).

  The handle map is `hdl cells`: small atom `(0, v)`, big atom `(2, 0)`, cell `(1, its index in cells)` (`0` when
  absent, as `InhabJ8MemDom.H0`).  The tables are arrays (filled once); the chip reads them through `colsOf`.
-/
import Nock.V1J8.Example
import Nock.Edit.GenXRows

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J8.Gen

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (Slot termCoord)

abbrev P : ℕ := Nock.Field.p

/-! ## 1. The run -/

/-- The generated run: its tree, result, BFS forest and noun rows (BFS order). -/
structure RunX where
  t : NTree SkelX
  res : Noun
  W : List (NTree SkelX)
  rows : Array RowNX

def runX (R : Nock.Jet.Registry) (fuel : ℕ) (s f : Noun) : Option RunX :=
  match genX R fuel s f with
  | some (t, r) =>
    let W := Nock.Walk.bfsForest [t]
    some ⟨t, r, W, (W.map fun u => rowOfSkelX u.label).toArray⟩
  | none => none

/-! ## 2. The cell list and the handle map -/

/-- Pre-order, first-occurrence insertion of a noun's cells (parent before children). -/
def addCells : Noun → List Noun → List Noun
  | .atom _, acc => acc
  | .cell a b, acc =>
    if Noun.cell a b ∈ acc then acc else addCells b (addCells a (acc ++ [Noun.cell a b]))

/-- The cells of a list of roots, in first-occurrence pre-order. -/
def cellsOfRoots (roots : List Noun) : List Noun := roots.foldl (fun acc n => addCells n acc) []

/-- The index of a cell in the list (`0` when absent). -/
def idxD : List Noun → Noun → ℕ
  | [], _ => 0
  | c :: cs, n => if c = n then 0 else idxD cs n + 1

/-- `idxD` with the `0` default for an absent noun. -/
def idxOf (cs : List Noun) (n : Noun) : ℕ := if n ∈ cs then idxD cs n else 0

/-- **The handle map** of a cell list: small atom `(0, v)`, big atom `(2, 0)`, cell `(1, serial)`. -/
def hdl (cs : List Noun) : Noun → ℕ × ℕ
  | .atom v => if v < P then (0, v) else (2, 0)
  | .cell a b => (1, idxOf cs (.cell a b))

/-- The demand roots: the claim's nouns, then every row's six handle nouns. -/
def rootsOf (c : P8PublicClaim) (rows : Array RowNX) : List Noun :=
  [c.subject, c.formula, c.result] ++ rows.toList.flatMap handleNounsX

/-- The claim message of a claim under a handle map (as `InhabJ8Comp.mC0`). -/
def mOf (c : P8PublicClaim) (H : Noun → ℕ × ℕ) : FrameVS.ClaimMsgVS := fun k =>
  ((H (FrameVS.claimNoun c k)).2, AcceptsJ8P.rkC (FrameVS.claimNoun c k))

/-! ## 3. Compute: base, inverses, accumulators -/

/-- The first / last flags of chip row `j` of `n`. -/
def flag (b : Bool) : ZMod P := if b then 1 else 0

/-- Round-0 columns `0.. 68` of row `j` of `n`, as a function (`FillX.colXE`). -/
def baseFn (H : Noun → ℕ × ℕ) (n j : ℕ) (r : RowNX) : ℕ → ZMod P := fun c =>
  FillX.colXE H (HonestPairX.pdX InhabJ8Comp.sx0) r (flag (j == 0)) (flag (j + 1 == n)) c

/-- The row environment at the coins (current = next: the slot templates read the current row; as
`Example.env0E`). -/
def envX (b : ℕ → ZMod P) (pub : ℕ → ZMod P) (χe : CoinsE) : Nock.Reified.Env (ZMod P) :=
  ⟨b, b, Example.chalE χe, pub⟩

/-- The coin-free row environment (the slot activities and record heads read base columns only). -/
def envB (b : ℕ → ZMod P) : Nock.Reified.Env (ZMod P) := ⟨b, b, fun _ => 0, fun _ => 0⟩

/-- The four slot inverses `A · D⁻¹` of a row (`Example.invE`). -/
def invsOf (e : Nock.Reified.Env (ZMod P)) : Array K6 := Array.ofFn (n := 4) fun s => Example.invE e s

/-- The 24 inverse limbs `69.. 92` of a row (slot `(c − 69) / 6`, Re limbs then Im limbs). -/
def invRow (iv : Array K6) : Array (ZMod P) :=
  Array.ofFn (n := 24) fun o =>
    let v := iv.getD ((o : ℕ) / 6) 0
    if (o : ℕ) % 6 < 3 then limbZ v.re ((o : ℕ) % 6) else limbZ v.im ((o : ℕ) % 6 - 3)

/-- The accumulator slots `(bal, im)` of accumulator `a` (`HonestTraceX.accSpec` order). -/
def accSpecE : ℕ → ChipHX.Bal × Bool
  | 0 => (.x, false) | 1 => (.x, true) | 2 => (.p, false) | 3 => (.p, true) | 4 => (.s, false) | _ => (.s, true)

/-- The activities of the four slots into balance `bl` at a row (coin-free). -/
def actsOf (b : ℕ → ZMod P) (bl : ChipHX.Bal) : List (ZMod P) :=
  (ChipHX.slotsX (F := ZMod P)).map fun S => (S.actB bl).eval (envB b)

/-- **The 18 per-row accumulator terms** (accumulator `a = i / 3`, coordinate `k = i % 3`):
`Σ_s act_s · limb_k(inv_s)` (Re or Im), i.e. `termCoord (slots) k` read at the row (`coord_termVal`). -/
def termRow (b : ℕ → ZMod P) (iv : Array K6) : Array (ZMod P) :=
  Array.ofFn (n := 18) fun i =>
    let a := (i : ℕ) / 3
    let k := (i : ℕ) % 3
    ((actsOf b (accSpecE a).1).zipIdx 0).foldl (fun s (x : ZMod P × ℕ) =>
      let v := iv.getD x.2 0
      s + x.1 * limbZ (if (accSpecE a).2 then v.im else v.re) k) 0

/-- Exclusive prefix sums of a list of equal-length rows (`out[j] = Σ_{j' < j} rows[j']`), and the total. -/
def prefixSums (w : ℕ) (rows : List (Array (ZMod P))) : List (Array (ZMod P)) × Array (ZMod P) :=
  rows.foldl (fun (st : List (Array (ZMod P)) × Array (ZMod P)) r =>
      (st.1 ++ [st.2], Array.ofFn (n := w) fun i => st.2.getD i 0 + r.getD i 0))
    ([], Array.replicate w 0)

/-- A record entry's value at a row. -/
def reVal (b : ℕ → ZMod P) : ChipHX.RE → ZMod P
  | .col i => b i
  | .k c => (c : ZMod P)

/-- **The consumed records of balance `bl` at a row** (coin-free): every active entry of every slot, and both
records of an active batched pair, each repeated by its activity. -/
def consOf (b : ℕ → ZMod P) (bl : ChipHX.Bal) : List (List (ZMod P)) :=
  (ChipHX.slotsX (F := ZMod P)).flatMap fun S =>
    ((S.ents.filter fun x => decide (x.bal = bl)).flatMap fun x =>
      List.replicate ((x.act.eval (envB b)).val) (x.rcd.map (reVal b))) ++
    (match S.pair with
     | some (fl, ra, rb, b') =>
       if b' = bl then List.replicate (b fl).val (ra.map (reVal b)) ++ List.replicate (b fl).val (rb.map (reVal b))
       else []
     | none => [])

/-- A record as a `𝕂′` vector (as `Example.vec5`). -/
def recVec (m : ℕ) (l : List (ZMod P)) : Fin m → K6 := fun c => g6 ((l.map Gold.ofZ).getD c 0)

/-- The handle-coin total `Σ (compress (γH′, ρH′) rec)⁻¹` of a list of records of length `m`. -/
def recTot (m : ℕ) (χe : CoinsE) (rs : List (List (ZMod P))) : K6 :=
  rs.foldr (fun r s => (compressE (γHE χe) (ρHE χe) (recVec m r))⁻¹ + s) 0

/-! ## 4. Compute: the walk columns -/

/-- `x ∈ 𝔽` as a `K3`. -/
def k3 (x : ZMod P) : K3 := g3 (Gold.ofZ x)

/-- The honest walk node value `rlcL γ 0 (hlX H (s, f, e))` (`nodeValX`). -/
def nodeValE (H : Noun → ℕ × ℕ) (γ : K3) (u : NTree SkelX) : K3 :=
  let t := HonestWalkX.tripOf u
  let vs : List K3 := [((H t.1).1 : ZMod P), ((H t.1).2 : ZMod P), ((H t.2.1).1 : ZMod P),
    ((H t.2.1).2 : ZMod P), ((H t.2.2).1 : ZMod P), ((H t.2.2).2 : ZMod P)].map k3
  (vs.foldl (fun (st : K3 × K3) v => (st.1 + st.2 * v, st.2 * γ)) (0, 1)).1

/-- **The walk values** `(ln, cnt, acc, inv)` of BFS rows `1.. |W|` (`α`, `γ`: the walk coins). -/
def walkVals (H : Noun → ℕ × ℕ) (W : List (NTree SkelX)) (α γ : K3) : List (K3 × K3 × K3 × K3) :=
  let step := fun (st : List (K3 × K3 × K3 × K3) × K3 × K3 × K3 × K3 × ℕ) (u : NTree SkelX) =>
    -- st: (out, ln_prev, cnt_prev, acc_prev, αSf_prev = α^{Sf(i-1)}, i - 1)
    match st with
    | (out, lnP, cntP, accP, aSf, i) =>
      let fo := u.children.length
      let ln := if i = 0 then α else lnP * α
      let cnt := if i = 0 then α * CompX.powK α fo else cntP * CompX.powK α fo
      let cs := (u.children.zipIdx 1).foldl
        (fun s (ch : NTree SkelX × ℕ) => s + nodeValE H γ ch.1 * CompX.powK α ch.2 * aSf) 0
      let cur := nodeValE H γ u
      let acc := if i = 0 then α * cs else accP - cur * ln + α * cs
      (out ++ [(ln, cnt, acc, (cnt - ln)⁻¹)], ln, cnt, acc, aSf * CompX.powK α fo, i + 1)
  (W.foldl step ([], 0, 0, 0, 1, 0)).1

/-! ## 5. The compute table -/

/-- **Column `c` of a compute row**: base, slot inverse limbs, accumulators, walk values. -/
def compColD (b : ℕ → ZMod P) (iv : Array K6) (a : Array (ZMod P)) (v : K3 × K3 × K3 × K3) (c : ℕ) : ZMod P :=
  if c < 69 then b c
  else if c < 93 then
    let w := iv.getD ((c - 69) / 6) 0
    if (c - 69) % 6 < 3 then limbZ w.re ((c - 69) % 6) else limbZ w.im ((c - 69) % 6 - 3)
  else if c < 111 then a.getD (c - 93) 0
  else
    let x := if (c - 111) / 3 = 0 then v.1 else if (c - 111) / 3 = 1 then v.2.1 else if (c - 111) / 3 = 2 then v.2.2.1
      else v.2.2.2
    limbZ x ((c - 111) % 3)

/-- The compute generator's output: the 123-column rows, the publics `ρ`, `ρS`, the base column functions. -/
structure CompOut where
  rows : Array (Array (ZMod P))
  ρ : Fin 5 → K6
  ρS : K6
  bases : List (ℕ → ZMod P)

/-- The base column functions of the rows. -/
def basesOf (H : Noun → ℕ × ℕ) (Rn : RunX) : List (ℕ → ZMod P) :=
  (Rn.rows.toList.zipIdx 0).map fun (r, j) => baseFn H Rn.rows.size j r

/-- `ρ₃` / `ρ₄`: the export / path records the rows consume (their handle-coin totals). -/
def rhoOfB (χe : CoinsE) (bs : List (ℕ → ZMod P)) : Fin 5 → K6 := fun i =>
  if (i : ℕ) = 3 then recTot 5 χe (bs.flatMap fun b => consOf b .x)
  else if (i : ℕ) = 4 then recTot 4 χe (bs.flatMap fun b => consOf b .p) else 0

/-- `ρ_S`: the service accumulator's total (at the publics without it). -/
def rhoSOf (c : P8PublicClaim) (m : FrameVS.ClaimMsgVS) (ρ : Fin 5 → K6) (χe : CoinsE) (bs : List (ℕ → ZMod P)) :
    K6 :=
  let pub0 := pubVJ8E c m ρ 0 χe
  let tot := (prefixSums 18 (bs.map fun b => termRow b (invsOf (envX b pub0 χe)))).2
  ⟨CompX.readK (fun c => tot.getD c 0) 12, CompX.readK (fun c => tot.getD c 0) 15⟩

/-- The 123-column table at the publics `pub`. -/
def compTable (H : Noun → ℕ × ℕ) (Rn : RunX) (pub : ℕ → ZMod P) (χe : CoinsE) (bs : List (ℕ → ZMod P)) :
    Array (Array (ZMod P)) :=
  let ivs := bs.map fun b => invsOf (envX b pub χe)
  let accs := (prefixSums 18 ((bs.zip ivs).map fun (b, iv) => termRow b iv)).1
  let wv := walkVals H Rn.W (χe ⟨13, by decide⟩) (χe ⟨14, by decide⟩)
  ((List.range Rn.rows.size).map fun j =>
    let b := bs.getD j (fun _ => 0)
    let iv := ivs.getD j #[]
    let a := accs.getD j #[]
    let v := wv.getD j (0, 0, 0, 0)
    Array.ofFn (n := 123) fun c => compColD b iv a v c).toArray

/-- **The compute tracegen.**  `ρ₃ ρ₄` from the consumed records, `ρ_S` from the service accumulator (pass 1), then
the columns at the publics. -/
def compGen (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (Rn : RunX) (χe : CoinsE) : CompOut :=
  let m := mOf c H
  let bs := basesOf H Rn
  let ρ := rhoOfB χe bs
  let ρS := rhoSOf c m ρ χe bs
  ⟨compTable H Rn (pubVJ8E c m ρ ρS χe) χe bs, ρ, ρS, bs⟩

/-- A table's column function (`0` off the table). -/
def colsOf (tbl : Array (Array (ZMod P))) (n : ℕ) : ℕ → Fin n → ZMod P :=
  fun c i => (tbl.getD i #[]).getD c 0

end Nock.V1J8.Gen
