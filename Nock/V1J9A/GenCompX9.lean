/-
  Nock/V1J9A/GenCompX9.lean

  EXECUTABLE evidence only (no theorem here).

  One pass over the BFS forest `W9 = bfsForest [genX9T t]` (rows `LX9`) gives the 137 twin columns of chip row `j`
  (BFS row `j + 1`, as `HonestTraceX9.trX9`):
  * `0..68`, `123..136`: `FillX9.colX9E` at the row, flags `fl1 (j+1)`, `llW W (j+1)`;
  * `69..92`: the four slot inverses `A · D⁻¹` over `slotsX9` (`slotAQ`/`slotDQ` at `slotAt9`);
  * `93..110`: the six exclusive prefix sums of `termRow9` (per-row terms over `slotsX9`);
  * `111..122`: the walk columns `ln, count, acc, walk_inv` of BFS row `j + 1` (node value `nodeV9E`).
  The table is returned in RAP column order (`RAP d = twin (invPermX9 d)`).  The six totals are the publics:
  `ρ 3 = (acc0, acc1)`, `ρ 4 = (acc2, acc3)`, `ρS = (acc4, acc5)`.
-/
import Nock.V1J9A.FillX9
import Nock.V1J9A.CompX9
import Nock.V1J8.GenComp
import Nock.V1J9.CheckJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HonestTraceX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J9A.GenCompX9

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (invPermX9)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (slotAt9)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (slotsX9)

/-! ## 1. Stage 1: the base columns -/

/-- **`basesX9`**: the honest base columns `colX9E` of chip row `j` (BFS row `j + 1`). -/
def baseFn9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
    (j : ℕ) : ℕ → ZMod P :=
  FillX9.colX9E P H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1))

/-- The base column functions of the `|W|` chip rows. -/
def basesX9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9)) :
    List (ℕ → ZMod P) :=
  (List.range W.length).map fun j => baseFn9 H pd idOf W j

/-- The stage-1 environment of chip row `j` (current / next base rows). -/
def envX9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
    (pub : ℕ → ZMod P) (χe : CoinsE) (j : ℕ) : Nock.Reified.Env (ZMod P) :=
  ⟨baseFn9 H pd idOf W j, baseFn9 H pd idOf W (j + 1), Example.chalE χe, pub⟩

/-! ## 2. Stage 2: slot inverses and accumulator terms -/

/-- The twin slot inverse `A · D⁻¹` of slot `k` at an environment (`Example.invE` over `slotAt9`). -/
def invE9 (e : Nock.Reified.Env (ZMod P)) (k : ℕ) : K6 :=
  let S := slotAt9 (F := ZMod P) k
  Example.qE e (HonestSlotX.slotAQ (ZMod P) deltaF S) * (Example.qE e (HonestSlotX.slotDQ (ZMod P) deltaF S))⁻¹

/-- The four twin slot inverses of a row. -/
def invsOf9 (e : Nock.Reified.Env (ZMod P)) : Array K6 := Array.ofFn (n := 4) fun s => invE9 e s

/-- The activities of the four twin slots into balance `bl` (coin-free base environment). -/
def actsOf9 (e : Nock.Reified.Env (ZMod P)) (bl : ChipHX.Bal) : List (ZMod P) :=
  (slotsX9 (F := ZMod P)).map fun S => (S.actB bl).eval e

/-- **The 18 per-row accumulator terms** (accumulator `a = i / 3`, coordinate `k = i % 3`) over `slotsX9`. -/
def termRow9 (e : Nock.Reified.Env (ZMod P)) (iv : Array K6) : Array (ZMod P) :=
  Array.ofFn (n := 18) fun i =>
    let a := (i : ℕ) / 3
    let k := (i : ℕ) % 3
    ((actsOf9 e (accSpecE a).1).zipIdx 0).foldl (fun s (x : ZMod P × ℕ) =>
      let v := iv.getD x.2 0
      s + x.1 * limbZ (if (accSpecE a).2 then v.im else v.re) k) 0

/-! ## 3. The walk columns -/

/-- The honest twin walk node value `rlcL γ 0 (nodeLab9E u)`. -/
def nodeV9E (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (γ : K3)
    (u : NTree LX9) : K3 :=
  let vs : List K3 := (FillX9.nodeLab9E P H pd idOf u).map k3
  (vs.foldl (fun (st : K3 × K3) v => (st.1 + st.2 * v, st.2 * γ)) (0, 1)).1

/-- **The walk values** `(ln, cnt, acc, inv)` of BFS rows `1 .. |W|` (`α`, `γ`: the walk coins). -/
def walkVals9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
    (α γ : K3) : List (K3 × K3 × K3 × K3) :=
  let step := fun (st : List (K3 × K3 × K3 × K3) × K3 × K3 × K3 × K3 × ℕ) (u : NTree LX9) =>
    match st with
    | (out, lnP, cntP, accP, aSf, i) =>
      let fo := u.children.length
      let ln := if i = 0 then α else lnP * α
      let cnt := if i = 0 then α * CompX.powK α fo else cntP * CompX.powK α fo
      let cs := (u.children.zipIdx 1).foldl
        (fun s (ch : NTree LX9 × ℕ) => s + nodeV9E H pd idOf γ ch.1 * CompX.powK α ch.2 * aSf) 0
      let cur := nodeV9E H pd idOf γ u
      let acc := if i = 0 then α * cs else accP - cur * ln + α * cs
      (out ++ [(ln, cnt, acc, (cnt - ln)⁻¹)], ln, cnt, acc, aSf * CompX.powK α fo, i + 1)
  (W.foldl step ([], 0, 0, 0, 1, 0)).1

/-! ## 4. The table -/

/-- **Twin column `c`** (`0..136`) of a compute row: base, slot inverse limbs, accumulators, walk values. -/
def compColD9 (b : ℕ → ZMod P) (iv : Array K6) (a : Array (ZMod P)) (v : K3 × K3 × K3 × K3) (c : ℕ) : ZMod P :=
  if c < 69 ∨ 123 ≤ c then b c
  else if c < 93 then
    let w := iv.getD ((c - 69) / 6) 0
    if (c - 69) % 6 < 3 then limbZ w.re ((c - 69) % 6) else limbZ w.im ((c - 69) % 6 - 3)
  else if c < 111 then a.getD (c - 93) 0
  else
    let x := if (c - 111) / 3 = 0 then v.1 else if (c - 111) / 3 = 1 then v.2.1 else if (c - 111) / 3 = 2 then
      v.2.2.1 else v.2.2.2
    limbZ x ((c - 111) % 3)

/-- The generator's output: the 137-column rows (RAP order), the publics `ρ`, `ρS`, the base column functions. -/
structure CompOut9 where
  rows : Array (Array (ZMod P))
  ρ : Fin 5 → K6
  ρS : K6
  bases : List (ℕ → ZMod P)

/-- The six accumulator totals at the publics `pub` (the prefix-sum total). -/
def totals9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
    (pub : ℕ → ZMod P) (χe : CoinsE) : Array (ZMod P) :=
  (prefixSums 18 ((List.range W.length).map fun j =>
    let e := envX9 H pd idOf W pub χe j
    termRow9 e (invsOf9 e))).2

/-- The publics `ρ`, `ρS` read off the totals (§0: `ρ 3 = (acc0, acc1)`, `ρ 4 = (acc2, acc3)`, `ρS = (acc4, acc5)`). -/
def rhoOfTot (tot : Array (ZMod P)) : (Fin 5 → K6) × K6 :=
  (fun i =>
    if (i : ℕ) = 3 then ⟨CompX.readK (fun c => tot.getD c 0) 0, CompX.readK (fun c => tot.getD c 0) 3⟩
    else if (i : ℕ) = 4 then ⟨CompX.readK (fun c => tot.getD c 0) 6, CompX.readK (fun c => tot.getD c 0) 9⟩
    else 0,
   ⟨CompX.readK (fun c => tot.getD c 0) 12, CompX.readK (fun c => tot.getD c 0) 15⟩)

/-- The 137-column RAP-order table at the publics `pub`. -/
def compTable9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
    (pub : ℕ → ZMod P) (χe : CoinsE) : Array (Array (ZMod P)) :=
  let es := (List.range W.length).map fun j => envX9 H pd idOf W pub χe j
  let ivs := es.map invsOf9
  let accs := (prefixSums 18 ((es.zip ivs).map fun (e, iv) => termRow9 e iv)).1
  let wv := walkVals9 H pd idOf W (χe ⟨13, by decide⟩) (χe ⟨14, by decide⟩)
  ((List.range W.length).map fun j =>
    let b := baseFn9 H pd idOf W j
    let iv := ivs.getD j #[]
    let a := accs.getD j #[]
    let v := wv.getD j (0, 0, 0, 0)
    Array.ofFn (n := 137) fun d => compColD9 b iv a v (invPermX9 d)).toArray

/-- **The twin compute tracegen**: pass 1 at the publics without `ρ, ρS` gives the totals, hence `ρ`, `ρS`; then
the table at the final publics `pubVJ9E`. -/
def compGenX9 (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (χe : CoinsE) : CompOut9 :=
  let m := mOf c H
  let pub0 := Nock.V1J9.Check9.pubVJ9E c m (fun _ => 0) 0 χe
  let r := rhoOfTot (totals9 H pd idOf W pub0 χe)
  ⟨compTable9 H pd idOf W (Nock.V1J9.Check9.pubVJ9E c m r.1 r.2 χe) χe, r.1, r.2, basesX9 H pd idOf W⟩

/-- The executable table for `CompX9.checkCompX9`. -/
def tabOf9 (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (O : CompOut9) (χe : CoinsE) (n : ℕ)
    (nodes : Fin n → ZMod p) (ω : ZMod p) : CompX9.TabX9 n :=
  ⟨nodes, ω, colsOf O.rows n, Example.chalE χe, Nock.V1J9.Check9.pubVJ9E c (mOf c H) O.ρ O.ρS χe⟩

end Nock.V1J9A.GenCompX9
