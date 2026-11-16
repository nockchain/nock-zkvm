/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8Data.lean

`j8DataOf p Rg Rt hgen` transcribes the DATA of the J-8 generators (`V1J8/GenJ8`, `GenAtom`, `GenJet`) at a
  GENERIC modulus `p` (the generators are computable at Goldilocks `P`; every `P` they read is `p` here):
  * the run's rows (`bfsForest [t]`, BFS order), the claim `(s, f, r)`;
  * the calls (`callsOf`), the called ids (`ids`), the registered ids, the J nouns (`jNouns`: each registered compiled formula, each call's
    subject and honest node values), the registry publics `idx`, `rk`, `lay`;
  * the cell list `cells = cellsOfRoots (rootsOf ++ jNouns)` (first-occurrence pre-order);
  * the big atoms (`bigs`: every leaf `≥ p`), the atom cell list `acs` (comb spines, link order, the `p` duplicate,
    the pad row), the handle map `H = hdlB` and the op-5 limb data `pd = pdX (sxPP p acs rows)` (J9BC5A: the pointer; `sxOf` before);
  * the path reads and the J-8 walk rows `ws` / roots `kr`; the atom-walk reads `preads` and rows `vs` / roots `krV`;
  * the multiplicities `mv` (claim + child refs + registry pins), `mx` (walk rows), `mh` (compute export
    consumes + walk rows + J export reads), `mb` (big children of cells), `mxA` / `mhA` (atom-walk rows), the atom
    table's inc / conversion data `info`;
  * the J rows `jrows` (`ChipJ8.honestJ8` + the `mv` fix by the in-chip consumers and the registry pins);
  * row counts and orbit heights of the six tables (`hOf`), the budgets `rows`, `g = |regs|`.

  **Not here (the assembler's, L6):** the orbits themselves (`StrictOrbitDomain (ZMod p) 3 h` needs
  `3·2^h ∣ p − 1`, a field binder as the 40th's `hF`); the coin-dependent honest totals (a follow-up section of
  this file, phase L0b).

  Sanity lemmas: `cells_nodup`; `mem_cells_of_subcell` (every cell sub-noun of a demand root, in particular of
  every row handle noun, is a cell of the table); `H_small` / `H_big` / `H_cell` (so `HdlOK p H`, `hdlOK`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
import Nock.V1J8.GenAtom
import Nock.V1J8.GenJet
import Nock.Jet.ChipJ8HG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.V1J8.Gen (cellsOfRoots addCells rootsOf idxOf idxD combOf spineOf padN linkOrder addNew lastIdxOf
  sxOf incChain AInfo atomV hdN' tlN' idxN pathReads walkGen mvCounts mxCounts mvPins wCounts bump callsOf
  WRow budget)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (CRow PRow layoutJ8 keysOf entsX)
open Nock.Jet.RapJetJ8 (consKT provKT tlF)

noncomputable section

/-! ## 1. The generator's `P`-dependent pieces at a generic modulus `p` -/

section Gen
variable (p : ℕ)

/-- **The big atoms** (`GenAtom.bigsOf` at `p`): every leaf `≥ p` of the roots and the rows' twelve handles. -/
def bigsP (roots : List Noun) (rows : Array RowNX) : List ℕ :=
  ((((roots ++ rows.toList.flatMap rowHandleNounsX).flatMap leavesOf).filter fun a => decide (p ≤ a)).dedup).mergeSort
    (fun a b => decide (a ≤ b))

/-- The comb of `p`. -/
def combPP : Noun := combOf (Nock.Atoms.limbs p)

/-- **The atom cell list** (`GenAtom.acsOfD` at `p`). -/
def acsP (bigs : List ℕ) (dupP : Bool) : List Noun :=
  let L := bigs.foldl (fun acc a => addNew acc (spineOf (Nock.Atoms.limbs a))) []
  linkOrder L ++ (if dupP && decide (Noun.cell (.atom 0) (combPP p) ∈ L) then [combPP p] else []) ++ [padN]

/-- The atom-table serial of a big atom's root comb (`GenAtom.rootIdx` at `p`). -/
def rootIdxP (acsL : List Noun) (a : ℕ) : ℕ :=
  if a = p then lastIdxOf acsL (combPP p) else idxOf acsL (combOf (Nock.Atoms.limbs a))

/-- **The handle map** (`GenAtom.hdlB` at `p`): small `(0, v)`, big `(2, root serial)`, cell `(1, serial)`. -/
def hdlP (cs acsL : List Noun) : Noun → ℕ × ℕ
  | .atom v => if v < p then (0, v) else (2, rootIdxP p acsL v)
  | .cell a b => (1, idxOf cs (.cell a b))

/-- **The J handle map**: the cell table's handle `hdlP`, cast into `ZMod p` (`hd := cast ∘ hdlP`).  The honest
J rows use it (`honestJ8G`), so a big child / big subject carries `(2, root serial)`, exactly as the cell table does. -/
def hJd (p : ℕ) [Fact p.Prime] (cs acsL : List Noun) : Noun → ZMod p × ZMod p := fun y =>
  ((((hdlP p cs acsL y).1 : ℕ) : ZMod p), (((hdlP p cs acsL y).2 : ℕ) : ZMod p))

theorem hJd_cell (p : ℕ) [Fact p.Prime] (cs acsL : List Noun) (l r : Noun) : (hJd p cs acsL (.cell l r)).1 = 1 := by
  simp [hJd, hdlP]

theorem hJd_atom_ne (p : ℕ) [Fact p.Prime] (cs acsL : List Noun) (v : ℕ) : (hJd p cs acsL (.atom v)).1 ≠ 1 := by
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h2 : (2 : ZMod p) ≠ 1 := by
    intro h
    have : (1 : ZMod p) = 0 := by linear_combination h
    exact h1 this
  unfold hJd hdlP
  by_cases hv : v < p
  · simp [hv]
  · simp [hv]; exact h2

theorem hJd_small (p : ℕ) [Fact p.Prime] (cs acsL : List Noun) (v : ℕ) (hv : v < p) :
    hJd p cs acsL (.atom v) = (0, (v : ZMod p)) := by
  simp [hJd, hdlP, hv]

/-- The atom-table root serial of a noun if it is a big atom (`GenAtom.bigIdOf` at `p`). -/
def bigIdOfP (acsL : List Noun) : Noun → Option ℕ
  | .atom v => if v < p then none else some (rootIdxP p acsL v)
  | .cell _ _ => none

/-- The slow OP4 operands (`GenAtom.incOps` at `p`). -/
def incOpsP (rows : Array RowNX) : List (ℕ × ℕ) :=
  let vs := rows.toList.filterMap fun r => match r.st, r.sf1 with
    | .s4, .atom v => if p ≤ v + 1 then some v else none
    | _, _ => none
  vs.dedup.map fun v => (v, vs.count v)

/-- **The row key of an atom-table noun** (G12 variant 3): `comb p` is keyed at its LAST copy (the conversion copy
when the table duplicates it), every other noun at its first. -/
def keyP (acsL : List Noun) (n : Noun) : ℕ :=
  if n = combPP p then lastIdxOf acsL (combPP p) else idxOf acsL n

/-- **A stop edge `x` of the run** (G12 variant 4, `stopEdges`): some slow OP4 operand `v` (not the conversion
`v + 1 = p`) has, at some depth `d`, the old suffix `x :: limbs p` with `x ≠ B − 1` (a stop step: the old row
`[x comb p]` and the new row `[x+1 comb p]`), every shallower old suffix carrying (`headD = B − 1`).  This is the
`incChain` stop step whose old row has tail `comb p`. -/
def StopE (rows : Array RowNX) (x : ℕ) : Prop :=
  ∃ vc ∈ incOpsP p rows, vc.1 + 1 ≠ p ∧ ∃ d, (Nock.Atoms.limbs vc.1).drop d = x :: Nock.Atoms.limbs p ∧
    x ≠ Nock.Atoms.B - 1 ∧ ∀ i < d, ((Nock.Atoms.limbs vc.1).drop i).headD 0 = Nock.Atoms.B - 1

/-- **The FIRST component** (G12 variant 4): head `x` lies in the stop-edge component of `0`, i.e. every edge
`0, …, x − 1` is a stop edge.  (`compOf x = 0` of the spike, as a predicate: no fuel.) -/
def FirstC (rows : Array RowNX) (x : ℕ) : Prop := ∀ y < x, StopE p rows y

open Classical in
/-- **The per-component tail pointer of an atom-table row `n`**: a row
`[x comb p]` takes the FIRST copy of `comb p` when `x` is in the component of `0` (`FirstC`), else the LAST copy;
every other row the first copy of its tail.  A row `[0 comb p]` is always FIRST (link order).  Under the spike's
generator this is `ptrG4`'s value: its FIRST components are `⊆ {compOf 0}`, and when `[0 comb p]` is not
link-forced there is no duplicate, so both copies coincide. -/
def ptrP (acsL : List Noun) (rows : Array RowNX) (n : Noun) : ℕ :=
  if tlN' n = combPP p ∧ ¬ FirstC p rows (atomV (hdN' n)) then lastIdxOf acsL (combPP p) else idxOf acsL (tlN' n)

/-- The right child `(wR, valR)` of an atom-table row at a pointer `ptr` (`GenAtom.valROf` re-keyed). -/
def valROfK (ptr : Noun → ℕ) (n : Noun) : ℕ × ℕ :=
  match tlN' n with
  | .cell _ _ => (1, ptr n)
  | .atom v => (0, v)

/-- **The op-5 pair spine serial at the pointer**: the suffix comb of `a` at
depth `e ≥ 1` is the TAIL of the row at depth `e − 1`, so its serial is that parent row's tail pointer `ptrP`
(`sxOf` reads `idxOf` of the suffix itself; the two agree when `lastIdxOf = idxOf` at `comb p`, `sxPP_eq_sxOf`). -/
def sxPP (acsL : List Noun) (rows : Array RowNX) (a e : ℕ) : ℕ :=
  ptrP p acsL rows ((spineOf (Nock.Atoms.limbs a)).getD (e - 1) (.atom 0))

/-- **The atom-walk child handle at the pointer** (J9BC5A): the handle a read `(root, axis)` of the atom walk
carries.  A cell child at an odd axis `2a + 1 ≥ 3` is the tail of the noun at axis `a`, so it is keyed by that
PARENT's tail pointer `ptrP` (the atom table's `idR`); every other child is the generator's `hdl acs`. -/
def chPP (acsL : List Noun) (rows : Array RowNX) (x : Noun × ℕ) : ℕ × ℕ :=
  match (Noun.slot x.2 x.1).getD (.atom 0) with
  | .cell l r =>
    if x.2 % 2 = 1 ∧ 2 ≤ x.2 then (1, ptrP p acsL rows ((Noun.slot (x.2 / 2) x.1).getD (.atom 0)))
    else Nock.V1J8.Gen.hdl acsL (.cell l r)
  | .atom v => Nock.V1J8.Gen.hdl acsL (.atom v)

/-- **The inc chain at a row key `key` and tail pointer `ptr`** (`GenAtom.incChain` with `jo := key o`,
`(kRO, vRO) := valROfK ptr o`). -/
def incChainK (acsL : List Noun) (key ptr : Noun → ℕ) : ℕ → List Noun → List Noun → Array AInfo → Array AInfo
  | 0, _, _, a => a
  | _ + 1, [], _, a => a
  | _ + 1, _ :: _, [], a => a
  | f + 1, n :: ns, o :: os, a =>
    let jn := idxOf acsL n
    let jo := key o
    let lO := atomV (hdN' o)
    let (kRO, vRO) := valROfK ptr o
    let cout := decide (lO = Nock.Atoms.B - 1)
    let a := a.modify jn fun x => { x with inc := true, cout := cout, idxO := jo, lO := lO, kRO := kRO, vRO := vRO }
    let a := a.modify jo fun x => { x with mhx := x.mhx + 1 }
    if cout && kRO == 1 then incChainK acsL key ptr f ns os a else a

/-- The inc / conversion data of the atom table (`GenAtom.infoOf` at `p`, G12 variant 3 keys, variant 4 pointer:
the chains keyed by `keyP` / `ptrP p acsL rows`; no `fixOld`). -/
def infoOfP (acsL : List Noun) (rows : Array RowNX) : Array AInfo := Nock.V1J8.Gen.recountMhx <|
  (incOpsP p rows).foldl (fun a (v, c) =>
    if v + 1 = p then
      a.modify (rootIdxP p acsL p) fun x => { x with conv := true, mi := x.mi + c }
    else
      let a := incChainK acsL (keyP p acsL) (ptrP p acsL rows) ((spineOf (Nock.Atoms.limbs v)).length + 1)
        (spineOf (Nock.Atoms.limbs (v + 1))) (spineOf (Nock.Atoms.limbs v)) a
      a.modify (rootIdxP p acsL (v + 1)) fun x => { x with mi := x.mi + c })
    (Array.replicate acsL.length AInfo.z)

/-! ### The variant-4 pointer: component facts -/

/-- The head `0` is in the FIRST component (no edge below it). -/
theorem firstC_zero (rows : Array RowNX) : FirstC p rows 0 := fun _ hy => absurd hy (Nat.not_lt_zero _)

/-- **Same component across a stop edge**: if `x` is a stop edge, `x + 1` is FIRST iff
`x` is. -/
theorem firstC_succ_iff {rows : Array RowNX} {x : ℕ} (h : StopE p rows x) :
    FirstC p rows (x + 1) ↔ FirstC p rows x := by
  constructor
  · intro hf y hy; exact hf y (by omega)
  · intro hf y hy
    rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
    · exact hf y hy
    · exact h

/-- A chain stops at most once: two stop depths of one old limb list coincide. -/
theorem stop_depth_unique {l : List ℕ} {d d' y y' : ℕ} {t t' : List ℕ}
    (h : l.drop d = y :: t) (hy : y ≠ Nock.Atoms.B - 1) (hi : ∀ i < d, (l.drop i).headD 0 = Nock.Atoms.B - 1)
    (h' : l.drop d' = y' :: t') (hy' : y' ≠ Nock.Atoms.B - 1)
    (hi' : ∀ i < d', (l.drop i).headD 0 = Nock.Atoms.B - 1) : d = d' := by
  rcases lt_trichotomy d d' with hlt | heq | hgt
  · have := hi' d hlt; rw [h] at this; exact absurd this hy
  · exact heq
  · have := hi d' hgt; rw [h'] at this; exact absurd this hy'

/-- `|incOps| ≤ rows`. -/
theorem incOpsP_length_le (rows : Array RowNX) : (incOpsP p rows).length ≤ rows.size := by
  simp only [incOpsP, List.length_map]
  refine (List.dedup_sublist _).length_le.trans ((List.length_filterMap_le _ _).trans ?_)
  simp

/-- **No conflict**: under the rows bound `rows ≤ 2^31`, the head `B − 1` is not in the
FIRST component.  A FIRST `B − 1` needs all `B − 1 = 2^32 − 1` stop edges `0, …, B − 2`; each comes from a distinct
slow OP4 operand (a chain stops at most once), and there are at most `rows ≤ 2^31` of them. -/
theorem not_firstC_top (rows : Array RowNX) (hrows : rows.size ≤ 2 ^ 31) :
    ¬ FirstC p rows (Nock.Atoms.B - 1) := by
  intro hF
  classical
  have hS : ∀ y ∈ Finset.range (Nock.Atoms.B - 1), StopE p rows y := fun y hy => hF y (Finset.mem_range.mp hy)
  choose! g hg using hS
  have hinj : Set.InjOn (fun y => (g y).1) (Finset.range (Nock.Atoms.B - 1) : Set ℕ) := by
    intro y hy y' hy' he
    obtain ⟨-, -, d, h1, h2, h3⟩ := hg y (Finset.mem_coe.mp hy)
    obtain ⟨-, -, d', h1', h2', h3'⟩ := hg y' (Finset.mem_coe.mp hy')
    simp only at he
    rw [he] at h1 h3
    have hd := stop_depth_unique h1 h2 h3 h1' h2' h3'
    subst hd
    rw [h1] at h1'
    exact (List.cons.inj h1').1
  have hc := Finset.card_le_card_of_injOn (fun y => (g y).1)
    (t := ((incOpsP p rows).map Prod.fst).toFinset) (by
      intro y hy
      exact List.mem_toFinset.mpr (List.mem_map_of_mem (hg y (Finset.mem_coe.mp hy)).1)) hinj
  rw [Finset.card_range] at hc
  have h2 := List.toFinset_card_le ((incOpsP p rows).map Prod.fst)
  rw [List.length_map] at h2
  have h3 := incOpsP_length_le p rows
  have hB : Nock.Atoms.B = 4294967296 := Nock.Atoms.B_eq
  have h31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  omega

/-- Off `comb p` the pointer is the first copy of the tail. -/
theorem ptrP_of_tl_ne (acsL : List Noun) (rows : Array RowNX) {n : Noun} (h : tlN' n ≠ combPP p) :
    ptrP p acsL rows n = idxOf acsL (tlN' n) := by
  unfold ptrP; rw [if_neg (fun hc => h hc.1)]

/-- In the FIRST component the pointer is the first copy of the tail. -/
theorem ptrP_of_firstC (acsL : List Noun) (rows : Array RowNX) {n : Noun} (h : FirstC p rows (atomV (hdN' n))) :
    ptrP p acsL rows n = idxOf acsL (tlN' n) := by
  unfold ptrP; rw [if_neg (fun hc => hc.2 h)]

/-- Out of the FIRST component a row `[x comb p]` points at the LAST copy of `comb p`. -/
theorem ptrP_of_not_firstC (acsL : List Noun) (rows : Array RowNX) {n : Noun} (ht : tlN' n = combPP p)
    (h : ¬ FirstC p rows (atomV (hdN' n))) : ptrP p acsL rows n = lastIdxOf acsL (combPP p) := by
  unfold ptrP; rw [if_pos ⟨ht, h⟩]

/-- **Milestone 0 (J-8 binders)**: without a duplicate of `comb p` the pointer is the first copy of the tail. -/
theorem ptrP_eq_idxOf (acsL : List Noun) (rows : Array RowNX)
    (h : lastIdxOf acsL (combPP p) = idxOf acsL (combPP p)) (n : Noun) :
    ptrP p acsL rows n = idxOf acsL (tlN' n) := by
  unfold ptrP; split_ifs with hc
  · rw [h, hc.1]
  · rfl

/-- `mb` (`GenAtom.mbCounts` at `p`): one per cell-table child that is a big atom, at the atom root. -/
def mbCountsP (acsL cs : List Noun) : Array ℕ :=
  (cs.flatMap fun n => [hdN' n, tlN' n]).foldl (fun a n => match bigIdOfP p acsL n with
    | some i => bump a i 1
    | none => a) (Array.replicate acsL.length 0)

/-- The atom walk's reads (`GenAtom.pairReads`). -/
def pairReadsP (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (rows : Array RowNX) : List (Noun × ℕ) :=
  rows.toList.flatMap fun r =>
    if Nock.V1J8.FillX.isPairB H r then
      [(combOf (Nock.Atoms.limbs (atomV r.ftth)), (pd r).1), (combOf (Nock.Atoms.limbs (atomV r.fttt)), (pd r).1)]
    else []

variable [Fact p.Prime]

/-- `0 / 1` flag in `ZMod p`. -/
def flagP (b : Bool) : ZMod p := if b then 1 else 0

/-- **The compute base columns** of the rows (`GenAtom.basesOfB` at `p`): row `j`'s round-0 column function. -/
def basesP (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (rows : Array RowNX) : List (ℕ → ZMod p) :=
  (rows.toList.zipIdx 0).map fun (r, j) => fun c =>
    Nock.V1J8.FillX.colXE (F := ZMod p) H pd r (flagP p (j == 0)) (flagP p (j + 1 == rows.size)) c

/-- The compute's export consumes at one row's environment (`GenMem.xConsumes` at `p`). -/
def xConsumesP (e : Nock.Reified.Env (ZMod p)) : List (ℕ × ℕ) :=
  (ChipHX.slotsX (F := ZMod p)).flatMap fun S =>
    (S.ents.filter fun x => decide (x.bal = ChipHX.Bal.x)).filterMap fun x =>
      let a := (x.act.eval e).val
      if a = 0 then none
      else match x.rcd with
        | ChipHX.RE.col i :: _ => some ((e.trace i).val, a)
        | _ => none

/-- `mh` (`GenMem.mhCounts` at `p`): the compute's export consumes + one per walk row. -/
def mhCountsP (cs : List Noun) (bs : List (ℕ → ZMod p)) (ws : List WRow) : Array ℕ :=
  let a := bs.foldl (fun a b => (xConsumesP p (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))).foldl
    (fun a q => bump a q.1 q.2) a) (Array.replicate cs.length 0)
  ws.foldl (fun a w => match w.node with
    | .cell _ _ => bump a (idxOf cs w.node) 1
    | .atom _ => a) a

/-- The honest node values of a call (`GenJet.callVals` at `p`). -/
def callValsP (Rt : ℕ → Tpl) (c : ℕ) (cl : ℕ × Noun) : List Noun :=
  (Nock.Jet.Interp.honestRows p (Rt cl.1) cl.2 c).map Nock.Jet.Interp.JRow.val

/-- The J chip's nouns (`GenJet.jNouns` at `p`). -/
def jNounsP (Rt : ℕ → Tpl) (regs : List ℕ) (calls : List (ℕ × Noun)) : List Noun :=
  regs.map (fun i => compile p (Rt i)) ++ (calls.zipIdx.flatMap fun (cl, c) => cl.2 :: callValsP p Rt c cl)

/-- The verifier's registry pins (`GenJet.pinsOf` at `p`). -/
def pinsOfP (regs : List ℕ) (idx : ℕ → ℕ) : List (List (ZMod p)) :=
  regs.map fun id => tlF (Nock.Jet.PinJ8.pinKey (F := ZMod p) id (idx id))

/-- **The `mv` fix** (`GenJet.mvFix` at `p`, by counting instead of a hash map): a provider's `mv` = its in-chip
consumers + the registry pins of its key. -/
def mvFixP (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) : List (CRow (ZMod p)) :=
  let cons := rows.flatMap consKT ++ pins
  rows.map fun r => match provKT r with
    | [k] => { r with w := { r.w with mv := ((cons.count k : ℕ) : ZMod p) } }
    | _ => { r with w := { r.w with mv := 0 } }

/-- `mh` + one per J export read (`GenJet.mhJ` at `p`). -/
def mhJP (mh : Array ℕ) (rows : List (CRow (ZMod p))) : Array ℕ :=
  rows.foldl (fun a r => (keysOf entsX r).foldl (fun a κ => bump a (κ.headD 0).val 1) a) mh

end Gen

/-! ## 2. The interface -/

/-- The BFS rows of a generated tree. -/
def rowsOfT (t : NTree SkelX) : Array RowNX := ((bfsForest [t]).map fun u => rowOfSkelX u.label).toArray

/-- **The honest J-8 generator data of one run** at modulus `p`. -/
structure J8Data (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (fuel : ℕ) (s f r : Noun) where
  /-- the run -/
  t : NTree SkelX
  hgen : genX Rg.R fuel s f = some (t, r)
  rows : Array RowNX
  /-- jets: the template table, the calls, the called and the registered ids, the J nouns, the registry publics -/
  Rt : ℕ → Tpl
  calls : List (ℕ × Noun)
  ids : List ℕ
  regs : List ℕ
  jn : List Noun
  idx : ℕ → ℕ
  rk : ℕ → ℕ × ℕ
  lay : List PRow
  /-- the cell list, the big atoms, the atom cell list, the handles, the op-5 limb data -/
  roots : List Noun
  cells : List Noun
  bigs : List ℕ
  dupP : Bool
  acs : List Noun
  H : Noun → ℕ × ℕ
  pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)
  /-- the J-8 walk and the atom walk -/
  reads : List (Noun × ℕ)
  ws : List WRow
  kr : ℕ
  preads : List (Noun × ℕ)
  vs : List WRow
  krV : ℕ
  /-- the compute base columns, the J rows -/
  bases : List (ℕ → ZMod p)
  jrows : List (CRow (ZMod p))
  /-- multiplicities: cell table `mv mx mh`, atom table `mb mxA mhA` and its inc data -/
  mv : Array ℕ
  mx : Array ℕ
  mh : Array ℕ
  mb : Array ℕ
  mxA : Array ℕ
  mhA : Array ℕ
  info : Array AInfo

/-- **The J-8 instance: the six tables' row counts and orbit heights, the budgets** (kept out of `J8Data` so that
J-9 A / B can add tables; `j8CountsOf`). -/
structure J8Counts where
  n : ℕ
  nC : ℕ
  nW : ℕ
  nJ : ℕ
  nA : ℕ
  nV : ℕ
  h : ℕ
  hC : ℕ
  hW : ℕ
  hJ : ℕ
  hA : ℕ
  hV : ℕ
  budget : FrameJ8.RowsJ8
  g : ℕ

/-- The atom walk's root serial map (`p`'s root at its last row). -/
def rIAP (p : ℕ) (acs : List Noun) : Noun → ℕ := fun n =>
  if n = combPP p then lastIdxOf acs (combPP p) else idxN acs n

/-- **The honest data of a run** at modulus `p`, registry `Rg`, template table `Rt`. -/
def j8DataOf (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) : J8Data p Rg fuel s f r :=
  let rows := rowsOfT t
  let c : P8PublicClaim := ⟨s, f, r⟩
  let calls := callsOf rows
  let ids := calls.map Prod.fst
  let regs := ids.dedup
  let jn := jNounsP p Rt regs calls
  let roots := rootsOf c rows ++ jn
  let cs := cellsOfRoots roots
  let idx : ℕ → ℕ := fun id => idxOf cs (compile p (Rt id))
  let bigs := bigsP p roots rows
  let dupP := (incOpsP p rows).any fun x => x.1 + 1 = p
  let acs := acsP p bigs dupP
  let H := hdlP p cs acs
  let pd := HonestPairX.pdX (sxPP p acs rows)
  let reads := Nock.V1J8.Gen.pathReads rows
  let wg := walkGen (cs.headD (.atom 0)) reads
  let preads := pairReadsP H pd rows
  let vg : List WRow × ℕ := if preads.isEmpty then ([], 0) else walkGen padN preads
  let bases := basesP p H pd rows
  let jrows := mvFixP p (Nock.Jet.ChipJ8.honestJ8G (hJd p cs acs) Rt regs calls) (pinsOfP p regs idx)
  let lay := layoutJ8 Rt regs ids
  { t := t
    hgen := hgen
    rows := rows
    Rt := Rt
    calls := calls
    ids := ids
    regs := regs
    jn := jn
    idx := idx
    rk := fun id => AcceptsJ8P.rkC (compile p (Rt id))
    lay := lay
    roots := roots
    cells := cs
    bigs := bigs
    dupP := dupP
    acs := acs
    H := H
    pd := pd
    reads := reads
    ws := wg.1
    kr := wg.2
    preads := preads
    vs := vg.1
    krV := vg.2
    bases := bases
    jrows := jrows
    mv := mvPins (mvCounts cs c) regs idx
    mx := mxCounts cs wg.1
    mh := mhJP p (mhCountsP p cs bases wg.1) jrows
    mb := mbCountsP p acs cs
    mxA := wCounts (rIAP p acs) acs vg.1
    mhA := wCounts (rIAP p acs) acs vg.1
    info := infoOfP p acs rows }

/-- **The J-8 table sizes of the data** (compute, cell, walk, J, atom, atom walk; the atom walk is the one-row
pad when absent), heights `hOf`, budgets `max 10 (2·largest)`, `g = |regs|`. -/
def j8CountsOf {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
    (D : J8Data p Rg fuel s f r) : J8Counts :=
  let nV := if D.krV = 0 then 1 else D.vs.length
  { n := D.rows.size
    nC := D.cells.length
    nW := D.ws.length
    nJ := D.lay.length
    nA := D.acs.length
    nV := nV
    h := Nock.V1J8.Gen.hOf D.rows.size
    hC := Nock.V1J8.Gen.hOf D.cells.length
    hW := Nock.V1J8.Gen.hOf D.ws.length
    hJ := Nock.V1J8.Gen.hOf D.lay.length
    hA := Nock.V1J8.Gen.hOf D.acs.length
    hV := Nock.V1J8.Gen.hOf nV
    budget := budget (max D.rows.size (max D.cells.length (max D.ws.length (max D.acs.length
      (max nV D.lay.length)))))
    g := D.regs.length }

/-! ## 3. Sanity lemmas -/

section Sanity

/-- `addCells` only appends. -/
theorem subset_addCells (n : Noun) (acc : List Noun) : ∀ x ∈ acc, x ∈ addCells n acc := by
  induction n generalizing acc with
  | atom a => intro x hx; simpa [addCells] using hx
  | cell a b iha ihb =>
    intro x hx
    unfold addCells
    split_ifs
    · exact hx
    · exact ihb _ x (iha _ x (List.mem_append_left _ hx))

/-- `addCells` keeps a list duplicate-free. -/
theorem nodup_addCells (n : Noun) (acc : List Noun) (h : acc.Nodup) : (addCells n acc).Nodup := by
  induction n generalizing acc with
  | atom a => simpa [addCells] using h
  | cell a b iha ihb =>
    unfold addCells
    split_ifs with hm
    · exact h
    · exact ihb _ (iha _ (List.nodup_append.mpr ⟨h, List.nodup_singleton _, by
        intro x hx y hy hxy; simp at hy; subst hy; subst hxy; exact hm hx⟩))

/-- A cell list is child-closed outside a pending list. -/
def ClP (acc pd : List Noun) : Prop :=
  ∀ a b, Noun.cell a b ∈ acc → Noun.cell a b ∉ pd →
    (∀ x y, a = .cell x y → a ∈ acc) ∧ (∀ x y, b = .cell x y → b ∈ acc)

theorem addCells_clP (n : Noun) : ∀ (acc pd : List Noun), ClP acc pd →
    ClP (addCells n acc) pd ∧ (∀ x y, n = .cell x y → n ∈ addCells n acc) := by
  induction n with
  | atom v => intro acc pd h; exact ⟨by simpa [addCells] using h, by simp⟩
  | cell a b iha ihb =>
    intro acc pd h
    by_cases hm : Noun.cell a b ∈ acc
    · simp only [addCells, if_pos hm]; exact ⟨h, fun _ _ _ => hm⟩
    · simp only [addCells, if_neg hm]
      set acc1 := acc ++ [Noun.cell a b]
      have h1 : ClP acc1 (Noun.cell a b :: pd) := by
        intro x y hx hp
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨h1, h2⟩ := h x y hx (fun h' => hp (List.mem_cons_of_mem _ h'))
          exact ⟨fun u v e => List.mem_append_left _ (h1 u v e),
            fun u v e => List.mem_append_left _ (h2 u v e)⟩
        · simp at hx; exact absurd (by rw [hx.1, hx.2]; exact List.mem_cons_self) hp
      obtain ⟨h2, ha⟩ := iha acc1 _ h1
      obtain ⟨h3, hb⟩ := ihb _ _ h2
      have hsa : ∀ z ∈ addCells a acc1, z ∈ addCells b (addCells a acc1) := subset_addCells b _
      refine ⟨?_, fun _ _ _ => hsa _ (subset_addCells a acc1 _ (List.mem_append_right _ (by simp)))⟩
      intro x y hx hp
      by_cases he : Noun.cell x y = Noun.cell a b
      · simp only [Noun.cell.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨fun u v e => hsa _ (ha u v e), fun u v e => hb u v e⟩
      · exact h3 x y hx (by simp [he, hp])

/-- The fold of `cellsOfRoots` stays child-closed and contains every cell root. -/
theorem foldCells_clP (roots : List Noun) : ∀ acc : List Noun, ClP acc [] →
    ClP (roots.foldl (fun acc n => addCells n acc) acc) [] ∧
    ∀ n ∈ roots, ∀ x y, n = .cell x y → n ∈ roots.foldl (fun acc n => addCells n acc) acc := by
  induction roots with
  | nil => intro acc h; exact ⟨h, by simp⟩
  | cons n ns ih =>
    intro acc h
    obtain ⟨h1, hn⟩ := addCells_clP n acc [] h
    obtain ⟨h2, hns⟩ := ih _ h1
    refine ⟨h2, ?_⟩
    intro m hm x y e
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [List.foldl_cons]
      have key : ∀ (l : List Noun) (acc' : List Noun), m ∈ acc' →
          m ∈ l.foldl (fun acc n => addCells n acc) acc' := by
        intro l; induction l with
        | nil => intro acc' h; exact h
        | cons k ks ihk => intro acc' h; exact ihk _ (subset_addCells k acc' m h)
      exact key ns _ (hn x y e)
    · exact hns m hm x y e

/-- **The cell list is child-closed.** -/
theorem cells_closed (roots : List Noun) : ClP (cellsOfRoots roots) [] :=
  (foldCells_clP roots [] (by intro a b h; simp at h)).1

/-- Every cell sub-noun of a cell in a child-closed list is in it. -/
theorem subs_mem_of_closed {L : List Noun} (hL : ClP L []) :
    ∀ n : Noun, (∀ x y, n = .cell x y → n ∈ L) → ∀ z ∈ Nock.Jet.ChipJ8.subs n, z ∈ L := by
  intro n
  induction n with
  | atom v => intro _ z hz; simp [Nock.Jet.ChipJ8.subs] at hz
  | cell a b iha ihb =>
    intro hn z hz
    have hab := hn a b rfl
    obtain ⟨ha, hb⟩ := hL a b hab (by simp)
    simp only [Nock.Jet.ChipJ8.subs, List.mem_cons, List.mem_append] at hz
    rcases hz with rfl | hz | hz
    · exact hab
    · exact iha (fun x y e => ha x y e) z hz
    · exact ihb (fun x y e => hb x y e) z hz

/-- **Every cell sub-noun of a demand root is a cell of the table.** -/
theorem mem_cells_of_subs {roots : List Noun} {n : Noun} (hn : n ∈ roots) :
    ∀ z ∈ Nock.Jet.ChipJ8.subs n, z ∈ cellsOfRoots roots :=
  subs_mem_of_closed (cells_closed roots) n
    (fun x y e => (foldCells_clP roots [] (by intro a b h; simp at h)).2 n hn x y e)

/-- **The cell list is duplicate-free.** -/
theorem cells_nodup (roots : List Noun) : (cellsOfRoots roots).Nodup := by
  unfold cellsOfRoots
  have key : ∀ (l acc : List Noun), acc.Nodup → (l.foldl (fun acc n => addCells n acc) acc).Nodup := by
    intro l; induction l with
    | nil => intro acc h; exact h
    | cons k ks ih => intro acc h; exact ih _ (nodup_addCells k acc h)
  exact key roots [] List.nodup_nil

end Sanity

/-! ## 4. The handle map is honest -/

/-- **`H` is an honest handle map at `p`.** -/
theorem hdlOK_hdlP (p : ℕ) (cs acs : List Noun) : HonestCompX.HdlOK p (hdlP p cs acs) where
  small v hv := by simp [hdlP, hv]
  big v hv := by simp [hdlP, Nat.not_lt.mpr hv]
  cell a b := rfl

theorem hdlOK (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    HonestCompX.HdlOK (ringChar (ZMod p)) (j8DataOf p Rg Rt hgen).H := by
  rw [ZMod.ringChar_zmod_n]; exact hdlOK_hdlP p _ _

/-- At Goldilocks, `H` agrees with the no-big-atom generator's `hdl` off the big atoms. -/
theorem hdlP_eq_hdl (cs acs : List Noun) (n : Noun) (hn : ∀ v, n = .atom v → v < Nock.Field.p) :
    hdlP Nock.Field.p cs acs n = Nock.V1J8.Gen.hdl cs n := by
  cases n with
  | atom v => have := hn v rfl; simp [hdlP, Nock.V1J8.Gen.hdl, this]
  | cell a b => rfl

/-- **Every handle noun of a row is a cell of the table, or a small atom, or a big atom.** -/
theorem handle_noun_cases (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) {row : RowNX}
    (hrow : row ∈ (j8DataOf p Rg Rt hgen).rows.toList) {n : Noun} (hn : n ∈ handleNounsX row) :
    ((∃ a b, n = .cell a b) ∧ n ∈ (j8DataOf p Rg Rt hgen).cells) ∨ (∃ v, n = .atom v ∧ v < p) ∨
      (∃ v, n = .atom v ∧ p ≤ v) := by
  cases n with
  | atom v =>
    right
    by_cases hv : v < p
    · exact Or.inl ⟨v, rfl, hv⟩
    · exact Or.inr ⟨v, rfl, Nat.not_lt.mp hv⟩
  | cell a b =>
    left
    refine ⟨⟨a, b, rfl⟩, ?_⟩
    have hroot : Noun.cell a b ∈ (j8DataOf p Rg Rt hgen).roots := by
      simp only [j8DataOf, rootsOf]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, hrow, hn⟩))
    exact mem_cells_of_subs hroot _ (by simp [Nock.Jet.ChipJ8.subs])

/-- The claim's cells are cells of the table. -/
theorem claim_mem_cells (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) {n : Noun}
    (hn : n ∈ [s, f, r]) : ∀ z ∈ Nock.Jet.ChipJ8.subs n, z ∈ (j8DataOf p Rg Rt hgen).cells := by
  apply mem_cells_of_subs
  simp only [rootsOf]
  exact List.mem_append_left _ (List.mem_append_left _ hn)

/-- **The cells are distinct.** -/
theorem j8_cells_nodup (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    (j8DataOf p Rg Rt hgen).cells.Nodup := cells_nodup _

/-! ## 5. The toy run `*[[0 0] [0 1]]` -/

theorem gen0E : genX Nock.Jet.VerifiedRegistry.empty.R 1 InhabJ8Base.s0 InhabJ8Base.f0 = some (InhabJ8Base.t0, InhabJ8Base.s0) := InhabJ8Base.gen0

theorem rows0 : rowsOfT InhabJ8Base.t0 = #[InhabJ8Comp.r0] := by
  simp only [rowsOfT, InhabJ8Comp.bfs0]; rfl

/-- **The toy run: the cell list is `[InhabJ8Base.s0, InhabJ8Base.f0]` and `H` is the generator's `hdl` (= the inhabitant's `H0`).** -/
theorem toy_cells_H (Rt : ℕ → Tpl) :
    (j8DataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty Rt gen0E).cells = [InhabJ8Base.s0, InhabJ8Base.f0] ∧
    ∀ n : Noun, (∀ v, n = .atom v → v < Nock.Field.p) →
      (j8DataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty Rt gen0E).H n =
        Nock.V1J8.Gen.hdl [InhabJ8Base.s0, InhabJ8Base.f0] n := by
  have hc : (j8DataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty Rt gen0E).cells = [InhabJ8Base.s0, InhabJ8Base.f0] := by
    have hcalls : callsOf #[InhabJ8Comp.r0] = [] := by decide
    have hc0 : cellsOfRoots (rootsOf InhabJ8Base.c0 #[InhabJ8Comp.r0]) = [InhabJ8Base.s0, InhabJ8Base.f0] := by
      decide
    simp only [j8DataOf, rows0, hcalls, jNounsP, List.map_nil, List.dedup_nil, List.zipIdx_nil,
      List.flatMap_nil, List.append_nil]
    exact hc0
  refine ⟨hc, fun n hn => ?_⟩
  rw [← hc]
  exact hdlP_eq_hdl _ _ n hn

/-! ## 6. Record lists: named, open, and the multiplicities as their counts

Every multiplicity of `J8Data` is the COUNT of a list of NAMED consumer record lists (`(serial, multiplicity)`
pairs, by consumer).  A new consumer (J-9 B claim big-atom records, a J-9 A limb-provider chip) appends one named
list; `cnt_append` splits the count.  The balance lemmas (L5) take these lists as parameters. -/

/-- **A named record list**: one consumer's (or provider's) `(serial, multiplicity)` records. -/
structure NamedRecs where
  name : String
  recs : List (ℕ × ℕ)

/-- The total multiplicity of serial `j` over a list of named record lists. -/
def cnt (L : List NamedRecs) (j : ℕ) : ℕ :=
  (((L.flatMap NamedRecs.recs).filter fun q => q.1 = j).map Prod.snd).sum

theorem cnt_append (L L' : List NamedRecs) (j : ℕ) : cnt (L ++ L') j = cnt L j + cnt L' j := by
  simp [cnt, List.flatMap_append, List.filter_append, List.map_append, List.sum_append]

theorem cnt_cons (r : NamedRecs) (L : List NamedRecs) (j : ℕ) :
    cnt (r :: L) j = ((r.recs.filter fun q => q.1 = j).map Prod.snd).sum + cnt L j := by
  simp [cnt, List.flatMap_cons, List.filter_append, List.map_append, List.sum_append]

theorem cnt_nil (j : ℕ) : cnt [] j = 0 := rfl

/-- The generators' `bump`, one entry. -/
theorem bump_getD (a : Array ℕ) (i m j : ℕ) :
    (bump a i m).getD j 0 = a.getD j 0 + (if j = i ∧ i < a.size then m else 0) := by
  unfold bump
  by_cases h1 : i < a.size
  · rw [if_pos h1]
    by_cases hj : j = i
    · subst hj; simp [Array.getD, Array.getElem_modify, h1]
    · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
      simp [hj, Ne.symm hj]
  · rw [if_neg h1]; simp [h1]

theorem bump_size (a : Array ℕ) (i m : ℕ) : (bump a i m).size = a.size := by
  unfold bump; split_ifs <;> simp

/-- Bump a list of `(serial, multiplicity)` pairs. -/
def bumpAll (a : Array ℕ) (l : List (ℕ × ℕ)) : Array ℕ := l.foldl (fun a q => bump a q.1 q.2) a

theorem bumpAll_append (a : Array ℕ) (l l' : List (ℕ × ℕ)) :
    bumpAll a (l ++ l') = bumpAll (bumpAll a l) l' := by simp [bumpAll, List.foldl_append]

theorem bumpAll_size (a : Array ℕ) (l : List (ℕ × ℕ)) : (bumpAll a l).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons q l ih => simp only [bumpAll, List.foldl_cons] at ih ⊢; rw [ih, bump_size]

/-- **`bumpAll` counts**: below the array size, entry `j` gains the multiplicities of the pairs at `j`. -/
theorem bumpAll_getD (a : Array ℕ) (l : List (ℕ × ℕ)) (j : ℕ) (hj : j < a.size) :
    (bumpAll a l).getD j 0 = a.getD j 0 + ((l.filter fun q => q.1 = j).map Prod.snd).sum := by
  induction l generalizing a with
  | nil => simp [bumpAll]
  | cons q l ih =>
    simp only [bumpAll, List.foldl_cons] at ih ⊢
    rw [ih _ (by rw [bump_size]; exact hj), bump_getD]
    by_cases hq : q.1 = j
    · have : j = q.1 ∧ q.1 < a.size := ⟨hq.symm, hq ▸ hj⟩
      rw [if_pos this, List.filter_cons_of_pos (by simpa using hq), List.map_cons, List.sum_cons]
      omega
    · have : ¬ (j = q.1 ∧ q.1 < a.size) := fun h => hq h.1.symm
      rw [if_neg this, List.filter_cons_of_neg (by simpa using hq)]
      omega

theorem replicate_getD (n j : ℕ) : (Array.replicate n 0).getD j 0 = 0 := by
  unfold Array.getD; split <;> simp

/-- The cell references of a noun list, `(serial, 1)` per cell. -/
def cellPairs (cs : List Noun) (l : List Noun) : List (ℕ × ℕ) :=
  l.filterMap fun n => match n with
    | .cell _ _ => some (idxOf cs n, 1)
    | .atom _ => none

theorem foldl_cellBump (cs : List Noun) (l : List Noun) (a : Array ℕ) :
    l.foldl (fun a n => match n with
      | .cell _ _ => bump a (idxOf cs n) 1
      | .atom _ => a) a = bumpAll a (cellPairs cs l) := by
  induction l generalizing a with
  | nil => rfl
  | cons n l ih =>
    cases n with
    | atom v => simp only [List.foldl_cons]; rw [ih]; rfl
    | cell x y => simp only [List.foldl_cons]; rw [ih]; rfl

theorem foldl_bumpPair (l : List (ℕ × ℕ)) (a : Array ℕ) :
    l.foldl (fun a q => bump a q.1 q.2) a = bumpAll a l := rfl

/-- The atom-walk row references (`wCounts`). -/
def wPairs (rI : Noun → ℕ) (cs : List Noun) (ws : List WRow) : List (ℕ × ℕ) :=
  ws.filterMap fun w => match w.node with
    | .cell _ _ => some (Nock.V1J8.Gen.wIdx rI cs w, 1)
    | .atom _ => none

theorem wCounts_eq (rI : Noun → ℕ) (cs : List Noun) (ws : List WRow) :
    wCounts rI cs ws = bumpAll (Array.replicate cs.length 0) (wPairs rI cs ws) := by
  unfold wCounts
  generalize Array.replicate cs.length 0 = a
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons]
    rcases hw : w.node with v | ⟨x, y⟩
    · simp only [wPairs, List.filterMap_cons, hw]; rw [ih]; rfl
    · simp only [wPairs, List.filterMap_cons, hw]; rw [ih]; rfl

section Recs
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **The validity consumers** (`mv`): every in-table child reference, the claim's cells, the registry pins. -/
def vRecs (D : J8Data p Rg fuel s f r) : List NamedRecs :=
  [⟨"cellChildren", cellPairs D.cells (D.cells.flatMap fun n => [hdN' n, tlN' n])⟩,
   ⟨"claim", cellPairs D.cells [s, f, r]⟩,
   ⟨"registryPins", D.regs.map fun id => (D.idx id, 1)⟩]

/-- **The walk-import consumers** (`mx`): one per J-8 walk row at a cell. -/
def wRecs (D : J8Data p Rg fuel s f r) : List NamedRecs :=
  [⟨"walk", cellPairs D.cells (D.ws.map WRow.node)⟩]

/-- **The export consumers** (`mh`): the compute's export consumes, the J-8 walk rows, the J export reads. -/
def xRecs (D : J8Data p Rg fuel s f r) : List NamedRecs :=
  [⟨"compute", D.bases.flatMap fun b => xConsumesP p (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))⟩,
   ⟨"walk", cellPairs D.cells (D.ws.map WRow.node)⟩,
   ⟨"J", D.jrows.flatMap fun row => (keysOf entsX row).map fun κ => ((κ.headD 0).val, 1)⟩]

/-- **The atom-root consumers** (`mb`): one per cell-table child that is a big atom. -/
def mbRecs (D : J8Data p Rg fuel s f r) : List NamedRecs :=
  [⟨"cellBigChildren", (D.cells.flatMap fun n => [hdN' n, tlN' n]).filterMap fun n =>
      (bigIdOfP p D.acs n).map fun i => (i, 1)⟩]

/-- **The atom table's walk consumers** (`mxA`, `mhA`): one per atom-walk row at a cell. -/
def awRecs (D : J8Data p Rg fuel s f r) : List NamedRecs :=
  [⟨"atomWalk", wPairs (rIAP p D.acs) D.acs D.vs⟩]

end Recs

/-- The `(serial, multiplicity)` sum at `j`. -/
def sumAt (l : List (ℕ × ℕ)) (j : ℕ) : ℕ := ((l.filter fun q => q.1 = j).map Prod.snd).sum

theorem sumAt_append (l l' : List (ℕ × ℕ)) (j : ℕ) : sumAt (l ++ l') j = sumAt l j + sumAt l' j := by
  simp [sumAt, List.filter_append, List.sum_append]

theorem cnt_eq_sumAt (L : List NamedRecs) (j : ℕ) : cnt L j = (L.map fun x => sumAt x.recs j).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => rw [cnt_cons, ih, List.map_cons, List.sum_cons]; rfl

theorem foldl_idBump (g : ℕ → ℕ) (l : List ℕ) (a : Array ℕ) :
    l.foldl (fun a id => bump a (g id) 1) a = bumpAll a (l.map fun id => (g id, 1)) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons, List.map_cons]; rw [ih]; rfl

/-- `bumpAll` from zero, at an in-range serial. -/
theorem bumpAll0_getD (n : ℕ) (l : List (ℕ × ℕ)) (j : ℕ) (hj : j < n) :
    (bumpAll (Array.replicate n 0) l).getD j 0 = sumAt l j := by
  rw [bumpAll_getD _ _ _ (by simpa using hj), replicate_getD, zero_add]; rfl

theorem bumpAll2_getD (n : ℕ) (l l' : List (ℕ × ℕ)) (j : ℕ) (hj : j < n) :
    (bumpAll (bumpAll (Array.replicate n 0) l) l').getD j 0 = sumAt l j + sumAt l' j := by
  rw [bumpAll_getD _ _ _ (by rw [bumpAll_size]; simpa using hj), bumpAll0_getD _ _ _ hj]; rfl

section Counts
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`mv` is the count of the validity consumers.** -/
theorem mv_eq_cnt (j : ℕ) (hj : j < (j8DataOf p Rg Rt hgen).cells.length) :
    (j8DataOf p Rg Rt hgen).mv.getD j 0 = cnt (vRecs (j8DataOf p Rg Rt hgen)) j := by
  have e : ∀ (cs : List Noun) (c : P8PublicClaim), mvCounts cs c = bumpAll (Array.replicate cs.length 0)
      (cellPairs cs ((cs.flatMap fun n => [hdN' n, tlN' n]) ++ [c.subject, c.formula, c.result])) := by
    intro cs c
    unfold mvCounts
    simp only
    generalize Array.replicate cs.length 0 = a
    generalize (cs.flatMap fun n => [hdN' n, tlN' n]) ++ [c.subject, c.formula, c.result] = l
    induction l generalizing a with
    | nil => rfl
    | cons n l ih =>
      simp only [List.foldl_cons]
      rcases n with v | ⟨x, y⟩
      · rw [ih]; simp [cellPairs]
      · rw [ih]; simp only [cellPairs, List.filterMap_cons]; rfl
  show (mvPins (mvCounts _ _) _ _).getD j 0 = _
  simp only [mvPins, foldl_idBump]
  rw [e, cnt_eq_sumAt]
  refine (bumpAll2_getD _ _ _ _ hj).trans ?_
  simp only [vRecs, cellPairs, List.filterMap_append, sumAt_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, add_assoc]
  rfl

/-- **`mx` is the count of the walk-import consumers.** -/
theorem mx_eq_cnt (j : ℕ) (hj : j < (j8DataOf p Rg Rt hgen).cells.length) :
    (j8DataOf p Rg Rt hgen).mx.getD j 0 = cnt (wRecs (j8DataOf p Rg Rt hgen)) j := by
  show (mxCounts _ _).getD j 0 = _
  have e : ∀ (cs : List Noun) (ws : List WRow), mxCounts cs ws =
      bumpAll (Array.replicate cs.length 0) (cellPairs cs (ws.map WRow.node)) := by
    intro cs ws
    unfold mxCounts
    generalize Array.replicate cs.length 0 = a
    induction ws generalizing a with
    | nil => rfl
    | cons w ws ih =>
      simp only [List.foldl_cons, List.map_cons]
      rcases hw : w.node with v | ⟨x, y⟩
      · rw [ih]; simp [cellPairs]
      · rw [ih]; simp only [cellPairs, List.filterMap_cons]; rfl
  rw [e, cnt_eq_sumAt]
  refine (bumpAll0_getD _ _ _ hj).trans ?_
  simp only [wRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rfl

/-- **`mxA` / `mhA` are the count of the atom-walk consumers.** -/
theorem mxA_eq_cnt (j : ℕ) (hj : j < (j8DataOf p Rg Rt hgen).acs.length) :
    (j8DataOf p Rg Rt hgen).mxA.getD j 0 = cnt (awRecs (j8DataOf p Rg Rt hgen)) j := by
  show (wCounts _ _ _).getD j 0 = _
  rw [wCounts_eq, cnt_eq_sumAt]
  refine (bumpAll0_getD _ _ _ hj).trans ?_
  simp only [awRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rfl

theorem mhA_eq_mxA : (j8DataOf p Rg Rt hgen).mhA = (j8DataOf p Rg Rt hgen).mxA := rfl

/-- **`mb` is the count of the atom-root consumers.** -/
theorem mb_eq_cnt (j : ℕ) (hj : j < (j8DataOf p Rg Rt hgen).acs.length) :
    (j8DataOf p Rg Rt hgen).mb.getD j 0 = cnt (mbRecs (j8DataOf p Rg Rt hgen)) j := by
  have e : ∀ (acs cs : List Noun), mbCountsP p acs cs = bumpAll (Array.replicate acs.length 0)
      ((cs.flatMap fun n => [hdN' n, tlN' n]).filterMap fun n => (bigIdOfP p acs n).map fun i => (i, 1)) := by
    intro acs cs
    unfold mbCountsP
    generalize Array.replicate acs.length 0 = a
    generalize (cs.flatMap fun n => [hdN' n, tlN' n]) = l
    induction l generalizing a with
    | nil => rfl
    | cons n l ih =>
      simp only [List.foldl_cons, List.filterMap_cons]
      rcases hb : bigIdOfP p acs n with _ | i
      · rw [ih]; rfl
      · rw [ih]; rfl
  show (mbCountsP p _ _).getD j 0 = _
  rw [e, cnt_eq_sumAt]
  refine (bumpAll0_getD _ _ _ hj).trans ?_
  simp only [mbRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rfl

/-- **`mh` is the count of the export consumers.** -/
theorem mh_eq_cnt (j : ℕ) (hj : j < (j8DataOf p Rg Rt hgen).cells.length) :
    (j8DataOf p Rg Rt hgen).mh.getD j 0 = cnt (xRecs (j8DataOf p Rg Rt hgen)) j := by
  have e1 : ∀ (cs : List Noun) (bs : List (ℕ → ZMod p)) (ws : List WRow), mhCountsP p cs bs ws =
      bumpAll (bumpAll (Array.replicate cs.length 0)
        (bs.flatMap fun b => xConsumesP p (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))))
        (cellPairs cs (ws.map WRow.node)) := by
    intro cs bs ws
    unfold mhCountsP
    simp only
    have hb : ∀ (a : Array ℕ) (bs : List (ℕ → ZMod p)),
        bs.foldl (fun a b => (xConsumesP p (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))).foldl
          (fun a q => bump a q.1 q.2) a) a =
        bumpAll a (bs.flatMap fun b => xConsumesP p (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))) := by
      intro a bs
      induction bs generalizing a with
      | nil => rfl
      | cons b bs ih => simp only [List.foldl_cons, List.flatMap_cons, bumpAll_append]; rw [ih]; rfl
    rw [hb]
    generalize bumpAll (Array.replicate cs.length 0) _ = a
    induction ws generalizing a with
    | nil => rfl
    | cons w ws ih =>
      simp only [List.foldl_cons, List.map_cons]
      rcases hw : w.node with v | ⟨x, y⟩
      · rw [ih]; simp [cellPairs]
      · rw [ih]; simp only [cellPairs, List.filterMap_cons]; rfl
  have e2 : ∀ (mh : Array ℕ) (rows : List (CRow (ZMod p))), mhJP p mh rows =
      bumpAll mh (rows.flatMap fun row => (keysOf entsX row).map fun κ => ((κ.headD 0).val, 1)) := by
    intro mh rows
    unfold mhJP
    induction rows generalizing mh with
    | nil => rfl
    | cons row rows ih =>
      simp only [List.foldl_cons, List.flatMap_cons, bumpAll_append]
      rw [ih]
      congr 1
      generalize keysOf entsX row = ks
      induction ks generalizing mh with
      | nil => rfl
      | cons κ ks ihk => simp only [List.foldl_cons, List.map_cons]; rw [ihk]; rfl
  show (mhJP p (mhCountsP p _ _ _) _).getD j 0 = _
  rw [e2, e1, cnt_eq_sumAt]
  rw [bumpAll_getD _ _ _ (by rw [bumpAll_size, bumpAll_size, Array.size_replicate]; exact hj)]
  refine (congrArg (· + _) (bumpAll2_getD _ _ _ _ hj)).trans ?_
  simp only [xRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
  rfl

end Counts


/-! ## 7. Totals over named record lists: equal counts give equal totals (the balance core) -/

section Totals
variable {M : Type} [AddCommMonoid M]

/-- **The total of a list of named record lists** at a per-serial weight `w` (e.g. a LogUp term
`(compress χ key_j)⁻¹`): `Σ multiplicity • w serial`. -/
def totalW (w : ℕ → M) (L : List NamedRecs) : M := ((L.flatMap NamedRecs.recs).map fun q => q.2 • w q.1).sum

theorem totalW_append (w : ℕ → M) (L L' : List NamedRecs) : totalW w (L ++ L') = totalW w L + totalW w L' := by
  simp [totalW, List.flatMap_append, List.sum_append]

theorem sum_pairs_eq (w : ℕ → M) (l : List (ℕ × ℕ)) (S : Finset ℕ) (hS : ∀ q ∈ l, q.1 ∈ S) :
    (l.map fun q => q.2 • w q.1).sum = ∑ j ∈ S, sumAt l j • w j := by
  induction l with
  | nil => simp [sumAt]
  | cons q l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun q' h => hS q' (List.mem_cons_of_mem _ h))]
    have hq : ∀ j, sumAt (q :: l) j = (if q.1 = j then q.2 else 0) + sumAt l j := by
      intro j; by_cases h : q.1 = j <;> simp [sumAt, h]
    simp only [hq, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq S q.1, if_pos (hS q List.mem_cons_self)]

/-- `totalW` as a sum of counts over any serial set containing every record. -/
theorem totalW_eq_sum_cnt (w : ℕ → M) (L : List NamedRecs) (S : Finset ℕ)
    (hS : ∀ q ∈ L.flatMap NamedRecs.recs, q.1 ∈ S) : totalW w L = ∑ j ∈ S, cnt L j • w j :=
  sum_pairs_eq w _ S hS

/-- **Equal counts, equal totals**: the multiset core of every balance (consumers vs providers). -/
theorem totalW_eq_of_cnt (w : ℕ → M) (L L' : List NamedRecs) (h : ∀ j, cnt L j = cnt L' j) :
    totalW w L = totalW w L' := by
  classical
  let S : Finset ℕ := ((L.flatMap NamedRecs.recs).map Prod.fst).toFinset ∪
    ((L'.flatMap NamedRecs.recs).map Prod.fst).toFinset
  rw [totalW_eq_sum_cnt w L S (fun q hq => Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hq))),
    totalW_eq_sum_cnt w L' S (fun q hq => Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem hq)))]
  simp only [h]

/-- A provider list: serial `j` with multiplicity `m j`, for `j < n`. -/
def provRecs (name : String) (n : ℕ) (m : ℕ → ℕ) : NamedRecs := ⟨name, (List.range n).map fun j => (j, m j)⟩

theorem sumAt_range (n : ℕ) (m : ℕ → ℕ) (j : ℕ) :
    sumAt ((List.range n).map fun j => (j, m j)) j = if j < n then m j else 0 := by
  induction n with
  | zero => simp [sumAt]
  | succ n ih =>
    rw [List.range_succ, List.map_append, sumAt_append, ih]
    by_cases h1 : j < n
    · have : n ≠ j := by omega
      simp [sumAt, h1, this, show j < n + 1 by omega]
    · by_cases h2 : j = n
      · subst h2; simp [sumAt]
      · have : n ≠ j := fun e => h2 e.symm
        simp [sumAt, h1, this, show ¬ j < n + 1 by omega]

theorem cnt_provRecs (name : String) (n : ℕ) (m : ℕ → ℕ) (j : ℕ) :
    cnt [provRecs name n m] j = if j < n then m j else 0 := by
  rw [cnt_eq_sumAt]; simp [provRecs, sumAt_range]

end Totals

/-! ## 8. The data-level balance facts, in the shape of L5's `BalancedN`

L5 (`ComplJ8Bal.BalancedN Cs Ps`: `hnd`, `hcov`, `hcnt`) takes consumer lists `Cs : List (List α)` (one entry per
consumed record) and provider lists `Ps : List (List (ℕ × α))` (`(multiplicity, key)`).  Here `α = ℕ` (the serial;
L5's weight maps a serial to its key's LogUp term): `Cs = L.map (expand ·.recs)`, `Ps = [provN m n]`.  `hcnt` is
exactly the `_eq_cnt` lemmas; `hcov` (every consumed serial is a row of the table) is the hypothesis `hrange`. -/

/-- One consumed record per unit of multiplicity. -/
def expand (l : List (ℕ × ℕ)) : List ℕ := l.flatMap fun q => List.replicate q.2 q.1

theorem count_expand (l : List (ℕ × ℕ)) (j : ℕ) : (expand l).count j = sumAt l j := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [expand, List.flatMap_cons, List.count_append, ← expand, ih, List.count_replicate]
    by_cases h : q.1 = j
    · subst h; simp [sumAt]
    · have h' : ¬ (q.1 == j) = true := by simpa using h
      simp [sumAt, h]

theorem count_flatten_expand (L : List NamedRecs) (j : ℕ) :
    (L.map fun r => expand r.recs).flatten.count j = cnt L j := by
  induction L with
  | nil => rfl
  | cons r L ih => rw [List.map_cons, List.flatten_cons, List.count_append, ih, count_expand, cnt_cons]; rfl

/-- A table's provider list `(multiplicity, serial)`, serials `0 .. n − 1`. -/
def provN (m : Array ℕ) (n : ℕ) : List (ℕ × ℕ) := (List.range n).map fun j => (m.getD j 0, j)

/-- The three `BalancedN` fields at `Cs = L.map (expand ·.recs)`, `Ps = [provN m n]`. -/
def BalFacts (L : List NamedRecs) (m : Array ℕ) (n : ℕ) : Prop :=
    ([provN m n].flatten.map Prod.snd).Nodup ∧
    (∀ x ∈ (L.map fun r => expand r.recs).flatten, x ∈ [provN m n].flatten.map Prod.snd) ∧
    (∀ q ∈ [provN m n].flatten, q.1 = (L.map fun r => expand r.recs).flatten.count q.2)

/-- **The three `BalancedN` facts** for one table: providers `provN m n`, consumers the named lists `L`. -/
theorem balancedN_facts (L : List NamedRecs) (m : Array ℕ) (n : ℕ) (hm : ∀ j < n, m.getD j 0 = cnt L j)
    (hrange : ∀ q ∈ L.flatMap NamedRecs.recs, 0 < q.2 → q.1 < n) :
    ([provN m n].flatten.map Prod.snd).Nodup ∧
    (∀ x ∈ (L.map fun r => expand r.recs).flatten, x ∈ [provN m n].flatten.map Prod.snd) ∧
    (∀ q ∈ [provN m n].flatten, q.1 = (L.map fun r => expand r.recs).flatten.count q.2) := by
  have hs : [provN m n].flatten.map Prod.snd = List.range n := by
    simp [provN, List.map_map, Function.comp_def]
  refine ⟨by rw [hs]; exact List.nodup_range, ?_, ?_⟩
  · intro x hx
    rw [hs, List.mem_range]
    obtain ⟨e, he, hxe⟩ := List.mem_flatten.mp hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hxe
    obtain ⟨hpos, rfl⟩ := List.mem_replicate.mp hxq
    exact hrange q (List.mem_flatMap.mpr ⟨r, hr, hq⟩) (Nat.pos_of_ne_zero hpos)
  · intro q hq
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, provN, List.mem_map, List.mem_range] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    rw [count_flatten_expand, hm j hj]

section BalJ8
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **Cell validity** (`mv`), the `BalancedN` facts. -/
theorem balV_facts (hrange : ∀ q ∈ (vRecs (j8DataOf p Rg Rt hgen)).flatMap NamedRecs.recs, 0 < q.2 →
      q.1 < (j8DataOf p Rg Rt hgen).cells.length) :
    BalFacts (vRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mv (j8DataOf p Rg Rt hgen).cells.length :=
  balancedN_facts _ _ _ (mv_eq_cnt p Rg Rt hgen) hrange

/-- **Walk import** (`mx`), the `BalancedN` facts. -/
theorem balW_facts (hrange : ∀ q ∈ (wRecs (j8DataOf p Rg Rt hgen)).flatMap NamedRecs.recs, 0 < q.2 →
      q.1 < (j8DataOf p Rg Rt hgen).cells.length) :
    BalFacts (wRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mx (j8DataOf p Rg Rt hgen).cells.length :=
  balancedN_facts _ _ _ (mx_eq_cnt p Rg Rt hgen) hrange

/-- **Cell export** (`mh`), the `BalancedN` facts. -/
theorem balX_facts (hrange : ∀ q ∈ (xRecs (j8DataOf p Rg Rt hgen)).flatMap NamedRecs.recs, 0 < q.2 →
      q.1 < (j8DataOf p Rg Rt hgen).cells.length) :
    BalFacts (xRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mh (j8DataOf p Rg Rt hgen).cells.length :=
  balancedN_facts _ _ _ (mh_eq_cnt p Rg Rt hgen) hrange

/-- **Atom roots** (`mb`), the `BalancedN` facts. -/
theorem balMB_facts (hrange : ∀ q ∈ (mbRecs (j8DataOf p Rg Rt hgen)).flatMap NamedRecs.recs, 0 < q.2 →
      q.1 < (j8DataOf p Rg Rt hgen).acs.length) :
    BalFacts (mbRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mb (j8DataOf p Rg Rt hgen).acs.length :=
  balancedN_facts _ _ _ (mb_eq_cnt p Rg Rt hgen) hrange

/-- **Atom-walk imports** (`mxA`, `= mhA`), the `BalancedN` facts. -/
theorem balAW_facts (hrange : ∀ q ∈ (awRecs (j8DataOf p Rg Rt hgen)).flatMap NamedRecs.recs, 0 < q.2 →
      q.1 < (j8DataOf p Rg Rt hgen).acs.length) :
    BalFacts (awRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mxA (j8DataOf p Rg Rt hgen).acs.length :=
  balancedN_facts _ _ _ (mxA_eq_cnt p Rg Rt hgen) hrange

end BalJ8

/-! ## 9. The range facts (`hrange`): every consumed serial is a table row -/

theorem idxD_lt (cs : List Noun) (n : Noun) (h : n ∈ cs) : idxD cs n < cs.length := by
  induction cs with
  | nil => simp at h
  | cons c cs ih =>
    unfold idxD
    split_ifs with hc
    · simp
    · have : n ∈ cs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hc
        · exact h
      simpa using ih this

theorem idxOf_lt (cs : List Noun) (n : Noun) (h : n ∈ cs) : idxOf cs n < cs.length := by
  unfold idxOf; rw [if_pos h]; exact idxD_lt cs n h

/-- `cellPairs` emits only cells of `cs` at multiplicity `1`; a cell of `cs` has an in-range serial. -/
theorem cellPairs_range (cs l : List Noun) (hl : ∀ a b, Noun.cell a b ∈ l → Noun.cell a b ∈ cs) :
    ∀ q ∈ cellPairs cs l, q.1 < cs.length := by
  intro q hq
  obtain ⟨n, hn, hq⟩ := List.mem_filterMap.mp hq
  cases n with
  | atom v => simp at hq
  | cell a b =>
    simp only [Option.some.injEq] at hq
    subst hq
    exact idxOf_lt cs _ (hl a b hn)

theorem compile_isCell (p : ℕ) (T : Tpl) : ∃ a b, compile p T = .cell a b := ⟨_, _, rfl⟩

section Range
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- A demand root that is a cell is a cell of the table. -/
theorem root_mem_cells {a b : Noun} (h : Noun.cell a b ∈ (j8DataOf p Rg Rt hgen).roots) :
    Noun.cell a b ∈ (j8DataOf p Rg Rt hgen).cells :=
  mem_cells_of_subs h _ (by simp [Nock.Jet.ChipJ8.subs])

/-- **`hrange` for the validity consumers.** -/
theorem vRecs_range : ∀ q ∈ (vRecs (j8DataOf p Rg Rt hgen)).flatMap NamedRecs.recs, 0 < q.2 →
    q.1 < (j8DataOf p Rg Rt hgen).cells.length := by
  intro q hq _
  simp only [vRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hq
  rcases hq with hq | hq | hq
  · refine cellPairs_range _ _ ?_ q hq
    intro a b hab
    obtain ⟨c, hc, hab⟩ := List.mem_flatMap.mp hab
    cases c with
    | atom v => simp [hdN', tlN'] at hab
    | cell x y =>
      obtain ⟨h1, h2⟩ := cells_closed _ x y hc (by simp)
      simp only [hdN', tlN', List.mem_cons, List.not_mem_nil, or_false] at hab
      rcases hab with e | e
      · exact e ▸ h1 a b e.symm
      · exact e ▸ h2 a b e.symm
  · refine cellPairs_range _ _ ?_ q hq
    intro a b hab
    exact claim_mem_cells p Rg Rt hgen hab _ (by simp [Nock.Jet.ChipJ8.subs])
  · obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hq
    obtain ⟨a, b, hab⟩ := compile_isCell p (Rt id)
    have hm : compile p (Rt id) ∈ (j8DataOf p Rg Rt hgen).roots :=
      List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
    show idxOf (j8DataOf p Rg Rt hgen).cells (compile p (Rt id)) < _
    apply idxOf_lt
    rw [hab] at hm ⊢
    exact root_mem_cells p Rg Rt hgen hm

/-- **Cell validity balance facts, unconditional.** -/
theorem balV_facts' :
    BalFacts (vRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mv (j8DataOf p Rg Rt hgen).cells.length :=
  balV_facts p Rg Rt hgen (vRecs_range p Rg Rt hgen)

end Range

/-! ### The walk rows' nodes -/

theorem subs_trans {x y R : Noun} (hy : y ∈ Nock.Jet.ChipJ8.subs x) (hx : x ∈ Nock.Jet.ChipJ8.subs R) :
    y ∈ Nock.Jet.ChipJ8.subs R := by
  induction R with
  | atom v => simp [Nock.Jet.ChipJ8.subs] at hx
  | cell a b iha ihb =>
    simp only [Nock.Jet.ChipJ8.subs, List.mem_cons, List.mem_append] at hx ⊢
    rcases hx with rfl | hx | hx
    · simpa [Nock.Jet.ChipJ8.subs] using hy
    · exact Or.inr (Or.inl (iha hx))
    · exact Or.inr (Or.inr (ihb hx))

/-- A node of a trie is a sub-noun of the trie's root. -/
def SubOf (R n : Noun) : Prop := ∀ a b, n = .cell a b → Noun.cell a b ∈ Nock.Jet.ChipJ8.subs R

theorem SubOf.left {R l r : Noun} (h : SubOf R (.cell l r)) : SubOf R l := by
  intro a b e; subst e
  exact subs_trans (by simp [Nock.Jet.ChipJ8.subs]) (h _ _ rfl)

theorem SubOf.right {R l r : Noun} (h : SubOf R (.cell l r)) : SubOf R r := by
  intro a b e; subst e
  exact subs_trans (by simp [Nock.Jet.ChipJ8.subs]) (h _ _ rfl)

/-- The trie invariant over a list of trie nodes. -/
def TrieInv (Rs : List Noun) (l : List Nock.V1J8.Gen.TN) : Prop :=
  ∀ u ∈ l, ∃ R ∈ Rs, ∃ n pre len T, u = Nock.V1J8.Gen.trie R n pre len T ∧ SubOf R n

theorem trieInv_kids (Rs : List Noun) (l : List Nock.V1J8.Gen.TN) (h : TrieInv Rs l) :
    TrieInv Rs (l.flatMap Nock.V1J8.Gen.TN.kids) := by
  intro u hu
  obtain ⟨v, hv, hu⟩ := List.mem_flatMap.mp hu
  obtain ⟨R, hR, n, pre, len, T, rfl, hn⟩ := h v hv
  cases n with
  | atom a => simp [Nock.V1J8.Gen.trie, Nock.V1J8.Gen.TN.kids] at hu
  | cell x y =>
    simp only [Nock.V1J8.Gen.trie, Nock.V1J8.Gen.TN.kids, List.mem_append] at hu
    rcases hu with hu | hu
    · split_ifs at hu
      · simp only [List.mem_singleton] at hu
        exact ⟨R, hR, _, _, _, _, hu, hn.left⟩
      · simp at hu
    · split_ifs at hu
      · simp only [List.mem_singleton] at hu
        exact ⟨R, hR, _, _, _, _, hu, hn.right⟩
      · simp at hu

theorem bfsTN_node (Rs : List Noun) : ∀ (k : ℕ) (l : List Nock.V1J8.Gen.TN), TrieInv Rs l →
    ∀ w ∈ Nock.V1J8.Gen.bfsTN k l, ∃ R ∈ Rs, SubOf R w.node := by
  intro k
  induction k with
  | zero => intro l _ w hw; simp [Nock.V1J8.Gen.bfsTN] at hw
  | succ k ih =>
    intro l hl w hw
    cases l with
    | nil => simp [Nock.V1J8.Gen.bfsTN] at hw
    | cons u us =>
      simp only [Nock.V1J8.Gen.bfsTN, List.mem_append] at hw
      rcases hw with hw | hw
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        obtain ⟨R, hR, n, pre, len, T, rfl, hn⟩ := hl v hv
        refine ⟨R, hR, ?_⟩
        cases n <;> exact hn
      · exact ih _ (trieInv_kids Rs _ hl) w hw

/-- **The walk rows' nodes are sub-nouns of the read roots or of the dummy root.** -/
theorem walkGen_node (dummy : Noun) (rs : List (Noun × ℕ)) :
    ∀ w ∈ (walkGen dummy rs).1, ∃ R ∈ dummy :: rs.map Prod.fst, SubOf R w.node := by
  intro w hw
  unfold walkGen at hw
  simp only at hw
  apply bfsTN_node _ _ _ _ w hw
  intro u hu
  split_ifs at hu
  · simp only [List.mem_singleton] at hu
    exact ⟨dummy, List.mem_cons_self, dummy, 1, 0, [], hu, fun a b e => by subst e; simp [Nock.Jet.ChipJ8.subs]⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hu
    refine ⟨g.1, ?_, g.1, 1, 0, g.2, rfl, fun a b e => by rw [e]; simp [Nock.Jet.ChipJ8.subs]⟩
    unfold Nock.V1J8.Gen.groupReads at hg
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hg
    refine List.mem_cons_of_mem _ ?_
    have key : ∀ (l : List (Noun × ℕ)) (acc : List Noun), (∀ x ∈ acc, x ∈ rs.map Prod.fst) →
        (∀ q ∈ l, q.1 ∈ rs.map Prod.fst) →
        ∀ x ∈ l.foldl (fun acc q => if q.1 ∈ acc then acc else acc ++ [q.1]) acc, x ∈ rs.map Prod.fst := by
      intro l
      induction l with
      | nil => intro acc h _; exact h
      | cons q l ih =>
        intro acc h hl
        simp only [List.foldl_cons]
        apply ih
        · split_ifs
          · exact h
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact h x hx
            · simp at hx; subst hx; exact hl q List.mem_cons_self
        · exact fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')
    exact key rs [] (by simp) (fun q hq => List.mem_map.mpr ⟨q, hq, rfl⟩) R hR

/-- The path reads' roots are handle nouns of the rows. -/
theorem pathReads_root (rows : Array RowNX) :
    ∀ q ∈ Nock.V1J8.Gen.pathReads rows, ∃ row ∈ rows.toList, q.1 ∈ handleNounsX row := by
  intro q hq
  unfold Nock.V1J8.Gen.pathReads at hq
  obtain ⟨hq, -⟩ := List.mem_filter.mp hq
  obtain ⟨row, hrow, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
  refine ⟨row, hrow, ?_⟩
  unfold consEntriesX at hx
  simp only [List.mem_append] at hx
  rcases hx with ((((hx | hx) | hx) | hx) | hx) <;> split_ifs at hx <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl <;> simp [handleNounsX]

section RangeW
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **Every J-8 walk row at a cell is at a cell of the table.** -/
theorem ws_node_mem (w : WRow) (hw : w ∈ (j8DataOf p Rg Rt hgen).ws) (a b : Noun) (e : w.node = .cell a b) :
    Noun.cell a b ∈ (j8DataOf p Rg Rt hgen).cells := by
  obtain ⟨R, hR, hsub⟩ := walkGen_node _ _ w hw
  have hRc : ∀ x y, R = .cell x y → R ∈ (j8DataOf p Rg Rt hgen).cells := by
    intro x y eR
    rcases List.mem_cons.mp hR with hR | hR
    · -- the dummy root is the head of the cell list
      have hd : ∀ cs : List Noun, cs.headD (.atom 0) = .cell x y → cs.headD (.atom 0) ∈ cs := by
        intro cs e; cases cs with
        | nil => simp at e
        | cons c cs => simp
      rw [hR] at eR ⊢
      exact hd (j8DataOf p Rg Rt hgen).cells eR
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hR
      obtain ⟨row, hrow, hroot⟩ := pathReads_root _ q hq
      rcases handle_noun_cases p Rg Rt hgen hrow hroot with ⟨_, hm⟩ | ⟨v, ev, _⟩ | ⟨v, ev, _⟩
      · exact hm
      · rw [eR] at ev; cases ev
      · rw [eR] at ev; cases ev
  exact subs_mem_of_closed (cells_closed _) R hRc _ (hsub a b e)

/-- **`hrange` for the walk-import consumers.** -/
theorem wRecs_range : ∀ q ∈ (wRecs (j8DataOf p Rg Rt hgen)).flatMap NamedRecs.recs, 0 < q.2 →
    q.1 < (j8DataOf p Rg Rt hgen).cells.length := by
  intro q hq _
  simp only [wRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hq
  refine cellPairs_range _ _ ?_ q hq
  intro a b hab
  obtain ⟨w, hw, e⟩ := List.mem_map.mp hab
  exact ws_node_mem p Rg Rt hgen w hw a b e

theorem balW_facts' :
    BalFacts (wRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mx (j8DataOf p Rg Rt hgen).cells.length :=
  balW_facts p Rg Rt hgen (wRecs_range p Rg Rt hgen)

end RangeW

/-! ### The atom table's consumers (serials into `acs`, which is non-empty: the pad row) -/

theorem idxOf_lt_of_ne (cs : List Noun) (n : Noun) (h : cs ≠ []) : idxOf cs n < cs.length := by
  by_cases hm : n ∈ cs
  · exact idxOf_lt cs n hm
  · unfold idxOf; rw [if_neg hm]; exact List.length_pos_of_ne_nil h

theorem lastIdxOf_lt (l : List Noun) (n : Noun) (h : l ≠ []) : lastIdxOf l n < l.length := by
  unfold lastIdxOf
  cases hf : ((l.zipIdx 0).reverse.find? fun x => x.1 == n) with
  | none => exact List.length_pos_of_ne_nil h
  | some x =>
    have hx := List.mem_reverse.mp (List.mem_of_find?_eq_some hf)
    simpa using List.snd_lt_add_of_mem_zipIdx hx

theorem acsP_ne (p : ℕ) (bigs : List ℕ) (d : Bool) : acsP p bigs d ≠ [] := by
  simp [acsP]

section RangeA
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

theorem rootIdxP_lt (acs : List Noun) (h : acs ≠ []) (a : ℕ) : rootIdxP p acs a < acs.length := by
  unfold rootIdxP; split_ifs
  · exact lastIdxOf_lt _ _ h
  · exact idxOf_lt_of_ne _ _ h

/-- **`hrange` for the atom-root consumers.** -/
theorem mbRecs_range : ∀ q ∈ (mbRecs (j8DataOf p Rg Rt hgen)).flatMap NamedRecs.recs, 0 < q.2 →
    q.1 < (j8DataOf p Rg Rt hgen).acs.length := by
  intro q hq _
  simp only [mbRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hq
  obtain ⟨n, -, hq⟩ := List.mem_filterMap.mp hq
  have hne : (j8DataOf p Rg Rt hgen).acs ≠ [] := acsP_ne _ _ _
  cases n with
  | cell a b => simp [bigIdOfP] at hq
  | atom v =>
    simp only [bigIdOfP] at hq
    split_ifs at hq
    · simp at hq
    · simp only [Option.map_some, Option.some.injEq] at hq
      subst hq
      exact rootIdxP_lt p _ hne v

/-- **`hrange` for the atom-walk consumers.** -/
theorem awRecs_range : ∀ q ∈ (awRecs (j8DataOf p Rg Rt hgen)).flatMap NamedRecs.recs, 0 < q.2 →
    q.1 < (j8DataOf p Rg Rt hgen).acs.length := by
  intro q hq _
  simp only [awRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hq
  have hne : (j8DataOf p Rg Rt hgen).acs ≠ [] := acsP_ne _ _ _
  obtain ⟨w, -, hq⟩ := List.mem_filterMap.mp hq
  rcases hw : w.node with v | ⟨a, b⟩
  · simp [hw] at hq
  · simp only [hw, Option.some.injEq] at hq
    subst hq
    show Nock.V1J8.Gen.wIdx _ _ w < _
    unfold Nock.V1J8.Gen.wIdx rIAP
    split_ifs
    · exact lastIdxOf_lt _ _ hne
    · rw [hw]; exact idxOf_lt_of_ne _ _ hne
    · rw [hw]; exact idxOf_lt_of_ne _ _ hne

theorem balMB_facts' :
    BalFacts (mbRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mb (j8DataOf p Rg Rt hgen).acs.length :=
  balMB_facts p Rg Rt hgen (mbRecs_range p Rg Rt hgen)

theorem balAW_facts' :
    BalFacts (awRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mxA (j8DataOf p Rg Rt hgen).acs.length :=
  balAW_facts p Rg Rt hgen (awRecs_range p Rg Rt hgen)

end RangeA

/-! ### The compute's export consumes (the honest row semantics `RowOKX`, from the binders `hax` / `hop5`) -/

open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX in
theorem selS_eval {p : ℕ} [Fact p.Prime] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (r : RowNX)
    (fst lst : ZMod p) (l : List ℕ) (hl : ∀ i ∈ l, i < 17) (hnd : l.Nodup) :
    (ChipH.selS l : CoeffExpr (ZMod p)).eval
      (⟨Nock.V1J8.FillX.colXE H pd r fst lst, Nock.V1J8.FillX.colXE H pd r fst lst, fun _ => 0, fun _ => 0⟩ :
        Nock.Reified.Env (ZMod p)) = if stIdx r.st ∈ l then 1 else 0 := by
  unfold ChipH.selS
  rw [CoeffExpr.eval_sumList]
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi := hl i List.mem_cons_self
    have hnd' := List.nodup_cons.mp hnd
    rw [List.map_cons, List.sum_cons, ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) hnd'.2]
    simp only [ChipH.cc, CoeffExpr.eval, Nock.V1J8.FillX.colXE, if_pos hi, List.mem_cons]
    by_cases h1 : stIdx r.st = i
    · subst h1; simp [hnd'.1]
    · simp [h1]

theorem mem_subs_self (n : Noun) (h : n.isCell = true) : n ∈ Nock.Jet.ChipJ8.subs n := by
  cases n with
  | atom v => simp [Noun.isCell] at h
  | cell a b => simp [Nock.Jet.ChipJ8.subs]

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
  Nock.NockVMROM.Thm54.CoordinateCompiler in
theorem xEnt_cell {p : ℕ} [Fact p.Prime] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (r : RowNX)
    (fst lst : ZMod p) (hok : HonestCompX.RowOKX p r) (hH : HonestCompX.HdlOK p H)
    (S : SlotX (ZMod p)) (hS : S ∈ (ChipHX.slotsX : List (SlotX (ZMod p)))) (x : EntX (ZMod p)) (hx : x ∈ S.ents)
    (hb : x.bal = .x)
    (hact : x.act.eval (⟨Nock.V1J8.FillX.colXE H pd r fst lst, Nock.V1J8.FillX.colXE H pd r fst lst,
      fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p)) ≠ 0) :
    ∃ k tail, x.rcd = .col (hdX k).v :: tail ∧ (HonestCompX.hN r k).isCell = true ∧ k < 12 ∧
      ∃ n ∈ handleNounsX r, HonestCompX.hN r k ∈ Nock.Jet.ChipJ8.subs n := by
  simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  all_goals simp only [slot0X, slot1X, slot2X, slot3X, List.mem_cons, List.not_mem_nil, or_false] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (simp at hb; done) | skip
  all_goals simp only [EntX.act, CoeffExpr.eval] at hact
  all_goals rw [selS_eval H pd r fst lst _ (by decide) (by decide)] at hact
  case inr.inr.inl.inr.inr.inr.inr.inl =>
    refine ⟨3, _, rfl, ?_⟩
    suffices hc : r.sf1.isCell = true from
      ⟨hc, by decide, r.sf1, by simp [handleNounsX], mem_subs_self _ hc⟩
    have he : (kcE xSf1 : CoeffExpr (ZMod p)).eval (⟨Nock.V1J8.FillX.colXE H pd r fst lst,
        Nock.V1J8.FillX.colXE H pd r fst lst, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p)) =
        HonestCompX.hk H r.sf1 - 2 * HonestCompX.hb H r.sf1 := by
      simp [kcE, kbE, kbX, ChipH.cc, CoeffExpr.eval, xSf1, hdX, Nock.V1J8.FillX.colXE, HonestCompX.hN]
    rw [he] at hact
    show r.sf1.isCell = true
    rcases hsf : r.sf1 with v | ⟨a, b⟩
    · exfalso
      rw [hsf] at hact
      by_cases hv : v < p
      · have := hH.small v hv
        simp [HonestCompX.hk, HonestCompX.hb, this] at hact
      · have := hH.big v (Nat.not_lt.mp hv)
        simp [HonestCompX.hk, HonestCompX.hb, this] at hact
    · rfl
  all_goals
    split_ifs at hact with hm
    swap; · simp at hact
    refine ⟨_, _, rfl, ?_⟩
    unfold HonestCompX.RowOKX at hok
    cases hst : r.st <;> rw [hst] at hok <;>
      simp [hst, stIdx, opStatesX, l2X, l3X, ChipH.consCol] at hm <;>
      simp_all [HonestCompX.hN, Noun.isCell, handleNounsX, Nock.Jet.ChipJ8.subs]

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX in
theorem xConsumesP_mem {p : ℕ} [Fact p.Prime] {e : Nock.Reified.Env (ZMod p)} {q : ℕ × ℕ}
    (hq : q ∈ xConsumesP p e) : ∃ S ∈ (ChipHX.slotsX : List (SlotX (ZMod p))), ∃ x ∈ S.ents, x.bal = .x ∧
      x.act.eval e ≠ 0 ∧ ∃ i tail, x.rcd = .col i :: tail ∧ q.1 = (e.trace i).val := by
  unfold xConsumesP at hq
  obtain ⟨S, hS, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨x, hx, hq⟩ := List.mem_filterMap.mp hq
  obtain ⟨hx, hb⟩ := List.mem_filter.mp hx
  refine ⟨S, hS, x, hx, by simpa using hb, ?_⟩
  simp only at hq
  split_ifs at hq with h0
  refine ⟨fun h => h0 (by rw [h]; exact ZMod.val_zero), ?_⟩
  split at hq
  · rename_i i tail hr
    simp only [Option.some.injEq] at hq
    exact ⟨i, tail, hr, by rw [← hq]⟩
  · simp at hq

/-- **The compute export consumes of an honest row are cells of the table** (in range). -/
theorem xcons_row_range {p : ℕ} [Fact p.Prime] (cs acs : List Noun) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (r : RowNX) (fst lst : ZMod p) (hok : HonestCompX.RowOKX p r)
    (hcs : ∀ n ∈ handleNounsX r, ∀ z ∈ Nock.Jet.ChipJ8.subs n, z ∈ cs) (hlen : cs.length < p) :
    ∀ q ∈ xConsumesP p (⟨Nock.V1J8.FillX.colXE (hdlP p cs acs) pd r fst lst,
      Nock.V1J8.FillX.colXE (hdlP p cs acs) pd r fst lst, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p)),
      q.1 < cs.length := by
  intro q hq
  obtain ⟨S, hS, x, hx, hb, hact, i, tail, hr, hq1⟩ := xConsumesP_mem hq
  obtain ⟨k, tail', hr', hcell, hk, n, hn, hsub⟩ :=
    xEnt_cell (hdlP p cs acs) pd r fst lst hok (hdlOK_hdlP p cs acs) S hS x hx hb hact
  rw [hr'] at hr
  simp only [List.cons.injEq, ChipHX.RE.col.injEq] at hr
  rw [hq1, ← hr.1]
  have hmem := hcs n hn _ hsub
  have hcol : Nock.V1J8.FillX.colXE (F := ZMod p) (hdlP p cs acs) pd r fst lst (ChipHX.hdX k).v =
      HonestCompX.hv (hdlP p cs acs) (HonestCompX.hN r k) := by
    have h1 : ¬ (ChipHX.hdX k).v < 17 := by simp only [ChipHX.hdX]; omega
    have h2 : (ChipHX.hdX k).v < 49 := by simp only [ChipHX.hdX]; omega
    simp only [Nock.V1J8.FillX.colXE, ChipHX.hdX] at h1 h2 ⊢
    erw [if_neg h1, if_neg (show ¬ (26 + 2 * k = 17) by omega), if_neg (show ¬ (26 + 2 * k = 18) by omega), if_neg (show ¬ (26 + 2 * k = 19) by omega), if_neg (show ¬ (26 + 2 * k = 20) by omega), if_neg (show ¬ (26 + 2 * k = 21) by omega), if_neg (show ¬ (26 + 2 * k = 22) by omega), if_neg (show ¬ (26 + 2 * k = 23) by omega), if_neg (show ¬ (26 + 2 * k = 24) by omega), if_pos h2,
      if_neg (show ¬ ((26 + 2 * k - 25) % 2 = 0) by omega)]
    congr 2; omega
  show ((Nock.V1J8.FillX.colXE (F := ZMod p) (hdlP p cs acs) pd r fst lst (ChipHX.hdX k).v)).val < _
  rw [hcol]
  rcases hN : HonestCompX.hN r k with v | ⟨a, b⟩
  · rw [hN] at hcell; simp [Noun.isCell] at hcell
  · rw [hN] at hmem
    have hlt := idxOf_lt cs _ hmem
    simp only [HonestCompX.hv, hdlP]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    exact hlt

section RangeX
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`hrange` for the compute's export consumes**, under the run binders' `SmallX` (`smallX_of_binders`) and the
cell-count bound `|cells| < p` (the budget `hlenC`). -/
theorem xRecs_compute_range (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataOf p Rg Rt hgen).cells.length < p) :
    ∀ q ∈ (j8DataOf p Rg Rt hgen).bases.flatMap (fun b => xConsumesP p
      (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))),
      q.1 < (j8DataOf p Rg Rt hgen).cells.length := by
  intro q hq
  obtain ⟨b, hb, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨⟨row, j⟩, hrj, rfl⟩ := List.mem_map.mp hb
  have hrow : row ∈ (j8DataOf p Rg Rt hgen).rows.toList := List.fst_mem_of_mem_zipIdx hrj
  have hrow' := hrow
  simp only [j8DataOf, rowsOfT, List.toList_toArray, List.mem_map] at hrow'
  obtain ⟨u, hu, rfl⟩ := hrow'
  have hin : InTree t u := by
    obtain ⟨c, hc, h⟩ := (mem_bfsForest [t] u).mp hu
    simp only [List.mem_singleton] at hc; subst hc; exact h
  have hok := HonestRowX.rowOKX_of_genX hgen hin (hsm u hin)
  exact xcons_row_range (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs _ _ _ _ hok
    (fun n hn => mem_cells_of_subs (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hrow, hn⟩)))) hlen q hq

/-- **`hrange` for the export consumers**: compute (above) and walk (`ws_node_mem`) discharged; the J export
reads `hJ` are the J chip's. -/
theorem xRecs_range (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataOf p Rg Rt hgen).cells.length < p)
    (hJ : ∀ q ∈ (j8DataOf p Rg Rt hgen).jrows.flatMap (fun row => (keysOf entsX row).map fun κ =>
      ((κ.headD 0).val, 1)), q.1 < (j8DataOf p Rg Rt hgen).cells.length) :
    ∀ q ∈ (xRecs (j8DataOf p Rg Rt hgen)).flatMap NamedRecs.recs, 0 < q.2 →
      q.1 < (j8DataOf p Rg Rt hgen).cells.length := by
  intro q hq _
  simp only [xRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hq
  rcases hq with hq | hq | hq
  · exact xRecs_compute_range p Rg Rt hgen hsm hlen q hq
  · refine cellPairs_range _ _ ?_ q hq
    intro a b hab
    obtain ⟨w, hw, e⟩ := List.mem_map.mp hab
    exact ws_node_mem p Rg Rt hgen w hw a b e
  · exact hJ q hq

theorem balX_facts' (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataOf p Rg Rt hgen).cells.length < p)
    (hJ : ∀ q ∈ (j8DataOf p Rg Rt hgen).jrows.flatMap (fun row => (keysOf entsX row).map fun κ =>
      ((κ.headD 0).val, 1)), q.1 < (j8DataOf p Rg Rt hgen).cells.length) :
    BalFacts (xRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mh (j8DataOf p Rg Rt hgen).cells.length :=
  balX_facts p Rg Rt hgen (xRecs_range p Rg Rt hgen hsm hlen hJ)

end RangeX

/-! ### The J export reads (`hJ`): every `rp / sl / sr` row reads a noun under a J root -/

section RangeJ
open Nock.Jet.ChipJ8 (chainWG nodeWG nodesWG blockWG honestJ8G hOf mkW callPre regPre)
open Nock.Jet.Interp (JNode JOp honestRows z0)

/-- A noun that is, if a cell, a cell of `cs`. -/
def GoodN (cs : List Noun) (y : Noun) : Prop := ∀ a b, y = .cell a b → y ∈ cs

/-- The export-read shape of a J row: its node handle is `hd y` for a good `y`. -/
def ReadOK (p : ℕ) [Fact p.Prime] (cs : List Noun) (hd : Noun → ZMod p × ZMod p) (r : CRow (ZMod p)) : Prop :=
  (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
    ∃ y, GoodN cs y ∧ r.w.kN = (hd y).1 ∧ r.w.vN = (hd y).2

variable {p : ℕ} [Fact p.Prime] {cs : List Noun} {hd : Noun → ZMod p × ZMod p}

theorem goodN_nhd (hcl : ClP cs []) {x : Noun} (hx : GoodN cs x) : GoodN cs (Nock.Jet.Autogen.nhd x) := by
  intro a b e
  cases x with
  | atom v => simp [Nock.Jet.Autogen.nhd] at e
  | cell l r =>
    simp only [Nock.Jet.Autogen.nhd] at e ⊢
    exact (hcl l r (hx l r rfl) (by simp)).1 a b e

theorem goodN_ntl (hcl : ClP cs []) {x : Noun} (hx : GoodN cs x) : GoodN cs (Nock.Jet.Autogen.ntl x) := by
  intro a b e
  cases x with
  | atom v => simp [Nock.Jet.Autogen.ntl] at e
  | cell l r =>
    simp only [Nock.Jet.Autogen.ntl] at e ⊢
    exact (hcl l r (hx l r rfl) (by simp)).2 a b e

theorem chainW_read (hcl : ClP cs []) (c dst : ℕ) : ∀ (bs : List Bool) (src ctr : ℕ) (x : Noun), GoodN cs x →
    ∀ r ∈ chainWG (p := p) hd c dst src ctr bs x, ReadOK p cs hd r
  | [], src, ctr, x, _, r, hr => by
    simp only [chainWG, List.mem_singleton] at hr
    subst hr
    intro h; simp at h
  | b :: bs, src, ctr, x, hx, r, hr => by
    simp only [chainWG, List.mem_cons] at hr
    rcases hr with rfl | hr
    · intro _; exact ⟨x, hx, rfl, rfl⟩
    · exact chainW_read hcl c dst bs ctr (ctr + 1) _
        (by cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact goodN_ntl hcl hx | exact goodN_nhd hcl hx) r hr

theorem nodeW_read (hcl : ClP cs []) (c S ctr : ℕ) (lk : ℕ → Noun) (s : Noun) (nd : JNode)
    (hs : GoodN cs s) (hlk : ∀ n, GoodN cs (lk n)) : ∀ r ∈ nodeWG (p := p) hd c S ctr lk s nd, ReadOK p cs hd r := by
  intro r hr
  unfold nodeWG at hr
  cases hop : nd.op with
  | var i ax => rw [hop] at hr; exact chainW_read hcl _ _ _ _ _ _ hs r hr
  | nth j => rw [hop] at hr; exact chainW_read hcl _ _ _ _ _ _ (hlk _) r hr
  | tlN n => rw [hop] at hr; exact chainW_read hcl _ _ _ _ _ _ (hlk _) r hr
  | pair =>
    rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr
    intro _; exact ⟨_, hlk nd.id, rfl, rfl⟩
  | const k => rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr; intro h; simp at h
  | add => rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr; intro h; simp at h
  | mul => rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr; intro h; simp at h
  | isF => rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr; intro h; simp at h
  | isNil => rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr; intro h; simp at h

theorem nodesW_read (hcl : ClP cs []) (c S : ℕ) (lk : ℕ → Noun) (s : Noun) (hs : GoodN cs s)
    (hlk : ∀ n, GoodN cs (lk n)) : ∀ (nds : List JNode) (ctr : ℕ), ∀ r ∈ nodesWG (p := p) hd c S lk s ctr nds,
      ReadOK p cs hd r
  | [], _, r, hr => by simp [nodesWG] at hr
  | nd :: nds, ctr, r, hr => by
    simp only [nodesWG, List.mem_append] at hr
    rcases hr with hr | hr
    · exact nodeW_read hcl c S ctr lk s nd hs hlk r hr
    · exact nodesW_read hcl c S lk s hs hlk nds _ r hr

theorem blockW_read (hcl : ClP cs []) (R : ℕ → Tpl) (c i : ℕ) (s : Noun) (hs : GoodN cs s)
    (hv : ∀ y ∈ (honestRows p (R i) s c).map Nock.Jet.Interp.JRow.val, GoodN cs y) :
    ∀ r ∈ blockWG (p := p) hd R c i s, ReadOK p cs hd r := by
  intro r hr
  simp only [blockWG, List.mem_cons] at hr
  rcases hr with rfl | hr
  · intro h; simp [callPre] at h
  · refine nodesW_read hcl c _ _ s hs ?_ _ _ r hr
    intro n
    unfold Nock.Jet.ChipJ8.honestLook
    cases hn : (honestRows p (R i) s c)[n]? with
    | none => intro a b e; simp [z0] at e
    | some row =>
      simp only [Option.map_some, Option.getD_some]
      exact hv _ (List.mem_map.mpr ⟨row, List.mem_of_getElem? hn, rfl⟩)

theorem honestJ8_read (hcl : ClP cs []) (R : ℕ → Tpl) (regs : List ℕ) (calls : List (ℕ × Noun))
    (hgood : ∀ cl ∈ calls.zipIdx, GoodN cs cl.1.2 ∧
      ∀ y ∈ (honestRows p (R cl.1.1) cl.1.2 cl.2).map Nock.Jet.Interp.JRow.val, GoodN cs y) :
    ∀ r ∈ honestJ8G (p := p) hd R regs calls, ReadOK p cs hd r := by
  intro r hr
  unfold honestJ8G at hr
  simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hr
  rcases hr with ⟨i, -, rfl⟩ | ⟨⟨⟨i, s⟩, c⟩, hmem, hr⟩
  · intro h; simp [regPre] at h
  · exact blockW_read hcl R c i s (hgood _ hmem).1 (hgood _ hmem).2 r hr

/-- The keys an export-read row puts in `entsX` have head `vN`. -/
theorem keysOf_entsX_head (r : CRow (ZMod p)) :
    ∀ κ ∈ keysOf entsX r, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) ∧ κ.headD 0 = r.w.vN := by
  intro κ hκ
  simp only [keysOf, entsX, List.mem_map, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hκ
  obtain ⟨e, ⟨he, hk⟩, rfl⟩ := hκ
  rcases he with rfl | rfl | rfl <;> simp at hk <;> rw [← hk] <;>
    simp [Nock.Jet.ChipJ8.keyX, Nock.Jet.ChipJ8.KE.ev, Nock.Jet.ChipJ8.colOf, Nock.Jet.ChipJ8.Col.vN]

/-- `mvFixP` changes only `mv`. -/
theorem mvFixP_mem (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) :
    ∀ x ∈ mvFixP p rows pins, ∃ r ∈ rows, x.pre = r.pre ∧ x.w.kN = r.w.kN ∧ x.w.vN = r.w.vN := by
  intro x hx
  unfold mvFixP at hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  refine ⟨r, hr, ?_⟩
  split <;> exact ⟨rfl, rfl, rfl⟩

section Data
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

theorem jn_good : ∀ y ∈ (j8DataOf p Rg Rt hgen).jn, GoodN (j8DataOf p Rg Rt hgen).cells y := by
  intro y hy a b e
  subst e
  exact root_mem_cells p Rg Rt hgen (List.mem_append_right _ hy)

/-- **`hJ`, the J export reads are in range**, from the base-gate fact `kN = 1` on `rp / sl / sr` rows and `|cells| < p`. -/
theorem jReads_range (hlen : (j8DataOf p Rg Rt hgen).cells.length < p)
    (hkN : ∀ x ∈ (j8DataOf p Rg Rt hgen).jrows,
      (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1) :
    ∀ q ∈ (j8DataOf p Rg Rt hgen).jrows.flatMap (fun row => (keysOf entsX row).map fun κ =>
      ((κ.headD 0).val, 1)), q.1 < (j8DataOf p Rg Rt hgen).cells.length := by
  intro q hq
  obtain ⟨x, hx, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hq
  obtain ⟨hkd, hhead⟩ := keysOf_entsX_head x κ hκ
  have hk1 := hkN x hx hkd
  obtain ⟨r0, hr0, hpre, hkN', hvN'⟩ := mvFixP_mem _ _ x hx
  have hjn := jn_good p Rg Rt hgen
  have hread := honestJ8_read (p := p) (hd := hJd p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs)
    (cells_closed _) Rt (j8DataOf p Rg Rt hgen).regs
    (j8DataOf p Rg Rt hgen).calls (by
      intro cl hcl
      refine ⟨hjn _ ?_, fun y hy => hjn _ ?_⟩
      · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨cl, hcl, List.mem_cons_self⟩)
      · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨cl, hcl, List.mem_cons_of_mem _ hy⟩))
    r0 hr0 (by rw [← hpre]; exact hkd)
  obtain ⟨y, hy, hk, hv⟩ := hread
  simp only [hhead, hvN', hv]
  cases y with
  | atom v =>
    rw [hkN', hk] at hk1
    exact absurd hk1 (hJd_atom_ne p _ _ v)
  | cell a b =>
    have hm := hy a b rfl
    have hlt : idxOf (j8DataOf p Rg Rt hgen).cells (Noun.cell a b) < (j8DataOf p Rg Rt hgen).cells.length :=
      idxOf_lt _ _ hm
    simp only [hJd, hdlP]
    rw [ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) hlt

theorem balX_facts'' (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataOf p Rg Rt hgen).cells.length < p)
    (hkN : ∀ x ∈ (j8DataOf p Rg Rt hgen).jrows,
      (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1) :
    BalFacts (xRecs (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).mh (j8DataOf p Rg Rt hgen).cells.length :=
  balX_facts' p Rg Rt hgen hsm hlen (jReads_range p Rg Rt hgen hlen hkN)

end Data

end RangeJ

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
