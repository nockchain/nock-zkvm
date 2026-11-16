/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/J8GenData.lean

 **J-8 completeness over any admissible `J8Data`: the generator with free list orders.**

 `j8DataGen p Rg Rt hgen O` is `ComplJ8Data.j8DataOf p Rg Rt hgen` with three list orders left to an `Ord8`:
 * the cell list `cells = O.ordC (cellsOfRoots roots)`;
 * the J-8 walk reads `reads = O.ordR H (pathReads rows)`;
 * the atom-walk reads `preads = O.ordR H (pairReadsP H pd rows)`.
 `Ord8` asks only that each order be a permutation of its input (`permC`, `permR`); the handle map, the walk
 rows, the multiplicities and the J rows are the generator's formulas over the reordered lists. The identity
 orders give `j8DataOf` back definitionally (`j8DataGen_ordId`).

 `J8DataOK D` (any `D : J8Data`) says `D` is such a generator output. The rest of this file re-states, over
 `j8DataGen … O`, the facts of `ComplJ8Data`, `ComplJ8Walk`, `ComplJ8CompRun`, `ComplJ8Jet`, `ComplJ8Atom`,
 `ComplJ8BigBound` and `ComplJ8AW` that the proof of `ComplJ8Closed.complJ8_closed` uses about `j8DataOf`
 (same names with the suffix `G`, proofs kept as close to the source proofs as the reordering allows).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8BigBound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.V1J8.Gen (cellsOfRoots addCells rootsOf idxOf idxD combOf spineOf padN linkOrder addNew lastIdxOf
  sxOf incChain AInfo atomV hdN' tlN' idxN pathReads walkGen mvCounts mxCounts mvPins wCounts bump callsOf
  WRow budget)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (CRow PRow layoutJ8 keysOf entsX)
open Nock.Jet.RapJetJ8 (consKT provKT tlF)

noncomputable section

/-! ## 1. The list orders and the generator -/

/-- **The free list orders of the generator**: a cell order and a read order (the read order may look at the
handle map, e.g. to sort reads by root serial); each is a permutation of its input. -/
structure Ord8 where
  ordC : List Noun → List Noun
  ordR : (Noun → ℕ × ℕ) → List (Noun × ℕ) → List (Noun × ℕ)
  permC : ∀ l, (ordC l).Perm l
  permR : ∀ H l, (ordR H l).Perm l

/-- The identity orders (the honest generator `j8DataOf`). -/
def ordId : Ord8 where
  ordC := fun l => l
  ordR := fun _ l => l
  permC := fun l => List.Perm.refl l
  permR := fun _ l => List.Perm.refl l

/-- **The generator with free list orders**: `j8DataOf` with `cells`, `reads` and `preads` reordered by `O`. -/
def j8DataGen (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) : J8Data p Rg fuel s f r :=
  let rows := rowsOfT t
  let c : P8PublicClaim := ⟨s, f, r⟩
  let calls := callsOf rows
  let ids := calls.map Prod.fst
  let regs := ids.dedup
  let jn := jNounsP p Rt regs calls
  let roots := rootsOf c rows ++ jn
  let cs := O.ordC (cellsOfRoots roots)
  let idx : ℕ → ℕ := fun id => idxOf cs (compile p (Rt id))
  let bigs := bigsP p roots rows
  let dupP := (incOpsP p rows).any fun x => x.1 + 1 = p
  let acs := acsP p bigs dupP
  let H := hdlP p cs acs
  let pd := HonestPairX.pdX (sxPP p acs rows)
  let reads := O.ordR H (Nock.V1J8.Gen.pathReads rows)
  let wg := walkGen (cs.headD (.atom 0)) reads
  let preads := O.ordR H (pairReadsP H pd rows)
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

/-- **The identity orders give the honest generator**, definitionally. -/
theorem j8DataGen_ordId (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    j8DataGen p Rg Rt hgen ordId = j8DataOf p Rg Rt hgen := rfl

/-- **An admissible J-8 datum**: the generator's output for some template table, run and list orders. Every
field of `D` other than the order of `cells`, `reads` and `preads` is the generator's formula. -/
structure J8DataOK {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
    (D : J8Data p Rg fuel s f r) where
  Rt : ℕ → Tpl
  t : NTree SkelX
  hgen : genX Rg.R fuel s f = some (t, r)
  O : Ord8
  eq : D = j8DataGen p Rg Rt hgen O

/-- **The honest generator is admissible** (identity orders). -/
def j8DataOf_ok (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    J8DataOK (j8DataOf p Rg Rt hgen) :=
  ⟨Rt, t, hgen, ordId, rfl⟩

/-- **Membership is order-free**: the reordered lists have the generator's members. -/
theorem mem_cells_iff (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) (x : Noun) :
    x ∈ (j8DataGen p Rg Rt hgen O).cells ↔ x ∈ cellsOfRoots (j8DataGen p Rg Rt hgen O).roots :=
  (O.permC _).mem_iff

theorem mem_reads_iff (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) (x : Noun × ℕ) :
    x ∈ (j8DataGen p Rg Rt hgen O).reads ↔ x ∈ Nock.V1J8.Gen.pathReads (j8DataGen p Rg Rt hgen O).rows :=
  (O.permR _ _).mem_iff

theorem mem_preads_iff (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) (x : Noun × ℕ) :
    x ∈ (j8DataGen p Rg Rt hgen O).preads ↔
      x ∈ pairReadsP (j8DataGen p Rg Rt hgen O).H (j8DataGen p Rg Rt hgen O).pd (j8DataGen p Rg Rt hgen O).rows :=
  (O.permR _ _).mem_iff

/-- Child-closure is order-free. -/
theorem clP_perm {L L' : List Noun} (h : L.Perm L') (hL : ClP L' []) : ClP L [] := by
  intro a b hab hn
  obtain ⟨h1, h2⟩ := hL a b (h.mem_iff.mp hab) hn
  exact ⟨fun x y e => h.mem_iff.mpr (h1 x y e), fun x y e => h.mem_iff.mpr (h2 x y e)⟩

section Cells
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)

/-- The reordered cell list is child-closed. -/
theorem cells_closedG : ClP (j8DataGen p Rg Rt hgen O).cells [] := clP_perm (O.permC _) (cells_closed _)

/-- The reordered cell list has no duplicates. -/
theorem cells_nodupG : (j8DataGen p Rg Rt hgen O).cells.Nodup := (O.permC _).nodup_iff.mpr (cells_nodup _)

/-- Every cell sub-noun of a demand root is a cell of the reordered table. -/
theorem mem_cells_of_subsG {n : Noun} (hn : n ∈ (j8DataGen p Rg Rt hgen O).roots) :
    ∀ z ∈ Nock.Jet.ChipJ8.subs n, z ∈ (j8DataGen p Rg Rt hgen O).cells := fun z hz =>
  (mem_cells_iff p Rg Rt hgen O z).mpr (mem_cells_of_subs hn z hz)

end Cells

/-! ### Twins of `ComplJ8Data` -/

section ComplJ8DataG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.V1J8.Gen (cellsOfRoots addCells rootsOf idxOf idxD combOf spineOf padN linkOrder addNew lastIdxOf
  sxOf incChain AInfo atomV hdN' tlN' idxN pathReads walkGen mvCounts mxCounts mvPins wCounts bump callsOf
  WRow budget)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (CRow PRow layoutJ8 keysOf entsX)
open Nock.Jet.RapJetJ8 (consKT provKT tlF)
noncomputable section
theorem hdlOKG (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) :
    HonestCompX.HdlOK (ringChar (ZMod p)) (j8DataGen p Rg Rt hgen O).H := by
  rw [ZMod.ringChar_zmod_n]; exact hdlOK_hdlP p _ _

/-- **Every handle noun of a row is a cell of the table, or a small atom, or a big atom.** -/
theorem handle_noun_casesG (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) {row : RowNX}
    (hrow : row ∈ (j8DataGen p Rg Rt hgen O).rows.toList) {n : Noun} (hn : n ∈ handleNounsX row) :
    ((∃ a b, n = .cell a b) ∧ n ∈ (j8DataGen p Rg Rt hgen O).cells) ∨ (∃ v, n = .atom v ∧ v < p) ∨
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
    have hroot : Noun.cell a b ∈ (j8DataGen p Rg Rt hgen O).roots := by
      simp only [j8DataGen, rootsOf]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, hrow, hn⟩))
    exact mem_cells_of_subsG p Rg Rt hgen O hroot _ (by simp [Nock.Jet.ChipJ8.subs])

/-- The claim's cells are cells of the table. -/
theorem claim_mem_cellsG (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ}
    {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) {n : Noun}
    (hn : n ∈ [s, f, r]) : ∀ z ∈ Nock.Jet.ChipJ8.subs n, z ∈ (j8DataGen p Rg Rt hgen O).cells := by
  apply mem_cells_of_subsG
  show n ∈ rootsOf _ _ ++ _
  simp only [rootsOf]
  exact List.mem_append_left _ (List.mem_append_left _ hn)

section Counts
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **`mv` is the count of the validity consumers.** -/
theorem mv_eq_cntG (j : ℕ) (hj : j < (j8DataGen p Rg Rt hgen O).cells.length) :
    (j8DataGen p Rg Rt hgen O).mv.getD j 0 = cnt (vRecs (j8DataGen p Rg Rt hgen O)) j := by
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
theorem mx_eq_cntG (j : ℕ) (hj : j < (j8DataGen p Rg Rt hgen O).cells.length) :
    (j8DataGen p Rg Rt hgen O).mx.getD j 0 = cnt (wRecs (j8DataGen p Rg Rt hgen O)) j := by
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
theorem mxA_eq_cntG (j : ℕ) (hj : j < (j8DataGen p Rg Rt hgen O).acs.length) :
    (j8DataGen p Rg Rt hgen O).mxA.getD j 0 = cnt (awRecs (j8DataGen p Rg Rt hgen O)) j := by
  show (wCounts _ _ _).getD j 0 = _
  rw [wCounts_eq, cnt_eq_sumAt]
  refine (bumpAll0_getD _ _ _ hj).trans ?_
  simp only [awRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rfl

/-- **`mb` is the count of the atom-root consumers.** -/
theorem mb_eq_cntG (j : ℕ) (hj : j < (j8DataGen p Rg Rt hgen O).acs.length) :
    (j8DataGen p Rg Rt hgen O).mb.getD j 0 = cnt (mbRecs (j8DataGen p Rg Rt hgen O)) j := by
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
theorem mh_eq_cntG (j : ℕ) (hj : j < (j8DataGen p Rg Rt hgen O).cells.length) :
    (j8DataGen p Rg Rt hgen O).mh.getD j 0 = cnt (xRecs (j8DataGen p Rg Rt hgen O)) j := by
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
section Range
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- A demand root that is a cell is a cell of the table. -/
theorem root_mem_cellsG {a b : Noun} (h : Noun.cell a b ∈ (j8DataGen p Rg Rt hgen O).roots) :
    Noun.cell a b ∈ (j8DataGen p Rg Rt hgen O).cells :=
  mem_cells_of_subsG p Rg Rt hgen O h _ (by simp [Nock.Jet.ChipJ8.subs])

/-- **`hrange` for the validity consumers.** -/
theorem vRecs_rangeG : ∀ q ∈ (vRecs (j8DataGen p Rg Rt hgen O)).flatMap NamedRecs.recs, 0 < q.2 →
    q.1 < (j8DataGen p Rg Rt hgen O).cells.length := by
  intro q hq _
  simp only [vRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hq
  rcases hq with hq | hq | hq
  · refine cellPairs_range _ _ ?_ q hq
    intro a b hab
    obtain ⟨c, hc, hab⟩ := List.mem_flatMap.mp hab
    cases c with
    | atom v => simp [hdN', tlN'] at hab
    | cell x y =>
      obtain ⟨h1, h2⟩ := cells_closedG p Rg Rt hgen O x y hc (by simp)
      simp only [hdN', tlN', List.mem_cons, List.not_mem_nil, or_false] at hab
      rcases hab with e | e
      · exact e ▸ h1 a b e.symm
      · exact e ▸ h2 a b e.symm
  · refine cellPairs_range _ _ ?_ q hq
    intro a b hab
    exact claim_mem_cellsG p Rg Rt hgen O hab _ (by simp [Nock.Jet.ChipJ8.subs])
  · obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hq
    obtain ⟨a, b, hab⟩ := compile_isCell p (Rt id)
    have hm : compile p (Rt id) ∈ (j8DataGen p Rg Rt hgen O).roots :=
      List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hid, rfl⟩))
    show idxOf (j8DataGen p Rg Rt hgen O).cells (compile p (Rt id)) < _
    apply idxOf_lt
    rw [hab] at hm ⊢
    exact root_mem_cellsG p Rg Rt hgen O hm

end Range
section RangeW
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **Every J-8 walk row at a cell is at a cell of the table.** -/
theorem ws_node_memG (w : WRow) (hw : w ∈ (j8DataGen p Rg Rt hgen O).ws) (a b : Noun) (e : w.node = .cell a b) :
    Noun.cell a b ∈ (j8DataGen p Rg Rt hgen O).cells := by
  obtain ⟨R, hR, hsub⟩ := walkGen_node _ _ w hw
  have hRc : ∀ x y, R = .cell x y → R ∈ (j8DataGen p Rg Rt hgen O).cells := by
    intro x y eR
    rcases List.mem_cons.mp hR with hR | hR
    · -- the dummy root is the head of the cell list
      have hd : ∀ cs : List Noun, cs.headD (.atom 0) = .cell x y → cs.headD (.atom 0) ∈ cs := by
        intro cs e; cases cs with
        | nil => simp at e
        | cons c cs => simp
      rw [hR] at eR ⊢
      exact hd (j8DataGen p Rg Rt hgen O).cells eR
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hR
      obtain ⟨row, hrow, hroot⟩ := pathReads_root _ q ((O.permR _ _).mem_iff.mp hq)
      rcases handle_noun_casesG p Rg Rt hgen O hrow hroot with ⟨_, hm⟩ | ⟨v, ev, _⟩ | ⟨v, ev, _⟩
      · exact hm
      · rw [eR] at ev; cases ev
      · rw [eR] at ev; cases ev
  exact subs_mem_of_closed (cells_closedG p Rg Rt hgen O) R hRc _ (hsub a b e)

end RangeW
section RangeA
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **`hrange` for the atom-root consumers.** -/
theorem mbRecs_rangeG : ∀ q ∈ (mbRecs (j8DataGen p Rg Rt hgen O)).flatMap NamedRecs.recs, 0 < q.2 →
    q.1 < (j8DataGen p Rg Rt hgen O).acs.length := by
  intro q hq _
  simp only [mbRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hq
  obtain ⟨n, -, hq⟩ := List.mem_filterMap.mp hq
  have hne : (j8DataGen p Rg Rt hgen O).acs ≠ [] := acsP_ne _ _ _
  cases n with
  | cell a b => simp [bigIdOfP] at hq
  | atom v =>
    simp only [bigIdOfP] at hq
    split_ifs at hq
    · simp at hq
    · simp only [Option.map_some, Option.some.injEq] at hq
      subst hq
      exact rootIdxP_lt p _ hne v

end RangeA
section RangeX
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **`hrange` for the compute's export consumes**, under the run binders' `SmallX` (`smallX_of_binders`) and the
cell-count bound `|cells| < p` (the budget `hlenC`). -/
theorem xRecs_compute_rangeG (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataGen p Rg Rt hgen O).cells.length < p) :
    ∀ q ∈ (j8DataGen p Rg Rt hgen O).bases.flatMap (fun b => xConsumesP p
      (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))),
      q.1 < (j8DataGen p Rg Rt hgen O).cells.length := by
  intro q hq
  obtain ⟨b, hb, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨⟨row, j⟩, hrj, rfl⟩ := List.mem_map.mp hb
  have hrow : row ∈ (j8DataGen p Rg Rt hgen O).rows.toList := List.fst_mem_of_mem_zipIdx hrj
  have hrow' := hrow
  simp only [j8DataGen, rowsOfT, List.toList_toArray, List.mem_map] at hrow'
  obtain ⟨u, hu, rfl⟩ := hrow'
  have hin : InTree t u := by
    obtain ⟨c, hc, h⟩ := (mem_bfsForest [t] u).mp hu
    simp only [List.mem_singleton] at hc; subst hc; exact h
  have hok := HonestRowX.rowOKX_of_genX hgen hin (hsm u hin)
  exact xcons_row_range (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).acs _ _ _ _ hok
    (fun n hn => mem_cells_of_subsG p Rg Rt hgen O (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hrow, hn⟩)))) hlen q hq

/-- **`hrange` for the export consumers**: compute (above) and walk (`ws_node_memG`) discharged; the J export
reads `hJ` are the J chip's (every J handle noun read by an `rp / sl / sr` row is a cell of the table). -/
theorem xRecs_rangeG (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataGen p Rg Rt hgen O).cells.length < p)
    (hJ : ∀ q ∈ (j8DataGen p Rg Rt hgen O).jrows.flatMap (fun row => (keysOf entsX row).map fun κ =>
      ((κ.headD 0).val, 1)), q.1 < (j8DataGen p Rg Rt hgen O).cells.length) :
    ∀ q ∈ (xRecs (j8DataGen p Rg Rt hgen O)).flatMap NamedRecs.recs, 0 < q.2 →
      q.1 < (j8DataGen p Rg Rt hgen O).cells.length := by
  intro q hq _
  simp only [xRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hq
  rcases hq with hq | hq | hq
  · exact xRecs_compute_rangeG p Rg Rt hgen O hsm hlen q hq
  · refine cellPairs_range _ _ ?_ q hq
    intro a b hab
    obtain ⟨w, hw, e⟩ := List.mem_map.mp hab
    exact ws_node_memG p Rg Rt hgen O w hw a b e
  · exact hJ q hq

end RangeX
section RangeJ
open Nock.Jet.ChipJ8 (chainWG nodeWG nodesWG blockWG honestJ8G hOf mkW callPre regPre)
open Nock.Jet.Interp (JNode JOp honestRows z0)
variable {p : ℕ} [Fact p.Prime] {cs : List Noun} {hd : Noun → ZMod p × ZMod p}
section Data
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
theorem jn_goodG : ∀ y ∈ (j8DataGen p Rg Rt hgen O).jn, GoodN (j8DataGen p Rg Rt hgen O).cells y := by
  intro y hy a b e
  subst e
  exact root_mem_cellsG p Rg Rt hgen O (List.mem_append_right _ hy)

/-- **`hJ`, the J export reads are in range**, from the base-gate fact `kN = 1` on `rp / sl / sr` rows (the J chip's
`RowFacts`, `jrows_gate` / `honestJ8_facts` + `mvFixP_facts`) and `|cells| < p`. -/
theorem jReads_rangeG (hlen : (j8DataGen p Rg Rt hgen O).cells.length < p)
    (hkN : ∀ x ∈ (j8DataGen p Rg Rt hgen O).jrows,
      (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1) :
    ∀ q ∈ (j8DataGen p Rg Rt hgen O).jrows.flatMap (fun row => (keysOf entsX row).map fun κ =>
      ((κ.headD 0).val, 1)), q.1 < (j8DataGen p Rg Rt hgen O).cells.length := by
  intro q hq
  obtain ⟨x, hx, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hq
  obtain ⟨hkd, hhead⟩ := keysOf_entsX_head x κ hκ
  have hk1 := hkN x hx hkd
  obtain ⟨r0, hr0, hpre, hkN', hvN'⟩ := mvFixP_mem _ _ x hx
  have hjn := jn_goodG p Rg Rt hgen O
  have hread := honestJ8_read (p := p) (hd := hJd p (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).acs)
    (cells_closedG p Rg Rt hgen O) Rt (j8DataGen p Rg Rt hgen O).regs
    (j8DataGen p Rg Rt hgen O).calls (by
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
    have hlt : idxOf (j8DataGen p Rg Rt hgen O).cells (Noun.cell a b) < (j8DataGen p Rg Rt hgen O).cells.length :=
      idxOf_lt _ _ hm
    simp only [hJd, hdlP]
    rw [ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) hlt

end Data
end RangeJ
end
end ComplJ8DataG_1
/-! ### Twins of `ComplJ8Walk` -/

section ComplJ8WalkG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk
open Nock Nock.Walk Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
noncomputable section
section J8Inst
open Nock.V1J8.Gen (addCells cellsOfRoots)
/-- **J-8 instance**: at the run's data (`j8DataGen`), `hleaf` over the demand roots gives every cell of
the cell table a cell of rank `< 2^110`. -/
theorem j8_cells_okG (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    {fuel : ℕ} {s f r : Noun} {t : NTree Nock.Edit.GenX.SkelX} (hgen : Nock.Edit.GenX.genX Rg.R fuel s f = some (t, r)) (O : Ord8)
    (hleaf : RootsLeafOK (j8DataGen p Rg Rt hgen O).roots) :
    (∀ c ∈ (j8DataGen p Rg Rt hgen O).cells, c.isCell = true) ∧
      ∀ c ∈ (j8DataGen p Rg Rt hgen O).cells, rankOf c < 2 ^ 110 :=
  ⟨fun c hc => (cells_ok_of_leaf _ hleaf).1 c ((O.permC _).mem_iff.mp hc),
    fun c hc => (cells_ok_of_leaf _ hleaf).2 c ((O.permC _).mem_iff.mp hc)⟩

end J8Inst
end
end ComplJ8WalkG_1
/-! ### Twins of `ComplJ8CompRun` -/

section ComplJ8CompRunG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8CompRun
open Nock Nock.Noun Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.HonestTraceX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data ( J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp
open Nock.NockVMROM.Thm54.SVFrame
noncomputable section
section Run
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
local notation "DD" => j8DataGen p Rg Rt hgen O
/-- The compute publics of the run's honest message. -/
abbrev pubRunG (χ : Coins frameJ8 K) : ℕ → ZMod p :=
  pubCOf δ b (DD).H (DD).pd (bfsForest [(DD).t]) (cJ s f r) χ

/-- **`hH`** (`hdlOKG`). -/
theorem hH_runG : HonestCompX.HdlOK (ringChar (ZMod p)) (DD).H :=
  hdlOKG p Rg Rt hgen O

theorem hpub_runG (hcl : ∀ k : Fin 3, ∀ v, claimNoun (cJ s f r) k = .atom v → v < p) (χ : Coins frameJ8 K) :
    pubRunG δ b Rt hgen O χ 0 = HonestCompX.hk (DD).H s ∧ pubRunG δ b Rt hgen O χ 1 = HonestCompX.hv (DD).H s ∧
    pubRunG δ b Rt hgen O χ 2 = HonestCompX.hk (DD).H f ∧ pubRunG δ b Rt hgen O χ 3 = HonestCompX.hv (DD).H f ∧
    pubRunG δ b Rt hgen O χ 4 = HonestCompX.hk (DD).H r ∧ pubRunG δ b Rt hgen O χ 5 = HonestCompX.hv (DD).H r := by
  have hH' : HonestCompX.HdlOK p (DD).H := by
    have := hH_runG Rt hgen O (p := p); rwa [ZMod.ringChar_zmod_n] at this
  exact hpub δ b (DD).pd _ hH' hcl χ

theorem hpS_runG (hcl : ∀ k : Fin 3, ∀ v, claimNoun (cJ s f r) k = .atom v → v < p) (χ : Coins frameJ8 K) :
    limbVal b (pubRunG δ b Rt hgen O χ) ChipH.pubSeed =
      curW (F := ZMod p) (DD).H (bfsForest [(DD).t]) (InhabJ8Comp.γC0 b χ) 1 * InhabJ8Comp.αC0 b χ := by
  have hH' : HonestCompX.HdlOK p (DD).H := by
    have := hH_runG Rt hgen O (p := p); rwa [ZMod.ringChar_zmod_n] at this
  have hlab := genX_label hgen
  have hroot : tripOf (DD).t = ((cJ s f r).subject, (cJ s f r).formula, (cJ s f r).result) := by
    simp [tripOf, cJ, j8DataGen, hlab.1, hlab.2.1, hlab.2.2.1]
  exact hpS δ b (DD).pd _ hH' hcl rfl hroot χ

theorem hρ_runG (χ : Coins frameJ8 K) :
    ∀ a < 6, ∀ k : Fin 3, pubRunG δ b Rt hgen O χ (pubOfA a + k) =
      coord b (accV b δ (DD).H (DD).pd (bfsForest [(DD).t]) (chalVJ8 b χ) (pubRunG δ b Rt hgen O χ) a
        (bfsForest [(DD).t]).length) k :=
  ComplJ8Comp.hρ δ b (DD).H (DD).pd _ (cJ s f r) χ

end Run
end
end ComplJ8CompRunG_1
/-! ### Twins of `ComplJ8Jet` -/

section ComplJ8JetG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet
open Nock Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Walk Nock.Framework
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.Jet.ChipJ8 (PRow chainPre nodePre nodesPre blockPre blocks callPre regPre layoutJ8 tvKey axPosB jetChipJ8 CRow baseGatesJ envOf keysOf ents3 entsX)
open Nock.Jet.RapJetJ8 (coinsJ coinsJX consKT provKT keyK)
open Nock.Jet.ChipJ8T.HonestRAP (polyJC layJ termJ sX)
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.MonolithicRAP Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsJJ8)
open Polynomial
noncomputable section
section Instance
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (mvFixP pinsOfP J8Data rowsOfT hJd)
open Nock.Jet.ChipJ8 Nock.Jet.Autogen
variable {p : ℕ} [Fact p.Prime]
theorem j8DataOf_jrowsG {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) :
    (j8DataGen p Rg Rt hgen O).jrows = mvFixP p (honestJ8G (hJd p (j8DataGen p Rg Rt hgen O).cells (j8DataGen p Rg Rt hgen O).acs) Rt
      (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).calls)
      (pinsOfP p (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).idx) := rfl

theorem j8DataOf_idsG {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) :
    (j8DataGen p Rg Rt hgen O).ids = (j8DataGen p Rg Rt hgen O).calls.map Prod.fst := rfl

theorem j8DataOf_callsG {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) :
    (j8DataGen p Rg Rt hgen O).calls = Nock.V1J8.Gen.callsOf (rowsOfT t) := rfl

/-- **The base gates on the J rows of a run** (`j8DataGen`): from `HregC`'s witness table alone. -/
theorem jrows_gate_runG {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) (hp : 0 < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      axPosB (Rt id) = true ∧ (Rt id).WellTyped p) :
    ∀ x ∈ (j8DataGen p Rg Rt hgen O).jrows, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))),
      g.eval (envOf x) = 0 :=
  jrows_gate _ hp (j8DataOf_jrowsG Rt hgen O) (by rw [j8DataOf_callsG]; exact calls_of_hregC hgen Rt hRt)

/-- The layout of the run's J rows. -/
theorem jrows_pre_runG {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Tpl) {fuel : ℕ} {s f r : Noun}
    {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8) :
    (j8DataGen p Rg Rt hgen O).jrows.map CRow.pre =
      layoutJ8 Rt (j8DataGen p Rg Rt hgen O).regs (j8DataGen p Rg Rt hgen O).ids :=
  jrows_pre _ (j8DataOf_jrowsG Rt hgen O) (j8DataOf_idsG Rt hgen O)

end Instance
end
end ComplJ8JetG_1
/-! ### Twins of `ComplJ8Atom` -/

section ComplJ8AtomG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ Nock.NockVMROM.Thm54.VclL.Handle.QGates
open Module
open scoped Polynomial
section Gen6
open Nock.V1J8.Gen
open Nock.Atoms (B)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (keyP ptrP valROfK incChainK)
section Chain
variable {rows : Array Nock.Edit.GenX.RowNX}
instance (l : List ℕ) : Decidable (Cnd l) := by unfold Cnd; infer_instance
end Chain
end Gen6
section Gen8
open Nock.V1J8.Gen
open Nock.Atoms (B val limbs)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.Edit Nock.Edit.GenX Nock.Walk
section RunJ8
variable (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
/-- **The run facts of a generated run** at Goldilocks (`GenHyp` of `j8DataGen`), under the two run binders. -/
theorem genHyp_j8G (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hN : (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows.size ≤ 2 ^ 31) :
    GenHyp (j8DataGen Nock.Atoms.p Rg Rt hgen O).bigs (j8DataGen Nock.Atoms.p Rg Rt hgen O).dupP
      (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows (j8DataGen Nock.Atoms.p Rg Rt hgen O).mb := by
  have hB : ∀ a, a ∈ (j8DataGen Nock.Atoms.p Rg Rt hgen O).bigs ↔
      a ∈ ((j8DataGen Nock.Atoms.p Rg Rt hgen O).roots ++
        (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows.toList.flatMap rowHandleNounsX).flatMap leavesOf ∧
        Nock.Atoms.p ≤ a :=
    fun a => mem_bigsP Nock.Atoms.p _ _ a
  have hrowB : ∀ x ∈ (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows.toList, ∀ y ∈ rowHandleNounsX x, ∀ a ∈ leavesOf y,
      Nock.Atoms.p ≤ a → a ∈ (j8DataGen Nock.Atoms.p Rg Rt hgen O).bigs := by
    intro x hx y hy a ha hp
    exact (hB a).mpr ⟨List.mem_flatMap.mpr ⟨y, List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hy⟩), ha⟩, hp⟩
  refine ⟨fun a ha => ((hB a).mp ha).2, fun vc hvc => ?_, fun ⟨vc, hvc, hp⟩ => ?_, fun j hj hm => ?_, hN⟩
  · obtain ⟨x, hx, hst, hs1, hle⟩ := mem_incOpsP _ _ vc hvc
    obtain ⟨n, hn1, he⟩ := s4_row hgen hax hop5 hx hst
    rw [hs1] at hn1; cases hn1
    have hsf : x.sf1 ∈ rowHandleNounsX x := by simp [rowHandleNounsX]
    have hee : x.e ∈ rowHandleNounsX x := by simp [rowHandleNounsX]
    refine ⟨fun hp => hrowB x hx _ hee _ (by rw [he]; simp [leavesOf, hp]) (by omega), fun hp => ⟨?_, ?_⟩⟩
    · exact hrowB x hx _ hsf _ (by rw [hs1]; simp [leavesOf]) (by omega)
    · exact hrowB x hx _ hee _ (by rw [he]; simp [leavesOf]) hle
  · show (incOpsP Nock.Atoms.p (rowsOfT t)).any (fun x => x.1 + 1 = Nock.Atoms.p) = true
    exact List.any_eq_true.mpr ⟨vc, hvc, by simp [hp]⟩
  · rw [mb_eq_cntG Nock.Atoms.p Rg Rt hgen O j hj] at hm
    obtain ⟨q, hq, hq0⟩ : ∃ q ∈ ((mbRecs (j8DataGen Nock.Atoms.p Rg Rt hgen O)).flatMap NamedRecs.recs).filter
        (fun q => q.1 = j), q.2 ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_and, ne_eq, not_not] at hc
      apply hm
      unfold cnt
      exact List.sum_eq_zero fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact hc q hq
    simp only [List.mem_filter, decide_eq_true_eq] at hq
    obtain ⟨hq, rfl⟩ := hq
    simp only [mbRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_filterMap,
      Option.map_eq_some_iff] at hq
    obtain ⟨n, hn, i, hi, rfl⟩ := hq
    obtain ⟨c, hc, hnc⟩ := List.mem_flatMap.mp hn
    cases n with
    | cell u w => simp [bigIdOfP] at hi
    | atom a =>
      simp only [bigIdOfP] at hi
      split_ifs at hi with hlt
      cases hi
      refine ⟨a, (hB a).mpr ⟨?_, by omega⟩, rfl⟩
      have hla : a ∈ leavesOf c := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hnc
        cases c with
        | atom b => rcases hnc with h | h <;> simp [hdN', tlN'] at h <;> subst h <;> simp [leavesOf]
        | cell u w => rcases hnc with h | h <;> simp [hdN', tlN'] at h <;> subst h <;> simp [leavesOf]
      have := leaves_cellsOfRoots _ c ((O.permC _).mem_iff.mp hc) a hla
      exact List.mem_flatMap.mpr (by
        obtain ⟨y, hy, hay⟩ := List.mem_flatMap.mp this
        exact ⟨y, List.mem_append_left _ hy, hay⟩)

/-- **The generator's atom table is valid** for every generated run at Goldilocks: `AtomTab.Valid` of the data's `acs` /
`info` / `mb`, hence `RowOK` at every row (`AtomTab.rows_ok`), from the two run binders (no inc-corner
binder; the rows bound `hN`, from `h31` by `rows_le_of_rows31G`). -/
theorem valid_j8_genG (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hN : (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows.size ≤ 2 ^ 31) :
    (tabOf (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs (j8DataGen Nock.Atoms.p Rg Rt hgen O).info
      (j8DataGen Nock.Atoms.p Rg Rt hgen O).mb (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows).Valid :=
  valid_gen _ _ _ _ (genHyp_j8G Rg Rt hgen O hax hop5 hN)

end RunJ8
end Gen8
end ComplJ8AtomG_1
/-! ### Twins of `ComplJ8BigBound` -/

section ComplJ8BigBoundG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8BigBound
open Nock Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL (hdN tlN)
open Nock.NockVMROM.Thm54.VclL.Handle (fdN axisOfPath)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgOp5OK Op5RowX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
section Data
open Nock.Jet.Autogen (Tpl compile)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.V1J8.Gen (callsOf rootsOf atomV)
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Tpl} {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
include hgen in
theorem data_rowsG : (j8DataGen p Rg Rt hgen O).rows = rowsOfT t := rfl

include hgen in
theorem data_bigsG : (j8DataGen p Rg Rt hgen O).bigs =
    bigsP p (rootsOf ⟨s, f, r⟩ (rowsOfT t) ++ jNounsP p Rt ((callsOf (rowsOfT t)).map Prod.fst).dedup
      (callsOf (rowsOfT t))) (rowsOfT t) := rfl

include hgen in
theorem data_acsG : (j8DataGen p Rg Rt hgen O).acs = acsP p (j8DataGen p Rg Rt hgen O).bigs
    (j8DataGen p Rg Rt hgen O).dupP := rfl

/-- **The big-atom bound of a run**: under the subject / formula leaves `< p`, `HregC` at `Rt` and
the op-5 depth binder, every big atom of the run's data is `< p + |rows|` (each op-4 row adds at most one). -/
theorem bigs_ltG (hS : ∀ v ∈ s.leafList, v < p) (hF : ∀ v ∈ f.leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hop5 : ProgOp5OK p t) :
    ∀ a ∈ (j8DataGen p Rg Rt hgen O).bigs, a < p + (j8DataGen p Rg Rt hgen O).rows.size := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hJ : JetB p Rg.R t := fun id hid => ⟨Rt id, (hRt id hid).1, (hRt id hid).2.2⟩
  obtain ⟨hr, hn⟩ := gen_bnd hp2 hgen p le_rfl hJ hop5 (bnd_of_leafList hS) (bnd_of_leafList hF)
  set K := p + t.size with hK
  have hKp : p ≤ K := by omega
  have hsB : Bnd K s := bnd_mono (by omega) (bnd_of_leafList hS)
  have hfB : Bnd K f := bnd_mono (by omega) (bnd_of_leafList hF)
  -- every handle noun of every row
  have hrow : ∀ x ∈ (rowsOfT t).toList, ∀ m ∈ rowHandleNounsX x, Bnd K m := by
    intro x hx m hm
    obtain ⟨u, hu, rfl⟩ := mem_rowsOfT hx
    exact (hn u hu).1 m hm
  -- the calls
  have hcall : ∀ cl ∈ callsOf (rowsOfT t), cl.1 ∈ CalledIds t ∧ Bnd K cl.2 ∧
      Bnd K (compile p (Rt cl.1)) := by
    intro cl hcl
    simp only [callsOf, List.mem_filterMap] at hcl
    obtain ⟨x, hx, hxc⟩ := hcl
    split_ifs at hxc with hst
    obtain rfl := Option.some.inj hxc
    obtain ⟨u, hu, rfl⟩ := mem_rowsOfT hx
    obtain ⟨id, j, hid, hRj, hjc⟩ := (hn u hu).2 hst
    have hcal : id ∈ CalledIds t := ⟨u, hu, hst, hid⟩
    rw [hid]
    refine ⟨hcal, (hn u hu).1 _ (by simp [rowHandleNounsX]), ?_⟩
    have h1 := (hRt id hcal).1
    rw [hRj, Option.some.injEq] at h1
    subst h1
    simp only [atomV]
    have hjc' : compile p (Rt id) = (rowOfSkelX u.label).ftt := hjc
    rw [hjc']
    exact (hn u hu).1 _ (by simp [rowHandleNounsX])
  have hroots : ∀ m ∈ rootsOf ⟨s, f, r⟩ (rowsOfT t) ++ jNounsP p Rt ((callsOf (rowsOfT t)).map Prod.fst).dedup
      (callsOf (rowsOfT t)), Bnd K m := by
    intro m hm
    simp only [rootsOf, jNounsP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap, List.mem_map, List.mem_dedup] at hm
    rcases hm with ((rfl | rfl | rfl) | ⟨x, hx, hm⟩) | (⟨i, ⟨cl, hcl, rfl⟩, rfl⟩ | ⟨⟨cl, c⟩, hcl, hm⟩)
    · exact hsB
    · exact hfB
    · exact hr
    · exact hrow x hx m (by
        simp only [handleNounsX, List.mem_cons, List.not_mem_nil, or_false] at hm
        simp only [rowHandleNounsX, List.mem_cons]
        rcases hm with h | h | h | h | h | h <;> simp [h])
    · exact (hcall cl hcl).2.2
    · have hcl' := List.fst_mem_of_mem_zipIdx hcl
      obtain ⟨hid, hsB', -⟩ := hcall cl hcl'
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact hsB'
      · simp only [callValsP, List.mem_map] at hm
        obtain ⟨y, hy, rfl⟩ := hm
        exact bnd_honestRows (by omega) hKp (Rt cl.1) (hRt cl.1 hid).2.2 hsB' c y hy
  intro a ha
  rw [data_bigsG] at ha
  obtain ⟨-, m, hm, ham⟩ := mem_bigsP ha
  rw [data_rowsG, size_rowsOfT]
  rw [List.mem_append, List.mem_flatMap] at hm
  rcases hm with hm | ⟨x, hx, hm⟩
  · exact bnd_leavesOf (hroots m hm) a ham
  · exact bnd_leavesOf (hrow x hx m hm) a ham

end Data
section DataSingle
open Nock.Jet.Autogen (Tpl compile)
open Nock.Atoms (B limbs)
open Nock.V1J8.Gen (combOf lastIdxOf idxOf idxN)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom (spineL)
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Tpl} {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
include hgen in
/-- **Atom bound at `j8DataGen`** (Goldilocks, rows `≤ 2^31`): every big atom is `< p + |rows|` and has two limbs
`[a + 1 − p, B − 1]`; the `p` duplicate is off; `D.acs` is duplicate-free with `combPP` at most once; its last index
is its first index; `rIAP p D.acs = idxN D.acs`; every member's `idxOf` is `List.idxOf`; `rootIdxP` is the comb's
first index. -/
theorem bigBound_singleG (hpG : p = Nock.Atoms.p) (hS : ∀ v ∈ s.leafList, v < p) (hF : ∀ v ∈ f.leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hop5 : ProgOp5OK p t) (hN : (j8DataGen p Rg Rt hgen O).rows.size ≤ 2 ^ 31) :
    let D := j8DataGen p Rg Rt hgen O
    (∀ a ∈ D.bigs, p ≤ a ∧ a < p + D.rows.size ∧ limbs a = [a + 1 - p, B - 1]) ∧
      (D.dupP && decide (Noun.cell (.atom 0) (combPP p) ∈ spineL D.bigs)) = false ∧
      D.acs.Nodup ∧ List.count (combPP p) D.acs ≤ 1 ∧
      lastIdxOf D.acs (combPP p) = idxOf D.acs (combPP p) ∧
      (combPP p ∈ D.acs → lastIdxOf D.acs (combPP p) = List.idxOf (combPP p) D.acs) ∧
      rIAP p D.acs = idxN D.acs ∧
      (∀ n ∈ D.acs, idxOf D.acs n = List.idxOf n D.acs) ∧
      ∀ a, rootIdxP p D.acs a = idxOf D.acs (combOf (limbs a)) := by
  intro D
  have hlt := bigs_ltG hgen O hS hF hRt hop5
  have hge : ∀ a ∈ D.bigs, p ≤ a := fun a ha => by
    rw [data_bigsG] at ha; exact (mem_bigsP ha).1
  subst hpG
  have hb : ∀ a ∈ D.bigs, Nock.Atoms.p ≤ a ∧ a < Nock.Atoms.p + 2 ^ 31 :=
    fun a ha => ⟨hge a ha, by have := hlt a ha; omega⟩
  have H := single_p D.dupP hb
  rw [← data_acsG hgen O] at H
  exact ⟨fun a ha => ⟨hge a ha, hlt a ha, limbs_two (hb a ha).1 (hb a ha).2⟩, H⟩

end DataSingle
end ComplJ8BigBoundG_1
/-! ### Twins of `ComplJ8AW` -/

section ComplJ8AWG_1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8AW
open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Module
open scoped Polynomial
noncomputable section
section J8Inst
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (atomChipHQ pubMB pubC pubMI mb inc mi)
open Nock.Edit Nock.Edit.GenX
variable {K : Type} [Field K] [Algebra (ZMod Nock.Atoms.p) K] [FiniteDimensional (ZMod Nock.Atoms.p) K]
  [Fintype K] (δ : ZMod Nock.Atoms.p) [Fact (¬ IsSquare (algebraMap (ZMod Nock.Atoms.p) K δ))]
  (b : Basis (Fin 3) (ZMod Nock.Atoms.p) K)
  (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) (O : Ord8)
  {hA : ℕ} (hn : 0 < (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length)
  (nodes : Fin (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length → ZMod Nock.Atoms.p)
  (orbit : StrictOrbitDomain (ZMod Nock.Atoms.p) 3 hA) (chals pubs : ℕ → K)
  (col : ℕ → Fin (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length → ZMod Nock.Atoms.p)
/-- The honest atom rows of a generated run (`tabOf` of the data). -/
abbrev rowsJ8G : ℕ → NRow :=
  (tabOf (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs (j8DataGen Nock.Atoms.p Rg Rt hgen O).info
    (j8DataGen Nock.Atoms.p Rg Rt hgen O).mb (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows).row

/-- **The generator's atom table at a good coin** (J-8 instance, Goldilocks): `atomChipHQ` and `atomChipHQL` are
satisfied and bound by the honest trace `atomTraceHQ … col (newOf rowsJ8G)`. Inputs: the run binders and
`hcor` (no inc corner; the J-8 name `atomOK_j8` under `complJ8`'s binders is in `ComplJ8OfAtom`); the cell
part `col` carries the generator's cell data of `acs` (`hcol`, as `GenMem.cellD`) and is accepted by `cellChipHQ`
(`hsat0`, the lemma at the atom cell list); the three non-vanishing atom denominators (bad events); the three
atom terminals (balances); the nodes. -/
theorem atomOK_j8_genG (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hN : (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows.size ≤ 2 ^ 31)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin _) (hi : (i : ℕ) + 1 < (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length),
      nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hcol : ∀ i : Fin (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length,
      let y := (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs[(i : ℕ)]
      col Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      col Cell.idR i = (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs
        (j8DataGen Nock.Atoms.p Rg Rt hgen O).rows y else 0 : ℕ))
        : ZMod Nock.Atoms.p) ∧
      col Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      col Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p))
    (hsat0 : (cellChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hz1 : ∀ i, HonestA8.dMB δ b hn nodes orbit chals pubs col (newOf (rowsJ8G Rg Rt hgen O)) i ≠ 0)
    (hz2 : ∀ i, HonestA8.dC δ b hn nodes orbit chals pubs col (newOf (rowsJ8G Rg Rt hgen O)) i ≠ 0)
    (hz3 : ∀ i, HonestA8.dMI δ b hn nodes orbit chals pubs col (newOf (rowsJ8G Rg Rt hgen O)) i ≠ 0)
    (hpMB : Quad.mk _ (pubs pubMB) (pubs (pubMB + 1)) = ∑ j ∈ Finset.range (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length) (rowsJ8G Rg Rt hgen O) mb)) *
        (HonestA8.dNat δ (HonestA8.dMB δ b hn nodes orbit chals pubs col (newOf (rowsJ8G Rg Rt hgen O))) j)⁻¹)
    (hpC : Quad.mk _ (pubs pubC) (pubs (pubC + 1)) = ∑ j ∈ Finset.range (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length) (rowsJ8G Rg Rt hgen O) inc)) *
        (HonestA8.dNat δ (HonestA8.dC δ b hn nodes orbit chals pubs col (newOf (rowsJ8G Rg Rt hgen O))) j)⁻¹)
    (hpMI : Quad.mk _ (pubs pubMI) (pubs (pubMI + 1)) = ∑ j ∈ Finset.range (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length) (rowsJ8G Rg Rt hgen O) mi)) *
        (HonestA8.dNat δ (HonestA8.dMI δ b hn nodes orbit chals pubs col (newOf (rowsJ8G Rg Rt hgen O))) j)⁻¹) :
    (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies
        (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8G Rg Rt hgen O))) ∧
      (atomChipHQ δ b hn nodes orbit chals pubs).BindsPreprocessing
        (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8G Rg Rt hgen O))) ∧
      (AtomChipHQL.atomChipHQL δ b hn nodes orbit chals pubs).rap.Satisfies
        (AtomChipHQL.ofHQ δ b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8G Rg Rt hgen O)))) ∧
      (AtomChipHQL.atomChipHQL δ b hn nodes orbit chals pubs).BindsPreprocessing
        (AtomChipHQL.ofHQ δ b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsJ8G Rg Rt hgen O)))) := by
  have hv := valid_j8_genG Rg Rt hgen O hax hop5 hN
  have hg := genHyp_j8G Rg Rt hgen O hax hop5 hN
  obtain ⟨hok, hlast⟩ := AtomTab.rows_ok hv (n := (j8DataGen Nock.Atoms.p Rg Rt hgen O).acs.length) rfl
  have hB : Nock.Atoms.B < ringChar (ZMod Nock.Atoms.p) := by
    rw [ZMod.ringChar_zmod_n]; exact Nock.Atoms.B_lt_p
  refine atomOK_of_rows δ b hn nodes orbit chals pubs col hinj hadj hB (rowsJ8G Rg Rt hgen O) (fun i => ?_) hok hlast
    hsat0 hz1 hz2 hz3 hpMB hpC hpMI
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcol i
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := row_cell _ _ _ _ hg (j8DataGen Nock.Atoms.p Rg Rt hgen O).info i i.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c1]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e1.symm
  · rw [c2]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e6.symm
  · rw [c3]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e4.symm
  · rw [c4]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e5.symm
  · rw [c5]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e2.symm
  · rw [c6]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e3.symm

end J8Inst
end
end ComplJ8AWG_1

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
