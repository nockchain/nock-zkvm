/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/CanonRunP1.lean

 **the run-side facts of the canonical generator, derived from the P1 fragment.**

 `CanonGenP1` / `CanonWalkP1` take run-side facts about `j8DataCanon p Rg Rt hgen` as hypotheses. Here they are
 derived from the formula-side fragment conditions of `P1FragC` (`opsB`, `axesB`, small atoms) and the run `hgen`
 (at ANY registry: the fragment has no op 11, so the registry is never consulted).

 * §1 `p1_gen`: along a run of a fragment formula every row is a fragment row (`RowP1`): its twelve handles have
 leaves `< P`, its state is one of `cons, s0, s7, s10, s10L, s10T`, and every walk read sits at an axis
 `< 2^61` whose root is a cell when the axis is `≥ 2`.
 * §2 the data facts at `j8DataCanon` (item (a)): `calls = ids = regs = jn = []`, `bigs = []`, `dupP = false`,
 `acs = [padN]`, `preads = []`, `jrows = []`.
 * §3 `hsmall` (item (b)), walk depth (item (e): `WalkDepthOK reads`, `WalkDepthOK preads`, the trie labels
 `≤ 60`), path roots are cells of the table (item (f)).
 * §4 the `J = 0` swap (item (h)): at `nJ = 0`, `AcceptsJ8V` reads no J column.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonWalkP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1

open Nock Nock.Walk Nock.Jet Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL (hdN tlN)
open Nock.NockVMROM.Thm54.VclL.Handle (fdN axisOfPath)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8BigBound
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

noncomputable section

/-! ## 1. The fragment rows -/

section Rows

/-- The fragment states. -/
def stP1 : List StateX := [.cons, .s0, .s7, .s10, .s10L, .s10T]

/-- **A fragment row** (bound `P`): handles with leaves `< P`, a fragment state, walk reads at axes `< 2^61`
rooted at cells (axis `≥ 2`). -/
structure RowP1 (P : ℕ) (r : RowNX) : Prop where
  bnd : ∀ x ∈ rowHandleNounsX r, Bnd P x
  st : r.st ∈ stP1
  rd : ∀ y ∈ consEntriesX r, y.2.1 < 2 ^ 61 ∧ (2 ≤ y.2.1 → y.1.isCell = true)

theorem isCell_of_slot : ∀ (a : ℕ) {n m : Noun}, 2 ≤ a → Noun.slot a n = some m → n.isCell = true := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro n m h2 h
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
    rw [Noun.slot] at h
    cases hs : Noun.slot (k / 2 + 1) n with
    | none => simp [hs] at h
    | some w =>
      cases w with
      | atom _ => simp [hs] at h
      | cell l r =>
        by_cases h1 : k / 2 + 1 = 1
        · rw [h1, Noun.slot] at hs
          obtain rfl := Option.some.inj hs
          rfl
        · exact ih (k / 2 + 1) (by omega) (by omega) hs

theorem isCell_of_edit {a : ℕ} {new old e : Noun} (h2 : 2 ≤ a) (h : Noun.edit a new old = some e) :
    e.isCell = true :=
  isCell_of_slot a h2 (edit_iff_chainOK.mp h).2

theorem bnd_sibX {P : ℕ} (hP : 0 < P) (b : ℕ) {n : Noun} (hn : Bnd P n) : Bnd P (sibX b n) := by
  unfold sibX
  cases hs : Noun.slot (b ^^^ 1) n with
  | none => simpa using hP
  | some m => exact bnd_slot _ _ hs hn

theorem xor_one_lt61 {a : ℕ} (h : a < 2 ^ 61) : a ^^^ 1 < 2 ^ 61 := by
  rw [xor_one_eq]
  have : (2 : ℕ) ^ 61 = 2 * 2 ^ 60 := by norm_num
  split <;> omega

/-- **Every row of an edit chain is a fragment row** (`old`, `e` bounded, chain axis `< 2^61 < P`). -/
theorem chain_p1 {P : ℕ} (hP : 2 ^ 61 < P) {old e : Noun} (ho : Bnd P old) (he : Bnd P e) :
    ∀ (k a : ℕ), a < 2 ^ 61 → ChainOK a old e → ∀ u, InTree (genChainF old e k a) u →
      RowP1 P (rowOfSkelX u.label) := by
  have hrowL : ∀ (a : ℕ) (ks : List RowX), a < 2 ^ 61 → ChainOK a old e → 2 ≤ a →
      RowP1 P (rowOfSkelX ⟨.s10L, old, .atom a, e, ks⟩) := by
    intro a ks ha hc h2
    obtain ⟨x, hx1, hx2⟩ := hc 0 (by simpa using h2)
    simp only [pow_zero, Nat.div_one] at hx1 hx2
    have h2x := two_le_xor_one h2
    have hco := isCell_of_slot _ h2x hx1
    have hce := isCell_of_slot _ h2x hx2
    have hxl := xor_one_lt61 ha
    refine ⟨fun x hx => ?_, by simp [rowOfSkelX, stP1], fun y hy => ?_⟩
    · simp only [rowOfSkelX, rowHandleNounsX, chainAxis, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact ho
        | exact he
        | exact bnd_sibX (by omega) _ ho
        | exact bnd_sibX (by omega) _ he
        | (simp only [bnd_atom]; omega)
    · simp only [rowOfSkelX, consEntriesX, chainAxis, atomVal] at hy
      simp at hy
      rcases hy with rfl | rfl
      · exact ⟨hxl, fun _ => hco⟩
      · exact ⟨hxl, fun _ => hce⟩
  have hrowT : ∀ (a : ℕ) (ks : List RowX), a < 2 ^ 61 → RowP1 P (rowOfSkelX ⟨.s10T, old, .atom a, e, ks⟩) := by
    intro a ks ha
    refine ⟨fun x hx => ?_, by simp [rowOfSkelX, stP1], fun y hy => by simp [rowOfSkelX, consEntriesX] at hy⟩
    simp only [rowOfSkelX, rowHandleNounsX, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact ho
      | exact he
      | (simp only [bnd_atom]; omega)
  intro k
  induction k with
  | zero =>
    intro a ha hc u hu
    simp only [genChainF] at hu
    rcases inTree_mkX hu with rfl | ⟨k, hk, -⟩
    · exact hrowT a _ ha
    · simp at hk
  | succ k ih =>
    intro a ha hc u hu
    simp only [genChainF] at hu
    split_ifs at hu with h2
    · rcases inTree_mkX hu with rfl | ⟨c, hc', hcu⟩
      · exact hrowL a _ ha hc h2
      · simp only [List.mem_singleton] at hc'; subst hc'
        exact ih (a / 2) (by omega) (chainOK_half hc) u hcu
    · rcases inTree_mkX hu with rfl | ⟨k, hk, -⟩
      · exact hrowT a _ ha
      · simp at hk

end Rows

/-! ## 2. The run -/

section Run

/-- The root row's handles (as `root_tac`, closing trivial goals first). -/
macro "root1" : tactic => `(tactic| (
  simp only [mkX_label, rowOfSkelX, rowHandleNounsX, kidE, kidF, List.map_cons, List.map_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some, SkelX.row,
    hdN, tlN, List.forall_mem_cons, List.forall_mem_nil, and_true, *] <;>
  (repeat' apply And.intro) <;> first | trivial | bnd_tac))

theorem p1_gen {P : ℕ} (hP : 2 ^ 61 < P) {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) :
    opsB f = true → axesB f = true → Bnd P s → Bnd P f →
      Bnd P r ∧ ∀ u, InTree t u → RowP1 P (rowOfSkelX u.label) := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals first | (simp_all [genComputeSkeletonX]; done) | skip
  all_goals first | (intro hops; simp [opsB] at hops; done) | skip
  case case3 n s b c d tl l tr r' hd hbc ihbc ihd =>
    simp only [genComputeSkeletonX, hd, hbc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro hops hax hs hf
    simp only [opsB, Bool.and_eq_true] at hops
    simp only [axesB, Bool.and_eq_true] at hax
    simp only [bnd_cell] at hf
    obtain ⟨⟨hb, hc⟩, hd'⟩ := hf
    obtain ⟨hr1, hn1⟩ := ihbc hbc hops.1 hax.1 hs ⟨hb, hc⟩
    obtain ⟨hr2, hn2⟩ := ihd hd hops.2 hax.2 hs hd'
    have e1 := (genX_label hbc).2.2.1
    have e2 := (genX_label hd).2.2.1
    refine ⟨⟨hr1, hr2⟩, fun u hu => ?_⟩
    rcases inTree_mkX hu with rfl | ⟨k, hk, hku⟩
    · refine ⟨?_, by simp [rowOfSkelX, stP1], fun y hy => by simp [rowOfSkelX, consEntriesX] at hy⟩
      root1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hn1 u hku
      · exact hn2 u hku
  case case5 n s ax r' hs =>
    simp only [genComputeSkeletonX, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro hops hax hsub hf
    simp only [axesB, Bool.and_eq_true, decide_eq_true_eq] at hax
    simp only [bnd_cell, bnd_atom] at hf
    have hr := bnd_slot _ _ hs hsub
    refine ⟨hr, fun u hu => ?_⟩
    rcases inTree_mkX hu with rfl | ⟨k, hk, -⟩
    · refine ⟨?_, by simp [rowOfSkelX, stP1], fun y hy => ?_⟩
      · root1
      · simp only [mkX_label, rowOfSkelX, consEntriesX, tlN, atomVal] at hy
        simp at hy
        obtain ⟨-, rfl⟩ := hy
        exact ⟨hax.2, fun h2 => isCell_of_slot ax h2 hs⟩
    · simp at hk
  case case22 n s b c tH r1 hb tM r2 hm ihb ihc =>
    simp only [genComputeSkeletonX, hb, hm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro hops hax hs hf
    simp only [opsB, Bool.and_eq_true] at hops
    simp only [axesB, Bool.and_eq_true] at hax
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, hfb, hfc⟩ := hf
    obtain ⟨hr1, hn1⟩ := ihb hb hops.1 hax.1 hs hfb
    obtain ⟨hr2, hn2⟩ := ihc hm hops.2 hax.2 hr1 hfc
    have e1 := (genX_label hb).2.2.1
    have e2 := (genX_label hm).2.2.1
    refine ⟨hr2, fun u hu => ?_⟩
    rcases inTree_mkX hu with rfl | ⟨k, hk, hku⟩
    · refine ⟨?_, by simp [rowOfSkelX, stP1], fun y hy => by simp [rowOfSkelX, consEntriesX] at hy⟩
      root1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hn2 u hku
      · exact hn1 u hku
  case case32 n s ax c d tl new tr old hd hc e he ihc ihd =>
    simp only [genComputeSkeletonX, hc, hd, he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro hops hax hs hf
    simp only [opsB, Bool.and_eq_true] at hops
    simp only [axesB, Bool.and_eq_true, decide_eq_true_eq] at hax
    simp only [bnd_cell, bnd_atom] at hf
    obtain ⟨hop, ⟨hfa, hfc⟩, hfd⟩ := hf
    obtain ⟨hr1, hn1⟩ := ihc hc hops.1 hax.1.2 hs hfc
    obtain ⟨hr2, hn2⟩ := ihd hd hops.2 hax.2 hs hfd
    have e1 := (genX_label hc).2.2.1
    have e2 := (genX_label hd).2.2.1
    have hre := bnd_edit _ _ _ he hr1 hr2
    refine ⟨hre, fun u hu => ?_⟩
    rcases inTree_mkX hu with rfl | ⟨k, hk, hku⟩
    · refine ⟨?_, by simp [rowOfSkelX, stP1], fun y hy => ?_⟩
      · root1
      · simp only [mkX_label, rowOfSkelX, consEntriesX, hdN, tlN, atomVal] at hy
        simp at hy
        obtain ⟨-, rfl⟩ := hy
        exact ⟨hax.1.1.2, fun h2 => isCell_of_edit h2 he⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact hn1 u hku
      · exact hn2 u hku
      · exact chain_p1 hP hr2 hre ax ax hax.1.1.2 (edit_iff_chainOK.mp he).1 u hku

end Run

/-! ## 3. The canonical data of a P1 run -/

section Data
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.V1J8.Gen (callsOf rootsOf cellsOfRoots padN linkOrder)

theorem p61_of {p : ℕ} (hpG : p = Nock.Atoms.p) : 2 ^ 61 < p := by
  rw [hpG, CellOrderP1.pG]; norm_num

/-- A row of `rowsOfT t` is the row of a node of `t`. -/
theorem mem_rowsOfT {t : NTree SkelX} {x : RowNX} (hx : x ∈ (rowsOfT t).toList) :
    ∃ u, InTree t u ∧ x = rowOfSkelX u.label := by
  simp only [rowsOfT, List.toList_toArray, List.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hu
  simp only [List.mem_singleton] at hc
  subst hc
  exact ⟨u, hcu, rfl⟩

variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl}
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- The claim's three nouns have leaves `< p`. -/
theorem claim_bnd (hpG : p = Nock.Atoms.p) (hc : P1FragC ⟨s, f, r⟩) : Bnd p s ∧ Bnd p f ∧ Bnd p r := by
  have h0 := hc.small 0
  have h1 := hc.small 1
  have h2 := hc.small 2
  rw [← hpG] at h0 h1 h2
  exact ⟨bnd_of_leafList h0, bnd_of_leafList h1, bnd_of_leafList h2⟩

/-- **Every row of a P1 run is a fragment row** (bound `p`). -/
theorem rows_p1 (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩) :
    ∀ x ∈ (rowsOfT t).toList, RowP1 p x := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := mem_rowsOfT hx
  obtain ⟨hs, hf, -⟩ := claim_bnd hpG hc
  exact (p1_gen (p61_of hpG) hgen hc.ops hc.axes hs hf).2 u hu

section
variable (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩)
include hpG hgen hc

theorem st_p1 : ∀ x ∈ (rowsOfT t).toList, x.st ∈ stP1 := fun x hx => (rows_p1 hpG hgen hc x hx).st

/-- **(a) no calls.** -/
theorem canon_calls : (j8DataCanon p Rg Rt hgen).calls = [] := by
  show callsOf (rowsOfT t) = []
  unfold callsOf
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  have := st_p1 hpG hgen hc x hx
  simp only [stP1, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h | h | h | h | h | h <;> simp [h]

theorem canon_ids : (j8DataCanon p Rg Rt hgen).ids = [] := by
  show (j8DataCanon p Rg Rt hgen).calls.map Prod.fst = []
  rw [canon_calls hpG hgen hc]; rfl

/-- **(a) no registered jets.** -/
theorem canon_regs : (j8DataCanon p Rg Rt hgen).regs = [] := by
  show (j8DataCanon p Rg Rt hgen).ids.dedup = []
  rw [canon_ids hpG hgen hc]; rfl

theorem canon_jn : (j8DataCanon p Rg Rt hgen).jn = [] := by
  show jNounsP p Rt (j8DataCanon p Rg Rt hgen).regs (j8DataCanon p Rg Rt hgen).calls = []
  rw [canon_regs hpG hgen hc, canon_calls hpG hgen hc]; rfl

/-- **(a) no J rows.** -/
theorem canon_jrows : (j8DataCanon p Rg Rt hgen).jrows = [] := by
  rw [j8DataOf_jrowsG, canon_regs hpG hgen hc, canon_calls hpG hgen hc]
  simp [mvFixP, Nock.Jet.ChipJ8.honestJ8G]

/-- Every handle noun of every row, and every root, has leaves `< p`. -/
theorem canon_roots_bnd : ∀ x ∈ (j8DataCanon p Rg Rt hgen).roots, Bnd p x := by
  show ∀ x ∈ rootsOf ⟨s, f, r⟩ (rowsOfT t) ++ (j8DataCanon p Rg Rt hgen).jn, Bnd p x
  rw [canon_jn hpG hgen hc, List.append_nil]
  obtain ⟨hs, hf, hr⟩ := claim_bnd hpG hc
  intro x hx
  simp only [rootsOf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hx
  rcases hx with (rfl | rfl | rfl) | ⟨y, hy, hxy⟩
  · exact hs
  · exact hf
  · exact hr
  · have hb := (rows_p1 hpG hgen hc y hy).bnd
    simp only [handleNounsX, List.mem_cons, List.not_mem_nil, or_false] at hxy
    rcases hxy with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hb _ (by simp [rowHandleNounsX])

/-- **(a) no big atoms.** -/
theorem canon_bigs : (j8DataCanon p Rg Rt hgen).bigs = [] := by
  show bigsP p (j8DataCanon p Rg Rt hgen).roots (rowsOfT t) = []
  have hroots := canon_roots_bnd (Rt := Rt) hpG hgen hc
  have hrows := rows_p1 hpG hgen hc
  have hfil : (((j8DataCanon p Rg Rt hgen).roots ++ (rowsOfT t).toList.flatMap rowHandleNounsX).flatMap
      leavesOf).filter (fun a => decide (p ≤ a)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp only [List.mem_flatMap, List.mem_append] at ha
    obtain ⟨x, hx, hax⟩ := ha
    have hbx : Bnd p x := by
      rcases hx with hx | ⟨y, hy, hxy⟩
      · exact hroots x hx
      · exact (hrows y hy).bnd x hxy
    have := bnd_leavesOf hbx a hax
    simp; omega
  unfold bigsP
  rw [hfil]; simp

/-- **(a) no `p` duplicate.** -/
theorem canon_dupP : (j8DataCanon p Rg Rt hgen).dupP = false := by
  show ((incOpsP p (rowsOfT t)).any fun x => x.1 + 1 = p) = false
  have : incOpsP p (rowsOfT t) = [] := by
    unfold incOpsP
    simp only [List.map_eq_nil_iff, List.dedup_eq_nil]
    rw [List.filterMap_eq_nil_iff]
    intro x hx
    have := st_p1 hpG hgen hc x hx
    simp only [stP1, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h | h | h <;> simp [h]
  rw [this]; rfl

/-- **(a) the atom table is the pad row.** -/
theorem canon_acs : (j8DataCanon p Rg Rt hgen).acs = [padN] := by
  rw [data_acsG, canon_bigs hpG hgen hc, canon_dupP hpG hgen hc]
  simp [acsP, linkOrder]

/-- **(a) no atom-walk reads.** -/
theorem canon_preads : (j8DataCanon p Rg Rt hgen).preads = [] := by
  show ordRS (j8DataCanon p Rg Rt hgen).H (pairReadsP (j8DataCanon p Rg Rt hgen).H (j8DataCanon p Rg Rt hgen).pd
    (rowsOfT t)) = []
  have : pairReadsP (j8DataCanon p Rg Rt hgen).H (j8DataCanon p Rg Rt hgen).pd (rowsOfT t) = [] := by
    unfold pairReadsP
    rw [List.flatMap_eq_nil_iff]
    intro x hx
    have := st_p1 hpG hgen hc x hx
    simp only [stP1, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h | h | h <;> simp [Nock.V1J8.FillX.isPairB, h]
  rw [this]; simp [ordRS]

/-- **(a) no atom-walk rows.** -/
theorem canon_vs : (j8DataCanon p Rg Rt hgen).vs = [] ∧ (j8DataCanon p Rg Rt hgen).krV = 0 := by
  have h := canon_preads (Rt := Rt) hpG hgen hc
  constructor
  · show (if (j8DataCanon p Rg Rt hgen).preads.isEmpty then (([] : List Nock.V1J8.Gen.WRow), 0)
      else Nock.V1J8.Gen.walkGen padN (j8DataCanon p Rg Rt hgen).preads).1 = []
    rw [h]; rfl
  · show (if (j8DataCanon p Rg Rt hgen).preads.isEmpty then (([] : List Nock.V1J8.Gen.WRow), 0)
      else Nock.V1J8.Gen.walkGen padN (j8DataCanon p Rg Rt hgen).preads).2 = 0
    rw [h]; rfl

/-- **(a) the atom table's walk multiplicities are `0`.** -/
theorem canon_mxA : (j8DataCanon p Rg Rt hgen).mxA = Array.replicate 1 0 ∧
    (j8DataCanon p Rg Rt hgen).mhA = Array.replicate 1 0 := by
  have hv := (canon_vs (Rt := Rt) hpG hgen hc).1
  have ha := canon_acs (Rt := Rt) hpG hgen hc
  constructor
  · show Nock.V1J8.Gen.wCounts (rIAP p (j8DataCanon p Rg Rt hgen).acs) (j8DataCanon p Rg Rt hgen).acs
      (j8DataCanon p Rg Rt hgen).vs = _
    rw [hv, ha]; rfl
  · show Nock.V1J8.Gen.wCounts (rIAP p (j8DataCanon p Rg Rt hgen).acs) (j8DataCanon p Rg Rt hgen).acs
      (j8DataCanon p Rg Rt hgen).vs = _
    rw [hv, ha]; rfl

end

end Data

/-! ## 4. Small children, walk depth, path roots -/

section Walk
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL (depthOf axisBits_of_two_le axisBits_of_lt_two isPathAx)
open Nock.V1J8.Gen (callsOf rootsOf cellsOfRoots padN linkOrder)

theorem depthOf_le' : ∀ (k a : ℕ), a < 2 ^ (k + 1) → depthOf a ≤ k := by
  intro k
  induction k with
  | zero =>
    intro a ha
    rw [depthOf, axisBits_of_lt_two (by simpa using ha)]; rfl
  | succ k ih =>
    intro a ha
    by_cases h2 : 2 ≤ a
    · rw [depthOf, axisBits_of_two_le h2, List.length_append, List.length_singleton]
      have := ih (a / 2) (by rw [pow_succ] at ha; omega)
      simp only [depthOf] at this
      omega
    · rw [depthOf, axisBits_of_lt_two (by omega)]; simp

/-- The root of every walk read of a row is one of the row's six root handles. -/
theorem consEntriesX_root (x : RowNX) : ∀ y ∈ consEntriesX x, y.1 ∈ handleNounsX x := by
  intro y hy
  simp only [consEntriesX, List.mem_append] at hy
  rcases hy with (((h | h) | h) | h) | h
  all_goals (split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
    (first | (subst h; simp [handleNounsX]) | (rcases h with rfl | rfl <;> simp [handleNounsX])))

theorem foldl_id {α β : Type} (g : α → β → α) : ∀ (l : List β) (a : α), (∀ x ∈ l, ∀ a, g a x = a) →
    l.foldl g a = a
  | [], a, _ => rfl
  | x :: l, a, h => by
    simp only [List.foldl_cons, h x (by simp)]
    exact foldl_id g l a fun y hy => h y (by simp [hy])

variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl}
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
variable (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩)
include hpG hgen hc

/-- **(b) `hsmall`**: every atom child of a cell of the canonical table is `< p`. -/
theorem canon_hsmall :
    ∀ a b, Noun.cell a b ∈ (j8DataCanon p Rg Rt hgen).cells → ∀ v, (a = .atom v ∨ b = .atom v) → v < p := by
  intro a b hab v hv
  have hm := (mem_cells_iff p Rg Rt hgen ord8Canon _).mp hab
  have hl := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.leaves_cellsOfRoots _ _ hm v
    (by rcases hv with rfl | rfl <;> simp [leavesOf])
  obtain ⟨x, hx, hvx⟩ := List.mem_flatMap.mp hl
  exact bnd_leavesOf (canon_roots_bnd hpG hgen hc x hx) v hvx

/-- **(a) no big-atom children**: the atom table's `mb` multiplicities are `0`. -/
theorem canon_mb : (j8DataCanon p Rg Rt hgen).mb = Array.replicate 1 0 := by
  show mbCountsP p (j8DataCanon p Rg Rt hgen).acs (j8DataCanon p Rg Rt hgen).cells = _
  unfold mbCountsP
  have hnone : ∀ x ∈ (j8DataCanon p Rg Rt hgen).cells.flatMap (fun n => [Nock.V1J8.Gen.hdN' n,
      Nock.V1J8.Gen.tlN' n]), bigIdOfP p (j8DataCanon p Rg Rt hgen).acs x = none := by
    intro x hx
    obtain ⟨n, hn, hxn⟩ := List.mem_flatMap.mp hx
    have hcell := (ComplJ8Walk.cellsOfRoots_mem _ n ((mem_cells_iff p Rg Rt hgen ord8Canon n).mp hn)).1
    cases n with
    | atom _ => simp [Noun.isCell] at hcell
    | cell a b =>
      have hs := canon_hsmall (Rt := Rt) hpG hgen hc a b hn
      simp only [Nock.V1J8.Gen.hdN', Nock.V1J8.Gen.tlN', List.mem_cons, List.not_mem_nil, or_false] at hxn
      rcases hxn with rfl | rfl
      · cases x with
        | atom v => simp [bigIdOfP, hs v (Or.inl rfl)]
        | cell _ _ => rfl
      · cases x with
        | atom v => simp [bigIdOfP, hs v (Or.inr rfl)]
        | cell _ _ => rfl
  refine (foldl_id _ _ _ ?_).trans ?_
  · intro x hx a
    simp only [hnone x hx]
  · rw [canon_acs (Rt := Rt) hpG hgen hc]; rfl

/-- **(b) the cell facts of `canonM_cellTr`** (`canon_cells_facts` at the derived `hsmall`). -/
theorem canon_cells_p1 :
    let cs := (j8DataCanon p Rg Rt hgen).cells
    cs.Pairwise CellOrderP1.nlt ∧ (∀ x ∈ cs, ∃ a b, x = .cell a b) ∧
      (∀ a b, Noun.cell a b ∈ cs → CanonGenP1.ChildOK p cs a ∧ CanonGenP1.ChildOK p cs b) ∧
      (∀ i (hi : i < cs.length),
        ComplJ8Cell.isBig (bigIdOfP p (j8DataCanon p Rg Rt hgen).acs) (VclL.hdN cs[i]) = false ∧
        ComplJ8Cell.isBig (bigIdOfP p (j8DataCanon p Rg Rt hgen).acs) (VclL.tlN cs[i]) = false) :=
  canon_cells_facts p Rg Rt hgen (canon_hsmall hpG hgen hc)

/-- Every J-8 walk read of the run: an axis `≥ 2` and `< 2^61` at a cell root that is a demand root. -/
theorem canon_read {x : Noun × ℕ} (hx : x ∈ Nock.V1J8.Gen.pathReads (rowsOfT t)) :
    2 ≤ x.2 ∧ x.2 < 2 ^ 61 ∧ x.1.isCell = true ∧ x.1 ∈ (j8DataCanon p Rg Rt hgen).roots := by
  simp only [Nock.V1J8.Gen.pathReads, List.mem_filter, List.mem_flatMap, List.mem_map, decide_eq_true_eq] at hx
  obtain ⟨⟨y, hy, z, hz, rfl⟩, h2⟩ := hx
  have hrd := (rows_p1 hpG hgen hc y hy).rd z hz
  refine ⟨h2, hrd.1, hrd.2 h2, ?_⟩
  show z.1 ∈ rootsOf ⟨s, f, r⟩ (rowsOfT t) ++ (j8DataCanon p Rg Rt hgen).jn
  simp only [rootsOf, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨y, hy, consEntriesX_root y z hz⟩)

/-- **(e) walk depth**: every J-8 walk read has depth `≤ 60`. -/
theorem canon_reads_depth60 : ∀ x ∈ (j8DataCanon p Rg Rt hgen).reads, depthOf x.2 ≤ 60 := by
  intro x hx
  have hx' := (mem_reads_iff p Rg Rt hgen ord8Canon x).mp hx
  exact depthOf_le' 60 x.2 (canon_read (Rt := Rt) hpG hgen hc hx').2.1

/-- **(e) `hwalk`** (`WalkDepthOK` of the J-8 walk reads). -/
theorem canon_hwalk : ComplJ8Walk.WalkDepthOK (j8DataCanon p Rg Rt hgen).reads := by
  intro x hx
  simp only [Nock.NockVMROM.Thm54.VclL.pathReads, List.mem_dedup, List.mem_filter] at hx
  have := canon_reads_depth60 hpG hgen hc x hx.1
  omega

/-- **(e) `hwalkA`** (`WalkDepthOK` of the atom-walk reads: there are none). -/
theorem canon_hwalkA : ComplJ8Walk.WalkDepthOK (j8DataCanon p Rg Rt hgen).preads := by
  rw [canon_preads hpG hgen hc]
  intro x hx
  simp [Nock.NockVMROM.Thm54.VclL.pathReads] at hx

/-- **(e) `hle`**: every honest walk row is at depth `≤ 60`. -/
theorem canon_hle : ∀ i < (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length,
    (Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.wTrie (j8DataCanon p Rg Rt hgen).cells
      (j8DataCanon p Rg Rt hgen).reads i).label.bits.length ≤ 60 := fun i hi =>
  ComplJ8Walk.walkRows_len_le60 (canon_hwalk hpG hgen hc)
    (Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.wTrie_mem _ _ hi)

/-- **(f) path roots are cells of the table** (`roots_sorted`'s `hroot`, on the generator's read list). -/
theorem canon_hroot : ∀ x ∈ Nock.V1J8.Gen.pathReads (rowsOfT t), isPathAx x.2 = true →
    ∃ a b, x.1 = .cell a b ∧ Noun.cell a b ∈ (j8DataCanon p Rg Rt hgen).cells := by
  intro x hx _
  obtain ⟨-, -, hcell, hroot⟩ := canon_read hpG hgen hc hx
  cases h1 : x.1 with
  | atom _ => rw [h1] at hcell; simp [Noun.isCell] at hcell
  | cell a b =>
    rw [h1] at hroot
    exact ⟨a, b, rfl, (mem_cells_iff p Rg Rt hgen ord8Canon _).mpr
      (ComplJ8Of.mem_cellsOfRoots_of_root _ [] a b hroot)⟩

/-- **(f) the read roots are cells of the table** (`walkRoots_strict`'s `hmem`). -/
theorem canon_hmem : ∀ q ∈ walkRoots (j8DataCanon p Rg Rt hgen).reads, q ∈ (j8DataCanon p Rg Rt hgen).cells := by
  intro q hq
  simp only [walkRoots, pathKind, List.mem_dedup, List.mem_map, List.mem_filter] at hq
  obtain ⟨x, ⟨hx, hpk⟩, rfl⟩ := hq
  obtain ⟨a, b, h1, hm⟩ := canon_hroot hpG hgen hc x ((mem_reads_iff p Rg Rt hgen ord8Canon x).mp hx) hpk
  rw [h1]; exact hm

/-- **(f) the read roots are sorted by serial** (`walkRoots_strict`'s `hsort`, from `roots_sorted`). -/
theorem canon_hsort : ((pathKind (j8DataCanon p Rg Rt hgen).reads).map Prod.fst).Pairwise
    fun a b => (j8DataCanon p Rg Rt hgen).cells.idxOf a ≤ (j8DataCanon p Rg Rt hgen).cells.idxOf b :=
  roots_sorted p (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).acs
    (Nock.V1J8.Gen.pathReads (rowsOfT t)) (canon_hroot hpG hgen hc)

end Walk


/-! ## 5. The size bounds that are NOT run-side: bridges from the existing binders -/

section Sizes
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.Walk (bfsForest)
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl}
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **(d) from `hleaf`**: under the completeness binder `RootsLeafOK` (leaves `≤ 2^109`) every canonical cell has
rank `< 2^124`. (Not derivable from `P1FragC`: a fragment run can build intermediate nouns of exponential rank.) -/
theorem canon_hrk_of_leaf (hleaf : ComplJ8Walk.RootsLeafOK (j8DataCanon p Rg Rt hgen).roots) :
    ∀ x ∈ (j8DataCanon p Rg Rt hgen).cells, x.internal < 2 ^ 124 := by
  intro x hx
  obtain ⟨-, q, hq, hle⟩ := ComplJ8Walk.cellsOfRoots_mem _ x ((mem_cells_iff p Rg Rt hgen ord8Canon x).mp hx)
  have h1 := ComplJ8Walk.internal_lt_leaves q
  have h2 := hleaf q hq
  have : (2 : ℕ) ^ 109 < 2 ^ 124 := by norm_num
  omega

/-- **(c) `< p` from `hfit`**: the `SizesP1.hfit` input (`≤ 2^32`) gives fewer than `p` cells (Goldilocks). -/
theorem canon_hlen_of_fit (hpG : p = Nock.Atoms.p)
    (hfit : max (bfsForest [(j8DataCanon p Rg Rt hgen).t]).length (max (j8DataCanon p Rg Rt hgen).cells.length
      (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length) ≤ 2 ^ 32) :
    (j8DataCanon p Rg Rt hgen).cells.length < p := by
  have h := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hfit
  have hp := CellOrderP1.hp63_of hpG
  have : (2 : ℕ) ^ 32 < 2 ^ 63 := by norm_num
  omega

/-- **(c), (g) from `Rows31`**: the completeness binder `Rows31` (every table `≤ 2^31`) gives `hfit` and the
`≤ 2^31` cell bound. -/
theorem canon_fit_of_rows31 (h31 : ComplJ8Of.Rows31 (j8DataCanon p Rg Rt hgen)) :
    max (bfsForest [(j8DataCanon p Rg Rt hgen).t]).length (max (j8DataCanon p Rg Rt hgen).cells.length
      (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length) ≤ 2 ^ 32 ∧
    (j8DataCanon p Rg Rt hgen).cells.length ≤ 2 ^ 31 := by
  have hn := h31 (bfsForest [(j8DataCanon p Rg Rt hgen).t]).length (by simp [ComplJ8Of.sizesJ8])
  have hC : (j8DataCanon p Rg Rt hgen).cells.length ≤ 2 ^ 31 := h31 _ (by simp [ComplJ8Of.sizesJ8])
  have hW := h31 (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length
    (by simp [ComplJ8Of.sizesJ8])
  have : (2 : ℕ) ^ 31 ≤ 2 ^ 32 := by norm_num
  exact ⟨max_le (hn.trans this) (max_le (hC.trans this) (hW.trans this)), hC⟩

end Sizes

/-! ## 6. The `J = 0` swap -/

section JSwap
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.SVFrame (Coins)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 RowsJ8)
open Module Polynomial Nock.NockVMROM.Thm54.T0Tower
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **(h) At `nJ = 0` the predicate reads no J column**: any `tr.J` is accepted alike (as `absent_trV_free`). -/
theorem absent_trJ_free {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (h0 : Pb.nJ = 0) (J' : Fin 71 → (ZMod p)[X]) :
    AcceptsJ8V δ b Pb Rg c χ M { tr with J := J' } r g := by
  have hJ : Pb.nJ = 0 ∧ M.pubsJ 0 = 0 ∧ M.pubsJ 1 = 0 ∧ M.pubsJ 2 = 0 ∧ M.pubsJ 3 = 0 := by
    rcases h.hJk with ⟨-, -, -, hpos, -⟩ | h'
    · omega
    · exact h'
  exact { h with hJk := Or.inr hJ }

end JSwap

/-! ## 7. The honest round-0 atom trace at the pad table -/

section AtomPad
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Cell (cellRowBP cellRowB idRP idOf wOf aOf isBig)
open Nock.NockVMROM.Thm54.T0Tower
open Nock.V1J8.Gen (padN)

section Row
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **The pad row's cell part**: base column `j` (`2 ≤ j < 129`) of the cell row of `padN = [0 1]` at serial `0`,
no big atoms, zero multiplicities, is `padA j`. -/
theorem padRow_base (z : Quad (algebraMap F K δF)) (cs : List Noun) (mv mx mx1 : ℕ → ℕ) (pt : Noun → ℕ)
    (hmv : mv 0 = 0) (hmx : mx 0 = 0) (hmx1 : mx1 0 = 0) {j : ℕ} (h2 : 2 ≤ j) (hj : j < 129) :
    (cellRowBP δF z (fun _ => none) cs mv mx mx1 pt padN 0).base j = padA j := by
  by_cases h18 : j < 18
  · interval_cases j <;>
      simp [CellVals.base, cellRowBP, cellRowB, cellRow0, idRP, idOf, wOf, aOf, isBig, padN, hdN, tlN, padA,
        hmv, hmx, hmx1, Noun.internal, Noun.isCell]
  · by_cases h128 : j = 128
    · subst h128
      simp [CellVals.base, cellRowBP, cellRowB, padA, hmx1]
    · have hb : (cellRowBP δF z (fun _ => none) cs mv mx mx1 pt padN 0).base j =
          rankBit (rankOf padN) (j - 18) := by
        simp only [CellVals.base]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg h128]
        rfl
      rw [hb]
      have hr : rankOf padN = 1 := rfl
      rw [hr]
      unfold rankBit padA
      by_cases h0 : j = 18
      · subst h0; simp
      · have hk : j - 18 < 62 ∨ 62 ≤ j - 18 := by omega
        have hnot : j ∉ [0, 1, 8, 9, 18, 162, 194] := by simp; omega
        rw [if_neg hnot]
        rcases hk with hk | hk
        · rw [if_pos hk]
          have : Nat.testBit 1 (j - 18) = false := by
            obtain ⟨k, hk'⟩ : ∃ k, j - 18 = k + 1 := ⟨j - 19, by omega⟩
            rw [hk', Nat.testBit_succ]; simp
          simp [this]
        · rw [if_neg (by omega)]
          simp

end Row

section New
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom (AtomTab newOf bitF)
variable {F : Type} [Field F]

/-- **The pad row's added columns**: column `c` (`130 ≤ c < 205`) of a row with spine `[0, 1]`, no inc / conversion,
`mb = mi = 0`, is `padA c`. -/
theorem padTab_new (T : AtomTab) {n : ℕ} (i : Fin n) (hsp : T.sp i = [0, 1]) (hinc : T.inc i = false)
    (hconv : T.conv i = false) (hmb : T.mb i = 0) (hmi : T.mi i = 0) {c : ℕ} (h1 : 130 ≤ c) (h2 : c < 205) :
    newOf (F := F) (n := n) T.row c i = padA c := by
  have hrow : T.row i = ⟨i, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
    simp [AtomTab.row, hsp, hinc, hconv, hmb, hmi]
  unfold newOf
  rw [hrow]
  by_cases hc1 : c < 162
  · have hnot : c ∉ [0, 1, 8, 9, 18, 162, 194] := by simp; omega
    simp [hc1, bitF, padA, hnot]
  · by_cases hc2 : c < 194
    · by_cases h0 : c = 162
      · subst h0; simp [bitF, padA]
      · have hnot : c ∉ [0, 1, 8, 9, 18, 162, 194] := by simp; omega
        have : Nat.testBit 1 (c - 162) = false := by
          obtain ⟨k, hk'⟩ : ∃ k, c - 162 = k + 1 := ⟨c - 163, by omega⟩
          rw [hk', Nat.testBit_succ]; simp
        simp [hc1, hc2, bitF, padA, hnot, this]
    · interval_cases c <;> simp [padA]

end New

section Trace
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.SVFrame (Coins)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8)
open Module Polynomial
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl}
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- The filled cell row has the row's base columns. -/
theorem cellFill_base_eq {F K' : Type} [Field F] [Field K'] [Algebra F K'] [Fintype K'] (δF : F)
    [Fact (¬ IsSquare (algebraMap F K' δF))] (γ ρ : Quad (algebraMap F K' δF))
    (rows : ℕ → CellVals F (Quad (algebraMap F K' δF))) (k j : ℕ) :
    (cellFill δF γ ρ rows k).base j = (rows k).base j := rfl

theorem canon_incOps (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r))
    (hc : P1FragC ⟨s, f, r⟩) : incOpsP p (rowsOfT t) = [] := by
  unfold incOpsP
  simp only [List.map_eq_nil_iff, List.dedup_eq_nil]
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  have := st_p1 hpG hgen hc x hx
  simp only [stP1, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h | h | h | h | h | h <;> simp [h]

/-- **(a) the pad row's inc data**: no inc, no conversion, `mi = mhx = 0`. -/
theorem canon_info (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r))
    (hc : P1FragC ⟨s, f, r⟩) :
    (j8DataCanon p Rg Rt hgen).info.getD 0 Nock.V1J8.Gen.AInfo.z = Nock.V1J8.Gen.AInfo.z := by
  show (infoOfP p (j8DataCanon p Rg Rt hgen).acs (rowsOfT t)).getD 0 Nock.V1J8.Gen.AInfo.z = _
  unfold infoOfP
  rw [canon_incOps hpG hgen hc, canon_acs (Rt := Rt) hpG hgen hc]
  rfl

/-- **(a) the honest round-0 atom trace is the pad** (`CanonP1.hApad`): every round-0 atom column (`< 205`) of the
honest atom trace at the canonical data is the constant `padA j`. -/
theorem canon_trA (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩)
    (hA : 0 < (j8DataCanon p Rg Rt hgen).acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (j : Fin 349) (hj : (j : ℕ) < 205) :
    trAOf δ b (j8DataCanon p Rg Rt hgen) hA o χ j = C (padA (j : ℕ)) := by
  have hacs := canon_acs (Rt := Rt) hpG hgen hc
  have hlen : (j8DataCanon p Rg Rt hgen).acs.length = 1 := by rw [hacs]; rfl
  have hinfo := canon_info (Rt := Rt) hpG hgen hc
  have hmb := canon_mb (Rt := Rt) hpG hgen hc
  have hmx := canon_mxA (Rt := Rt) hpG hgen hc
  have key : ∀ i : Fin (j8DataCanon p Rg Rt hgen).acs.length,
      fullCol hA (HonestA8.colA δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b (j8DataCanon p Rg Rt hgen) hA o χ)
        (colAH δ b (j8DataCanon p Rg Rt hgen) hA o χ (pubsAOf δ b (j8DataCanon p Rg Rt hgen) hA o χ))
        (newBA (j8DataCanon p Rg Rt hgen))) j i = padA (j : ℕ) := by
    intro i
    have hi0 : (i : ℕ) = 0 := by have := i.isLt; omega
    by_cases h0 : (j : ℕ) = 0
    · simp [fullCol, h0, hi0, padA]
    by_cases h1 : (j : ℕ) = 1
    · have : i = ⟨(j8DataCanon p Rg Rt hgen).acs.length - 1, Nat.sub_lt hA (by omega)⟩ := Fin.ext (by simp; omega)
      simp [fullCol, h1, this, padA]
    simp only [fullCol, h0, h1, ↓reduceIte, HonestA8.colA, extColF]
    by_cases h130 : (j : ℕ) < 130
    · rw [if_pos h130]
      simp only [colAH, CellTraceHQ.colHQ, extColF]
      by_cases h129 : (j : ℕ) < 129
      · rw [if_pos h129]
        simp only [aCol, cellCol, if_pos h129, ComplJ8Cell.valsBP, cellFill_base_eq, ComplJ8Cell.cellRowsBP, hi0]
        have hg : (j8DataCanon p Rg Rt hgen).acs.getD 0 (.atom 0) = padN := by rw [hacs]; rfl
        rw [hg]
        refine padRow_base δ _ _ _ _ _ _ ?_ ?_ rfl (by omega) h129
        · simp [mvA, hacs, padN, Nock.V1J8.Gen.hdN', Nock.V1J8.Gen.tlN', Noun.isCell]
        · simp [mxAF, hmx.1]
      · have he : (j : ℕ) = 129 := by omega
        rw [if_neg h129, if_pos (by omega)]
        simp only [CellTraceHQ.new, he, ↓reduceIte, mhvA, mhAF, hi0, hmx.2, hinfo]
        simp [Nock.V1J8.Gen.AInfo.z, padA]
    · rw [if_neg h130, if_pos hj]
      simp only [HonestA8.newFull, if_pos (show (j : ℕ) < 313 by omega), newBA]
      refine padTab_new _ i ?_ ?_ ?_ ?_ ?_ (by omega) hj
      · simp only [ComplJ8Atom.tabOf, hi0]; rw [hacs]; rfl
      · simp only [ComplJ8Atom.tabOf, hi0, hinfo]; rfl
      · simp only [ComplJ8Atom.tabOf, hi0, hinfo]; rfl
      · simp only [ComplJ8Atom.tabOf, hi0, hmb]; rfl
      · simp only [ComplJ8Atom.tabOf, hi0, hinfo]; rfl
  unfold trAOf HonestA8.atomTraceHQ honestQ
  symm
  apply Lagrange.eq_interpolate_of_eval_eq
  · intro a _ a' _ _
    exact Fin.ext (by have := a.isLt; have := a'.isLt; omega)
  · rw [Finset.card_univ, Fintype.card_fin, hlen]
    exact lt_of_le_of_lt degree_C_le (by norm_num)
  · intro i _
    rw [eval_C, key i]

end Trace

end AtomPad

/-! ## 8. The run-side bundle -/

section Bundle
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK AxRowX Op5RowX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.V1J8.Gen (padN)
open Nock.Walk (bfsForest)
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl}
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}

/-- **The op-0 / op-10 / chain axes of a P1 run are small** (`hax`). -/
theorem canon_hax (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩) :
    ProgAxOK p t := by
  intro u hu
  obtain ⟨hs, hf, -⟩ := claim_bnd hpG hc
  have R := (p1_gen (p61_of hpG) hgen hc.ops hc.axes hs hf).2 u hu
  have hp61 := p61_of hpG
  obtain ⟨hb, hst, hrd⟩ := R
  unfold AxRowX
  cases hS : u.label.state <;> simp only [rowOfSkelX, hS, stP1, List.mem_cons, List.not_mem_nil, or_false,
    reduceCtorEq, or_self, false_or] at hb hst hrd ⊢
  · intro ax hax
    have := hb (tlN u.label.formula) (by simp [rowHandleNounsX])
    rw [hax] at this; exact this
  · intro ax hax
    have := hb (hdN (hdN (tlN u.label.formula))) (by simp [rowHandleNounsX])
    rw [hax] at this; exact this
  · intro a ha
    have := (hrd (u.label.subject, atomVal (.atom (chainAxis u.label.formula ^^^ 1)),
      sibX (chainAxis u.label.formula) u.label.subject) (by simp [consEntriesX])).1
    simp only [atomVal, ha, chainAxis] at this
    have hx := xor_one_eq a
    split_ifs at hx <;> omega

/-- **No op-5 rows** (`hop5`). -/
theorem canon_hop5 (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩) :
    ProgOp5OK p t := by
  intro u hu h5
  obtain ⟨hs, hf, -⟩ := claim_bnd hpG hc
  have := ((p1_gen (p61_of hpG) hgen hc.ops hc.axes hs hf).2 u hu).st
  rw [h5] at this
  simp [stP1] at this

/-- **No jet is called** (`hRt`, `hregAx` hold vacuously). -/
theorem canon_called (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩) :
    ∀ id, id ∉ CalledIds t := by
  rintro id ⟨u, hu, h11, -⟩
  obtain ⟨hs, hf, -⟩ := claim_bnd hpG hc
  have := ((p1_gen (p61_of hpG) hgen hc.ops hc.axes hs hf).2 u hu).st
  rw [h11] at this
  simp [stP1] at this

/-- **Every run-side hypothesis of `CanonGenP1` / `CanonWalkP1` / `CanonOrbP1` at the canonical data** (the honest
atom trace is `canon_trA`, stated over the coins separately). -/
structure RunP1 (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) : Prop where
  -- (a) the P1 constants
  calls : (j8DataCanon p Rg Rt hgen).calls = []
  regs : (j8DataCanon p Rg Rt hgen).regs = []
  jrows : (j8DataCanon p Rg Rt hgen).jrows = []
  bigs : (j8DataCanon p Rg Rt hgen).bigs = []
  acs : (j8DataCanon p Rg Rt hgen).acs = [padN]
  acs1 : (j8DataCanon p Rg Rt hgen).acs.length = 1
  preads : (j8DataCanon p Rg Rt hgen).preads = []
  vs : (j8DataCanon p Rg Rt hgen).vs = [] ∧ (j8DataCanon p Rg Rt hgen).krV = 0
  mxA : (j8DataCanon p Rg Rt hgen).mxA = Array.replicate 1 0 ∧ (j8DataCanon p Rg Rt hgen).mhA = Array.replicate 1 0
  mb : (j8DataCanon p Rg Rt hgen).mb = Array.replicate 1 0
  info : (j8DataCanon p Rg Rt hgen).info.getD 0 Nock.V1J8.Gen.AInfo.z = Nock.V1J8.Gen.AInfo.z
  -- the run binders of `complJ8_closed_canon`
  hax : ProgAxOK p t
  hop5 : ProgOp5OK p t
  hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p
  hcalled : ∀ id, id ∉ CalledIds t
  hleaf : ComplJ8Walk.RootsLeafOK (j8DataCanon p Rg Rt hgen).roots
  hwalk : ComplJ8Walk.WalkDepthOK (j8DataCanon p Rg Rt hgen).reads
  hwalkA : ComplJ8Walk.WalkDepthOK (j8DataCanon p Rg Rt hgen).preads
  h31 : ComplJ8Of.Rows31 (j8DataCanon p Rg Rt hgen)
  -- (b), (c), (d): the cell table (`canonM_cellTr`)
  hC : 0 < (j8DataCanon p Rg Rt hgen).cells.length
  hsmall : ∀ a b, Noun.cell a b ∈ (j8DataCanon p Rg Rt hgen).cells → ∀ v, (a = .atom v ∨ b = .atom v) → v < p
  hcs : (j8DataCanon p Rg Rt hgen).cells.Pairwise CellOrderP1.nlt
  hcell : ∀ x ∈ (j8DataCanon p Rg Rt hgen).cells, ∃ a b, x = .cell a b
  hch : ∀ a b, Noun.cell a b ∈ (j8DataCanon p Rg Rt hgen).cells →
    CanonGenP1.ChildOK p (j8DataCanon p Rg Rt hgen).cells a ∧ CanonGenP1.ChildOK p (j8DataCanon p Rg Rt hgen).cells b
  hnb : ∀ i (hi : i < (j8DataCanon p Rg Rt hgen).cells.length),
    ComplJ8Cell.isBig (bigIdOfP p (j8DataCanon p Rg Rt hgen).acs) (VclL.hdN (j8DataCanon p Rg Rt hgen).cells[i]) = false ∧
    ComplJ8Cell.isBig (bigIdOfP p (j8DataCanon p Rg Rt hgen).acs) (VclL.tlN (j8DataCanon p Rg Rt hgen).cells[i]) = false
  hlen : (j8DataCanon p Rg Rt hgen).cells.length < p
  hlen31 : (j8DataCanon p Rg Rt hgen).cells.length ≤ 2 ^ 31
  hrk : ∀ x ∈ (j8DataCanon p Rg Rt hgen).cells, x.internal < 2 ^ 124
  -- (g) the sizes (`szCanon`)
  hfit : max (bfsForest [(j8DataCanon p Rg Rt hgen).t]).length (max (j8DataCanon p Rg Rt hgen).cells.length
    (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length) ≤ 2 ^ 32
  hn31 : (bfsForest [(j8DataCanon p Rg Rt hgen).t]).length ≤ 2 ^ 31
  -- (e), (f): the walk (`honestW_cols`, `canonW_walkTr`, `roots_sorted`)
  hle : ∀ i < (walkRows (j8DataCanon p Rg Rt hgen).cells (j8DataCanon p Rg Rt hgen).reads).length,
    (Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.wTrie (j8DataCanon p Rg Rt hgen).cells
      (j8DataCanon p Rg Rt hgen).reads i).label.bits.length ≤ 60
  hroot : ∀ x ∈ Nock.V1J8.Gen.pathReads (rowsOfT t), Nock.NockVMROM.Thm54.VclL.isPathAx x.2 = true →
    ∃ a b, x.1 = .cell a b ∧ Noun.cell a b ∈ (j8DataCanon p Rg Rt hgen).cells
  hmem : ∀ q ∈ walkRoots (j8DataCanon p Rg Rt hgen).reads, q ∈ (j8DataCanon p Rg Rt hgen).cells
  hsort : ((pathKind (j8DataCanon p Rg Rt hgen).reads).map Prod.fst).Pairwise
    fun a b => (j8DataCanon p Rg Rt hgen).cells.idxOf a ≤ (j8DataCanon p Rg Rt hgen).cells.idxOf b

/-- **`canon_run_all`**: `P1FragC`, the run, Goldilocks and the two size binders (`Rows31`, `RootsLeafOK` at the
canonical data: the proposed `P1SizeOK`) give every run-side hypothesis. -/
theorem canon_run_all (hpG : p = Nock.Atoms.p) (hgen : genX Rg.R fuel s f = some (t, r)) (hc : P1FragC ⟨s, f, r⟩)
    (hR : ComplJ8Of.Rows31 (j8DataCanon p Rg Rt hgen))
    (hL : ComplJ8Walk.RootsLeafOK (j8DataCanon p Rg Rt hgen).roots) : RunP1 p Rg Rt hgen := by
  haveI : Fact (ringChar (ZMod p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
  have hcf := canon_cells_p1 (Rt := Rt) hpG hgen hc
  have hfit := canon_fit_of_rows31 hgen hR
  have hacs := canon_acs (Rt := Rt) hpG hgen hc
  obtain ⟨hs, hf, hr⟩ := claim_bnd hpG hc
  exact
  { calls := canon_calls hpG hgen hc
    regs := canon_regs hpG hgen hc
    jrows := canon_jrows hpG hgen hc
    bigs := canon_bigs hpG hgen hc
    acs := hacs
    acs1 := by rw [hacs]; rfl
    preads := canon_preads hpG hgen hc
    vs := canon_vs hpG hgen hc
    mxA := canon_mxA hpG hgen hc
    mb := canon_mb hpG hgen hc
    info := canon_info hpG hgen hc
    hax := canon_hax hpG hgen hc
    hop5 := canon_hop5 hpG hgen hc
    hclA := by
      intro k v hv
      have h := hc.small k v hv
      rw [← hpG] at h; exact h
    hcalled := canon_called hpG hgen hc
    hleaf := hL
    hwalk := canon_hwalk hpG hgen hc
    hwalkA := canon_hwalkA hpG hgen hc
    h31 := hR
    hC := cells_posG Rt hgen ord8Canon
    hsmall := canon_hsmall hpG hgen hc
    hcs := hcf.1
    hcell := hcf.2.1
    hch := hcf.2.2.1
    hnb := hcf.2.2.2
    hlen := canon_hlen_of_fit hgen hpG hfit.1
    hlen31 := hfit.2
    hrk := canon_hrk_of_leaf hgen hL
    hfit := hfit.1
    hn31 := hR _ (by simp [ComplJ8Of.sizesJ8])
    hle := canon_hle hpG hgen hc
    hroot := canon_hroot hpG hgen hc
    hmem := canon_hmem hpG hgen hc
    hsort := canon_hsort hpG hgen hc }

end Bundle

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.p1_gen
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.rows_p1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_calls
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_ids
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_regs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_jn
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_jrows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_roots_bnd
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_bigs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_dupP
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_acs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_preads
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_vs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_mxA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_mb
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hsmall
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_cells_p1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_read
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_reads_depth60
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hwalk
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hwalkA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hle
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hroot
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hmem
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hsort
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hrk_of_leaf
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hlen_of_fit
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_fit_of_rows31
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.absent_trJ_free
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.padRow_base
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.padTab_new
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_info
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_trA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hax
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_hop5
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_called
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonRunP1.canon_run_all
