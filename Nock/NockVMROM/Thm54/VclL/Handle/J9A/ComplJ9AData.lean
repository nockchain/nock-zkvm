/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AData.lean

* `axAtoms9 rows`: the op-0 / op-10 axis atoms of the `s0B` / `s10B` rows (first occurrence); `bigAx9 p`
    (`≥ p`: served by the axis chip through the atom table and the atom walk) and `fieldAx9 p` (`[2^62, p)`: one split row per distinct value, ids `nA + index`).
  * `limbAxes L`: the comb axes of the limbs of an `L`-limb atom (top limb at `2^L − 1`, limb `j < L − 1` at
    `2^(j+2) − 2`, `HonestPairX.recsA`'s layout), exactly the `walkRecA` consumes of an axis chain (`G2`: head
    `axK = pw − 1`, non-head `axK = pw − 2`, `pw` from `2^L` down to `4`) and of the `s10S` rows
    (`axL = hd·(pw − 1) + (1 − hd)·(2pw − 2)`, `pw = 2^(m+1)`).
  * `limbReads a`, `axReads9 p rows`: the atom-walk reads of the big axis atoms.
  * **`rowsOfT9_big_node`**: every `s0B` / `s10B` row of the J-9 A rows is the row of a node of `t`.
  * **`axAtoms9_cap`**: on a generated run, under the J-9 A binder `hax9 : ProgAxOK9A p t`, every axis atom is
    `≥ 2^62` and (`< p` or within the limb cap); **`bigAx9_cap`**: every big one is within the cap.
  * **`walkDepthOK_preads9`** (the atom-walk binder): J-9 B's `hwalkA : WalkDepthOK L` on the J-8
    pair reads `L` and the J-9 A binder `hax9` give `WalkDepthOK (L ++ axReads9 p (rowsOfT9 t))`.  So `hwalkA`
    does NOT itself mention the axis atoms' reads, but no new binder is needed: the cap already in `hax9`
    bounds their depth by `61`.  No statement is weakened.
  * `segReads`, `axChainReads9`: the axis chains' segment path reads on the cell walk (an `s0B` chain on its
    subject, an `s10B` chain on its result); **`walkDepthOK_axChainReads9`** (axes `< 2^33`, no binder) and
    **`walkDepthOK_reads9`**: the J-9 A cell-walk read list `walkReadsX9 ++ axChainReads9` from `hwalk9` alone.
  * **`bigAx9_sub_bigs`**: every big axis atom is already a big atom of the J-8 data `j8DataOf` (a leaf of its
    row's `ft` / `ftth` handle), so the J-9 A data keeps `DD.bigs` / `DD.acs` / the handle map.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AReads

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads (depthOf_le61)
open Nock.V1J8.Gen (combOf)
open Nock.J9A.NounAx (top segRd segRd_lt)

/-! ## 1. The axis atoms and the split values -/

/-- The axis atoms of the `s0B` / `s10B` rows (first occurrence). -/
def axAtoms9 (rows : Array LX9) : List ℕ :=
  ((rows.toList.filter fun l => decide (l.chip = .s0B) || decide (l.chip = .s10B)).map LX9.n).dedup

/-- The big axis atoms (`≥ p`): atom-table roots, served through the atom walk. -/
def bigAx9 (p : ℕ) (rows : Array LX9) : List ℕ := (axAtoms9 rows).filter fun a => decide (p ≤ a)

/-- The field axis atoms (`< p`, hence in `[2^62, p)`): one split row each, ids `nA + index`. -/
def fieldAx9 (p : ℕ) (rows : Array LX9) : List ℕ := (axAtoms9 rows).filter fun a => decide (a < p)

theorem axAtoms9_nodup (rows : Array LX9) : (axAtoms9 rows).Nodup := List.nodup_dedup _

theorem fieldAx9_nodup (p : ℕ) (rows : Array LX9) : (fieldAx9 p rows).Nodup :=
  (axAtoms9_nodup rows).filter _

theorem mem_axAtoms9 {rows : Array LX9} {a : ℕ} :
    a ∈ axAtoms9 rows ↔ ∃ l ∈ rows.toList, (l.chip = .s0B ∨ l.chip = .s10B) ∧ l.n = a := by
  simp only [axAtoms9, List.mem_dedup, List.mem_map, List.mem_filter, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨l, ⟨hl, hc⟩, rfl⟩; exact ⟨l, hl, hc, rfl⟩
  · rintro ⟨l, hl, hc, rfl⟩; exact ⟨l, ⟨hl, hc⟩, rfl⟩

/-! ## 2. The comb axes of the limbs and the atom-walk reads -/

/-- **The comb axes of an `L`-limb atom's limbs**: the top limb at `2^L − 1`, limb `j < L − 1` at `2^(j+2) − 2`. -/
def limbAxes (L : ℕ) : List ℕ := (2 ^ L - 1) :: (List.range (L - 1)).map fun j => 2 ^ (j + 2) - 2

/-- The atom-walk reads of one big axis atom (its comb, at every limb axis). -/
def limbReads (a : ℕ) : List (Noun × ℕ) :=
  (limbAxes (Nock.Atoms.limbs a).length).map fun x => (combOf (Nock.Atoms.limbs a), x)

/-- **The atom-walk reads of the big axis atoms.** -/
def axReads9 (p : ℕ) (rows : Array LX9) : List (Noun × ℕ) := (bigAx9 p rows).flatMap limbReads

theorem limbAxes_lt {L : ℕ} (hL : L ≤ 62) : ∀ x ∈ limbAxes L, x < 2 ^ 62 := by
  intro x hx
  simp only [limbAxes, List.mem_cons, List.mem_map, List.mem_range] at hx
  rcases hx with rfl | ⟨j, hj, rfl⟩
  · have : 2 ^ L ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hL
    have : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    omega
  · have : 2 ^ (j + 2) ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- `WalkDepthOK` from an axis bound `< 2^62`. -/
theorem walkDepthOK_of_lt {l : List (Noun × ℕ)} (h : ∀ x ∈ l, x.2 < 2 ^ 62) : ComplJ8Walk.WalkDepthOK l := by
  intro x hx
  simp only [pathReads, List.mem_dedup, List.mem_filter] at hx
  exact depthOf_le61 (h x hx.1)

theorem walkDepthOK_append {l l' : List (Noun × ℕ)} (h : ComplJ8Walk.WalkDepthOK l)
    (h' : ComplJ8Walk.WalkDepthOK l') : ComplJ8Walk.WalkDepthOK (l ++ l') := by
  intro x hx
  simp only [pathReads, List.mem_dedup, List.mem_filter, List.mem_append] at hx
  rcases hx with ⟨hx | hx, hp⟩
  · exact h x (by simp only [pathReads, List.mem_dedup, List.mem_filter]; exact ⟨hx, hp⟩)
  · exact h' x (by simp only [pathReads, List.mem_dedup, List.mem_filter]; exact ⟨hx, hp⟩)

/-- **The axis-atom reads are at depth `≤ 61` under the cap.** -/
theorem walkDepthOK_axReads9 {p : ℕ} {rows : Array LX9} (hcap : ∀ a ∈ bigAx9 p rows, AxCap a) :
    ComplJ8Walk.WalkDepthOK (axReads9 p rows) := by
  refine walkDepthOK_of_lt fun x hx => ?_
  simp only [axReads9, limbReads, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨a, ha, y, hy, rfl⟩ := hx
  exact limbAxes_lt (hcap a ha) y hy

/-! ## 3. The axis atoms of a generated run -/

section Run
variable {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}

/-- **Every `s0B` / `s10B` row of the J-9 A rows is the row of a node of `t`.** -/
theorem rowsOfT9_big_node (h : genX R n s f = some (t, r)) :
    ∀ l ∈ (rowsOfT9 t).toList, (l.chip = .s0B ∨ l.chip = .s10B) →
      ∃ v, InTree t v ∧ l.rn = rowOfSkelX v.label := by
  intro l hl hch
  simp only [rowsOfT9, List.toList_toArray, List.mem_map] at hl
  obtain ⟨u, hu, rfl⟩ := hl
  obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hu
  simp only [List.mem_singleton] at hc
  subst hc
  rcases genX9T_inTree h hcu with ⟨v, hv, -, rfl⟩ | ⟨v, -, -, rfl⟩ | ⟨n', m, s', e, new, -, -, -, rfl⟩ | ⟨X, Y, rfl⟩
  · exact ⟨v, hv, by rw [genX9T_label]⟩
  · rw [liftT_label] at hch; simp [liftL] at hch
  · rw [segT_label] at hch; simp at hch
  · simp [tNode] at hch

/-- **The axis atoms of a generated run under `hax9`**: `≥ 2^62`, and `< p` or within the cap. -/
theorem axAtoms9_cap (h : genX R n s f = some (t, r)) {p : ℕ} (hax9 : ProgAxOK9A p t) :
    ∀ a ∈ axAtoms9 (rowsOfT9 t), 2 ^ 62 ≤ a ∧ (a < p ∨ AxCap a) := by
  intro a ha
  obtain ⟨l, hl, hch, rfl⟩ := mem_axAtoms9.1 ha
  obtain ⟨v, hv, hrn⟩ := rowsOfT9_big_node h l hl hch
  have hsem := rowsOfT9_semN9 h l hl
  have hrow := hax9 v hv
  rw [← hrn] at hrow
  rcases hch with hc | hc
  · simp only [SemN9, hc] at hsem
    obtain ⟨-, hst, hft, hbig⟩ := hsem
    unfold AxRowX9A at hrow
    rw [hst] at hrow
    exact ⟨hbig, hrow _ hft⟩
  · simp only [SemN9, hc] at hsem
    obtain ⟨-, hst, hft, hbig⟩ := hsem
    unfold AxRowX9A at hrow
    rw [hst] at hrow
    exact ⟨hbig, hrow _ hft⟩

/-- **Every big axis atom is within the limb cap.** -/
theorem bigAx9_cap (h : genX R n s f = some (t, r)) {p : ℕ} (hax9 : ProgAxOK9A p t) :
    ∀ a ∈ bigAx9 p (rowsOfT9 t), AxCap a := by
  intro a ha
  simp only [bigAx9, List.mem_filter, decide_eq_true_eq] at ha
  rcases (axAtoms9_cap h hax9 a ha.1).2 with hlt | hc
  · omega
  · exact hc

/-- **Every field axis atom lies in `[2^62, p)`.** -/
theorem fieldAx9_range (h : genX R n s f = some (t, r)) {p : ℕ} (hax9 : ProgAxOK9A p t) :
    ∀ a ∈ fieldAx9 p (rowsOfT9 t), 2 ^ 62 ≤ a ∧ a < p := by
  intro a ha
  simp only [fieldAx9, List.mem_filter, decide_eq_true_eq] at ha
  exact ⟨(axAtoms9_cap h hax9 a ha.1).1, ha.2⟩

/-- **The atom-walk binder**: J-9 B's `hwalkA` on the J-8 pair reads `L`, plus the J-9 A binder
`hax9`, give `WalkDepthOK` on the J-9 A atom-walk reads `L ++ axReads9`.  No new binder. -/
theorem walkDepthOK_preads9 (h : genX R n s f = some (t, r)) {p : ℕ} (hax9 : ProgAxOK9A p t)
    {L : List (Noun × ℕ)} (hwalkA : ComplJ8Walk.WalkDepthOK L) :
    ComplJ8Walk.WalkDepthOK (L ++ axReads9 p (rowsOfT9 t)) :=
  walkDepthOK_append hwalkA (walkDepthOK_axReads9 (bigAx9_cap h hax9))

end Run

/-! ## 4. The axis chains' path reads (the cell walk side) -/

/-- **The segment reads of an axis-`n` chain on `s`, from segment `m` down**: `(X_m, segRd n m)` with `X_m = s`
and `X_(m-1) = /[segRd n m] X_m` (the axis chip's path consume `(hin.v, axS, hout.k, hout.v)` row by row, design
§2.1 G3/G5/G6; the same reads as the `s10S` pair, `ComplJ9AGen.segT`). -/
def segReads (n : ℕ) : ℕ → Noun → List (Noun × ℕ)
  | 0, s => [(s, segRd n 0)]
  | m + 1, s => (s, segRd n (m + 1)) :: segReads n m (segX n (m + 1) s)

/-- **The axis chains' path reads** (one chain per `s0B` row on its subject, per `s10B` row on its result; the
generator merges duplicates, `walkGen` is keyed by `(root, axis)`), axis `≥ 2` (axis `1` is never served: `G4`). -/
def axChainReads9 (rows : Array LX9) : List (Noun × ℕ) :=
  (rows.toList.flatMap fun l =>
    if l.chip = .s0B then segReads l.n (top l.n) l.rn.s
    else if l.chip = .s10B then segReads l.n (top l.n) l.rn.e
    else []).filter fun q => 2 ≤ q.2

theorem segReads_lt (n : ℕ) : ∀ (m : ℕ) (s : Noun), ∀ x ∈ segReads n m s, x.2 < 2 ^ 33 := by
  intro m
  induction m with
  | zero => intro s x hx; simp only [segReads, List.mem_singleton] at hx; subst hx; exact segRd_lt n 0
  | succ m ih =>
    intro s x hx
    simp only [segReads, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact segRd_lt n (m + 1)
    · exact ih _ x hx

/-- **The axis chains' path reads are at depth `≤ 32`**, hence within the walk's `61` (no binder). -/
theorem walkDepthOK_axChainReads9 (rows : Array LX9) : ComplJ8Walk.WalkDepthOK (axChainReads9 rows) := by
  refine walkDepthOK_of_lt fun x hx => ?_
  simp only [axChainReads9, List.mem_filter, List.mem_flatMap] at hx
  obtain ⟨⟨l, -, hl⟩, -⟩ := hx
  have h33 : (2 : ℕ) ^ 33 < 2 ^ 62 := by norm_num
  split_ifs at hl
  · exact lt_trans (segReads_lt _ _ _ x hl) h33
  · exact lt_trans (segReads_lt _ _ _ x hl) h33
  · simp at hl

/-- **The J-9 A cell-walk read list** (`walkReadsX9`: J-8's routed reads and the `s10S` pairs, plus the axis
chains' segment reads) satisfies `WalkDepthOK` from the J-9 A binder `hwalk9` alone. -/
theorem walkDepthOK_reads9 {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t)) :
    ComplJ8Walk.WalkDepthOK (ComplJ9AReads.walkReadsX9 (rowsOfT9 t) ++ axChainReads9 (rowsOfT9 t)) :=
  walkDepthOK_append (ComplJ9AReads.walkDepthOK_X9 h hwalk9) (walkDepthOK_axChainReads9 _)

/-! ## 5. The big axis atoms are J-8 big atoms (data plan option B keeps `DD.bigs`) -/

section Bigs
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **Every big axis atom is already a big atom of the J-8 data** (a leaf of its row's `ft` / `ftth` handle), so
the J-9 A data keeps `DD.bigs`, `DD.acs` and the handle map. -/
theorem bigAx9_sub_bigs : ∀ a ∈ bigAx9 p (rowsOfT9 t), a ∈ (ComplJ8Data.j8DataOf p Rg Rt hgen).bigs := by
  intro a ha
  simp only [bigAx9, List.mem_filter, decide_eq_true_eq] at ha
  obtain ⟨l, hl, hch, rfl⟩ := mem_axAtoms9.1 ha.1
  obtain ⟨v, hv, hrn⟩ := rowsOfT9_big_node hgen l hl hch
  have hsem := rowsOfT9_semN9 hgen l hl
  have hmem : rowOfSkelX v.label ∈ (ComplJ8Data.rowsOfT t).toList := ComplJ9AReads.rowOfSkelX_mem_rowsOfT hv
  have hleaf : l.n ∈ (rowOfSkelX v.label).ft.leafList ∨ l.n ∈ (rowOfSkelX v.label).ftth.leafList := by
    rcases hch with hc | hc
    · simp only [SemN9, hc] at hsem
      left; rw [← hrn, hsem.2.2.1]; simp [Noun.leafList]
    · simp only [SemN9, hc] at hsem
      right; rw [← hrn, hsem.2.2.1]; simp [Noun.leafList]
  have hx : ∃ x, x ∈ rowHandleNounsX (rowOfSkelX v.label) ∧ l.n ∈ leavesOf x := by
    rcases hleaf with h1 | h1
    · exact ⟨(rowOfSkelX v.label).ft, by simp [rowHandleNounsX], by rw [ComplJ9BOf.leavesOf_eq]; exact h1⟩
    · exact ⟨(rowOfSkelX v.label).ftth, by simp [rowHandleNounsX], by rw [ComplJ9BOf.leavesOf_eq]; exact h1⟩
  obtain ⟨x, hx1, hx2⟩ := hx
  show l.n ∈ ComplJ8Data.bigsP p _ (ComplJ8Data.rowsOfT t)
  rw [ComplJ8Data.bigsP, List.mem_mergeSort, List.mem_dedup, List.mem_filter]
  refine ⟨List.mem_flatMap.2 ⟨x, List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hmem, hx1⟩), hx2⟩, ?_⟩
  simpa using ha.2

end Bigs

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData
#print axioms walkDepthOK_axReads9
#print axioms rowsOfT9_big_node
#print axioms axAtoms9_cap
#print axioms bigAx9_cap
#print axioms fieldAx9_range
#print axioms walkDepthOK_preads9
#print axioms walkDepthOK_axChainReads9
#print axioms walkDepthOK_reads9
#print axioms bigAx9_sub_bigs
end Axioms
