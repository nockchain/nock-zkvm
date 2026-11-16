/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemReq.lean

  **`honestReq` is the sum of `den⁻¹` over the honest requests.**

  `HonestVCL.req` / `.msg2` are DEFINED as the four accumulator terminals.  Here they are shown to be the
  `Σ den⁻¹` over the honest compute requests of the demand `d` (the memory side's request records):
  * export: the depth-1 compute lookups with their side (`shallowSided`, `xReqs`);
  * path-provide: the deep reads `(root, axis)` (`pReqs`), at their slot (`hslot`).
  The proof regroups the cell table's validity / export terminals by the consumer counts (`mv`, `mx0`, `mx1`) and
  the path table's terminals by chain rows, through `perm_expand_count` (`List.Perm.sum_eq`) and the sided split
  (`xs_count_add`); the export balance `Σ_{xs0,xs1} = Σ_{path pxKey consumes} + Σ_{shallow}` is
  `export_side_balance`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemHonest

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Generic regrouping lemmas -/

section Generic

/-- `Σ_{a ∈ S} count a L • f a = Σ_{x ∈ L} f x` for a nodup `S ⊇ L`. -/
theorem sum_count_nsmul {α M : Type*} [DecidableEq α] [AddCommMonoid M] (S L : List α) (f : α → M)
    (hS : S.Nodup) (hL : ∀ x ∈ L, x ∈ S) :
    (S.map fun a => L.count a • f a).sum = (L.map f).sum := by
  have h1 : (L.map f).sum = ∑ a ∈ L.toFinset, L.count a • f a := by
    have := Finset.sum_multiset_map_count (↑L : Multiset α) f
    simpa [Multiset.map_coe, Multiset.sum_coe] using this
  rw [h1, ← List.sum_toFinset _ hS]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro a ha; exact List.mem_toFinset.mpr (hL a (List.mem_toFinset.mp ha))
  · intro a _ ha
    have : L.count a = 0 := List.count_eq_zero.mpr fun h => ha (List.mem_toFinset.mpr h)
    simp [this]

/-- `Σ_{i<len} f (l.getD i d) = Σ_{x ∈ l} f x`. -/
theorem sum_range_getD {α M : Type*} [AddCommMonoid M] (l : List α) (d : α) (f : α → M) :
    ∑ k ∈ Finset.range l.length, f (l.getD k d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons, ih]
    abel

theorem sum_range_list {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- Splitting a sided list by side. -/
theorem sum_sided_split {M : Type*} [AddCommMonoid M] (L : List (Noun × Bool)) (g : Noun → Bool → M) :
    (L.map fun c => g c.1 c.2).sum =
      (((L.filter fun c => !c.2).map Prod.fst).map fun n => g n false).sum +
      (((L.filter fun c => c.2).map Prod.fst).map fun n => g n true).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
    obtain ⟨m, b⟩ := c
    cases b <;> simp [ih] <;> abel

end Generic

/-! ## 2. The honest request records and the cell-table terminals -/

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- `den⁻¹` of a record at the IO coins `(γ, ρ)`. -/
def cinv {m : ℕ} (γ ρ : Quad (algebraMap F K δF)) (v : Fin m → Quad (algebraMap F K δF)) :
    Quad (algebraMap F K δF) := (FiniteIO.compress (m := m) ⟨γ, ρ⟩ v)⁻¹

/-- **The validity request record of the cell `n`**: `(fn n, rank lo, rank hi, serial)`. -/
def vReq (z : Quad (algebraMap F K δF)) (cells : List Noun) (n : Noun) :
    Fin 5 → Quad (algebraMap F K δF) :=
  ![(GlobalCarryRecognizer.enc z n).size, (GlobalCarryRecognizer.enc z n).dyck,
    (GlobalCarryRecognizer.enc z n).leaf,
    Quad.mk _ (algebraMap F K ((rankOf n % 2 ^ 62 : ℕ) : F)) (algebraMap F K ((rankOf n / 2 ^ 62 : ℕ) : F)),
    liftQ δF (cells.idxOf n : F)]

/-- **The export request record of the cell `n` at side `b`**: `(fn n, fn hd, fn tl, serial, side)`. -/
def xReq (z : Quad (algebraMap F K δF)) (cells : List Noun) (n : Noun) (b : Bool) :
    Fin 11 → Quad (algebraMap F K δF) :=
  ![(GlobalCarryRecognizer.enc z n).size, (GlobalCarryRecognizer.enc z n).dyck,
    (GlobalCarryRecognizer.enc z n).leaf,
    (GlobalCarryRecognizer.enc z (hdN n)).size, (GlobalCarryRecognizer.enc z (hdN n)).dyck,
    (GlobalCarryRecognizer.enc z (hdN n)).leaf,
    (GlobalCarryRecognizer.enc z (tlN n)).size, (GlobalCarryRecognizer.enc z (tlN n)).dyck,
    (GlobalCarryRecognizer.enc z (tlN n)).leaf,
    liftQ δF (cells.idxOf n : F), liftQ δF (if b then (1 : F) else 0)]

/-- **The path-provide request record of the read `(root, axis)`**: `(fn root, fn child, axis, root serial)`
with `child` the slot read. -/
def pReq (z : Quad (algebraMap F K δF)) (cells : List Noun) (r : Noun × ℕ) :
    Fin 8 → Quad (algebraMap F K δF) :=
  ![(GlobalCarryRecognizer.enc z r.1).size, (GlobalCarryRecognizer.enc z r.1).dyck,
    (GlobalCarryRecognizer.enc z r.1).leaf,
    (GlobalCarryRecognizer.enc z ((Noun.slot r.2 r.1).getD (.atom 0))).size,
    (GlobalCarryRecognizer.enc z ((Noun.slot r.2 r.1).getD (.atom 0))).dyck,
    (GlobalCarryRecognizer.enc z ((Noun.slot r.2 r.1).getD (.atom 0))).leaf,
    liftQ δF (r.2 : F), liftQ δF (cells.idxOf r.1 : F)]

variable {δF}
variable (γ ρ z : Quad (algebraMap F K δF)) (cells vcs xs0 xs1 : List Noun)

theorem vKeyOf_cellRow0 (n : Noun) : vKeyOf δF (cellRow0 δF z cells vcs xs0 xs1 n) = vReq δF z cells n := rfl

theorem xKeyOf_cellRow0 (n : Noun) (b : Bool) :
    xKeyOf δF (cellRow0 δF z cells vcs xs0 xs1 n) (if b then 1 else 0) = xReq δF z cells n b := rfl

theorem lKeyOf_cellRow0 (a b : Noun) (ha : a.isCell = true) :
    lKeyOf δF (cellRow0 δF z cells vcs xs0 xs1 (.cell a b)) = vReq δF z cells a := by
  cases a with
  | atom _ => simp [Noun.isCell] at ha
  | cell x y => rfl

theorem rKeyOf_cellRow0 (a b : Noun) (hb : b.isCell = true) :
    rKeyOf δF (cellRow0 δF z cells vcs xs0 xs1 (.cell a b)) = vReq δF z cells b := by
  cases b with
  | atom _ => simp [Noun.isCell] at hb
  | cell x y => rfl

theorem lInv_cellRow0 (a b : Noun) :
    (cellFillInv δF γ ρ (cellRow0 δF z cells vcs xs0 xs1 (.cell a b))).lInv =
      ((selfCell a).map fun c => cinv δF γ ρ (vReq δF z cells c)).sum := by
  cases a with
  | atom v => simp [cellFillInv, cellRow0, hdN, selfCell, Noun.isCell, liftQ]
  | cell x y =>
    have := lKeyOf_cellRow0 z cells vcs xs0 xs1 (.cell x y) b rfl
    simp only [cellFillInv, this, selfCell, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, cinv]
    simp [cellRow0, hdN, Noun.isCell, liftQ]

theorem rInv_cellRow0 (a b : Noun) :
    (cellFillInv δF γ ρ (cellRow0 δF z cells vcs xs0 xs1 (.cell a b))).rInv =
      ((selfCell b).map fun c => cinv δF γ ρ (vReq δF z cells c)).sum := by
  cases b with
  | atom v => simp [cellFillInv, cellRow0, tlN, selfCell, Noun.isCell, liftQ]
  | cell x y =>
    have := rKeyOf_cellRow0 z cells vcs xs0 xs1 a (.cell x y) rfl
    simp only [cellFillInv, this, selfCell, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, cinv]
    simp [cellRow0, tlN, Noun.isCell, liftQ]

/-- **One cell's validity term**: `mv·den(v)⁻¹ − (den(l)⁻¹ + den(r)⁻¹)` is `count · cinv(vReq n)` minus the sum
over its cell children. -/
theorem vTerm_cellRow0 (a b : Noun) :
    vTermOf δF (cellFillInv δF γ ρ (cellRow0 δF z cells vcs xs0 xs1 (.cell a b))) =
      vcs.count (.cell a b) • cinv δF γ ρ (vReq δF z cells (.cell a b)) -
        ((childCells (.cell a b)).map fun c => cinv δF γ ρ (vReq δF z cells c)).sum := by
  unfold vTermOf
  rw [lInv_cellRow0, rInv_cellRow0]
  simp only [childCells, List.map_append, List.sum_append, nsmul_eq_mul, sub_add_eq_sub_sub]
  have : liftQ δF (cellFillInv δF γ ρ (cellRow0 δF z cells vcs xs0 xs1 (.cell a b))).mv = ((vcs.count (.cell a b) : ℕ) : Quad (algebraMap F K δF)) := by
    simp [cellFillInv, cellRow0, liftQ]
  rw [this]
  rfl

/-- One cell's export term: `mx0 · den(x, side 0)⁻¹ + mx1 · den(x, side 1)⁻¹`. -/
theorem xTerm_cellRow0 (n : Noun) :
    xTermOf δF (cellFillInv δF γ ρ (cellRow0 δF z cells vcs xs0 xs1 n)) =
      xs0.count n • cinv δF γ ρ (xReq δF z cells n false) +
        xs1.count n • cinv δF γ ρ (xReq δF z cells n true) := by
  unfold xTermOf
  simp only [nsmul_eq_mul]
  have h0 : (cellFillInv δF γ ρ (cellRow0 δF z cells vcs xs0 xs1 n)).x0Inv =
      cinv δF γ ρ (xReq δF z cells n false) := rfl
  have h1 : (cellFillInv δF γ ρ (cellRow0 δF z cells vcs xs0 xs1 n)).x1Inv =
      cinv δF γ ρ (xReq δF z cells n true) := rfl
  rw [h0, h1]
  simp [cellFillInv, cellRow0, liftQ]

theorem sum_flatMap_map {α β M : Type*} [AddCommMonoid M] (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem sum_map_sub' {α M : Type*} [AddCommGroup M] (l : List α) (f g : α → M) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; abel

/-- **The validity terminal is the sum over the bound cells.**  `Σ_k vTerm = Σ_{b ∈ binds} cinv(vReq b)`: the
cell table's provides (`mv · inv_v`) regroup (by the consumer counts) into the consumers `vcs`, the child
consumptions cancel the `inv_L + inv_R`, and the root bindings remain. -/
theorem cell_vTotal (cells binds xs0 xs1 : List Noun)
    (hnd : cells.Nodup) (hcell : ∀ n ∈ cells, n.isCell = true)
    (hclosed : ∀ n ∈ cells, ∀ c ∈ childCells n, c ∈ cells)
    (hbind : ∀ b ∈ binds.flatMap selfCell, b ∈ cells) :
    ∑ k ∈ Finset.range cells.length,
      vTermOf δF (cellFillInv δF γ ρ (cellRows0 δF z cells (vcsOf cells binds) xs0 xs1 k)) =
    ((binds.flatMap selfCell).map fun c => cinv δF γ ρ (vReq δF z cells c)).sum := by
  have h1 := sum_range_getD cells (.atom 0) fun n =>
    vTermOf δF (cellFillInv δF γ ρ (cellRow0 δF z cells (vcsOf cells binds) xs0 xs1 n))
  refine (h1.trans ?_)
  have h2 : (cells.map fun n =>
      vTermOf δF (cellFillInv δF γ ρ (cellRow0 δF z cells (vcsOf cells binds) xs0 xs1 n))) =
      cells.map fun n => (vcsOf cells binds).count n • cinv δF γ ρ (vReq δF z cells n) -
        ((childCells n).map fun c => cinv δF γ ρ (vReq δF z cells c)).sum := by
    refine List.map_congr_left fun n hn => ?_
    have := hcell n hn
    cases n with
    | atom _ => simp [Noun.isCell] at this
    | cell a b => exact vTerm_cellRow0 γ ρ z cells _ xs0 xs1 a b
  rw [h2, sum_map_sub']
  have hsub : ∀ c ∈ vcsOf cells binds, c ∈ cells := by
    intro c hc
    simp only [vcsOf, List.mem_append, List.mem_flatMap] at hc
    rcases hc with ⟨n, hn, hcn⟩ | h
    · exact hclosed n hn c hcn
    · exact hbind c (List.mem_flatMap.mpr h)
  rw [sum_count_nsmul cells _ (fun n => cinv δF γ ρ (vReq δF z cells n)) hnd hsub]
  simp only [vcsOf, List.map_append, List.sum_append, sum_flatMap_map]
  abel

/-- **The export terminal**: `Σ_k xTerm = Σ_{xs0} cinv(xReq · false) + Σ_{xs1} cinv(xReq · true)`. -/
theorem cell_xTotal (cells vcs xs0 xs1 : List Noun) (hnd : cells.Nodup)
    (h0 : ∀ c ∈ xs0, c ∈ cells) (h1 : ∀ c ∈ xs1, c ∈ cells) :
    ∑ k ∈ Finset.range cells.length,
      xTermOf δF (cellFillInv δF γ ρ (cellRows0 δF z cells vcs xs0 xs1 k)) =
    (xs0.map fun c => cinv δF γ ρ (xReq δF z cells c false)).sum +
      (xs1.map fun c => cinv δF γ ρ (xReq δF z cells c true)).sum := by
  have h := sum_range_getD cells (.atom 0) fun n =>
    xTermOf δF (cellFillInv δF γ ρ (cellRow0 δF z cells vcs xs0 xs1 n))
  refine h.trans ?_
  simp only [xTerm_cellRow0, List.sum_map_add, ]
  rw [sum_count_nsmul cells _ (fun n => cinv δF γ ρ (xReq δF z cells n false)) hnd h0,
    sum_count_nsmul cells _ (fun n => cinv δF γ ρ (xReq δF z cells n true)) hnd h1]

end Cell

/-! ## 3. The path-table terminals -/

section PathReq
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))]
variable (γ ρ z : Quad (algebraMap F K δF)) (cells : List Noun)

/-- A chain row's consume key is the export request of its step. -/
theorem pxKeyOf_chainRow (root : Noun) (mult : ℕ) (steps : List (Noun × Bool)) (k : ℕ) :
    pxKeyOf δF (chainRow δF z cells root mult steps k) =
      xReq δF z cells (steps.getD k (.atom 0, false)).1 (steps.getD k (.atom 0, false)).2 := rfl

/-- **The path-consume total is the sum over the path edges**: `y = Σ_{edges} cinv(xReq)`. -/
theorem path_yTotal (preads : List (Noun × ℕ)) :
    ∑ k ∈ Finset.range (pathTable δF z cells preads).length,
      (pathFillInv δF γ ρ ((pathTable δF z cells preads).getD k
        (chainRow δF z cells (.atom 0) 0 [] 0))).xConsInv =
    ((edgeSided preads).map fun c => cinv δF γ ρ (xReq δF z cells c.1 c.2)).sum := by
  have h := sum_range_getD (pathTable δF z cells preads) (chainRow δF z cells (.atom 0) 0 [] 0)
    fun x => (pathFillInv δF γ ρ x).xConsInv
  refine h.trans ?_
  unfold pathTable edgeSided
  rw [sum_flatMap_map, sum_flatMap_map]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  unfold chainRows
  rw [List.map_map, sum_range_list,
    ← sum_range_getD (pathSteps r.1 (axisBits r.2)) (.atom 0, false)
      fun c => cinv δF γ ρ (xReq δF z cells c.1 c.2)]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- The consume total of one chain's rows is the sum over its steps. -/
theorem chainRows_xSum (root : Noun) (mult : ℕ) (steps : List (Noun × Bool)) :
    ((chainRows δF z cells root mult steps).map fun x => (pathFillInv δF γ ρ x).xConsInv).sum =
      (steps.map fun c => cinv δF γ ρ (xReq δF z cells c.1 c.2)).sum := by
  unfold chainRows
  rw [List.map_map, sum_range_list,
    ← sum_range_getD steps (.atom 0, false) fun c => cinv δF γ ρ (xReq δF z cells c.1 c.2)]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- **`path_yTotal` with the padding chain**: `y = Σ_{padded edges} cinv(xReq)`. -/
theorem path_yTotalP (preads : List (Noun × ℕ)) :
    ∑ k ∈ Finset.range (pathTableP δF z cells preads).length,
      (pathFillInv δF γ ρ ((pathTableP δF z cells preads).getD k
        (chainRow δF z cells (.atom 0) 0 [] 0))).xConsInv =
    ((edgeSidedP cells preads).map fun c => cinv δF γ ρ (xReq δF z cells c.1 c.2)).sum := by
  have h := sum_range_getD (pathTableP δF z cells preads) (chainRow δF z cells (.atom 0) 0 [] 0)
    fun x => (pathFillInv δF γ ρ x).xConsInv
  refine h.trans ?_
  have h0 := (sum_range_getD (pathTable δF z cells preads) (chainRow δF z cells (.atom 0) 0 [] 0)
    fun x => (pathFillInv δF γ ρ x).xConsInv).symm.trans (path_yTotal (δF := δF) γ ρ z cells preads)
  unfold pathTableP edgeSidedP
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append, h0,
    chainRows_xSum γ ρ z cells]

/-- The last step of a completed chain consumes the cell whose `side` child is the read's value. -/
theorem pathSteps_last : ∀ (bits : List Bool) (root child : Noun), chainWalk root bits = some child →
    bits ≠ [] → ∃ (pre : List (Noun × Bool)) (p : Noun) (b : Bool),
      pathSteps root bits = pre ++ [(p, b)] ∧ (if b then tlN p else hdN p) = child
  | [], _, _, _, h => absurd rfl h
  | [b], .cell l r, child, hw, _ => by
    simp only [chainWalk, chainWalk] at hw
    exact ⟨[], .cell l r, b, by simp [pathSteps], by cases b <;> simp_all [hdN, tlN]⟩
  | b :: b' :: bs, .cell l r, child, hw, _ => by
    simp only [chainWalk] at hw
    obtain ⟨pre, p, c, h1, h2⟩ := pathSteps_last (b' :: bs) (if b then r else l) child hw (by simp)
    exact ⟨(.cell l r, b) :: pre, p, c, by simp [pathSteps, h1], h2⟩
  | _ :: _, .atom _, _, hw, _ => by simp [chainWalk] at hw

/-- The `childOf` of a path row is the fingerprint of the `side` child. -/
theorem childOf_chainRow_last (root : Noun) (mult : ℕ) (steps : List (Noun × Bool)) (k : ℕ)
    (p : Noun) (b : Bool) (hk : steps.getD k (.atom 0, false) = (p, b)) :
    childOf δF (chainRow δF z cells root mult steps k) =
      GlobalCarryRecognizer.enc z (if b then tlN p else hdN p) := by
  unfold childOf chainRow
  dsimp only
  rw [hk]
  cases b <;> simp [liftQ] <;> rfl

/-- **The last row of the chain of a defined deep read provides the slot record.** -/
theorem pRecOf_chain_last (root : Noun) (a : ℕ) (mult : ℕ) (child : Noun) (ha : 1 ≤ a)
    (hne : axisBits a ≠ []) (hw : chainWalk root (axisBits a) = some child) :
    pRecOf δF (chainRow δF z cells root mult (pathSteps root (axisBits a))
      ((pathSteps root (axisBits a)).length - 1)) = pReq δF z cells (root, a) := by
  obtain ⟨pre, p, b, hst, hc⟩ := pathSteps_last _ root child hw hne
  have hslot : (Noun.slot a root).getD (.atom 0) = child := by
    rw [slot_eq_chainWalk a ha, hw]; rfl
  have hk : (pathSteps root (axisBits a)).getD ((pathSteps root (axisBits a)).length - 1) (.atom 0, false)
      = (p, b) := by
    rw [hst]; simp [List.getD_eq_getElem?_getD]
  have hsides := pathSteps_sides root (axisBits a) (by rw [hw]; rfl)
  have hlen : ((pathSteps root (axisBits a)).map Prod.snd).take
      ((pathSteps root (axisBits a)).length - 1 + 1) = axisBits a := by
    rw [hsides]
    have : (pathSteps root (axisBits a)).length = (axisBits a).length := by
      simpa using congrArg List.length hsides
    rw [this, Nat.sub_add_cancel (List.length_pos_of_ne_nil hne)]
    exact List.take_length
  have hacc : axisFold (((pathSteps root (axisBits a)).map Prod.snd).take
      ((pathSteps root (axisBits a)).length - 1 + 1)) = a := by
    rw [hlen]; exact axisFold_axisBits a ha
  have hch := childOf_chainRow_last z cells root mult (pathSteps root (axisBits a)) _ p b hk
  have hacc' : (chainRow δF z cells root mult (pathSteps root (axisBits a))
      ((pathSteps root (axisBits a)).length - 1)).acc = (a : F) := by
    show ((axisFold _ : ℕ) : F) = _
    rw [hacc]
  unfold pRecOf pReq
  rw [hch, hacc', hc, hslot]
  rfl

/-- The number of path rows does not depend on the seed. -/
theorem pathTable_length_seed (z z' : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) :
    (pathTable δF z cells preads).length = (pathTable δF z' cells preads).length := by
  simp [pathTable, List.length_flatMap, chainRows_length]

theorem deep_facts {preads : List (Noun × ℕ)} {r : Noun × ℕ} (hr : r ∈ pathReads preads)
    (hslot : (Noun.slot r.2 r.1).isSome) :
    1 ≤ r.2 ∧ axisBits r.2 ≠ [] ∧ ∃ child, chainWalk r.1 (axisBits r.2) = some child := by
  simp only [pathReads, List.mem_dedup, List.mem_filter, isPathAx, decide_eq_true_eq, depthOf] at hr
  have h2 := hr.2
  have ha : 1 ≤ r.2 := by
    by_contra h
    have : r.2 = 0 := by omega
    rw [this] at h2
    simp [axisBits, axisBitsAux] at h2
  refine ⟨ha, fun h => by rw [h] at h2; simp at h2, ?_⟩
  rw [slot_eq_chainWalk r.2 ha] at hslot
  exact Option.isSome_iff_exists.mp hslot

/-- **The path-provide total is the sum over the path reads**: `Σ_k m·pProvInv = Σ_{path reads} cinv(pReq)`. -/
theorem path_pTotal (preads : List (Noun × ℕ))
    (hslot : ∀ r ∈ pathReads preads, (Noun.slot r.2 r.1).isSome) :
    ∑ k ∈ Finset.range (pathTable δF z cells preads).length,
      liftQ δF ((pathTable δF z cells preads).getD k (chainRow δF z cells (.atom 0) 0 [] 0)).m *
        (pathFillInv δF γ ρ ((pathTable δF z cells preads).getD k
          (chainRow δF z cells (.atom 0) 0 [] 0))).pProvInv =
    (((preads.filter fun r => isPathAx r.2)).map fun r => cinv δF γ ρ (pReq δF z cells r)).sum := by
  have h := sum_range_getD (pathTable δF z cells preads) (chainRow δF z cells (.atom 0) 0 [] 0)
    fun x => liftQ δF x.m * (pathFillInv δF γ ρ x).pProvInv
  refine h.trans ?_
  unfold pathTable
  rw [sum_flatMap_map]
  have hper : ∀ r ∈ pathReads preads,
      ((chainRows δF z cells r.1 (preads.count r) (pathSteps r.1 (axisBits r.2))).map
        fun x => liftQ δF x.m * (pathFillInv δF γ ρ x).pProvInv).sum =
      preads.count r • cinv δF γ ρ (pReq δF z cells r) := by
    intro r hr
    obtain ⟨ha, hne, child, hw⟩ := deep_facts hr (hslot r hr)
    have hlen : (pathSteps r.1 (axisBits r.2)).length = (axisBits r.2).length := by
      simpa using congrArg List.length (pathSteps_sides r.1 _ (by rw [hw]; rfl))
    have hpos : 0 < (pathSteps r.1 (axisBits r.2)).length := by
      rw [hlen]; exact List.length_pos_of_ne_nil hne
    unfold chainRows
    rw [List.map_map, sum_range_list]
    rw [Finset.sum_eq_single ((pathSteps r.1 (axisBits r.2)).length - 1)]
    · have := pRecOf_chain_last z cells r.1 r.2 (preads.count r) child ha hne hw
      simp only [Function.comp, pathFillInv, cinv]
      have hm : (chainRow δF z cells r.1 (preads.count r) (pathSteps r.1 (axisBits r.2))
          ((pathSteps r.1 (axisBits r.2)).length - 1)).m = (preads.count r : F) := by
        show (if (pathSteps r.1 (axisBits r.2)).length - 1 + 1 = (pathSteps r.1 (axisBits r.2)).length
          then (preads.count r : F) else 0) = _
        rw [if_pos (by omega)]
      rw [hm, this, nsmul_eq_mul]
      simp [liftQ]
    · intro k hk hne'
      have : ¬ (k + 1 = (pathSteps r.1 (axisBits r.2)).length) := by
        have := Finset.mem_range.mp hk; omega
      simp only [Function.comp, chainRow, if_neg this, liftQ, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [List.map_congr_left hper]
  have hcount : ∀ r ∈ pathReads preads, preads.count r =
      ((preads.filter fun r => isPathAx r.2)).count r := by
    intro r hr
    have hd : isPathAx r.2 = true := by
      simp only [pathReads, List.mem_dedup, List.mem_filter] at hr; exact hr.2
    rw [List.count_filter]; simp [hd]
  rw [List.map_congr_left (fun r hr => by rw [hcount r hr])]
  have := sum_count_nsmul (pathReads preads) ((preads.filter fun r => isPathAx r.2))
    (fun r => cinv δF γ ρ (pReq δF z cells r)) (List.nodup_dedup _) (fun x hx => List.mem_dedup.mpr hx)
  convert this

/-- The padding chain (multiplicity `0`) provides nothing. -/
theorem chainRows_zero_pSum (root : Noun) (steps : List (Noun × Bool)) :
    ((chainRows δF z cells root 0 steps).map
      fun x => liftQ δF x.m * (pathFillInv δF γ ρ x).pProvInv).sum = 0 := by
  unfold chainRows
  rw [List.map_map, sum_range_list]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp [Function.comp, chainRow, liftQ]

/-- **`path_pTotal` with the padding chain**: the same total (`m = 0` contributes `0`). -/
theorem path_pTotalP (preads : List (Noun × ℕ))
    (hslot : ∀ r ∈ pathReads preads, (Noun.slot r.2 r.1).isSome) :
    ∑ k ∈ Finset.range (pathTableP δF z cells preads).length,
      liftQ δF ((pathTableP δF z cells preads).getD k (chainRow δF z cells (.atom 0) 0 [] 0)).m *
        (pathFillInv δF γ ρ ((pathTableP δF z cells preads).getD k
          (chainRow δF z cells (.atom 0) 0 [] 0))).pProvInv =
    (((preads.filter fun r => isPathAx r.2)).map fun r => cinv δF γ ρ (pReq δF z cells r)).sum := by
  have h := sum_range_getD (pathTableP δF z cells preads) (chainRow δF z cells (.atom 0) 0 [] 0)
    fun x => liftQ δF x.m * (pathFillInv δF γ ρ x).pProvInv
  refine h.trans ?_
  have h0 := (sum_range_getD (pathTable δF z cells preads) (chainRow δF z cells (.atom 0) 0 [] 0)
    fun x => liftQ δF x.m * (pathFillInv δF γ ρ x).pProvInv).symm.trans
      (path_pTotal (δF := δF) γ ρ z cells preads hslot)
  unfold pathTableP
  rw [List.map_append, List.sum_append, h0, chainRows_zero_pSum γ ρ z cells, add_zero]

end PathReq


/-! ## 4. The honest datum: `honestReq` is `Σ den⁻¹` over the honest requests -/

section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] {hT hP hC : ℕ}

namespace HonestVCL
variable (H : HonestVCL (K := K) δF hT hP hC)

/-- The honest validity requests: none. -/
def vReqs (_χ : Coins frameVCL K) : List (Fin 5 → Quad (algebraMap F K δF)) :=
  let _ := H  -- keeps the datum in the signature (field notation)
  []

/-- The honest export requests: the depth-1 compute lookups with their side. -/
def xReqs (χ : Coins frameVCL K) : List (Fin 11 → Quad (algebraMap F K δF)) :=
  (shallowSided H.d.reads).map fun c => xReq δF (zC χ) H.d.cells c.1 c.2

/-- The honest path requests: the deep reads (with multiplicity), as `(root, child, axis, serial)` records. -/
def pReqs (χ : Coins frameVCL K) : List (Fin 8 → Quad (algebraMap F K δF)) :=
  (H.d.preads.filter fun r => isPathAx r.2).map (pReq δF (zC χ) H.d.cells)

/-- The honest requests per accumulator, at the record shapes of `RV.mVCL`. -/
def reqRecs (χ : Coins frameVCL K) : ∀ a : Fin 3, List (Fin (RV.mVCL a) → Quad (algebraMap F K δF))
  | 0 => H.vReqs χ
  | 1 => H.xReqs χ
  | 2 => H.pReqs χ

theorem cells_hyps :
    H.d.cells.Nodup ∧ (∀ n ∈ H.d.cells, n.isCell = true) ∧
    (∀ n ∈ H.d.cells, ∀ c ∈ childCells n, c ∈ H.d.cells) :=
  ⟨closureOf_nodup _, fun n hn => closureOf_isCell hn, fun n hn c hc => closureOf_closed hn hc⟩

/-- The cell table is non-empty (the verifier datum's `hM` and `hC0`). -/
theorem cells_pos : 0 < H.d.cells.length := H.hC0 ▸ H.V.hM (tC hT hP)

theorem padCell_mem : padCell H.d.cells ∈ H.d.cells := by
  have h := H.cells_pos
  generalize H.d.cells = cs at h ⊢
  cases cs with
  | nil => simp at h
  | cons a l => simp [padCell]

theorem sidedP_subset : ∀ x ∈ sidedConsumersP H.d.cells H.d.preads H.d.reads, x.1 ∈ H.d.cells := by
  intro x hx
  have hold : x ∈ sidedConsumers H.d.preads H.d.reads → x.1 ∈ H.d.cells := fun h => by
    apply exportConsumers_subset H.d
    rw [← sidedConsumers_fst H.d.preads H.d.reads]
    exact List.mem_map.mpr ⟨x, h, rfl⟩
  simp only [sidedConsumersP, edgeSidedP, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact hold (by simp only [sidedConsumers, List.mem_append]; exact Or.inl hx)
  · unfold padSteps at hx
    split_ifs at hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact H.padCell_mem
    · simp at hx
  · exact hold (by simp only [sidedConsumers, List.mem_append]; exact Or.inr hx)

theorem xs0_subset : ∀ c ∈ xs0P H.d.cells H.d.preads H.d.reads, c ∈ H.d.cells := by
  intro c hc
  simp only [xs0P, List.mem_map, List.mem_filter] at hc
  obtain ⟨x, ⟨hx, -⟩, rfl⟩ := hc
  exact H.sidedP_subset x hx

theorem xs1_subset : ∀ c ∈ xs1P H.d.cells H.d.preads H.d.reads, c ∈ H.d.cells := by
  intro c hc
  simp only [xs1P, List.mem_map, List.mem_filter] at hc
  obtain ⟨x, ⟨hx, -⟩, rfl⟩ := hc
  exact H.sidedP_subset x hx

variable (χ : Coins frameVCL K)

/-- **Validity (accumulator 0)**: `vTot = Σ_{vReqs} den⁻¹ = 0` (`vReqs = []`). -/
theorem vTot_eq : H.vTot χ = ((H.vReqs χ).map fun r =>
    (FiniteIO.compress (m := 5) ⟨γC χ, ρC χ⟩ r)⁻¹).sum := by
  obtain ⟨hnd, hcell, hclosed⟩ := H.cells_hyps
  unfold vTot vReqs cellRows
  rw [H.hC0]
  have := cell_vTotal (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells [] (xs0P H.d.cells H.d.preads H.d.reads) (xs1P H.d.cells H.d.preads H.d.reads)
    hnd hcell hclosed (fun b hb => by simp at hb)
  simpa using this

/-- **Validity closes internally**: `vTot = 0` (C5 consumes this). -/
theorem vTot_eq_zero : H.vTot χ = 0 := by
  rw [H.vTot_eq]; simp [vReqs]

/-- The cell table's export provides (`mx0`, `mx1` per side) total `Σ_{sided consumers} den⁻¹`. -/
theorem xTot_eq : H.xTot χ =
    ((sidedConsumersP H.d.cells H.d.preads H.d.reads).map fun c => cinv δF (γC χ) (ρC χ) (xReq δF (zC χ) H.d.cells c.1 c.2)).sum := by
  obtain ⟨hnd, hcell, hclosed⟩ := H.cells_hyps
  unfold xTot
  rw [H.hC0]
  have := cell_xTotal (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells (vcsOf H.d.cells [])
    (xs0P H.d.cells H.d.preads H.d.reads) (xs1P H.d.cells H.d.preads H.d.reads) hnd (H.xs0_subset) (H.xs1_subset)
  refine this.trans ?_
  exact (sum_sided_split (sidedConsumersP H.d.cells H.d.preads H.d.reads)
    fun n b => cinv δF (γC χ) (ρC χ) (xReq δF (zC χ) H.d.cells n b)).symm

/-- The path chip's export consumes total `Σ_{path edges} den⁻¹`. -/
theorem yTot_eq : H.yTot χ =
    ((edgeSidedP H.d.cells H.d.preads).map fun c => cinv δF (γC χ) (ρC χ) (xReq δF (zC χ) H.d.cells c.1 c.2)).sum := by
  unfold yTot
  rw [H.hP0, pathTableP_length (0 : Quad (algebraMap F K δF)) (zC χ)]
  exact path_yTotalP (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells H.d.preads

/-- **Deviation (d), the export balance**: the cell table's per-side export provides (`mx0` / `mx1`, the
generator's `xs0` / `xs1` counts) equal the path chip's `pxKey` consumes plus the compute lookups. -/
theorem export_side_balance : H.xTot χ = H.yTot χ +
    ((H.xReqs χ).map fun r => (FiniteIO.compress (m := 11) ⟨γC (δF := δF) χ, ρC χ⟩ r)⁻¹).sum := by
  rw [xTot_eq, yTot_eq, sidedConsumersP, List.map_append, List.sum_append]
  simp [xReqs, cinv, List.map_map, Function.comp_def]

/-- **Export (accumulator 1)**: `xTot − yTot = Σ_{shallow lookups} den⁻¹`. -/
theorem xTot_sub_yTot_eq : H.xTot χ - H.yTot χ = ((H.xReqs χ).map fun r =>
    (FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ r)⁻¹).sum := by
  rw [export_side_balance]; abel

/-- **Path-provide (accumulator 2)**: `pTot = Σ_{deep reads} den⁻¹` (given every deep read is a defined slot). -/
theorem pTot_eq (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) :
    H.pTot χ = ((H.pReqs χ).map fun r => (FiniteIO.compress (m := 8) ⟨γC χ, ρC χ⟩ r)⁻¹).sum := by
  unfold pTot pReqs
  rw [H.hP0, pathTableP_length (0 : Quad (algebraMap F K δF)) (zC χ), List.map_map]
  exact path_pTotalP (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells H.d.preads hslot

/-- **`honestReq` is `Σ den⁻¹` over the honest compute requests, per accumulator.** -/
theorem req_eq (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) (a : Fin 3) :
    H.req χ a = ((H.reqRecs χ a).map fun r =>
      (FiniteIO.compress (m := RV.mVCL a) ⟨γC χ, ρC χ⟩ r)⁻¹).sum := by
  fin_cases a
  · exact vTot_eq H χ
  · exact xTot_sub_yTot_eq H χ
  · exact pTot_eq H χ hslot

/-- `honestReq` at accumulator 0 is `0`. -/
theorem req_zero : H.req χ 0 = 0 := by
  exact H.vTot_eq_zero χ

/-- `honestMsg2` is the export-consume total: `Σ_{path edges} den⁻¹`. -/
theorem msg2_eq : H.msg2 χ = ((edgeSidedP H.d.cells H.d.preads).map fun c =>
    (FiniteIO.compress (m := 11) ⟨γC (δF := δF) χ, ρC χ⟩ (xReq δF (zC χ) H.d.cells c.1 c.2))⁻¹).sum :=
  yTot_eq H χ

end HonestVCL

end Honest

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
