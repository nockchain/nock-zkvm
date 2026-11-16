import Nock.V1J8.FillCell
import Nock.V1J8.GenAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal

/-!

`regroup rs`: each root's reads contiguous, roots in exec (first-occurrence) order. Pure list/trie lemmas:
the honest walk forest at `regroup rs` has the exec root order, and is a permutation of the one at `rs`. -/

set_option autoImplicit false
open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd

/-- The exec root order (first occurrence; `groupReads`' fold). -/
def rootsR (rs : List (Noun × ℕ)) : List Noun :=
  rs.foldl (fun acc p => if p.1 ∈ acc then acc else acc ++ [p.1]) []

theorem rootsR_eq (rs : List (Noun × ℕ)) : rootsR rs = (Nock.V1J8.Gen.groupReads rs).map Prod.fst := by
  simp [rootsR, Nock.V1J8.Gen.groupReads, List.map_map, Function.comp_def]

theorem rootsR_nodup (rs : List (Noun × ℕ)) : (rootsR rs).Nodup :=
  (rootsFold_spec rs [] List.nodup_nil).1

theorem mem_rootsR (rs : List (Noun × ℕ)) (x : Noun) : x ∈ rootsR rs ↔ x ∈ rs.map Prod.fst := by
  have := (rootsFold_spec rs [] List.nodup_nil).2 x
  unfold rootsR; rw [this]; simp

/-- **The regrouped read list**: each root's reads contiguous, roots in exec order. -/
def regroup (rs : List (Noun × ℕ)) : List (Noun × ℕ) :=
  (rootsR rs).flatMap fun r => rs.filter fun p => p.1 = r

theorem mem_regroup (rs : List (Noun × ℕ)) (x : Noun × ℕ) : x ∈ regroup rs ↔ x ∈ rs := by
  unfold regroup
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, mem_rootsR, List.mem_map]
  constructor
  · rintro ⟨r, -, h, -⟩; exact h
  · intro h; exact ⟨x.1, ⟨x, h, rfl⟩, h, rfl⟩

/-- the filter over the block of `r` in the regrouped list is the filter of `rs` -/
theorem filter_regroup (rs : List (Noun × ℕ)) (r : Noun) :
    (regroup rs).filter (fun p => decide (p.1 = r)) = rs.filter fun p => decide (p.1 = r) := by
  have key : ∀ L : List Noun, L.Nodup →
      (L.flatMap fun r' => (rs.filter fun p => decide (p.1 = r')).filter fun p => decide (p.1 = r)) =
        if r ∈ L then rs.filter (fun p => decide (p.1 = r)) else [] := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons a L ih =>
      intro hL
      obtain ⟨ha, hL'⟩ := List.nodup_cons.mp hL
      rw [List.flatMap_cons, ih hL']
      by_cases har : a = r
      · subst har
        rw [if_neg ha, if_pos (List.mem_cons_self ..)]
        simp [List.filter_filter]
      · have : ((rs.filter fun p => decide (p.1 = a)).filter fun p => decide (p.1 = r)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro p hp
          simp only [List.mem_filter, decide_eq_true_eq] at hp
          simp only [decide_eq_true_eq]
          intro h
          exact har (hp.2.symm.trans h)
        rw [this, List.nil_append]
        by_cases hr : r ∈ L
        · rw [if_pos hr, if_pos (List.mem_cons_of_mem _ hr)]
        · rw [if_neg hr, if_neg (by simp [hr, Ne.symm har])]
  unfold regroup
  rw [List.filter_flatMap, key _ (rootsR_nodup rs)]
  by_cases hr : r ∈ rootsR rs
  · rw [if_pos hr]
  · rw [if_neg hr]
    symm
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simp only [decide_eq_true_eq]
    rintro rfl
    exact hr ((mem_rootsR rs _).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩))

theorem regroup_perm (rs : List (Noun × ℕ)) : (regroup rs).Perm rs := by
  rw [List.perm_iff_count]
  intro x
  have h1 : (regroup rs).count x = ((regroup rs).filter fun p => decide (p.1 = x.1)).count x :=
    (List.count_filter (by simp)).symm
  have h2 : rs.count x = (rs.filter fun p => decide (p.1 = x.1)).count x :=
    (List.count_filter (by simp)).symm
  rw [h1, h2, filter_regroup]

/-- `dedup` of a nonempty constant block followed by a tail not containing the constant -/
theorem dedup_block (a : Noun) (B : List Noun) (haB : a ∉ B) :
    ∀ A : List Noun, A ≠ [] → (∀ x ∈ A, x = a) → (A ++ B).dedup = a :: B.dedup
  | [], h, _ => absurd rfl h
  | x :: A', _, hA => by
    have hx : x = a := hA x (List.mem_cons_self ..)
    rw [hx]
    by_cases hA' : A' = []
    · subst hA'
      simp [List.dedup_cons_of_notMem haB]
    · rw [List.cons_append, List.dedup_cons_of_mem]
      · exact dedup_block a B haB A' hA' fun y hy => hA y (List.mem_cons_of_mem _ hy)
      · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hA'
        have := hA y (List.mem_cons_of_mem _ hy)
        rw [← this]; exact List.mem_append_left _ hy

theorem dedup_flatMap_blocks (f : Noun → List Noun) :
    ∀ L : List Noun, L.Nodup → (∀ r ∈ L, f r ≠ [] ∧ ∀ x ∈ f r, x = r) → (L.flatMap f).dedup = L
  | [], _, _ => by simp
  | a :: L, hL, hf => by
    obtain ⟨ha, hL'⟩ := List.nodup_cons.mp hL
    have hfa := hf a (List.mem_cons_self ..)
    have hB : a ∉ L.flatMap f := by
      intro h
      obtain ⟨r, hr, hx⟩ := List.mem_flatMap.mp h
      have := (hf r (List.mem_cons_of_mem _ hr)).2 a hx
      exact ha (this ▸ hr)
    rw [List.flatMap_cons, dedup_block a _ hB (f a) hfa.1 hfa.2,
      dedup_flatMap_blocks f L hL' fun r hr => hf r (List.mem_cons_of_mem _ hr)]

theorem walkRoots_regroup (rs : List (Noun × ℕ)) (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) :
    walkRoots (regroup rs) = rootsR rs := by
  have hall' : ∀ x ∈ regroup rs, VclL.isPathAx x.2 = true := fun x hx => hall x ((mem_regroup rs x).mp hx)
  unfold walkRoots
  rw [pathKind_of_all hall']
  unfold regroup
  rw [List.map_flatMap]
  apply dedup_flatMap_blocks _ _ (rootsR_nodup rs)
  intro r hr
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : ∃ p ∈ rs, p.1 = r := by
      obtain ⟨p, hp, hpr⟩ := List.mem_map.mp ((mem_rootsR rs r).mp hr)
      exact ⟨p, hp, hpr⟩
    obtain ⟨p, hp, hpr⟩ := h1
    have : p.1 ∈ (rs.filter fun p => decide (p.1 = r)).map Prod.fst :=
      List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simpa using hpr⟩, rfl⟩
    rw [h] at this; simp at this
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    simpa using (List.mem_filter.mp hp).2

theorem targetsOf_regroup (rs : List (Noun × ℕ)) (r : Noun) :
    targetsOf (regroup rs) r = targetsOf rs r := by
  have hcomm : ∀ (P Q : Noun × ℕ → Bool) (l : List (Noun × ℕ)),
      (l.filter P).filter Q = (l.filter Q).filter P := by
    intro P Q l
    rw [List.filter_filter, List.filter_filter]
    congr 1; funext x; exact Bool.and_comm _ _
  unfold targetsOf pathKind
  rw [hcomm _ _ (regroup rs), filter_regroup, hcomm _ _ rs]

theorem walkForest_regroup (cells : List Noun) (rs : List (Noun × ℕ))
    (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) :
    walkForest cells (regroup rs) =
      if rootsR rs = [] then [trie (cells.headD (.atom 0)) (cells.headD (.atom 0)) [] []]
      else (rootsR rs).map fun r => trie r r [] (targetsOf rs r) := by
  unfold walkForest
  rw [walkRoots_regroup rs hall]
  simp only [targetsOf_regroup]

theorem walkForest_regroup_perm (cells : List Noun) (rs : List (Noun × ℕ))
    (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) :
    (walkForest cells (regroup rs)).Perm (walkForest cells rs) := by
  have hwr : walkRoots rs = (rs.map Prod.fst).dedup := by unfold walkRoots; rw [pathKind_of_all hall]
  have hperm : (rootsR rs).Perm (walkRoots rs) := by rw [hwr]; exact groupRoots_perm rs
  rw [walkForest_regroup cells rs hall]
  by_cases h : rootsR rs = []
  · have h2 : walkRoots rs = [] := by
      rw [h] at hperm; exact hperm.symm.eq_nil
    unfold walkForest
    rw [if_pos h, if_pos h2]
  · have h2 : walkRoots rs ≠ [] := fun e => by
      rw [e] at hperm; exact h hperm.eq_nil
    unfold walkForest
    rw [if_neg h, if_neg h2]
    exact hperm.map _

theorem walkRows_regroup_perm (cells : List Noun) (rs : List (Noun × ℕ))
    (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) :
    (walkRows cells (regroup rs)).Perm (walkRows cells rs) := by
  unfold walkRows
  exact bfsForest_perm_of_perm (walkForest_regroup_perm cells rs hall)

theorem krW_regroup (cells : List Noun) (rs : List (Noun × ℕ)) (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) :
    krW cells (regroup rs) = krW cells rs := by
  unfold krW
  exact (walkForest_regroup_perm cells rs hall).length_eq

theorem walkDepthOK_regroup (rs : List (Noun × ℕ)) (h : ComplJ8Walk.WalkDepthOK rs) :
    ComplJ8Walk.WalkDepthOK (regroup rs) := by
  intro r hr
  apply h r
  simp only [VclL.pathReads, List.mem_dedup, List.mem_filter] at hr ⊢
  exact ⟨(mem_regroup rs r).mp hr.1, hr.2⟩

#print axioms rootsR_eq
#print axioms rootsR_nodup
#print axioms mem_rootsR
#print axioms regroup_perm
#print axioms walkRoots_regroup
#print axioms targetsOf_regroup
#print axioms walkForest_regroup
#print axioms walkRows_regroup_perm
#print axioms krW_regroup
#print axioms walkDepthOK_regroup

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd
