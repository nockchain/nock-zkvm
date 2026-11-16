import Nock.V1J8.FillCell
import Nock.V1J8.GenAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd

/-!

`walkGen_eq_map`: the executable walk rows `(walkGen dummy rs).1` are, row by row, `wrowOf` of the honest walk rows
at the regrouped reads `regroup rs`; and `kr` is `krW cells (regroup rs)`. -/

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
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkBfs

/-- The exec row of an honest trie node. -/
def wrowOf (t : NTree WN) : Nock.V1J8.Gen.WRow :=
  ⟨t.label.node, t.label.root, VclL.axisFold t.label.bits, t.label.bits.length, t.label.cL, t.label.cR,
    t.label.mL, t.label.mR⟩

/-- Executable trie node ↔ spec trie node: `CorrK` with the exec prefix `= axisFold bs`. -/
def CorrP (k : ℕ) (u : Nock.V1J8.Gen.TN) (t : NTree WN) : Prop :=
  ∃ (R n : Noun) (bs : List Bool) (T : List (List Bool)),
    u = Nock.V1J8.Gen.trie R n (VclL.axisFold bs) bs.length T ∧ t = GenWalk.trie R n bs T ∧
      ∀ s ∈ T, s.length ≤ k

theorem label_corrP {k : ℕ} {u : Nock.V1J8.Gen.TN} {t : NTree WN} (h : CorrP k u t) :
    u.label = wrowOf t := by
  obtain ⟨R, n, bs, T, rfl, rfl, -⟩ := h
  cases n <;> rfl

theorem kids_corrP {k : ℕ} {u : Nock.V1J8.Gen.TN} {t : NTree WN} (h : CorrP (k + 1) u t) :
    List.Forall₂ (CorrP k) u.kids t.children := by
  obtain ⟨R, n, bs, T, rfl, rfl, hT⟩ := h
  cases n with
  | atom a => exact List.Forall₂.nil
  | cell l r =>
    show List.Forall₂ (CorrP k)
      ((if Nock.V1J8.Gen.contB false T then [Nock.V1J8.Gen.trie R l (2 * VclL.axisFold bs) (bs.length + 1)
          (Nock.V1J8.Gen.contT false T)] else []) ++
       (if Nock.V1J8.Gen.contB true T then [Nock.V1J8.Gen.trie R r (2 * VclL.axisFold bs + 1) (bs.length + 1)
          (Nock.V1J8.Gen.contT true T)] else []))
      ((if cont false T then [GenWalk.trie R l (bs ++ [false]) (GenWalk.contT false T)] else []) ++
       (if cont true T then [GenWalk.trie R r (bs ++ [true]) (GenWalk.contT true T)] else []))
    rw [contB_eq, contB_eq, contT_eq, contT_eq]
    refine forall₂_append ?_ ?_
    · split_ifs
      · exact List.Forall₂.cons ⟨R, l, bs ++ [false], _, by simp [VclL.axisFold_append], rfl,
          contT_le false T hT⟩ List.Forall₂.nil
      · exact List.Forall₂.nil
    · split_ifs
      · exact List.Forall₂.cons ⟨R, r, bs ++ [true], _, by simp [VclL.axisFold_append], rfl,
          contT_le true T hT⟩ List.Forall₂.nil
      · exact List.Forall₂.nil

theorem kids_nil0P {u : Nock.V1J8.Gen.TN} {t : NTree WN} (h : CorrP 0 u t) : u.kids = [] ∧ t.children = [] := by
  obtain ⟨R, n, bs, T, rfl, rfl, hT⟩ := h
  cases n with
  | atom a => exact ⟨rfl, rfl⟩
  | cell l r =>
    have h0 := contT_nil_of_le0 false T hT
    have h1 := contT_nil_of_le0 true T hT
    have c0 : cont false T = false := by simp [cont, h0]
    have c1 : cont true T = false := by simp [cont, h1]
    refine ⟨?_, ?_⟩
    · show ((if Nock.V1J8.Gen.contB false T then _ else []) ++ (if Nock.V1J8.Gen.contB true T then _ else [])) = []
      rw [contB_eq, contB_eq, c0, c1]; rfl
    · show ((if cont false T then _ else []) ++ (if cont true T then _ else [])) = []
      rw [c0, c1]; rfl

theorem forall₂_map_label {k : ℕ} : ∀ {l : List Nock.V1J8.Gen.TN} {l' : List (NTree WN)},
    List.Forall₂ (CorrP k) l l' → l.map Nock.V1J8.Gen.TN.label = l'.map wrowOf
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [List.map_cons, label_corrP h, forall₂_map_label hs]

/-- **The executable BFS rows are `wrowOf` of the spec BFS** once the fuel exceeds the target depth. -/
theorem bfsTN_label : ∀ (k m : ℕ), k + 1 ≤ m → ∀ (l : List Nock.V1J8.Gen.TN) (l' : List (NTree WN)),
    List.Forall₂ (CorrP k) l l' → Nock.V1J8.Gen.bfsTN m l = (bfsForest l').map wrowOf
  | k, 0, hm, _, _, _ => by omega
  | k, m + 1, hm, [], l', h => by
    cases h; simp [Nock.V1J8.Gen.bfsTN, bfsForest]
  | k, m + 1, hm, u :: us, l', h => by
    cases h with
    | cons hu hus =>
      rename_i t ts
      rw [bfsForest]
      simp only [Nock.V1J8.Gen.bfsTN, List.map_append]
      have hl := forall₂_map_label (List.Forall₂.cons hu hus)
      rw [hl]
      congr 1
      cases k with
      | zero =>
        have hk : ((u :: us).flatMap Nock.V1J8.Gen.TN.kids) = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro x hx
          obtain ⟨y, hy⟩ := f2_left (List.Forall₂.cons hu hus) x hx
          exact (kids_nil0P hy).1
        have hk' : ((t :: ts).flatMap NTree.children) = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro x hx
          obtain ⟨y, hy⟩ := f2_right (List.Forall₂.cons hu hus) x hx
          exact (kids_nil0P hy).2
        rw [hk, hk']
        cases m <;> simp [Nock.V1J8.Gen.bfsTN, bfsForest]
      | succ k =>
        exact bfsTN_label k m (by omega) _ _
          (forall₂_flatMap (fun a b hab => kids_corrP hab) (List.Forall₂.cons hu hus))

/-- **The executable walk table = the honest walk rows at the regrouped reads** (row by row, via `wrowOf`). -/
theorem walkGen_eq_map (cells : List Noun) (rs : List (Noun × ℕ))
    (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) (hwalk : ComplJ8Walk.WalkDepthOK rs) :
    (Nock.V1J8.Gen.walkGen (cells.headD (.atom 0)) rs).1 = (walkRows cells (regroup rs)).map wrowOf ∧
      (Nock.V1J8.Gen.walkGen (cells.headD (.atom 0)) rs).2 = krW cells (regroup rs) := by
  have h62 : ∀ r ∈ VclL.pathReads rs, VclL.depthOf r.2 ≤ 62 := fun r hr => (hwalk r hr).trans (by norm_num)
  set dummy := cells.headD (.atom 0)
  have hgs : Nock.V1J8.Gen.groupReads rs =
      (rootsR rs).map fun r => (r, (rs.filter fun p => p.1 = r).map fun p => Nock.V1J8.Gen.axisBits p.2) := rfl
  have hfs := walkForest_regroup cells rs hall
  let fs : List (NTree WN) := walkForest cells (regroup rs)
  have hfe : List.Forall₂ (CorrP 62)
      (if (Nock.V1J8.Gen.groupReads rs).isEmpty then [Nock.V1J8.Gen.trie dummy dummy 1 0 []]
        else (Nock.V1J8.Gen.groupReads rs).map fun g => Nock.V1J8.Gen.trie g.1 g.1 1 0 g.2) fs := by
    rw [hgs]
    by_cases h0 : rootsR rs = []
    · simp only [fs, hfs, h0, List.map_nil, List.isEmpty_nil, if_true]
      exact List.Forall₂.cons ⟨dummy, dummy, [], [], rfl, rfl, by simp⟩ List.Forall₂.nil
    · have he : ((rootsR rs).map fun r =>
          (r, (rs.filter fun p => p.1 = r).map fun p => Nock.V1J8.Gen.axisBits p.2)).isEmpty = false := by
        simpa using h0
      simp only [fs, hfs, h0, he, if_false, Bool.false_eq_true, List.map_map]
      induction rootsR rs with
      | nil => exact List.Forall₂.nil
      | cons r rt ih =>
        refine List.Forall₂.cons ⟨r, r, [], targetsOf rs r, ?_, rfl, ?_⟩ ?_
        · simp only [List.map_cons, Function.comp_apply, targets_eq hall]; rfl
        · intro s hs
          have := (targetsOf_depth h62 r).2 s hs
          simp at this; omega
        · exact ih
  have hws : (Nock.V1J8.Gen.walkGen dummy rs).1 = Nock.V1J8.Gen.bfsTN 70
      (if (Nock.V1J8.Gen.groupReads rs).isEmpty then [Nock.V1J8.Gen.trie dummy dummy 1 0 []]
        else (Nock.V1J8.Gen.groupReads rs).map fun g => Nock.V1J8.Gen.trie g.1 g.1 1 0 g.2) := rfl
  refine ⟨?_, ?_⟩
  · rw [hws, bfsTN_label 62 70 (by norm_num) _ _ hfe]
    rfl
  · have hlen := hfe.length_eq
    have h2 : (Nock.V1J8.Gen.walkGen dummy rs).2 =
        (if (Nock.V1J8.Gen.groupReads rs).isEmpty then [Nock.V1J8.Gen.trie dummy dummy 1 0 []]
          else (Nock.V1J8.Gen.groupReads rs).map fun g => Nock.V1J8.Gen.trie g.1 g.1 1 0 g.2).length := rfl
    rw [h2, hlen]
    rfl

#print axioms label_corrP
#print axioms kids_corrP
#print axioms bfsTN_label
#print axioms walkGen_eq_map

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkBfs
