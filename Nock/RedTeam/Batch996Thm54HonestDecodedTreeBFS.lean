/-
  Nock/RedTeam/Batch996Thm54HonestDecodedTreeBFS.lean

  No `hgood`, no event.

  `DecodedLambdaEvent.decodedMTreeOfEnvs` rebuilds a memory tree from round-0 columns only: the
  state selectors (`memRowStateOf`), the BFS inversion of the fanout column (`childIdx`, `foOfMem`)
  and the exponent column (`rowExp`).  §A shows that on environments which carry the rows of a
  BFS-laid-out forest `l` (state and exponent of row `r` read off the `r`-th BFS node), and whose
  forest has the exact memory topology (`fanoutMem st = #children` at every node), the decoded
  tree at row `i` IS the forest's subtree at BFS position `i`, translated node by node (`mt`):
  `decoded_eq_mt`.  The induction is the inverse-BFS one of `ExactTraversal.buildTF_bfsForest_get`
  (children of node `i` sit at `firstCF kroots fo i + j`, `exact_bfsForest_child_pos`; queue
  validity `foCol_BFSValidF` makes every child index exceed its parent's).

  §B identifies the translation with the axis tree a served walk lives on:
  `mt ex (mapNTree enc t) = rn g (ofNTree E t).toMTree` whenever `enc` keeps states and the decoded
  exponent of every read / verify node is `g` of its timestamp exponent (`mt_mapNTree_eq_rn`).
-/
import Nock.RedTeam.Batch995Thm54HonestFormRTreeCore
import Nock.NockVMROM.Thm54.DecodedLambdaEvent
import Nock.NockVMROM.Thm54.ExactTraversal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch996

open Nock
open Nock.Walk
open Nock.Reified
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.RedTeam.Batch995

noncomputable section

/-- A memory-table label. -/
abbrev MLT (K : Type) := MemoryTable.MState × MemoryTable.DTmem K

variable {F K : Type} [Field F] [Field K] [DecidableEq F]

/-! ## A. The decoded tree of a BFS-laid-out forest -/

/-- **The decoded-tree translation of a memory `NTree`**: shape from the state, exponent `ex` of
the label, verify `a` written `0` (the `decodedMTreeOfEnvs` convention). -/
def mt (ex : MLT K → ℕ) : NTree (MLT K) → MTree K
  | .node a ch =>
      match a.1, ch with
      | .halt, _ => .halt
      | .decompose, [l, r] => .decompose (mt ex l) (mt ex r)
      | .read_root, [c] => .read (ex a) (mt ex c)
      | .verify_child, [c] => .verify (ex a) 0 (mt ex c)
      | _, _ => .halt
termination_by t => sizeOf t
decreasing_by
  all_goals (simp only [wfParam] at *; simp_wf; omega)

theorem mt_halt (ex : MLT K → ℕ) (d : MemoryTable.DTmem K) (ch : List (NTree (MLT K))) :
    mt ex (.node (.halt, d) ch) = .halt := by
  rw [mt.eq_def]

theorem mt_decompose (ex : MLT K → ℕ) (d : MemoryTable.DTmem K) (l r : NTree (MLT K)) :
    mt ex (.node (.decompose, d) [l, r]) = .decompose (mt ex l) (mt ex r) := by
  rw [mt.eq_def]

theorem mt_read (ex : MLT K → ℕ) (d : MemoryTable.DTmem K) (c : NTree (MLT K)) :
    mt ex (.node (.read_root, d) [c]) = .read (ex (.read_root, d)) (mt ex c) := by
  rw [mt.eq_def]

theorem mt_verify (ex : MLT K → ℕ) (d : MemoryTable.DTmem K) (c : NTree (MLT K)) :
    mt ex (.node (.verify_child, d) [c]) = .verify (ex (.verify_child, d)) 0 (mt ex c) := by
  rw [mt.eq_def]

/-- `Sf` only reads indices `1..k`. -/
theorem Sf_congr {fo fo' : ℕ → ℕ} {k : ℕ} (h : ∀ j, 1 ≤ j → j ≤ k → fo j = fo' j) :
    Sf fo k = Sf fo' k := by
  unfold Sf
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  exact h j hj.1 hj.2

section BFS

variable (l : List (NTree (MLT K))) (hl : l ≠ [])
variable {M : ℕ} (hM : (bfsForest l).length = M)
variable (envsK : Fin M → Env K) (envsF : Fin M → Env F) (ex : MLT K → ℕ)
variable (hst : ∀ (r : Fin M) (t : NTree (MLT K)), (bfsForest l)[(r : ℕ)]? = some t →
    memRowStateOf (envsF r) = t.label.1)
variable (hex : ∀ (r : Fin M) (t : NTree (MLT K)), (bfsForest l)[(r : ℕ)]? = some t →
    rowExp envsF r = ex t.label)
variable (htopo : ∀ t ∈ bfsForest l, MemoryTable.fanoutMem t.label.1 = t.children.length)

include hM hst htopo in
/-- The decoded fanout column is the BFS walk's `foCol` on `1..M`. -/
theorem foOfMem_eq_foCol (j : ℕ) (hj1 : 1 ≤ j) (hjM : j ≤ M) :
    foOfMem envsF j = foCol (bfsForest l) j := by
  have hlt : j - 1 < (bfsForest l).length := by omega
  obtain ⟨t, ht⟩ : ∃ t, (bfsForest l)[j - 1]? = some t :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  unfold foOfMem
  rw [dif_pos ⟨hj1, by omega⟩, hst ⟨j - 1, by omega⟩ t ht]
  unfold foCol
  rw [ht]
  simp only [Option.map_some, Option.getD_some]
  exact htopo t (List.mem_of_getElem? ht)

include hl hM hst htopo in
/-- **The child position of the decoded tree.**  Child slot `j + 1` of row `i` is the `j`-th child
of the BFS node at `i`, and it sits strictly after `i`. -/
theorem childIdx_spec (i : ℕ) (hi : 1 ≤ i) (t : NTree (MLT K))
    (ht : (bfsForest l)[i - 1]? = some t) (j : ℕ) (hj : j < t.children.length) :
    i < childIdx envsF l.length i (j + 1) ∧
      (bfsForest l)[childIdx envsF l.length i (j + 1) - 1]? = t.children[j]? := by
  have hiM : i ≤ M := by
    have := (List.getElem?_eq_some_iff.mp ht).1; omega
  have hSf : Sf (foOfMem envsF) (i - 1) = Sf (foCol (bfsForest l)) (i - 1) :=
    Sf_congr fun k hk1 hk2 => foOfMem_eq_foCol l hM envsF hst htopo k hk1 (by omega)
  have hfo : foCol (bfsForest l) i = t.children.length := by
    unfold foCol; rw [ht]; rfl
  have hvalid := foCol_BFSValidF l hl i hi (by omega)
  have hpos := exact_bfsForest_child_pos l hl hi (j := j) (by rw [hfo]; exact hj)
  rw [ht] at hpos
  have hidx : childIdx envsF l.length i (j + 1) - 1 =
      firstCF l.length (foCol (bfsForest l)) i + j - 1 := by
    unfold childIdx firstCF; rw [hSf]; omega
  refine ⟨?_, ?_⟩
  · unfold childIdx; rw [hSf]; omega
  · rw [hidx, hpos]; rfl

include hl hM hst hex htopo in
/-- **BFS identification.**  The decoded tree at row `i` is the translation of the forest's subtree
at BFS position `i`. -/
theorem decoded_eq_mt :
    ∀ (i : ℕ) (t : NTree (MLT K)), 1 ≤ i → (bfsForest l)[i - 1]? = some t →
      decodedMTreeOfEnvs envsK envsF l.length i = mt ex t := by
  intro i
  induction i using DecodedLambdaEvent.measure_induction (M := M) with
  | step i ih =>
    intro t hi ht
    have hiM : i ≤ M := by
      have := (List.getElem?_eq_some_iff.mp ht).1; omega
    have hmemt : t ∈ bfsForest l := List.mem_of_getElem? ht
    have hS := hst ⟨i - 1, by omega⟩ t ht
    have hE := hex ⟨i - 1, by omega⟩ t ht
    have hT := htopo t hmemt
    -- the followed children
    have hchild : ∀ j (hj : j < t.children.length),
        (if i < childIdx envsF l.length i (j + 1) then
          decodedMTreeOfEnvs envsK envsF l.length (childIdx envsF l.length i (j + 1)) else .halt)
          = mt ex (t.children[j]) := by
      intro j hj
      obtain ⟨hlt, hpos⟩ := childIdx_spec l hl hM envsF hst htopo i hi t ht j hj
      rw [if_pos hlt]
      exact ih _ hlt hi hiM _ (by omega) (by rw [hpos, List.getElem?_eq_getElem hj])
    obtain ⟨a, ch⟩ := t
    obtain ⟨s, d⟩ := a
    simp only [NTree.label] at hS hE hT
    simp only [NTree.children] at hchild
    rw [decodedMTreeOfEnvs, dif_pos ⟨hi, hiM⟩, hS]
    cases s with
    | halt => rw [mt_halt]
    | decompose =>
        simp only [MemoryTable.fanoutMem] at hT
        match ch, hT, hchild with
        | [c0, c1], _, hchild =>
            have h0 := hchild 0 (by simp)
            have h1 := hchild 1 (by simp)
            simp only [Nat.zero_add, Nat.reduceAdd, List.getElem_cons_zero,
              List.getElem_cons_succ] at h0 h1
            simp only
            rw [mt_decompose, h0, h1]
    | read_root =>
        simp only [MemoryTable.fanoutMem] at hT
        match ch, hT, hchild with
        | [c0], _, hchild =>
            have h0 := hchild 0 (by simp)
            simp only [Nat.zero_add, List.getElem_cons_zero] at h0
            simp only
            rw [mt_read, h0, hE]
    | verify_child =>
        simp only [MemoryTable.fanoutMem] at hT
        match ch, hT, hchild with
        | [c0], _, hchild =>
            have h0 := hchild 0 (by simp)
            simp only [Nat.zero_add, List.getElem_cons_zero] at h0
            simp only
            rw [mt_verify, h0, hE]

end BFS

/-! ## B. The translation of an encoded forest is a renaming of its axis tree -/

/-- Every node of `t` (by `InTree`). -/
def AllNodes (P : NTree (MLT K) → Prop) (t : NTree (MLT K)) : Prop := ∀ s, InTree t s → P s

theorem allNodes_self {P : NTree (MLT K) → Prop} {t : NTree (MLT K)} (h : AllNodes P t) : P t :=
  h t (InTree.here t)

theorem allNodes_child {P : NTree (MLT K) → Prop} {a : MLT K} {ch : List (NTree (MLT K))}
    (h : AllNodes P (.node a ch)) {c : NTree (MLT K)} (hc : c ∈ ch) : AllNodes P c :=
  fun s hs => h s (InTree.sub hc hs)

theorem size_lt_of_mem {a : MLT K} {ch : List (NTree (MLT K))} {c : NTree (MLT K)}
    (hc : c ∈ ch) : c.size < (NTree.node a ch).size := by
  have : c.size ≤ (ch.map NTree.size).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
  simp only [NTree.size]; omega

/-- `enc` keeps the state;
the topology holds at every node; on every read / verify node the decoded exponent of the encoded
label is `g` of the node's timestamp exponent `E`. -/
theorem mt_mapNTree_eq_rn (ex : MLT K → ℕ) (enc : MLT K → MLT K) (henc : ∀ a, (enc a).1 = a.1)
    (E : NTree (MLT K) → ℕ) (g : ℕ → ℕ) :
    ∀ t : NTree (MLT K),
      AllNodes (fun s => MemoryTable.fanoutMem s.label.1 = s.children.length) t →
      AllNodes (fun s => s.label.1 = .read_root ∨ s.label.1 = .verify_child →
        ex (enc s.label) = g (E s)) t →
      mt ex (mapNTree enc t) = rn g (ofNTree E t).toMTree := by
  suffices key : ∀ n (t : NTree (MLT K)), t.size ≤ n →
      AllNodes (fun s => MemoryTable.fanoutMem s.label.1 = s.children.length) t →
      AllNodes (fun s => s.label.1 = .read_root ∨ s.label.1 = .verify_child →
        ex (enc s.label) = g (E s)) t →
      mt ex (mapNTree enc t) = rn g (ofNTree E t).toMTree from
    fun t => key _ t le_rfl
  intro n
  induction n with
  | zero =>
      intro t ht
      obtain ⟨a, ch⟩ := t
      simp [NTree.size] at ht
  | succ n ih =>
    intro t hsz htopo hexp
    obtain ⟨a, ch⟩ := t
    have hrec : ∀ c ∈ ch, mt ex (mapNTree enc c) = rn g (ofNTree E c).toMTree := fun c hc =>
      ih c (by have := size_lt_of_mem (a := a) hc; omega)
        (allNodes_child htopo hc) (allNodes_child hexp hc)
    have hT := allNodes_self htopo
    have hX := allNodes_self hexp
    simp only [NTree.label, NTree.children] at hT hX
    obtain ⟨s, d⟩ := a
    have hs := henc (s, d)
    rcases hed : enc (s, d) with ⟨s', d'⟩
    rw [hed] at hs
    simp only at hs
    subst hs
    simp only [mapNTree]
    rw [hed]
    cases s' with
    | halt =>
        rw [mt_halt, ofNTree.eq_def]
        rfl
    | decompose =>
        simp only [MemoryTable.fanoutMem] at hT
        obtain ⟨l, r, rfl⟩ : ∃ l r, ch = [l, r] := by
          match ch, hT with | [l, r], _ => exact ⟨l, r, rfl⟩
        simp only [List.map_cons, List.map_nil]
        rw [mt_decompose, ofNTree_decompose]
        simp only [MemWalk.toMTree, rn]
        rw [hrec l (by simp), hrec r (by simp)]
    | read_root =>
        simp only [MemoryTable.fanoutMem] at hT
        obtain ⟨c, rfl⟩ : ∃ c, ch = [c] := by
          match ch, hT with | [c], _ => exact ⟨c, rfl⟩
        simp only [List.map_cons, List.map_nil]
        rw [mt_read, ofNTree.eq_def]
        simp only [MemWalk.toMTree, rn]
        rw [hrec c (by simp)]
        have := hX (Or.inl rfl)
        rw [hed] at this
        rw [this]
    | verify_child =>
        simp only [MemoryTable.fanoutMem] at hT
        obtain ⟨c, rfl⟩ : ∃ c, ch = [c] := by
          match ch, hT with | [c], _ => exact ⟨c, rfl⟩
        simp only [List.map_cons, List.map_nil]
        rw [mt_verify, ofNTree.eq_def]
        simp only [MemWalk.toMTree, rn]
        rw [hrec c (by simp)]
        have := hX (Or.inr rfl)
        rw [hed] at this
        rw [this]

end

end Nock.RedTeam.Batch996

#print axioms Nock.RedTeam.Batch996.decoded_eq_mt
#print axioms Nock.RedTeam.Batch996.mt_mapNTree_eq_rn
