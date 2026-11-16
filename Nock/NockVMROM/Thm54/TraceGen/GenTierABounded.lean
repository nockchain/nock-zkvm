/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierABounded.lean

  `SemanticSkeleton.BoundedBy 769` on the generated F769 carrier, then
  `ExactExecutionNounRealization` from the already-proved `BindsAt`.

  Compute `childLinkComp` / `ComputeExactTopology` are not claimed here.
  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierABinds
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMem

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Atom / constructor bounds -/

theorem atom_lt_769 {n : ℕ} (h : n ≤ 9) : n < 769 := by omega

theorem atom0_bounded : FieldEmbedding.BoundedBy 769 (.atom 0) := by
  simp [FieldEmbedding.BoundedBy]

theorem memHaltSkel_bounded {q a : ℕ} (ha : a < q) :
    (memHaltSkel a).BoundedBy q := by
  refine ⟨by simp [memHaltSkel, FieldEmbedding.BoundedBy, ha], ?_, ?_⟩
  · intro i h
    simp [memHaltSkel, fanoutMem] at h
  · intro h
    simp [memHaltSkel, memoryMemRecKind] at h

theorem memDecomposeSkel_bounded {q : ℕ} {formula head result : Noun}
    (hf : FieldEmbedding.BoundedBy q formula)
    (hh : FieldEmbedding.BoundedBy q head)
    (hr : FieldEmbedding.BoundedBy q result) :
    (memDecomposeSkel formula head result).BoundedBy q := by
  refine ⟨hf, ?_, ?_⟩
  · intro i h
    fin_cases i <;> simp [memDecomposeSkel, fanoutMem] at h ⊢
    · exact hh
    · exact hr
  · intro h
    simp [memDecomposeSkel, memoryMemRecKind] at h

theorem memReadSkelAx_bounded {q : ℕ} {root child : Noun} {ax : ℕ}
    (hr : FieldEmbedding.BoundedBy q root)
    (hc : FieldEmbedding.BoundedBy q child)
    (_h0 : FieldEmbedding.BoundedBy q (.atom 0)) :
    (memReadSkelAx root child ax).BoundedBy q := by
  refine ⟨hr, ?_, ?_⟩
  · intro i h
    fin_cases i
    · simp [memReadSkelAx, fanoutMem] at h ⊢
      exact hr
    · simp [memReadSkelAx, fanoutMem] at h
  · intro h
    simp [memReadSkelAx, memoryMemRecKind, MemRecSkeleton.BoundedBy]
    exact ⟨hr, hc⟩

theorem memVerifySkelAx_bounded {q : ℕ} {root child : Noun} {ax : ℕ}
    (hr : FieldEmbedding.BoundedBy q root)
    (hc : FieldEmbedding.BoundedBy q child) :
    (memVerifySkelAx root child ax).BoundedBy q := by
  refine ⟨hc, ?_, ?_⟩
  · intro i h
    fin_cases i
    · simp [memVerifySkelAx, fanoutMem] at h ⊢
      exact hc
    · simp [memVerifySkelAx, fanoutMem] at h
  · intro h
    simp [memVerifySkelAx, memoryMemRecKind, MemRecSkeleton.BoundedBy]
    exact ⟨hr, hc⟩

theorem genSkelOp1_bounded {q : ℕ} {s f r h : Noun}
    (hs : FieldEmbedding.BoundedBy q s)
    (hf : FieldEmbedding.BoundedBy q f)
    (hr : FieldEmbedding.BoundedBy q r)
    (hh : FieldEmbedding.BoundedBy q h) :
    (genSkelOp1 s f r h).BoundedBy q := by
  refine ⟨hs, hf, hr, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot with
    | f_h => simpa [genSkelOp1] using hh
    | f_t => simpa [genSkelOp1] using hr
    | f_th | f_tt | f_tth | f_ttt =>
      simp [genSkelOp1, decActive, hasTailDecomposition] at hact
  · intro i hi slot
    simp [genSkelOp1, ComputeTable.fanoutComp] at hi
  · intro i hi
    have : i = 0 := by
      have hlt : (i : ℕ) < 1 := by
        simpa [genSkelOp1, Nock.Framework.recordCount] using hi
      exact Fin.ext (by omega)
    subst i
    simp [genSkelOp1, MemRecSkeleton.BoundedBy]
    exact ⟨hf, hr⟩

theorem genSkelOp2_bounded {q : ℕ}
    {subject formula head fTail fTh fTt sf1 sf2 result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hh : FieldEmbedding.BoundedBy q head)
    (hft : FieldEmbedding.BoundedBy q fTail)
    (hth : FieldEmbedding.BoundedBy q fTh)
    (htt : FieldEmbedding.BoundedBy q fTt)
    (hs1 : FieldEmbedding.BoundedBy q sf1)
    (hs2 : FieldEmbedding.BoundedBy q sf2)
    (hr : FieldEmbedding.BoundedBy q result) :
    (genSkelOp2 subject formula head fTail fTh fTt sf1 sf2 result).BoundedBy q := by
  refine ⟨hs, hf, hr, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot with
    | f_h => simpa [genSkelOp2] using hh
    | f_t => simpa [genSkelOp2] using hft
    | f_th => simpa [genSkelOp2] using hth
    | f_tt => simpa [genSkelOp2] using htt
    | f_tth | f_ttt =>
      simp [genSkelOp2, decActive] at hact
  · intro i hi slot
    fin_cases i <;> cases slot <;>
      simp [genSkelOp2, ComputeTable.fanoutComp] at hi ⊢
    · exact hs
    · exact hth
    · exact hs1
    · exact hs
    · exact htt
    · exact hs2
    · exact hs1
    · exact hs2
    · exact hr
  · intro i hi
    fin_cases i <;> simp [genSkelOp2, Nock.Framework.recordCount,
      MemRecSkeleton.BoundedBy] at hi ⊢
    · exact ⟨hf, hft⟩
    · exact ⟨hft, hth⟩

theorem genSkelOp6_bounded {q : ℕ}
    {subject formula head fTail fTh fTt fTth fTtt cond taken result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hh : FieldEmbedding.BoundedBy q head)
    (hft : FieldEmbedding.BoundedBy q fTail)
    (hth : FieldEmbedding.BoundedBy q fTh)
    (htt : FieldEmbedding.BoundedBy q fTt)
    (htth : FieldEmbedding.BoundedBy q fTth)
    (httt : FieldEmbedding.BoundedBy q fTtt)
    (hc : FieldEmbedding.BoundedBy q cond)
    (hta : FieldEmbedding.BoundedBy q taken)
    (hr : FieldEmbedding.BoundedBy q result) :
    (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt
      cond taken result).BoundedBy q := by
  refine ⟨hs, hf, hr, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot <;> simp [genSkelOp6, decActive] at hact ⊢
    · exact hh
    · exact hft
    · exact hth
    · exact htt
    · exact htth
    · exact httt
  · intro i hi slot
    fin_cases i <;> cases slot <;>
      simp [genSkelOp6, ComputeTable.fanoutComp] at hi ⊢
    · exact hs
    · exact hta
    · exact hr
    · exact hs
    · exact hth
    · exact hc
  · intro i hi
    fin_cases i <;> simp [genSkelOp6, Nock.Framework.recordCount,
      MemRecSkeleton.BoundedBy] at hi ⊢
    · exact ⟨hf, hft⟩
    · exact ⟨hft, hth⟩
    · exact ⟨htt, htth⟩

theorem genSkelOp9_bounded {q : ℕ}
    {subject formula head fTail fTh fTt core arm result : Noun} {axis : ℕ}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hh : FieldEmbedding.BoundedBy q head)
    (hft : FieldEmbedding.BoundedBy q fTail)
    (hth : FieldEmbedding.BoundedBy q fTh)
    (htt : FieldEmbedding.BoundedBy q fTt)
    (hcore : FieldEmbedding.BoundedBy q core)
    (harm : FieldEmbedding.BoundedBy q arm)
    (hr : FieldEmbedding.BoundedBy q result) :
    (genSkelOp9 subject formula head fTail fTh fTt core arm result axis).BoundedBy q := by
  refine ⟨hs, hf, hr, ?_, ?_, ?_⟩
  · intro slot hact
    cases slot with
    | f_h => simpa [genSkelOp9] using hh
    | f_t => simpa [genSkelOp9] using hft
    | f_th => simpa [genSkelOp9] using hth
    | f_tt => simpa [genSkelOp9] using htt
    | f_tth | f_ttt =>
      simp [genSkelOp9, decActive] at hact
  · intro i hi slot
    fin_cases i <;> cases slot <;>
      simp [genSkelOp9, ComputeTable.fanoutComp] at hi ⊢
    · exact hs
    · exact htt
    · exact hcore
    · exact hcore
    · exact harm
    · exact hr
  · intro i hi
    fin_cases i <;> simp [genSkelOp9, Nock.Framework.recordCount,
      MemRecSkeleton.BoundedBy] at hi ⊢
    · exact ⟨hf, hft⟩
    · exact ⟨hft, hth⟩
    · exact ⟨hcore, harm⟩

/-! ## Named program nouns -/

theorem b_dotSubject : FieldEmbedding.BoundedBy 769 dotSubject := by
  simp [dotSubject, FieldEmbedding.BoundedBy]
theorem b_dotElem0 : FieldEmbedding.BoundedBy 769 dotElem0 := by
  simp [dotElem0, FieldEmbedding.BoundedBy]
theorem b_dotElem1 : FieldEmbedding.BoundedBy 769 dotElem1 := by
  simp [dotElem1, FieldEmbedding.BoundedBy]
theorem b_dotCore : FieldEmbedding.BoundedBy 769 dotCore := by
  simp [dotCore, b_dotElem0, b_dotElem1, FieldEmbedding.BoundedBy]
theorem b_dotCoreFormula : FieldEmbedding.BoundedBy 769 dotCoreFormula := by
  simp [dotCoreFormula, b_dotCore, FieldEmbedding.BoundedBy]
theorem b_dotCondFormula : FieldEmbedding.BoundedBy 769 dotCondFormula := by
  simp [dotCondFormula, FieldEmbedding.BoundedBy]
theorem b_dotCondResult : FieldEmbedding.BoundedBy 769 dotCondResult := by
  simp [dotCondResult, FieldEmbedding.BoundedBy]
theorem b_dotOp9Tail : FieldEmbedding.BoundedBy 769 dotOp9Tail := by
  simp [dotOp9Tail, b_dotCoreFormula, FieldEmbedding.BoundedBy]
theorem b_dotOp9Formula : FieldEmbedding.BoundedBy 769 dotOp9Formula := by
  simp [dotOp9Formula, b_dotOp9Tail, FieldEmbedding.BoundedBy]
theorem b_dotOp2B : FieldEmbedding.BoundedBy 769 dotOp2B := by
  simp [dotOp2B, FieldEmbedding.BoundedBy]
theorem b_dotOp2C : FieldEmbedding.BoundedBy 769 dotOp2C := by
  simp [dotOp2C, b_dotOp9Formula, FieldEmbedding.BoundedBy]
theorem b_dotOp2Sf1 : FieldEmbedding.BoundedBy 769 dotOp2Sf1 := by
  simp [dotOp2Sf1, FieldEmbedding.BoundedBy]
theorem b_dotOp2Sf2 : FieldEmbedding.BoundedBy 769 dotOp2Sf2 := b_dotOp9Formula
theorem b_dotThenTail : FieldEmbedding.BoundedBy 769 dotThenTail := by
  simp [dotThenTail, b_dotOp2B, b_dotOp2C, FieldEmbedding.BoundedBy]
theorem b_dotThenFormula : FieldEmbedding.BoundedBy 769 dotThenFormula := by
  simp [dotThenFormula, b_dotThenTail, FieldEmbedding.BoundedBy]
theorem b_dotElseFormula : FieldEmbedding.BoundedBy 769 dotElseFormula := by
  simp [dotElseFormula, b_dotCoreFormula, FieldEmbedding.BoundedBy]
theorem b_dotBranchPair : FieldEmbedding.BoundedBy 769 dotBranchPair := by
  simp [dotBranchPair, b_dotThenFormula, b_dotElseFormula, FieldEmbedding.BoundedBy]
theorem b_dotParentTail : FieldEmbedding.BoundedBy 769 dotParentTail := by
  simp [dotParentTail, b_dotCondFormula, b_dotBranchPair, FieldEmbedding.BoundedBy]
theorem b_dotFormula : FieldEmbedding.BoundedBy 769 dotFormula := by
  simp [dotFormula, b_dotParentTail, FieldEmbedding.BoundedBy]
theorem b_dotResult : FieldEmbedding.BoundedBy 769 dotResult := by
  simp [dotResult, FieldEmbedding.BoundedBy]
theorem b_dotArm : FieldEmbedding.BoundedBy 769 dotArm := b_dotElem0
theorem b_atom1 : FieldEmbedding.BoundedBy 769 (.atom 1) := by
  simp [FieldEmbedding.BoundedBy]
theorem b_atom2 : FieldEmbedding.BoundedBy 769 (.atom 2) := by
  simp [FieldEmbedding.BoundedBy]
theorem b_atom6 : FieldEmbedding.BoundedBy 769 (.atom 6) := by
  simp [FieldEmbedding.BoundedBy]
theorem b_atom9 : FieldEmbedding.BoundedBy 769 (.atom 9) := by
  simp [FieldEmbedding.BoundedBy]

theorem b_dotOp6Skel : dotOp6Skel.BoundedBy 769 :=
  genSkelOp6_bounded b_dotSubject b_dotFormula b_atom6 b_dotParentTail
    b_dotCondFormula b_dotBranchPair b_dotThenFormula b_dotElseFormula
    b_dotCondResult b_dotThenFormula b_dotResult

theorem b_dotOp2Skel : dotOp2Skel.BoundedBy 769 :=
  genSkelOp2_bounded b_dotSubject b_dotThenFormula b_atom2
    b_dotThenTail b_dotOp2B b_dotOp2C b_dotOp2Sf1 b_dotOp2Sf2 b_dotResult

theorem b_dotOp9Skel : dotOp9Skel.BoundedBy 769 :=
  genSkelOp9_bounded b_dotOp2Sf1 b_dotOp9Formula b_atom9 b_dotOp9Tail
    b_atom2 b_dotCoreFormula b_dotCore b_dotArm b_dotResult

theorem b_dotCondSkel :
    (dotCondTree (K := K)).label.skel.BoundedBy 769 :=
  genSkelOp1_bounded b_dotSubject b_dotCondFormula b_dotCondResult b_atom1

theorem b_dotOp1BSkel :
    (dotOp1BTree (K := K)).label.skel.BoundedBy 769 :=
  genSkelOp1_bounded b_dotSubject b_dotOp2B b_dotOp2Sf1 b_atom1

theorem b_dotOp1CSkel :
    (dotOp1CTree (K := K)).label.skel.BoundedBy 769 :=
  genSkelOp1_bounded b_dotSubject b_dotOp2C b_dotOp2Sf2 b_atom1

theorem b_dotOp9CoreSkel :
    (dotOp9CoreTree (K := K)).label.skel.BoundedBy 769 :=
  genSkelOp1_bounded b_dotOp2Sf1 b_dotCoreFormula b_dotCore b_atom1

theorem b_dotOp9InvokeSkel :
    (dotOp9InvokeTree (K := K)).label.skel.BoundedBy 769 :=
  genSkelOp1_bounded b_dotCore b_dotArm b_dotResult b_atom1

/-! ## Assigned compute skels equal original BFS skels -/

theorem bfsAssign_skel_list (t : NTree (GenComputeRow K)) :
    (bfsForest [bfsAssign t]).map (fun n => n.label.skel) =
      (bfsForest [t]).map (fun n => n.label.skel) := by
  have h :
      (bfsForest [bfsAssign t]).map (fun n => n.label.skel) =
        ((bfsForest [bfsAssign t]).map NTree.label).map (fun g => g.skel) := by
    rw [List.map_map]; rfl
  rw [h, bfsAssign_bfsForest_labels, List.map_map]
  apply List.ext_getElem
  · simp [List.length_map, List.length_range']
  · intro n hn hn'
    simp only [List.getElem_map, List.getElem_range', one_mul, Function.comp_apply]
    have hidx : 1 + n - 1 < (bfsRows t).length := by
      simpa [bfsRows_length] using hn'
    rw [bfsLabelAt_skel t (1 + n) hidx]
    have heq : 1 + n - 1 = n := by omega
    simp [heq, bfsRows]

/-! ## Memory-builder InTree bounds -/

theorem inTree_walk_bounded (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, FieldEmbedding.BoundedBy 769 n →
      ∀ t, InTree (genAnnotatedNounWalk E z lmb n).1 t →
        t.label.skel.BoundedBy 769
  | .atom a, hn, t, ht => by
      cases ht with
      | here =>
        simp [genAnnotatedNounWalk, NTree.label, gMemRow9]
        exact memHaltSkel_bounded (by simpa [FieldEmbedding.BoundedBy] using hn)
      | sub hs _ =>
        simp [genAnnotatedNounWalk, NTree.children] at hs
  | .cell h tl, hn, t, ht => by
      have hh : FieldEmbedding.BoundedBy 769 h := (FieldEmbedding.BoundedBy_cell.mp hn).1
      have htl : FieldEmbedding.BoundedBy 769 tl := (FieldEmbedding.BoundedBy_cell.mp hn).2
      cases ht with
      | here =>
        simp [genAnnotatedNounWalk, NTree.label, gMemRow9]
        exact memDecomposeSkel_bounded (by simpa using hn) hh htl
      | sub hs hu =>
        simp [genAnnotatedNounWalk, NTree.children_node, List.mem_cons,
          List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact inTree_walk_bounded E z h hh _ hu
        · exact inTree_walk_bounded E z tl htl _ hu

theorem inTree_verify_bounded (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ)
    (hr : FieldEmbedding.BoundedBy 769 root)
    (hc : FieldEmbedding.BoundedBy 769 child)
    (t : NTree (GenMemoryRow K))
    (ht : InTree (genAnnotatedVerify E z lmb root child ax ts recordExp).1 t) :
    t.label.skel.BoundedBy 769 := by
  cases ht with
  | here =>
    simp [genAnnotatedVerify, NTree.label, gMemRow9]
    exact memVerifySkelAx_bounded hr hc
  | sub hs hu =>
    simp [genAnnotatedVerify, NTree.children_node, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    subst hs
    exact inTree_walk_bounded E z child hc _ hu

theorem inTree_record_axis3_bounded (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ)
    (hhd : FieldEmbedding.BoundedBy 769 hd)
    (htl : FieldEmbedding.BoundedBy 769 tl)
    (t : NTree (GenMemoryRow K))
    (ht : InTree (genAnnotatedRecordTree E z α lmb (.cell hd tl) tl 3 e) t) :
    t.label.skel.BoundedBy 769 := by
  have hcell : FieldEmbedding.BoundedBy 769 (.cell hd tl) :=
    FieldEmbedding.BoundedBy_cell.mpr ⟨hhd, htl⟩
  rw [genAnnotatedRecordTree_eq, genAnnotatedDescent_axis3] at ht
  cases ht with
  | here =>
    simp [NTree.label, gMemRow9]
    exact memReadSkelAx_bounded hcell htl atom0_bounded
  | sub hs hu =>
    simp [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    cases hu with
    | here =>
      simp [NTree.label, gMemRow9]
      exact memDecomposeSkel_bounded hcell hhd htl
    | sub hs' hu' =>
      simp [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl
      · exact inTree_walk_bounded E z hd hhd _ hu'
      · exact inTree_verify_bounded E z (.cell hd tl) tl 3 (α ^ e) e
          hcell htl _ hu'

theorem inTree_record_axis2_bounded (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ)
    (hhd : FieldEmbedding.BoundedBy 769 hd)
    (htl : FieldEmbedding.BoundedBy 769 tl)
    (t : NTree (GenMemoryRow K))
    (ht : InTree (genAnnotatedRecordTree E z α lmb (.cell hd tl) hd 2 e) t) :
    t.label.skel.BoundedBy 769 := by
  have hcell : FieldEmbedding.BoundedBy 769 (.cell hd tl) :=
    FieldEmbedding.BoundedBy_cell.mpr ⟨hhd, htl⟩
  rw [genAnnotatedRecordTree_eq, genAnnotatedDescent_axis2] at ht
  cases ht with
  | here =>
    simp [NTree.label, gMemRow9]
    exact memReadSkelAx_bounded hcell hhd atom0_bounded
  | sub hs hu =>
    simp [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    cases hu with
    | here =>
      simp [NTree.label, gMemRow9]
      exact memDecomposeSkel_bounded hcell hhd htl
    | sub hs' hu' =>
      simp [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl
      · exact inTree_verify_bounded E z (.cell hd tl) hd 2 (α ^ e) e
          hcell hhd _ hu'
      · exact inTree_walk_bounded E z tl htl _ hu'

theorem inTree_descentCont_axis2_bounded (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (hd tl : Noun)
    (hhd : FieldEmbedding.BoundedBy 769 hd)
    (htl : FieldEmbedding.BoundedBy 769 tl)
    (hcs : ∀ u ∈ cont, ∀ n, InTree u n → n.label.skel.BoundedBy 769)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ (genAnnotatedDescentCont E z lmb cont contCell contState (.cell hd tl) 2).1)
    (n : NTree (GenMemoryRow K)) (hn : InTree u n) :
    n.label.skel.BoundedBy 769 := by
  have hcell : FieldEmbedding.BoundedBy 769 (.cell hd tl) :=
    FieldEmbedding.BoundedBy_cell.mpr ⟨hhd, htl⟩
  rw [genAnnotatedDescentCont_axis2] at hu
  simp at hu
  subst u
  cases hn with
  | here =>
    simp [NTree.label, gMemRow9]
    exact memDecomposeSkel_bounded hcell hhd htl
  | sub hs hu' =>
    simp [NTree.children_node, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    rcases hs with hmem | rfl
    · exact hcs _ hmem _ hu'
    · exact inTree_walk_bounded E z tl htl _ hu'

theorem inTree_descentCont_axis3_bounded (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (hd tl : Noun)
    (hhd : FieldEmbedding.BoundedBy 769 hd)
    (htl : FieldEmbedding.BoundedBy 769 tl)
    (hcs : ∀ u ∈ cont, ∀ n, InTree u n → n.label.skel.BoundedBy 769)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ (genAnnotatedDescentCont E z lmb cont contCell contState (.cell hd tl) 3).1)
    (n : NTree (GenMemoryRow K)) (hn : InTree u n) :
    n.label.skel.BoundedBy 769 := by
  have hcell : FieldEmbedding.BoundedBy 769 (.cell hd tl) :=
    FieldEmbedding.BoundedBy_cell.mpr ⟨hhd, htl⟩
  rw [genAnnotatedDescentCont_axis3] at hu
  simp at hu
  subst u
  cases hn with
  | here =>
    simp [NTree.label, gMemRow9]
    exact memDecomposeSkel_bounded hcell hhd htl
  | sub hs hu' =>
    simp [NTree.children_node, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    rcases hs with rfl | hmem
    · exact inTree_walk_bounded E z hd hhd _ hu'
    · exact hcs _ hmem _ hu'

theorem inTree_chainedInner_one_axis2_bounded (E : Noun → ComputeTable.FP K)
    (z α : K) (prevRoot : Noun) (hd2 tl2 : Noun) (ePrev e2 : ℕ)
    (hprev : FieldEmbedding.BoundedBy 769 prevRoot)
    (hhd2 : FieldEmbedding.BoundedBy 769 hd2)
    (htl2 : FieldEmbedding.BoundedBy 769 tl2)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ (genAnnotatedChainedInner E z α lmb
        ⟨prevRoot, .cell hd2 tl2, 3, ePrev⟩
        [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1)
    (n : NTree (GenMemoryRow K)) (hn : InTree u n) :
    n.label.skel.BoundedBy 769 := by
  have hcell : FieldEmbedding.BoundedBy 769 (.cell hd2 tl2) :=
    FieldEmbedding.BoundedBy_cell.mpr ⟨hhd2, htl2⟩
  unfold genAnnotatedChainedInner at hu
  simp only [genAnnotatedChainedInner_nil, chainedInnerRootState] at hu
  simp at hu
  subst u
  cases hn with
  | here =>
    simp [NTree.label, gMemRow9]
    exact memReadSkelAx_bounded hcell hhd2 atom0_bounded
  | sub hs hu' =>
    simp [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    cases hu' with
    | here =>
      simp [NTree.label, gMemRow9]
      exact memVerifySkelAx_bounded hprev hcell
    | sub hs' hu'' =>
      exact inTree_descentCont_axis2_bounded E z
        [(genAnnotatedVerify E z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1]
        (genAnnotatedVerify E z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2
        .verify_child hd2 tl2 hhd2 htl2
        (fun w hw m hm => by
          simp [List.mem_cons, List.not_mem_nil, or_false] at hw
          subst w
          exact inTree_verify_bounded E z (.cell hd2 tl2) hd2 2 (α ^ e2) e2
            hcell hhd2 m hm)
        _ hs' _ hu''

theorem inTree_chained_axis3_axis2_bounded (E : Noun → ComputeTable.FP K)
    (z α : K) (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ)
    (hhd1 : FieldEmbedding.BoundedBy 769 hd1)
    (hhd2 : FieldEmbedding.BoundedBy 769 hd2)
    (htl2 : FieldEmbedding.BoundedBy 769 tl2)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t)
    (n : NTree (GenMemoryRow K)) (hn : InTree t n) :
    n.label.skel.BoundedBy 769 := by
  have hmid : FieldEmbedding.BoundedBy 769 (.cell hd2 tl2) :=
    FieldEmbedding.BoundedBy_cell.mpr ⟨hhd2, htl2⟩
  have hroot : FieldEmbedding.BoundedBy 769 (.cell hd1 (.cell hd2 tl2)) :=
    FieldEmbedding.BoundedBy_cell.mpr ⟨hhd1, hmid⟩
  unfold genAnnotatedChainedTree at ht
  simp only [chainedInnerRootState] at ht
  injection ht with ht
  subst t
  cases hn with
  | here =>
    simp [NTree.label, gMemRow9]
    exact memReadSkelAx_bounded hroot hmid atom0_bounded
  | sub hs hu =>
    simp [NTree.children_node] at hs
    exact inTree_descentCont_axis3_bounded E z
      (genAnnotatedChainedInner E z α lmb
        ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
        [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1
      (genAnnotatedChainedInner E z α lmb
        ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
        [⟨.cell hd2 tl2, hd2, 2, e2⟩]).2
      .read_root hd1 (.cell hd2 tl2) hhd1 hmid
      (fun u hu n hn =>
        inTree_chainedInner_one_axis2_bounded E z α
          (.cell hd1 (.cell hd2 tl2)) hd2 tl2 e1 e2 hroot hhd2 htl2 u hu n hn)
      _ hs _ hu

theorem genRowMemForest_singleton_axis3_bounded (z α : K) (hd tl : Noun) (e : ℕ)
    (hhd : FieldEmbedding.BoundedBy 769 hd)
    (htl : FieldEmbedding.BoundedBy 769 tl) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb [⟨.cell hd tl, tl, 3, e⟩],
      ∀ t, InTree u t → t.label.skel.BoundedBy 769 := by
  intro u hu t ht
  simp [genRowMemForest_singleton] at hu
  subst u
  exact inTree_record_axis3_bounded (encC z) z α hd tl e hhd htl t ht

theorem genRowMemForest_chain32_bounded (z α : K) (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ)
    (hhd1 : FieldEmbedding.BoundedBy 769 hd1)
    (hhd2 : FieldEmbedding.BoundedBy 769 hd2)
    (htl2 : FieldEmbedding.BoundedBy 769 tl2) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩],
      ∀ t, InTree u t → t.label.skel.BoundedBy 769 := by
  intro u hu t ht
  unfold genRowMemForest at hu
  simp only at hu
  cases h : genAnnotatedChainedTree (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some tree =>
    simp [h] at hu
    subst u
    exact inTree_chained_axis3_axis2_bounded (encC z) z α hd1 hd2 tl2 e1 e2
      hhd1 hhd2 htl2 tree h t ht

theorem genRowMemForest_three_chain32_bounded (z α : K)
    (hd1 hd2 tl2 hd3 tl3 : Noun) (e1 e2 e3 : ℕ)
    (hhd1 : FieldEmbedding.BoundedBy 769 hd1)
    (hhd2 : FieldEmbedding.BoundedBy 769 hd2)
    (htl2 : FieldEmbedding.BoundedBy 769 tl2)
    (hhd3 : FieldEmbedding.BoundedBy 769 hd3)
    (htl3 : FieldEmbedding.BoundedBy 769 tl3) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩,
       ⟨.cell hd3 tl3, hd3, 2, e3⟩],
      ∀ t, InTree u t → t.label.skel.BoundedBy 769 := by
  intro u hu t ht
  unfold genRowMemForest at hu
  cases h : genAnnotatedChainedTree (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some tree =>
    simp [h, List.mem_append, List.mem_singleton] at hu
    rcases hu with hmem | hmem
    · rw [hmem] at ht
      exact inTree_chained_axis3_axis2_bounded (encC z) z α hd1 hd2 tl2 e1 e2
        hhd1 hhd2 htl2 tree h t ht
    · rw [hmem] at ht
      exact inTree_record_axis2_bounded (encC z) z α hd3 tl3 e3 hhd3 htl3 t ht

theorem genMemForestFromTree_of_rowBounded (z α : K)
    (t : NTree (GenComputeRow K))
    (H : ∀ n, InTree t n →
      ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
        ∀ v, InTree u v → v.label.skel.BoundedBy 769)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb t)
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    v.label.skel.BoundedBy 769 := by
  suffices ∀ N t,
      NTree.size t ≤ N →
      (∀ n, InTree t n →
        ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
          ∀ v, InTree u v → v.label.skel.BoundedBy 769) →
      ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
        ∀ v, InTree u v → v.label.skel.BoundedBy 769 from
    this (NTree.size t) t le_rfl H u hu v hv
  intro N
  induction N with
  | zero =>
    intro t ht H u hu v hv
    cases t with
    | node g cs =>
      simp [NTree.size] at ht
  | succ N ih =>
    intro t ht H u hu v hv
    cases t with
    | node g cs =>
      simp [genMemForestFromTree] at hu
      rcases hu with hu | hu
      · exact H (.node g cs) (InTree.here _) u hu v hv
      · have recList :
            ∀ cs', (∀ c ∈ cs', c ∈ cs) →
              (∀ t ∈ cs', NTree.size t ≤ N) →
              (∀ t ∈ cs', ∀ n, InTree t n →
                ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
                  ∀ v, InTree u v → v.label.skel.BoundedBy 769) →
              ∀ u ∈ genMemForestFromList (encC z) z α lmb cs',
                ∀ v, InTree u v → v.label.skel.BoundedBy 769 := by
          intro cs' hsub hsz H' u' hu' v' hv'
          induction cs' generalizing u' v' with
          | nil => simp [genMemForestFromList] at hu'
          | cons c rest ihcs =>
            simp [genMemForestFromList] at hu'
            rcases hu' with hu' | hu'
            · exact ih c (hsz c (by simp))
                (fun n hn => H' c (by simp) n hn) u' hu' v' hv'
            · refine ihcs ?_ ?_ ?_ u' hu' v' hv'
              · intro c' hc'; exact hsub c' (List.mem_cons_of_mem _ hc')
              · intro t htt; exact hsz t (List.mem_cons_of_mem _ htt)
              · intro t htt; exact H' t (List.mem_cons_of_mem _ htt)
        refine recList cs (fun _ h => h) ?_
          (fun t ht n hn => H n (InTree.sub ht hn)) u hu v hv
        intro c hc
        have hin : NTree.size c ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
        have hsum : NTree.size c ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
        simp [NTree.size] at ht
        omega

theorem dotAssigned_rowBounded (z α : K)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTree (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v → v.label.skel.BoundedBy 769 := by
  have hnF : n ∈ bfsForest [bfsAssign (dotTree (K := K))] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels (dotTree (K := K))
  have hmem : n.label ∈ (bfsForest [bfsAssign (dotTree (K := K))]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTree (K := K))) hi
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests (dotTree (K := K)) i hi']
  rcases dot_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hget : (bfsRows (dotTree (K := K)))[0] = (dotTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 1).stamp 0 g.requests) hget]
    simp [dotTree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_bounded z α (.atom 6) dotCondFormula
      dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 1)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 2)
      b_atom6 b_dotCondFormula b_dotBranchPair b_dotThenFormula b_dotElseFormula
  · have hget : (bfsRows (dotTree (K := K)))[1] = (dotCondTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 2).stamp 0 g.requests) hget]
    simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_bounded z α (.atom 1) (.atom 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 2).stamp 0)
      b_atom1 atom0_bounded
  · have hget : (bfsRows (dotTree (K := K)))[2] = (dotOp2Tree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 3).stamp 0 g.requests) hget]
    simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]
    exact genRowMemForest_chain32_bounded z α (.atom 2) dotOp2B dotOp2C
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 1)
      b_atom2 b_dotOp2B b_dotOp2C
  · have hget : (bfsRows (dotTree (K := K)))[3] = (dotOp1BTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 4).stamp 0 g.requests) hget]
    simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_bounded z α (.atom 1)
      (.cell (.atom 0) (.atom 1))
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 4).stamp 0)
      b_atom1 (FieldEmbedding.BoundedBy_cell.mpr ⟨atom0_bounded, b_atom1⟩)
  · have hget : (bfsRows (dotTree (K := K)))[4] = (dotOp1CTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 5).stamp 0 g.requests) hget]
    simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_bounded z α (.atom 1) dotOp9Formula
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 5).stamp 0)
      b_atom1 b_dotOp9Formula
  · have hget : (bfsRows (dotTree (K := K)))[5] = (dotOp9Tree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 6).stamp 0 g.requests) hget]
    simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_bounded z α (.atom 9) (.atom 2)
      dotCoreFormula dotElem0 dotElem1
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 1)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 2)
      b_atom9 b_atom2 b_dotCoreFormula b_dotElem0 b_dotElem1
  · have hget : (bfsRows (dotTree (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 7).stamp 0 g.requests) hget]
    simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_bounded z α (.atom 1) dotCore
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 7).stamp 0)
      b_atom1 b_dotCore
  · have hget : (bfsRows (dotTree (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 8).stamp 0 g.requests) hget]
    simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_bounded z α (.atom 1) (.atom 3)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 8).stamp 0)
      b_atom1 (by simp [FieldEmbedding.BoundedBy])

theorem assignedForest_inTree_bounded (z α : K)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K))))
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    v.label.skel.BoundedBy 769 :=
  genMemForestFromTree_of_rowBounded z α _ (dotAssigned_rowBounded z α) u hu v hv

theorem dotAssigned_rowBounded_air (z α : K)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTreeAir (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      ∀ v, InTree u v → v.label.skel.BoundedBy 769 := by
  have hnF : n ∈ bfsForest [bfsAssign (dotTreeAir (K := K))] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels (dotTreeAir (K := K))
  have hmem : n.label ∈ (bfsForest [bfsAssign (dotTreeAir (K := K))]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := (dotTreeAir (K := K))) hi
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests (dotTreeAir (K := K)) i hi']
  rcases dot_air_bfs_index i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hget : (bfsRows (dotTreeAir (K := K)))[0] = (dotTreeAir (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0 g.requests) hget]
    simp [dotTreeAir, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_bounded z α (.atom 6) dotCondFormula
      dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 1)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 1).stamp 2)
      b_atom6 b_dotCondFormula b_dotBranchPair b_dotThenFormula b_dotElseFormula
  · have hget : (bfsRows (dotTreeAir (K := K)))[1] = (dotOp2Tree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0 g.requests) hget]
    simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]
    exact genRowMemForest_chain32_bounded z α (.atom 2) dotOp2B dotOp2C
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 2).stamp 1)
      b_atom2 b_dotOp2B b_dotOp2C
  · have hget : (bfsRows (dotTreeAir (K := K)))[2] = (dotCondTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0 g.requests) hget]
    simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_bounded z α (.atom 1) (.atom 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 3).stamp 0)
      b_atom1 atom0_bounded
  · have hget : (bfsRows (dotTreeAir (K := K)))[3] = (dotOp1BTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0 g.requests) hget]
    simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_bounded z α (.atom 1)
      (.cell (.atom 0) (.atom 1))
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 4).stamp 0)
      b_atom1 (FieldEmbedding.BoundedBy_cell.mpr ⟨atom0_bounded, b_atom1⟩)
  · have hget : (bfsRows (dotTreeAir (K := K)))[4] = (dotOp1CTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0 g.requests) hget]
    simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_bounded z α (.atom 1) dotOp9Formula
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 5).stamp 0)
      b_atom1 b_dotOp9Formula
  · have hget : (bfsRows (dotTreeAir (K := K)))[5] = (dotOp9Tree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0 g.requests) hget]
    simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_bounded z α (.atom 9) (.atom 2)
      dotCoreFormula dotElem0 dotElem1
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 0)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 1)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 6).stamp 2)
      b_atom9 b_atom2 b_dotCoreFormula b_dotElem0 b_dotElem1
  · have hget : (bfsRows (dotTreeAir (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0 g.requests) hget]
    simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_bounded z α (.atom 1) dotCore
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 7).stamp 0)
      b_atom1 b_dotCore
  · have hget : (bfsRows (dotTreeAir (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
      simp [dot_air_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0 g.requests) hget]
    simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_bounded z α (.atom 1) (.atom 3)
      (getRecordExp (bfsLabelAt (dotTreeAir (K := K)) 8).stamp 0)
      b_atom1 (by simp [FieldEmbedding.BoundedBy])

theorem assignedForest_inTree_bounded_air (z α : K)
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTreeAir (K := K))))
    (v : NTree (GenMemoryRow K)) (hv : InTree u v) :
    v.label.skel.BoundedBy 769 :=
  genMemForestFromTree_of_rowBounded z α _ (dotAssigned_rowBounded_air z α) u hu v hv

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

noncomputable section

theorem semanticSkeleton_computeRows (z α : K) :
    computeSkeletonRows (semanticSkeleton z α) =
      [(dotTreeAir (K := K)).label.skel,
       (dotOp2Tree (K := K)).label.skel,
       (dotCondTree (K := K)).label.skel,
       (dotOp1BTree (K := K)).label.skel,
       (dotOp1CTree (K := K)).label.skel,
       (dotOp9Tree (K := K)).label.skel,
       (dotOp9CoreTree (K := K)).label.skel,
       (dotOp9InvokeTree (K := K)).label.skel] := by
  rw [semanticSkeleton, computeSkeletonRows_genSemantic,
    computeSkeletonRows_genCompute, bfsAssign_skel_list]
  simp [dot_air_bfsForest]

theorem semanticSkeleton_memoryRows (z α : K) :
    (memorySkeletonRows (semanticSkeleton z α)).Forall
      (MemoryRowSkeleton.BoundedBy 769) := by
  rw [semanticSkeleton, memorySkeletonRows_genSemantic]
  refine List.forall_iff_forall_mem.mpr ?_
  intro x hx
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ n).mp hn
  unfold assignedForest at hu
  exact assignedForest_inTree_bounded_air z α u hu n hin

theorem semanticSkeleton_bounded (z α : K) :
    (semanticSkeleton z α).BoundedBy 769 := by
  refine ⟨?_, semanticSkeleton_memoryRows z α, ?_⟩
  · rw [semanticSkeleton_computeRows]
    exact ⟨by simp [dotTreeAir, skelNode]; exact b_dotOp6Skel,
      by simp [dotOp2Tree, skelNode]; exact b_dotOp2Skel,
      b_dotCondSkel,
      b_dotOp1BSkel, b_dotOp1CSkel,
      by simp [dotOp9Tree, skelNode]; exact b_dotOp9Skel,
      b_dotOp9CoreSkel, b_dotOp9InvokeSkel⟩
  · intro tree htree node hnode
    have hmem : node.label ∈ memorySkeletonRows (semanticSkeleton z α) := by
      refine List.mem_map.mpr ⟨node, ?_, rfl⟩
      exact (mem_bfsForest _ node).mpr ⟨tree, htree, hnode⟩
    exact List.forall_iff_forall_mem.mp (semanticSkeleton_memoryRows z α) _ hmem

theorem nounRealization_seed :
    ExactExecutionNounRealization 769 (cfg seedZ alphaA)
      (execThreaded seedZ alphaA) :=
  BindsAt.nounRealization seedZ_ne_zero
    (semanticSkeleton_bounded seedZ alphaA) bindsAt_seed

end

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.semanticSkeleton_bounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.nounRealization_seed
