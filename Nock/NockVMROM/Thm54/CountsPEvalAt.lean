/-
  Nock/NockVMROM/Thm54/CountsPEvalAt.lean

  Domain-lift of `indP` / `countsP` at the timestamp base `α`, not at
  `Inputs.z`.  `ChallengeVector.z` / `Inputs.z` is the NPR fingerprint
  seed (`AxisSoundness`); record timestamps are `α^e`.
  `AxisBridge.WF` / `countsP_eval` evaluate at `inp.z` and therefore
  cannot inhabit both `Vmem` (needs `z = nprSeed`) and `TsNode`
  (needs `z = α`).  `WFAt` splits them.
-/
import Nock.AxisBridge
import Nock.NockVM
import Nock.Walk

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.CountsPEvalAt

open Nock
open Nock.Walk
open Nock.NockVM
open Nock.MemoryTable
open Nock.AxisBridge
open Nock.AxisBridge.MemWalk
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open scoped Polynomial
open Polynomial

variable {K : Type*} [Field K]

/-- `WF` with timestamp base `α` and verifier inputs `inp` (NPR seed). -/
def WFAt (inp : Inputs K) (α : K) : MemWalk K → Prop
  | .halt row =>
      row.st = MState.halt ∧ Vmem inp row
  | .decompose row l r =>
      row.st = MState.decompose ∧ Vmem inp row
        ∧ row.lc = l.rootRow.pt ∧ row.rc = r.rootRow.pt
        ∧ WFAt inp α l ∧ WFAt inp α r
  | .read row e c =>
      row.st = MState.read_root ∧ Vmem inp row ∧ row.mem.ts = α ^ e
        ∧ row.lc = c.rootRow.pt ∧ WFAt inp α c
  | .verify row e c =>
      row.st = MState.verify_child ∧ Vmem inp row ∧ row.mem.ts = α ^ e
        ∧ row.lc = c.rootRow.pt ∧ WFAt inp α c

/-- `TsNode` at the timestamp base, not at `inp.z`. -/
def TsNodeAt (E : NTree (MState × DTmem K) → ℕ) (α : K)
    (t : NTree (MState × DTmem K)) : Prop :=
  TsNode E { z := α, β := 0, γ := 0 } t

theorem indP_eval_at (inp : Inputs K) (α : K) (lmb : K) (T : ℕ → K) :
    ∀ w : MemWalk K, WFAt inp α w → sameLambda lmb w → readAxis T w →
      (indP w.toMTree lmb T).eval α = w.rootRow.pt.indicator := by
  intro w
  induction w with
  | halt row =>
      intro hw hlam _hT
      obtain ⟨hst, hV⟩ := hw
      unfold Vmem at hV
      have hEq := hV.2.1
      simp only [eqBlk, hst] at hEq
      simp only [MemWalk.toMTree, indP, eval_zero, MemWalk.rootRow]
      exact hEq.2.2.1.symm
  | decompose row l r ihl ihr =>
      intro hw hlam hT
      obtain ⟨hst, hV, hlc, hrc, hWl, hWr⟩ := hw
      obtain ⟨hlamrow, hlaml, hlamr⟩ := hlam
      obtain ⟨hTl, hTr⟩ := hT
      unfold Vmem at hV
      have hEq := hV.2.1
      simp only [eqBlk, hst] at hEq
      simp only [MemWalk.toMTree, indP, eval_mul, eval_C, eval_add, MemWalk.rootRow]
      rw [ihl hWl hlaml hTl, ihr hWr hlamr hTr, hEq.2.1, hlc, hrc, hlamrow]
  | read row e c ih =>
      intro hw hlam hT
      obtain ⟨hst, hV, hts, hlc, hWc⟩ := hw
      obtain ⟨hlamrow, hlamc⟩ := hlam
      obtain ⟨hTrow, hTc⟩ := hT
      unfold Vmem at hV
      have hEq := hV.2.1
      simp only [eqBlk, hst] at hEq
      simp only [MemWalk.toMTree, indP, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
        MemWalk.rootRow, pwScale]
      rw [ih hWc hlamc hTc, hEq.2.2.1, hlc, hts, hlamrow, hTrow]
      ring
  | verify row e c ih =>
      intro hw hlam hT
      obtain ⟨hst, hV, hts, hlc, hWc⟩ := hw
      obtain ⟨hlamrow, hlamc⟩ := hlam
      unfold Vmem at hV
      have hEq := hV.2.1
      simp only [eqBlk, hst] at hEq
      simp only [MemWalk.toMTree, indP, eval_add, eval_mul, eval_C, eval_pow, eval_X,
        MemWalk.rootRow, pwScale]
      rw [ih hWc hlamc hT, hEq.2.2.1, hlc, hts, hlamrow]

theorem countsP_eval_at (inp : Inputs K) (α : K) (lmb : K) (T C' : ℕ → K) :
    ∀ w : MemWalk K, WFAt inp α w → sameLambda lmb w → readAxis T w → readCprime C' w →
      (countsP w.toMTree lmb T C').eval α = w.rootRow.pt.counts := by
  intro w
  induction w with
  | halt row =>
      intro hw hlam _hT _hC
      obtain ⟨hst, hV⟩ := hw
      unfold Vmem at hV
      have hEq := hV.2.1
      simp only [eqBlk, hst] at hEq
      simp only [MemWalk.toMTree, countsP, eval_zero, MemWalk.rootRow]
      exact hEq.2.2.2.1.symm
  | decompose row l r ihl ihr =>
      intro hw hlam hT hC
      obtain ⟨hst, hV, hlc, hrc, hWl, hWr⟩ := hw
      obtain ⟨hlamrow, hlaml, hlamr⟩ := hlam
      obtain ⟨hTl, hTr⟩ := hT
      obtain ⟨hCl, hCr⟩ := hC
      unfold Vmem at hV
      have hEq := hV.2.1
      simp only [eqBlk, hst] at hEq
      simp only [MemWalk.toMTree, countsP, eval_add, eval_mul, eval_C, eval_sub, MemWalk.rootRow]
      rw [ihl hWl hlaml hTl hCl, ihr hWr hlamr hTr hCr,
          indP_eval_at inp α lmb T l hWl hlaml hTl, indP_eval_at inp α lmb T r hWr hlamr hTr]
      rw [hEq.2.2.1, hlc, hrc, hlamrow]
  | read row e c ih =>
      intro hw hlam hT hC
      obtain ⟨hst, hV, hts, hlc, hWc⟩ := hw
      obtain ⟨hlamrow, hlamc⟩ := hlam
      obtain ⟨hTrow, hTc⟩ := hT
      obtain ⟨hCrow, hCc⟩ := hC
      unfold Vmem at hV
      have hEq := hV.2.1
      simp only [eqBlk, hst] at hEq
      simp only [MemWalk.toMTree, countsP, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
        MemWalk.rootRow]
      rw [ih hWc hlamc hTc hCc, hEq.2.2.2.1, hlc, hts, hCrow, hTrow]
  | verify row e c ih =>
      intro hw hlam hT hC
      obtain ⟨hst, hV, hts, hlc, hWc⟩ := hw
      obtain ⟨hlamrow, hlamc⟩ := hlam
      unfold Vmem at hV
      have hEq := hV.2.1
      simp only [eqBlk, hst] at hEq
      simp only [MemWalk.toMTree, countsP, eval_add, eval_mul, eval_C, eval_pow, eval_X,
        MemWalk.rootRow, pwScale]
      rw [ih hWc hlamc hT hC, hEq.2.2.2.1, hlc, hts, hlamrow]

/-- AIR-forest assembly at timestamp base `α`.  `Vmem` / `ChainNode` come
    from `RVT Fmem`; only `TsNodeAt` is the monomial `α^e`. -/
theorem wfAt_ofNTree (E : NTree (MState × DTmem K) → ℕ) (inp : Inputs K) (α : K)
    (root : NTree (MState × DTmem K))
    (hrvt : RVT (Fmem (K := K)) root)
    (hinp : ∀ t', InTree root t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree root t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree root t' → TsNodeAt E α t') :
    WFAt inp α (ofNTree E root) := by
  suffices H : ∀ n : ℕ, ∀ root : NTree (MState × DTmem K), sizeOf root ≤ n →
      RVT (Fmem (K := K)) root →
      (∀ t', InTree root t' → (NTree.label t').2.1 = inp) →
      (∀ t', InTree root t' → fanoutMem (NTree.label t').1 = (NTree.children t').length) →
      (∀ t', InTree root t' → TsNodeAt E α t') →
      WFAt inp α (ofNTree E root) by
    exact H (sizeOf root) root le_rfl hrvt hinp hshape hts
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro root hn hrvt hinp hshape hts
    have hFcon := (RVT_iff_forall_InTree (Fmem (K := K)) root).mp hrvt
      root (InTree.here root)
    have hshR := hshape root (InTree.here root)
    have hchR := chainNode_of_Fcon root hFcon hshR
    have htsR := hts root (InTree.here root)
    have hinpR := hinp root (InTree.here root)
    cases root with
    | node lbl ch =>
      obtain ⟨s, d⟩ := lbl
      simp only [NTree.label_node, NTree.children_node] at hFcon hshR hchR htsR hinpR hn
      have hstrow : d.2.st = s := hFcon.1.1
      have hVm : Vmem d.1 d.2 := hFcon.1.2.1
      rw [hinpR] at hVm
      cases s
      · have hlen : ch.length = 2 := by
          have := hshR; simp only [fanoutMem] at this; omega
        obtain ⟨l, r, rfl⟩ := List.length_eq_two.mp hlen
        have hRootL : InTree (NTree.node (MState.decompose, d) [l, r]) l :=
          InTree.sub (by simp) (InTree.here l)
        have hRootR : InTree (NTree.node (MState.decompose, d) [l, r]) r :=
          InTree.sub (by simp) (InTree.here r)
        have hszL : sizeOf l < sizeOf (NTree.node (MState.decompose, d) [l, r]) := by
          simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
        have hszR : sizeOf r < sizeOf (NTree.node (MState.decompose, d) [l, r]) := by
          simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
        simp only [ChainNode, NTree.label_node, NTree.children_node] at hchR
        rw [ofNTree_decompose]
        refine ⟨hstrow, hVm, ?_, ?_, ?_, ?_⟩
        · rw [rootRow_ofNTree]; exact hchR.1
        · rw [rootRow_ofNTree]; exact hchR.2
        · exact ih (sizeOf l) (by omega) l le_rfl
            (RVT_of_InTree hrvt hRootL)
            (fun t' ht' => hinp t' (InTree_trans hRootL ht'))
            (fun t' ht' => hshape t' (InTree_trans hRootL ht'))
            (fun t' ht' => hts t' (InTree_trans hRootL ht'))
        · exact ih (sizeOf r) (by omega) r le_rfl
            (RVT_of_InTree hrvt hRootR)
            (fun t' ht' => hinp t' (InTree_trans hRootR ht'))
            (fun t' ht' => hshape t' (InTree_trans hRootR ht'))
            (fun t' ht' => hts t' (InTree_trans hRootR ht'))
      · have hlen : ch.length = 0 := by
          have := hshR; simp only [fanoutMem] at this; omega
        obtain rfl := List.length_eq_zero_iff.mp hlen
        rw [ofNTree_halt]
        exact ⟨hstrow, hVm⟩
      · have hlen : ch.length = 1 := by
          have := hshR; simp only [fanoutMem] at this; omega
        obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hlen
        have hRootC : InTree (NTree.node (MState.read_root, d) [c]) c :=
          InTree.sub (by simp) (InTree.here c)
        have hszC : sizeOf c < sizeOf (NTree.node (MState.read_root, d) [c]) := by
          simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
        simp only [ChainNode, NTree.label_node, NTree.children_node] at hchR
        simp only [TsNodeAt, TsNode, NTree.label_node] at htsR
        rw [ofNTree_read]
        refine ⟨hstrow, hVm, ?_, ?_, ?_⟩
        · exact htsR
        · rw [rootRow_ofNTree]; exact hchR
        · exact ih (sizeOf c) (by omega) c le_rfl
            (RVT_of_InTree hrvt hRootC)
            (fun t' ht' => hinp t' (InTree_trans hRootC ht'))
            (fun t' ht' => hshape t' (InTree_trans hRootC ht'))
            (fun t' ht' => hts t' (InTree_trans hRootC ht'))
      · have hlen : ch.length = 1 := by
          have := hshR; simp only [fanoutMem] at this; omega
        obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hlen
        have hRootC : InTree (NTree.node (MState.verify_child, d) [c]) c :=
          InTree.sub (by simp) (InTree.here c)
        have hszC : sizeOf c < sizeOf (NTree.node (MState.verify_child, d) [c]) := by
          simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
        simp only [ChainNode, NTree.label_node, NTree.children_node] at hchR
        simp only [TsNodeAt, TsNode, NTree.label_node] at htsR
        rw [ofNTree_verify]
        refine ⟨hstrow, hVm, ?_, ?_, ?_⟩
        · exact htsR
        · rw [rootRow_ofNTree]; exact hchR
        · exact ih (sizeOf c) (by omega) c le_rfl
            (RVT_of_InTree hrvt hRootC)
            (fun t' ht' => hinp t' (InTree_trans hRootC ht'))
            (fun t' ht' => hshape t' (InTree_trans hRootC ht'))
            (fun t' ht' => hts t' (InTree_trans hRootC ht'))

end Nock.NockVMROM.Thm54.CountsPEvalAt
