/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAMem.lean

  Memory-side lift of the Tier A generated forest toward `MemoryNodesOK`.

  The annotated builder walks every noun (`genAnnotatedNounWalk`): halt at
  an atom, decompose at a cell, so `verify_child` and off-path siblings
  match `fanoutMem`.  Every tree of
  `genMemForestFromTree (bfsAssign dotTree)` inhabits `MemoryNodesOK`.

  `BuildableNockExecution` CORE / `Data` over K3 are not claimed.  F97's
  cubic `K3` has `|K*|` 2-adic valuation 5, so the honest orbit is at most
  `2^5 = 32` rows.  The OP6 branch-pair axis-2 record alone has 39 nodes
  (`dotBranchPairRecord_size`); `dotMemForest_exceeds_F97_orbit` records
  that the generated forest does not fit.  No cubic over `ZMod 97` can.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAData

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open MemoryTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Halt leaves -/

theorem gMemRow9_halt_bind (z : K) (a : ℕ) :
    BindMemoryRowA z (memHaltSkel a)
      (gMemRow9 (memHaltSkel a) 0 z (op9HaltPub (encC z) a)).row := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simpa [gMemRow9, op9HaltPub, memHaltSkel] using bindFP_encC z (.atom a)
  · intro i
    have hi : ¬ ((i : ℕ) < fanoutMem (memHaltSkel a).state) := by
      simp [memHaltSkel, fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem gMemRow9_halt_specializes (z α : K) (a : ℕ) :
    MemoryTimestampSpecializesAt α
      (gMemRow9 (memHaltSkel a) 0 z (op9HaltPub (encC z) a)).stamp
      (gMemRow9 (memHaltSkel a) 0 z (op9HaltPub (encC z) a)).row := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [gMemRow9, op9HaltPub, memHaltSkel, memoryMemRecKind, ComputeTable.MemRec.zero]
  · intro _
    rfl

theorem gMemRow9_halt_nodeOK (z α : K) (a : ℕ) :
    MemoryNodeOK z α
      (.node (gMemRow9 (memHaltSkel a) 0 z (op9HaltPub (encC z) a)).node []) := by
  refine ⟨?_, rfl, gMemRow9_halt_bind z a, gMemRow9_halt_specializes z α a⟩
  simp [gMemRow9, memHaltSkel, fanoutMem, GenMemoryRow.node]

theorem genHaltNodes_atom_OK (z α : K) (a : ℕ) :
    MemoryNodesOK z α
      (mapNTree GenMemoryRow.node
        (.node (gMemRow9 (memHaltSkel a) 0 z (op9HaltPub (encC z) a)) [])) := by
  simp [mapNTree]
  exact MemoryNodesOK.mk' (gMemRow9_halt_nodeOK z α a) (by simp)

/-! ## Annotated row binding -/

theorem gMemRow9_read_bind (z : K) (root child : Noun) (ax e : ℕ)
    (lcCell : Cell K) (ts ipre icur : K)
    (hlc : bindFP z root lcCell.noun) :
    BindMemoryRowA z (memReadSkelAx root child ax)
      (gMemRow9 (memReadSkelAx root child ax) e z
        (annotatedReadPub (encC z) root child ax ts lcCell ipre icur lmb)).row := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simpa [gMemRow9, annotatedReadPub, memReadSkelAx] using bindFP_encC z root
  · intro i
    fin_cases i
    · rw [dif_pos (by simp [memReadSkelAx, fanoutMem])]
      simpa [gMemRow9, annotatedReadPub, memReadSkelAx, memoryChildCell] using hlc
    · rw [dif_neg (by simp [memReadSkelAx, fanoutMem])]
      rfl
  · simp only [gMemRow9, annotatedReadPub, memReadSkelAx, memoryMemRecKind]
    exact ⟨bindFP_encC z root, bindFP_encC z child, rfl⟩

theorem gMemRow9_read_specializes (z α : K) (root child : Noun) (ax e : ℕ)
    (lcCell : Cell K) (ipre icur : K) :
    MemoryTimestampSpecializesAt α
      (gMemRow9 (memReadSkelAx root child ax) e z
        (annotatedReadPub (encC z) root child ax (α ^ e) lcCell ipre icur lmb)).stamp
      (gMemRow9 (memReadSkelAx root child ax) e z
        (annotatedReadPub (encC z) root child ax (α ^ e) lcCell ipre icur lmb)).row := by
  refine ⟨rfl, rfl, ?_, fun h => by
    simp [gMemRow9, memReadSkelAx, memoryMemRecKind] at h⟩
  simp [gMemRow9, annotatedReadPub, memReadSkelAx, memoryMemRecKind]

theorem gMemRow9_verify_bind (z : K) (root child : Noun) (ax e : ℕ)
    (lcCell : Cell K) (ts ipre icur : K)
    (hlc : bindFP z child lcCell.noun) :
    BindMemoryRowA z (memVerifySkelAx root child ax)
      (gMemRow9 (memVerifySkelAx root child ax) e z
        (annotatedVerifyPub (encC z) root child ax ts lcCell ipre icur lmb)).row := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simpa [gMemRow9, annotatedVerifyPub, memVerifySkelAx] using bindFP_encC z child
  · intro i
    fin_cases i
    · rw [dif_pos (by simp [memVerifySkelAx, fanoutMem])]
      simpa [gMemRow9, annotatedVerifyPub, memVerifySkelAx, memoryChildCell] using hlc
    · rw [dif_neg (by simp [memVerifySkelAx, fanoutMem])]
      rfl
  · simp only [gMemRow9, annotatedVerifyPub, memVerifySkelAx, memoryMemRecKind]
    exact ⟨bindFP_encC z root, bindFP_encC z child, rfl⟩

theorem gMemRow9_verify_specializes (z α : K) (root child : Noun) (ax e : ℕ)
    (lcCell : Cell K) (ipre icur : K) :
    MemoryTimestampSpecializesAt α
      (gMemRow9 (memVerifySkelAx root child ax) e z
        (annotatedVerifyPub (encC z) root child ax (α ^ e) lcCell ipre icur lmb)).stamp
      (gMemRow9 (memVerifySkelAx root child ax) e z
        (annotatedVerifyPub (encC z) root child ax (α ^ e) lcCell ipre icur lmb)).row := by
  refine ⟨rfl, rfl, ?_, fun h => by
    simp [gMemRow9, memVerifySkelAx, memoryMemRecKind] at h⟩
  simp [gMemRow9, annotatedVerifyPub, memVerifySkelAx, memoryMemRecKind]

theorem gMemRow9_dec_bind (z : K) (parent head tail : Noun) (e : ℕ)
    (lcCell rcCell : Cell K) (lcSt rcSt : MState) (ipre icur : K)
    (hlc : bindFP z head lcCell.noun) (hrc : bindFP z tail rcCell.noun) :
    BindMemoryRowA z (memDecomposeSkel parent head tail)
      (gMemRow9 (memDecomposeSkel parent head tail) e z
        (annotatedDecPub (encC z) parent head tail lcCell rcCell lcSt rcSt ipre icur lmb)).row := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simpa [gMemRow9, annotatedDecPub, memDecomposeSkel] using bindFP_encC z parent
  · intro i
    fin_cases i
    · simp [gMemRow9, annotatedDecPub, memDecomposeSkel, fanoutMem, memoryChildCell]
      exact hlc
    · simp [gMemRow9, annotatedDecPub, memDecomposeSkel, fanoutMem, memoryChildCell]
      exact hrc
  · rfl

theorem gMemRow9_dec_specializes (z α : K) (parent head tail : Noun) (e : ℕ)
    (lcCell rcCell : Cell K) (lcSt rcSt : MState) (ipre icur : K) :
    MemoryTimestampSpecializesAt α
      (gMemRow9 (memDecomposeSkel parent head tail) e z
        (annotatedDecPub (encC z) parent head tail lcCell rcCell lcSt rcSt ipre icur lmb)).stamp
      (gMemRow9 (memDecomposeSkel parent head tail) e z
        (annotatedDecPub (encC z) parent head tail lcCell rcCell lcSt rcSt ipre icur lmb)).row := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp [gMemRow9, annotatedDecPub, memDecomposeSkel, memoryMemRecKind,
      ComputeTable.MemRec.zero]
  · intro _
    rfl

/-! ## Noun walk -/

theorem genAnnotatedNounWalk_OK (z α : K) :
    ∀ n, MemoryNodesOK z α
      (mapNTree GenMemoryRow.node (genAnnotatedNounWalk (encC z) z lmb n).1)
  | .atom a => by
      simp [genAnnotatedNounWalk]
      exact genHaltNodes_atom_OK z α a
  | .cell h t => by
      simp only [genAnnotatedNounWalk, mapNTree]
      refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
      · simp [gMemRow9, memDecomposeSkel, fanoutMem, GenMemoryRow.node]
      · exact gMemRow9_dec_bind z (.cell h t) h t 0
          (genAnnotatedNounWalk (encC z) z lmb h).2
          (genAnnotatedNounWalk (encC z) z lmb t).2
          (nounWalkRootState h) (nounWalkRootState t) 0 0
          (by simpa [genAnnotatedNounWalk_pt_noun] using bindFP_encC z h)
          (by simpa [genAnnotatedNounWalk_pt_noun] using bindFP_encC z t)
      · exact gMemRow9_dec_specializes z α (.cell h t) h t 0
          (genAnnotatedNounWalk (encC z) z lmb h).2
          (genAnnotatedNounWalk (encC z) z lmb t).2
          (nounWalkRootState h) (nounWalkRootState t) 0 0
      intro c hc
      simp at hc
      rcases hc with rfl | rfl
      · exact genAnnotatedNounWalk_OK z α h
      · exact genAnnotatedNounWalk_OK z α t

theorem genAnnotatedVerify_OK (z α : K) (root child : Noun) (ax e : ℕ) :
    MemoryNodesOK z α
      (mapNTree GenMemoryRow.node
        (genAnnotatedVerify (encC z) z lmb root child ax (α ^ e) e).1) := by
  simp only [genAnnotatedVerify, mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · simp [gMemRow9, memVerifySkelAx, fanoutMem, GenMemoryRow.node]
  · exact gMemRow9_verify_bind z root child ax e
      (genAnnotatedNounWalk (encC z) z lmb child).2 (α ^ e) 0 0
      (by simpa [genAnnotatedNounWalk_pt_noun] using bindFP_encC z child)
  · exact gMemRow9_verify_specializes z α root child ax e
      (genAnnotatedNounWalk (encC z) z lmb child).2 0 0
  intro c hc
  simp at hc
  subst c
  exact genAnnotatedNounWalk_OK z α child

theorem genAnnotatedVerify_cell_children (E : Noun → ComputeTable.FP K) (z : K)
    (root hd tl : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    (genAnnotatedVerify E z lmb root (.cell hd tl) ax ts recordExp).1.children.length = 1 := by
  simp [genAnnotatedVerify]

/-! ## Axis-2/3 annotated record trees -/

theorem genAnnotatedRecordTree_axis3_OK (z α : K) (hd tl : Noun) (e : ℕ) :
    MemoryNodesOK z α
      (mapNTree GenMemoryRow.node
        (genAnnotatedRecordTree (encC z) z α lmb (.cell hd tl) tl 3 e)) := by
  unfold genAnnotatedRecordTree
  unfold genAnnotatedDescent
  simp only [show ¬((3 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_three, axisRest_three, ↓reduceIte]
  unfold genAnnotatedDescent
  simp only [show (1 : ℕ) < 2 from by omega, ite_true,
    genAnnotatedVerify, List.cons_append, List.nil_append]
  simp only [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · simp [gMemRow9, memReadSkelAx, fanoutMem, GenMemoryRow.node]
  · exact gMemRow9_read_bind z (.cell hd tl) tl 3 e
      (annotatedDecPub (encC z) (.cell hd tl) hd tl
        (genAnnotatedNounWalk (encC z) z lmb hd).2
        (annotatedVerifyPub (encC z) (.cell hd tl) tl 3 (α ^ e)
          (genAnnotatedNounWalk (encC z) z lmb tl).2 0 0 lmb).pt
        (nounWalkRootState hd) (descentRootState 1) 0 0 lmb).pt (α ^ e) 0 0
      (by simpa [annotatedDecPub] using bindFP_encC z (.cell hd tl))
  · exact gMemRow9_read_specializes z α (.cell hd tl) tl 3 e
      (annotatedDecPub (encC z) (.cell hd tl) hd tl
        (genAnnotatedNounWalk (encC z) z lmb hd).2
        (annotatedVerifyPub (encC z) (.cell hd tl) tl 3 (α ^ e)
          (genAnnotatedNounWalk (encC z) z lmb tl).2 0 0 lmb).pt
        (nounWalkRootState hd) (descentRootState 1) 0 0 lmb).pt 0 0
  intro c hc
  simp at hc
  subst c
  rw [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · simp [gMemRow9, memDecomposeSkel, fanoutMem, GenMemoryRow.node]
  · exact gMemRow9_dec_bind z (.cell hd tl) hd tl 0
      (genAnnotatedNounWalk (encC z) z lmb hd).2
      (annotatedVerifyPub (encC z) (.cell hd tl) tl 3 (α ^ e)
        (genAnnotatedNounWalk (encC z) z lmb tl).2 0 0 lmb).pt
      (nounWalkRootState hd) (descentRootState 1) 0 0
      (by simpa [genAnnotatedNounWalk_pt_noun] using bindFP_encC z hd)
      (by simpa [annotatedVerifyPub] using bindFP_encC z tl)
  · exact gMemRow9_dec_specializes z α (.cell hd tl) hd tl 0
      (genAnnotatedNounWalk (encC z) z lmb hd).2
      (annotatedVerifyPub (encC z) (.cell hd tl) tl 3 (α ^ e)
        (genAnnotatedNounWalk (encC z) z lmb tl).2 0 0 lmb).pt
      (nounWalkRootState hd) (descentRootState 1) 0 0
  intro d hdmem
  simp at hdmem
  rcases hdmem with rfl | rfl
  · exact genAnnotatedNounWalk_OK z α hd
  · exact genAnnotatedVerify_OK z α (.cell hd tl) tl 3 e

theorem genAnnotatedRecordTree_axis2_OK (z α : K) (hd tl : Noun) (e : ℕ) :
    MemoryNodesOK z α
      (mapNTree GenMemoryRow.node
        (genAnnotatedRecordTree (encC z) z α lmb (.cell hd tl) hd 2 e)) := by
  unfold genAnnotatedRecordTree
  unfold genAnnotatedDescent
  simp only [show ¬((2 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_two, axisRest_two, Bool.false_eq_true, ↓reduceIte]
  unfold genAnnotatedDescent
  simp only [show (1 : ℕ) < 2 from by omega, ite_true,
    genAnnotatedVerify, List.cons_append, List.nil_append]
  simp only [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · simp [gMemRow9, memReadSkelAx, fanoutMem, GenMemoryRow.node]
  · exact gMemRow9_read_bind z (.cell hd tl) hd 2 e
      (annotatedDecPub (encC z) (.cell hd tl) hd tl
        (annotatedVerifyPub (encC z) (.cell hd tl) hd 2 (α ^ e)
          (genAnnotatedNounWalk (encC z) z lmb hd).2 0 0 lmb).pt
        (genAnnotatedNounWalk (encC z) z lmb tl).2
        (descentRootState 1) (nounWalkRootState tl) 0 0 lmb).pt (α ^ e) 0 0
      (by simpa [annotatedDecPub] using bindFP_encC z (.cell hd tl))
  · exact gMemRow9_read_specializes z α (.cell hd tl) hd 2 e
      (annotatedDecPub (encC z) (.cell hd tl) hd tl
        (annotatedVerifyPub (encC z) (.cell hd tl) hd 2 (α ^ e)
          (genAnnotatedNounWalk (encC z) z lmb hd).2 0 0 lmb).pt
        (genAnnotatedNounWalk (encC z) z lmb tl).2
        (descentRootState 1) (nounWalkRootState tl) 0 0 lmb).pt 0 0
  intro c hc
  simp at hc
  subst c
  rw [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · simp [gMemRow9, memDecomposeSkel, fanoutMem, GenMemoryRow.node]
  · exact gMemRow9_dec_bind z (.cell hd tl) hd tl 0
      (annotatedVerifyPub (encC z) (.cell hd tl) hd 2 (α ^ e)
        (genAnnotatedNounWalk (encC z) z lmb hd).2 0 0 lmb).pt
      (genAnnotatedNounWalk (encC z) z lmb tl).2
      (descentRootState 1) (nounWalkRootState tl) 0 0
      (by simpa [annotatedVerifyPub] using bindFP_encC z hd)
      (by simpa [genAnnotatedNounWalk_pt_noun] using bindFP_encC z tl)
  · exact gMemRow9_dec_specializes z α (.cell hd tl) hd tl 0
      (annotatedVerifyPub (encC z) (.cell hd tl) hd 2 (α ^ e)
        (genAnnotatedNounWalk (encC z) z lmb hd).2 0 0 lmb).pt
      (genAnnotatedNounWalk (encC z) z lmb tl).2
      (descentRootState 1) (nounWalkRootState tl) 0 0
  intro d hdmem
  simp at hdmem
  rcases hdmem with rfl | rfl
  · exact genAnnotatedVerify_OK z α (.cell hd tl) hd 2 e
  · exact genAnnotatedNounWalk_OK z α tl

/-! ## Axis-3 quote-of-atom record tree -/

/-- Served tree of `*[subj [1 n]] = n` at axis 3: read → decompose → (halt 1, verify → halt n). -/
theorem genAnnotatedRecordTree_quoteAtom (z α : K) (n e : ℕ) :
    genAnnotatedRecordTree (encC z) z α lmb
        (.cell (.atom 1) (.atom n)) (.atom n) 3 e =
      .node (gMemRow9 (memReadSkelAx (.cell (.atom 1) (.atom n)) (.atom n) 3) e z
          (annotatedReadPub (encC z) (.cell (.atom 1) (.atom n)) (.atom n) 3 (α ^ e)
            (annotatedDecPub (encC z) (.cell (.atom 1) (.atom n)) (.atom 1) (.atom n)
              ⟨encC z (.atom 1), 0, 0⟩
              (annotatedVerifyPub (encC z) (.cell (.atom 1) (.atom n)) (.atom n) 3 (α ^ e)
                ⟨encC z (.atom n), 0, 0⟩ 0 0 lmb).pt
              .halt .verify_child 0 0 lmb).pt 0 0 lmb))
        [.node (gMemRow9 (memDecomposeSkel (.cell (.atom 1) (.atom n)) (.atom 1) (.atom n)) 0 z
            (annotatedDecPub (encC z) (.cell (.atom 1) (.atom n)) (.atom 1) (.atom n)
              ⟨encC z (.atom 1), 0, 0⟩
              (annotatedVerifyPub (encC z) (.cell (.atom 1) (.atom n)) (.atom n) 3 (α ^ e)
                ⟨encC z (.atom n), 0, 0⟩ 0 0 lmb).pt
              .halt .verify_child 0 0 lmb))
          [.node (gMemRow9 (memHaltSkel 1) 0 z (op9HaltPub (encC z) 1)) [],
           .node (gMemRow9 (memVerifySkelAx (.cell (.atom 1) (.atom n)) (.atom n) 3) e z
              (annotatedVerifyPub (encC z) (.cell (.atom 1) (.atom n)) (.atom n) 3 (α ^ e)
                ⟨encC z (.atom n), 0, 0⟩ 0 0 lmb))
             [.node (gMemRow9 (memHaltSkel n) 0 z (op9HaltPub (encC z) n)) []]]] := by
  unfold genAnnotatedRecordTree
  unfold genAnnotatedDescent
  simp only [show ¬((3 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_three, axisRest_three, axisZeroBits_three, ↓reduceIte]
  unfold genAnnotatedDescent
  simp only [show (1 : ℕ) < 2 from by omega, ite_true,
    genAnnotatedVerify, genAnnotatedNounWalk, List.cons_append, List.nil_append]
  rfl

theorem quoteAtomMemTree_OK (z α : K) (n e : ℕ) :
    MemoryNodesOK z α
      (mapNTree GenMemoryRow.node
        (genAnnotatedRecordTree (encC z) z α lmb
          (.cell (.atom 1) (.atom n)) (.atom n) 3 e)) :=
  genAnnotatedRecordTree_axis3_OK z α (.atom 1) (.atom n) e

/-! ## Concrete Tier A atom-result trees -/

theorem dotCondMemTree_OK (z α : K) (e : ℕ) :
    MemoryNodesOK z α
      (mapNTree GenMemoryRow.node
        (genAnnotatedRecordTree (encC z) z α lmb dotCondFormula dotCondResult 3 e)) := by
  simpa [dotCondFormula, dotCondResult] using quoteAtomMemTree_OK z α 0 e

theorem dotInvokeMemTree_OK (z α : K) (e : ℕ) :
    MemoryNodesOK z α
      (mapNTree GenMemoryRow.node
        (genAnnotatedRecordTree (encC z) z α lmb dotArm dotResult 3 e)) := by
  simpa [dotArm, dotElem0, dotResult] using quoteAtomMemTree_OK z α 3 e

theorem dotCondMemTree_OK_F97 :
    MemoryNodesOK seedZ alphaA
      (mapNTree GenMemoryRow.node
        (genAnnotatedRecordTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
          dotCondFormula dotCondResult 3 0)) :=
  dotCondMemTree_OK seedZ alphaA 0

theorem dotInvokeMemTree_OK_F97 :
    MemoryNodesOK seedZ alphaA
      (mapNTree GenMemoryRow.node
        (genAnnotatedRecordTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
          dotArm dotResult 3 0)) :=
  dotInvokeMemTree_OK seedZ alphaA 0

/-! ## Chained axis-3 then axis-2 -/

theorem genAnnotatedDescentCont_axis3 (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (hd tl : Noun) :
    genAnnotatedDescentCont E z lmb cont contCell contState (.cell hd tl) 3 =
      ([.node (gMemRow9 (memDecomposeSkel (.cell hd tl) hd tl) 0 z
          (annotatedDecPub E (.cell hd tl) hd tl
            (genAnnotatedNounWalk E z lmb hd).2 contCell
            (nounWalkRootState hd) (descentContRootState contState 1) 0 0 lmb))
          ([(genAnnotatedNounWalk E z lmb hd).1] ++ cont)],
        (annotatedDecPub E (.cell hd tl) hd tl
          (genAnnotatedNounWalk E z lmb hd).2 contCell
          (nounWalkRootState hd) (descentContRootState contState 1) 0 0 lmb).pt) := by
  unfold genAnnotatedDescentCont
  simp only [show ¬((3 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_three, axisRest_three, ↓reduceIte]
  unfold genAnnotatedDescentCont
  simp only [show (1 : ℕ) < 2 from by omega, ↓reduceIte, ite_true,
    List.cons_append, List.nil_append]

theorem genAnnotatedDescentCont_axis2 (E : Noun → ComputeTable.FP K) (z : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (hd tl : Noun) :
    genAnnotatedDescentCont E z lmb cont contCell contState (.cell hd tl) 2 =
      ([.node (gMemRow9 (memDecomposeSkel (.cell hd tl) hd tl) 0 z
          (annotatedDecPub E (.cell hd tl) hd tl
            contCell (genAnnotatedNounWalk E z lmb tl).2
            (descentContRootState contState 1) (nounWalkRootState tl) 0 0 lmb))
          (cont ++ [(genAnnotatedNounWalk E z lmb tl).1])],
        (annotatedDecPub E (.cell hd tl) hd tl
          contCell (genAnnotatedNounWalk E z lmb tl).2
          (descentContRootState contState 1) (nounWalkRootState tl) 0 0 lmb).pt) := by
  unfold genAnnotatedDescentCont
  simp only [show ¬((2 : ℕ) < 2) from by omega, formulaHead, formulaTail,
    axisTopBit_two, axisRest_two, Bool.false_eq_true, ↓reduceIte]
  unfold genAnnotatedDescentCont
  simp only [show (1 : ℕ) < 2 from by omega, ↓reduceIte, ite_true,
    List.cons_append, List.nil_append]

theorem genAnnotatedDescentCont_axis3_OK (z α : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (hd tl : Noun)
    (h1 : cont.length = 1)
    (hrc : bindFP z tl contCell.noun)
    (hcs : ∀ u ∈ cont, MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) :
    ∀ u ∈ (genAnnotatedDescentCont (encC z) z lmb cont contCell contState (.cell hd tl) 3).1,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  rw [genAnnotatedDescentCont_axis3] at hu
  simp at hu
  subst u
  simp only [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · have : ([(genAnnotatedNounWalk (encC z) z lmb hd).1] ++ cont).length = 2 := by
      simp [h1]
    simpa [gMemRow9, memDecomposeSkel, fanoutMem, GenMemoryRow.node, List.length_map]
  · exact gMemRow9_dec_bind z (.cell hd tl) hd tl 0
      (genAnnotatedNounWalk (encC z) z lmb hd).2 contCell
      (nounWalkRootState hd) (descentContRootState contState 1) 0 0
      (by simpa [genAnnotatedNounWalk_pt_noun] using bindFP_encC z hd) hrc
  · exact gMemRow9_dec_specializes z α (.cell hd tl) hd tl 0
      (genAnnotatedNounWalk (encC z) z lmb hd).2 contCell
      (nounWalkRootState hd) (descentContRootState contState 1) 0 0
  intro d hdmem
  simp at hdmem
  rcases hdmem with rfl | ⟨w, hw, rfl⟩
  · exact genAnnotatedNounWalk_OK z α hd
  · exact hcs w hw

theorem genAnnotatedDescentCont_axis2_OK (z α : K)
    (cont : List (NTree (GenMemoryRow K))) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) (hd tl : Noun)
    (h1 : cont.length = 1)
    (hlc : bindFP z hd contCell.noun)
    (hcs : ∀ u ∈ cont, MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) :
    ∀ u ∈ (genAnnotatedDescentCont (encC z) z lmb cont contCell contState (.cell hd tl) 2).1,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  rw [genAnnotatedDescentCont_axis2] at hu
  simp at hu
  subst u
  simp only [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · have : (cont ++ [(genAnnotatedNounWalk (encC z) z lmb tl).1]).length = 2 := by
      simp [h1]
    simpa [gMemRow9, memDecomposeSkel, fanoutMem, GenMemoryRow.node, List.length_map]
  · exact gMemRow9_dec_bind z (.cell hd tl) hd tl 0
      contCell (genAnnotatedNounWalk (encC z) z lmb tl).2
      (descentContRootState contState 1) (nounWalkRootState tl) 0 0
      hlc (by simpa [genAnnotatedNounWalk_pt_noun] using bindFP_encC z tl)
  · exact gMemRow9_dec_specializes z α (.cell hd tl) hd tl 0
      contCell (genAnnotatedNounWalk (encC z) z lmb tl).2
      (descentContRootState contState 1) (nounWalkRootState tl) 0 0
  intro d hdmem
  simp at hdmem
  rcases hdmem with ⟨w, hw, rfl⟩ | rfl
  · exact hcs w hw
  · exact genAnnotatedNounWalk_OK z α tl

theorem genAnnotatedChainedInner_nil (E : Noun → ComputeTable.FP K) (z α : K)
    (prev : MemRecordReq) :
    genAnnotatedChainedInner E z α lmb prev [] =
      ([ (genAnnotatedVerify E z lmb prev.root prev.child prev.axis
            (α ^ prev.recordExp) prev.recordExp).1 ],
       (genAnnotatedVerify E z lmb prev.root prev.child prev.axis
          (α ^ prev.recordExp) prev.recordExp).2) := rfl

theorem genAnnotatedVerify_pt_noun (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (recordExp : ℕ) :
    (genAnnotatedVerify E z lmb root child ax ts recordExp).2.noun = E child := by
  simp [genAnnotatedVerify, annotatedVerifyPub]

theorem genAnnotatedChainedInner_one_axis2_OK (z α : K)
    (prevRoot : Noun) (hd2 tl2 : Noun) (ePrev e2 : ℕ) :
    ∀ u ∈ (genAnnotatedChainedInner (encC z) z α lmb
        ⟨prevRoot, .cell hd2 tl2, 3, ePrev⟩
        [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1,
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  unfold genAnnotatedChainedInner at hu
  simp only [genAnnotatedChainedInner_nil, chainedInnerRootState] at hu
  simp at hu
  subst u
  simp only [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · simp [gMemRow9, memReadSkelAx, fanoutMem, GenMemoryRow.node]
  · exact gMemRow9_read_bind z (.cell hd2 tl2) hd2 2 e2
      (annotatedVerifyPub (encC z) prevRoot (.cell hd2 tl2) 3 (α ^ ePrev)
        (genAnnotatedDescentCont (encC z) z lmb
          [(genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1]
          (genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2
          .verify_child (.cell hd2 tl2) 2).2 0 0 lmb).pt (α ^ e2) 0 0
      (by simpa [annotatedVerifyPub] using bindFP_encC z (.cell hd2 tl2))
  · exact gMemRow9_read_specializes z α (.cell hd2 tl2) hd2 2 e2
      (annotatedVerifyPub (encC z) prevRoot (.cell hd2 tl2) 3 (α ^ ePrev)
        (genAnnotatedDescentCont (encC z) z lmb
          [(genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1]
          (genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2
          .verify_child (.cell hd2 tl2) 2).2 0 0 lmb).pt 0 0
  intro c hc
  simp at hc
  subst c
  rw [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · have hlen :
        (genAnnotatedDescentCont (encC z) z lmb
          [(genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1]
          (genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2
          .verify_child (.cell hd2 tl2) 2).1.length = 1 := by
      rw [genAnnotatedDescentCont_axis2]; simp
    simpa [gMemRow9, memVerifySkelAx, fanoutMem, GenMemoryRow.node, hlen]
  · exact gMemRow9_verify_bind z prevRoot (.cell hd2 tl2) 3 ePrev
      (genAnnotatedDescentCont (encC z) z lmb
        [(genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1]
        (genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2
        .verify_child (.cell hd2 tl2) 2).2 (α ^ ePrev) 0 0
      (by simpa [genAnnotatedDescentCont_axis2, annotatedDecPub]
        using bindFP_encC z (.cell hd2 tl2))
  · exact gMemRow9_verify_specializes z α prevRoot (.cell hd2 tl2) 3 ePrev
      (genAnnotatedDescentCont (encC z) z lmb
        [(genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1]
        (genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2
        .verify_child (.cell hd2 tl2) 2).2 0 0
  intro d hdmem
  simp [List.mem_map] at hdmem
  rcases hdmem with ⟨w, hw, rfl⟩
  exact genAnnotatedDescentCont_axis2_OK z α
    [(genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1]
    (genAnnotatedVerify (encC z) z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).2
    .verify_child hd2 tl2 (by simp)
    (by simpa [genAnnotatedVerify_pt_noun] using bindFP_encC z hd2)
    (by
      intro v hv
      simp at hv
      subst v
      exact genAnnotatedVerify_OK z α (.cell hd2 tl2) hd2 2 e2)
    w hw

theorem genAnnotatedChainedInner_one_length (z α : K)
    (prevRoot : Noun) (hd2 tl2 : Noun) (ePrev e2 : ℕ) :
    (genAnnotatedChainedInner (encC z) z α lmb
        ⟨prevRoot, .cell hd2 tl2, 3, ePrev⟩
        [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1.length = 1 := by
  unfold genAnnotatedChainedInner
  simp [genAnnotatedChainedInner_nil]

theorem genAnnotatedChainedInner_one_pt_noun (z α : K)
    (prevRoot : Noun) (hd2 tl2 : Noun) (ePrev e2 : ℕ) :
    (genAnnotatedChainedInner (encC z) z α lmb
        ⟨prevRoot, .cell hd2 tl2, 3, ePrev⟩
        [⟨.cell hd2 tl2, hd2, 2, e2⟩]).2.noun =
      encC z (.cell hd2 tl2) := by
  unfold genAnnotatedChainedInner
  simp [genAnnotatedChainedInner_nil, annotatedReadPub]

theorem genAnnotatedChainedTree_axis3_axis2_OK (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ t, genAnnotatedChainedTree (encC z) z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t →
      MemoryNodesOK z α (mapNTree GenMemoryRow.node t) := by
  intro t ht
  unfold genAnnotatedChainedTree at ht
  simp only [chainedInnerRootState] at ht
  injection ht with ht
  subst t
  simp only [mapNTree]
  refine MemoryNodesOK.mk' ⟨?_, rfl, ?_, ?_⟩ ?_
  · have hlen :
        (genAnnotatedDescentCont (encC z) z lmb
          (genAnnotatedChainedInner (encC z) z α lmb
            ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
            [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1
          (genAnnotatedChainedInner (encC z) z α lmb
            ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
            [⟨.cell hd2 tl2, hd2, 2, e2⟩]).2
          .read_root (.cell hd1 (.cell hd2 tl2)) 3).1.length = 1 := by
      rw [genAnnotatedDescentCont_axis3]; simp
    simpa [gMemRow9, memReadSkelAx, fanoutMem, GenMemoryRow.node, hlen]
  · exact gMemRow9_read_bind z (.cell hd1 (.cell hd2 tl2)) (.cell hd2 tl2) 3 e1
      (genAnnotatedDescentCont (encC z) z lmb
        (genAnnotatedChainedInner (encC z) z α lmb
          ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
          [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1
        (genAnnotatedChainedInner (encC z) z α lmb
          ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
          [⟨.cell hd2 tl2, hd2, 2, e2⟩]).2
        .read_root (.cell hd1 (.cell hd2 tl2)) 3).2 (α ^ e1) 0 0
      (by simpa [annotatedReadPub, genAnnotatedDescentCont_axis3, annotatedDecPub]
        using bindFP_encC z (.cell hd1 (.cell hd2 tl2)))
  · exact gMemRow9_read_specializes z α (.cell hd1 (.cell hd2 tl2))
      (.cell hd2 tl2) 3 e1
      (genAnnotatedDescentCont (encC z) z lmb
        (genAnnotatedChainedInner (encC z) z α lmb
          ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
          [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1
        (genAnnotatedChainedInner (encC z) z α lmb
          ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
          [⟨.cell hd2 tl2, hd2, 2, e2⟩]).2
        .read_root (.cell hd1 (.cell hd2 tl2)) 3).2 0 0
  intro c hc
  simp [List.mem_map] at hc
  rcases hc with ⟨w, hw, rfl⟩
  exact genAnnotatedDescentCont_axis3_OK z α
    (genAnnotatedChainedInner (encC z) z α lmb
      ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
      [⟨.cell hd2 tl2, hd2, 2, e2⟩]).1
    (genAnnotatedChainedInner (encC z) z α lmb
      ⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩
      [⟨.cell hd2 tl2, hd2, 2, e2⟩]).2
    .read_root hd1 (.cell hd2 tl2)
    (genAnnotatedChainedInner_one_length z α _ hd2 tl2 e1 e2)
    (by simpa [genAnnotatedChainedInner_one_pt_noun]
      using bindFP_encC z (.cell hd2 tl2))
    (genAnnotatedChainedInner_one_axis2_OK z α
      (.cell hd1 (.cell hd2 tl2)) hd2 tl2 e1 e2)
    w hw

theorem genRowMemForest_singleton_axis3_OK (z α : K) (hd tl : Noun) (e : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb [⟨.cell hd tl, tl, 3, e⟩],
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  simp [genRowMemForest_singleton] at hu
  subst u
  exact genAnnotatedRecordTree_axis3_OK z α hd tl e

theorem genRowMemForest_singleton_axis2_OK (z α : K) (hd tl : Noun) (e : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb [⟨.cell hd tl, hd, 2, e⟩],
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  simp [genRowMemForest_singleton] at hu
  subst u
  exact genAnnotatedRecordTree_axis2_OK z α hd tl e

theorem genRowMemForest_chain32_OK (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩],
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  unfold genRowMemForest at hu
  simp only at hu
  cases h : genAnnotatedChainedTree (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some t =>
    simp [h] at hu
    subst u
    exact genAnnotatedChainedTree_axis3_axis2_OK z α hd1 hd2 tl2 e1 e2 t h

theorem genRowMemForest_three_chain32_OK (z α : K)
    (hd1 hd2 tl2 hd3 tl3 : Noun) (e1 e2 e3 : ℕ) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩,
       ⟨.cell hd3 tl3, hd3, 2, e3⟩],
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  intro u hu
  unfold genRowMemForest at hu
  cases h : genAnnotatedChainedTree (encC z) z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none =>
    simp [genAnnotatedChainedTree] at h
  | some t =>
    simp [h, List.mem_append, List.mem_singleton] at hu
    rcases hu with hmem | hmem
    · rw [hmem]
      exact genAnnotatedChainedTree_axis3_axis2_OK z α hd1 hd2 tl2 e1 e2 t h
    · rw [hmem]
      exact genAnnotatedRecordTree_axis2_OK z α hd3 tl3 e3

/-! ## Full generated forest -/

theorem extractNodeReqsAux_cons1 (stamp : ComputeTimestampRow) (i : ℕ)
    (r : ServiceReq K) :
    extractNodeReqsAux stamp i [r] =
      [⟨r.root, r.child, r.axis, getRecordExp stamp i⟩] := rfl

theorem extractNodeReqsAux_cons2 (stamp : ComputeTimestampRow) (i : ℕ)
    (r1 r2 : ServiceReq K) :
    extractNodeReqsAux stamp i [r1, r2] =
      [⟨r1.root, r1.child, r1.axis, getRecordExp stamp i⟩,
       ⟨r2.root, r2.child, r2.axis, getRecordExp stamp (i + 1)⟩] := rfl

theorem extractNodeReqsAux_cons3 (stamp : ComputeTimestampRow) (i : ℕ)
    (r1 r2 r3 : ServiceReq K) :
    extractNodeReqsAux stamp i [r1, r2, r3] =
      [⟨r1.root, r1.child, r1.axis, getRecordExp stamp i⟩,
       ⟨r2.root, r2.child, r2.axis, getRecordExp stamp (i + 1)⟩,
       ⟨r3.root, r3.child, r3.axis, getRecordExp stamp (i + 2)⟩] := rfl

theorem bfsLabelAt_requests (t : NTree (GenComputeRow K)) (i : ℕ)
    (hi : i - 1 < (bfsRows t).length) :
    (bfsLabelAt t i).requests = (bfsRows t)[i - 1].requests := by
  simp [bfsLabelAt_eq t i hi]

theorem genMemForestFromTree_of_rowOK (z α : K)
    (t : NTree (GenComputeRow K))
    (H : ∀ n, InTree t n →
      ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
        MemoryNodesOK z α (mapNTree GenMemoryRow.node u))
    (u : NTree (GenMemoryRow K))
    (hu : u ∈ genMemForestFromTree (encC z) z α lmb t) :
    MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
  suffices ∀ N t,
      NTree.size t ≤ N →
      (∀ n, InTree t n →
        ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
          MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) →
      ∀ u ∈ genMemForestFromTree (encC z) z α lmb t,
        MemoryNodesOK z α (mapNTree GenMemoryRow.node u) from
    this (NTree.size t) t le_rfl H u hu
  intro N
  induction N with
  | zero =>
    intro t ht H u hu
    cases t with
    | node g cs =>
      simp [NTree.size] at ht
  | succ N ih =>
    intro t ht H u hu
    cases t with
    | node g cs =>
      simp [genMemForestFromTree] at hu
      rcases hu with hu | hu
      · exact H (.node g cs) (InTree.here _) u hu
      · have recList :
            ∀ cs', (∀ c ∈ cs', c ∈ cs) →
              (∀ t ∈ cs', NTree.size t ≤ N) →
              (∀ t ∈ cs', ∀ n, InTree t n →
                ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
                  MemoryNodesOK z α (mapNTree GenMemoryRow.node u)) →
              ∀ u ∈ genMemForestFromList (encC z) z α lmb cs',
                MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
          intro cs' hsub hsz H' u' hu'
          induction cs' generalizing u' with
          | nil => simp [genMemForestFromList] at hu'
          | cons c rest ihcs =>
            simp [genMemForestFromList] at hu'
            rcases hu' with hu' | hu'
            · exact ih c (hsz c (by simp))
                (fun n hn => H' c (by simp) n hn) u' hu'
            · refine ihcs ?_ ?_ ?_ u' hu'
              · intro c' hc'; exact hsub c' (List.mem_cons_of_mem _ hc')
              · intro t htt; exact hsz t (List.mem_cons_of_mem _ htt)
              · intro t htt; exact H' t (List.mem_cons_of_mem _ htt)
        refine recList cs (fun _ h => h) ?_ (fun t ht n hn => H n (InTree.sub ht hn)) u hu
        intro c hc
        have hin : NTree.size c ∈ cs.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
        have hsum : NTree.size c ≤ (cs.map NTree.size).sum := List.le_sum_of_mem hin
        simp [NTree.size] at ht
        omega

theorem dotAssigned_rowOK (z α : K)
    (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (dotTree (K := K))) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) := by
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
    exact genRowMemForest_three_chain32_OK z α (.atom 6) dotCondFormula
      dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 1)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 1).stamp 2)
  · have hget : (bfsRows (dotTree (K := K)))[1] = (dotCondTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 2).stamp 0 g.requests) hget]
    simp [dotCondTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_OK z α (.atom 1) (.atom 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 2).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[2] = (dotOp2Tree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 3).stamp 0 g.requests) hget]
    simp [dotOp2Tree, skelNode, extractNodeReqsAux_cons2]
    exact genRowMemForest_chain32_OK z α (.atom 2) dotOp2B dotOp2C
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 3).stamp 1)
  · have hget : (bfsRows (dotTree (K := K)))[3] = (dotOp1BTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 4).stamp 0 g.requests) hget]
    simp [dotOp1BTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_OK z α (.atom 1) (.cell (.atom 0) (.atom 1))
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 4).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[4] = (dotOp1CTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 5).stamp 0 g.requests) hget]
    simp [dotOp1CTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_OK z α (.atom 1) dotOp9Formula
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 5).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[5] = (dotOp9Tree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 6).stamp 0 g.requests) hget]
    simp [dotOp9Tree, skelNode, extractNodeReqsAux_cons3]
    exact genRowMemForest_three_chain32_OK z α (.atom 9) (.atom 2) dotCoreFormula
      dotElem0 dotElem1
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 0)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 1)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 6).stamp 2)
  · have hget : (bfsRows (dotTree (K := K)))[6] = (dotOp9CoreTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 7).stamp 0 g.requests) hget]
    simp [dotOp9CoreTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_OK z α (.atom 1) dotCore
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 7).stamp 0)
  · have hget : (bfsRows (dotTree (K := K)))[7] = (dotOp9InvokeTree (K := K)).label := by
      simp [dot_bfsRows]
    rw [congrArg (fun g => extractNodeReqsAux
      (bfsLabelAt (dotTree (K := K)) 8).stamp 0 g.requests) hget]
    simp [dotOp9InvokeTree, skelNode, extractNodeReqsAux_cons1]
    exact genRowMemForest_singleton_axis3_OK z α (.atom 1) (.atom 3)
      (getRecordExp (bfsLabelAt (dotTree (K := K)) 8).stamp 0)

theorem dotMemForest_OK (z α : K) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K))),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) :=
  genMemForestFromTree_of_rowOK z α _ (dotAssigned_rowOK z α)

theorem dotMemForest_OK_F97 :
    ∀ u ∈ genMemForestFromTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
        (bfsAssign (dotTree (K := ZMod 97))),
      MemoryNodesOK seedZ alphaA (mapNTree GenMemoryRow.node u) :=
  dotMemForest_OK seedZ alphaA

/-! ## Served forest vs F97 orbit -/

theorem nounWalkSize_dotThenFormula : nounWalkSize dotThenFormula = 23 := by
  simp [nounWalkSize, dotThenFormula, dotThenTail, dotOp2B, dotOp2C,
    dotOp9Formula, dotOp9Tail, dotCoreFormula, dotCore, dotElem0, dotElem1]

theorem nounWalkSize_dotElseFormula : nounWalkSize dotElseFormula = 13 := by
  simp [nounWalkSize, dotElseFormula, dotCoreFormula, dotCore, dotElem0, dotElem1]

theorem dotBranchPairRecord_size (z α : K) (e : ℕ) :
    (genAnnotatedRecordTree (encC z) z α lmb dotBranchPair dotThenFormula 2 e).size
      = 39 := by
  simpa [dotBranchPair, nounWalkSize_dotThenFormula, nounWalkSize_dotElseFormula]
    using genAnnotatedRecordTree_axis2_size (encC z) z α
      dotThenFormula dotElseFormula e

theorem genRowMemForest_three_chain32_has_third
    (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 hd3 tl3 : Noun) (e1 e2 e3 : ℕ) :
    genAnnotatedRecordTree E z α lmb (.cell hd3 tl3) hd3 2 e3 ∈
      genRowMemForest E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩,
         ⟨.cell hd3 tl3, hd3, 2, e3⟩] := by
  unfold genRowMemForest
  cases h : genAnnotatedChainedTree E z α lmb
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] with
  | none => simp [genAnnotatedChainedTree] at h
  | some t => simp [h]

theorem extractNodeReqs_dot_root :
    extractNodeReqs (bfsAssign (dotTree (K := K))).label =
      [⟨dotFormula, dotParentTail, 3,
          getRecordExp (bfsAssign (dotTree (K := K))).label.stamp 0⟩,
       ⟨dotParentTail, dotCondFormula, 2,
          getRecordExp (bfsAssign (dotTree (K := K))).label.stamp 1⟩,
       ⟨dotBranchPair, dotThenFormula, 2,
          getRecordExp (bfsAssign (dotTree (K := K))).label.stamp 2⟩] := by
  rw [extractNodeReqs, bfsAssign_dot_root_requests]
  simp [dotTree, skelNode, extractNodeReqsAux_cons3]

theorem dotBranchPairRecord_mem (z α : K) :
    genAnnotatedRecordTree (encC z) z α lmb dotBranchPair dotThenFormula 2
        (getRecordExp (bfsAssign (dotTree (K := K))).label.stamp 2) ∈
      genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K))) := by
  have hshape :
      bfsAssign (dotTree (K := K)) =
        NTree.node (bfsAssign (dotTree (K := K))).label
          (bfsAssign (dotTree (K := K))).children := by
    cases bfsAssign (dotTree (K := K)); rfl
  rw [hshape, genMemForestFromTree, extractNodeReqs_dot_root]
  refine List.mem_append.mpr (Or.inl ?_)
  simpa [dotFormula, dotParentTail, dotBranchPair] using
    genRowMemForest_three_chain32_has_third (encC z) z α
      (.atom 6) dotCondFormula dotBranchPair dotThenFormula dotElseFormula
      (getRecordExp (bfsAssign (dotTree (K := K))).label.stamp 0)
      (getRecordExp (bfsAssign (dotTree (K := K))).label.stamp 1)
      (getRecordExp (bfsAssign (dotTree (K := K))).label.stamp 2)

theorem size_le_totalSize {α} (t : NTree α) (ts : List (NTree α)) (ht : t ∈ ts) :
    t.size ≤ totalSize ts := by
  simpa [totalSize] using
    (List.le_sum_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩))

/-- F97 cubic orbit capacity is `2^5 = 32`.  The generated forest is larger:
    the OP6 branch-pair record alone has 39 nodes. -/
theorem dotMemForest_exceeds_F97_orbit (z α : K) :
    32 < totalSize
      (genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K)))) := by
  have hmem := dotBranchPairRecord_mem (lmb := lmb) z α
  have hsz := dotBranchPairRecord_size (lmb := lmb) z α
    (getRecordExp (bfsAssign (dotTree (K := K))).label.stamp 2)
  have hle := size_le_totalSize _ _ hmem
  omega

theorem dotMemForest_exceeds_F97_orbit_F97 :
    32 < totalSize
      (genMemForestFromTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
        (bfsAssign (dotTree (K := ZMod 97)))) :=
  dotMemForest_exceeds_F97_orbit seedZ alphaA

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genHaltNodes_atom_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedNounWalk_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedVerify_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedRecordTree_axis3_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedRecordTree_axis2_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.quoteAtomMemTree_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotCondMemTree_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotCondMemTree_OK_F97
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedDescentCont_axis3_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedDescentCont_axis2_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedChainedInner_one_axis2_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genAnnotatedChainedTree_axis3_axis2_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRowMemForest_three_chain32_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotAssigned_rowOK
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_OK_F97
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotBranchPairRecord_size
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_exceeds_F97_orbit
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotMemForest_exceeds_F97_orbit_F97
