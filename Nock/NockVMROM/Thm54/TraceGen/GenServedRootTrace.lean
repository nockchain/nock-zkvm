/-
  Nock/NockVMROM/Thm54/TraceGen/GenServedRootTrace.lean

  **`RootTrace` at an arbitrary axis, generically in the forest.**  P3.3's first field.

  -- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemoryTrace
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMem
import Nock.NockVMROM.Thm54.TraceGen.GenTierASemantic
import Nock.NockVMROM.Thm54.GenericHonestCommitment

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticStrategy

variable {K : Type} [Field K]

-- Form R `λ` of the generated memory rows (the configuration's `λ`; 28th λ-fix).
variable {lmb : K}

/-! ## A. The builder's top-bit descent IS the paper's `axisPath` -/

/-- `axisPath` consumes its topmost bit first, which is exactly the builder's
`axisTopBit`/`axisRest` step. -/
theorem axisPath_cons {a : ℕ} (h : 2 ≤ a) :
    axisPath a = axisTopBit a :: axisPath (axisRest a) := by
  induction a using Nat.strongRecOn with
  | _ a ih =>
    by_cases h4 : a < 4
    · have h23 : a = 2 ∨ a = 3 := by omega
      rcases h23 with rfl | rfl
      · rw [axisPath_two, axisTopBit_two, axisRest_two,
          axisPath_of_lt_two (by omega)]
      · rw [axisPath_three, axisTopBit_three, axisRest_three,
          axisPath_of_lt_two (by omega)]
    · have ha4 : 4 ≤ a := by omega
      have hhalf : 2 ≤ a / 2 := by omega
      have hlt : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      have hbit : axisTopBit a = axisTopBit (a / 2) := axisTopBit_div2 ha4
      have hrest : axisRest a = 2 * axisRest (a / 2) + a % 2 := axisRest_div2 ha4
      have hk : 1 ≤ axisRest (a / 2) := axisRest_pos hhalf
      have hb : a % 2 < 2 := Nat.mod_lt _ (by decide)
      have hrest2 : 2 ≤ axisRest a := by omega
      have hdiv : (axisRest a) / 2 = axisRest (a / 2) := by omega
      have hmod : (axisRest a) % 2 = a % 2 := by omega
      rw [axisPath_of_two_le h, ih (a / 2) hlt hhalf, hbit,
        axisPath_of_two_le hrest2, hdiv, hmod]
      simp

/-! ## B. The annotated axis descent at an ARBITRARY axis

`GenTierAMemoryTrace` proves the walk facts only at axes `2` and `3` (`serviceWalk_recordTree_axis2`
/ `_axis3`).  A generated program emits arbitrary axes: the `OP_0` slot read (`Gen.lean:579`) and the
`OP_9` arm fetch (`Gen.lean:706`) both carry the formula's own axis.  This is the missing induction.
-/

variable {F : Type} [Field F] [Algebra F K]

noncomputable section

/-- **Bundled walk facts for the annotated descent at any axis.**

The single hypothesis is the Nock fact `slot remaining current = some child`; the builder's
`axisTopBit`/`axisRest` step is `axisPath`'s own step (`axisPath_cons`), so the generated route IS
the binary expansion of the record's axis. -/
theorem descent_bundle {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (services : List (Service cfg exec))
    (E : Noun → ComputeTable.FP K) (z : K) (root child : Noun) (recAxis e : ℕ) :
    ∀ (remaining : ℕ) (current : Noun),
      Noun.slot remaining current = some child →
      ∀ u ∈ (genAnnotatedDescent E z lmb root child recAxis
              (cfg.challenges.α ^ e) e current remaining).1,
        VerifyRoute (timestampExp cfg.challenges.α (cfg.challenges.α ^ e)) child
            ((recAxis : ℕ) : K) (axisPath remaining) current
            (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row u)) ∧
          ServiceWalk services current
            (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row u)) ∧
          readExps (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row u)) = [] ∧
          verifyExps (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row u))
            = [timestampExp cfg.challenges.α (cfg.challenges.α ^ e)] := by
  intro remaining
  induction remaining using Nat.strongRecOn with
  | _ n ih =>
    intro current hslot u hu
    have hdesc := hu
    unfold genAnnotatedDescent at hdesc
    split at hdesc
    · rename_i hlt
      have hn1 : n = 1 := by
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simp [Noun.slot] at hslot
        · omega
      subst hn1
      have hcur : current = child := by
        simpa [Noun.slot] using hslot
      subst hcur
      simp [genAnnotatedVerify] at hdesc
      subst u
      rw [show (NTree.node (gMemRow9 (memVerifySkelAx root current recAxis) e z
            (annotatedVerifyPub E root current recAxis (cfg.challenges.α ^ e)
              (genAnnotatedNounWalk E z lmb current).2 0 0 lmb))
            [(genAnnotatedNounWalk E z lmb current).1] : NTree (GenMemoryRow K))
          = (genAnnotatedVerify E z lmb root current recAxis
              (cfg.challenges.α ^ e) e).1 from rfl,
        axisMTree_verify]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [axisPath_of_lt_two (by omega)]
        exact VerifyRoute.here rfl rfl
          (readCount_nounWalk E z cfg.challenges.α _ current)
          (verifyCount_nounWalk E z cfg.challenges.α _ current)
      · exact ServiceWalk.verify (serviceWalk_nounWalk services E z current)
      · simp [readExps, readExps_nounWalk]
      · simp [verifyExps, verifyExps_nounWalk]
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      cases current with
      | atom a =>
          rw [slot_atom_of_ge_two h2] at hslot
          simp at hslot
      | cell hd tl =>
        rw [slot_eq_msb hd tl h2] at hslot
        simp only [formulaHead, formulaTail] at hdesc
        obtain ⟨tt, htt⟩ := List.length_eq_one_iff.mp
          (genAnnotatedDescent_length (lmb := lmb) E z root child recAxis
            (cfg.challenges.α ^ e) e tl (axisRest n))
        obtain ⟨ht2, hht2⟩ := List.length_eq_one_iff.mp
          (genAnnotatedDescent_length (lmb := lmb) E z root child recAxis
            (cfg.challenges.α ^ e) e hd (axisRest n))
        split at hdesc
        · rename_i htb
          have hslot' : Noun.slot (axisRest n) tl = some child := by
            simpa [htb] using hslot
          simp only [htt, List.cons_append, List.nil_append,
            List.mem_singleton] at hdesc
          subst u
          have hmap :
              (mapNTree GenMemoryRow.row
                (.node (gMemRow9 (memDecomposeSkel (.cell hd tl) hd tl) 0 z
                    (annotatedDecPub E (.cell hd tl) hd tl
                      (genAnnotatedNounWalk E z lmb hd).2
                      (genAnnotatedDescent E z lmb root child recAxis (cfg.challenges.α ^ e) e
                        tl (axisRest n)).2
                      (nounWalkRootState hd)
                      (descentRootState (axisRest n)) 0 0 lmb))
                  [(genAnnotatedNounWalk E z lmb hd).1, tt])
                : NTree (MState × DTmem K))
              = .node (MState.decompose,
                  (memInputs z,
                    annotatedDecPub E (.cell hd tl) hd tl
                      (genAnnotatedNounWalk E z lmb hd).2
                      (genAnnotatedDescent E z lmb root child recAxis (cfg.challenges.α ^ e) e
                        tl (axisRest n)).2
                      (nounWalkRootState hd) (descentRootState (axisRest n)) 0 0 lmb))
                  [mappedNounWalk E z lmb hd, mapNTree GenMemoryRow.row tt] := by
            rw [mapped_gMemRow9]
            simp [memDecomposeSkel, mappedNounWalk]
          rw [hmap, axisMTree_decompose_node]
          obtain ⟨hroute, hwalk, hread, hverify⟩ :=
            ih (axisRest n) (axisRest_lt h2) tl hslot' tt (by rw [htt]; simp)
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [axisPath_cons h2, htb]
            exact VerifyRoute.right
              (readCount_nounWalk E z cfg.challenges.α _ hd)
              (verifyCount_nounWalk E z cfg.challenges.α _ hd) hroute
          · exact ServiceWalk.decompose (serviceWalk_nounWalk services E z hd) hwalk
          · simp [readExps, readExps_nounWalk, hread]
          · simp [verifyExps, verifyExps_nounWalk, hverify]
        · rename_i htb
          have htbf : axisTopBit n = false := by
            simpa using htb
          have hslot' : Noun.slot (axisRest n) hd = some child := by
            simpa [htbf] using hslot
          simp only [hht2, List.singleton_append, List.mem_singleton] at hdesc
          subst u
          have hmap :
              (mapNTree GenMemoryRow.row
                (.node (gMemRow9 (memDecomposeSkel (.cell hd tl) hd tl) 0 z
                    (annotatedDecPub E (.cell hd tl) hd tl
                      (genAnnotatedDescent E z lmb root child recAxis (cfg.challenges.α ^ e) e
                        hd (axisRest n)).2
                      (genAnnotatedNounWalk E z lmb tl).2
                      (descentRootState (axisRest n))
                      (nounWalkRootState tl) 0 0 lmb))
                  [ht2, (genAnnotatedNounWalk E z lmb tl).1])
                : NTree (MState × DTmem K))
              = .node (MState.decompose,
                  (memInputs z,
                    annotatedDecPub E (.cell hd tl) hd tl
                      (genAnnotatedDescent E z lmb root child recAxis (cfg.challenges.α ^ e) e
                        hd (axisRest n)).2
                      (genAnnotatedNounWalk E z lmb tl).2
                      (descentRootState (axisRest n)) (nounWalkRootState tl) 0 0 lmb))
                  [mapNTree GenMemoryRow.row ht2, mappedNounWalk E z lmb tl] := by
            rw [mapped_gMemRow9]
            simp [memDecomposeSkel, mappedNounWalk]
          rw [hmap, axisMTree_decompose_node]
          obtain ⟨hroute, hwalk, hread, hverify⟩ :=
            ih (axisRest n) (axisRest_lt h2) hd hslot' ht2 (by rw [hht2]; simp)
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [axisPath_cons h2, htbf]
            exact VerifyRoute.left hroute
              (readCount_nounWalk E z cfg.challenges.α _ tl)
              (verifyCount_nounWalk E z cfg.challenges.α _ tl)
          · exact ServiceWalk.decompose hwalk (serviceWalk_nounWalk services E z tl)
          · simp [readExps, readExps_nounWalk, hread]
          · simp [verifyExps, verifyExps_nounWalk, hverify]

end

/-! ## C. The record tree at an arbitrary axis -/

noncomputable section



/-- The mapped record tree is a `read_root` above the descent, at ANY axis. -/
theorem axisMTree_recordTree {E : Noun → ComputeTable.FP K} {z α : K}
    {root child : Noun} {ax e : ℕ} {u : NTree (GenMemoryRow K)}
    (hu : (genAnnotatedDescent E z lmb root child ax (α ^ e) e root ax).1 = [u]) :
    axisMTree α (mappedRecordTree E z α lmb root child ax e) =
      .read (timestampExp α (α ^ e))
        (axisMTree α (mapNTree GenMemoryRow.row u)) := by
  rw [mappedRecordTree, genAnnotatedRecordTree]
  simp only [hu]
  rw [mapped_gMemRow9]
  rw [show (memReadSkelAx root child ax).state = MState.read_root from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [axisMTree_read_node]
  simp [annotatedReadPub]

/-- **The service walk of a one-record tree, at ANY axis.**  The axis-2 and axis-3 lemmas of
`GenTierAMemoryTrace` are the `ax = 2` / `ax = 3` cases. -/
theorem serviceWalk_recordTree {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (services : List (Service cfg exec)) (s : Service cfg exec)
    (E : Noun → ComputeTable.FP K) (z : K) (root child : Noun) (ax e : ℕ)
    (hs : s ∈ services) (hroot : s.root = root) (hchild : s.child = child)
    (haxis : s.axis = ax)
    (hexp : s.exponent = timestampExp cfg.challenges.α (cfg.challenges.α ^ e))
    (hslot : Noun.slot ax root = some child) :
    ServiceWalk services root
      (axisMTree cfg.challenges.α
        (mappedRecordTree E z cfg.challenges.α lmb root child ax e)) := by
  obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp
    (genAnnotatedDescent_length E z root child ax
      (cfg.challenges.α ^ e) e root ax)
  obtain ⟨hroute, hwalk, -, -⟩ :=
    descent_bundle services E z root child ax e ax root hslot u
      (by rw [hu]; simp)
  rw [axisMTree_recordTree hu]
  refine ServiceWalk.read s hs hexp hroot ?_ hwalk
  have hrecax : s.record.axis = ((ax : ℕ) : K) := by
    rw [s.realization.axis_realizes, haxis]
  rw [hchild, hrecax, haxis]
  exact hroute

/-- Read exponents of a one-record tree, at ANY axis. -/
theorem readExps_recordTree (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (ax e : ℕ)
    (hslot : Noun.slot ax root = some child)
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hα : α = cfg.challenges.α) :
    readExps (axisMTree α (mappedRecordTree E z α lmb root child ax e)) =
      [timestampExp α (α ^ e)] := by
  subst hα
  obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp
    (genAnnotatedDescent_length (lmb := lmb) E z root child ax
      (cfg.challenges.α ^ e) e root ax)
  obtain ⟨-, -, hread, -⟩ :=
    descent_bundle (cfg := cfg) (exec := exec) [] E z root child ax e ax root hslot u
      (by rw [hu]; simp)
  rw [axisMTree_recordTree hu]
  simp [readExps, hread]

/-- Verify exponents of a one-record tree, at ANY axis. -/
theorem verifyExps_recordTree (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (ax e : ℕ)
    (hslot : Noun.slot ax root = some child)
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hα : α = cfg.challenges.α) :
    verifyExps (axisMTree α (mappedRecordTree E z α lmb root child ax e)) =
      [timestampExp α (α ^ e)] := by
  subst hα
  obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp
    (genAnnotatedDescent_length (lmb := lmb) E z root child ax
      (cfg.challenges.α ^ e) e root ax)
  obtain ⟨-, -, -, hverify⟩ :=
    descent_bundle (cfg := cfg) (exec := exec) [] E z root child ax e ax root hslot u
      (by rw [hu]; simp)
  rw [axisMTree_recordTree hu]
  simp [verifyExps, hverify]

end

/-! ### The response records of a one-record tree, at any field

Every lemma its proof uses is genuinely generic, so this is the same proof at a real
`variable {K}`. -/

/-- The `read_root` state and served record of a one-record tree, at any axis and any field. -/
theorem genAnnotatedRecordTree_root_read (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (ax e : ℕ) :
    (genAnnotatedRecordTree E z α lmb root child ax e).label.row.2.2.st = .read_root ∧
      (genAnnotatedRecordTree E z α lmb root child ax e).label.row.2.2.ver = true ∧
      (genAnnotatedRecordTree E z α lmb root child ax e).label.row.2.2.mem =
        ⟨E root, E child, (ax : K), α ^ e⟩ := by
  simp only [genAnnotatedRecordTree, NTree.label]
  exact ⟨by rw [gMemRow9_st, annotatedReadPub_st],
    by rw [gMemRow9_ver, annotatedReadPub_ver],
    by rw [gMemRow9_mem, annotatedReadPub_mem]⟩

/-- **`servedGen` of a one-record tree, generically in the field.** -/
theorem genAnnotatedRecordTree_servedGen (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (ax e : ℕ) :
    servedGen [genAnnotatedRecordTree E z α lmb root child ax e] =
      [⟨E root, E child, (ax : K), α ^ e⟩] := by
  have hne : ([genAnnotatedRecordTree E z α lmb root child ax e] :
      List (NTree (GenMemoryRow K))) ≠ [] := List.cons_ne_nil _ _
  rw [servedGen_of_ne_nil _ hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  obtain ⟨hst, hver, hmem⟩ := genAnnotatedRecordTree_root_read E z α root child ax e
  rw [responseRecords_eq_singleton_of_read_root _ hst hver, hmem]
  have hch :
      forestFibre (.read_root : MemoryTable.MState)
        (genAnnotatedRecordTree E z α lmb root child ax e).children = 0 := by
    have hf := genAnnotatedRecordTree_fibre (lmb := lmb) E z α root child ax e
    unfold genAnnotatedRecordTree at hf ⊢
    simp [treeFibre_gMemRow9, annotatedReadPub_st] at hf ⊢
    omega
  have hchVer :
      ∀ t ∈ bfsForest (genAnnotatedRecordTree E z α lmb root child ax e).children,
        t.label.row.2.2.ver = false :=
    genAnnotatedRecordTree_children_bfs_ver_false E z α root child ax e
  rw [servedGen_no_read _ hch hchVer]
  rfl

/-! ## D. `RootTrace` from a one-record forest root, generically

The two hypotheses `hax` / `hsrv` are the *interface* between a configuration's forest and the
generic walk theory: they say which generated tree sits at forest index `i`.  Both live
configurations already prove exactly this shape (`DotConfig769.axis_at`, `.served_at`), and on the
generated carrier they come from `axisMTree_threadGenForest` / `servedGen_thread_get`.
-/

noncomputable section



/-- **One forest root, one record, ANY axis: a `RootTrace`.** -/
noncomputable def rootTraceOfRecordTree
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (E : Noun → ComputeTable.FP K) (z : K) (root child : Noun) (ax e : ℕ)
    (s : Service cfg exec)
    (hroot : s.root = root) (hchild : s.child = child) (haxis : s.axis = ax)
    (hexp : s.exponent = timestampExp cfg.challenges.α (cfg.challenges.α ^ e))
    (hrec : s.record = ⟨E root, E child, (ax : K), cfg.challenges.α ^ e⟩)
    (hslot : Noun.slot ax root = some child)
    (hax : exactAxisTree cfg exec i
        = axisMTree cfg.challenges.α
            (mappedRecordTree E z cfg.challenges.α lmb root child ax e))
    (hsrv : rootResponseRecords exec i
        = servedGen [genAnnotatedRecordTree E z cfg.challenges.α lmb root child ax e]) :
    RootTrace cfg exec i where
  subject := root
  services := [s]
  recordPartition := by
    rw [hsrv, genAnnotatedRecordTree_servedGen]
    simp [hrec]
  readPartition := by
    rw [hax, readExps_recordTree (cfg := cfg) (exec := exec) E z _ root child ax e hslot rfl]
    simp [hexp]
  verifyPartition := by
    rw [hax, verifyExps_recordTree (cfg := cfg) (exec := exec) E z _ root child ax e hslot rfl]
    simp [hexp]
  traversal := by
    rw [hax]
    exact serviceWalk_recordTree [s] s E z root child ax e (by simp)
      hroot hchild haxis hexp hslot

end

/-! ## E. The continuation descent at an arbitrary axis

`genAnnotatedChainedTree` threads a *continuation* through the descent rather than a verify leaf, so
the chained shapes need the same induction with the terminal left as a parameter. -/

noncomputable section

/-- **Bundled walk facts for the annotated continuation descent at any axis.**

The four conclusions are transported from the continuation `c`, which sits at the terminal noun
`term`.  Taking `c` to be the record's own verify node recovers `descent_bundle`. -/
theorem descentCont_bundle {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (services : List (Service cfg exec))
    (E : Noun → ComputeTable.FP K) (z : K)
    (c : NTree (GenMemoryRow K)) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState)
    (ex : ℕ) (child : Noun) (recAxis : K) (term : Noun) (R V : List ℕ)
    (hroute : VerifyRoute ex child recAxis [] term
      (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row c)))
    (hwalk : ServiceWalk services term
      (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row c)))
    (hread : readExps (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row c)) = R)
    (hverify : verifyExps (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row c)) = V) :
    ∀ (remaining : ℕ) (current : Noun),
      Noun.slot remaining current = some term →
      ∀ u ∈ (genAnnotatedDescentCont E z lmb [c] contCell contState current remaining).1,
        VerifyRoute ex child recAxis (axisPath remaining) current
            (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row u)) ∧
          ServiceWalk services current
            (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row u)) ∧
          readExps (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row u)) = R ∧
          verifyExps (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row u)) = V := by
  intro remaining
  induction remaining using Nat.strongRecOn with
  | _ n ih =>
    intro current hslot u hu
    have hdesc := hu
    unfold genAnnotatedDescentCont at hdesc
    split at hdesc
    · rename_i hlt
      have hn1 : n = 1 := by
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simp [Noun.slot] at hslot
        · omega
      subst hn1
      have hcur : current = term := by simpa [Noun.slot] using hslot
      subst hcur
      simp only [List.mem_singleton] at hdesc
      subst u
      rw [axisPath_of_lt_two (by omega)]
      exact ⟨hroute, hwalk, hread, hverify⟩
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      cases current with
      | atom a =>
          rw [slot_atom_of_ge_two h2] at hslot
          simp at hslot
      | cell hd tl =>
        rw [slot_eq_msb hd tl h2] at hslot
        simp only [formulaHead, formulaTail] at hdesc
        obtain ⟨tt, htt⟩ := List.length_eq_one_iff.mp
          (genAnnotatedDescentCont_length_one (lmb := lmb) E z [c] contCell contState
            (by simp) tl (axisRest n))
        obtain ⟨ht2, hht2⟩ := List.length_eq_one_iff.mp
          (genAnnotatedDescentCont_length_one (lmb := lmb) E z [c] contCell contState
            (by simp) hd (axisRest n))
        split at hdesc
        · rename_i htb
          have hslot' : Noun.slot (axisRest n) tl = some term := by
            simpa [htb] using hslot
          simp only [htt, List.cons_append, List.nil_append,
            List.mem_singleton] at hdesc
          subst u
          have hmap :
              (mapNTree GenMemoryRow.row
                (.node (gMemRow9 (memDecomposeSkel (.cell hd tl) hd tl) 0 z
                    (annotatedDecPub E (.cell hd tl) hd tl
                      (genAnnotatedNounWalk E z lmb hd).2
                      (genAnnotatedDescentCont E z lmb [c] contCell contState
                        tl (axisRest n)).2
                      (nounWalkRootState hd)
                      (descentContRootState contState (axisRest n)) 0 0 lmb))
                  [(genAnnotatedNounWalk E z lmb hd).1, tt])
                : NTree (MState × DTmem K))
              = .node (MState.decompose,
                  (memInputs z,
                    annotatedDecPub E (.cell hd tl) hd tl
                      (genAnnotatedNounWalk E z lmb hd).2
                      (genAnnotatedDescentCont E z lmb [c] contCell contState
                        tl (axisRest n)).2
                      (nounWalkRootState hd)
                      (descentContRootState contState (axisRest n)) 0 0 lmb))
                  [mappedNounWalk E z lmb hd, mapNTree GenMemoryRow.row tt] := by
            rw [mapped_gMemRow9]
            simp [memDecomposeSkel, mappedNounWalk]
          rw [hmap, axisMTree_decompose_node]
          obtain ⟨hr, hw, hrd, hvf⟩ :=
            ih (axisRest n) (axisRest_lt h2) tl hslot' tt (by rw [htt]; simp)
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [axisPath_cons h2, htb]
            exact VerifyRoute.right
              (readCount_nounWalk E z cfg.challenges.α _ hd)
              (verifyCount_nounWalk E z cfg.challenges.α _ hd) hr
          · exact ServiceWalk.decompose (serviceWalk_nounWalk services E z hd) hw
          · simp [readExps, readExps_nounWalk, hrd]
          · simp [verifyExps, verifyExps_nounWalk, hvf]
        · rename_i htb
          have htbf : axisTopBit n = false := by simpa using htb
          have hslot' : Noun.slot (axisRest n) hd = some term := by
            simpa [htbf] using hslot
          simp only [hht2, List.singleton_append, List.mem_singleton] at hdesc
          subst u
          have hmap :
              (mapNTree GenMemoryRow.row
                (.node (gMemRow9 (memDecomposeSkel (.cell hd tl) hd tl) 0 z
                    (annotatedDecPub E (.cell hd tl) hd tl
                      (genAnnotatedDescentCont E z lmb [c] contCell contState
                        hd (axisRest n)).2
                      (genAnnotatedNounWalk E z lmb tl).2
                      (descentContRootState contState (axisRest n))
                      (nounWalkRootState tl) 0 0 lmb))
                  [ht2, (genAnnotatedNounWalk E z lmb tl).1])
                : NTree (MState × DTmem K))
              = .node (MState.decompose,
                  (memInputs z,
                    annotatedDecPub E (.cell hd tl) hd tl
                      (genAnnotatedDescentCont E z lmb [c] contCell contState
                        hd (axisRest n)).2
                      (genAnnotatedNounWalk E z lmb tl).2
                      (descentContRootState contState (axisRest n))
                      (nounWalkRootState tl) 0 0 lmb))
                  [mapNTree GenMemoryRow.row ht2, mappedNounWalk E z lmb tl] := by
            rw [mapped_gMemRow9]
            simp [memDecomposeSkel, mappedNounWalk]
          rw [hmap, axisMTree_decompose_node]
          obtain ⟨hr, hw, hrd, hvf⟩ :=
            ih (axisRest n) (axisRest_lt h2) hd hslot' ht2 (by rw [hht2]; simp)
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [axisPath_cons h2, htbf]
            exact VerifyRoute.left hr
              (readCount_nounWalk E z cfg.challenges.α _ tl)
              (verifyCount_nounWalk E z cfg.challenges.α _ tl)
          · exact ServiceWalk.decompose hw (serviceWalk_nounWalk services E z tl)
          · simp [readExps, readExps_nounWalk, hrd]
          · simp [verifyExps, verifyExps_nounWalk, hvf]

end

/-! ## F. Read-free siblings do not disturb `servedGen`

`recordPartition` is a literal list equality, so the emission order matters and a multiset argument
will not do.  Every off-path sibling of the annotated descent is a noun walk, which contains no
`read_root` node at all; this says such trees can be deleted from a forest without moving any
surviving record.  BFS interleaves levels, so the statement has to be two-sided and proved by
descent on the total size. -/

theorem forestFibre_flatMap_children (s : MState) :
    ∀ l : List (NTree (GenMemoryRow K)), forestFibre s l = 0 →
      forestFibre s (l.flatMap NTree.children) = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons t ts ih =>
      intro h
      cases t with
      | node g cs =>
        rw [forestFibre, treeFibre_node] at h
        have hcs : forestFibre s cs = 0 := by omega
        have hts : forestFibre s ts = 0 := by omega
        rw [List.flatMap_cons]
        simp only [NTree.children]
        rw [forestFibre_append, hcs, ih hts]

theorem servedGen_nil : servedGen ([] : List (NTree (GenMemoryRow K))) = [] := by
  unfold servedGen
  rw [bfsForest_nil]
  rfl

theorem flatMap_responseRecords_no_read :
    ∀ l : List (NTree (GenMemoryRow K)),
      forestFibre (.read_root : MState) l = 0 →
      (∀ t ∈ l, t.label.row.2.2.ver = false) →
      l.flatMap (fun t => responseRecords t.label.row.2.2) = [] := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons t ts ih =>
      intro h hver
      cases t with
      | node g cs =>
        rw [forestFibre, treeFibre_node] at h
        have hst : memPubSt g ≠ .read_root := by
          intro hEq
          rw [hEq] at h
          simp at h
        have hgver : g.row.2.2.ver = false := by
          simpa [NTree.label] using hver _ (List.mem_cons_self)
        rw [List.flatMap_cons, show (NTree.node g cs).label = g from rfl,
          responseRecords_of_ne_read _ hst hgver,
          ih (by omega) (fun u hu => hver u (List.mem_cons_of_mem _ hu)),
          List.nil_append]

/-- **Deleting read-free trees from either end of a forest leaves `servedGen` unchanged.** -/
theorem servedGen_sandwich_no_read :
    ∀ (n : ℕ) (W₁ T W₂ : List (NTree (GenMemoryRow K))),
      totalSize (W₁ ++ T ++ W₂) ≤ n →
      forestFibre (.read_root : MState) W₁ = 0 →
      forestFibre (.read_root : MState) W₂ = 0 →
      (∀ t ∈ bfsForest W₁, t.label.row.2.2.ver = false) →
      (∀ t ∈ bfsForest W₂, t.label.row.2.2.ver = false) →
      servedGen (W₁ ++ T ++ W₂) = servedGen T := by
  intro n
  induction n with
  | zero =>
      intro W₁ T W₂ hsz h1 h2 _ _
      have hlen : (W₁ ++ T ++ W₂).length = 0 := by
        have := totalSize_flatMap_children (W₁ ++ T ++ W₂)
        omega
      have hnil : W₁ ++ T ++ W₂ = [] := List.eq_nil_of_length_eq_zero hlen
      have h' := List.append_eq_nil_iff.mp hnil
      have hT : T = [] := (List.append_eq_nil_iff.mp h'.1).2
      rw [hnil, hT, servedGen_nil]
  | succ n ih =>
      intro W₁ T W₂ hsz h1 h2 hver1 hver2
      by_cases hnil : W₁ ++ T ++ W₂ = []
      · have hT : T = [] := by
          have h' := List.append_eq_nil_iff.mp hnil
          exact (List.append_eq_nil_iff.mp h'.1).2
        rw [hnil, hT, servedGen_nil]
      · rw [servedGen_of_ne_nil _ hnil]
        have hflat :
            (W₁ ++ T ++ W₂).flatMap (fun t => responseRecords t.label.row.2.2) =
              T.flatMap (fun t => responseRecords t.label.row.2.2) := by
          have hW1 : ∀ t ∈ W₁, t.label.row.2.2.ver = false := by
            intro t ht
            exact hver1 t ((mem_bfsForest _ _).mpr ⟨t, ht, InTree.here _⟩)
          have hW2 : ∀ t ∈ W₂, t.label.row.2.2.ver = false := by
            intro t ht
            exact hver2 t ((mem_bfsForest _ _).mpr ⟨t, ht, InTree.here _⟩)
          rw [List.flatMap_append, List.flatMap_append,
            flatMap_responseRecords_no_read W₁ h1 hW1,
            flatMap_responseRecords_no_read W₂ h2 hW2,
            List.nil_append, List.append_nil]
        have hchild :
            (W₁ ++ T ++ W₂).flatMap NTree.children =
              W₁.flatMap NTree.children ++ T.flatMap NTree.children
                ++ W₂.flatMap NTree.children := by
          rw [List.flatMap_append, List.flatMap_append]
        have hsz' : totalSize ((W₁ ++ T ++ W₂).flatMap NTree.children) ≤ n := by
          have hlen : 0 < (W₁ ++ T ++ W₂).length :=
            List.length_pos_iff.mpr hnil
          have := totalSize_flatMap_children (W₁ ++ T ++ W₂)
          omega
        have hver1' : ∀ t ∈ bfsForest (W₁.flatMap NTree.children),
            t.label.row.2.2.ver = false := by
          intro t ht
          obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp ht
          obtain ⟨p, hp, hchild⟩ := List.mem_flatMap.mp hc
          exact hver1 t ((mem_bfsForest _ _).mpr ⟨p, hp, InTree.sub hchild hin⟩)
        have hver2' : ∀ t ∈ bfsForest (W₂.flatMap NTree.children),
            t.label.row.2.2.ver = false := by
          intro t ht
          obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp ht
          obtain ⟨p, hp, hchild⟩ := List.mem_flatMap.mp hc
          exact hver2 t ((mem_bfsForest _ _).mpr ⟨p, hp, InTree.sub hchild hin⟩)
        rw [hflat, hchild]
        rw [ih _ _ _ (by rw [← hchild]; exact hsz')
          (forestFibre_flatMap_children _ W₁ h1)
          (forestFibre_flatMap_children _ W₂ h2) hver1' hver2']
        by_cases hTnil : T = []
        · subst hTnil
          rfl
        · rw [servedGen_of_ne_nil T hTnil]

theorem servedGen_cons_no_read (w : NTree (GenMemoryRow K))
    (T : List (NTree (GenMemoryRow K)))
    (h : treeFibre (.read_root : MState) w = 0)
    (hver : ∀ t ∈ bfsForest [w], t.label.row.2.2.ver = false) :
    servedGen (w :: T) = servedGen T := by
  have := servedGen_sandwich_no_read (totalSize ([w] ++ T ++ [])) [w] T []
    (le_refl _) (by simp [forestFibre, h]) rfl hver
    (by intro t ht; simp [bfsForest] at ht)
  simpa using this

theorem servedGen_snoc_no_read (w : NTree (GenMemoryRow K))
    (T : List (NTree (GenMemoryRow K)))
    (h : treeFibre (.read_root : MState) w = 0)
    (hver : ∀ t ∈ bfsForest [w], t.label.row.2.2.ver = false) :
    servedGen (T ++ [w]) = servedGen T := by
  have := servedGen_sandwich_no_read (totalSize ([] ++ T ++ [w])) [] T [w]
    (le_refl _) rfl (by simp [forestFibre, h])
    (by intro t ht; simp [bfsForest] at ht) hver
  simpa using this

/-- One node's `servedGen`, peeled. -/
theorem servedGen_singleton_node (g : GenMemoryRow K)
    (ch : List (NTree (GenMemoryRow K))) :
    servedGen [.node g ch] = responseRecords g.row.2.2 ++ servedGen ch := by
  rw [servedGen_of_ne_nil _ (List.cons_ne_nil _ _)]
  simp
  rfl

/-- **The continuation descent serves exactly what its continuation serves.**  Every node it adds is
a `decompose`, and every sibling it adds is a noun walk. -/
theorem servedGen_descentCont (E : Noun → ComputeTable.FP K) (z : K)
    (c : NTree (GenMemoryRow K)) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) :
    ∀ (remaining : ℕ) (current : Noun),
      ∀ u ∈ (genAnnotatedDescentCont E z lmb [c] contCell contState current remaining).1,
        servedGen [u] = servedGen [c] := by
  intro remaining
  induction remaining using Nat.strongRecOn with
  | _ n ih =>
    intro current u hu
    have hdesc := hu
    unfold genAnnotatedDescentCont at hdesc
    split at hdesc
    · simp only [List.mem_singleton] at hdesc
      subst u
      rfl
    · rename_i hge
      have h2 : 2 ≤ n := by omega
      obtain ⟨tt, htt⟩ := List.length_eq_one_iff.mp
        (genAnnotatedDescentCont_length_one (lmb := lmb) E z [c] contCell contState
          (by simp) (formulaTail current) (axisRest n))
      obtain ⟨ht2, hht2⟩ := List.length_eq_one_iff.mp
        (genAnnotatedDescentCont_length_one (lmb := lmb) E z [c] contCell contState
          (by simp) (formulaHead current) (axisRest n))
      split at hdesc
      · simp only [htt, List.cons_append, List.nil_append,
          List.mem_singleton] at hdesc
        subst u
        rw [servedGen_singleton_node]
        rw [responseRecords_of_ne_read _
          (by rw [gMemRow9_st, annotatedDecPub_st]; simp)
          (by simp [gMemRow9_ver, annotatedDecPub_ver])]
        rw [List.nil_append]
        rw [servedGen_cons_no_read _ _
          (genAnnotatedNounWalk_fibre_read E z (formulaHead current))
          (genAnnotatedNounWalk_bfs_ver_false E z (formulaHead current))]
        exact ih (axisRest n) (axisRest_lt h2) (formulaTail current) tt
          (by rw [htt]; simp)
      · simp only [hht2, List.singleton_append, List.mem_singleton] at hdesc
        subst u
        rw [servedGen_singleton_node]
        rw [responseRecords_of_ne_read _
          (by rw [gMemRow9_st, annotatedDecPub_st]; simp)
          (by simp [gMemRow9_ver, annotatedDecPub_ver])]
        rw [List.nil_append]
        rw [show ([ht2, (genAnnotatedNounWalk E z lmb (formulaTail current)).1])
            = [ht2] ++ [(genAnnotatedNounWalk E z lmb (formulaTail current)).1] from rfl,
          servedGen_snoc_no_read _ _
          (genAnnotatedNounWalk_fibre_read E z (formulaTail current))
          (genAnnotatedNounWalk_bfs_ver_false E z (formulaTail current))]
        exact ih (axisRest n) (axisRest_lt h2) (formulaHead current) ht2
          (by rw [hht2]; simp)


/-! ## G. The two-record chain at arbitrary axes

`genRowMemForest` (`GenMem.lean:1066`) chains two consecutive requests whenever
`r₁.child = r₂.root`.  `GenTierAMemoryTrace.serviceWalk_chain32` is that shape at axes `3` then `2`;
this is the same at any pair of axes.  The chained tree interleaves the two records —
`read(r₁) ↓ read(r₂) ↓ verify(r₁) ↓ verify(r₂)` — so the two exponents have to be separated, which is
the one extra hypothesis. -/

noncomputable section

/-- The inner continuation of a two-record chain: `read(r₂)` above `verify(r₁)`. -/
theorem chainInner_pair_props {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (services : List (Service cfg exec)) (s2 : Service cfg exec)
    (E : Noun → ComputeTable.FP K) (z : K) (r1 r2 : MemRecordReq)
    (hlink : r1.child = r2.root)
    (hs2 : s2 ∈ services) (hroot2 : s2.root = r2.root) (hchild2 : s2.child = r2.child)
    (haxis2 : s2.axis = r2.axis)
    (hexp2 : s2.exponent =
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp))
    (hslot2 : Noun.slot r2.axis r2.root = some r2.child)
    (hne : timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp) ≠
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp)) :
    ∃ c, (genAnnotatedChainedInner E z cfg.challenges.α lmb r1 [r2]).1 = [c] ∧
      VerifyRoute (timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp))
          r1.child ((r1.axis : ℕ) : K) [] r1.child
          (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row c)) ∧
      ServiceWalk services r1.child
          (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row c)) ∧
      readExps (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row c)) =
        [timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp)] ∧
      verifyExps (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row c)) =
        [timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp),
         timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp)] ∧
      servedGen [c] =
        [⟨E r2.root, E r2.child, (r2.axis : K), cfg.challenges.α ^ r2.recordExp⟩] := by
  set ex1 := timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp) with hex1
  set ex2 := timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp) with hex2
  -- the verify leaf of `r₂`
  set vt2 := (genAnnotatedVerify E z lmb r2.root r2.child r2.axis
    (cfg.challenges.α ^ r2.recordExp) r2.recordExp).1 with hvt2
  set vc2 := (genAnnotatedVerify E z lmb r2.root r2.child r2.axis
    (cfg.challenges.α ^ r2.recordExp) r2.recordExp).2 with hvc2
  have hleaf : axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row vt2) =
      .verify ex2 ((r2.axis : ℕ) : K)
        (axisMTree cfg.challenges.α (mappedNounWalk E z lmb r2.child)) := by
    rw [hvt2, axisMTree_verify]
  -- the descent from `r₂.root` down to that leaf
  obtain ⟨d2, hd2⟩ := List.length_eq_one_iff.mp
    (genAnnotatedDescentCont_length_one (lmb := lmb) E z [vt2] vc2 (chainedInnerRootState [])
      (by simp) r2.root r2.axis)
  obtain ⟨hroute2, hwalk2, hread2, hverify2⟩ :=
    descentCont_bundle services E z vt2 vc2 (chainedInnerRootState [])
      ex2 r2.child ((r2.axis : ℕ) : K) r2.child [] [ex2]
      (by rw [hleaf]
          exact VerifyRoute.here rfl rfl
            (readCount_nounWalk E z cfg.challenges.α _ r2.child)
            (verifyCount_nounWalk E z cfg.challenges.α _ r2.child))
      (by rw [hleaf]
          exact ServiceWalk.verify (serviceWalk_nounWalk services E z r2.child))
      (by rw [hleaf]; simp [readExps, readExps_nounWalk])
      (by rw [hleaf]; simp [verifyExps, verifyExps_nounWalk])
      r2.axis r2.root hslot2 d2 (by rw [hd2]; simp)
  have hserved2 : servedGen [d2] = [] := by
    rw [servedGen_descentCont E z vt2 vc2 (chainedInnerRootState [])
      r2.axis r2.root d2 (by rw [hd2]; simp)]
    refine servedGen_no_read _ ?_ ?_
    · simp [forestFibre, hvt2, genAnnotatedVerify_fibre_read]
    · intro t ht
      rw [hvt2] at ht
      exact genAnnotatedVerify_bfs_ver_false E z r2.root r2.child
        r2.axis (cfg.challenges.α ^ r2.recordExp) r2.recordExp t ht
  -- the interleaved inner node: `read(r₂)` above `verify(r₁)`
  set vp1 := annotatedVerifyPub E r1.root r1.child r1.axis (cfg.challenges.α ^ r1.recordExp)
    (genAnnotatedDescentCont E z lmb [vt2] vc2 (chainedInnerRootState [])
      r2.root r2.axis).2 0 0 lmb with hvp1
  set vn1 : NTree (GenMemoryRow K) :=
    .node (gMemRow9 (memVerifySkelAx r1.root r1.child r1.axis) r1.recordExp z vp1)
      (genAnnotatedDescentCont E z lmb [vt2] vc2 (chainedInnerRootState [])
        r2.root r2.axis).1 with hvn1
  set rp2 := annotatedReadPub E r2.root r2.child r2.axis (cfg.challenges.α ^ r2.recordExp)
    vp1.pt 0 0 lmb with hrp2
  set rn2 : NTree (GenMemoryRow K) :=
    .node (gMemRow9 (memReadSkelAx r2.root r2.child r2.axis) r2.recordExp z rp2)
      [vn1] with hrn2
  have hinner : (genAnnotatedChainedInner E z cfg.challenges.α lmb r1 [r2]).1 = [rn2] := by
    rw [hrn2, hvn1, hrp2, hvp1, hvt2, hvc2]
    unfold genAnnotatedChainedInner
    simp only [genAnnotatedChainedInner_nil]
  have hvn1map : axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row vn1) =
      .verify ex1 ((r1.axis : ℕ) : K)
        (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row d2)) := by
    rw [hvn1, hd2, mapped_gMemRow9,
      show (memVerifySkelAx r1.root r1.child r1.axis).state = MState.verify_child from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [axisMTree_verify_node, hvp1]
    simp only [annotatedVerifyPub, ← hex1]
  have hrn2map : axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row rn2) =
      .read ex2 (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row vn1)) := by
    rw [hrn2, mapped_gMemRow9,
      show (memReadSkelAx r2.root r2.child r2.axis).state = MState.read_root from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [axisMTree_read_node, hrp2]
    simp only [annotatedReadPub, ← hex2]
  have hrd0 : readCount ex1 (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row d2)) = 0 := by
    rw [readCount_eq_count, hread2]
    simp
  have hvf0 : verifyCount ex1 (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row d2)) = 0 := by
    rw [verifyCount_eq_count, hverify2, List.count_cons]
    simp only [List.count_nil, Nat.zero_add, beq_iff_eq, ite_eq_right_iff,
      Nat.one_ne_zero, imp_false]
    exact Ne.symm hne
  refine ⟨rn2, hinner, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrn2map, hvn1map]
    exact VerifyRoute.read_other (Ne.symm hne)
      (VerifyRoute.here rfl rfl hrd0 hvf0)
  · rw [hrn2map, hvn1map]
    refine ServiceWalk.read s2 hs2 hexp2 (by rw [hroot2, hlink]) ?_ ?_
    · have hrecax : s2.record.axis = ((r2.axis : ℕ) : K) := by
        rw [s2.realization.axis_realizes, haxis2]
      rw [hchild2, hrecax, haxis2]
      refine VerifyRoute.verify_other hne ?_
      rw [← hlink] at hroute2
      exact hroute2
    · refine ServiceWalk.verify ?_
      rw [← hlink] at hwalk2
      exact hwalk2
  · rw [hrn2map, hvn1map]
    simp [readExps, hread2]
  · rw [hrn2map, hvn1map]
    simp [verifyExps, hverify2]
  · rw [hrn2, servedGen_singleton_node,
      responseRecords_eq_singleton_of_read_root _ (by
        rw [gMemRow9_st, hrp2, annotatedReadPub_st])
        (by rw [gMemRow9_ver, hrp2, annotatedReadPub_ver])]
    rw [show (gMemRow9 (memReadSkelAx r2.root r2.child r2.axis) r2.recordExp z rp2).row.2.2.mem
        = ⟨E r2.root, E r2.child, (r2.axis : K), cfg.challenges.α ^ r2.recordExp⟩ from by
      rw [gMemRow9_mem, hrp2, annotatedReadPub_mem]]
    rw [hvn1, hd2, servedGen_singleton_node,
      responseRecords_of_ne_read _ (by
        rw [gMemRow9_st, hvp1, annotatedVerifyPub_st]; simp)
        (by rw [gMemRow9_ver, hvp1, annotatedVerifyPub_ver]),
      List.nil_append]
    rw [show ([d2] : List (NTree (GenMemoryRow K))) = [d2] from rfl, hserved2]
    simp

/-- **The two-record chain, at any pair of axes.**  `serviceWalk_chain32` is the `@3`-then-`@2`
case. -/
theorem chainPair_bundle {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (services : List (Service cfg exec)) (s1 s2 : Service cfg exec)
    (E : Noun → ComputeTable.FP K) (z : K) (r1 r2 : MemRecordReq)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z cfg.challenges.α lmb [r1, r2] = some t)
    (hlink : r1.child = r2.root)
    (hs1 : s1 ∈ services) (hroot1 : s1.root = r1.root) (hchild1 : s1.child = r1.child)
    (haxis1 : s1.axis = r1.axis)
    (hexp1 : s1.exponent =
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp))
    (hs2 : s2 ∈ services) (hroot2 : s2.root = r2.root) (hchild2 : s2.child = r2.child)
    (haxis2 : s2.axis = r2.axis)
    (hexp2 : s2.exponent =
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp))
    (hslot1 : Noun.slot r1.axis r1.root = some r1.child)
    (hslot2 : Noun.slot r2.axis r2.root = some r2.child)
    (hne : timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp) ≠
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp)) :
    ServiceWalk services r1.root
        (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row t)) ∧
      readExps (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row t)) =
        [timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp),
         timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp)] ∧
      verifyExps (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row t)) =
        [timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp),
         timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp)] ∧
      servedGen [t] =
        [⟨E r1.root, E r1.child, (r1.axis : K), cfg.challenges.α ^ r1.recordExp⟩,
         ⟨E r2.root, E r2.child, (r2.axis : K), cfg.challenges.α ^ r2.recordExp⟩] := by
  set ex1 := timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp) with hex1
  set ex2 := timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp) with hex2
  obtain ⟨c, hinner, hroutec, hwalkc, hreadc, hverifyc, hservedc⟩ :=
    chainInner_pair_props services s2 E z r1 r2 hlink hs2 hroot2 hchild2 haxis2
      hexp2 hslot2 hne
  set cc := (genAnnotatedChainedInner E z cfg.challenges.α lmb r1 [r2]).2 with hcc
  obtain ⟨d1, hd1⟩ := List.length_eq_one_iff.mp
    (genAnnotatedDescentCont_length_one (lmb := lmb) E z [c] cc (chainedInnerRootState [r2])
      (by simp) r1.root r1.axis)
  obtain ⟨hroute1, hwalk1, hread1, hverify1⟩ :=
    descentCont_bundle services E z c cc (chainedInnerRootState [r2])
      ex1 r1.child ((r1.axis : ℕ) : K) r1.child [ex2] [ex1, ex2]
      hroutec hwalkc hreadc hverifyc r1.axis r1.root hslot1 d1 (by rw [hd1]; simp)
  have hserved1 : servedGen [d1] =
      [⟨E r2.root, E r2.child, (r2.axis : K), cfg.challenges.α ^ r2.recordExp⟩] := by
    rw [servedGen_descentCont E z c cc (chainedInnerRootState [r2]) r1.axis r1.root d1
      (by rw [hd1]; simp)]
    exact hservedc
  have hteq : t = .node (gMemRow9 (memReadSkelAx r1.root r1.child r1.axis)
      r1.recordExp z (annotatedReadPub E r1.root r1.child r1.axis
        (cfg.challenges.α ^ r1.recordExp)
        (genAnnotatedDescentCont E z lmb [c] cc (chainedInnerRootState [r2])
          r1.root r1.axis).2 0 0 lmb)) [d1] := by
    have hp := genAnnotatedChainedTree_pair (lmb := lmb) E z cfg.challenges.α r1 r2
    rw [hp] at ht
    injection ht with ht
    rw [← ht, hinner, ← hcc, hd1]
  have htmap : axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row t) =
      .read ex1 (axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row d1)) := by
    rw [hteq, mapped_gMemRow9,
      show (memReadSkelAx r1.root r1.child r1.axis).state = MState.read_root from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [axisMTree_read_node]
    simp only [annotatedReadPub, ← hex1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htmap]
    refine ServiceWalk.read s1 hs1 hexp1 hroot1 ?_ hwalk1
    have hrecax : s1.record.axis = ((r1.axis : ℕ) : K) := by
      rw [s1.realization.axis_realizes, haxis1]
    rw [hchild1, hrecax, haxis1]
    exact hroute1
  · rw [htmap]; simp [readExps, hread1]
  · rw [htmap]; simp [verifyExps, hverify1]
  · rw [hteq, servedGen_singleton_node,
      responseRecords_eq_singleton_of_read_root _ (by
        rw [gMemRow9_st, annotatedReadPub_st])
        (by rw [gMemRow9_ver, annotatedReadPub_ver])]
    rw [show (gMemRow9 (memReadSkelAx r1.root r1.child r1.axis) r1.recordExp z
        (annotatedReadPub E r1.root r1.child r1.axis (cfg.challenges.α ^ r1.recordExp)
          (genAnnotatedDescentCont E z lmb [c] cc (chainedInnerRootState [r2])
            r1.root r1.axis).2 0 0 lmb)).row.2.2.mem
        = ⟨E r1.root, E r1.child, (r1.axis : K), cfg.challenges.α ^ r1.recordExp⟩ from by
      rw [gMemRow9_mem, annotatedReadPub_mem]]
    rw [hserved1]
    rfl

/-- **One forest root, a two-record chain, ANY axes: a `RootTrace`.** -/
noncomputable def rootTraceOfChainedPair
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (E : Noun → ComputeTable.FP K) (z : K) (r1 r2 : MemRecordReq)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z cfg.challenges.α lmb [r1, r2] = some t)
    (hlink : r1.child = r2.root)
    (s1 s2 : Service cfg exec)
    (hroot1 : s1.root = r1.root) (hchild1 : s1.child = r1.child)
    (haxis1 : s1.axis = r1.axis)
    (hexp1 : s1.exponent =
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp))
    (hrec1 : s1.record =
      ⟨E r1.root, E r1.child, (r1.axis : K), cfg.challenges.α ^ r1.recordExp⟩)
    (hroot2 : s2.root = r2.root) (hchild2 : s2.child = r2.child)
    (haxis2 : s2.axis = r2.axis)
    (hexp2 : s2.exponent =
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp))
    (hrec2 : s2.record =
      ⟨E r2.root, E r2.child, (r2.axis : K), cfg.challenges.α ^ r2.recordExp⟩)
    (hslot1 : Noun.slot r1.axis r1.root = some r1.child)
    (hslot2 : Noun.slot r2.axis r2.root = some r2.child)
    (hne : timestampExp cfg.challenges.α (cfg.challenges.α ^ r1.recordExp) ≠
      timestampExp cfg.challenges.α (cfg.challenges.α ^ r2.recordExp))
    (hax : exactAxisTree cfg exec i
        = axisMTree cfg.challenges.α (mapNTree GenMemoryRow.row t))
    (hsrv : rootResponseRecords exec i = servedGen [t]) :
    RootTrace cfg exec i where
  subject := r1.root
  services := [s1, s2]
  recordPartition := by
    rw [hsrv, (chainPair_bundle [s1, s2] s1 s2 E z r1 r2 t ht hlink (by simp)
      hroot1 hchild1 haxis1 hexp1 (by simp) hroot2 hchild2 haxis2 hexp2
      hslot1 hslot2 hne).2.2.2]
    simp [hrec1, hrec2]
  readPartition := by
    rw [hax, (chainPair_bundle [s1, s2] s1 s2 E z r1 r2 t ht hlink (by simp)
      hroot1 hchild1 haxis1 hexp1 (by simp) hroot2 hchild2 haxis2 hexp2
      hslot1 hslot2 hne).2.1]
    simp [hexp1, hexp2]
  verifyPartition := by
    rw [hax, (chainPair_bundle [s1, s2] s1 s2 E z r1 r2 t ht hlink (by simp)
      hroot1 hchild1 haxis1 hexp1 (by simp) hroot2 hchild2 haxis2 hexp2
      hslot1 hslot2 hne).2.2.1]
    simp [hexp1, hexp2]
  traversal := by
    rw [hax]
    exact (chainPair_bundle [s1, s2] s1 s2 E z r1 r2 t ht hlink (by simp)
      hroot1 hchild1 haxis1 hexp1 (by simp) hroot2 hchild2 haxis2 hexp2
      hslot1 hslot2 hne).1

end
