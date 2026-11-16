/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulTraceConfined.lean

  **`TraceConfined 568 (airReorder mmTree)` as a lemma, not a binder.**

  Combinator induction along the `seedOK_mm` spine (`gen_cons`, `gen_op0`,
  `gen_op1`, `gen_invokeMac`, `gen_macArm_one_m1`, slam unfolding).
  Each `confined_gen_*` takes confined subtrees plus three `leaves ≤ Λ`
  facts at the root — `RowNounsConfined`, weaker than `RowLeafWindow`
  (`GenLeafWindow.lean`).  No 401-row unfold, no `decide` at an
  extension field, no growth invariant.

  Seed-independent: every noun is a subnoun of the subject, the
  formula, a threaded core of 62 leaves, or an atom result.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulLeafBound
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSize
import Nock.NockVMROM.Thm54.TraceGen.GenTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensusWindow
import Nock.NockVMROM.Thm54.TraceGen.GenSubISAWindow
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open ComputeTable

variable {K : Type} [Field K]

/-! ## Monotonicity and the node combinator -/

theorem traceConfined_mono {Λ Λ' : ℕ} {t : NTree (GenComputeRow K)}
    (h : Λ ≤ Λ') (ht : TraceConfined Λ t) : TraceConfined Λ' t := by
  intro g hg
  obtain ⟨hs, hf, he⟩ := ht g hg
  exact ⟨le_trans hs h, le_trans hf h, le_trans he h⟩

theorem rowNouns_of_leaves {Λ : ℕ} {g : GenComputeRow K}
    (hs : g.skel.subject.leaves ≤ Λ)
    (hf : g.skel.formula.leaves ≤ Λ)
    (he : g.skel.evaluation.leaves ≤ Λ) :
    RowNounsConfined Λ g :=
  ⟨hs, hf, he⟩

/-- Subtrees confined plus the root row's three nouns gives the composite. -/
theorem confined_of_children {Λ : ℕ} {lab : GenComputeRow K}
    {cs : List (NTree (GenComputeRow K))}
    (hroot : RowNounsConfined Λ lab)
    (hcs : ∀ c ∈ cs, TraceConfined Λ c) :
    TraceConfined Λ (.node lab cs) := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest [.node lab cs] u).mp hu
  simp [List.mem_singleton] at hr
  subst hr
  cases hin with
  | here => exact hroot
  | sub hs hu' => exact confined_inTree (hcs _ hs) hu'

/-! ## Per-constructor `confined_gen_*`

Root-row bounds are `leaves_le_cell_*` / `slot_leaves_le` / atom facts,
never a `2 · (F ⊔ S)` growth theorem. -/

theorem confined_gen_op0 {Λ n : ℕ} {s : Noun} {ax : ℕ} {r : Noun}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (hslot : Noun.slot ax s = some r)
    (h : genComputeSkeleton (K := K) (n + 1) s (op0 ax) = .ok (t, res))
    (hs : s.leaves ≤ Λ) (hΛ : 2 ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_op0 (K := K) n hslot
  rw [(gen_ok_unique h h').1]
  refine confined_of_children ?_ (fun _ hc => by cases hc)
  refine rowNouns_of_leaves ?_ ?_ ?_
  · simp [skelNode, genSkelOp0]; exact hs
  · simp [skelNode, genSkelOp0, op0, cell_leaves, atom_leaves]; exact hΛ
  · simp [skelNode, genSkelOp0]
    exact le_trans (slot_leaves_le ax s hslot) hs

theorem confined_gen_op1 {Λ n : ℕ} {s : Noun} {k : ℕ}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) s (op1 k) = .ok (t, res))
    (hs : s.leaves ≤ Λ) (hΛ : 2 ≤ Λ) :
    TraceConfined Λ t := by
  have h1 : 1 ≤ Λ := le_trans (by decide : 1 ≤ 2) hΛ
  have h' := gen_op1 (K := K) n s k
  rw [(gen_ok_unique h h').1]
  refine confined_of_children ?_ (fun _ hc => by cases hc)
  refine rowNouns_of_leaves ?_ ?_ ?_
  · simp [skelNode, genSkelOp1]; exact hs
  · simp [skelNode, genSkelOp1, op1, cell_leaves, atom_leaves]; exact hΛ
  · simp [skelNode, genSkelOp1, atom_leaves]; exact h1

theorem confined_gen_quote {Λ n : ℕ} {s result : Noun}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) s (quote result) = .ok (t, res))
    (hs : s.leaves ≤ Λ) (hf : (quote result).leaves ≤ Λ)
    (hr : result.leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_quote (K := K) n s result
  rw [(gen_ok_unique h h').1]
  refine confined_of_children ?_ (fun _ hc => by cases hc)
  refine rowNouns_of_leaves ?_ ?_ ?_
  · simp [skelNode, genSkelOp1]; exact hs
  · simp [skelNode, genSkelOp1]; exact hf
  · simp [skelNode, genSkelOp1]; exact hr

theorem confined_gen_cons {Λ n : ℕ}
    {s leftHead leftTail tail lRes rRes : Noun}
    {lTree rTree t : NTree (GenComputeRow K)} {res : Noun}
    (hl : genComputeSkeleton (K := K) n s (Noun.cell leftHead leftTail) =
      .ok (lTree, lRes))
    (hr : genComputeSkeleton (K := K) n s tail = .ok (rTree, rRes))
    (h : genComputeSkeleton (K := K) (n + 1) s
      (Noun.cell (Noun.cell leftHead leftTail) tail) = .ok (t, res))
    (ihl : TraceConfined Λ lTree) (ihr : TraceConfined Λ rTree)
    (hs : s.leaves ≤ Λ)
    (hf : (Noun.cell (Noun.cell leftHead leftTail) tail).leaves ≤ Λ)
    (he : (Noun.cell lRes rRes).leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_cons (K := K) n hl hr
  rw [(gen_ok_unique h h').1]
  refine confined_of_children ?_ ?_
  · refine rowNouns_of_leaves ?_ ?_ ?_
    · simp [skelNode, genSkelCons]; exact hs
    · simp [skelNode, genSkelCons]; exact hf
    · simp [skelNode, genSkelCons]; exact he
  · intro c hc
    simp [NTree.children] at hc
    rcases hc with rfl | rfl
    · exact ihl
    · exact ihr

theorem confined_gen_op4 {Λ n : ℕ} {s tail callResult result : Noun}
    {callTree t : NTree (GenComputeRow K)} {res : Noun}
    (hcall : genComputeSkeleton (K := K) n s tail = .ok (callTree, callResult))
    (hinc : Noun.lus callResult = some result)
    (h : genComputeSkeleton (K := K) (n + 1) s (op4 tail) = .ok (t, res))
    (ih : TraceConfined Λ callTree)
    (hs : s.leaves ≤ Λ) (hf : (op4 tail).leaves ≤ Λ)
    (he : result.leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_op4 (K := K) n hcall hinc
  rw [(gen_ok_unique h h').1]
  refine confined_of_children ?_ ?_
  · refine rowNouns_of_leaves ?_ ?_ ?_
    · simp [skelNode, genSkelOp4]; exact hs
    · simp [skelNode, genSkelOp4]; exact hf
    · simp [skelNode, genSkelOp4]; exact he
  · intro c hc
    simp [NTree.children] at hc
    subst c
    exact ih

theorem confined_gen_op5 {Λ n : ℕ} {s b c sf1 sf2 : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n s c = .ok (cTree, sf2))
    (h : genComputeSkeleton (K := K) (n + 1) s (op5 b c) = .ok (t, res))
    (ihb : TraceConfined Λ bTree) (ihc : TraceConfined Λ cTree)
    (hs : s.leaves ≤ Λ) (hf : (op5 b c).leaves ≤ Λ) (hΛ : 1 ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_op5 (K := K) n hb hc
  rw [(gen_ok_unique h h').1]
  refine confined_of_children ?_ ?_
  · refine rowNouns_of_leaves ?_ ?_ ?_
    · simp [skelNode, genSkelOp5]; exact hs
    · simp [skelNode, genSkelOp5]; exact hf
    · have htis : (Noun.tis sf1 sf2).leaves = 1 := by
        simp [Noun.tis]; split <;> simp [atom_leaves]
      simp [skelNode, genSkelOp5, htis]; exact hΛ
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihc

theorem confined_gen_op6_zero {Λ n : ℕ} {s b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (condTree, .atom 0))
    (hc : genComputeSkeleton (K := K) n s c = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op6 b c d) = .ok (t, res))
    (ihb : TraceConfined Λ condTree) (ihc : TraceConfined Λ takenTree)
    (hs : s.leaves ≤ Λ) (hf : (op6 b c d).leaves ≤ Λ)
    (he : result.leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_op6_zero (K := K) (d := d) n hb hc
  rw [(gen_ok_unique h h').1]
  refine confined_of_children ?_ ?_
  · refine rowNouns_of_leaves ?_ ?_ ?_
    · simp [skelNode, genSkelOp6]; exact hs
    · simp [skelNode, genSkelOp6]; exact hf
    · simp [skelNode, genSkelOp6]; exact he
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihc

theorem confined_gen_op6_one {Λ n : ℕ} {s b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (condTree, .atom 1))
    (hd : genComputeSkeleton (K := K) n s d = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op6 b c d) = .ok (t, res))
    (ihb : TraceConfined Λ condTree) (ihd : TraceConfined Λ takenTree)
    (hs : s.leaves ≤ Λ) (hf : (op6 b c d).leaves ≤ Λ)
    (he : result.leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_op6_one (K := K) (c := c) n hb hd
  rw [(gen_ok_unique h h').1]
  refine confined_of_children ?_ ?_
  · refine rowNouns_of_leaves ?_ ?_ ?_
    · simp [skelNode, genSkelOp6]; exact hs
    · simp [skelNode, genSkelOp6]; exact hf
    · simp [skelNode, genSkelOp6]; exact he
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihd

theorem confined_gen_op7 {Λ n : ℕ} {s b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n sb c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op7 b c) = .ok (t, res))
    (ihb : TraceConfined Λ bTree) (ihc : TraceConfined Λ cTree)
    (hs : s.leaves ≤ Λ) (hf : (op7 b c).leaves ≤ Λ)
    (he : result.leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_op7 (K := K) n hb hc
  rw [(gen_ok_unique h h').1]
  refine confined_of_children ?_ ?_
  · refine rowNouns_of_leaves ?_ ?_ ?_
    · simp [skelNode, genSkelOp7]; exact hs
    · simp [skelNode, genSkelOp7]; exact hf
    · simp [skelNode, genSkelOp7]; exact he
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihc

theorem confined_gen_invokeAxis {Λ n : ℕ} {s core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree t : NTree (GenComputeRow K)} {res : Noun}
    (hcore : genComputeSkeleton (K := K) (n + 2) s (op0 1) =
      .ok (coreTree, core))
    (hslotA : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) (n + 2) core arm =
      .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 3) s (invokeAxis axis) = .ok (t, res))
    (ihc : TraceConfined Λ coreTree) (iha : TraceConfined Λ invokeTree)
    (hs : s.leaves ≤ Λ) (hf : (invokeAxis axis).leaves ≤ Λ)
    (he : result.leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_invokeAxis (K := K) n hcore hslotA harm
  rw [(gen_ok_unique h h').1]
  refine confined_of_children ?_ ?_
  · refine rowNouns_of_leaves ?_ ?_ ?_
    · simp [skelNode, genSkelOp9]; exact hs
    · simp [skelNode, genSkelOp9]; exact hf
    · simp [skelNode, genSkelOp9]; exact he
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihc
    · exact iha

theorem confined_gen_slam {Λ n : ℕ} {axis : ℕ}
    {s bHead bTail sampleF battery sample arm result : Noun}
    {battTree sampTree invokeTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) (n + 3) s (Noun.cell bHead bTail) =
      .ok (battTree, battery))
    (hsamp : genComputeSkeleton (K := K) (n + 3) s sampleF =
      .ok (sampTree, sample))
    (hslot : Noun.slot axis (Noun.cell battery sample) = some arm)
    (harm : genComputeSkeleton (K := K) (n + 3) (Noun.cell battery sample) arm =
      .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 5) s
      (slam (Noun.cell bHead bTail) sampleF axis) = .ok (t, res))
    (ihb : TraceConfined Λ battTree) (ihs : TraceConfined Λ sampTree)
    (iha : TraceConfined Λ invokeTree)
    (hs : s.leaves ≤ Λ)
    (hf : (slam (Noun.cell bHead bTail) sampleF axis).leaves ≤ Λ)
    (he : result.leaves ≤ Λ)
    (hcore : (Noun.cell battery sample).leaves ≤ Λ)
    (_harmF : arm.leaves ≤ Λ)
    (hinv : (invokeAxis axis).leaves ≤ Λ)
    (hpair : (Noun.cell (Noun.cell bHead bTail) sampleF).leaves ≤ Λ) :
    TraceConfined Λ t := by
  have hpairT :=
    gen_cons (K := K) (n + 3) (lTree := battTree) (rTree := sampTree) hb hsamp
  have hcoreT := gen_op0 (K := K) (n + 2) (slot_1 (.cell battery sample))
  have hax := gen_invokeAxis (K := K) (n + 1) hcoreT hslot harm
  have hop := gen_op7 (K := K) (n + 4) hpairT hax
  have huniq := gen_ok_unique h (by simpa [slam] using hop)
  rw [huniq.1]
  have ihpair := confined_gen_cons (Λ := Λ) hb hsamp hpairT ihb ihs hs hpair
    (by simpa [cell_leaves] using hcore)
  have h2 : 2 ≤ Λ := by
    have hbpos := leaves_pos battery
    have hspos := leaves_pos sample
    simp [cell_leaves] at hcore
    omega
  have ihcore := confined_gen_op0 (Λ := Λ) (slot_1 (Noun.cell battery sample)) hcoreT
    hcore h2
  have ihax := confined_gen_invokeAxis (Λ := Λ) hcoreT hslot harm hax
    ihcore iha hcore hinv he
  exact confined_gen_op7 (Λ := Λ) hpairT hax hop ihpair ihax hs
    (by simpa [slam] using hf) he

/-! ## Threaded-core leaf counts (not a computation) -/

theorem addCore_leaves (acc i m : Noun) :
    (addCore acc i m).leaves =
      addArm.leaves + acc.leaves + i.leaves + m.leaves := by
  simp [addCore, cell_leaves]; omega

theorem macCoreAt_leaves (acc i n m : Noun) :
    (macCoreAt acc i n m).leaves =
      mmBattery.leaves + acc.leaves + i.leaves + n.leaves + m.leaves := by
  simp [macCoreAt, cell_leaves]; omega

theorem addCore_atoms_leaves (acc i m : ℕ) :
    (addCore (.atom acc) (.atom i) (.atom m)).leaves = 26 := by
  rw [addCore_leaves, addArm_leaves, atom_leaves, atom_leaves, atom_leaves]

theorem macCore_atoms_leaves (acc n m : ℕ) :
    (macCore (.atom acc) (.atom n) (.atom m)).leaves = 62 := by
  rw [macCore, macCoreAt_leaves, mmBattery_leaves, atom_leaves, atom_leaves,
    atom_leaves, atom_leaves]

theorem mmSubject_leaves_eq : mmSubject.leaves = 8 := by
  decide

theorem invokeAxis_leaves_le (axis : ℕ) : (invokeAxis axis).leaves = 4 :=
  invokeAxis_leaves axis

/-! ## Arm combinators at `Λ ≥ 62`

Every subject here is an atom-core (`26` or `62`); every evaluation is
an atom or a 4-leaf sample cell. -/

theorem confined_addArm_done {Λ n : ℕ} (acc m : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (addCore acc m m) addArm =
      .ok (t, acc))
    (hs : (addCore acc m m).leaves ≤ Λ) (hΛ : 23 ≤ Λ)
    (he : acc.leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h2 : 2 ≤ Λ := le_trans (by decide : 2 ≤ 23) hΛ
  have h1 : 1 ≤ Λ := le_trans (by decide : 1 ≤ 2) h2
  have hf : addArm.leaves ≤ Λ := le_trans (le_of_eq addArm_leaves) hΛ
  have h14 := gen_op0 (K := K) (n + 3) (addCore_slot14 acc m m)
  have h15 := gen_op0 (K := K) (n + 3) (addCore_slot15 acc m m)
  have h5eq := gen_op5 (K := K) (n + 4) h14 h15
  have ih5 := confined_gen_op5 (Λ := Λ) h14 h15 h5eq
    (confined_gen_op0 (Λ := Λ) (addCore_slot14 acc m m) h14 hs h2)
    (confined_gen_op0 (Λ := Λ) (addCore_slot15 acc m m) h15 hs h2)
    hs (by
      simp [op5, op0, cell_leaves, atom_leaves]
      have := addArm_leaves
      omega) h1
  rw [tis_self m] at h5eq
  have hthen := gen_op0 (K := K) (n + 4) (addCore_slot6 acc m m)
  have hop6 := gen_op6_zero (K := K) (n + 5)
    (d := slam (op0 2) addNewSample 2) h5eq hthen
  have huniq := gen_ok_unique h (by simpa [addArm] using hop6)
  rw [huniq.1]
  exact confined_gen_op6_zero (Λ := Λ) h5eq hthen hop6
    (by convert ih5; simp [tis_self])
    (confined_gen_op0 (Λ := Λ) (addCore_slot6 acc m m) hthen hs h2)
    hs (by simpa [addArm] using hf) he

/-! ## Uniform `62 ≤ Λ` facts (threaded cores, not a growth theorem) -/

theorem two_le_of_62 {Λ : ℕ} (h : 62 ≤ Λ) : 2 ≤ Λ :=
  le_trans (by decide : 2 ≤ 62) h

theorem one_le_of_62 {Λ : ℕ} (h : 62 ≤ Λ) : 1 ≤ Λ :=
  le_trans (by decide : 1 ≤ 62) h

theorem twentythree_le_of_62 {Λ : ℕ} (h : 62 ≤ Λ) : 23 ≤ Λ :=
  le_trans (by decide : 23 ≤ 62) h

theorem addCore_atoms_le (acc i m : ℕ) {Λ : ℕ} (h : 62 ≤ Λ) :
    (addCore (.atom acc) (.atom i) (.atom m)).leaves ≤ Λ :=
  le_trans (le_of_eq (addCore_atoms_leaves acc i m))
    (le_trans (by decide : 26 ≤ 62) h)

theorem macCore_atoms_le (acc n m : ℕ) {Λ : ℕ} (h : 62 ≤ Λ) :
    (macCore (.atom acc) (.atom n) (.atom m)).leaves ≤ Λ :=
  le_trans (le_of_eq (macCore_atoms_leaves acc n m)) h

theorem macCoreAt_atoms_le (acc i n m : ℕ) {Λ : ℕ} (h : 62 ≤ Λ) :
    (macCoreAt (.atom acc) (.atom i) (.atom n) (.atom m)).leaves ≤ Λ := by
  rw [macCoreAt_leaves, mmBattery_leaves, atom_leaves, atom_leaves, atom_leaves,
    atom_leaves]
  exact h

theorem atom_le_of_62 (k : ℕ) {Λ : ℕ} (h : 62 ≤ Λ) : (Noun.atom k).leaves ≤ Λ := by
  simp [atom_leaves]; exact one_le_of_62 h

theorem addArm_le_of_62 {Λ : ℕ} (h : 62 ≤ Λ) : addArm.leaves ≤ Λ :=
  le_trans (le_of_eq addArm_leaves) (twentythree_le_of_62 h)

theorem macArm_le_of_62 {Λ : ℕ} (h : 62 ≤ Λ) : macArm.leaves ≤ Λ :=
  le_trans (le_of_eq macArm_leaves) (le_trans (by decide : 35 ≤ 62) h)

theorem mmBattery_le_of_62 {Λ : ℕ} (h : 62 ≤ Λ) : mmBattery.leaves ≤ Λ :=
  le_trans (le_of_eq mmBattery_leaves) (le_trans (by decide : 58 ≤ 62) h)

theorem invokeAxis_le_of_62 (axis : ℕ) {Λ : ℕ} (h : 62 ≤ Λ) :
    (invokeAxis axis).leaves ≤ Λ :=
  le_trans (le_of_eq (invokeAxis_leaves axis))
    (le_trans (by decide : 4 ≤ 62) h)

theorem quote_mmBattery_le_of_62 {Λ : ℕ} (h : 62 ≤ Λ) :
    (quote mmBattery).leaves ≤ Λ := by
  rw [quote_leaves, mmBattery_leaves]
  exact le_trans (by decide : 59 ≤ 62) h

theorem slam_op0_addNewSample_le {Λ : ℕ} (h : 62 ≤ Λ) :
    (slam (op0 2) addNewSample 2).leaves ≤ Λ := by
  rw [slam_leaves, op0_leaves, addNewSample_leaves]
  exact le_trans (by decide : 15 ≤ 62) h

theorem addFromMac_le_of_62 {Λ : ℕ} (h : 62 ≤ Λ) : addFromMac.leaves ≤ Λ :=
  le_trans (le_of_eq addFromMac_leaves) (le_trans (by decide : 13 ≤ 62) h)

theorem macNewSample_le_of_62 {Λ : ℕ} (h : 62 ≤ Λ) : macNewSample.leaves ≤ Λ :=
  le_trans (le_of_eq macNewSample_leaves) (le_trans (by decide : 20 ≤ 62) h)

theorem slam_op0_macNewSample_le {Λ : ℕ} (h : 62 ≤ Λ) :
    (slam (op0 2) macNewSample 4).leaves ≤ Λ := by
  rw [slam_leaves, op0_leaves, macNewSample_leaves]
  exact le_trans (by decide : 27 ≤ 62) h

theorem sample3_le (a b c : ℕ) {Λ : ℕ} (h : 62 ≤ Λ) :
    (Noun.cell (.atom a) (Noun.cell (.atom b) (.atom c))).leaves ≤ Λ := by
  simp [cell_leaves, atom_leaves]; exact le_trans (by decide : 3 ≤ 62) h

theorem sample4_le (a b c d : ℕ) {Λ : ℕ} (h : 62 ≤ Λ) :
    (Noun.cell (.atom a) (Noun.cell (.atom b) (Noun.cell (.atom c) (.atom d)))).leaves ≤ Λ := by
  simp [cell_leaves, atom_leaves]; exact le_trans (by decide : 4 ≤ 62) h

theorem addCore_cell_le (acc i m : ℕ) {Λ : ℕ} (h : 62 ≤ Λ) :
    (Noun.cell addArm (Noun.cell (.atom acc) (Noun.cell (.atom i) (.atom m)))).leaves ≤ Λ := by
  simp [cell_leaves, atom_leaves, addArm_leaves]
  exact le_trans (by decide : 26 ≤ 62) h

theorem macCore_cell_le (acc i n m : ℕ) {Λ : ℕ} (h : 62 ≤ Λ) :
    (Noun.cell mmBattery
      (Noun.cell (.atom acc) (Noun.cell (.atom i) (Noun.cell (.atom n) (.atom m))))).leaves ≤ Λ := by
  simp [cell_leaves, atom_leaves, mmBattery_leaves]
  exact le_trans (by decide : 62 ≤ 62) h

theorem pair_op0_addNewSample_le {Λ : ℕ} (h : 62 ≤ Λ) :
    (Noun.cell (op0 2) addNewSample).leaves ≤ Λ := by
  simp [cell_leaves, op0_leaves, addNewSample_leaves]
  exact le_trans (by decide : 10 ≤ 62) h

theorem pair_op0_5_sampleF_le {Λ : ℕ} (h : 62 ≤ Λ) :
    (Noun.cell (op0 5)
      (Noun.cell (op0 6) (Noun.cell (op1 0) (op0 31)))).leaves ≤ Λ := by
  simp [cell_leaves, op0_leaves, op1_leaves]
  exact le_trans (by decide : 8 ≤ 62) h

theorem pair_op0_2_macNewSample_le {Λ : ℕ} (h : 62 ≤ Λ) :
    (Noun.cell (op0 2) macNewSample).leaves ≤ Λ := by
  simp [cell_leaves, op0_leaves, macNewSample_leaves]
  exact le_trans (by decide : 22 ≤ 62) h

theorem op5_op0_le (a b : ℕ) {Λ : ℕ} (h : 62 ≤ Λ) :
    (op5 (op0 a) (op0 b)).leaves ≤ Λ := by
  simp [op5, op0, cell_leaves, atom_leaves]
  exact le_trans (by decide : 5 ≤ 62) h

/-! ## Remaining arm combinators -/

theorem confined_addNewSample {Λ n acc i m : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 5)
      (addCore (.atom acc) (.atom i) (.atom m)) addNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom (i + 1)) (.atom m))))
    (hΛ : 62 ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_62 hΛ
  have hs := addCore_atoms_le acc i m hΛ
  have h6 := gen_op0 (K := K) (n + 2)
    (addCore_slot6 (.atom acc) (.atom i) (.atom m))
  have h14 := gen_op0 (K := K) (n + 1)
    (addCore_slot14 (.atom acc) (.atom i) (.atom m))
  have h15 := gen_op0 (K := K) (n + 2)
    (addCore_slot15 (.atom acc) (.atom i) (.atom m))
  have hincA := gen_op4 (K := K) (n + 3) h6 (lus_nat acc)
  have hincI := gen_op4 (K := K) (n + 2) h14 (lus_nat i)
  have hinner := gen_cons (K := K) (n + 3) hincI h15
  have houter := gen_cons (K := K) (n + 4) hincA hinner
  have huniq := gen_ok_unique h houter
  rw [huniq.1]
  refine confined_gen_cons (Λ := Λ) hincA hinner houter ?_ ?_ hs ?_ ?_
  · exact confined_gen_op4 (Λ := Λ) h6 (lus_nat acc) hincA
      (confined_gen_op0 (Λ := Λ) (addCore_slot6 (.atom acc) (.atom i) (.atom m)) h6 hs h2)
      hs (by simp [op4, op0, cell_leaves, atom_leaves]; exact le_trans (by decide : 3 ≤ 62) hΛ)
      (atom_le_of_62 (acc + 1) hΛ)
  · refine confined_gen_cons (Λ := Λ) hincI h15 hinner ?_ ?_ hs ?_ ?_
    · exact confined_gen_op4 (Λ := Λ) h14 (lus_nat i) hincI
        (confined_gen_op0 (Λ := Λ) (addCore_slot14 (.atom acc) (.atom i) (.atom m)) h14 hs h2)
        hs (by simp [op4, op0, cell_leaves, atom_leaves]; exact le_trans (by decide : 3 ≤ 62) hΛ)
        (atom_le_of_62 (i + 1) hΛ)
    · exact confined_gen_op0 (Λ := Λ) (addCore_slot15 (.atom acc) (.atom i) (.atom m)) h15 hs h2
    · simp [cell_leaves, op4, op0, atom_leaves]; exact le_trans (by decide : 5 ≤ 62) hΛ
    · simp [cell_leaves, atom_leaves]; exact two_le_of_62 hΛ
  · exact le_trans (le_of_eq addNewSample_leaves) (le_trans (by decide : 8 ≤ 62) hΛ)
  · exact sample3_le (acc + 1) (i + 1) m hΛ

theorem confined_addArm_one {Λ n acc : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      .ok (t, .atom (acc + 1)))
    (hΛ : 62 ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_62 hΛ
  have h1 := one_le_of_62 hΛ
  have hs := addCore_atoms_le acc 0 1 hΛ
  have hf := addArm_le_of_62 hΛ
  have h14 := gen_op0 (K := K) (n + 13)
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1))
  have h15 := gen_op0 (K := K) (n + 13)
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 14) h14 h15
  have ihcond := confined_gen_op5 (Λ := Λ) h14 h15 hcond
    (confined_gen_op0 (Λ := Λ) (addCore_slot14 (.atom acc) (.atom 0) (.atom 1)) h14 hs h2)
    (confined_gen_op0 (Λ := Λ) (addCore_slot15 (.atom acc) (.atom 0) (.atom 1)) h15 hs h2)
    hs (op5_op0_le 14 15 hΛ) h1
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_addNewSample (K := K) (n + 8) acc 0 1
  have ihns := confined_addNewSample (Λ := Λ) hns hΛ
  have hbatt := gen_op0 (K := K) (n + 12)
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
  obtain ⟨doneTree, hdone⟩ :=
    gen_addArm_done (K := K) (n + 7) (.atom (acc + 1)) (.atom 1)
  have ihdone := confined_addArm_done (Λ := Λ) (.atom (acc + 1)) (.atom 1) hdone
    (addCore_atoms_le (acc + 1) 1 1 hΛ) (twentythree_le_of_62 hΛ)
    (atom_le_of_62 (acc + 1) hΛ)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 10) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone
  have ihslam := confined_gen_slam (Λ := Λ) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone hslam
    (confined_gen_op0 (Λ := Λ) (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hbatt hs h2)
    ihns ihdone hs (slam_op0_addNewSample_le hΛ) (atom_le_of_62 (acc + 1) hΛ)
    (addCore_cell_le (acc + 1) 1 1 hΛ) (addArm_le_of_62 hΛ)
    (invokeAxis_le_of_62 2 hΛ) (pair_op0_addNewSample_le hΛ)
  have hop6 := gen_op6_one (K := K) (n + 15) (c := op0 6) hcond hslam
  have huniq := gen_ok_unique h (by simpa [addArm, slam, op0] using hop6)
  rw [huniq.1]
  exact confined_gen_op6_one (Λ := Λ) hcond hslam hop6
    (by convert ihcond; simp [htis]) ihslam hs (by simpa [addArm, slam, op0] using hf)
    (atom_le_of_62 (acc + 1) hΛ)

theorem confined_macArm_done {Λ n : ℕ} (acc k m : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (macCoreAt acc k k m) macArm =
      .ok (t, acc))
    (hs : (macCoreAt acc k k m).leaves ≤ Λ) (hΛ : 62 ≤ Λ)
    (he : acc.leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_62 hΛ
  have h1 := one_le_of_62 hΛ
  have hf := macArm_le_of_62 hΛ
  have h14 := gen_op0 (K := K) (n + 3) (macCoreAt_slot14 acc k k m)
  have h30 := gen_op0 (K := K) (n + 3) (macCoreAt_slot30 acc k k m)
  have h5eq := gen_op5 (K := K) (n + 4) h14 h30
  have ih5 := confined_gen_op5 (Λ := Λ) h14 h30 h5eq
    (confined_gen_op0 (Λ := Λ) (macCoreAt_slot14 acc k k m) h14 hs h2)
    (confined_gen_op0 (Λ := Λ) (macCoreAt_slot30 acc k k m) h30 hs h2)
    hs (op5_op0_le 14 30 hΛ) h1
  rw [tis_self k] at h5eq
  have hthen := gen_op0 (K := K) (n + 4) (macCoreAt_slot6 acc k k m)
  have hop6 := gen_op6_zero (K := K) (n + 5)
    (d := slam (op0 2) macNewSample 4) h5eq hthen
  have huniq := gen_ok_unique h (by simpa [macArm] using hop6)
  rw [huniq.1]
  exact confined_gen_op6_zero (Λ := Λ) h5eq hthen hop6
    (by convert ih5; simp [tis_self])
    (confined_gen_op0 (Λ := Λ) (macCoreAt_slot6 acc k k m) hthen hs h2)
    hs (by simpa [macArm] using hf) he

theorem confined_macArm_zero {Λ n : ℕ} (acc m : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (macCore acc (.atom 0) m) macArm =
      .ok (t, acc))
    (hs : (macCore acc (.atom 0) m).leaves ≤ Λ) (hΛ : 62 ≤ Λ)
    (he : acc.leaves ≤ Λ) :
    TraceConfined Λ t :=
  confined_macArm_done (Λ := Λ) acc (.atom 0) m (by simpa [macCore] using h)
    (by simpa [macCore] using hs) hΛ he

theorem confined_gen_macSampleF {Λ n : ℕ}
    {s aH aT nH nT mF acc k m : Noun}
    {aTree nTree mTree t : NTree (GenComputeRow K)} {res : Noun}
    (ha : genComputeSkeleton (K := K) (n + 2) s (Noun.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n s (Noun.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n s mF = .ok (mTree, m))
    (h : genComputeSkeleton (K := K) (n + 3) s
      (Noun.cell (Noun.cell aH aT) (Noun.cell (op1 0) (Noun.cell (Noun.cell nH nT) mF))) =
      .ok (t, res))
    (iha : TraceConfined Λ aTree) (ihn : TraceConfined Λ nTree)
    (ihm : TraceConfined Λ mTree)
    (hs : s.leaves ≤ Λ) (hΛ : 62 ≤ Λ)
    (hf : (Noun.cell (Noun.cell aH aT)
      (Noun.cell (op1 0) (Noun.cell (Noun.cell nH nT) mF))).leaves ≤ Λ)
    (he : (Noun.cell acc (Noun.cell (.atom 0) (Noun.cell k m))).leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_62 hΛ
  have hnm := gen_cons (K := K) n hn hm
  have hz := gen_op1 (K := K) n s 0
  have hinner := gen_cons (K := K) (n + 1) hz hnm
  have houter := gen_cons (K := K) (n + 2) ha hinner
  have huniq := gen_ok_unique h houter
  rw [huniq.1]
  have haccF : (Noun.cell aH aT).leaves ≤ Λ :=
    le_trans (leaves_le_cell_left _ _) hf
  have hinnerF : (Noun.cell (op1 0) (Noun.cell (Noun.cell nH nT) mF)).leaves ≤ Λ :=
    le_trans (leaves_le_cell_right _ _) hf
  have hnmF : (Noun.cell (Noun.cell nH nT) mF).leaves ≤ Λ :=
    le_trans (leaves_le_cell_right _ _) hinnerF
  have hnF : (Noun.cell nH nT).leaves ≤ Λ :=
    le_trans (leaves_le_cell_left _ _) hnmF
  have hmF : mF.leaves ≤ Λ :=
    le_trans (leaves_le_cell_right _ _) hnmF
  have hinnerE : (Noun.cell (.atom 0) (Noun.cell k m)).leaves ≤ Λ :=
    le_trans (leaves_le_cell_right _ _) he
  have hnmE : (Noun.cell k m).leaves ≤ Λ :=
    le_trans (leaves_le_cell_right _ _) hinnerE
  refine confined_gen_cons (Λ := Λ) ha hinner houter iha ?_ hs hf he
  refine confined_gen_cons (Λ := Λ) hz hnm hinner
    (confined_gen_op1 (Λ := Λ) hz hs h2) ?_ hs hinnerF hinnerE
  exact confined_gen_cons (Λ := Λ) hn hm hnm ihn ihm hs hnmF hnmE

theorem confined_addFromMac_m0 {Λ n acc : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 12)
      (macCore (.atom acc) (.atom 1) (.atom 0)) addFromMac = .ok (t, .atom acc))
    (hΛ : 62 ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_62 hΛ
  have hs := macCore_atoms_le acc 1 0 hΛ
  have h5 := gen_op0 (K := K) (n + 9)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hacc := gen_op0 (K := K) (n + 8)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hz := gen_op1 (K := K) (n + 7)
    (macCore (.atom acc) (.atom 1) (.atom 0)) 0
  have hm := gen_op0 (K := K) (n + 7)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinner := gen_cons (K := K) (n + 8) hz hm
  have hsmpl := gen_cons (K := K) (n + 9) hacc hinner
  obtain ⟨doneTree, hdone⟩ := gen_addArm_done (K := K) (n + 4) (.atom acc) (.atom 0)
  have ihdone := confined_addArm_done (Λ := Λ) (.atom acc) (.atom 0) hdone
    (addCore_atoms_le acc 0 0 hΛ) (twentythree_le_of_62 hΛ) (atom_le_of_62 acc hΛ)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 7) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone
  have huniq := gen_ok_unique h (by simpa [addFromMac, slam, op0, op1, macCore] using hslam)
  rw [huniq.1]
  have ihsamp :=
    confined_gen_cons (K := K) (Λ := Λ) hacc hinner hsmpl
      (confined_gen_op0 (Λ := Λ) (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
        hacc hs h2)
      (confined_gen_cons (K := K) (Λ := Λ) hz hm hinner
        (confined_gen_op1 (Λ := Λ) hz hs h2)
        (confined_gen_op0 (Λ := Λ) (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
          hm hs h2) hs
        (by simp [cell_leaves, op1_leaves, op0_leaves]; exact le_trans (by decide : 4 ≤ 62) hΛ)
        (by simp [cell_leaves, atom_leaves]; exact two_le_of_62 hΛ))
      hs
      (by simp [cell_leaves, op0_leaves, op1_leaves]; exact le_trans (by decide : 6 ≤ 62) hΛ)
      (sample3_le acc 0 0 hΛ)
  exact confined_gen_slam (Λ := Λ) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone hslam
    (confined_gen_op0 (Λ := Λ) (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h5 hs h2)
    ihsamp ihdone hs (addFromMac_le_of_62 hΛ) (atom_le_of_62 acc hΛ)
    (addCore_cell_le acc 0 0 hΛ) (addArm_le_of_62 hΛ)
    (invokeAxis_le_of_62 2 hΛ) (pair_op0_5_sampleF_le hΛ)

theorem confined_addFromMac_m1 {Λ n acc : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 21)
      (macCore (.atom acc) (.atom 1) (.atom 1)) addFromMac =
      .ok (t, .atom (acc + 1)))
    (hΛ : 62 ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_62 hΛ
  have hs := macCore_atoms_le acc 1 1 hΛ
  have h5 := gen_op0 (K := K) (n + 18)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have haccS := gen_op0 (K := K) (n + 17)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hz := gen_op1 (K := K) (n + 16)
    (macCore (.atom acc) (.atom 1) (.atom 1)) 0
  have hm := gen_op0 (K := K) (n + 16)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinner := gen_cons (K := K) (n + 17) hz hm
  have hsmpl := gen_cons (K := K) (n + 18) haccS hinner
  obtain ⟨doneTree, hdone⟩ := gen_addArm_one (K := K) (n + 3) acc
  have ihdone := confined_addArm_one (Λ := Λ) hdone hΛ
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone
  have huniq := gen_ok_unique h (by simpa [addFromMac, slam, op0, op1, macCore] using hslam)
  rw [huniq.1]
  have ihsamp :=
    confined_gen_cons (K := K) (Λ := Λ) haccS hinner hsmpl
      (confined_gen_op0 (Λ := Λ) (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
        haccS hs h2)
      (confined_gen_cons (K := K) (Λ := Λ) hz hm hinner
        (confined_gen_op1 (Λ := Λ) hz hs h2)
        (confined_gen_op0 (Λ := Λ) (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
          hm hs h2) hs
        (by simp [cell_leaves, op1_leaves, op0_leaves]; exact le_trans (by decide : 4 ≤ 62) hΛ)
        (by simp [cell_leaves, atom_leaves]; exact two_le_of_62 hΛ))
      hs
      (by simp [cell_leaves, op0_leaves, op1_leaves]; exact le_trans (by decide : 6 ≤ 62) hΛ)
      (sample3_le acc 0 1 hΛ)
  exact confined_gen_slam (Λ := Λ) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone hslam
    (confined_gen_op0 (Λ := Λ) (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h5 hs h2)
    ihsamp ihdone hs (addFromMac_le_of_62 hΛ) (atom_le_of_62 (acc + 1) hΛ)
    (addCore_cell_le acc 0 1 hΛ) (addArm_le_of_62 hΛ)
    (invokeAxis_le_of_62 2 hΛ) (pair_op0_5_sampleF_le hΛ)

theorem confined_macNewSample_m0 {Λ n acc : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 14)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample =
      .ok (t, .cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0)))))
    (hΛ : 62 ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_62 hΛ
  have hs := macCore_atoms_le acc 1 0 hΛ
  obtain ⟨addT, hadd⟩ := gen_addFromMac_m0 (K := K) (n + 1) acc
  have ihadd := confined_addFromMac_m0 (Λ := Λ) hadd hΛ
  have h14 := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinc := gen_op4 (K := K) (n + 11) h14 (lus_nat 0)
  have hn := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hm := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hnm := gen_cons (K := K) (n + 11) hn hm
  have hrest := gen_cons (K := K) (n + 12) hinc hnm
  have hadd' :
      genComputeSkeleton (K := K) (n + 13)
        (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0))
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2))) = .ok (addT, .atom acc) := by
    simpa [addFromMac, slam, op7, op0, op1, invokeAxis, macCore] using hadd
  have hcell := gen_cons (K := K) (n + 13) hadd' hrest
  have ihrest :=
    confined_gen_cons (K := K) (Λ := Λ) hinc hnm hrest
      (confined_gen_op4 (Λ := Λ) h14 (lus_nat 0) hinc
        (confined_gen_op0 (Λ := Λ)
          (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14 hs h2)
        hs (by simp [op4, op0, cell_leaves, atom_leaves]; exact le_trans (by decide : 3 ≤ 62) hΛ)
        (atom_le_of_62 1 hΛ))
      (confined_gen_cons (K := K) (Λ := Λ) hn hm hnm
        (confined_gen_op0 (Λ := Λ)
          (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hn hs h2)
        (confined_gen_op0 (Λ := Λ)
          (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hm hs h2)
        hs (by simp [cell_leaves, op0_leaves]; exact le_trans (by decide : 4 ≤ 62) hΛ)
        (by simp [cell_leaves, atom_leaves]; exact two_le_of_62 hΛ))
      hs (by simp [cell_leaves, op4, op0, atom_leaves]; exact le_trans (by decide : 7 ≤ 62) hΛ)
      (sample3_le 1 1 0 hΛ)
  have ihcell := confined_gen_cons (K := K) (Λ := Λ) hadd' hrest hcell ihadd ihrest hs
    (macNewSample_le_of_62 hΛ) (sample4_le acc 1 1 0 hΛ)
  have hnamed :=
    show genComputeSkeleton (K := K) (n + 14)
        (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample = _ from by
      simpa [macNewSample, addFromMac, slam, op7, op4, op0, op1, invokeAxis,
        macCore] using hcell
  have huniq := gen_ok_unique h hnamed
  rw [huniq.1]
  exact ihcell

theorem confined_macNewSample_m1 {Λ n acc : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 23)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1)))))
    (hΛ : 62 ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_62 hΛ
  have hs := macCore_atoms_le acc 1 1 hΛ
  obtain ⟨addT, hadd⟩ := gen_addFromMac_m1 (K := K) (n + 1) acc
  have ihadd := confined_addFromMac_m1 (Λ := Λ) hadd hΛ
  have h14 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinc := gen_op4 (K := K) (n + 20) h14 (lus_nat 0)
  have hn := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hm := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hnm := gen_cons (K := K) (n + 20) hn hm
  have hrest := gen_cons (K := K) (n + 21) hinc hnm
  have hadd' :
      genComputeSkeleton (K := K) (n + 22)
        (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1))
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2))) = .ok (addT, .atom (acc + 1)) := by
    simpa [addFromMac, slam, op7, op0, op1, invokeAxis, macCore] using hadd
  have hcell := gen_cons (K := K) (n + 22) hadd' hrest
  have ihrest :=
    confined_gen_cons (K := K) (Λ := Λ) hinc hnm hrest
      (confined_gen_op4 (Λ := Λ) h14 (lus_nat 0) hinc
        (confined_gen_op0 (Λ := Λ)
          (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14 hs h2)
        hs (by simp [op4, op0, cell_leaves, atom_leaves]; exact le_trans (by decide : 3 ≤ 62) hΛ)
        (atom_le_of_62 1 hΛ))
      (confined_gen_cons (K := K) (Λ := Λ) hn hm hnm
        (confined_gen_op0 (Λ := Λ)
          (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hn hs h2)
        (confined_gen_op0 (Λ := Λ)
          (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hm hs h2)
        hs (by simp [cell_leaves, op0_leaves]; exact le_trans (by decide : 4 ≤ 62) hΛ)
        (by simp [cell_leaves, atom_leaves]; exact two_le_of_62 hΛ))
      hs (by simp [cell_leaves, op4, op0, atom_leaves]; exact le_trans (by decide : 7 ≤ 62) hΛ)
      (sample3_le 1 1 1 hΛ)
  have ihcell := confined_gen_cons (K := K) (Λ := Λ) hadd' hrest hcell ihadd ihrest hs
    (macNewSample_le_of_62 hΛ) (sample4_le (acc + 1) 1 1 1 hΛ)
  have hnamed :=
    show genComputeSkeleton (K := K) (n + 23)
        (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample = _ from by
      simpa [macNewSample, addFromMac, slam, op7, op4, op0, op1, invokeAxis,
        macCore] using hcell
  have huniq := gen_ok_unique h hnamed
  rw [huniq.1]
  exact ihcell

theorem confined_macArm_one_m0 {Λ n acc : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = .ok (t, .atom acc))
    (hΛ : 62 ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_62 hΛ
  have h1 := one_le_of_62 hΛ
  have hs := macCore_atoms_le acc 1 0 hΛ
  have hf := macArm_le_of_62 hΛ
  have h14 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have h30 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hcond := gen_op5 (K := K) (n + 20) h14 h30
  have ihcond := confined_gen_op5 (Λ := Λ) h14 h30 hcond
    (confined_gen_op0 (Λ := Λ)
      (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14 hs h2)
    (confined_gen_op0 (Λ := Λ)
      (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h30 hs h2)
    hs (op5_op0_le 14 30 hΛ) h1
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_macNewSample_m0 (K := K) (n + 5) acc
  have ihns := confined_macNewSample_m0 (Λ := Λ) hns hΛ
  have hbatt := gen_op0 (K := K) (n + 18)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  obtain ⟨doneTree, hdone⟩ :=
    gen_macArm_done (K := K) (n + 13) (.atom acc) (.atom 1) (.atom 0)
  have ihdone := confined_macArm_done (Λ := Λ) (.atom acc) (.atom 1) (.atom 0) hdone
    (macCoreAt_atoms_le acc 1 1 0 hΛ) hΛ (atom_le_of_62 acc hΛ)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16)
    (axis := 4) (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone
  have ihslam := confined_gen_slam (Λ := Λ) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone hslam
    (confined_gen_op0 (Λ := Λ)
      (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hbatt hs h2)
    ihns ihdone hs (slam_op0_macNewSample_le hΛ) (atom_le_of_62 acc hΛ)
    (macCore_cell_le acc 1 1 0 hΛ) (macArm_le_of_62 hΛ)
    (invokeAxis_le_of_62 4 hΛ) (pair_op0_2_macNewSample_le hΛ)
  have hop6 := gen_op6_one (K := K) (n + 21) (c := op0 6) hcond hslam
  have huniq := gen_ok_unique h
    (by simpa [macArm, slam, op0, macNewSample, macCore] using hop6)
  rw [huniq.1]
  exact confined_gen_op6_one (Λ := Λ) hcond hslam hop6
    (by convert ihcond; simp [htis]) ihslam hs (by simpa [macArm, slam, op0] using hf)
    (atom_le_of_62 acc hΛ)

theorem confined_macArm_one_m1 {Λ n acc : ℕ}
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      .ok (t, .atom (acc + 1)))
    (hΛ : 62 ≤ Λ) :
    TraceConfined Λ t := by
  have h2 := two_le_of_62 hΛ
  have h1 := one_le_of_62 hΛ
  have hs := macCore_atoms_le acc 1 1 hΛ
  have hf := macArm_le_of_62 hΛ
  have h14 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have h30 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 29) h14 h30
  have ihcond := confined_gen_op5 (Λ := Λ) h14 h30 hcond
    (confined_gen_op0 (Λ := Λ)
      (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14 hs h2)
    (confined_gen_op0 (Λ := Λ)
      (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h30 hs h2)
    hs (op5_op0_le 14 30 hΛ) h1
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_macNewSample_m1 (K := K) (n + 5) acc
  have ihns := confined_macNewSample_m1 (Λ := Λ) hns hΛ
  have hbatt := gen_op0 (K := K) (n + 27)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  obtain ⟨doneTree, hdone⟩ :=
    gen_macArm_done (K := K) (n + 22) (.atom (acc + 1)) (.atom 1) (.atom 1)
  have ihdone := confined_macArm_done (Λ := Λ) (.atom (acc + 1)) (.atom 1) (.atom 1) hdone
    (macCoreAt_atoms_le (acc + 1) 1 1 1 hΛ) hΛ
    (atom_le_of_62 (acc + 1) hΛ)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 25)
    (axis := 4) (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone
  have ihslam := confined_gen_slam (Λ := Λ) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone hslam
    (confined_gen_op0 (Λ := Λ)
      (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hbatt hs h2)
    ihns ihdone hs (slam_op0_macNewSample_le hΛ) (atom_le_of_62 (acc + 1) hΛ)
    (macCore_cell_le (acc + 1) 1 1 1 hΛ) (macArm_le_of_62 hΛ)
    (invokeAxis_le_of_62 4 hΛ) (pair_op0_2_macNewSample_le hΛ)
  have hop6 := gen_op6_one (K := K) (n + 30) (c := op0 6) hcond hslam
  have huniq := gen_ok_unique h
    (by simpa [macArm, slam, op0, macNewSample, macCore] using hop6)
  rw [huniq.1]
  exact confined_gen_op6_one (Λ := Λ) hcond hslam hop6
    (by convert ihcond; simp [htis]) ihslam hs (by simpa [macArm, slam, op0] using hf)
    (atom_le_of_62 (acc + 1) hΛ)

/-- `invokeMac` formula is a subnoun of `mmCij` (`142`) or `mmFormula` (`568`). -/
theorem confined_gen_invokeMac {Λ n : ℕ}
    {s aH aT nH nT mF acc k m result : Noun}
    {aTree nTree mTree armTree t : NTree (GenComputeRow K)} {res : Noun}
    (ha : genComputeSkeleton (K := K) (n + 2) s (Noun.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n s (Noun.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n s mF = .ok (mTree, m))
    (harm : genComputeSkeleton (K := K) (n + 3) (macCore acc k m) macArm =
      .ok (armTree, result))
    (h : genComputeSkeleton (K := K) (n + 5) s
      (invokeMac (Noun.cell aH aT) (Noun.cell nH nT) mF) = .ok (t, res))
    (iha : TraceConfined Λ aTree) (ihn : TraceConfined Λ nTree)
    (ihm : TraceConfined Λ mTree) (ihaArm : TraceConfined Λ armTree)
    (hs : s.leaves ≤ Λ) (hΛ : 62 ≤ Λ)
    (hf : (invokeMac (Noun.cell aH aT) (Noun.cell nH nT) mF).leaves ≤ Λ)
    (he : result.leaves ≤ Λ)
    (hcore : (macCore acc k m).leaves ≤ Λ) :
    TraceConfined Λ t := by
  have hqB := gen_quote (K := K) (n + 2) s mmBattery
  obtain ⟨sfTree, hsf⟩ := gen_macSampleF (K := K) n ha hn hm
  have hpair_le_inv :
      (Noun.cell (quote mmBattery)
        (Noun.cell (Noun.cell aH aT)
          (Noun.cell (op1 0) (Noun.cell (Noun.cell nH nT) mF)))).leaves ≤
        (invokeMac (Noun.cell aH aT) (Noun.cell nH nT) mF).leaves := by
    simp [invokeMac, slam, op7, quote, cell_leaves, atom_leaves]; omega
  have hsfF :
      (Noun.cell (Noun.cell aH aT)
        (Noun.cell (op1 0) (Noun.cell (Noun.cell nH nT) mF))).leaves ≤ Λ :=
    le_trans (leaves_le_cell_right _ _) (le_trans hpair_le_inv hf)
  have hsfE : (Noun.cell acc (Noun.cell (.atom 0) (Noun.cell k m))).leaves ≤ Λ :=
    le_trans (leaves_le_cell_right _ _) (by simpa [macCore, macCoreAt] using hcore)
  have ihsf := confined_gen_macSampleF (Λ := Λ) ha hn hm hsf iha ihn ihm hs hΛ hsfF hsfE
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) n (axis := 4)
    (bHead := .atom 1) (bTail := mmBattery) hqB hsf
    (macCoreAt_slot4 acc (.atom 0) k m) harm
  have huniq := gen_ok_unique h
    (by simpa [invokeMac, slam, quote, macCore, macCoreAt] using hslam)
  rw [huniq.1]
  have hpair := le_trans hpair_le_inv hf
  exact confined_gen_slam (Λ := Λ) hqB hsf
    (macCoreAt_slot4 acc (.atom 0) k m) harm hslam
    (confined_gen_quote (Λ := Λ) hqB hs (quote_mmBattery_le_of_62 hΛ)
      (mmBattery_le_of_62 hΛ))
    ihsf ihaArm hs (by simpa [invokeMac, slam, quote] using hf) he
    (by simpa [macCore, macCoreAt] using hcore)
    (macArm_le_of_62 hΛ) (invokeAxis_le_of_62 4 hΛ) hpair

theorem sixtyTwo_le_of_568 {Λ : ℕ} (h : 568 ≤ Λ) : 62 ≤ Λ :=
  le_trans (by decide : 62 ≤ 568) h

theorem mmSubject_le_of_568 {Λ : ℕ} (h : 568 ≤ Λ) : mmSubject.leaves ≤ Λ :=
  le_trans (le_of_eq mmSubject_leaves_eq) (le_trans (by decide : 8 ≤ 568) h)

theorem mmCij_le_of_568 {Λ : ℕ} (h : 568 ≤ Λ)
    {cij : Noun} (hc : cij.leaves = 142) : cij.leaves ≤ Λ :=
  le_trans (le_of_eq hc) (le_trans (by decide : 142 ≤ 568) h)

theorem invokeMac_inner_le {Λ : ℕ} (h : 568 ≤ Λ) (nAx mAx : ℕ) :
    (invokeMac (op1 0) (op0 nAx) (op0 mAx)).leaves ≤ Λ := by
  rw [invokeMac_leaves, op1_leaves, op0_leaves, op0_leaves]
  exact le_trans (by decide : 72 ≤ 568) h

theorem confined_mmC00 {Λ n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC00 = .ok (t, .atom 2))
    (hΛ : 568 ≤ Λ) :
    TraceConfined Λ t := by
  have h62 := sixtyTwo_le_of_568 hΛ
  have h2 := two_le_of_62 h62
  have hs := mmSubject_le_of_568 hΛ
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA⟩ := gen_macArm_one_m1 (K := K) (n + 20) 0
  have ihInnerArm := confined_macArm_one_m1 (Λ := Λ) innerA h62
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 12) ha0 a00 b00 innerA
  have ihInner := confined_gen_invokeMac (Λ := Λ) ha0 a00 b00 innerA hinner
    (confined_gen_op1 (Λ := Λ) ha0 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot8 a00 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot12 b00 hs h2)
    ihInnerArm hs h62 (by simpa [op1, op0] using invokeMac_inner_le hΛ 8 12)
    (atom_le_of_62 1 h62) (macCore_atoms_le 0 1 1 h62)
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 1
  have ihOuterArm := confined_macArm_one_m1 (Λ := Λ) outerA h62
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 14)
    hinner' a01 b10 outerA
  have hh := h
  simp only [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact confined_gen_invokeMac (Λ := Λ) hinner' a01 b10 outerA houter
    ihInner
    (confined_gen_op0 (Λ := Λ) mmSubject_slot9 a01 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot14 b10 hs h2)
    ihOuterArm hs h62 (by simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0]
      using mmCij_le_of_568 hΛ mmC00_leaves)
    (atom_le_of_62 2 h62) (macCore_atoms_le 1 1 1 h62)

theorem confined_mmC01 {Λ n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC01 = .ok (t, .atom 1))
    (hΛ : 568 ≤ Λ) :
    TraceConfined Λ t := by
  have h62 := sixtyTwo_le_of_568 hΛ
  have h2 := two_le_of_62 h62
  have hs := mmSubject_le_of_568 hΛ
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA⟩ := gen_macArm_one_m0 (K := K) (n + 29) 0
  have ihInnerArm := confined_macArm_one_m0 (Λ := Λ) innerA h62
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 13) ha0 a00 b01 innerA
  have ihInner := confined_gen_invokeMac (Λ := Λ) ha0 a00 b01 innerA hinner
    (confined_gen_op1 (Λ := Λ) ha0 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot8 a00 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot13 b01 hs h2)
    ihInnerArm hs h62 (by simpa [op1, op0] using invokeMac_inner_le hΛ 8 13)
    (atom_le_of_62 0 h62) (macCore_atoms_le 0 1 0 h62)
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := confined_macArm_one_m1 (Λ := Λ) outerA h62
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 15)
    hinner' a01 b11 outerA
  have hh := h
  simp only [mmC01, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact confined_gen_invokeMac (Λ := Λ) hinner' a01 b11 outerA houter
    ihInner
    (confined_gen_op0 (Λ := Λ) mmSubject_slot9 a01 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot15 b11 hs h2)
    ihOuterArm hs h62 (by simpa [mmC01, mac2, invokeMac, slam, op7, quote, op1, op0]
      using mmCij_le_of_568 hΛ mmC01_leaves)
    (atom_le_of_62 1 h62) (macCore_atoms_le 0 1 1 h62)

theorem confined_mmC10 {Λ n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC10 = .ok (t, .atom 1))
    (hΛ : 568 ≤ Λ) :
    TraceConfined Λ t := by
  have h62 := sixtyTwo_le_of_568 hΛ
  have h2 := two_le_of_62 h62
  have hs := mmSubject_le_of_568 hΛ
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA⟩ := gen_macArm_zero (K := K) (n + 45) (.atom 0) (.atom 1)
  have ihInnerArm := confined_macArm_zero (Λ := Λ) (.atom 0) (.atom 1) innerA
    (macCore_atoms_le 0 0 1 h62) h62 (atom_le_of_62 0 h62)
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 12) ha0 a10 b00 innerA
  have ihInner := confined_gen_invokeMac (Λ := Λ) ha0 a10 b00 innerA hinner
    (confined_gen_op1 (Λ := Λ) ha0 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot10 a10 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot12 b00 hs h2)
    ihInnerArm hs h62 (by simpa [op1, op0] using invokeMac_inner_le hΛ 10 12)
    (atom_le_of_62 0 h62) (macCore_atoms_le 0 0 1 h62)
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := confined_macArm_one_m1 (Λ := Λ) outerA h62
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 14)
    hinner' a11 b10 outerA
  have hh := h
  simp only [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact confined_gen_invokeMac (Λ := Λ) hinner' a11 b10 outerA houter
    ihInner
    (confined_gen_op0 (Λ := Λ) mmSubject_slot11 a11 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot14 b10 hs h2)
    ihOuterArm hs h62 (by simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0]
      using mmCij_le_of_568 hΛ mmC10_leaves)
    (atom_le_of_62 1 h62) (macCore_atoms_le 0 1 1 h62)

theorem confined_mmC11 {Λ n : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC11 = .ok (t, .atom 1))
    (hΛ : 568 ≤ Λ) :
    TraceConfined Λ t := by
  have h62 := sixtyTwo_le_of_568 hΛ
  have h2 := two_le_of_62 h62
  have hs := mmSubject_le_of_568 hΛ
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA⟩ := gen_macArm_zero (K := K) (n + 45) (.atom 0) (.atom 0)
  have ihInnerArm := confined_macArm_zero (Λ := Λ) (.atom 0) (.atom 0) innerA
    (macCore_atoms_le 0 0 0 h62) h62 (atom_le_of_62 0 h62)
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 13) ha0 a10 b01 innerA
  have ihInner := confined_gen_invokeMac (Λ := Λ) ha0 a10 b01 innerA hinner
    (confined_gen_op1 (Λ := Λ) ha0 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot10 a10 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot13 b01 hs h2)
    ihInnerArm hs h62 (by simpa [op1, op0] using invokeMac_inner_le hΛ 10 13)
    (atom_le_of_62 0 h62) (macCore_atoms_le 0 0 0 h62)
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := confined_macArm_one_m1 (Λ := Λ) outerA h62
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 15)
    hinner' a11 b11 outerA
  have hh := h
  simp only [mmC11, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact confined_gen_invokeMac (Λ := Λ) hinner' a11 b11 outerA houter
    ihInner
    (confined_gen_op0 (Λ := Λ) mmSubject_slot11 a11 hs h2)
    (confined_gen_op0 (Λ := Λ) mmSubject_slot15 b11 hs h2)
    ihOuterArm hs h62 (by simpa [mmC11, mac2, invokeMac, slam, op7, quote, op1, op0]
      using mmCij_le_of_568 hΛ mmC11_leaves)
    (atom_le_of_62 1 h62) (macCore_atoms_le 0 1 1 h62)

theorem confined_mm {Λ : ℕ} {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) 64 mmSubject mmFormula = .ok (t, mmC))
    (hΛ : 568 ≤ Λ) :
    TraceConfined Λ t := by
  have hs := mmSubject_le_of_568 hΛ
  obtain ⟨t00, h00⟩ := gen_mmC00 (K := K) 6
  obtain ⟨t01, h01⟩ := gen_mmC01 (K := K) 6
  obtain ⟨t10, h10⟩ := gen_mmC10 (K := K) 6
  obtain ⟨t11, h11⟩ := gen_mmC11 (K := K) 6
  have ih00 := confined_mmC00 (Λ := Λ) h00 hΛ
  have ih01 := confined_mmC01 (Λ := Λ) h01 hΛ
  have ih10 := confined_mmC10 (Λ := Λ) h10 hΛ
  have ih11 := confined_mmC11 (Λ := Λ) h11 hΛ
  have h00c := h00
  simp only [mmC00, mac2, invokeMac, slam, op7, quote, op1] at h00c
  have h01c := h01
  simp only [mmC01, mac2, invokeMac, slam, op7, quote, op1] at h01c
  have h10c := h10
  simp only [mmC10, mac2, invokeMac, slam, op7, quote, op1] at h10c
  have h11c := h11
  simp only [mmC11, mac2, invokeMac, slam, op7, quote, op1] at h11c
  have hL := gen_cons (K := K) 62 h00c h01c
  have hR := gen_cons (K := K) 62 h10c h11c
  have hop := gen_cons (K := K) 63 hL hR
  have hh := h
  simp only [mmFormula, mmC00, mmC01, mmC10, mmC11, mac2, invokeMac, slam, op7,
    quote, op1, op0] at hh
  have huniq := gen_ok_unique hh hop
  rw [huniq.1]
  have hfL : (Noun.cell mmC00 mmC01).leaves ≤ Λ := by
    simp [cell_leaves, mmC00_leaves, mmC01_leaves]
    exact le_trans (by decide : 284 ≤ 568) hΛ
  have hfR : (Noun.cell mmC10 mmC11).leaves ≤ Λ := by
    simp [cell_leaves, mmC10_leaves, mmC11_leaves]
    exact le_trans (by decide : 284 ≤ 568) hΛ
  have heL : (Noun.cell (.atom 2) (.atom 1)).leaves ≤ Λ := by
    simp [cell_leaves, atom_leaves]; exact le_trans (by decide : 2 ≤ 568) hΛ
  have heR : (Noun.cell (.atom 1) (.atom 1)).leaves ≤ Λ := by
    simp [cell_leaves, atom_leaves]; exact le_trans (by decide : 2 ≤ 568) hΛ
  exact confined_gen_cons (Λ := Λ) hL hR hop
    (confined_gen_cons (Λ := Λ) h00c h01c hL ih00 ih01 hs hfL heL)
    (confined_gen_cons (Λ := Λ) h10c h11c hR ih10 ih11 hs hfR heR)
    hs (le_trans (le_of_eq mmFormula_leaves) hΛ)
    (le_trans (le_of_eq mmC_leaves) (le_trans (by decide : 4 ≤ 568) hΛ))

/-- Combinator induction, not a binder. `Λ = 568` is the program-text numeral. -/
theorem mm_traceConfined :
    TraceConfined 568 (airReorder (mmTree (K := K))) :=
  traceConfined_airReorder _ (confined_mm (mmTree_gen (K := K)) (le_refl 568))

/-- Lift to the Goldilocks config host `Ksz = 2048` by monotonicity. -/
theorem mm_traceConfined_2048 :
    TraceConfined 2048 (airReorder (mmTree (K := K))) :=
  traceConfined_mono (by decide : 568 ≤ 2048) mm_traceConfined

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.mm_traceConfined
#print axioms Nock.NockVMROM.Thm54.TraceGen.confined_gen_invokeMac
#print axioms Nock.NockVMROM.Thm54.TraceGen.confined_macArm_one_m1
