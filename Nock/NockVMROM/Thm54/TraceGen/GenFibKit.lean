/-
  Nock/NockVMROM/Thm54/TraceGen/GenFibKit.lean

  Combinators the matmul kit does not name: `OP_2`, `OP_3`, `OP_8`
  for size, `TraceConfined`, `SeedGood`, `TraceSep`, and served memory.
  Same shape as `GenMatmulTraceConfined` / `GenProgramKitMem`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenFib
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMemSize
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksHbad
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenDyckBadSeed
import Nock.NockVMROM.Thm54.TraceGen.GenProgramKitMem
import Nock.NockVMROM.Thm54.TraceGen.GenGenericOffdiag
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonVcomp

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## Size of `OP_2` / `OP_3` / `OP_8` -/

theorem size_node_three {α} (l : α) (a b c : NTree α) :
    (NTree.node l [a, b, c]).size = 1 + a.size + b.size + c.size := by
  simp [NTree.size]
  omega

theorem gen_op2_size (n : ℕ) {subject b c sf1 sf2 result : Noun}
    {bTree cTree mTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (cTree, sf2))
    (hm : genComputeSkeleton (K := K) n sf1 sf2 = .ok (mTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op2 b c) = .ok (t, r)) :
    t.size = 1 + bTree.size + cTree.size + mTree.size :=
  gen_ok_size h (by simpa [op2] using gen_op2 (K := K) n hb hc hm)
    (size_node_three _ _ _ _)

theorem gen_op3_size (n : ℕ) {subject tail callResult : Noun}
    {callTree t : NTree (GenComputeRow K)} {r : Noun}
    (hc : genComputeSkeleton (K := K) n subject tail = .ok (callTree, callResult))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op3 tail) = .ok (t, r)) :
    t.size = 1 + callTree.size :=
  gen_ok_size h (by simpa [op3] using gen_op3 (K := K) n hc) (size_node_one _ _)

theorem gen_op8_size (n : ℕ) {subject b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n (.cell sb subject) c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op8 b c) = .ok (t, r)) :
    t.size = 1 + bTree.size + cTree.size :=
  gen_ok_size h (by simpa [op8] using gen_op8 (K := K) n hb hc)
    (size_node_two _ _ _)

/-! ## `TraceConfined` for the three new opcodes -/

theorem confined_gen_op3 {Λ n : ℕ} {s tail callResult : Noun}
    {callTree t : NTree (GenComputeRow K)} {res : Noun}
    (hcall : genComputeSkeleton (K := K) n s tail = .ok (callTree, callResult))
    (h : genComputeSkeleton (K := K) (n + 1) s (op3 tail) = .ok (t, res))
    (ih : TraceConfined Λ callTree)
    (hs : s.leaves ≤ Λ) (hf : (op3 tail).leaves ≤ Λ)
    (he : (Noun.wut callResult).leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_op3 (K := K) n hcall
  rw [(gen_ok_unique h (by simpa [op3] using h')).1]
  refine confined_of_children ?_ ?_
  · refine rowNouns_of_leaves ?_ ?_ ?_
    · simp [skelNode, genSkelOp3]; exact hs
    · simp [skelNode, genSkelOp3]; exact hf
    · simpa [skelNode, genSkelOp3] using he
  · intro c hc
    simp [NTree.children] at hc
    subst c
    exact ih

theorem confined_gen_op2 {Λ n : ℕ} {s b c sf1 sf2 result : Noun}
    {bTree cTree mTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n s c = .ok (cTree, sf2))
    (hm : genComputeSkeleton (K := K) n sf1 sf2 = .ok (mTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op2 b c) = .ok (t, res))
    (ihb : TraceConfined Λ bTree) (ihc : TraceConfined Λ cTree)
    (ihm : TraceConfined Λ mTree)
    (hs : s.leaves ≤ Λ) (hf : (op2 b c).leaves ≤ Λ)
    (he : result.leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_op2 (K := K) n hb hc hm
  rw [(gen_ok_unique h (by simpa [op2] using h')).1]
  refine confined_of_children ?_ ?_
  · refine rowNouns_of_leaves ?_ ?_ ?_
    · simp [skelNode, genSkelOp2]; exact hs
    · simp [skelNode, genSkelOp2]; exact hf
    · simp [skelNode, genSkelOp2]; exact he
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl | rfl
    · exact ihb
    · exact ihc
    · exact ihm

theorem confined_gen_op8 {Λ n : ℕ} {s b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n (.cell sb s) c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op8 b c) = .ok (t, res))
    (ihb : TraceConfined Λ bTree) (ihc : TraceConfined Λ cTree)
    (hs : s.leaves ≤ Λ) (hf : (op8 b c).leaves ≤ Λ)
    (he : result.leaves ≤ Λ) :
    TraceConfined Λ t := by
  have h' := gen_op8 (K := K) n hb hc
  rw [(gen_ok_unique h (by simpa [op8] using h')).1]
  refine confined_of_children ?_ ?_
  · refine rowNouns_of_leaves ?_ ?_ ?_
    · simp [skelNode, genSkelOp8]; exact hs
    · simp [skelNode, genSkelOp8]; exact hf
    · simp [skelNode, genSkelOp8]; exact he
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihc

/-! ## `SeedGood` combinators (OP3 is live; `SeedOK` is not) -/

theorem seedGood_of_children {z : K} {lab : GenComputeRow K}
    {cs : List (NTree (GenComputeRow K))}
    (hroot : RowSeedGood z lab)
    (hcs : ∀ c ∈ cs, SeedGood z c) :
    SeedGood z (.node lab cs) := by
  intro v hv
  cases hv with
  | here => exact hroot
  | sub hs hu => exact hcs _ hs _ hu

theorem seedGood_leaf {z : K} {lab : GenComputeRow K}
    (hroot : RowSeedGood z lab) :
    SeedGood z (.node lab []) :=
  seedGood_of_children hroot (fun _ hc => by simp [NTree.children] at hc)

theorem rowSeedGood_vacuous {z : K} {g : GenComputeRow K}
    (hneC : g.skel.state ≠ .cons) (hne5 : g.skel.state ≠ .s5)
    (hne3 : g.skel.state ≠ .s3) :
    RowSeedGood z g :=
  ⟨fun h => absurd h hneC, fun h => absurd h hne5, fun h => absurd h hne3⟩

theorem seedGood_gen_op0 {z : K} {n : ℕ} {s : Noun} {ax : ℕ} {r : Noun}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (hslot : Noun.slot ax s = some r)
    (h : genComputeSkeleton (K := K) (n + 1) s (op0 ax) = .ok (t, res)) :
    SeedGood z t := by
  have h' := gen_op0 (K := K) n hslot
  rw [(gen_ok_unique h h').1]
  exact seedGood_leaf (rowSeedGood_vacuous
    (by simp [skelNode, genSkelOp0])
    (by simp [skelNode, genSkelOp0])
    (by simp [skelNode, genSkelOp0]))

theorem seedGood_gen_op1 {z : K} {n : ℕ} {s : Noun} {k : ℕ}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) s (op1 k) = .ok (t, res)) :
    SeedGood z t := by
  have h' := gen_op1 (K := K) n s k
  rw [(gen_ok_unique h h').1]
  exact seedGood_leaf (rowSeedGood_vacuous
    (by simp [skelNode, genSkelOp1])
    (by simp [skelNode, genSkelOp1])
    (by simp [skelNode, genSkelOp1]))

theorem seedGood_gen_quote {z : K} {n : ℕ} {s result : Noun}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) s (quote result) = .ok (t, res)) :
    SeedGood z t := by
  have h' := gen_quote (K := K) n s result
  rw [(gen_ok_unique h h').1]
  exact seedGood_leaf (rowSeedGood_vacuous
    (by simp [skelNode, genSkelOp1])
    (by simp [skelNode, genSkelOp1])
    (by simp [skelNode, genSkelOp1]))

theorem seedGood_gen_op4 {z : K} {n : ℕ} {s tail callResult result : Noun}
    {callTree t : NTree (GenComputeRow K)} {res : Noun}
    (hcall : genComputeSkeleton (K := K) n s tail = .ok (callTree, callResult))
    (hinc : Noun.lus callResult = some result)
    (h : genComputeSkeleton (K := K) (n + 1) s (op4 tail) = .ok (t, res))
    (ih : SeedGood z callTree) :
    SeedGood z t := by
  have h' := gen_op4 (K := K) n hcall hinc
  rw [(gen_ok_unique h h').1]
  refine seedGood_of_children ?_ ?_
  · exact rowSeedGood_vacuous
      (by simp [skelNode, genSkelOp4])
      (by simp [skelNode, genSkelOp4])
      (by simp [skelNode, genSkelOp4])
  · intro c hc
    simp [NTree.children] at hc
    subst c
    exact ih

theorem seedGood_gen_op6_zero {z : K} {n : ℕ} {s b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (condTree, .atom 0))
    (hc : genComputeSkeleton (K := K) n s c = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op6 b c d) = .ok (t, res))
    (ihb : SeedGood z condTree) (ihc : SeedGood z takenTree) :
    SeedGood z t := by
  have h' := gen_op6_zero (K := K) n (d := d) hb hc
  rw [(gen_ok_unique h h').1]
  refine seedGood_of_children ?_ ?_
  · exact rowSeedGood_vacuous
      (by simp [skelNode, genSkelOp6])
      (by simp [skelNode, genSkelOp6])
      (by simp [skelNode, genSkelOp6])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihc

theorem seedGood_gen_op6_one {z : K} {n : ℕ} {s b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (condTree, .atom 1))
    (hd : genComputeSkeleton (K := K) n s d = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op6 b c d) = .ok (t, res))
    (ihb : SeedGood z condTree) (ihd : SeedGood z takenTree) :
    SeedGood z t := by
  have h' := gen_op6_one (K := K) n (c := c) hb hd
  rw [(gen_ok_unique h h').1]
  refine seedGood_of_children ?_ ?_
  · exact rowSeedGood_vacuous
      (by simp [skelNode, genSkelOp6])
      (by simp [skelNode, genSkelOp6])
      (by simp [skelNode, genSkelOp6])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihd

theorem seedGood_gen_cons {z : K} {n : ℕ}
    {s leftHead leftTail tail lRes rRes : Noun}
    {lTree rTree t : NTree (GenComputeRow K)} {res : Noun}
    (hl : genComputeSkeleton (K := K) n s (.cell leftHead leftTail) =
      .ok (lTree, lRes))
    (hr : genComputeSkeleton (K := K) n s tail = .ok (rTree, rRes))
    (h : genComputeSkeleton (K := K) (n + 1) s
      (.cell (.cell leftHead leftTail) tail) = .ok (t, res))
    (ihl : SeedGood z lTree) (ihr : SeedGood z rTree)
    (hdyck : (encC z (.cell leftHead leftTail)).dyck ≠ 0) :
    SeedGood z t := by
  have h' := gen_cons (K := K) n hl hr
  rw [(gen_ok_unique h h').1]
  refine seedGood_of_children ?_ ?_
  · refine ⟨?_, ?_, ?_⟩
    · intro _
      simpa [skelNode, genSkelCons, formulaHead] using hdyck
    · intro hs5
      simp [skelNode, genSkelCons] at hs5
    · intro hs3
      simp [skelNode, genSkelCons] at hs3
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihl
    · exact ihr

/-- Cell-branch `op3CallSizeOk`: `z^leaves ≠ z` from the seed order. -/
theorem op3CallSizeOk_of_cell_order {z : K} {s : ComputeRowSkeleton}
    {x y : Noun}
    (hres : P8Census.skeletonSubformula s 0 TripleSlot.result = .cell x y)
    (hz : z ≠ 0)
    (hord : ¬ orderOf z ∣ ((Noun.cell x y).leaves - 1)) :
    op3CallSizeOk z s := by
  unfold op3CallSizeOk
  rw [hres]
  intro hsz
  have hpow : z ^ (Noun.cell x y).leaves = z := by
    simpa [encC_size] using hsz
  have hpos : 1 ≤ (Noun.cell x y).leaves := leaves_pos _
  have : z ^ ((Noun.cell x y).leaves - 1) = 1 := by
    have hsplit :
        z ^ (Noun.cell x y).leaves =
          z ^ ((Noun.cell x y).leaves - 1 + 1) := by
      congr 1; omega
    rw [hsplit, pow_succ] at hpow
    have : z ^ ((Noun.cell x y).leaves - 1) * z = 1 * z := by
      simpa [one_mul] using hpow
    exact mul_right_cancel₀ hz this
  exact hord (orderOf_dvd_of_pow_eq_one this)

theorem op3CallSizeOk_of_atom {z : K} {s : ComputeRowSkeleton} {k : ℕ}
    (hres : P8Census.skeletonSubformula s 0 TripleSlot.result = .atom k) :
    op3CallSizeOk z s := by
  unfold op3CallSizeOk
  rw [hres]
  trivial

theorem seedGood_gen_op3 {z : K} {n : ℕ} {s tail callResult : Noun}
    {callTree t : NTree (GenComputeRow K)} {res : Noun}
    (hcall : genComputeSkeleton (K := K) n s tail = .ok (callTree, callResult))
    (h : genComputeSkeleton (K := K) (n + 1) s (op3 tail) = .ok (t, res))
    (ih : SeedGood z callTree)
    (hok : op3CallSizeOk z
      (genSkelOp3 s (.cell (.atom 3) tail) (.atom 3) tail s tail callResult
        (Noun.wut callResult))) :
    SeedGood z t := by
  have h' := gen_op3 (K := K) n hcall
  rw [(gen_ok_unique h (by simpa [op3] using h')).1]
  refine seedGood_of_children ?_ ?_
  · refine ⟨?_, ?_, ?_⟩
    · intro hst; simp [skelNode, genSkelOp3] at hst
    · intro hst; simp [skelNode, genSkelOp3] at hst
    · intro _
      simpa [skelNode, op3] using hok
  · intro c hc
    simp [NTree.children] at hc
    subst c
    exact ih

theorem seedGood_gen_op2 {z : K} {n : ℕ} {s b c sf1 sf2 result : Noun}
    {bTree cTree mTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n s c = .ok (cTree, sf2))
    (hm : genComputeSkeleton (K := K) n sf1 sf2 = .ok (mTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op2 b c) = .ok (t, res))
    (ihb : SeedGood z bTree) (ihc : SeedGood z cTree)
    (ihm : SeedGood z mTree) :
    SeedGood z t := by
  have h' := gen_op2 (K := K) n hb hc hm
  rw [(gen_ok_unique h (by simpa [op2] using h')).1]
  refine seedGood_of_children ?_ ?_
  · exact rowSeedGood_vacuous
      (by simp [skelNode, genSkelOp2])
      (by simp [skelNode, genSkelOp2])
      (by simp [skelNode, genSkelOp2])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl | rfl
    · exact ihb
    · exact ihc
    · exact ihm

theorem seedGood_gen_op8 {z : K} {n : ℕ} {s b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n (.cell sb s) c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op8 b c) = .ok (t, res))
    (ihb : SeedGood z bTree) (ihc : SeedGood z cTree) :
    SeedGood z t := by
  have h' := gen_op8 (K := K) n hb hc
  rw [(gen_ok_unique h (by simpa [op8] using h')).1]
  refine seedGood_of_children ?_ ?_
  · exact rowSeedGood_vacuous
      (by simp [skelNode, genSkelOp8])
      (by simp [skelNode, genSkelOp8])
      (by simp [skelNode, genSkelOp8])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihc

/-! ## `TraceSep` for the three new opcodes -/

theorem traceSep_gen_op3 {z : K} {n : ℕ} {s tail callResult : Noun}
    {callTree t : NTree (GenComputeRow K)} {res : Noun}
    (hcall : genComputeSkeleton (K := K) n s tail = .ok (callTree, callResult))
    (h : genComputeSkeleton (K := K) (n + 1) s (op3 tail) = .ok (t, res))
    (ih : TraceSep z callTree) :
    TraceSep z t := by
  have h' := gen_op3 (K := K) n hcall
  rw [(gen_ok_unique h (by simpa [op3] using h')).1]
  refine traceSep_of_children ?_ ?_ ?_
  · exact rowOffdiag_vacuous
      (by simp [skelNode, genSkelOp3])
      (by simp [skelNode, genSkelOp3])
  · exact wrap_vacuous (by simp [skelNode, genSkelOp3])
  · intro c hc
    simp [NTree.children] at hc
    subst c
    exact ih

theorem traceSep_gen_op2 {z : K} {n : ℕ} {s b c sf1 sf2 result : Noun}
    {bTree cTree mTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n s c = .ok (cTree, sf2))
    (hm : genComputeSkeleton (K := K) n sf1 sf2 = .ok (mTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op2 b c) = .ok (t, res))
    (ihb : TraceSep z bTree) (ihc : TraceSep z cTree)
    (ihm : TraceSep z mTree) :
    TraceSep z t := by
  have h' := gen_op2 (K := K) n hb hc hm
  rw [(gen_ok_unique h (by simpa [op2] using h')).1]
  refine traceSep_of_children ?_ ?_ ?_
  · exact rowOffdiag_vacuous
      (by simp [skelNode, genSkelOp2])
      (by simp [skelNode, genSkelOp2])
  · exact wrap_vacuous (by simp [skelNode, genSkelOp2])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl | rfl
    · exact ihb
    · exact ihc
    · exact ihm

theorem traceSep_gen_op8 {z : K} {n : ℕ} {s b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n (.cell sb s) c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op8 b c) = .ok (t, res))
    (ihb : TraceSep z bTree) (ihc : TraceSep z cTree) :
    TraceSep z t := by
  have h' := gen_op8 (K := K) n hb hc
  rw [(gen_ok_unique h (by simpa [op8] using h')).1]
  refine traceSep_of_children ?_ ?_ ?_
  · exact rowOffdiag_vacuous
      (by simp [skelNode, genSkelOp8])
      (by simp [skelNode, genSkelOp8])
  · exact wrap_vacuous (by simp [skelNode, genSkelOp8])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihc

/-! ## Served memory for `OP_2` (the kit is missing this arm) -/

theorem genMemForestFromList_three (E : Noun → ComputeTable.FP K) (z α : K)
    (a b c : NTree (GenComputeRow K)) :
    genMemForestFromList E z α lmb [a, b, c] =
      genMemForestFromTree E z α lmb a ++
        (genMemForestFromTree E z α lmb b ++ genMemForestFromTree E z α lmb c) := by
  simp [genMemForestFromList_cons, genMemForestFromList_nil]

theorem gen_op2_mem (E : Noun → ComputeTable.FP K) (z α : K)
    (n : ℕ) {subject b c sf1 sf2 result : Noun}
    {bTree cTree mTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (cTree, sf2))
    (hm : genComputeSkeleton (K := K) n sf1 sf2 = .ok (mTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op2 b c) = .ok (t, r)) :
    (genMemForestFromTree E z α lmb t).length =
      1 + (genMemForestFromTree E z α lmb bTree).length +
        (genMemForestFromTree E z α lmb cTree).length +
        (genMemForestFromTree E z α lmb mTree).length ∧
    totalSize (genMemForestFromTree E z α lmb t) =
      7 + nounWalkSize b + nounWalkSize c +
        totalSize (genMemForestFromTree E z α lmb bTree) +
        totalSize (genMemForestFromTree E z α lmb cTree) +
        totalSize (genMemForestFromTree E z α lmb mTree) := by
  refine gen_ok_mem E z α h (by simpa [op2] using gen_op2 (K := K) n hb hc hm) ?_ ?_
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
      genMemForestFromList_three, List.length_append, List.length_append,
      List.length_append]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_chain_length (lmb := lmb) (hc := rfl)]
    omega
  · rw [genMemForestFromTree_node, extractNodeReqs_skel_two,
      genMemForestFromList_three, totalSize_append, totalSize_append,
      totalSize_append]
    simp [ServiceReq.root, ServiceReq.child, ServiceReq.axis]
    rw [genRowMemForest_chain32_size]
    simp [nounWalkSize]
    omega

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.gen_op2_mem
#print axioms Nock.NockVMROM.Thm54.TraceGen.confined_gen_op2
#print axioms Nock.NockVMROM.Thm54.TraceGen.seedGood_gen_op3
