/-
  Nock/Jet/ChipJ8Toy.lean

  **Honest acceptance of the J chip at matmul `n = 2`.**
  New module, additive.  The honest trace generator (`honestJ8`: registry rows, then per call the
  call row and the rows of every J-3a node, read chains included, with handles into a list memory
  `mem`), and at `p = 1009`, `R = matmulT 2`, one call on J-2's toy subject:

  * `toy_accepted`: the honest rows meet `Accepted` (layout, bounds, unique provides, every base
    gate, the in-chip balance in existence form) — kernel;
  * `toy_memory`: the list memory meets `MemoryBB` (kind-`0` atoms, every export read genuine,
    the registry root denotes `compile 1009 (matmulT 2)`) — kernel;
  * `toy_holds`: hence, by `jetChip_holds`, the call's output handle denotes `T.sem` and
    `HoldsN ⟨toyS, compile 1009 (matmulT 2), toyCG⟩`;
  * `toy_tampered_rejected`: a `mul` row with a wrong value fails a base gate.

  NOT built here (U): the round-1 `𝕂′` columns (slot inverses, accumulators) of the honest trace;
  acceptance is stated at the level `jetChip_sound` consumes.
-/
import Nock.Jet.ChipJ8

set_option autoImplicit false

namespace Nock.Jet.ChipJ8

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp
open Nock.NockVMROM.Thm54.CoordinateCompiler

section Gen
variable {p : ℕ} [Fact p.Prime]

/-- All cell subterms (pre-order). -/
def subs : Noun → List Noun
  | .atom _ => []
  | x@(.cell l r) => x :: (subs l ++ subs r)

/-- The honest handle of a noun: an atom is kind `0`, a cell is `(1, index in mem)`. -/
def hOf (mem : List Noun) : Noun → ZMod p × ZMod p
  | .atom v => (0, (v : ZMod p))
  | x@(.cell _ _) => (1, ((mem.idxOf x : ℕ) : ZMod p))

/-- The list memory's denotation. -/
def denM (mem : List Noun) (h : ZMod p × ZMod p) : Option Noun :=
  if h.1 = 0 then some (.atom h.2.val) else if h.1 = 1 then mem[h.2.val]? else none

def w0 : WRow (ZMod p) := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- A witness row from its handles (`m mv val v1 v2` then `hN hL hR`). -/
def mkW (m mv val v1 v2 : ZMod p) (hN hL hR : ZMod p × ZMod p) : WRow (ZMod p) :=
  ⟨m, mv, val, v1, v2, hN.1, hN.2, hL.1, hL.2, hR.1, hR.2⟩

def chainW (mem : List Noun) (c dst : ℕ) : ℕ → ℕ → List Bool → Noun → List (CRow (ZMod p))
  | src, _, [], x =>
    [⟨⟨.cp, 0, c, dst, src, 0⟩, mkW 0 1 0 0 0 (0, 0) (hOf mem x) (0, 0)⟩]
  | src, ctr, b :: bs, x =>
    ⟨⟨if b then .sr else .sl, 0, c, ctr, src, 0⟩,
      mkW 0 1 0 0 0 (hOf mem x) (hOf mem (nhd x)) (hOf mem (ntl x))⟩ ::
      chainW mem c dst ctr (ctr + 1) bs (if b then ntl x else nhd x)

/-- The honest rows of one node (`lk` = the J-3a honest values, `s` the subject). -/
def nodeW (mem : List Noun) (c S ctr : ℕ) (lk : ℕ → Noun) (s : Noun) (nd : JNode) :
    List (CRow (ZMod p)) :=
  match nd.op with
  | .var _ ax => chainW mem c nd.id S ctr (axPath ax) s
  | .nth j => chainW mem c nd.id nd.a ctr (List.replicate j true ++ [false]) (lk nd.a)
  | .tlN n => chainW mem c nd.id nd.a ctr (List.replicate n true) (lk nd.a)
  | .const k => [⟨⟨.cst, 0, c, nd.id, k, 0⟩, mkW 0 1 (k : ZMod p) 0 0 (0, 0) (0, 0) (0, 0)⟩]
  | .add => [⟨⟨.add, 0, c, nd.id, nd.a, nd.b⟩, mkW 0 1 (atomVal (lk nd.id) : ZMod p)
      (atomVal (lk nd.a) : ZMod p) (atomVal (lk nd.b) : ZMod p) (0, 0) (0, 0) (0, 0)⟩]
  | .mul => [⟨⟨.mul, 0, c, nd.id, nd.a, nd.b⟩, mkW 0 1 (atomVal (lk nd.id) : ZMod p)
      (atomVal (lk nd.a) : ZMod p) (atomVal (lk nd.b) : ZMod p) (0, 0) (0, 0) (0, 0)⟩]
  | .pair => [⟨⟨.rp, 0, c, nd.id, nd.a, nd.b⟩, mkW 0 1 0 0 0
      (hOf mem (lk nd.id)) (hOf mem (lk nd.a)) (hOf mem (lk nd.b))⟩]
  | .isF => [⟨⟨.isf, 0, c, nd.id, nd.a, 0⟩, mkW 0 1 0 (atomVal (lk nd.a) : ZMod p) 0 (0, 0) (0, 0) (0, 0)⟩]
  | .isNil => [⟨⟨.nil, 0, c, nd.id, nd.a, 0⟩, mkW 0 1 0 0 0 (0, 0) (0, 0) (0, 0)⟩]

def nodesW (mem : List Noun) (c S : ℕ) (lk : ℕ → Noun) (s : Noun) :
    ℕ → List JNode → List (CRow (ZMod p))
  | _, [] => []
  | ctr, nd :: nds => nodeW mem c S ctr lk s nd ++ nodesW mem c S lk s (ctr + nodeVirt nd) nds

/-- J-3a's honest node values of call `c`. -/
def honestLook (T : Tpl) (s : Noun) (c : ℕ) (n : ℕ) : Noun :=
  (((honestRows p T s c)[n]?).map JRow.val).getD z0

/-- The honest block of call `c` (template `R i`, subject `s`). -/
def blockW (mem : List Noun) (R : ℕ → Tpl) (c i : ℕ) (s : Noun) : List (CRow (ZMod p)) :=
  let T := R i
  let N := (nodesOf T).length
  let lk := honestLook (p := p) T s c
  ⟨callPre R c i, mkW 1 1 0 0 0
      (hOf mem (compile p T)) (hOf mem s) (hOf mem (lk 0))⟩ ::
    nodesW mem c N lk s (N + 1) (nodesOf T)

/-- The honest J chip rows: one registry row per id, one block per call `(i, s)`. -/
def honestJ8 (mem : List Noun) (R : ℕ → Tpl) (regs : List ℕ) (calls : List (ℕ × Noun)) :
    List (CRow (ZMod p)) :=
  regs.map (fun i => ⟨regPre i, mkW 0 1 0 0 0
    (hOf mem (compile p (R i))) (0, 0) (0, 0)⟩) ++
  (calls.zipIdx.flatMap fun ⟨⟨i, s⟩, c⟩ => blockW mem R c i s)

theorem denM_zero (mem : List Noun) (v : ZMod p) : denM mem (0, v) = some (.atom v.val) := by
  simp [denM]

end Gen

/-! ## The toy: `p = 1009`, `R = matmulT 2`, one call on J-2's toy subject -/

instance fact1009 : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

def toyR : ℕ → Tpl := fun _ => matmulT 2

/-- The memory: the subject's cells, the product's cells, the compiled formula. -/
def toyMem : List Noun := subs toyS ++ subs toyCG ++ [compile 1009 (matmulT 2)]

def toyRowsJ : List (CRow (ZMod 1009)) := honestJ8 toyMem toyR [0] [(0, toyS)]

def toyDen : ZMod 1009 × ZMod 1009 → Option Noun := denM toyMem

/-- At `p = 1009` the toy product does not wrap: `[[5 8] [15 22]]`. -/
theorem toy_sem1009 : (matmulT 2).sem 1009 toyS = some toyCG := by
  refine sem_eq_some_iff.2 ⟨![toyA, toyB], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [matmulT, toyS, Noun.slot]
  · intro i; fin_cases i <;> decide
  · decide

/-- Row count of the honest chip trace (`1` registry row + `1` call row + node and chain rows). -/
theorem toyRowsJ_length : toyRowsJ.length = 237 := by decide +kernel

theorem toy_layout : toyRowsJ.map CRow.pre = layoutJ8 toyR [0] [0] := by decide +kernel

theorem toy_small : ∀ q ∈ layoutJ8 toyR [0] [0],
    q.id < 1009 ∧ q.cid < 1009 ∧ q.nid < 1009 ∧ q.n1 < 1009 ∧ q.n2 < 1009 := by decide +kernel

theorem toy_uniq : ((layoutJ8 toyR [0] [0]).filterMap tvKey).Nodup := by decide +kernel

theorem toy_gates : ∀ r ∈ toyRowsJ, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod 1009))),
    g.eval (envOf r) = 0 := by decide +kernel

theorem toy_bal : ∀ r ∈ toyRowsJ, ∀ κ ∈ consK r, ∃ r' ∈ toyRowsJ, κ ∈ provK r' := by
  decide +kernel

/-- **Honest acceptance** (the chip side). -/
theorem toy_accepted : Accepted toyR [0] [0] toyRowsJ :=
  ⟨toy_layout, toy_small, toy_uniq, toy_gates, toy_bal⟩

theorem toy_gen : ∀ r ∈ toyRowsJ, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
    recB toyDen r = true := by decide +kernel

theorem toy_reg : ∀ r ∈ toyRowsJ, r.pre.kd = .reg →
    toyDen (r.w.kN, r.w.vN) = some (compile 1009 (toyR r.pre.id)) := by decide +kernel

/-- **Honest acceptance** (the memory black box, met by the list memory). -/
theorem toy_memory : MemoryBB toyR toyRowsJ toyDen := ⟨denM_zero toyMem, toy_gen, toy_reg⟩

/-- The call row. -/
def toyCall : CRow (ZMod 1009) :=
  ⟨callPre toyR 0 0, mkW 1 1 0 0 0 (hOf toyMem (compile 1009 (matmulT 2))) (hOf toyMem toyS)
    (hOf toyMem (honestLook (p := 1009) (matmulT 2) toyS 0 0))⟩

theorem toyCall_mem : toyCall ∈ toyRowsJ := by decide +kernel
theorem toyCall_pre : toyCall.pre = callPre toyR 0 0 := rfl
theorem toyCall_subject : toyDen (toyCall.w.kL, toyCall.w.vL) = some toyS := by decide +kernel
theorem toyCall_out : toyDen (toyCall.w.kR, toyCall.w.vR) = some toyCG := by decide +kernel

theorem toy_axPos : axPosB (toyR 0) = true := by decide +kernel

/-- **The soundness theorem applied to the honest trace** (non-vacuity of its hypotheses): the
call's handles denote `compile 1009 (matmulT 2)` and `toyCG`, with `HoldsN`. -/
theorem toy_holds :
    toyDen (toyCall.w.kN, toyCall.w.vN) = some (compile 1009 (matmulT 2)) ∧
    ∃ e, toyDen (toyCall.w.kR, toyCall.w.vR) = some e ∧ (matmulT 2).sem 1009 toyS = some e ∧
      HoldsN ⟨toyS, compile 1009 (matmulT 2), e⟩ :=
  jetChip_holds toyR [0] [0] toyRowsJ toyDen toy_accepted toy_memory 0 0 rfl toy_axPos
    (matmul_wellTyped (by norm_num) 2) toyCall toyCall_mem toyCall_pre toyS toyCall_subject

/-! ## A tampered row is rejected -/

/-- The first `mul` row of the honest trace. -/
def toyMulIdx : ℕ := (toyRowsJ.findIdx fun r => r.pre.kd == .mul)

def toyTamperedJ : List (CRow (ZMod 1009)) :=
  toyRowsJ.modify toyMulIdx fun r => { r with w := { r.w with val := r.w.val + 1 } }

/-- **The tampered trace fails a base gate** (the `mul` gate), so it is not `Accepted`. -/
theorem toy_tampered_rejected :
    ¬ ∀ r ∈ toyTamperedJ, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod 1009))), g.eval (envOf r) = 0 := by
  decide +kernel

end Nock.Jet.ChipJ8
