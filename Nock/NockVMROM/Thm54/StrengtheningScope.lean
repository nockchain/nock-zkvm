/-
  Nock/NockVMROM/Thm54/StrengtheningScope.lean

  This module is **measurement only**.  It shadows nothing shipped: every AIR/verifier
  copy below carries a fresh name and no shipped declaration is modified.  Nothing here
  is capstone-facing and nothing here is claimed to be paper-1-1; the theorems are
  evidence for a scoping report, not statements about `Thm:NockVMROM`.

  Axioms: every theorem below is `{propext, Classical.choice, Quot.sound}` (the two
  purely-computational ones drop `Classical.choice`).  No `sorry`/`admit`/`native_decide`.

  ## Strengthening 1 — the OP9 axis-operand pin

  `Nock/AIR.lean:808` (`evalRExprs.s9`) carries `[.Sub cFth.size (chl 1), cFth.dyck]`,
  i.e. `f_th.size = z ∧ f_th.dyck = 0`; the Prop-level twins are
  `ComputeTable.evalR` (decl `ComputeTable.lean:584`, pin at `:619`) and
  `ComputeTable.evalV` (decl `:626`, pin at `:649`); the packed twin is
  `AIRPacked.extraPacked` (decl `AIRPacked.lean:368`, `.s9` entries at `:374-375`).  Algorithm `NockCompute` line the paper writes
  only `mem_root_3 = sf_evaluation_1`, `mem_axis_3 = formula_tail_head`,
  `timestamp_3 = ln`; `tab:V_comp_equality`'s `f_th` row is `⊥`
  for every one of the eleven opcodes.

  §1 establishes three things about it:
  * `(z, 0, ⊥)` is the paper's own *atom* idiom, used at three licensed sites, so the OP9 pin is the same predicate;
  * it is **not derivable** from the remaining OP9 clauses — an explicit witness
    satisfies every other conjunct of `Vcomp` at `.s9` with `f_th.dyck ≠ 0`;
  * it costs **nothing on the completeness side**: any row whose `f_th` is the
    fingerprint of a Nock atom satisfies it definitionally.

  ## Strengthening 2 — the memory axis-accumulator seed boundary

  `Nock/AIR.lean:2362` `memSeedBoundaryExprs` pins `axis_counts = axis_indicator = 0`
  at the walk root.  Removing the seed gate therefore leaves the axis
  free — the halt-zero checks alone do not catch a wrong `mem.axis`.
-/
import Nock.ComputeTable
import Nock.MemoryTable

namespace Nock
namespace Thm54
namespace StrengtheningScope

open Nock.ComputeTable

variable {K : Type*} [Field K]

/-! ## §1  The OP9 axis-operand pin -/

/-- The paper's **atom** predicate on a fingerprint triple, written `(z, 0, ⊥)`
    throughout: size `z = z^1` (one leaf) and an empty
    Dyck word.  `⊥` is the free leaf coordinate. -/
def AtomShape (z : K) (x : FP K) : Prop := x.size = z ∧ x.dyck = 0

/-- `FP.atomFP` — the fingerprint of an atom — has atom shape.  (`Def:ion_univariate`,
    the paper: `fn(n;r) = (r^{|dt|}, F_d(r), F_w(r))`, so `|dt| = 1` gives
    `(z, ·, 0)`.) -/
theorem atomFP_atomShape (z v : K) : AtomShape z (FP.atomFP z v) := ⟨rfl, rfl⟩

/-- **Licensed site A.**  In-tree it rides in `memBlk.s0` (decl `ComputeTable.lean:560`).  This is the exact
    structural analogue of the OP9 pin: the paper equates the `𝔽`-typed
    `mem_axis_2` with the noun `formula_tail`, and the paper renders that as
    `mem_axis_2 = f_t.leaf` — a rendering that is only faithful when `f_t` is an atom. -/
theorem op0_ft_atomShape {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hst : pub.state = .s0) (h : memBlk inp pub dec) : AtomShape inp.z dec.f_t := by
  simp only [memBlk, hst] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

/-- **Licensed site B.**  The memory table's `halt` state pins `pt.noun` to atom shape:
    `tab:v_mem` the paper, Algorithm `Memspec` the paper.  Same predicate. -/
theorem memHalt_noun_atomShape {inp : MemoryTable.Inputs K} {p : MemoryTable.Pub K}
    (hst : p.st = .halt) (h : MemoryTable.eqBlk inp p) : AtomShape inp.z p.pt.noun := by
  simp only [MemoryTable.eqBlk, hst] at h
  exact ⟨h.1, h.2.1⟩

/-- **The strengthening itself**, as a projection: the shipped `Vcomp` pins `f_th` to the
    same atom shape at OP9.  (Twin of `ComputeTable.Vcomp.s9_axis_atom_shape`,
    `ComputeTable.lean:672`, restated against `AtomShape` so §1 compares like with like.) -/
theorem op9_fth_atomShape {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hst : pub.state = .s9) (h : Vcomp inp pub dec) : AtomShape inp.z dec.f_th := by
  obtain ⟨_, _, _, _, heval⟩ := h
  simp only [evalV, hst] at heval
  exact ⟨heval.2.2.2.2.2.1, heval.2.2.2.2.2.2⟩

/-! ### 1.1  Completeness: the pin is free on any honest OP9 row

    Nock `OP_9` reduces as `*[n₁,[9,n₂]] → *[*[n₁,tail(n₂)], 2, [[0,1],0,head(n₂)]]`, so `head(n₂) = formula_tail_head` occupies the axis slot of an
    inlined `0 head(n₂)`; on any run that Nock does not crash on it is an atom.  Hence
    an honest generator that sets `f_th := fn(atom; z)` discharges the pin definitionally
    — removing the gate buys the honest prover nothing. -/
theorem op9_pin_free_on_atom_axis {z : K} {dec : Dec K} {v : K}
    (h : dec.f_th = FP.atomFP z v) : AtomShape z dec.f_th := by
  rw [h]; exact atomFP_atomShape z v

/-! ### 1.2  Non-derivability: the pin is not implied by the rest of `V_comp` at OP9

    `evalV9NoPin` / `VcompNoOp9Pin` are **copies under new names** of `ComputeTable.evalV`
    / `ComputeTable.Vcomp` with the two OP9 conjuncts deleted and every other opcode
    branch left untouched.  Nothing shipped is modified. -/

/-- `ComputeTable.evalV` with the OP9 atom pin deleted; all other branches verbatim. -/
def evalV9NoPin (inp : Inputs K) (pub : Pub K) (dec : Dec K) : Prop :=
  match pub.state with
  | .s9 => pub.sf1_s = pub.s ∧ pub.sf1_f = dec.f_tt ∧ pub.sf2_s = pub.sf1_e
        ∧ pub.e = pub.sf2_e ∧ sfz3 pub
  | _ => evalV inp pub dec

/-- `ComputeTable.Vcomp` with the OP9 atom pin deleted. -/
def VcompNoOp9Pin (inp : Inputs K) (pub : Pub K) (dec : Dec K) : Prop :=
  pub.f = FP.cons inp.z dec.f_h dec.f_t
    ∧ pub.mr1 = ⟨pub.f, dec.f_t, 3, pub.ln_prev * inp.α⟩
    ∧ SVhead inp pub dec
    ∧ memBlk inp pub dec
    ∧ evalV9NoPin inp pub dec

/-- Deleting the pin is a real weakening: the shipped `Vcomp` implies the pin-free copy,
    and (next theorem) the converse fails. -/
theorem Vcomp_le_VcompNoOp9Pin {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (h : Vcomp inp pub dec) : VcompNoOp9Pin inp pub dec := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, ?_⟩
  unfold evalV9NoPin
  split
  · next hst =>
      simp only [evalV, hst] at h5
      exact ⟨h5.1, h5.2.1, h5.2.2.1, h5.2.2.2.1, h5.2.2.2.2.1⟩
  · exact h5

/-! The witness, as named definitions so every verifier conjunct reduces by `rfl`. -/

/-- Witness inputs: `(α, z, a, b, c)` with the three OP5 coins unused. -/
def wInp (z α : K) : Inputs K := ⟨α, z, 0, 0, 0⟩

/-- Witness `formula_tail_head`: a genuine **cell**, `[1 2]`. -/
def wFth (z : K) : FP K := FP.cons z (FP.atomFP z 1) (FP.atomFP z 2)

/-- Witness `formula_tail_tail`. -/
def wFtt (z : K) : FP K := FP.atomFP z 7

/-- Witness `formula_tail` — the `cons` decomposition `memBlk.s9` demands. -/
def wFt (z : K) : FP K := FP.cons z (wFth z) (wFtt z)

/-- Witness `formula_head`: the atom `9`, as `SVhead` demands. -/
def wFh (z : K) : FP K := FP.atomFP z 9

/-- Witness `input_formula = cons(f_h, f_t)`. -/
def wF (z : K) : FP K := FP.cons z (wFh z) (wFt z)

/-- Witness decomposition columns. -/
def wDec (z : K) : Dec K := ⟨wFh z, wFt z, wFth z, wFtt z, 0, 0⟩

/-- Witness row, in state `.s9`. -/
def wPub (z α : K) : Pub K :=
  { state := .s9
    s := 0, f := wF z, e := 0
    sf1_s := 0, sf1_f := wFtt z, sf1_e := 0
    sf2_s := 0, sf2_f := 0, sf2_e := 0
    sf3_s := 0, sf3_f := 0, sf3_e := 0
    ln_prev := 1, ln := 1 * α ^ 3
    mr1 := ⟨wF z, wFt z, 3, 1 * α⟩
    mr2 := ⟨wFt z, wFth z, 2, 1 * α ^ 2⟩
    mr3 := ⟨0, 0, (wFth z).leaf, 1 * α ^ 3⟩ }

/-- The witness `f_th` is a cell: its Dyck coordinate is `z ≠ 0`.  (`FP.cons`'s `Φ₃`
    identity at two atoms: `z·0 + z·z·z⁻¹ + z·z·0 = z`.) -/
theorem wFth_dyck {z : K} (hz : z ≠ 0) : (wFth z).dyck = z := by
  simp only [wFth, FP.cons, FP.atomFP, mul_zero, zero_add, add_zero]
  field_simp

/-- **The pin is not derivable from the rest of `V_comp` at OP9.**  Explicit witness: a
    row in state `.s9` whose `formula_tail_head` is a genuine *cell* fingerprint
    (`f_th = cons(atom 1, atom 2)`, so `f_th.dyck = z ≠ 0`), satisfying every other
    conjunct of the verifier — the `cons` decomposition, the three memory records with
    `mem_axis_3 = f_th.leaf`, the `ln` recurrence,
    the SV head-atom block and the whole OP9 evaluation block.

    Consequence for the scoping question "is a shape condition on `f_th` derivable from
    `V_comp`'s three OP9 clauses plus the NPR typing?": **no**, not algebraically.  If
    the pin is wanted it has to be asserted; the only alternative licence is the typing
    of `mem_axis_3 ∈ 𝔽` against the paper's
    `mem_axis_3 = formula_tail_head`. -/
theorem op9_pin_not_derivable {z α : K} (hz : z ≠ 0) :
    ∃ (inp : Inputs K) (pub : Pub K) (dec : Dec K),
      pub.state = .s9 ∧ VcompNoOp9Pin inp pub dec ∧ ¬ AtomShape inp.z dec.f_th := by
  refine ⟨wInp z α, wPub z α, wDec z, rfl, ⟨rfl, rfl, ?_, ?_, ?_⟩, ?_⟩
  · -- SVhead: the head is the atom `9`
    exact ⟨rfl, rfl, rfl⟩
  · -- memBlk at `.s9`: mr2, the `cons` decomposition, mr3 with `mem_axis_3 = f_th.leaf`,
    -- and `ln = ln_prev · α³`
    exact ⟨rfl, rfl, rfl, rfl⟩
  · -- the OP9 evaluation block, pin deleted
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- but `f_th` is a cell: its Dyck coordinate is `z ≠ 0`
    rintro ⟨-, hd⟩
    exact hz (by rw [← wFth_dyck (z := z) hz]; exact hd)

/-! ## §2  The memory axis-accumulator seed boundary

    Setting: three rows of the memory walk, linked as the paper's walk links them — the child *cell* recorded in
    one row is the parent *cell* of the row that resolves it.

      rRoot : read_root   — serves the record, root = parent
        └ rDec : decompose — the noun splits
            ├ (left)  a `halt` leaf, accumulators `0`
            └ rVC : verify_child — removes `axis·timestamp`
                └ a `halt` leaf, accumulators `0`

    The record's child sits at the right child of the root of the walked noun, so its
    true axis is `2·1 + 1 = 3`. -/

open MemoryTable in
/-- **The halt-zero checks alone do not pin the axis; the seed value does.**

    Under every row-local `eqBlk`, the two walk
    edges, and both `halt` leaves zero, the walk root's
    `axis_counts` satisfies `2 · counts_root = (axis − 3) · timestamp`.  Hence:

    Halt-zero leaves therefore give

    * `axis_indicator` at the root `ts · (1 − axis)`
    * `axis_counts` at the root `ts · (2 − axis)`

    Relaxis recovery from the priced form-R event is the remaining join
    `Batch558.cancellingTree_is_remaining_join`. -/
theorem seed_counts_pins_the_axis
    {inp : MemoryTable.Inputs K} {rRoot rDec rVC : MemoryTable.Pub K}
    (_h2 : (2 : K) ≠ 0)
    (hRootSt : rRoot.st = .read_root) (hRoot : MemoryTable.eqBlk inp rRoot)
    (hDecSt : rDec.st = .decompose) (hDec : MemoryTable.eqBlk inp rDec)
    (hVCSt : rVC.st = .verify_child) (hVC : MemoryTable.eqBlk inp rVC)
    (edge1 : rRoot.lc = rDec.pt) (edge2 : rDec.rc = rVC.pt)
    (haltL : rDec.lc.indicator = 0 ∧ rDec.lc.counts = 0)
    (haltV : rVC.lc.indicator = 0 ∧ rVC.lc.counts = 0)
    (hts : rVC.mem.ts = rRoot.mem.ts) (_ht : rRoot.mem.ts ≠ 0)
    (hlamR : rRoot.lambda? = some 1) (hlamD : rDec.lambda? = some 1)
    (hlamV : rVC.lambda? = some 1)
    (hC : rRoot.cprime? = none) :
    rRoot.pt.indicator = rRoot.mem.ts * (1 - rRoot.mem.axis)
      ∧ rRoot.pt.counts = rRoot.mem.ts * (2 - rRoot.mem.axis) := by
  simp only [MemoryTable.eqBlk, hRootSt] at hRoot
  simp only [MemoryTable.eqBlk, hDecSt] at hDec
  simp only [MemoryTable.eqBlk, hVCSt] at hVC
  obtain ⟨-, -, hRootInd, hRootCnt, -, -⟩ := hRoot
  obtain ⟨-, hDecInd, hDecCnt, -⟩ := hDec
  obtain ⟨-, -, hVCInd, hVCCnt, -, -⟩ := hVC
  set t : K := rRoot.mem.ts with hT
  have hlamV1 : rVC.lambda = 1 := by simp [MemoryTable.Pub.lambda, hlamV]
  have hscale : rVC.lambda ^ MemoryTable.pwScaleExp K = (1 : K) := by
    rw [hlamV1, one_pow]
  have hVCi : rVC.pt.indicator = t := by
    rw [hVCInd, haltV.1, hts, hscale, zero_add, one_mul]
  have hVCc : rVC.pt.counts = t := by
    rw [hVCCnt, haltV.2, hts, hscale, zero_add, one_mul]
  have hlamD1 : rDec.lambda = 1 := by simp [MemoryTable.Pub.lambda, hlamD]
  have hDi : rDec.pt.indicator = t := by
    rw [hDecInd, hlamD1, haltL.1, zero_add, edge2, hVCi, one_mul]
  have hDc : rDec.pt.counts = (2 : K) * t := by
    rw [hDecCnt, hlamD1, haltL.2, zero_add, edge2, hVCi, hVCc]
    ring
  have hlamR1 : rRoot.lambda = 1 := by simp [MemoryTable.Pub.lambda, hlamR]
  have hsc : rRoot.lambda ^ MemoryTable.pwScaleExp K = (1 : K) := by
    rw [hlamR1, one_pow]
  have hC1 : rRoot.cprime = 1 := by simp [MemoryTable.Pub.cprime, hC]
  have hRi : rRoot.pt.indicator = t * (1 - rRoot.mem.axis) := by
    rw [hRootInd, edge1, hDi, hsc, one_mul, hT]
    ring
  have hRc : rRoot.pt.counts = t * (2 - rRoot.mem.axis) := by
    rw [hRootCnt, edge1, hDc, hC1, hT]
    ring
  exact ⟨hRi, hRc⟩

open MemoryTable in
/-- The same three rows, read the other way: **every** `axis` is realizable once the
    seed gate is gone.  Given any `a`, `t ≠ 0`, and any noun fingerprints, there is an
    assignment of the three rows satisfying every row-local `eqBlk`, both walk edges and
    both `halt`-leaf zeros, whose recorded axis is `a`.  For `a ≠ 3` the walk root's
    `axis_counts` is then nonzero — and nothing but `memSeedCountsExpr` looks at it. -/
theorem wrong_axis_satisfies_every_rowlocal_constraint
    {inp : MemoryTable.Inputs K} (_h2 : (2 : K) ≠ 0) (a t : K)
    (nL nR : FP K) (hL : AtomShape inp.z nL) (hR : AtomShape inp.z nR) :
    ∃ rRoot rDec rVC rHL rHR : MemoryTable.Pub K,
      -- every row satisfies its own `V_mem` equality block
      rRoot.st = .read_root ∧ MemoryTable.eqBlk inp rRoot ∧
      rDec.st  = .decompose ∧ MemoryTable.eqBlk inp rDec ∧
      rVC.st   = .verify_child ∧ MemoryTable.eqBlk inp rVC ∧
      rHL.st   = .halt ∧ MemoryTable.eqBlk inp rHL ∧
      rHR.st   = .halt ∧ MemoryTable.eqBlk inp rHR ∧
      -- and the walk edges agree
      rRoot.lc = rDec.pt ∧ rDec.lc = rHL.pt ∧ rDec.rc = rVC.pt ∧ rVC.lc = rHR.pt ∧
      -- with the record's recorded axis freely chosen …
      rVC.mem.axis = a ∧ rVC.mem.ts = t ∧ rRoot.mem.ts = t ∧
      -- `C' = a⁻¹` (or `λ = 0` on decompose when `a = 0`) keeps counts `t`.
      rRoot.pt.counts = t := by
  by_cases ha : a = 0
  · subst ha
    refine
      ⟨{ st := .read_root
         pt := ⟨FP.cons inp.z nL nR, 0, t⟩
         lc := ⟨FP.cons inp.z nL nR, 0, t⟩
         rc := MemoryTable.Cell.zero
         lcSt := .read_root, rcSt := .halt
         mem := ⟨FP.cons inp.z nL nR, nR, 0, t⟩, ipre := 0, icur := 0, lambda? := some 1 },
       { st := .decompose
         pt := ⟨FP.cons inp.z nL nR, 0, t⟩
         lc := ⟨nL, 0, 0⟩
         rc := ⟨nR, t, t⟩
         lcSt := .halt, rcSt := .verify_child
         mem := MemRec.zero, ipre := 0, icur := 0
         lambda? := some 0 },
       { st := .verify_child
         pt := ⟨nR, t, t⟩
         lc := ⟨nR, 0, 0⟩
         rc := MemoryTable.Cell.zero
         lcSt := .verify_child, rcSt := .halt
         mem := ⟨FP.cons inp.z nL nR, nR, 0, t⟩, ipre := 0, icur := 0, lambda? := some 1 },
       { st := .halt, pt := ⟨nL, 0, 0⟩, lc := MemoryTable.Cell.zero,
         rc := MemoryTable.Cell.zero, lcSt := .halt, rcSt := .halt,
         mem := MemRec.zero, ipre := 0, icur := 0 },
       { st := .halt, pt := ⟨nR, 0, 0⟩, lc := MemoryTable.Cell.zero,
         rc := MemoryTable.Cell.zero, lcSt := .halt, rcSt := .halt,
         mem := MemRec.zero, ipre := 0, icur := 0 },
       rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_,
       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
      · simp [MemoryTable.Pub.lambda, one_pow]
      · simp [MemoryTable.Pub.cprime]
    · refine ⟨rfl, ?_, ?_, rfl⟩
      · simp [MemoryTable.Pub.lambda]
      · simp [MemoryTable.Pub.lambda]
    · refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
      · simp [MemoryTable.Pub.lambda, one_pow]
      · simp [MemoryTable.Pub.lambda, one_pow]
    · exact ⟨hL.1, hL.2, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨hR.1, hR.2, rfl, rfl, rfl, rfl, rfl⟩
  · refine
      ⟨{ st := .read_root
         pt := ⟨FP.cons inp.z nL nR, t * (1 - a), t⟩
         lc := ⟨FP.cons inp.z nL nR, t, (2 : K) * t⟩
         rc := MemoryTable.Cell.zero
         lcSt := .read_root, rcSt := .halt
         mem := ⟨FP.cons inp.z nL nR, nR, a, t⟩, ipre := 0, icur := 0
         cprime? := some a⁻¹, lambda? := some 1 },
       { st := .decompose
         pt := ⟨FP.cons inp.z nL nR, t, (2 : K) * t⟩
         lc := ⟨nL, 0, 0⟩
         rc := ⟨nR, t, t⟩
         lcSt := .halt, rcSt := .verify_child
         mem := MemRec.zero, ipre := 0, icur := 0, lambda? := some 1 },
       { st := .verify_child
         pt := ⟨nR, t, t⟩
         lc := ⟨nR, 0, 0⟩
         rc := MemoryTable.Cell.zero
         lcSt := .verify_child, rcSt := .halt
         mem := ⟨FP.cons inp.z nL nR, nR, a, t⟩, ipre := 0, icur := 0, lambda? := some 1 },
       { st := .halt, pt := ⟨nL, 0, 0⟩, lc := MemoryTable.Cell.zero,
         rc := MemoryTable.Cell.zero, lcSt := .halt, rcSt := .halt,
         mem := MemRec.zero, ipre := 0, icur := 0 },
       { st := .halt, pt := ⟨nR, 0, 0⟩, lc := MemoryTable.Cell.zero,
         rc := MemoryTable.Cell.zero, lcSt := .halt, rcSt := .halt,
         mem := MemRec.zero, ipre := 0, icur := 0 },
       rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_,
       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
      · simp [MemoryTable.Pub.lambda, one_pow]; ring
      · simp [MemoryTable.Pub.cprime]; field_simp [ha]; ring
    · refine ⟨rfl, ?_, ?_, rfl⟩
      · simp [MemoryTable.Pub.lambda]
      · simp [MemoryTable.Pub.lambda]; ring
    · refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
      · simp [MemoryTable.Pub.lambda, one_pow]
      · simp [MemoryTable.Pub.lambda, one_pow]
    · exact ⟨hL.1, hL.2, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨hR.1, hR.2, rfl, rfl, rfl, rfl, rfl⟩

end StrengtheningScope
end Thm54
end Nock

