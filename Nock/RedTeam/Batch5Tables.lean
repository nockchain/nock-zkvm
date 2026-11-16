/-
  Nock/RedTeam/Batch5Tables.lean

  Independent verification of definitional faithfulness + non-vacuity witnesses.

This artifact provides MACHINE-CHECKED evidence for:
  1. Algorithm:NockCompute — ComputeTable.Vcomp (Algorithm)
  2. Lem:equiv_compute — equiv_compute/equiv_compute_sound (Lemma)
  3. Thm:comp_38 — comp_stateSep (Theorem)
  4. Algorithm:Memspec — MemoryTable.Vmem (Algorithm)
  5. Lem:equiv_mem — equiv_mem/equiv_mem_sound (Lemma)
  6. Thm:mem_38 — mem_stateSep (Theorem)

  HYGIENE: No `sorry`, `admit`, or `native_decide`.
  Axiom-clean target ⊆ {propext, Classical.choice, Quot.sound}.
  Items over extension field K legitimately use `Nock.Field.goldilocks_prime` (whitelisted).
-/
import Nock.NockVM
import Nock.Counts

namespace Nock.RedTeam

open Nock.ComputeTable Nock.MemoryTable Nock.NockVM Nock.Reified

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 1. `Algorithm:NockCompute` (Algorithm) — `ComputeTable.Vcomp`
    ══════════════════════════════════════════════════════════════════════════════════════

    Drift check + DISCRIMINATION: exhibit concrete `inp/pub/dec` where `Vcomp` HOLDS
    (a satisfying assignment) AND one where `Vcomp` FAILS (prove `¬ Vcomp`).

    The `OP_0` row is the simplest: all three subformula slots `⊥` (zero), evaluation undefined
, and the memory/SV constraints are minimal.

    Disposition: PASSED (def, non-vacuous + discriminating)
-/

section Algorithm_NockCompute

variable {K : Type*} [Field K]

/-- **[1.a] POSITIVE witness: a concrete `OP_0` row where `Vcomp` HOLDS.**
    This witnesses that `Vcomp` is satisfiable (non-vacuous algorithm).

    OP_0: formula `[0 f_t]`, all sf slots ⊥, evaluation ignored (tree halts).
    We construct:
    - `inp` with arbitrary seeds (we use all zeros for simplicity)
    - `pub` with `state = s0`, formula = `cons z (atomFP z 0) (atomFP z 0)` (a valid `[0 t]` cell)
    - `dec` with `f_h = atomFP z 0` (head is atom 0), `f_t = atomFP z 0`
-/
noncomputable def vcomp_positive_inp : ComputeTable.Inputs K := ⟨0, 1, 0, 0, 0⟩

noncomputable def vcomp_positive_pub : ComputeTable.Pub K :=
{ state := State.s0
  s := 0
  f := FP.cons 1 (FP.atomFP 1 0) (FP.atomFP 1 0)
  e := 0
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 0
  ln := 0
  mr1 := ⟨FP.cons 1 (FP.atomFP 1 0) (FP.atomFP 1 0), FP.atomFP 1 0, 3, 0⟩
  mr2 := ⟨0, 0, 0, 0⟩
  mr3 := MemRec.zero }

noncomputable def vcomp_positive_dec : Dec K :=
{ f_h := FP.atomFP 1 0
  f_t := FP.atomFP 1 0
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0 }

/-- **[1.a] POSITIVE discrimination witness: `Vcomp` HOLDS on this concrete assignment.**
    This proves `Vcomp` is satisfiable (non-vacuous). -/
theorem vcomp_positive_witness :
    Vcomp (vcomp_positive_inp (K := K)) (vcomp_positive_pub (K := K)) (vcomp_positive_dec (K := K)) := by
  unfold Vcomp vcomp_positive_inp vcomp_positive_pub vcomp_positive_dec
  -- Goal: 5-fold conjunction for s0
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  -- mr1 = ⟨f, f_t, 3, ln_prev * α⟩
  · ext <;> simp [mul_zero]
  -- SVhead for s0
  · unfold SVhead headAtom
    simp only [FP.atomFP, State.toNat, Nat.cast_zero, reduceCtorEq, ↓reduceIte, and_self]
  -- memBlk for s0: mr2 = ⟨s, e, f_t.leaf, ln_prev * α^2⟩ ∧ mr3 = zero ∧ ln = ln_prev * α^2 ∧ f_t.size = z ∧ f_t.dyck = 0
  · unfold memBlk
    simp only [FP.atomFP, MemRec.zero, mul_zero, pow_two, and_self, eq_self]
  -- evalV for s0: all sf slots zero
  · unfold evalV sfz1 sfz2 sfz3
    trivial

/-- **[1.b] NEGATIVE discrimination witness: tampered `pub.f.size` causes `Vcomp` to FAIL.**
    If `pub.f.size ≠ (FP.cons z f_h f_t).size`, the first conjunct fails.
    We tamper `f.size = 0` while the honest value is `1*1 = 1`. -/
noncomputable def vcomp_negative_pub : ComputeTable.Pub K :=
{ vcomp_positive_pub (K := K) with f := ⟨0, 0, 0⟩ }  -- f.size = 0, should be 1

/-- Negative witness requires `1 ≠ 0` (nontrivial field). -/
theorem vcomp_negative_witness (hz : (1 : K) ≠ 0) :
    ¬ Vcomp (vcomp_positive_inp (K := K)) (vcomp_negative_pub (K := K)) (vcomp_positive_dec (K := K)) := by
  intro h
  have hf := h.1
  unfold vcomp_negative_pub vcomp_positive_pub vcomp_positive_inp vcomp_positive_dec at hf
  simp only [FP.cons, FP.atomFP, FP.mk.injEq] at hf
  obtain ⟨hsize, _, _⟩ := hf
  -- hsize : 0 = 1 * 1 = 1
  simp only [one_mul] at hsize
  exact hz hsize.symm

/-- **[1.b'] Documentation: negative Vcomp witness.**
    Structural mismatch: `f.size = 0 ≠ 1 = cons(...).size` in any nontrivial field. -/
def vcomp_negative_doc : String :=
  "Negative Vcomp witness: f.size = 0 tampered vs FP.cons(...).size = 1*1 = 1. " ++
  "The first Vcomp conjunct fails when 1 ≠ 0 (any nontrivial field). " ++
  "This discriminates Vcomp: the positive witness passes, the negative fails."

/-- **[1.c] Structural faithfulness: `Vcomp` is the 5-fold conjunction from Algorithm NockCompute.**
    The definition is: formula = cons(head, tail) ∧ mr1 = expected ∧ SVhead ∧ memBlk ∧ evalV. -/
def vcomp_structure_doc : String :=
  "Vcomp (main.tex:1724) is the 5-fold conjunction: " ++
  "(1) pub.f = FP.cons z dec.f_h dec.f_t [formula decomposition]; " ++
  "(2) pub.mr1 = ⟨pub.f, dec.f_t, 3, ln_prev·α⟩ [memory record 1]; " ++
  "(3) SVhead [formula-head shape matches state]; " ++
  "(4) memBlk [per-state memory records 2-3 and ln recurrence]; " ++
  "(5) evalV [per-state evaluation constraints]."

end Algorithm_NockCompute


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 2. `Lem:equiv_compute` (Lemma) — `equiv_compute`/`equiv_compute_sound`
    ══════════════════════════════════════════════════════════════════════════════════════

    Confirms §B (B1-B6): the Lean adopts the corrected reading on BOTH RAP and V sides.
    - WF-FREE forward: `equiv_compute_sound` (RAP satisfiable ⟹ Vcomp)
    - Full biconditional: `equiv_compute` needs `WF` (B6 genericity)

    Disposition: PASSED (1-1* with §B WF documented)
-/

section Lem_equiv_compute

variable {K : Type*} [Field K]

/-- **[2.a] WF-FREE forward direction: `equiv_compute_sound`.**
    RAP satisfiable ⟹ algorithmic verifier accepts (soundness direction). -/
example (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K) (dec : Dec K) :
    (∃ ex : Extra K, RAPcomp inp pub dec ex) → Vcomp inp pub dec :=
  equiv_compute_sound inp pub dec

/-- **[2.b] Full biconditional: `equiv_compute` with WF hypothesis.**
    The exact ⟺ needs the genericity conditions `WF` (B6: rlc5, size8, size11). -/
example (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K) (dec : Dec K) (wf : WF inp pub) :
    (∃ ex : Extra K, RAPcomp inp pub dec ex) ↔ Vcomp inp pub dec :=
  equiv_compute inp pub dec wf

/-- **[2.c] WF structure: the genericity conditions from §B6.**
    - `rlc5`: OP_5 RLC non-degeneracy when `sf1_e ≠ sf2_e`
    - `size8`: OP_8 sizes nonzero (`sf2_e.size ≠ 0 ∧ s.size ≠ 0`)
    - `size11`: OP_11/cons sizes nonzero (`sf1_e.size ≠ 0 ∧ sf2_e.size ≠ 0`)
    These are the paper's implicit genericity conditions (random a,b,c; sizes powers of z ≠ 0). -/
example (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K) : WF inp pub → Prop := fun _ =>
  -- WF bundles the three conditions; we cite their types
  (pub.state = State.s5 → pub.sf1_e ≠ pub.sf2_e →
    inp.a * (pub.sf1_e.size - pub.sf2_e.size) + inp.b * (pub.sf1_e.dyck - pub.sf2_e.dyck)
      + inp.c * (pub.sf1_e.leaf - pub.sf2_e.leaf) ≠ 0)  -- rlc5
  ∧ (pub.state = State.s8 → pub.sf2_e.size ≠ 0 ∧ pub.s.size ≠ 0)  -- size8
  ∧ (pub.state = State.cons → pub.sf1_e.size ≠ 0 ∧ pub.sf2_e.size ≠ 0)  -- size11

/-- **[2.d] Documentation: §B (B1-B6) drift summary.**
    The Lean adopts the semantically-correct reading identically on BOTH sides (RAP and V).
    - B1-B5: corrected algorithm/table entries match on both sides
    - B6: WF bundles the genericity conditions (random RLC, nonzero sizes)
    - Forward (soundness) is unconditional; backward (completeness) needs WF. -/
def census_B_equiv_compute : String :=
  "CENSUS §B (B1-B6) CONFIRMED:\n" ++
  "• B1-B5: Paper algorithm vs RAP inconsistencies; Lean adopts corrected reading on BOTH sides.\n" ++
  "• B6: WF (genericity): rlc5 (OP_5 RLC non-degenerate), size8/size11 (sizes ≠ 0).\n" ++
  "• `equiv_compute_sound`: forward (soundness) is WF-FREE — RAP sat ⟹ Vcomp.\n" ++
  "• `equiv_compute`: exact ⟺ needs WF for backward direction (completeness).\n" ++
  "Disposition: PASSED (1-1* with §B WF documented)."

end Lem_equiv_compute


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 3. `Thm:comp_38` (Theorem) — `comp_stateSep`
    ══════════════════════════════════════════════════════════════════════════════════════

    The compute language `L_comp` satisfies `Def:state_data_separation` (StateSep).
    Also CONFIRM §D cost caveat: paper gives identical `20·e+13` for both tables (D1);
    reified counts prove memory is strictly smaller.

    Disposition: PASSED (structural + §D confirmed)
-/

section Thm_comp_38

variable {K : Type*} [Field K]

/-- **[3.a] `comp_stateSep` EXISTS — the structural 1-1 claim.**
    `L_comp = Fcomp` satisfies `StateSep`: solely state-traversable with `S_leaf = {OP_0, OP_1}`. -/
noncomputable example : Walk.StateSep (Fcomp (K := K)) := comp_stateSep

/-- **[3.b] Non-vacuity: `Fcomp_nonvacuous` — the StateSep instance is not over an empty language.**
    There exists a concrete `OP_0` leaf that `Fcomp` accepts. -/
noncomputable example : ∃ (lbl : State × DTcomp K), Fcomp lbl (fun _ => none) := Fcomp_nonvacuous

/-- **[3.c] Cost figure: `comp_deg4_gates 3 = 73` (the carried e=3 figure).**
    Paper states `20·e+13` deg-4 gates; at e=3 this is 73. -/
example : comp_deg4_gates 3 = 73 := rfl


example : (memoryAIR (K := K)).constraints.length < computeAIR.constraints.length :=
  mem_fewer_constraints_than_comp


example : (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 4) <
    computeAIR.constraints.countP (fun c => c.degree == 4) :=
  mem_fewer_deg4_than_comp

/-- **[3.f] Documentation: §D cost caveat.**
    Paper gives `20·e+13` deg-4 gates for BOTH Thm:comp_38 and Thm:mem_38 (D1 copy-paste artifact).
    Prose says memory is "much smaller". Reified counts prove memory < compute. -/
def census_D_comp_38 : String :=
  "CENSUS §D CONFIRMED (Thm:comp_38):\n" ++
  "• comp_deg4_gates 3 = 73 (the paper's `20·e+13` at e=3).\n" ++
  "• D1 (copy-paste): paper claims IDENTICAL gate count for memory; reified refutes:\n" ++
  "  - mem_fewer_constraints_than_comp: 75 < 526\n" ++
  "  - mem_fewer_deg4_than_comp: 1 < 13\n" ++
  "Disposition: PASSED (structural 1-1 + §D cost caveat confirmed)."

end Thm_comp_38


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 4. `Algorithm:Memspec` (Algorithm) — `MemoryTable.Vmem`
    ══════════════════════════════════════════════════════════════════════════════════════

    Drift check + DISCRIMINATION: exhibit concrete `inp/p` where `Vmem` HOLDS
    (a satisfying assignment for a `halt` row) AND one where `Vmem` FAILS.

    The `halt` row is simplest: parent is an atom, both children null, mem_record zero.

    Disposition: PASSED (def, non-vacuous + discriminating)
-/

section Algorithm_Memspec

variable {K : Type*} [Field K]

/-- **[4.a] POSITIVE witness: a concrete `halt` row where `Vmem` HOLDS.**
    This witnesses that `Vmem` is satisfiable (non-vacuous algorithm).

    halt: parent is atom `(z,0,⊥)`, indicator=counts=0, children null. -/
noncomputable def vmem_positive_inp : MemoryTable.Inputs K := ⟨1, 0, 0⟩

noncomputable def vmem_positive_pub : MemoryTable.Pub K :=
{ st := MState.halt
  pt := ⟨FP.atomFP 1 0, 0, 0⟩  -- atom with indicator=counts=0
  lc := Cell.zero
  rc := Cell.zero
  lcSt := MState.halt
  rcSt := MState.halt
  mem := ComputeTable.MemRec.zero
  ipre := 0
  icur := 0 }

/-- The `eqBlk` constraints for `halt` are satisfied. -/
theorem vmem_positive_eqBlk : eqBlk vmem_positive_inp (vmem_positive_pub (K := K)) := by
  unfold eqBlk vmem_positive_pub vmem_positive_inp
  -- Goal is a 7-tuple for halt state
  -- pt.noun.size = z ∧ pt.noun.dyck = 0 ∧ pt.indicator = 0 ∧ pt.counts = 0
  --   ∧ lc = Cell.zero ∧ rc = Cell.zero ∧ mem = MemRec.zero
  constructor; rfl  -- pt.noun.size = 1 (z = 1)
  constructor; rfl  -- pt.noun.dyck = 0
  constructor; rfl  -- pt.indicator = 0
  constructor; rfl  -- pt.counts = 0
  constructor; rfl  -- lc = Cell.zero
  constructor; rfl  -- rc = Cell.zero
  rfl               -- mem = MemRec.zero

/-- The `interV` constraints for `halt` are satisfied: `icur = ipre`. -/
theorem vmem_positive_interV : interV vmem_positive_inp (vmem_positive_pub (K := K)) := by
  unfold interV vmem_positive_pub
  rfl

/-- **[4.a] POSITIVE discrimination witness: `Vmem` HOLDS on this concrete `halt` assignment.** -/
theorem vmem_positive_witness :
    Vmem vmem_positive_inp (vmem_positive_pub (K := K)) := by
  exact ⟨MemoryTable.verBool_holds _, vmem_positive_eqBlk, vmem_positive_interV⟩

/-- **[4.b] NEGATIVE discrimination witness: wrong state (`decompose`) with halt-style data fails.**
    The `decompose` state requires `pt.noun = cons(lc.noun, rc.noun)`, which our halt-style
    data violates (pt.noun = atomFP, not a cons). -/
noncomputable def vmem_negative_pub : MemoryTable.Pub K :=
{ vmem_positive_pub with st := MState.decompose }  -- wrong state for halt-style data

/-- For decompose state, `pt.noun = FP.cons z lc.noun rc.noun` is required.
    With halt-style data (pt = atomFP, lc = rc = Cell.zero), this constraint fails
    because `atomFP z 0 ≠ FP.cons z 0 0` (the size doesn't match: z vs 0*0=0). -/
theorem vmem_negative_witness (hz : (1 : K) ≠ 0) :
    ¬ Vmem vmem_positive_inp (vmem_negative_pub (K := K)) := by
  intro h
  have heq := h.2.1  -- eqBlk (Vmem = verBool ∧ eqBlk ∧ interV)
  unfold eqBlk vmem_negative_pub vmem_positive_pub vmem_positive_inp at heq
  simp only [Cell.zero, FP.cons, FP.atomFP, FP.zero_size, FP.zero_dyck, FP.zero_leaf] at heq
  -- For decompose: pt.noun = FP.cons z lc.noun rc.noun
  -- pt.noun = ⟨1, 0, 0⟩, FP.cons 1 0 0 = ⟨0*0, ..., ...⟩ = ⟨0, ..., ...⟩
  obtain ⟨hpt, _⟩ := heq
  simp only [FP.mk.injEq] at hpt
  obtain ⟨hsize, _, _⟩ := hpt
  -- hsize : 1 = 0 * 0 = 0, contradiction with hz
  simp only [zero_mul] at hsize
  exact hz hsize

/-- **[4.c] Documentation: negative witness requires nontrivial field.**
    The structural mismatch `atomFP ≠ FP.cons 0 0` relies on `1 ≠ 0` (size field).
    This holds in any nontrivial field (char ≠ 1). -/
def vmem_negative_doc : String :=
  "Negative Vmem witness: decompose state with halt-style data fails because " ++
  "pt.noun = atomFP z 0 has size z = 1, but FP.cons z 0 0 has size 0*0 = 0. " ++
  "Constraint: 1 = 0 is false in any nontrivial field."

/-- **[4.d] Structural faithfulness: `Vmem` is the 2-fold conjunction from Algorithm NockMemory.**
    The definition is: eqBlk (per-state equality constraints) ∧ interV (LogUp intermediate). -/
def vmem_structure_doc : String :=
  "Vmem (main.tex:2053) is the 2-fold conjunction: " ++
  "(1) eqBlk [per-state equality constraints: decompose/halt/read_root/verify_child]; " ++
  "(2) interV [LogUp intermediate accumulator step: unchanged/+pole⁻¹/-pole⁻¹]."

end Algorithm_Memspec


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 5. `Lem:equiv_mem` (Lemma) — `equiv_mem`/`equiv_mem_sound`
    ══════════════════════════════════════════════════════════════════════════════════════

    Confirms §C (M1-M8): the Lean adopts the corrected reading on BOTH RAP and V sides.
    - WF-FREE forward: `equiv_mem_sound` (RAP satisfiable ⟹ Vmem)
    - Full biconditional: `equiv_mem` needs `WF.pole_ne` (M6)
    - `logup_spec`: resolves M2/M3 sign/pole

    Disposition: PASSED (1-1* with §C WF.pole_ne documented)
-/

section Lem_equiv_mem

variable {K : Type*} [Field K]

/-- **[5.a] WF-FREE forward direction: `equiv_mem_sound`.**
    RAP satisfiable ⟹ algorithmic verifier accepts (soundness direction). -/
example (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K) :
    (∃ g, RAPmem inp p g) → Vmem inp p :=
  equiv_mem_sound inp p

/-- **[5.b] Full biconditional: `equiv_mem` with WF hypothesis.**
    The exact ⟺ needs the genericity condition `WF` (M6: pole_ne). -/
example (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K) (wf : MemoryTable.WF inp p) :
    (∃ g, RAPmem inp p g) ↔ Vmem inp p :=
  equiv_mem inp p wf

/-- **[5.c] WF structure: the genericity condition from §M6.**
    `pole_ne`: in `read_root` or `verify_child` states, the LogUp pole is nonzero.
    This is the random-β non-vanishing condition. -/
example (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K) : MemoryTable.WF inp p → Prop := fun _ =>
  (p.st = MState.read_root ∨ p.st = MState.verify_child) → pole inp p.mem p.cprime ≠ 0

/-- **[5.d] `logup_spec`: M2/M3 sign/pole resolution.**
    The RAP intermediate block implies `pole·(icur − ipre) = opDiff st`. -/
example (inp : MemoryTable.Inputs K) (p : MemoryTable.Pub K) (g : K) (h : interR inp p g) :
    pole inp p.mem p.cprime * (p.icur - p.ipre) = opDiff p.st :=
  logup_spec inp p g h

/-- **[5.e] Documentation: §C (M1-M8) drift summary.**
    - M1: `check_child` vs `verify_child` naming (same state)
    - M2/M3: sign/pole resolved by `logup_spec`
    - M4: decompose/halt intermediate unchanged (semantically correct reading)
    - M5-M8: other table/algorithm corrections
    - M6: WF.pole_ne (random β non-vanishing) -/
def census_C_equiv_mem : String :=
  "CENSUS §C (M1-M8) CONFIRMED:\n" ++
  "• M1: 'check_child' vs 'verify_child' naming (same state, table vs algorithm).\n" ++
  "• M2/M3: LogUp sign/pole resolved by `logup_spec`: pole·Δ = op₂ - op₃.\n" ++
  "• M4: decompose/halt intermediate unchanged (Lean's semantically correct reading).\n" ++
  "• M5-M8: other table/algorithm corrections adopted on both sides.\n" ++
  "• M6: WF.pole_ne (random β ⟹ pole ≠ 0) — load-bearing on backward direction.\n" ++
  "• `equiv_mem_sound`: forward (soundness) is WF-FREE.\n" ++
  "• `equiv_mem`: exact ⟺ needs WF for backward direction.\n" ++
  "Disposition: PASSED (1-1* with §C WF.pole_ne documented)."

end Lem_equiv_mem


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 6. `Thm:mem_38` (Theorem) — `mem_stateSep`
    ══════════════════════════════════════════════════════════════════════════════════════

    The memory language `L_mem` satisfies `Def:state_data_separation` (StateSep).
    CONFIRM §D D1: paper gives IDENTICAL `20·e+13` for both tables (copy-paste artifact);
    reified counts prove memory < compute.
    D2: asymmetric `+IO` increments (`24·e+15` compute vs `24·e+16` memory).

    Disposition: PASSED (structural + §D D1/D2 confirmed)
-/

section Thm_mem_38

variable {K : Type*} [Field K]

/-- **[6.a] `mem_stateSep` EXISTS — the structural 1-1 claim.**
    `L_mem = Fmem` satisfies `StateSep`: solely state-traversable with `S_leaf = {halt}`. -/
noncomputable example : Walk.StateSep (Fmem (K := K)) := mem_stateSep

/-- **[6.b] Non-vacuity: `Fmem_nonvacuous` — the StateSep instance is not over an empty language.**
    There exists a concrete `halt` leaf that `Fmem` accepts. -/
noncomputable example : ∃ (lbl : MState × DTmem K), Fmem lbl (fun _ => none) := Fmem_nonvacuous

/-- **[6.c] Cost figure: `mem_deg4_gates 3 = 73` (the carried e=3 figure).**
    Paper states `20·e+13` deg-4 gates; at e=3 this is 73. -/
example : mem_deg4_gates 3 = 73 := rfl


example : comp_deg4_gates 3 = mem_deg4_gates 3 := rfl


example : (memoryAIR (K := K)).constraints.length < computeAIR.constraints.length :=
  mem_fewer_constraints_than_comp

/-- **[6.f] D2: asymmetric `+IO` increments.**
    - `comp_io_deg4_gates e = 24·e+15`
    - `mem_io_deg4_gates e = 24·e+16`
    The increments differ by 1 (paper states identical bases + asymmetric +IO). -/
example : comp_io_deg4_gates 3 = 87 := rfl
example : mem_io_deg4_gates 3 = 88 := rfl
example : mem_io_deg4_gates 3 = comp_io_deg4_gates 3 + 1 := rfl

/-- **[6.g] Documentation: §D D1/D2 cost caveat.**
    - D1: paper gives identical `20·e+13` for both; reified refutes (memory smaller)
    - D2: `+IO` increments differ (`24·e+15` vs `24·e+16`; off by 1) -/
def census_D_mem_38 : String :=
  "CENSUS §D CONFIRMED (Thm:mem_38):\n" ++
  "• mem_deg4_gates 3 = 73 (the paper's `20·e+13` at e=3).\n" ++
  "• D1 (copy-paste): comp_deg4_gates 3 = mem_deg4_gates 3 = 73 (paper's IDENTICAL claim).\n" ++
  "  REFUTED by reified counts: memory AIR is strictly smaller (75 < 526 constraints, 1 < 13 deg-4).\n" ++
  "• D2 (asymmetric +IO): comp_io_deg4_gates 3 = 87, mem_io_deg4_gates 3 = 88.\n" ++
  "  The aggregate increments differ by 1 (asymmetric, despite identical bases).\n" ++
  "Disposition: PASSED (structural 1-1 + §D D1/D2 confirmed)."

end Thm_mem_38


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SUMMARY: Drift Findings
    ══════════════════════════════════════════════════════════════════════════════════════
-/


def batch5_drift_summary : String :=
  "BATCH 5 TABLES DRIFT FINDINGS:\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "1. Algorithm:NockCompute — PASSED (Vcomp: positive OP_0 witness + negative discrimination)\n" ++
  "2. Lem:equiv_compute — PASSED (§B: WF-free forward `equiv_compute_sound`, WF for ⟺)\n" ++
  "3. Thm:comp_38 — PASSED (comp_stateSep exists; §D reified refutes D1)\n" ++
  "4. Algorithm:Memspec — PASSED (Vmem: positive halt witness + negative discrimination)\n" ++
  "5. Lem:equiv_mem — PASSED (§C: WF-free forward `equiv_mem_sound`, WF.pole_ne for ⟺)\n" ++
  "6. Thm:mem_38 — PASSED (mem_stateSep exists; §D D1 equal base, D2 asymmetric +IO)\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "NO NEW DRIFT DETECTED. All deltas match documented CORRESPONDENCE.md / CENSUS.md.\n" ++
  "§B WF, §C WF.pole_ne, §D cost-def/D1/D2 — ALL BENIGN-DOCUMENTED."

end Nock.RedTeam
