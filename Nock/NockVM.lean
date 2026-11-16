/-
  Nock/NockVM.lean

  The capstone of the NockVM construction.  It assembles the compilation results of the paper §5:

    * `Thm:comp_38`: the compute language `L_comp` satisfies
      `Def:state_data_separation` (`Walk.StateSep`).
    * `Thm:mem_38`: the memory language `L_mem` satisfies
      `Def:state_data_separation`.
    * `V_NockVMROM`: the **conjunction** of the two chips' walk soundness (`Walk_IOP_final`
      for the execution and memory walks, with the `ε_RLC` bound) and the IO-linking
      biconditional (`io_result`).

  In `V_NockVMROM`:

    (A) *Shared IO witness.*  The IO conjunct is fed `reqRecs lblc hc` / `respRecs lblm hm` —
        the compute walk's *emitted* memory-request records and the memory walk's *served*
        records, both literal functions of the SAME `lblc`/`lblm` the two walk-soundness
        conjuncts range over (via `encRec`).
    (B) *RAP→verifier bridges.*  The per-row hypotheses are stated at the RAP-satisfiability
        level; the proof derives the `Fcomp`/`Fmem` labelling facts internally through
        `equiv_compute_sound` / `equiv_mem_sound`.

  What `V_NockVMROM` *proves* (conjuncts 1/2): each chip's walk-soundness `≤ h/|K| + ε_RLC`.
  What it *certifies* (conjunct 3): the biconditional
  `(reqRecs, respRecs) ∈ L_IO ⟺ jointly IO-RAP-satisfiable` (`Thm:IO_result`); the request-
  set = response-set equality is what the IO check certifies, not something proved here.  What it
  *assumes*: the unique-request/response + range side conditions (as in `cor_uni_req_uni_resp`).
  No conjunct is weakened, `+ ε_RLC` is retained, and `WF` is not assumed.

  `NockVMROM` is the **bundle corollary**: it is `V_NockVMROM` with the IO conjunct at fresh
  `req/resp` and the per-row hypotheses given directly at the `Fcomp`/`Fmem` level.  It bundles
  three facts over *unrelated* inputs; the witness-sharing and bridge-descent live only in
  `V_NockVMROM`.

  Everything is proved without `sorry`.  Numeric cost/security figures (columns, gates,
  bit-security) are documented `def`s.  The development is generic over an arbitrary finite
  field `K` and introduces no axioms; `Field.goldilocks_prime` is used only by the concrete
  Goldilocks instantiation of the security figures.

  Layer references:
    Nock.ComputeTable  `RAPcomp`/`Vcomp`, `equiv_compute`  (App B.1)
    Nock.MemoryTable   `RAPmem`/`Vmem`, `equiv_mem`        (App B.2)
    Nock.Walk          `StateSep`, `BFSValid`, `Walk_IOP_final_*`, `Corr:forest`
    Nock.IO            `io_result` / `io_result_LIO`        (Thm:IO_result)
    Nock.NPR           collision bound                      (lem:ion_univariate_sec)
    Nock.Field         Goldilocks 𝔽 + cubic extension K
-/

import Nock.ComputeTable
import Nock.MemoryTable
import Nock.Walk
import Nock.IO
import Nock.NPR
import Nock.Field

open scoped Classical

namespace Nock

/-! # `WF`-free forward (soundness-direction) lemmas

  The soundness composition needs the *forward* direction of
  `Lem:equiv_compute` / `Lem:equiv_mem` — `RAP satisfiable ⟹ verifier accepts` — which does
  **not** require the genericity hypothesis `WF` (that is needed only for the *backward*
  direction, i.e. completeness of the RAP).  The two forward lemmas are stated here. -/

namespace ComputeTable

variable {K : Type*} [Field K]

/-- **Opcode-5 gate, forward only** (no `WF`).  The `.mp` direction of `gate5` does not use the RLC-nondegeneracy hypothesis `hnd`: a satisfying
    assignment of the five gates forces `ev = ⟦(d1,d2,d3) ≠ 0⟧` unconditionally. -/
theorem gate5_mp {F : Type*} [Field F] (a b c d1 d2 d3 ev : F)
    (h : ev * (1 - ev) = 0 ∧ (1 - ev) * d1 = 0 ∧ (1 - ev) * d2 = 0 ∧ (1 - ev) * d3 = 0 ∧
        ∃ w : F, w * (a * d1 + b * d2 + c * d3 + (1 - ev)) = 1) :
    ev = (if (d1 = 0 ∧ d2 = 0 ∧ d3 = 0) then 0 else 1) := by
  obtain ⟨hb, h1, h2, h3, w, h5⟩ := h
  by_cases heq : d1 = 0 ∧ d2 = 0 ∧ d3 = 0
  · rw [if_pos heq]
    obtain ⟨e1, e2, e3⟩ := heq
    rcases mul_eq_zero.mp hb with hh | hh
    · exact hh
    · exfalso
      have hev : ev = 1 := by linear_combination -hh
      rw [hev, e1, e2, e3] at h5; simp at h5
  · rw [if_neg heq]
    rcases mul_eq_zero.mp hb with hh | hh
    · exfalso; subst hh
      simp only [sub_zero, one_mul] at h1 h2 h3
      exact heq ⟨h1, h2, h3⟩
    · linear_combination -hh

/-- **Evaluation block, forward (`WF`-free).**  If the RAP evaluation block `evalR` is
    satisfiable (for some inverse witness `g`), the algorithmic verifier's evaluation block
    `evalV` accepts.  This is the soundness direction of `eval_iff`; unlike the biconditional
    it needs **no** `WF` (the gate forward directions `gate3`/`gate5_mp`/`gate_prod` do not use
    the genericity conditions). -/
theorem eval_sound (inp : Inputs K) (pub : Pub K) (dec : Dec K) (g : K)
    (hg : evalR inp pub dec g) : evalV inp pub dec := by
  cases hst : pub.state <;> simp only [evalR, hst] at hg <;> simp only [evalV, hst]
  -- non-gate opcodes: evalR = evalV
  case s0 => exact hg
  case s1 => exact hg
  case s2 => exact hg
  case s4 => exact hg
  case s7 => exact hg
  case s9 => exact hg
  -- OP_3: gate3 forward + qm bridge
  case s3 =>
    obtain ⟨h1, h2, h3, h4, h5, h6, hb, hg1, hg2, hg3⟩ := hg
    refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
    rw [← qm_eq]
    exact (gate3 (inp.z - pub.sf1_e.size) pub.e.leaf).mp ⟨hb, g, hg1, hg2, hg3⟩
  -- OP_5: gate5 forward (no hnd) + eqOp bridge
  case s5 =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, hb, hd1, hd2, hd3, hg5⟩ := hg
    refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩
    rw [← eqOp_eq]
    exact gate5_mp inp.a inp.b inp.c _ _ _ pub.e.leaf ⟨hb, hd1, hd2, hd3, g, hg5⟩
  -- OP_6: branch selection under booleanity
  case s6 =>
    obtain ⟨h1, hf, h3, h4, h5, h6, h7, hbool, hsfz⟩ := hg
    have hsel := (bool_iff pub.sf2_e.leaf).mp hbool
    exact ⟨h1, by rw [hf]; exact FP_branch_eq _ _ _ hsel, h3, h4, h5, h6, h7, hsel, hsfz⟩
  -- OP_8 / cons: drop the inverse witness
  case s8 =>
    obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hg
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  case cons =>
    obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hg
    exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **`Lem:equiv_compute`, forward direction (`WF`-free)** — the soundness half.  A satisfying
    assignment of the compute RAP `RAP_comp` (over the auxiliary columns) implies the
    algorithmic verifier `V_comp` accepts.  This is the
    prerequisite the soundness composition feeds on; it does **not** assume `WF`. -/
theorem equiv_compute_sound (inp : Inputs K) (pub : Pub K) (dec : Dec K) :
    (∃ ex : Extra K, RAPcomp inp pub dec ex) → Vcomp inp pub dec := by
  rintro ⟨ex, hal, hmr1, hsv, hmem, hev⟩
  exact ⟨hal, hmr1, (SV_head_iff inp pub dec).mp ⟨ex.consInv, hsv⟩, hmem,
    eval_sound inp pub dec ex.invGen hev⟩

/-! ## `Thm:comp_38`: `L_comp` satisfies `Def:state_data_separation` -/

open Walk

/-- Per-opcode **fanout** — the number of recursive `*`-children: `OP_2 ↦ 3`, `OP_5..OP_9,cons ↦ 2`,
    `OP_3/OP_4 ↦ 1`, `OP_0/OP_1 ↦ 0` (terminal).  Max is `3`, so the arity is `n = 3`. -/
def fanoutComp : State → ℕ
  | .s0 => 0 | .s1 => 0 | .s2 => 3 | .s3 => 1 | .s4 => 1 | .s5 => 2
  | .s6 => 2 | .s7 => 2 | .s8 => 2 | .s9 => 2 | .cons => 2

/-- The data field `𝒟𝒯_comp` of a compute label: the RAP inputs and the row's public+witness
    columns (fingerprints).  The state is carried separately as the `S` component. -/
abbrev DTcomp (K : Type*) := Inputs K × Pub K × Dec K

/-- Opcode tag as a field element. -/
def stateTagField (st : State) : K :=
  match st with
  | .s0 => 0 | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4
  | .s5 => 5 | .s6 => 6 | .s7 => 7 | .s8 => 8 | .s9 => 9 | .cons => 11

/-- The parent subformula-slot a child must reproduce: slot `i ↦ (sf(i+1)_s, sf(i+1)_f,
    sf(i+1)_e)` (the paper's `x_out^comp = (sf1,sf2,sf3)`, each a `(child_subject,
    child_formula, sf_evaluation)` triple).  A §0-structural address referencing ONLY the parent
    label's `Pub` — no pointer, no positional lookup. -/
def sfTriple (pub : Pub K) : Fin 3 → FP K × FP K × FP K
  | 0 => (pub.sf1_s, pub.sf1_f, pub.sf1_e)
  | 1 => (pub.sf2_s, pub.sf2_f, pub.sf2_e)
  | 2 => (pub.sf3_s, pub.sf3_f, pub.sf3_e)

/-- Parent-declared child state tag `sf*_st`, `none ↦ nullStateTag`. -/
def sfState (pub : Pub K) : Fin 3 → K
  | 0 => pub.sf1_st.getD (nullStateTag : K)
  | 1 => pub.sf2_st.getD (nullStateTag : K)
  | 2 => pub.sf3_st.getD (nullStateTag : K)

/-- **Child-content link.**  Each
    active subformula child's committed *input/output data* — the child compute row's
    `(input_subject, input_formula, evaluation) = (s, f, e)` — must equal the parent's committed
    `(sf_i_s, sf_i_f, sf_i_e)` subformula slot.  Child *state* is bound by the walk RLC
    (overlay hosts + in-gate `childPayloadRLC`), not by this `Fcomp` conjunct.
    References ONLY `lbl` and `xout` — §0-structural. -/
def childLinkComp (lbl : State × DTcomp K)
    (xout : Fin 3 → Option (State × DTcomp K)) : Prop :=
  ∀ i : Fin 3, (i : ℕ) < fanoutComp lbl.1 →
    (xout i).map (fun c => (c.2.2.1.s, c.2.2.1.f, c.2.2.1.e)) = some (sfTriple lbl.2.2.1 i)

/-- **`L_comp` as an algebraically-constrainable labeling language `L(F,n)`**.  A label `(s, (inp,pub,dec))` with child-label vector `xout ∈
    (Fin 3 → Option _)` is accepted iff (1) the row's own state is `s`, (2) the algorithmic
    verifier `V_comp` accepts the row, (3) the child vector has exactly the first `fanoutComp s`
    slots non-`⊥` — the *state-defined dynamic labeling* of the opcode, and (4) each active child's
    `(s,f,e)` data links to the parent's `sf`-slot. -/
def Fcomp : (State × DTcomp K) → (Fin 3 → Option (State × DTcomp K)) → Prop :=
  fun lbl xout =>
    lbl.2.2.1.state = lbl.1 ∧ Vcomp lbl.2.1 lbl.2.2.1 lbl.2.2.2 ∧
      (∀ i : Fin 3, (i : ℕ) < fanoutComp lbl.1 ↔ xout i ≠ none) ∧
      childLinkComp lbl xout

/-- **The paper's `LT_comp` projection of a full compute label**:
    the row's state and its `(subject, formula, evaluation)` fingerprints — exactly the data the
    walk's `RLC^γ(current_node)` commits.  The state is read from the
    row's `Pub` (the selector bank); `Fcomp`'s first conjunct identifies it with the tree's `S`
    component on accepted trees. -/
def computeLabelOf (l : State × DTcomp K) : LTcomp K :=
  ⟨l.2.2.1.state, l.2.2.1.s, l.2.2.1.f, l.2.2.1.e⟩

/-- **The paper's `LT_comp` label vector** of a row's `Pub`:
    coordinate `0` the opcode tag, `1..9` the `size/dyck/leaf` coordinates of `(s, f, e)`.  This
    is what `RLC^γ(current_node)` commits in the walk and what a parent can declare
    for a child.  It is a function of `computeLabelOf` alone. -/
def labelVecOfPub (pub : Pub K) : Fin 10 → K
  | ⟨0, _⟩ => stateTagField pub.state
  | ⟨1, _⟩ => pub.s.size
  | ⟨2, _⟩ => pub.s.dyck
  | ⟨3, _⟩ => pub.s.leaf
  | ⟨4, _⟩ => pub.f.size
  | ⟨5, _⟩ => pub.f.dyck
  | ⟨6, _⟩ => pub.f.leaf
  | ⟨7, _⟩ => pub.e.size
  | ⟨8, _⟩ => pub.e.dyck
  | ⟨9, _⟩ => pub.e.leaf

/-- The hosted state tag of child slot `j` of walk node `i` (1-indexed) of a BFS row list: the
    child's own opcode tag when the slot is active, `nullStateTag` when it
    is absent.  This is the honest prover's value for the overlay hosts. -/
def childStateTagCol (W : List (Walk.NTree (State × DTcomp K))) (i j : ℕ) : K :=
  (((W[i - 1]?).bind fun t => t.children[j]?).map
    fun c => stateTagField c.label.2.2.1.state).getD (nullStateTag : K)

theorem computeLabelOf_eval_eq {a b : State × DTcomp K}
    (h : computeLabelOf a = computeLabelOf b) :
    (a.2.2.1.s, a.2.2.1.f, a.2.2.1.e) = (b.2.2.1.s, b.2.2.1.f, b.2.2.1.e) := by
  simp only [computeLabelOf, LTcomp.mk.injEq] at h
  obtain ⟨_, hs, hf, he⟩ := h
  rw [hs, hf, he]

/-- `childLinkComp` reads each child only through its `LT_comp` projection. -/
theorem childLinkComp_of_labelOf_eq (lbl : State × DTcomp K)
    {xout xout' : Fin 3 → Option (State × DTcomp K)}
    (h : ∀ j, (xout j).map computeLabelOf = (xout' j).map computeLabelOf)
    (hl : childLinkComp lbl xout) : childLinkComp lbl xout' := by
  intro i hi
  have hli := hl i hi
  have hj := h i
  cases hx : xout i with
  | none => rw [hx] at hli; simp at hli
  | some c =>
    cases hx' : xout' i with
    | none => rw [hx, hx'] at hj; simp at hj
    | some c' =>
      rw [hx, hx'] at hj
      simp only [Option.map_some, Option.some.injEq] at hj
      rw [hx] at hli
      simp only [Option.map_some, Option.some.injEq] at hli
      simp only [Option.map_some, Option.some.injEq]
      rw [← hli]
      exact (computeLabelOf_eval_eq hj).symm

/-- **`Fcomp` depends on the child vector only through `computeLabelOf`** — the walk needs to
    bind no more of a child than its `LT_comp` label. -/
theorem Fcomp_respects_labelOf (lbl : State × DTcomp K)
    {xout xout' : Fin 3 → Option (State × DTcomp K)}
    (h : ∀ j, (xout j).map computeLabelOf = (xout' j).map computeLabelOf)
    (hF : Fcomp lbl xout) : Fcomp lbl xout' := by
  obtain ⟨h1, h2, h3, h4⟩ := hF
  refine ⟨h1, h2, ?_, childLinkComp_of_labelOf_eq lbl h h4⟩
  intro i
  rw [h3 i]
  have hj := h i
  constructor
  · intro hne hx'
    rw [hx'] at hj
    cases hx : xout i with
    | none => exact hne hx
    | some c => rw [hx] at hj; simp at hj
  · intro hne hx
    rw [hx] at hj
    cases hx' : xout' i with
    | none => exact hne hx'
    | some c => rw [hx'] at hj; simp at hj

/-- **`Thm:comp_38`, the load-bearing structural claim.**  `L_comp` satisfies
    `Def:state_data_separation` (`StateSep`): it is *solely state-traversable* with terminal
    states `S_leaf = {s : fanout s = 0} = {OP_0, OP_1}`, and a *state-defined
    dynamic labeling* language (fanout determined by the opcode).  Hence `Walk_IOP_final`
    applies to the compute walk. -/
noncomputable def comp_stateSep : StateSep (Fcomp (K := K)) where
  Sleaf := fun s => fanoutComp s = 0
  fanout := fanoutComp
  fanout_le := by intro s; cases s <;> simp [fanoutComp]
  fanout_leaf := fun s h => h
  dynamic := by intro s d xout hF i; exact hF.2.2.1 i
  solely := by
    rintro ⟨⟨s, d⟩, ch⟩ hrvt
    rw [RVT] at hrvt
    obtain ⟨hF, _hch, hleaf⟩ := hrvt
    simp only [NTree.label_node]
    constructor
    · intro hsl
      rw [hleaf]
      refine ⟨hF.1, hF.2.1, ?_, ?_⟩
      · intro i
        exact ⟨fun hlt => absurd (hsl ▸ hlt) (Nat.not_lt_zero _), fun hne => absurd rfl hne⟩
      · -- childLinkComp is vacuous at a leaf (fanout = 0)
        intro i hi; exact absurd (hsl ▸ hi) (Nat.not_lt_zero _)
    · intro hil
      rw [hleaf] at hil
      have h0 := hil.2.2.1 ⟨0, by norm_num⟩
      simp only [ne_eq, not_true_eq_false, iff_false, not_lt, Nat.le_zero] at h0
      exact h0

/-- **Non-vacuity of `L_comp`.**  `F_comp` accepts a concrete `OP_0` leaf, so the `StateSep`
    instance is not vacuously over an empty language (defends against a vacuity attack). -/
theorem Fcomp_nonvacuous : ∃ (lbl : State × DTcomp K), Fcomp lbl (fun _ => none) := by
  refine ⟨⟨State.s0, ⟨0, 0, 0, 0, 0⟩,
    { state := .s0, s := 0, f := FP.cons 0 ⟨0,0,0⟩ ⟨0,0,0⟩, e := 0,
      sf1_s := 0, sf1_f := 0, sf1_e := 0, sf2_s := 0, sf2_f := 0, sf2_e := 0,
      sf3_s := 0, sf3_f := 0, sf3_e := 0, ln_prev := 0, ln := 0,
      mr1 := ⟨FP.cons 0 ⟨0,0,0⟩ ⟨0,0,0⟩, ⟨0,0,0⟩, 3, 0⟩, mr2 := ⟨0, 0, 0, 0⟩,
      mr3 := MemRec.zero },
    ⟨⟨0,0,0⟩, ⟨0,0,0⟩, 0, 0, 0, 0⟩⟩, ?_⟩
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rfl
  · simp
  · simp [SVhead, headAtom, State.toNat]
  · simp [memBlk, MemRec.zero]
  · simp [evalV, sfz1, sfz2, sfz3]
  · intro i; simp only [fanoutComp, Nat.not_lt_zero, ne_eq, false_iff, not_not]
  · intro i hi; simp only [fanoutComp, Nat.not_lt_zero] at hi

/-! ### Cost figures

  The numeric figures are recorded as documented `def`s referencing the table structure.  The
  paper states: `57·e + 13` columns and `20·e + 13` degree-4 transition gates, over the
  extension order `e` (`= 3` for the Goldilocks cubic). -/

/-- Column count of the compute-table RAP: `57·e + 13`. -/
def comp_columns (e : ℕ) : ℕ := 57 * e + 13
/-- Degree-4 transition-gate count of the compute-table RAP: `20·e + 13`. -/
def comp_deg4_gates (e : ℕ) : ℕ := 20 * e + 13

end ComputeTable

namespace MemoryTable

variable {K : Type*} [Field K]

/-- **`intermediate` LogUp block, forward (`WF`-free).**  A satisfying assignment of the RAP
    `intermediate` block `interR` (over the inverse-witness column `g`) implies the algorithm's
    honest `pole⁻¹` form `interV`.  Forward is unconditional
    (`pole·g = 1 ⟹ pole ≠ 0`); it is the backward direction of `inter_iff` that needs `WF`. -/
theorem inter_sound (inp : Inputs K) (p : Pub K) (g : K) (hg : interR inp p g) :
    interV inp p := by
  cases hst : p.st <;> simp only [interR, interV, hst] at hg ⊢
  case decompose => exact hg
  case halt => exact hg
  case read_root =>
    obtain ⟨h1, h2⟩ := hg
    have hP : pole inp p.mem p.cprime ≠ 0 := by
      intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
    have hgv : g = (pole inp p.mem p.cprime)⁻¹ := by
      calc g = (pole inp p.mem p.cprime)⁻¹ * (pole inp p.mem p.cprime * g) := by
                rw [← mul_assoc, inv_mul_cancel₀ hP, one_mul]
        _ = (pole inp p.mem p.cprime)⁻¹ := by rw [h1, mul_one]
    rw [h2, hgv]
  case verify_child =>
    obtain ⟨h1, h2⟩ := hg
    have hP : pole inp p.mem p.cprime ≠ 0 := by
      intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
    have hgv : g = (pole inp p.mem p.cprime)⁻¹ := by
      calc g = (pole inp p.mem p.cprime)⁻¹ * (pole inp p.mem p.cprime * g) := by
                rw [← mul_assoc, inv_mul_cancel₀ hP, one_mul]
        _ = (pole inp p.mem p.cprime)⁻¹ := by rw [h1, mul_one]
    rw [hgv] at h2; linear_combination -h2

/-- **`Lem:equiv_mem`, forward direction (`WF`-free)** — the soundness half.  A satisfying
    assignment of the memory RAP `RAP_mem` implies the algorithmic verifier `V_mem` accepts.  Does **not** assume `WF` (the pole-nonvanishing genericity). -/
theorem equiv_mem_sound (inp : Inputs K) (p : Pub K) :
    (∃ g, RAPmem inp p g) → Vmem inp p := by
  rintro ⟨g, _hsv, heq, hint⟩
  exact ⟨verBool_holds p, heq, inter_sound inp p g hint⟩

/-! ## `Thm:mem_38`: `L_mem` satisfies `Def:state_data_separation` -/

open Walk

/-- Per-state **fanout** of the memory walk: `decompose ↦ 2` (a cell has two
    children), `halt ↦ 0` (a leaf/atom, terminal), and the two axis-lookup states
    `read_root`/`verify_child ↦ 1`.  Max is `2`, so the memory arity is `n = 2`. -/
def fanoutMem : MState → ℕ
  | .decompose => 2 | .halt => 0 | .read_root => 1 | .verify_child => 1

/-- The data field of a memory label: the RAP inputs and the row's public columns. -/
abbrev DTmem (K : Type*) := Inputs K × Pub K

/-- The parent cell a child slot must reproduce: slot `0 ↦ lc`, slot `1 ↦ rc`.  A §0-structural (tree-edge) address referencing ONLY the parent label `lbl` — no
    pointer, no committed-line/positional lookup. -/
def memCell (lbl : MState × DTmem K) : Fin 2 → Cell K
  | 0 => lbl.2.2.lc
  | 1 => lbl.2.2.rc

/-- **Child-content link.**  Each
    active child slot's committed *content* — the child label's parent-cell `pt` — must equal the
    parent's corresponding `lc`/`rc` cell.  This is the tree-edge equality the paper's traversable
    `F` carries (it is what makes the per-row `pt = cons(lc,rc)` check descend into the REAL
    children).  References ONLY `lbl` (parent) and `xout` (the child-label vector) — a
    §0-structural constraint, NOT a pointer/committed-line/index. -/
def childLinkMem (lbl : MState × DTmem K)
    (xout : Fin 2 → Option (MState × DTmem K)) : Prop :=
  ∀ i : Fin 2, (i : ℕ) < fanoutMem lbl.1 →
    (xout i).map (fun c => c.2.2.pt) = some (memCell lbl i)

/-- **`L_mem` as a labeling language**.  A label `(s, (inp,pub))` with
    child vector `xout` is accepted iff (1) the row's state is `s`, (2) the algorithmic memory
    verifier `V_mem` accepts, (3) the child vector has exactly the first `fanoutMem s` slots
    non-`⊥`, and (4) each active child's content links to the parent's `lc`/`rc` cell. -/
def Fmem : (MState × DTmem K) → (Fin 2 → Option (MState × DTmem K)) → Prop :=
  fun lbl xout =>
    lbl.2.2.st = lbl.1 ∧ Vmem lbl.2.1 lbl.2.2 ∧
      (∀ i : Fin 2, (i : ℕ) < fanoutMem lbl.1 ↔ xout i ≠ none) ∧
      childLinkMem lbl xout

/-! ### The paper's `x^mem` label projection -/

/-- Memory-state tag as a field element, in table order: the
    `NodeEncoding.memoryStateTag` values `0..3`. -/
def mstateTagField (st : MState) : K :=
  match st with
  | .decompose => 0 | .halt => 1 | .read_root => 2 | .verify_child => 3

/-- The tag an absent child slot carries in
    the hosted child-state coordinate: `4`, outside the four state tags.  The one-hot
    fanout selector keeps absent slots out of the walk sum, so the value is a convention only. -/
def nullMStateTag : ℕ := 4

/-- **The paper's `x^mem` projection of a full memory label**:
    `(state, (parent, (axis_counts_P, axis_indicator_P)))` — the row's `Pub` state and its
    parent cell.  `Fmem`'s first conjunct identifies the `Pub` state with the tree's `S`
    component on accepted trees; `childLinkMem` reads a child only through its parent cell. -/
def memoryLabelOf (l : MState × DTmem K) : LTmem K :=
  ⟨l.2.2.st, l.2.2.pt⟩

/-- **The paper's `x^mem` label vector** of a row's `Pub`: coordinate `0`
    the state tag, `1..3` the parent noun fingerprint `(size, dyck, leaf)`, `4` `axis_counts_P`,
    `5` `axis_indicator_P`.  This is what `RLC^γ(current_node)` commits in the memory walk
    and what a parent declares for a child.  A function of
    `memoryLabelOf` alone. -/
def memoryLabelVec (pub : Pub K) : Fin 6 → K
  | ⟨0, _⟩ => mstateTagField pub.st
  | ⟨1, _⟩ => pub.pt.noun.size
  | ⟨2, _⟩ => pub.pt.noun.dyck
  | ⟨3, _⟩ => pub.pt.noun.leaf
  | ⟨4, _⟩ => pub.pt.counts
  | ⟨5, _⟩ => pub.pt.indicator

/-- The hosted state tag of child slot `j` of memory walk node `i` (1-indexed) of a BFS row
    list: the child's own state tag when the slot is active, `nullMStateTag` when absent.  The
    honest prover's value for the two hosted child-state coordinates. -/
def memChildStateTagCol (W : List (NTree (MState × DTmem K))) (i j : ℕ) : K :=
  (((W[i - 1]?).bind fun t => t.children[j]?).map
    fun c => mstateTagField c.label.2.2.st).getD (nullMStateTag : K)

theorem memoryLabelOf_pt_eq {a b : MState × DTmem K}
    (h : memoryLabelOf a = memoryLabelOf b) : a.2.2.pt = b.2.2.pt := by
  simp only [memoryLabelOf, LTmem.mk.injEq] at h
  exact h.2

/-- `childLinkMem` reads each child only through its `x^mem` projection. -/
theorem childLinkMem_of_labelOf_eq (lbl : MState × DTmem K)
    {xout xout' : Fin 2 → Option (MState × DTmem K)}
    (h : ∀ j, (xout j).map memoryLabelOf = (xout' j).map memoryLabelOf)
    (hl : childLinkMem lbl xout) : childLinkMem lbl xout' := by
  intro i hi
  have hli := hl i hi
  have hj := h i
  cases hx : xout i with
  | none => rw [hx] at hli; simp at hli
  | some c =>
    cases hx' : xout' i with
    | none => rw [hx, hx'] at hj; simp at hj
    | some c' =>
      rw [hx, hx'] at hj
      simp only [Option.map_some, Option.some.injEq] at hj
      rw [hx] at hli
      simp only [Option.map_some, Option.some.injEq] at hli
      simp only [Option.map_some, Option.some.injEq]
      rw [← hli]
      exact (memoryLabelOf_pt_eq hj).symm

/-- **`Fmem` depends on the child vector only through `memoryLabelOf`** — the memory walk needs
    to bind no more of a child than its `x^mem` label. -/
theorem Fmem_respects_labelOf (lbl : MState × DTmem K)
    {xout xout' : Fin 2 → Option (MState × DTmem K)}
    (h : ∀ j, (xout j).map memoryLabelOf = (xout' j).map memoryLabelOf)
    (hF : Fmem lbl xout) : Fmem lbl xout' := by
  obtain ⟨h1, h2, h3, h4⟩ := hF
  refine ⟨h1, h2, ?_, childLinkMem_of_labelOf_eq lbl h h4⟩
  intro i
  rw [h3 i]
  have hj := h i
  constructor
  · intro hne hx'
    rw [hx'] at hj
    cases hx : xout i with
    | none => exact hne hx
    | some c => rw [hx] at hj; simp at hj
  · intro hne hx
    rw [hx] at hj
    cases hx' : xout' i with
    | none => exact hne hx'
    | some c => rw [hx'] at hj; simp at hj

/-- **`Thm:mem_38`, the load-bearing structural claim.**  `L_mem` satisfies
    `Def:state_data_separation`: solely state-traversable with `S_leaf = {halt}`
    and a state-defined dynamic labeling (`fanout`: `decompose ↦ 2`, `halt ↦ 0`,
    `read_root/verify_child ↦ 1`).  Hence `Walk_IOP_final` applies to the memory walk — for a
    **single root**.  The multi-root `Corr:forest` extension is ALSO covered: its composed soundness
    is closed as `Walk.Walk_IOP_forest_final_card`/`_prob` (via
    `Walk.reconForest_ForestReconGoal`), restated here as `walkBadForest_prob` and consumed
    by `V_NockVMROM_forest`.  This is in fact the corollary the paper's own `Thm:mem_38`
    proof invokes. -/
noncomputable def mem_stateSep : StateSep (Fmem (K := K)) where
  Sleaf := fun s => fanoutMem s = 0
  fanout := fanoutMem
  fanout_le := by intro s; cases s <;> simp [fanoutMem]
  fanout_leaf := fun s h => h
  dynamic := by intro s d xout hF i; exact hF.2.2.1 i
  solely := by
    rintro ⟨⟨s, d⟩, ch⟩ hrvt
    rw [RVT] at hrvt
    obtain ⟨hF, _hch, hleaf⟩ := hrvt
    simp only [NTree.label_node]
    constructor
    · intro hsl
      rw [hleaf]
      refine ⟨hF.1, hF.2.1, ?_, ?_⟩
      · intro i
        exact ⟨fun hlt => absurd (hsl ▸ hlt) (Nat.not_lt_zero _), fun hne => absurd rfl hne⟩
      · -- childLinkMem is vacuous at a leaf (fanout = 0)
        intro i hi; exact absurd (hsl ▸ hi) (Nat.not_lt_zero _)
    · intro hil
      rw [hleaf] at hil
      have h0 := hil.2.2.1 ⟨0, by norm_num⟩
      simp only [ne_eq, not_true_eq_false, iff_false, not_lt, Nat.le_zero] at h0
      exact h0

/-- **Non-vacuity of `L_mem`.**  `F_mem` accepts a concrete `halt` leaf. -/
theorem Fmem_nonvacuous : ∃ (lbl : MState × DTmem K), Fmem lbl (fun _ => none) := by
  refine ⟨⟨MState.halt, ⟨0, 0, 0⟩,
    { st := .halt, pt := Cell.zero, lc := Cell.zero, rc := Cell.zero,
      lcSt := .halt, rcSt := .halt, mem := ComputeTable.MemRec.zero, ipre := 0, icur := 0 }⟩, ?_⟩
  refine ⟨rfl, ⟨verBool_holds _, ?_, ?_⟩, ?_, ?_⟩
  · simp [eqBlk, Cell.zero, ComputeTable.MemRec.zero]
  · simp only [interV]
  · intro i; simp only [fanoutMem, Nat.not_lt_zero, ne_eq, false_iff, not_not]
  · intro i hi; simp only [fanoutMem, Nat.not_lt_zero] at hi

/-! ### Cost figures

  Documented `def`s (see the compute-table note).  The paper states `54·e + 5` columns and
  `20·e + 13` degree-4 transition gates. -/

/-- Column count of the memory-table RAP: `54·e + 5`. -/
def mem_columns (e : ℕ) : ℕ := 54 * e + 5
/-- Degree-4 transition-gate count of the memory-table RAP: `20·e + 13`. -/
def mem_deg4_gates (e : ℕ) : ℕ := 20 * e + 13

end MemoryTable

/-! The step that a satisfied walk with
  `node_list = node_queue` witnesses a full BFT is **false** without queue-validity (witness
  `h=3, fo=(0,2,0)`).  `Walk_IOP_final` therefore carries a `BFSValid fo h` hypothesis.
  The instantiation *supplies* it: the BFS layout of
  **any genuine finite tree** (a real Nock execution tree / noun-decomposition tree) yields a
  fanout column satisfying both `BFSValid` and the tiling `Sf fo h + 1 = h`.  So the
  hypothesis is not vacuous and is discharged exactly by the table instantiation. -/

namespace Walk

variable {LT : Type*}

/-- A nonempty forest has positive total size. -/
theorem nonempty_totalSize (l : List (NTree LT)) (hne : l ≠ []) : 1 ≤ totalSize l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons t rest =>
    have : 1 ≤ t.size := by cases t with | node _ _ => simp [NTree.size]
    rw [totalSize_cons]; omega

/-- The BFS of a nonempty forest is nonempty. -/
theorem bfsForest_nonempty (l : List (NTree LT)) (hne : l ≠ []) : bfsForest l ≠ [] := by
  intro h
  have hlen := bfsForest_length l
  rw [h] at hlen
  simp only [List.length_nil] at hlen
  have := nonempty_totalSize l hne
  omega

/-- **BFS queue-validity (forest form).**  For a nonempty forest `l` with `m = l.length` roots
    and BFS list `W = bfsForest l`, every position `i = k+1 ≤ |W|` has already been *queued* by
    the time the first `k` nodes are processed: `i ≤ m + |children of the first k nodes|`.
    Strong induction on `totalSize`, peeling one BFS level (`bfsForest_cons_eq`). -/
theorem bfsForest_queue (n : ℕ) : ∀ (l : List (NTree LT)), totalSize l ≤ n → l ≠ [] →
    ∀ k, k + 1 ≤ (bfsForest l).length →
      k + 1 ≤ l.length + (((bfsForest l).take k).flatMap NTree.children).length := by
  induction n with
  | zero =>
    intro l hn hne
    exact absurd (le_trans (nonempty_totalSize l hne) hn) (by norm_num)
  | succ m ih =>
    intro l hn hne k hk
    have hstep : bfsForest l = l ++ bfsForest (l.flatMap NTree.children) :=
      bfsForest_cons_eq l hne
    set C := l.flatMap NTree.children with hC
    set W' := bfsForest C with hW'
    have hWlen : (bfsForest l).length = l.length + W'.length := by
      rw [hstep, List.length_append]
    by_cases hkle : k ≤ l.length
    · -- prefix stays within the first BFS level `l`
      rw [hstep, List.take_append_of_le_length hkle]
      by_cases hklt : k < l.length
      · have : ((l.take k).flatMap NTree.children).length ≥ 0 := Nat.zero_le _
        omega
      · -- k = |l|: `l.take k = l`, so the children are all of `C`; need `|C| ≥ 1`
        have hkeq : k = l.length := le_antisymm hkle (not_lt.mp hklt)
        subst hkeq
        rw [List.take_length]
        have hEq : (l.flatMap NTree.children) = C := rfl
        rw [hEq]
        have hW'pos : 1 ≤ W'.length := by rw [hWlen] at hk; omega
        have hCne : C ≠ [] := by
          intro hCnil; rw [hW', hCnil, bfsForest_nil] at hW'pos; simp at hW'pos
        have hCpos : 1 ≤ C.length := List.length_pos_of_ne_nil hCne
        omega
    · -- k > |l|: prefix covers all of `l` plus a `W'`-prefix; use the IH on `C`
      have hkgt : l.length < k := not_le.mp hkle
      rw [hstep, List.take_append, List.flatMap_append, List.length_append]
      rw [List.take_of_length_le (le_of_lt hkgt)]
      have hClen : (l.flatMap NTree.children).length = C.length := rfl
      have hCne : C ≠ [] := by
        have hW'pos : 1 ≤ W'.length := by rw [hWlen] at hk; omega
        intro hCnil; rw [hW', hCnil, bfsForest_nil] at hW'pos; simp at hW'pos
      have htsC : totalSize C ≤ m := by
        have hts := totalSize_flatMap_children l
        have hlpos : 1 ≤ l.length := List.length_pos_of_ne_nil hne
        rw [← hC] at hts; omega
      have hk' : (k - l.length) + 1 ≤ W'.length := by rw [hWlen] at hk; omega
      have IHapp := ih C htsC hCne (k - l.length) (by rw [← hW']; exact hk')
      rw [← hW'] at IHapp
      rw [hClen]
      omega

/-- **Genuine trees are queue-valid.**  The BFS layout of any concrete finite
    `NTree root` yields a fanout column `foCol (bfsForest [root])` satisfying `BFSValid` at
    height `h = |bfsForest [root]| = totalSize [root]`. -/
theorem foCol_BFSValid (root : NTree LT) :
    BFSValid (foCol (bfsForest [root])) (bfsForest [root]).length := by
  intro i hi1 hih
  rw [Sf_foCol]
  have hq := bfsForest_queue (totalSize [root]) [root] le_rfl (by simp) (i - 1) (by omega)
  have h1 : ([root] : List (NTree LT)).length = 1 := rfl
  rw [h1] at hq
  have hi : i - 1 + 1 = i := by omega
  rw [hi] at hq
  exact hq

/-- **The queue tiles.**  For the BFS layout of a genuine tree, the fanout
    column also satisfies the tiling identity `Sf fo h + 1 = h`: the total children count is
    `h − 1` (every non-root node is exactly one child, `walk_tail_eq`). -/
theorem foCol_Sf_tiling (root : NTree LT) :
    Sf (foCol (bfsForest [root])) (bfsForest [root]).length + 1 = (bfsForest [root]).length := by
  rw [Sf_foCol, List.take_length]
  have htail := walk_tail_eq root
  have hlen : (bfsForest [root]).length
      = ((bfsForest [root]).flatMap NTree.children).length + 1 := by
    conv_lhs => rw [htail]; rw [List.length_cons]
  omega

end Walk

/-! # The final `NockVMROM` theorem

  We assemble the two RAP chips.  `Walk_IOP_final` provides both `RAP_walk` soundness gadgets
  over the `StateSep` instances above — the compute walk (arity `3`) and the memory walk
  (arity `2`) — each as a **single-root** tree (`Sf fo h + 1 = h`); that is the shape used by
  the bundle corollary `NockVMROM` and by `V_NockVMROM`, and for the memory chip it is the
  paper's base memory table.  The multi-root `Corr:forest` generalization for
  subject-mutating programs is NOT deferred: its composed
  soundness is `Walk.Walk_IOP_forest_final_card`/`_prob`, restated below as
  `walkBadForest_prob`, and `V_NockVMROM_forest` discharges the memory conjunct at
  `kroots_m ≥ 1` with it.  `Thm:IO_result` (`io_result_LIO`) links the two IO columns (the
  memory-execution separation).  `BFSValid`/tiling are discharged by genuine trees. -/

namespace NockVM

open Walk ComputeTable MemoryTable

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The **bad-challenge set** of a walk chip: challenge pairs `(α, γ)` for which the
    `RAP_walk` gates accept (`out_walk = acc h = 0`) yet no genuine `L_RVT` tree reproduces
    the committed rows (`¬ ReconGoal`).  Exactly the set bounded by `Walk_IOP_final_prob`. -/
noncomputable def walkBad {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT)
    (fo : ℕ → ℕ) (h : ℕ) : Finset (K × K) :=
  Finset.univ.filter (fun p : K × K =>
    (∃ ln count acc : ℕ → K,
      WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
        ln count acc p.1 (rlc p.2 (enc (lbl 1)) * p.1) p.1 h ∧ acc h = 0)
    ∧ ¬ ReconGoal St lbl h)

/-- **`Walk_IOP_final_prob`, restated through `walkBad`.**  Over uniform challenges `(α, γ)`,
    the probability of the walk chip accepting without a genuine `L_RVT` witness is
    `≤ h/|K| + ε_RLC`, `ε_RLC = h·(node_size − 1)/|K|` (honest bound). -/
theorem walkBad_prob {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (hEnc : Function.Injective enc)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((walkBad St enc lbl clab fo h).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) :=
  Walk_IOP_final_prob St enc hEnc lbl clab fo hSf hvalid harity hfo hFcommit

/-- `walkBad_prob` when the encoder binds only a label projection: `hEnc` says
encoder-equal labels have equal projections, `hResp` that `F` reads children through it. -/
theorem walkBad_prob_of_label {S DT L : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : StateSep F)
    (labelOf : S × DT → L) (hResp : Walk.RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {h : ℕ} (hSf : Sf fo h + 1 = h) (hvalid : BFSValid fo h) (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((walkBad St enc lbl clab fo h).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) :=
  Walk_IOP_final_prob_of_label St labelOf hResp enc hEnc lbl clab fo hSf hvalid harity hfo
    hFcommit

/-- The **forest bad-challenge set** of a walk chip: challenge
    pairs `(α, γ)` for which the `RAP_walk` gates accept with the FOREST recognizer inputs
    `(seed, initial_count) = (Σ_{i≤kroots} RLC^γ(sltᵢ)·αⁱ, αᵏ)` (`out_walk = 0`) yet no list of
    `kroots` genuine `L_RVT` trees reproduces the committed rows in AGGREGATE BFS
    (`¬ ForestReconGoal`).  The multi-root analogue of `walkBad`; exactly the set bounded by
    `Walk_IOP_forest_final_prob`. -/
noncomputable def walkBadForest {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT)
    (fo : ℕ → ℕ) (kroots h : ℕ) : Finset (K × K) :=
  Finset.univ.filter (fun p : K × K =>
    (∃ ln count acc : ℕ → K,
      WalkSat (fun i => rlc p.2 (enc (lbl i))) (fun i l => rlc p.2 (enc (clab i l))) fo
        ln count acc p.1 (∑ i ∈ Finset.Icc 1 kroots, rlc p.2 (enc (lbl i)) * p.1 ^ i)
        (p.1 ^ kroots) h ∧ acc h = 0)
    ∧ ¬ ForestReconGoal St lbl kroots h)

/-- **`Walk_IOP_forest_final_prob`, restated through `walkBadForest`.**  Over uniform challenges
    `(α, γ)`, the probability of the forest walk chip accepting without `kroots` genuine `L_RVT`
    trees (in aggregate) is `≤ h/|K| + ε_RLC`, `ε_RLC = h·(node_size − 1)/|K|` (honest bound). -/
theorem walkBadForest_prob {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (hEnc : Function.Injective enc)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((walkBadForest St enc lbl clab fo kroots h).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) :=
  Walk_IOP_forest_final_prob St enc hEnc lbl clab fo hk hSf hvalid harity hfo hFcommit

/-- `walkBadForest_prob` when the encoder binds only a label projection. -/
theorem walkBadForest_prob_of_label {S DT L : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : StateSep F)
    (labelOf : S × DT → L) (hResp : Walk.RespectsChildLabels F labelOf)
    (enc : (S × DT) → (Fin node_size → K))
    (hEnc : ∀ a b, enc a = enc b → labelOf a = labelOf b)
    (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT) (fo : ℕ → ℕ)
    {kroots h : ℕ} (hk : 1 ≤ kroots) (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h)
    (harity : ∀ i, fo i ≤ n)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = St.fanout (lbl i).1)
    (hFcommit : ∀ i, 1 ≤ i → i ≤ h →
      F (lbl i) (fun j : Fin n => if (j : ℕ) < fo i then some (clab i (j + 1)) else none)) :
    ((walkBadForest St enc lbl clab fo kroots h).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (h : ℚ) / (Fintype.card K : ℚ)
          + ((h * (node_size - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ) :=
  Walk_IOP_forest_final_prob_of_label St labelOf hResp enc hEnc lbl clab fo hk hSf hvalid harity
    hfo hFcommit

/-- **The `kroots = 1` collapse of the forest bad-challenge set, mechanized.**  `walkBad` and
    `walkBadForest … 1` are *definitionally* distinct — the single-root recognizer seed is
    `RLC^γ(lbl 1)·α` with `initial_count = α`, the forest seed is
    `Σ_{i=1}^{1} RLC^γ(lbl i)·αⁱ` with `initial_count = α¹` —
    but they are equal as `Finset`s: the one-element sum collapses and `α¹ = α`, while the
    reconstruction goals agree by `Walk.ForestReconGoal_one`.  This is the capstone-layer
    counterpart of the walk-layer `Walk.Walk_IOP_final_card_of_forest`, and it upgrades the
    `V_NockVMROM` / `V_NockVMROM_forest` relationship from a *stated* correspondence to a proved
    one: the multi-root memory conjunct is a strict generalisation, not a different claim. -/
theorem walkBad_eq_walkBadForest_one {S DT : Type*} {n node_size : ℕ}
    {F : (S × DT) → (Fin n → Option (S × DT)) → Prop} (St : StateSep F)
    (enc : (S × DT) → (Fin node_size → K)) (lbl : ℕ → S × DT) (clab : ℕ → ℕ → S × DT)
    (fo : ℕ → ℕ) (h : ℕ) :
    walkBad St enc lbl clab fo h = walkBadForest St enc lbl clab fo 1 h := by
  unfold walkBad walkBadForest
  apply Finset.filter_congr
  intro q _
  have hseed_eq : (∑ i ∈ Finset.Icc 1 1, rlc q.2 (enc (lbl i)) * q.1 ^ i)
      = rlc q.2 (enc (lbl 1)) * q.1 := by
    rw [Finset.Icc_self, Finset.sum_singleton, pow_one]
  rw [hseed_eq, pow_one, Walk.ForestReconGoal_one]

/-- **Structural constants of `NockVMROM`**: opcode/memory one-hot of size `10`
    and memory-record arity `3`. -/
def opcode_onehot_size : ℕ := 10
def mem_record_arity : ℕ := 3

/-! ### Shared IO witness — deriving the IO record lists from the walk data

  The bundle `NockVMROM` feeds `io_result_LIO` *fresh* request/response lists with no connection
  to what the two walks commit.  `V_NockVMROM` instead feeds lists that are
  **functions of the same `lblc`/`lblm`** the walk-soundness conjuncts range over.  `encRec`
  flattens a memory record into its 9 field elements;
  `reqRecs`/`respRecs` collect, respectively, the compute walk's *emitted* memory-request records
  and the memory walk's *served* records, row by row.  The IO check then certifies that these two
  derived multisets match (`∈ L_IO`) — the memory-execution separation of §5. -/

/-- Flatten a memory record into 9 field coordinates
    `(root.size, root.dyck, root.leaf, child.size, child.dyck, child.leaf, T, ts, C')`.
    The one-argument form pins `C' = 0`; use `encRecC` when the pub carries a live `C'`.
    Do **not** add a default `cprime` argument: `encRec r 7` must remain coordinate 7. -/
def encRec (r : MemRec K) : Fin 9 → K :=
  ![r.root.size, r.root.dyck, r.root.leaf, r.child.size, r.child.dyck, r.child.leaf, r.axis, r.ts, 0]

/-- Nine-wide encode with an explicit form R `C'`. -/
def encRecC (r : MemRec K) (cprime : K) : Fin 9 → K :=
  ![r.root.size, r.root.dyck, r.root.leaf, r.child.size, r.child.dyck, r.child.leaf,
    r.axis, r.ts, cprime]

@[simp] theorem encRecC_zero (r : MemRec K) : encRecC r 0 = encRec r := rfl

/-- Encode a compute-side request whose `axis` field is the Nock-axis nat-cast: slot 6 is
    `T = λ^m`, slot 8 is `C' = (Cpoly (n−1) c).eval λ`, from the same `(m, c)` the certificate
    columns carry (`exists_cert`).  The single compute-IO encode; memory rows carry `(T, C')`. -/
noncomputable def encRecFormR (r : MemRec K) (lmb : K) : Fin 9 → K :=
  let ax := MemoryTable.nockAxisOf r.axis
  encRecC { r with axis := MemoryTable.formRT lmb ax } (MemoryTable.formRC lmb ax)

omit [Fintype K] [DecidableEq K] in
theorem encRecFormR_eq_encRecC (r : MemRec K) (lmb : K) :
    encRecFormR r lmb =
      encRecC { r with axis := MemoryTable.formRT lmb (MemoryTable.nockAxisOf r.axis) }
        (MemoryTable.formRC lmb (MemoryTable.nockAxisOf r.axis)) :=
  rfl

/-- The row-level memory record of an a-bearing record (`BindMemRow`): `axis := T`. -/
noncomputable def formRRow (r : MemRec K) (lmb : K) : MemRec K :=
  { r with axis := MemoryTable.formRT lmb (MemoryTable.nockAxisOf r.axis) }

/-- The row-level `C'` of an a-bearing record. -/
noncomputable def formRCprime (r : MemRec K) (lmb : K) : K :=
  MemoryTable.formRC lmb (MemoryTable.nockAxisOf r.axis)

omit [Fintype K] [DecidableEq K] in
/-- A row-level memory row's IO record is the single Form R encode of the a-bearing record. -/
@[simp] theorem encRecC_formRRow (r : MemRec K) (lmb : K) :
    encRecC (formRRow r lmb) (formRCprime r lmb) = encRecFormR r lmb :=
  rfl

omit [Fintype K] [DecidableEq K] in
@[simp] theorem formRRow_root (r : MemRec K) (lmb : K) : (formRRow r lmb).root = r.root := rfl
omit [Fintype K] [DecidableEq K] in
@[simp] theorem formRRow_child (r : MemRec K) (lmb : K) : (formRRow r lmb).child = r.child := rfl
omit [Fintype K] [DecidableEq K] in
@[simp] theorem formRRow_ts (r : MemRec K) (lmb : K) : (formRRow r lmb).ts = r.ts := rfl

/-- The request slots active for one compute row, in canonical slot order.  Activity is determined
    by the opcode's paper-specified request arity, not by testing the field value of a record:
    an active record is allowed to encode to zero, while inactive padding is omitted. -/
def activeRequestRecords (pub : ComputeTable.Pub K) : List (MemRec K) :=
  match pub.state with
  | .s1 | .s3 | .s4 | .cons => [pub.mr1]
  | .s0 | .s2 | .s5 | .s7 | .s8 => [pub.mr1, pub.mr2]
  | .s6 | .s9 => [pub.mr1, pub.mr2, pub.mr3]

/-- The compute walk's **emitted memory-request records** over rows `1..hc`.  Each compute row
    `lblc (k+1)` contributes exactly the opcode-active prefix of `mr1/mr2/mr3`; inactive padding
    is omitted independently of the active records' field values.  `lmb` is the Form R `λ` of the
    request encode (the shared coin, `ChallengeVector.lam`). -/
noncomputable def reqRecs (lblc : ℕ → State × DTcomp K) (hc : ℕ) (lmb : K) :
    List (Fin 9 → K) :=
  (List.range hc).flatMap (fun k =>
    let pub := (lblc (k + 1)).2.2.1
    (activeRequestRecords pub).map (fun r => encRecFormR r lmb))

omit [Fintype K] [DecidableEq K] in
/-- `reqRecs` is definitionally the opcode-active request prefix, encoded in slot order. -/
theorem reqRecs_eq_computeRows (lblc : ℕ → State × DTcomp K) (hc : ℕ) (lmb : K) :
    reqRecs lblc hc lmb =
      (List.range hc).flatMap (fun k =>
        let pub := (lblc (k + 1)).2.2.1
        (activeRequestRecords pub).map (fun r => encRecFormR r lmb)) :=
  rfl

variable {lmb : K}

/-- The memory walk's **served records** over rows `1..hm`.  A memory row `lblm (k+1)` serves its
    single `mem` record to the **external memory IO column** `W^IO_mem` exactly when its state is
    `read_root` — this is the ONLY state that removes a record from the IO column.  The
    `verify_child` state does NOT touch the external IO column: it removes an element from the
    SEPARATE internal `intermediate` accumulator, so it serves nothing to `W^IO_mem`.  The
    `decompose`/`halt` states serve nothing either.  One served record per
    `read_root`, matching the compute walk's one emitted request per lookup (`reqRecs`); each
    carries the lookup's unique timestamp `z^i`.
    Flat-mapped and `encRec`-encoded across the rows. -/
def respRecs (lblm : ℕ → MState × DTmem K) (hm : ℕ) : List (Fin 9 → K) :=
  (List.range hm).flatMap (fun k =>
    let pub := (lblm (k + 1)).2.2
    (MemoryTable.responseRecords pub).map (fun r => encRecC r pub.cprime))

omit [Fintype K] [DecidableEq K] in
/-- `respRecs` is the paper's `ver`-selected encoded response list. -/
theorem respRecs_eq_memoryRows (lblm : ℕ → MState × DTmem K) (hm : ℕ) :
    respRecs lblm hm =
      (List.range hm).flatMap (fun k =>
        let pub := (lblm (k + 1)).2.2
        if pub.ver then [encRecC pub.mem pub.cprime] else []) :=
  by
    unfold respRecs
    apply congrArg (fun f : ℕ → List (Fin 9 → K) => (List.range hm).flatMap f)
    funext k
    dsimp [MemoryTable.responseRecords]
    split_ifs <;> rfl

/-! ### The `Def:MES` SEED COUPLING — pinning the reconstructed record-roots to the compute requests

  `V_NockVMROM`/`V_NockVMROM_forest` couple the two chips ONLY through the multiset biconditional
  `io_result_LIO` (conjunct (3)): it certifies `(reqRecs, respRecs) ∈ L_IO`, i.e. that the served
  list is a *permutation* of the requested list.  That is the multiset half of `Def:MES`: the requests are all answered by the responses, uniquely.
  The *other* half of `Def:MES` — the operational **seed pin** of `Sec:IO_consistency` — is implicit
  there, folded inside the right-hand side of a biconditional and not available to the memory side
  in forward, per-record form.  Consequently the memory forest's **root nouns are a
  free witness** (see `AxisBridge.readVerifyNested_wall`).

  `SeedCoupled` states the seed pin in FORWARD, PER-RECORD form: from the `Thm:IO_result`
  endpoint it extracts that every served (reconstructed) memory record IS, verbatim, one of the
  compute's requested records — so its **root** is a compute-requested root, not a free seed —
  and that every served record's timestamp is the closed-form monomial `z^e`.  This is the transferable coupling object: it is stated at
  the shared record-list level (`reqRecs`/`respRecs`), so it applies to the single-root `V_NockVMROM`
  and the forest `V_NockVMROM_forest` verbatim. -/

/-- **`SeedCoupled` — the `Def:MES` seed coupling in forward, per-record form.**  Relative to the multiset-only `IO.LIO`, this exposes the coupling as the paper's
    shared `IO` object fed to the memory table as-is:
    * every served memory record `v` is, verbatim, a
      compute request (`v ∈ reqRecs`) — hence its root fingerprint `(v 0, v 1, v 2)` is one the
      compute table requested, NOT a free reconstructed seed;
    * every served record's timestamp `v 7` is the closed-form
      monomial `z^e` (the compute-table line number). -/
def SeedCoupled (lmb : K) (lblc : ℕ → State × DTcomp K) (hc : ℕ)
    (lblm : ℕ → MState × DTmem K) (hm : ℕ) (z : K) : Prop :=
  (∀ v ∈ respRecs lblm hm, v ∈ reqRecs lblc hc lmb)
    ∧ (∀ v ∈ respRecs lblm hm, ∃ e : ℕ, v 7 = z ^ e)

/-- **`seedCoupled_of_LIO` — the IO link delivers the seed coupling.**  From
    the `Thm:IO_result` endpoint `(reqRecs, respRecs) ∈ L_IO` — whose content (`IO.LIO`) is that the
    served list is a `List.Perm` of the requested list — together with the compute chip's closed-form
    request timestamps `z^i`, `SeedCoupled` holds: each served record is
    as-is a compute request (by the `Perm` membership) and thereby inherits the closed-form
    timestamp.  This is the memory-side transfer described in the paper. -/
theorem seedCoupled_of_LIO (lblc : ℕ → State × DTcomp K) (hc : ℕ)
    (lblm : ℕ → MState × DTmem K) (hm : ℕ) (z : K) {Ksz : ℕ}
    (hReqTs : ∀ v ∈ reqRecs lblc hc lmb, ∃ e : ℕ, v 7 = z ^ e)
    (hLIO : IO.LIO Ksz (reqRecs lblc hc lmb) (respRecs lblm hm)) :
    SeedCoupled lmb lblc hc lblm hm z := by
  obtain ⟨_, _, hperm⟩ := hLIO
  exact ⟨fun v hv => hperm.mem_iff.mpr hv, fun v hv => hReqTs v (hperm.mem_iff.mpr hv)⟩

/-- A direct corollary of `SeedCoupled`: each
    served record's root fingerprint `(size, dyck, leaf) = (v 0, v 1, v 2)` (the `read_root`'s
    looked-up noun) equals that of a compute-requested record `w`.  This is precisely "the memory
    table's reconstructed record-roots ARE the compute's requested records", the `Def:MES` seed pin
    that the multiset-only coupling drops (the served record `v` is itself the witness `w`). -/
theorem seedCoupled_root_pin {lblc : ℕ → State × DTcomp K} {hc : ℕ}
    {lblm : ℕ → MState × DTmem K} {hm : ℕ} {z : K} (h : SeedCoupled lmb lblc hc lblm hm z) :
    ∀ v ∈ respRecs lblm hm, ∃ w ∈ reqRecs lblc hc lmb, (w 0, w 1, w 2) = (v 0, v 1, v 2) :=
  fun v hv => ⟨v, h.1 v hv, rfl⟩

/-- **The `NockVMROM` bundle corollary.**  This is the *un-linked* bundle: the
    conjunction of the two chips' walk-soundness and the IO biconditional over INDEPENDENT
    inputs.  It
    is exactly `V_NockVMROM` with the IO conjunct instantiated at fresh `req/resp` instead of
    `reqRecs/respRecs`, and with the per-row hypotheses given directly at the `Fcomp`/`Fmem`
    level rather than the RAP level.  Composes the two RAP chips.  Given
    (i) the compute walk's committed rows (encoded by an injective `encc`) laid out as a
    queue-valid tree (`hSfc`/`hvalidc` — discharged for genuine execution trees by
    `Walk.foCol_BFSValid`/`Walk.foCol_Sf_tiling`), arity-`3`, state-defined fanout, every row
    accepted by `L_comp = Fcomp` (`comp_stateSep`, `Thm:comp_38`); (ii) the analogous memory
    walk data over `L_mem = Fmem` (`mem_stateSep`, `Thm:mem_38`, arity `2`); and (iii) the IO
    record lists with unique request/response, THEN:

    * **compute chip is sound:** the walk-accepting-but-no-genuine-tree probability is
      `≤ hc/|K| + ε_RLC`;
    * **memory chip is sound:** likewise `≤ hm/|K| + ε_RLC`.  This
      bundle is stated only at `kroots = 1`; the multi-root `Corr:forest` composition is
      available (`Walk.Walk_IOP_forest_final_prob` / `walkBadForest_prob`) and is consumed by
      the integrated `V_NockVMROM_forest` below, not by this corollary;
    * **memory-execution IO linking:** the two IO columns are jointly RAP-satisfiable with the
      consistency checks (`requests = responses`, `out_mem = 0`) iff `(req, resp) ∈ L_IO`.
    ⚠️ These three conjuncts are over INDEPENDENT inputs (the `req/resp` here are NOT the compute
    walk's emitted requests / memory walk's responses) — this is a BUNDLE, not the paper's
    witness-shared integrated `V_NockVMROM` (shared IO columns + RAP→verifier bridges). -/
theorem NockVMROM
    {p : ℕ} [CharP K p]
    -- compute chip
    {ncs : ℕ} (encc : (State × DTcomp K) → (Fin ncs → K)) (hEncc : Function.Injective encc)
    (lblc : ℕ → State × DTcomp K) (clabc : ℕ → ℕ → State × DTcomp K) (foc : ℕ → ℕ)
    {hc : ℕ} (hSfc : Sf foc hc + 1 = hc) (hvalidc : BFSValid foc hc) (harityc : ∀ i, foc i ≤ 3)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (comp_stateSep (K := K)).fanout (lblc i).1)
    (hFc : ∀ i, 1 ≤ i → i ≤ hc →
      Fcomp (lblc i) (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
    -- memory chip
    {nms : ℕ} (encm : (MState × DTmem K) → (Fin nms → K)) (hEncm : Function.Injective encm)
    (lblm : ℕ → MState × DTmem K) (clabm : ℕ → ℕ → MState × DTmem K) (fom : ℕ → ℕ)
    {hm : ℕ} (hSfm : Sf fom hm + 1 = hm) (hvalidm : BFSValid fom hm) (haritym : ∀ i, fom i ≤ 2)
    (hfom : ∀ i, 1 ≤ i → i ≤ hm → fom i = (mem_stateSep (K := K)).fanout (lblm i).1)
    (hFm : ∀ i, 1 ≤ i → i ≤ hm →
      Fmem (lblm i) (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none))
    -- IO linking
    {M : ℕ} (Ksz : ℕ) (hKp : Ksz < p) (req resp : List (Fin M → K))
    (hKreq : IO.InRange Ksz req.length) (hKresp : resp.length ≤ Ksz)
    (hreqnd : req.Nodup) (hrespnd : resp.Nodup) :
    -- (1) compute chip soundness
    (((walkBad (comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (2) memory chip soundness
    ∧ (((walkBad (mem_stateSep (K := K)) encm lblm clabm fom hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (3) IO memory-execution linking (Thm:IO_result)
    ∧ ((∃ (m : Fin resp.length → ZMod p) (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt req i)) accP requests req.length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt resp i)) (IO.castμ m) accM
              responses out_mem resp.length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz req resp) := by
  refine ⟨?_, ?_, ?_⟩
  · exact walkBad_prob (comp_stateSep (K := K)) encc hEncc lblc clabc foc hSfc hvalidc harityc
      hfoc hFc
  · exact walkBad_prob (mem_stateSep (K := K)) encm hEncm lblm clabm fom hSfm hvalidm haritym
      hfom hFm
  · exact IO.io_result_LIO Ksz hKp req resp hKreq hKresp hreqnd hrespnd

/-- **The integrated `V_NockVMROM` capstone — witness-SHARED.**  This is the
    paper's `V_NockVMROM`, which differs from the bundle corollary above in two ways:

    * **(A) Shared IO witness.**  The IO conjunct (3) no longer ranges over fresh `req/resp`.
      It is fed `reqRecs lblc hc` (the compute walk's emitted memory-request records) and
      `respRecs lblm hm` (the memory walk's served records) — both literally functions of the
      same walk data `lblc`/`lblm` that soundness conjuncts (1)/(2) range over.  So the multiset
      the IO check certifies to lie in `L_IO` is the walks' *own* committed memory traffic.

    * **(B) RAP→verifier bridges wired in.**  The per-row hypotheses `hRc`/`hRm` are phrased at
      the RAP-satisfiability level (`∃ ex, RAPcomp …` / `∃ g, RAPmem …`), and the proof *derives*
      the `Fcomp`/`Fmem` labeling facts internally via `equiv_compute_sound`/`equiv_mem_sound`.
      This makes the `WF`-free forward bridges load-bearing.

    **What is proved vs assumed vs certified.**  Conjuncts (1)/(2) are *proved*: the walk-
    accepting-but-no-genuine-tree probability is `≤ h/|K| + ε_RLC` (honest bound), from
    `Walk_IOP_final` via `walkBad_prob`, given the per-row RAP-satisfiability + structural side
    conditions.  Conjunct (3) is the IO biconditional *certified* by `Thm:IO_result`
    (`io_result_LIO`): the two derived record lists are jointly RAP-satisfiable with the
    consistency checks (`requests = responses`, `out_mem = 0`) **iff** `(reqRecs, respRecs) ∈
    L_IO`.  We do NOT prove `reqRecs = respRecs` as sets — that equality is *exactly* what the IO
    check certifies (the biconditional is the endpoint, matching `cor_uni_req_uni_resp`).  The
    unique-request/response + range side conditions (`hKreq`/`hKresp`/`hreqnd`/`hrespnd`) are
    legitimately *assumed*, exactly as in `Thm:IO_result`.  No conjunct is weakened, the honest
    `+ ε_RLC` term is retained, and no `WF` is introduced.

    **Memory-chip scope.**  This capstone discharges the memory chip via the *single-root*
    `Walk_IOP_final` (`hSfm : Sf fom hm + 1 = hm` forces exactly ONE root) — the paper's *base*
    memory table.  It is the `kroots_m = 1` case of the multi-root
    `V_NockVMROM_forest` below, which covers subject-mutating
    programs.  The `kroots = 1` collapse is
    mechanized at BOTH layers: at the walk layer by `Walk.Walk_IOP_final_card_of_forest` /
    `Walk.ForestReconGoal_one`, and at the capstone layer by
    `walkBad_eq_walkBadForest_one : walkBad … = walkBadForest … 1` (the two walk-recognizer
    seeds are definitionally distinct but provably equal, so conjunct (2) here is literally the
    `kroots_m = 1` instance of `V_NockVMROM_forest`'s).  See
    `V_NockVMROM_forest`. -/
theorem V_NockVMROM
    {p : ℕ} [CharP K p]
    -- compute chip
    {ncs : ℕ} (encc : (State × DTcomp K) → (Fin ncs → K)) (hEncc : Function.Injective encc)
    (lblc : ℕ → State × DTcomp K) (clabc : ℕ → ℕ → State × DTcomp K) (foc : ℕ → ℕ)
    {hc : ℕ} (harityc : ∀ i, foc i ≤ 3)
    -- queue-length structural gate (discharges `Sf`-tiling + `BFSValid`)
    (qc qinvc : ℕ → K) (hqc : Walk.QGate foc qc qinvc 1 hc) (hwrapc : 1 + hc * 3 < p)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (comp_stateSep (K := K)).fanout (lblc i).1)
    -- per-row RAP satisfiability + structural side-conditions (the bridge is derived internally)
    (hRc : ∀ i, 1 ≤ i → i ≤ hc →
      (∃ ex, ComputeTable.RAPcomp (lblc i).2.1 (lblc i).2.2.1 (lblc i).2.2.2 ex)
        ∧ (lblc i).2.2.1.state = (lblc i).1
        ∧ (∀ j : Fin 3, (j : ℕ) < foc i ↔
            (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none)
        ∧ ComputeTable.childLinkComp (lblc i)
            (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
    -- memory chip
    {nms : ℕ} (encm : (MState × DTmem K) → (Fin nms → K)) (hEncm : Function.Injective encm)
    (lblm : ℕ → MState × DTmem K) (clabm : ℕ → ℕ → MState × DTmem K) (fom : ℕ → ℕ)
    {hm : ℕ} (haritym : ∀ i, fom i ≤ 2)
    -- queue-length structural gate for the (single-root) memory walk
    (qm qinvm : ℕ → K) (hqm : Walk.QGate fom qm qinvm 1 hm) (hwrapm : 1 + hm * 2 < p)
    (hfom : ∀ i, 1 ≤ i → i ≤ hm → fom i = (mem_stateSep (K := K)).fanout (lblm i).1)
    (hRm : ∀ i, 1 ≤ i → i ≤ hm →
      (∃ g, MemoryTable.RAPmem (lblm i).2.1 (lblm i).2.2 g)
        ∧ (lblm i).2.2.st = (lblm i).1
        ∧ (∀ j : Fin 2, (j : ℕ) < fom i ↔
            (if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) ≠ none)
        ∧ MemoryTable.childLinkMem (lblm i)
            (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none))
    -- IO linking over the SHARED derived record lists `reqRecs`/`respRecs`
    (Ksz : ℕ) (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz (reqRecs lblc hc lmb).length)
    (hKresp : (respRecs lblm hm).length ≤ Ksz)
    (hreqnd : (reqRecs lblc hc lmb).Nodup) (hrespnd : (respRecs lblm hm).Nodup) :
    -- (1) compute chip soundness
    (((walkBad (comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (2) memory chip soundness
    ∧ (((walkBad (mem_stateSep (K := K)) encm lblm clabm fom hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (3) IO memory-execution linking over the SHARED derived lists (Thm:IO_result)
    ∧ ((∃ (m : Fin (respRecs lblm hm).length → ZMod p) (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (reqRecs lblc hc lmb) i)) accP requests
              (reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (respRecs lblm hm) i)) (IO.castμ m) accM
              responses out_mem (respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz (reqRecs lblc hc lmb) (respRecs lblm hm)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1): derive the per-row `Fcomp` facts from RAP-satisfiability via `equiv_compute_sound`
    have hFc : ∀ i, 1 ≤ i → i ≤ hc →
        Fcomp (lblc i) (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) := by
      intro i h1 h2
      obtain ⟨hRAP, hstate, _, hlink⟩ := hRc i h1 h2
      refine ⟨hstate, ComputeTable.equiv_compute_sound _ _ _ hRAP, ?_, hlink⟩
      intro j
      have hf : fanoutComp (lblc i).1 = foc i := (hfoc i h1 h2).symm
      rw [hf]
      by_cases hj : (j : ℕ) < foc i <;> simp [hj]
    -- discharge `Sf`-tiling + `BFSValid` from the queue-length gate + no-wraparound bound
    have hsfle : Sf foc hc ≤ hc * 3 := Walk.Sf_le_mul harityc hc
    have hSfc : Sf foc hc + 1 = hc := Walk.Sf_tiling_of_qgate hqc (by omega) (by omega)
    have hvalidc : BFSValid foc hc := Walk.bfsValid_of_qgate hqc
    exact walkBad_prob (comp_stateSep (K := K)) encc hEncc lblc clabc foc hSfc hvalidc harityc
      hfoc hFc
  · -- (2): derive the per-row `Fmem` facts from RAP-satisfiability via `equiv_mem_sound`
    have hFm : ∀ i, 1 ≤ i → i ≤ hm →
        Fmem (lblm i) (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) := by
      intro i h1 h2
      obtain ⟨hRAP, hstate, _, hlink⟩ := hRm i h1 h2
      refine ⟨hstate, MemoryTable.equiv_mem_sound _ _ hRAP, ?_, hlink⟩
      intro j
      have hf : fanoutMem (lblm i).1 = fom i := (hfom i h1 h2).symm
      rw [hf]
      by_cases hj : (j : ℕ) < fom i <;> simp [hj]
    have hsmle : Sf fom hm ≤ hm * 2 := Walk.Sf_le_mul haritym hm
    have hSfm : Sf fom hm + 1 = hm := Walk.Sf_tiling_of_qgate hqm (by omega) (by omega)
    have hvalidm : BFSValid fom hm := Walk.bfsValid_of_qgate hqm
    exact walkBad_prob (mem_stateSep (K := K)) encm hEncm lblm clabm fom hSfm hvalidm haritym
      hfom hFm
  · -- (3): the IO biconditional over the SHARED derived lists (Thm:IO_result)
    exact IO.io_result_LIO Ksz hKp (reqRecs lblc hc lmb) (respRecs lblm hm) hKreq hKresp hreqnd hrespnd

/-- **`V_NockVMROM_seedcoupled` — the single-root capstone WITH the `Def:MES` seed coupling.**  Conjuncts (1)/(2)/(3) are VERBATIM `V_NockVMROM`'s (compute-chip
    soundness, single-root memory-chip soundness, shared-witness IO biconditional — re-derived by
    delegating to `V_NockVMROM`; un-weakened, honest `+ ε_RLC`, no `WF`).

    Conjunct (4) ADDS the seed coupling the base capstone drops: gated on the `Thm:IO_result`
    endpoint (`IO.LIO` — the served list is a `Perm` of the requested list) and the compute chip's
    closed-form request timestamps `z^i`, it delivers `SeedCoupled lmb lblc hc lblm hm z`
    — i.e. every served (reconstructed) memory record is, as-is, a compute request, and every served
    record's timestamp is the closed-form monomial `z^e`.  This is the
    coupling object downstream axis reasoning consumes (`AxisBridge.seedCoupled_tsExists_read`
    surfaces `TsNode`/`TsExists` on the reconstructed `read_root` nodes from it).  The gating exactly
    mirrors the axis capstones' conjunct (4) (`AxisBridge.V_NockVMROM_forest_axisvalid_*`): conjuncts
    (1)(2)(3) stay `V_NockVMROM` verbatim / ungated.  Axiom-clean. -/
theorem V_NockVMROM_seedcoupled
    {p : ℕ} [CharP K p]
    {ncs : ℕ} (encc : (State × DTcomp K) → (Fin ncs → K)) (hEncc : Function.Injective encc)
    (lblc : ℕ → State × DTcomp K) (clabc : ℕ → ℕ → State × DTcomp K) (foc : ℕ → ℕ)
    {hc : ℕ} (harityc : ∀ i, foc i ≤ 3)
    (qc qinvc : ℕ → K) (hqc : Walk.QGate foc qc qinvc 1 hc) (hwrapc : 1 + hc * 3 < p)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (comp_stateSep (K := K)).fanout (lblc i).1)
    (hRc : ∀ i, 1 ≤ i → i ≤ hc →
      (∃ ex, ComputeTable.RAPcomp (lblc i).2.1 (lblc i).2.2.1 (lblc i).2.2.2 ex)
        ∧ (lblc i).2.2.1.state = (lblc i).1
        ∧ (∀ j : Fin 3, (j : ℕ) < foc i ↔
            (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none)
        ∧ ComputeTable.childLinkComp (lblc i)
            (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
    {nms : ℕ} (encm : (MState × DTmem K) → (Fin nms → K)) (hEncm : Function.Injective encm)
    (lblm : ℕ → MState × DTmem K) (clabm : ℕ → ℕ → MState × DTmem K) (fom : ℕ → ℕ)
    {hm : ℕ} (haritym : ∀ i, fom i ≤ 2)
    (qm qinvm : ℕ → K) (hqm : Walk.QGate fom qm qinvm 1 hm) (hwrapm : 1 + hm * 2 < p)
    (hfom : ∀ i, 1 ≤ i → i ≤ hm → fom i = (mem_stateSep (K := K)).fanout (lblm i).1)
    (hRm : ∀ i, 1 ≤ i → i ≤ hm →
      (∃ g, MemoryTable.RAPmem (lblm i).2.1 (lblm i).2.2 g)
        ∧ (lblm i).2.2.st = (lblm i).1
        ∧ (∀ j : Fin 2, (j : ℕ) < fom i ↔
            (if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) ≠ none)
        ∧ MemoryTable.childLinkMem (lblm i)
            (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none))
    (Ksz : ℕ) (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz (reqRecs lblc hc lmb).length)
    (hKresp : (respRecs lblm hm).length ≤ Ksz)
    (hreqnd : (reqRecs lblc hc lmb).Nodup) (hrespnd : (respRecs lblm hm).Nodup) :
    -- (1) compute chip soundness
    (((walkBad (comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (2) memory chip soundness
    ∧ (((walkBad (mem_stateSep (K := K)) encm lblm clabm fom hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (3) IO memory-execution linking over the SHARED derived lists (Thm:IO_result)
    ∧ ((∃ (m : Fin (respRecs lblm hm).length → ZMod p) (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (reqRecs lblc hc lmb) i)) accP requests
              (reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (respRecs lblm hm) i)) (IO.castμ m) accM
              responses out_mem (respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz (reqRecs lblc hc lmb) (respRecs lblm hm))
    -- (4) the Def:MES SEED COUPLING, delivered from the IO endpoint + compute closed-form timestamps
    ∧ (IO.LIO Ksz (reqRecs lblc hc lmb) (respRecs lblm hm) →
        ∀ z : K, (∀ v ∈ reqRecs lblc hc lmb, ∃ e : ℕ, v 7 = z ^ e) →
          SeedCoupled lmb lblc hc lblm hm z) := by
  obtain ⟨h1, h2, h3⟩ :=
    V_NockVMROM encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc hfoc hRc
      encm hEncm lblm clabm fom haritym qm qinvm hqm hwrapm hfom hRm
      Ksz hKp hKreq hKresp hreqnd hrespnd
  exact ⟨h1, h2, h3, fun hLIO z hReqTs => seedCoupled_of_LIO lblc hc lblm hm z hReqTs hLIO⟩

/-- **The multi-root forest `V_NockVMROM_forest` capstone — witness-SHARED,
    subject-mutating programs.**  Identical to `V_NockVMROM` except the **memory chip** is
    discharged by the multi-root `Corr:forest` gadget (`Walk_IOP_forest_final`) instead of the
    single-root `Walk_IOP_final`.  For a subject-mutating Nock program (OP_2/7/8/9 — the common
    case) the memory table is a **forest** of `kroots_m` initial subject-formula nouns, not a
    single tree; conjunct (2) here bounds the forest bad-challenge set `walkBadForest` with tiling
    `kroots_m + Sf fom hm = hm` (`kroots_m` roots + all children = `hm` aggregate rows), so it
    covers membership in `∏_{i=1}^{kroots_m} L_RVT^{Fmem,2}`.

    The **compute chip** conjunct (1) is the same as in `V_NockVMROM` (the execution walk is single-root — one initial
    subject-formula), and so is the **IO** conjunct (3) (the shared `reqRecs`/`respRecs`
    linking via `Thm:IO_result`).  The single-root `V_NockVMROM` is the `kroots_m = 1` case of
    this theorem; the specialisation is mechanized at the walk level (`Walk_IOP_final_card_of_forest`,
    `ForestReconGoal_one`) — the two capstones are proved independently (see the `V_NockVMROM`
    docstring).  Honest bound `≤ hm/|K| + ε_RLC` retained; no conjunct weakened; axiom-clean. -/
theorem V_NockVMROM_forest
    {p : ℕ} [CharP K p]
    -- compute chip (single-root execution walk)
    {ncs : ℕ} (encc : (State × DTcomp K) → (Fin ncs → K)) (hEncc : Function.Injective encc)
    (lblc : ℕ → State × DTcomp K) (clabc : ℕ → ℕ → State × DTcomp K) (foc : ℕ → ℕ)
    {hc : ℕ} (harityc : ∀ i, foc i ≤ 3)
    -- queue-length structural gate for the (single-root) compute walk
    (qc qinvc : ℕ → K) (hqc : Walk.QGate foc qc qinvc 1 hc) (hwrapc : 1 + hc * 3 < p)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (comp_stateSep (K := K)).fanout (lblc i).1)
    (hRc : ∀ i, 1 ≤ i → i ≤ hc →
      (∃ ex, ComputeTable.RAPcomp (lblc i).2.1 (lblc i).2.2.1 (lblc i).2.2.2 ex)
        ∧ (lblc i).2.2.1.state = (lblc i).1
        ∧ (∀ j : Fin 3, (j : ℕ) < foc i ↔
            (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none)
        ∧ ComputeTable.childLinkComp (lblc i)
            (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
    -- memory chip (MULTI-ROOT FOREST — kroots_m initial subject-formula nouns)
    {nms : ℕ} (encm : (MState × DTmem K) → (Fin nms → K)) (hEncm : Function.Injective encm)
    (lblm : ℕ → MState × DTmem K) (clabm : ℕ → ℕ → MState × DTmem K) (fom : ℕ → ℕ)
    {kroots_m hm : ℕ} (hkm : 1 ≤ kroots_m) (haritym : ∀ i, fom i ≤ 2)
    -- queue-length structural gate for the multi-root (kroots_m-root) memory forest walk
    (qm qinvm : ℕ → K) (hqm : Walk.QGate fom qm qinvm kroots_m hm)
    (hwrapm : kroots_m + hm * 2 < p)
    (hfom : ∀ i, 1 ≤ i → i ≤ hm → fom i = (mem_stateSep (K := K)).fanout (lblm i).1)
    (hRm : ∀ i, 1 ≤ i → i ≤ hm →
      (∃ g, MemoryTable.RAPmem (lblm i).2.1 (lblm i).2.2 g)
        ∧ (lblm i).2.2.st = (lblm i).1
        ∧ (∀ j : Fin 2, (j : ℕ) < fom i ↔
            (if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) ≠ none)
        ∧ MemoryTable.childLinkMem (lblm i)
            (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none))
    -- IO linking over the SHARED derived record lists `reqRecs`/`respRecs`
    (Ksz : ℕ) (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz (reqRecs lblc hc lmb).length)
    (hKresp : (respRecs lblm hm).length ≤ Ksz)
    (hreqnd : (reqRecs lblc hc lmb).Nodup) (hrespnd : (respRecs lblm hm).Nodup) :
    -- (1) compute chip soundness (single-root)
    (((walkBad (comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (2) memory chip soundness (MULTI-ROOT forest, kroots_m roots)
    ∧ (((walkBadForest (mem_stateSep (K := K)) encm lblm clabm fom kroots_m hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (3) IO memory-execution linking over the SHARED derived lists (Thm:IO_result)
    ∧ ((∃ (m : Fin (respRecs lblm hm).length → ZMod p) (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (reqRecs lblc hc lmb) i)) accP requests
              (reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (respRecs lblm hm) i)) (IO.castμ m) accM
              responses out_mem (respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz (reqRecs lblc hc lmb) (respRecs lblm hm)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1): compute chip, single-root (identical to V_NockVMROM)
    have hFc : ∀ i, 1 ≤ i → i ≤ hc →
        Fcomp (lblc i) (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) := by
      intro i h1 h2
      obtain ⟨hRAP, hstate, _, hlink⟩ := hRc i h1 h2
      refine ⟨hstate, ComputeTable.equiv_compute_sound _ _ _ hRAP, ?_, hlink⟩
      intro j
      have hf : fanoutComp (lblc i).1 = foc i := (hfoc i h1 h2).symm
      rw [hf]
      by_cases hj : (j : ℕ) < foc i <;> simp [hj]
    have hsfle : Sf foc hc ≤ hc * 3 := Walk.Sf_le_mul harityc hc
    have hSfc : Sf foc hc + 1 = hc := Walk.Sf_tiling_of_qgate hqc (by omega) (by omega)
    have hvalidc : BFSValid foc hc := Walk.bfsValid_of_qgate hqc
    exact walkBad_prob (comp_stateSep (K := K)) encc hEncc lblc clabc foc hSfc hvalidc harityc
      hfoc hFc
  · -- (2): memory chip, MULTI-ROOT forest via `walkBadForest_prob`
    have hFm : ∀ i, 1 ≤ i → i ≤ hm →
        Fmem (lblm i) (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) := by
      intro i h1 h2
      obtain ⟨hRAP, hstate, _, hlink⟩ := hRm i h1 h2
      refine ⟨hstate, MemoryTable.equiv_mem_sound _ _ hRAP, ?_, hlink⟩
      intro j
      have hf : fanoutMem (lblm i).1 = fom i := (hfom i h1 h2).symm
      rw [hf]
      by_cases hj : (j : ℕ) < fom i <;> simp [hj]
    -- discharge forest tiling + `BFSValidF` from the queue-length gate + no-wraparound bound
    have hsmle : Sf fom hm ≤ hm * 2 := Walk.Sf_le_mul haritym hm
    have hSfm : kroots_m + Sf fom hm = hm := Walk.SfF_tiling_of_qgate hqm (by omega) (by omega)
    have hvalidm : BFSValidF kroots_m fom hm := Walk.bfsValidF_of_qgate hkm hqm
    exact walkBadForest_prob (mem_stateSep (K := K)) encm hEncm lblm clabm fom hkm hSfm hvalidm
      haritym hfom hFm
  · -- (3): the IO biconditional over the SHARED derived lists (Thm:IO_result)
    exact IO.io_result_LIO Ksz hKp (reqRecs lblc hc lmb) (respRecs lblm hm) hKreq hKresp hreqnd hrespnd

/-! ### Aggregate cost & security figures

  The aggregate cost/security figures are documented `def`s referencing the
  table structure and the NPR collision bound + parameters.  The concrete Goldilocks
  instantiation (`e = 3`, `|K| = p³ ≈ 2¹⁹²`) is isolated below; only *it* pulls in
  `Field.goldilocks_prime`. -/

/-- Extension order for the Goldilocks cubic: `e = 3`. -/
def extOrder : ℕ := 3

/-- Aggregate `RAP_NockComp-IO` column count: `62·e + 13`. -/
def comp_io_columns (e : ℕ) : ℕ := 62 * e + 13
/-- Aggregate `RAP_NockComp-IO` degree-4 gate count: `24·e + 15`. -/
def comp_io_deg4_gates (e : ℕ) : ℕ := 24 * e + 15
/-- Aggregate `RAP_NockMem-IO` column count: `61·e + 13`. -/
def mem_io_columns (e : ℕ) : ℕ := 61 * e + 13
/-- Aggregate `RAP_NockMem-IO` degree-4 gate count: `24·e + 16`. -/
def mem_io_deg4_gates (e : ℕ) : ℕ := 24 * e + 16

/-- Total field elements per row across both chips (paper §5 headline: `395`). -/
def total_row_elements : ℕ := comp_io_columns extOrder + mem_io_columns extOrder
/-- Total degree-4 gates across both chips (paper §5 headline: `175`). -/
def total_deg4_gates : ℕ := comp_io_deg4_gates extOrder + mem_io_deg4_gates extOrder

/-- **Security parameters** (paper §5): noun size bound `Λ = 2⁹`, opcode/record count bound
    `k = 2³¹`, over Goldilocks `|K| = p³ ≈ 2¹⁹²`, giving ≈ `121`-bit security. -/
def Λ : ℕ := 2 ^ 9
def kbound : ℕ := 2 ^ 31
def security_bits : ℕ := 121

end NockVM

end Nock

#print axioms Nock.NockVM.V_NockVMROM
#print axioms Nock.NockVM.V_NockVMROM_forest
#print axioms Nock.Walk.Walk_IOP_forest_final_prob
-- `Corr:forest` at `kroots = 1`: the capstone-layer collapse of the forest recognizer.
#print axioms Nock.NockVM.walkBad_eq_walkBadForest_one
-- Def:MES SEED COUPLING: the forward per-record seed pin + TsNode surfacing.
#print axioms Nock.NockVM.seedCoupled_of_LIO
#print axioms Nock.NockVM.seedCoupled_root_pin
#print axioms Nock.NockVM.V_NockVMROM_seedcoupled
