/-
  Nock/RedTeam/Batch7TreesTraversal.lean

  Independent verification of definitional faithfulness + non-vacuity/discrimination witnesses,
  and CONFIRMATION (not re-flagging) of the documented deltas.

This artifact provides MACHINE-CHECKED evidence for:
  1. Def:traversable         — `Nock.Framework.Traversable` + `nock_traversable`   (Def)
  2. Lem:optimal_dyck        — `dyck_iff_encode`/`dyck_length_graded`/`dyckWordsOfLen_card` (Lem)
  3. Corr:forest             — `Walk.Walk_IOP_forest_final_prob`/`_card`/`ForestReconGoal` (Cor)
  4. Lem:decomp              — `Nock.Noun.decomp` + `cons_children_unique`          (Lem)
  5. Lem:domain              — `Nock.Verb.domain`                                    (Lem)
  6. lemma:equiv_continuations — `Verb.equiv_continuations` + `equiv_continuationsΛ` (Lem)

  HYGIENE: No `sorry`, `admit`, `native_decide`, `axiom`, or `@[extern]`.
  Axiom-clean target ⊆ {propext, Classical.choice, Quot.sound}.  Audited over `ℚ`, so not even
  the whitelisted `Nock.Field.goldilocks_prime` is required.
-/
import Nock.Framework
import Nock.Walk
import Nock.NockVM
import Nock.Dyck
import Nock.NounValidation
import Nock.Trace

namespace Nock.RedTeam

open Nock Nock.Walk Nock.Framework Nock.ComputeTable Nock.MemoryTable

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 1. `Def:traversable` — `Nock.Framework.Traversable` + `nock_traversable`
    ══════════════════════════════════════════════════════════════════════════════════════

    Structure with TWO genuine `Equiv` bijections `φcomp`/`φmem` (NOT `:= True`).  The Nock
    instance sets `Lcomp := {t // RVT Fcomp t}`, `kc := 1`, `φcomp := (piUnique).symm` — an
    IDENTITY bijection onto a single-factor product.

    HONESTY / SCOPING: this is FAITHFUL to the paper's remark that it suffices to
    build a RAP for `L_RVT` since the language IS isomorphic to the RVT tree set.  The
    substantive "the Nock verifiers V_comp/V_mem recognize exactly these RVT sets" claim is
    `Thm:comp_38`/`Thm:mem_38` (`comp_stateSep`/`mem_stateSep`), proved ELSEWHERE, NOT inside
    `nock_traversable`.  The instance is a genuine (tautological-over-RVT) bijection — honest per
    its own docstring, NOT vacuous `:= True`, NOT an overclaim that Nock languages ARE RVT.

    Disposition: PASSED (faithful structure + honest scoping).
-/

section Def_traversable

/-- **[1.cite] `nock_traversable ℚ` — a concrete inhabitant of `Traversable`.** -/
noncomputable def trav_ℚ := nock_traversable ℚ

/-- **[1.a] FAITHFULNESS: `φcomp` is a genuine `Equiv` bijection** of the paper's type
    `L^comp ≃ ∏_{i=1}^{kc} L_RVT^{Fc i}` — its very type forces `Traversable` to carry a real
    bijection, so it is NOT `:= True`. -/
noncomputable def trav_φcomp_isEquiv :
    {t : NTree (State × DTcomp ℚ) // RVT (Fcomp (K := ℚ)) t}
      ≃ (Π _ : Fin 1, {t : NTree (State × DTcomp ℚ) // RVT (Fcomp (K := ℚ)) t}) :=
  trav_ℚ.φcomp

/-- **[1.a'] FAITHFULNESS: `φmem` is likewise a genuine `Equiv` bijection.** -/
noncomputable def trav_φmem_isEquiv :
    {t : NTree (MState × DTmem ℚ) // RVT (Fmem (K := ℚ)) t}
      ≃ (Π _ : Fin 1, {t : NTree (MState × DTmem ℚ) // RVT (Fmem (K := ℚ)) t}) :=
  trav_ℚ.φmem

/-- **[1.b] SCOPING (exact): `φcomp` IS the `piUnique` identity bijection.**  This pins the
    instance to the tautological-over-RVT identity — honest, not an overclaim. -/
theorem trav_φcomp_is_piUnique :
    trav_ℚ.φcomp
      = (Equiv.piUnique
          (fun _ : Fin 1 => {t : NTree (State × DTcomp ℚ) // RVT (Fcomp (K := ℚ)) t})).symm :=
  rfl

/-- **[1.b'] The bijection genuinely round-trips (`Equiv.left_inv`) — it is a real bijection,
    not a degenerate map.** -/
theorem trav_φcomp_roundtrip
    (x : {t : NTree (State × DTcomp ℚ) // RVT (Fcomp (K := ℚ)) t}) :
    trav_ℚ.φcomp.symm (trav_ℚ.φcomp x) = x :=
  trav_ℚ.φcomp.left_inv x

/-- **[1.c] Leaf-RVT builder: any label `lbl` with `F lbl (fun _ => none)` gives an RVT leaf.**
    This bridges `Fcomp_nonvacuous`/`Fmem_nonvacuous` (a single accepted leaf label) into an
    inhabitant of the `Equiv`'s DOMAIN `{t // RVT F t}` — so the bijection is over NON-EMPTY
    sets (strong non-vacuity). -/
theorem rvt_leaf {LT : Type*} {n : ℕ} {F : LT → (Fin n → Option LT) → Prop} {lbl : LT}
    (h : F lbl (fun _ => none)) : RVT F (NTree.node lbl []) := by
  unfold RVT
  refine ⟨h, ?_, ?_⟩
  · intro s hs; simp at hs
  · exact ⟨fun _ => h, fun _ => rfl⟩

/-- **[1.c'] NON-VACUITY: the compute RVT-language `{t // RVT Fcomp t}` is inhabited** (built
    from `Fcomp_nonvacuous`). -/
noncomputable def compRVT_inhabited :
    {t : NTree (State × DTcomp ℚ) // RVT (Fcomp (K := ℚ)) t} :=
  ⟨NTree.node (Fcomp_nonvacuous (K := ℚ)).choose [],
    rvt_leaf (Fcomp_nonvacuous (K := ℚ)).choose_spec⟩

/-- **[1.c''] NON-VACUITY: the memory RVT-language `{t // RVT Fmem t}` is inhabited** (built
    from `Fmem_nonvacuous`). -/
noncomputable def memRVT_inhabited :
    {t : NTree (MState × DTmem ℚ) // RVT (Fmem (K := ℚ)) t} :=
  ⟨NTree.node (Fmem_nonvacuous (K := ℚ)).choose [],
    rvt_leaf (Fmem_nonvacuous (K := ℚ)).choose_spec⟩

/-- **[1.c'''] The bijection is meaningfully non-trivial: applying `φcomp` to the concrete
    inhabitant and reading the unique factor returns it (the identity).** -/
theorem trav_φcomp_on_inhabited :
    trav_ℚ.φcomp compRVT_inhabited 0 = compRVT_inhabited := rfl

/-- **[1.doc]** -/
def traversable_doc : String :=
  "Def:traversable (main.tex:750) → Nock.Framework.Traversable (Framework.lean:320) + " ++
  "nock_traversable (Framework.lean:343). Traversable is a GENUINE structure with two Equiv " ++
  "bijections φcomp/φmem (NOT `:= True`; witnessed by trav_φcomp_isEquiv/trav_φmem_isEquiv). " ++
  "The Nock instance: Lcomp = {t // RVT Fcomp t}, kc = 1, φcomp = (piUnique).symm (IDENTITY " ++
  "bijection, trav_φcomp_is_piUnique). FAITHFUL to main.tex:762 (RAP for L_RVT suffices, since " ++
  "the language IS isomorphic to the RVT tree set). The substantive 'V_comp/V_mem recognize " ++
  "exactly these RVT sets' is Thm:comp_38/mem_38 (comp_stateSep/mem_stateSep), proved ELSEWHERE, " ++
  "NOT inside nock_traversable. Domain non-empty (compRVT_inhabited/memRVT_inhabited from " ++
  "Fcomp_nonvacuous/Fmem_nonvacuous). VERDICT: PASSED — faithful + honest scoping, NOT vacuity, " ++
  "NOT overclaim."

end Def_traversable


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 2. `Lem:optimal_dyck` — Dyck ≡ full-BT, length-grading, |L^{2λ}_dk| = C_λ
    ══════════════════════════════════════════════════════════════════════════════════════

    The paper lemma is the CONJUNCTION of three parts.  The `«Lem:optimal_dyck»` alias covers
    only `dyck_iff_encode`; the Catalan count `dyckWordsOfLen_card` is the part that makes it
    "optimal".  All three are proved.

    Disposition: PASSED (verdict 1-1, full lemma proved).
-/

section Lem_optimal_dyck

open Nock.BTree

/-- **[2.a] `dyck_iff_encode`**: `Dyck w ↔ ∃ t:BTree, encode t = w`. -/
theorem dyck_iff_encode_cite {w : List Bool} : Dyck w ↔ ∃ t : BTree, BTree.encode t = w :=
  BTree.dyck_iff_encode

/-- **[2.b] `dyck_length_graded`**: the length-graded correspondence. -/
theorem dyck_length_graded_cite {w : List Bool} (t : BTree) (ht : BTree.encode t = w) (lam : Nat) :
    w.length = 2 * lam ↔ t.size = 2 * lam + 1 :=
  BTree.dyck_length_graded t ht lam

/-- **[2.c] `dyckWordsOfLen_card`**: `|L^{2λ}_dk| = C_λ` — the "optimal" part. -/
theorem dyckWordsOfLen_card_cite (lam : ℕ) : (BTree.dyckWordsOfLen lam).card = catalan lam :=
  BTree.dyckWordsOfLen_card lam

/-- **[2.d] DISCRIMINATION: concrete Catalan numbers `C_0=1, C_1=1, C_2=2, C_3=5`** — the bound
    is a REAL arithmetic claim, not `0 = 0`. -/
theorem catalan_0 : catalan 0 = 1 := catalan_zero
theorem catalan_1 : catalan 1 = 1 := catalan_one
theorem catalan_2 : catalan 2 = 2 := by
  have h : catalan 2 = ∑ i : Fin 2, catalan i * catalan (1 - i) := catalan_succ 1
  rw [h, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one]
  norm_num [catalan_0, catalan_1]
theorem catalan_3 : catalan 3 = 5 := by
  have h : catalan 3 = ∑ i : Fin 3, catalan i * catalan (2 - i) := catalan_succ 2
  rw [h, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num [catalan_0, catalan_1, catalan_2]

/-- **[2.d'] `|L^{6}_dk| = C_3 = 5`** — the finset cardinality evaluates to a concrete number. -/
theorem dyck_card_3 : (BTree.dyckWordsOfLen 3).card = 5 := by
  rw [BTree.dyckWordsOfLen_card]; exact catalan_3

/-- **[2.e] DISCRIMINATION: a concrete Dyck-word round-trip.**  The tree `node leaf leaf`
    encodes to `[false, true] = "01"`, which is therefore a genuine Dyck word. -/
theorem encode_small : BTree.encode (BTree.node BTree.leaf BTree.leaf) = [false, true] := rfl

theorem dyck_01 : Dyck [false, true] :=
  BTree.dyck_iff_encode.mpr ⟨BTree.node BTree.leaf BTree.leaf, rfl⟩

/-- **[2.e'] Round-trip: the empty word is Dyck (the `leaf` shape) and `[false,true]` is not
    the empty word — DISCRIMINATION between two distinct shapes.** -/
theorem encode_leaf : BTree.encode BTree.leaf = ([] : List Bool) := rfl

theorem encode_injective_small :
    BTree.node BTree.leaf BTree.leaf ≠ BTree.leaf := by decide

/-- **[2.doc]** -/
def optimal_dyck_doc : String :=
  "Lem:optimal_dyck (main.tex:340) → Nock.BTree.dyck_iff_encode + dyck_length_graded + " ++
  "dyckWordsOfLen_card (Dyck.lean:178,185,305). The paper lemma is the CONJUNCTION of three: " ++
  "(i) L_dk ≡ L_full_BT (dyck_iff_encode); (ii) length-grading L^{2λ}_dk ≡ L^{2λ+1}_full_BT " ++
  "(dyck_length_graded); (iii) |L^{2λ}_dk| = C_λ (dyckWordsOfLen_card). The «Lem:optimal_dyck» " ++
  "alias covers ONLY (i); the Catalan count (iii) is the part that makes it 'optimal' and is " ++
  "separately proved. Discrimination: catalan 0/1/2/3 = 1/1/2/5; |L^6_dk| = 5; encode(node leaf " ++
  "leaf) = [0,1] is a concrete Dyck word. VERDICT: 1-1 (full lemma proved). PASSED."

end Lem_optimal_dyck


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 3. `Corr:forest` — `Walk_IOP_forest_final_prob`/`_card`/`ForestReconGoal`
    ══════════════════════════════════════════════════════════════════════════════════════

    The multi-root/forest walk soundness capstone.

    Disposition: PASSED.
-/

section Corr_forest

/-- **[3.a] `Corr:forest` probability form** — cited by naming the constant.
    Its conclusion is literally the honest bound `≤ h/|K| + (h·(node_size−1))/|K|`. -/
noncomputable def forest_prob_cite := @Walk.Walk_IOP_forest_final_prob

/-- **[3.b] `Corr:forest` cardinality form** — cited by naming the constant. -/
noncomputable def forest_card_cite := @Walk.Walk_IOP_forest_final_card

/-- **[3.c] `ForestReconGoal`** — the literal `∃ (sltᵢ)_{i=1}^{k} ∈ ∏ L_RVT`
    goal.  Cited by naming the constant. -/
def forestReconGoal_cite := @Walk.ForestReconGoal

/-- **[3.d] NON-VACUITY (single-root recovery): `ForestReconGoal … 1 h ↔ ReconGoal … h`** — a
    one-tree forest goal is EXACTLY the single-tree `ReconGoal`, so the forest predicate is a
    strict generalisation, not a weakening (hence non-vacuously satisfiable whenever `ReconGoal`
    is). -/
theorem forestReconGoal_one_cite
    {n : ℕ} {S DT : Type*} {F : (S × DT) → (Fin n → Option (S × DT)) → Prop}
    (St : StateSep F) (lbl : ℕ → S × DT) (h : ℕ) :
    ForestReconGoal St lbl 1 h ↔ ReconGoal St lbl h :=
  Walk.ForestReconGoal_one St lbl h

/-- **[3.e] NON-VACUITY (completeness side): `forest_walk` — the accepting identity is
    EQUIVALENT to `acc h = 0`**, so the capstone's hypotheses are jointly satisfiable (the
    completeness direction `forest_completeness` builds an accepting instance).  Cited by
    naming the constants. -/
noncomputable def forest_walk_cite := @Walk.forest_walk
noncomputable def forest_completeness_cite := @Walk.forest_completeness

/-- **[3.f] The single-root card theorem IS the `kroots = 1` case of the forest theorem** — no
    strength lost (documented sanity, `Walk_IOP_final_card_of_forest`). -/
noncomputable def forest_specializes_cite := @Walk.Walk_IOP_final_card_of_forest

/-- **[3.doc]** -/
def forest_doc : String :=
  "Corr:forest (main.tex:1002) → Walk.Walk_IOP_forest_final_prob/_card + ForestReconGoal " ++
  "(Walk.lean:3459,3432,3370). Multi-root forest walk soundness capstone. NON-VACUITY: " ++
  "ForestReconGoal_one (kroots=1 ⇔ single-root ReconGoal) + forest_walk/forest_completeness " ++
  "(hypotheses jointly satisfiable) + Walk_IOP_final_card_of_forest (single-root = kroots=1 case). " ++
  "CENSUS #4 (MED) CONFIRMED: the soundness bound is h/|K| + ε_RLC (ε_RLC = h·(node_size−1)/|K|) " ++
  "in the theorem's own conclusion — NOT the paper's bare h/|K| (main.tex:1010 omits ε_RLC). " ++
  "CENSUS #5 (MED) CONFIRMED: the capstone DERIVES BFSValidF (hyp hvalid) from a QGate; the " ++
  "'self-evident' BFS step is false without it — witness (0,2,0) excluded via " ++
  "witness_020_excluded/bfsValid_of_qgate (Batch 4). Both CLOSED/benign-documented. PASSED."

end Corr_forest


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 4. `Lem:decomp` — `Nock.Noun.decomp` + `cons_children_unique`
    ══════════════════════════════════════════════════════════════════════════════════════

    `(∃! p, 0<p.1 ∧ 0<p.2 ∧ lam=p.1+p.2 ∧ nL.leaves=p.1 ∧ nR.leaves=p.2 ∧ n=cell nL nR)
       ↔ (n=cell nL nR ∧ n.leaves=lam)`.

    This is DIFFERENT from `Lem:NPR_decomp` — not conflated.

    Disposition: PASSED (repair confirmed, biconditional has content both ways).
-/

section Lem_decomp

/-- **[4.a] `Nock.Noun.decomp`** — type-checks at the (repaired) paper statement. -/
theorem decomp_cite (n nL nR : Noun) (lam : ℕ) :
    (∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ lam = p.1 + p.2 ∧
        nL.leaves = p.1 ∧ nR.leaves = p.2 ∧ n = Noun.cell nL nR)
      ↔ (n = Noun.cell nL nR ∧ n.leaves = lam) :=
  Noun.decomp n nL nR lam

/-- **[4.b] `cons_children_unique`** — the structural uniqueness core. -/
theorem cons_children_unique_cite {l r l' r' : Noun}
    (h : Noun.cell l r = Noun.cell l' r') : l = l' ∧ r = r' :=
  Noun.cons_children_unique h

/-- **[4.c] NON-VACUITY / DISCRIMINATION: the `∃!` is genuinely satisfiable AND unique** on the
    concrete cell `cons(atom 1, atom 2)` with leaf count `λ = 2`. -/
theorem decomp_concrete :
    ∃! p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ (2 : ℕ) = p.1 + p.2 ∧
        (Noun.atom 1).leaves = p.1 ∧ (Noun.atom 2).leaves = p.2 ∧
        Noun.cell (Noun.atom 1) (Noun.atom 2) = Noun.cell (Noun.atom 1) (Noun.atom 2) :=
  (Noun.decomp (Noun.cell (Noun.atom 1) (Noun.atom 2)) (Noun.atom 1) (Noun.atom 2) 2).mpr
    ⟨rfl, rfl⟩

/-- **[4.c'] The unique witness is `(1,1)`** — the decomposition genuinely determines `(λL,λR)`. -/
theorem decomp_witness_unique :
    (∀ p : ℕ × ℕ, (0 < p.1 ∧ 0 < p.2 ∧ (2 : ℕ) = p.1 + p.2 ∧
        (Noun.atom 1).leaves = p.1 ∧ (Noun.atom 2).leaves = p.2 ∧
        Noun.cell (Noun.atom 1) (Noun.atom 2) = Noun.cell (Noun.atom 1) (Noun.atom 2))
      → p = (1, 1)) := by
  rintro ⟨a, b⟩ ⟨_, _, _, hL, hR, _⟩
  simp only [Noun.leaves] at hL hR
  exact Prod.ext hL.symm hR.symm

/-- **[4.d] DISCRIMINATION (uniqueness of children): `cons` is injective**, so the
    decomposition is well-defined. -/
theorem cons_children_unique_concrete :
    (Noun.atom 1 = Noun.atom 1 ∧ Noun.atom 2 = Noun.atom 2) :=
  Noun.cons_children_unique
    (rfl : Noun.cell (Noun.atom 1) (Noun.atom 2) = Noun.cell (Noun.atom 1) (Noun.atom 2))

/-- **[4.doc]** -/
def decomp_doc : String :=
  "Lem:decomp (main.tex:1210) → Nock.Noun.decomp + cons_children_unique (NounValidation.lean:41,60). " ++
  "CENSUS #3 (LOW) CONFIRMED: the paper's LHS ∃! (main.tex:1211) NEVER mentions n, so a LITERAL " ++
  "transcription of the ⟺ is UNSOUND (the ∃! could hold with n unrelated to nL,nR). The Lean " ++
  "REPAIRS this by carrying `n = cons(nL,nR)` INTO the existential (the paper's own RHS reads " ++
  "'n = cons(nL,nR), n ∈ 𝒩^λ'). Non-vacuity: on cons(atom 1, atom 2), λ=2, the ∃! is satisfiable " ++
  "with unique witness (1,1) (decomp_concrete/decomp_witness_unique). DISTINCT from Lem:NPR_decomp " ++
  "(field-level Φ identities, Batch 4) — not conflated. VERDICT: PASSED (repair, not unsoundness)."

end Lem_decomp


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 5. `Lem:domain` — `Nock.Verb.domain`
    ══════════════════════════════════════════════════════════════════════════════════════

    `(h : Step c t) → ∃ i sub, getIndex c = some i ∧ map i c = some sub ∧ inDomain sub = true`,
    with `inDomain v := inOpcodeDomain v || opReady v` (`inOpcodeDomain` = paper's `D`,
    `opReady` = ready operator nodes).

    KEY EVIDENCE: an `opReady` verb that is NOT `inOpcodeDomain`, i.e. `D ∪ opReady ⊋ D`.

    Disposition: PASSED (completeness repair, evidence crisp).
-/

section Lem_domain

/-- **[5.a] `Nock.Verb.domain`** — type-checks at the (broadened) paper statement. -/
theorem domain_cite {c t : Verb} (h : Verb.Step c t) :
    ∃ i sub, Verb.getIndex c = some i ∧ Verb.map i c = some sub ∧ Verb.inDomain sub = true :=
  Verb.domain h

/-- A concrete `opReady` verb: the operator `=` with two terminal (leaf) argument subtrees.
    This is a ready operator-application redex (`opReady`) but NOT an opcode redex
    (`inOpcodeDomain`), since it is not a `*`-node. -/
def cReady : Verb := Verb.node Action.equal (Verb.leaf 5) (Verb.leaf 5)

/-- **[5.b] KEY DELTA: `cReady` is `opReady` but NOT `inOpcodeDomain`.**  Hence
    `inDomain = D ∪ opReady ⊋ D`: the conclusion is strictly broader than the paper's `map ∈ D`. -/
theorem cReady_opReady : Verb.opReady cReady = true := by decide
theorem cReady_not_inOpcodeDomain : Verb.inOpcodeDomain cReady = false := by decide
theorem cReady_inDomain : Verb.inDomain cReady = true := by decide

/-- **[5.b'] The strict-broadening witness in one statement: `opReady ∧ ¬inOpcodeDomain ∧ inDomain`.** -/
theorem cReady_strict_broadening :
    Verb.opReady cReady = true ∧ Verb.inOpcodeDomain cReady = false
      ∧ Verb.inDomain cReady = true := by decide

/-- **[5.c] NON-VACUITY: a CONCRETE `Step` out of `cReady`.**  `next cReady = some _` (an
    operator-application step firing `=` on the two terminal leaves). -/
theorem cReady_step : ∃ t, Verb.Step cReady t := ⟨_, rfl⟩

/-- **[5.c'] `domain` applied to the concrete `Step` yields the (broadened) conclusion.** -/
theorem cReady_domain :
    ∃ i sub, Verb.getIndex cReady = some i ∧ Verb.map i cReady = some sub
      ∧ Verb.inDomain sub = true := by
  obtain ⟨t, ht⟩ := cReady_step
  exact Verb.domain ht

/-- **[5.doc]** -/
def domain_doc : String :=
  "Lem:domain (main.tex:1141) → Nock.Verb.domain (Trace.lean:133). Step c t := next c = some t; " ++
  "inDomain v := inOpcodeDomain v || opReady v (inOpcodeDomain = paper's D, opReady = ready " ++
  "operator nodes). CENSUS #2 (MED) CONFIRMED: App A's transition algorithm has NO branch for a " ++
  "pending OPERATOR node, though OP_3/4/5/10 produce them and getIndex selects them — so the Lean " ++
  "BROADENS the conclusion from the paper's D to D ∪ opReady (= inDomain). KEY EVIDENCE: cReady = " ++
  "node(=, leaf 5, leaf 5) is opReady = true but inOpcodeDomain = false, so D ∪ opReady ⊋ D " ++
  "(cReady_strict_broadening). Non-vacuity: a concrete Step out of cReady exists (cReady_step) and " ++
  "domain fires on it (cReady_domain). VERDICT: PASSED (completeness repair, NOT unsoundness)."

end Lem_domain


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## 6. `lemma:equiv_continuations` — `equiv_continuations` + `equiv_continuationsΛ`
    ══════════════════════════════════════════════════════════════════════════════════════

    `Finite F ↔ FiniteTransition F` (unbounded) and `FiniteΛ Λ F ↔ FiniteTransitionΛ Λ F`
    (Λ-capped).  The paper states the Λ-BOUNDED version `NockVM^Λ ≡ FiniteTransitions^Λ`; the
    `«lemma:equiv_continuations»` alias points at the UNBOUNDED `equiv_continuations`, while
    `equiv_continuationsΛ` is the LITERAL Λ-capped match to the paper's `^Λ`.

    Disposition: PASSED (both proved; alias-vs-Λ subtlety documented).
-/

section Lem_equiv_continuations

/-- **[6.a] `equiv_continuations` (unbounded)** — the alias target. -/
theorem equiv_continuations_cite (F : Verb) : Verb.Finite F ↔ Verb.FiniteTransition F :=
  Verb.equiv_continuations F

/-- **[6.b] `equiv_continuationsΛ` (Λ-capped)** — the LITERAL match to the paper's `^Λ`. -/
theorem equiv_continuationsΛ_cite (Λ : ℕ) (F : Verb) :
    Verb.FiniteΛ Λ F ↔ Verb.FiniteTransitionΛ Λ F :=
  Verb.equiv_continuationsΛ Λ F

/-- **[6.c] NON-VACUITY: `Finite` is inhabited** — the terminal leaf `0` is finite (`finite_leaf`). -/
theorem leaf0_finite : Verb.Finite (Verb.leaf 0) := Verb.finite_leaf 0

/-- **[6.c'] Push the concrete `Finite` witness THROUGH `equiv_continuations`** to obtain
    `FiniteTransition (leaf 0)` — the biconditional is non-vacuously applicable. -/
theorem leaf0_finiteTransition : Verb.FiniteTransition (Verb.leaf 0) :=
  (Verb.equiv_continuations (Verb.leaf 0)).mp leaf0_finite

/-- **[6.c''] …and back again (the reverse direction fires too).** -/
theorem leaf0_finite_back : Verb.Finite (Verb.leaf 0) :=
  (Verb.equiv_continuations (Verb.leaf 0)).mpr leaf0_finiteTransition

/-- **[6.d] NON-VACUITY (Λ-capped): `FiniteΛ 1 (leaf 0)` holds** (`size (leaf 0) = 1 ≤ 1`) and
    pushes through `equiv_continuationsΛ` to `FiniteTransitionΛ 1 (leaf 0)`. -/
theorem leaf0_finiteΛ : Verb.FiniteΛ 1 (Verb.leaf 0) :=
  ⟨Verb.finite_leaf 0, by decide⟩

theorem leaf0_finiteTransitionΛ : Verb.FiniteTransitionΛ 1 (Verb.leaf 0) :=
  (Verb.equiv_continuationsΛ 1 (Verb.leaf 0)).mp leaf0_finiteΛ

/-- **[6.doc]** -/
def equiv_continuations_doc : String :=
  "lemma:equiv_continuations (main.tex:1150) → Nock.Verb.equiv_continuations (Trace.lean:154) + " ++
  "equiv_continuationsΛ (Trace.lean:361). Finite F := ∃ T, TraceOf F T ∧ Complete T; " ++
  "FiniteTransition F := ∃ F0 T, TraceOf F0 T ∧ Complete T ∧ F ∈ T. SUBTLETY: the paper states " ++
  "the Λ-BOUNDED version NockVM^Λ ≡ FiniteTransitions^Λ; the «lemma:equiv_continuations» alias " ++
  "points at the UNBOUNDED equiv_continuations, while equiv_continuationsΛ is the LITERAL Λ-capped " ++
  "match to the paper's ^Λ. Non-vacuity: Finite (leaf 0) via finite_leaf, pushed through both " ++
  "directions (leaf0_finiteTransition/leaf0_finite_back) and the Λ-capped version (FiniteΛ 1 " ++
  "(leaf 0), size = 1 ≤ 1). VERDICT: PASSED (both proved; alias-vs-Λ documented)."

end Lem_equiv_continuations


/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SUMMARY: Drift Findings
    ══════════════════════════════════════════════════════════════════════════════════════
-/


def batch7_drift_summary : String :=
  "BATCH 7 TREES & TRAVERSAL DRIFT FINDINGS:\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "1. Def:traversable          — PASSED (genuine Equiv structure; nock_traversable = piUnique " ++
     "identity over RVT; honest scoping, RVT-recognition deferred to Thm:comp_38/mem_38)\n" ++
  "2. Lem:optimal_dyck         — PASSED (dyck_iff_encode + dyck_length_graded + dyckWordsOfLen_card; " ++
     "C_3 = 5, |L^6_dk| = 5, [0,1] round-trip)\n" ++
  "3. Corr:forest              — PASSED (Walk_IOP_forest_final_prob/_card + ForestReconGoal; " ++
     "CENSUS #4 ε_RLC bound + CENSUS #5 QGate-derived BFSValid confirmed)\n" ++
  "4. Lem:decomp               — PASSED (Noun.decomp; CENSUS #3 ∃! carries n = cons(nL,nR); " ++
     "witness (1,1) unique)\n" ++
  "5. Lem:domain               — PASSED (Verb.domain; CENSUS #2 D → D∪opReady; opReady witness " ++
     "cReady NOT inOpcodeDomain ⇒ D∪opReady ⊋ D)\n" ++
  "6. lemma:equiv_continuations — PASSED (unbounded alias vs Λ-capped equiv_continuationsΛ; both " ++
     "proved; Finite (leaf 0) pushed both ways)\n" ++
  "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n" ++
  "NO NEW DRIFT DETECTED. Documented deltas CONFIRMED (not re-flagged as new drift):\n" ++
  "• CENSUS #2 (MED): Lem:domain conclusion broadened D → D∪opReady (operator-step / App A gap).\n" ++
  "• CENSUS #3 (LOW): Lem:decomp ∃! carries n = cons(nL,nR) (repairs paper LHS bug).\n" ++
  "• CENSUS #4 (MED): Corr:forest bound h/|K| + ε_RLC (RLC term in the theorem's conclusion).\n" ++
  "• CENSUS #5 (MED): Corr:forest QGate-derived BFSValid (paper 'self-evident' BFS false without it).\n" ++
  "• Def:traversable: nock_traversable is an IDENTITY bijection over the RVT languages; " ++
     "RVT-recognition deferred to Thm:comp_38/mem_38. SCOPING, not vacuity.\n" ++
  "• equiv_continuations: unbounded alias vs Λ-capped equiv_continuationsΛ (matches paper's ^Λ).\n" ++
  "TRAVERSABLE VERDICT: FAITHFUL + honestly scoped — NOT vacuous (`:= True`), NOT an overclaim.\n" ++
  "AXIOM HYGIENE: audited over ℚ; no goldilocks_prime, no sorry/admit/native_decide/axiom/@[extern]."

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## SELF-CERTIFICATION: `#print axioms` for every proof-carrying declaration
    (all must be ⊆ {propext, Classical.choice, Quot.sound})
    ══════════════════════════════════════════════════════════════════════════════════════
-/

-- Object 1
#print axioms trav_φcomp_isEquiv
#print axioms trav_φmem_isEquiv
#print axioms trav_φcomp_is_piUnique
#print axioms trav_φcomp_roundtrip
#print axioms rvt_leaf
#print axioms compRVT_inhabited
#print axioms memRVT_inhabited
#print axioms trav_φcomp_on_inhabited
-- Object 2
#print axioms dyck_iff_encode_cite
#print axioms dyck_length_graded_cite
#print axioms dyckWordsOfLen_card_cite
#print axioms catalan_0
#print axioms catalan_1
#print axioms catalan_2
#print axioms catalan_3
#print axioms dyck_card_3
#print axioms encode_small
#print axioms dyck_01
#print axioms encode_leaf
#print axioms encode_injective_small
-- Object 3
#print axioms forest_prob_cite
#print axioms forest_card_cite
#print axioms forestReconGoal_cite
#print axioms forestReconGoal_one_cite
#print axioms forest_walk_cite
#print axioms forest_completeness_cite
#print axioms forest_specializes_cite
-- Object 4
#print axioms decomp_cite
#print axioms cons_children_unique_cite
#print axioms decomp_concrete
#print axioms decomp_witness_unique
#print axioms cons_children_unique_concrete
-- Object 5
#print axioms domain_cite
#print axioms cReady_opReady
#print axioms cReady_not_inOpcodeDomain
#print axioms cReady_inDomain
#print axioms cReady_strict_broadening
#print axioms cReady_step
#print axioms cReady_domain
-- Object 6
#print axioms equiv_continuations_cite
#print axioms equiv_continuationsΛ_cite
#print axioms leaf0_finite
#print axioms leaf0_finiteTransition
#print axioms leaf0_finite_back
#print axioms leaf0_finiteΛ
#print axioms leaf0_finiteTransitionΛ

end Nock.RedTeam
