import Nock.GlobalCarryRecognizer
import Nock.FieldEmbedding
import Nock.Trace
import Mathlib.GroupTheory.OrderOfElement

/-!
# Per-opcode semantic containment for exact compute rows

`ComputeTable.Vcomp` checks field fingerprints and recursive-call wiring; it does not by itself
decode those fingerprints to nouns or assert that emitted memory requests were served.

* `Realizes` says that one table fingerprint is the NPR encoding of one concrete noun.
* `PairFaithful` is the collision/boundedness datum needed only when an equality of fingerprints
  must be reflected back to an equality of nouns.
* `RealizesMemRec` realizes the noun/axis coordinates of a non-padding memory record.
* OP0/OP9 take a `GlobalCarryAxis.ServedLookup`; the existing global-carry theorem turns that
  concrete memory witness into the required `Noun.slot` fact.

No global decoder `FP K → Noun` is postulated, and no hypothesis is an `evalFBy` conclusion for the
row being proved.  Recursive `evalFBy` premises are exactly the child calls recorded in `sf1..sf3`.

Opcode 10 is absent because `ComputeTable.State` is precisely `s0..s9, cons` and `StepROM` rejects
OP10.  Here `cons` is the structural formula-head case, not standard-Nock hint opcode 11.

Existing assembly points reused here:

* `ComputeTable.equiv_compute`: exact RAP satisfiability iff `Vcomp` (no operational semantics).
* `GlobalCarryRecognizer.formula_cons_sound`: accepted NPR cons equality to structural slots 2/3.
* `GlobalCarryRecognizer.axis_sound_recognizer'`: a served global-carry record to `Noun.slot`.
* `Verb.StepROM` / `Verb.step_of_stepROM` / `Verb.traceOf_of_traceOfROM`: ROM-step containment.
* `FieldEmbedding.evalFBy` and `noOverflow_agreeBy`: field-valued evaluation and its Nat agreement.

Coverage:

* `s0`: ROM step + `evalFBy`, using served `mr2`;
* `s1..s8`: ROM step + `evalFBy`, using exactly the live realized `sf` calls;
* `s9`: ROM step + `evalFBy`, using served `mr3`; the verifier's atom-shape gate and one
  pair-local NPR separation witness identify the axis noun;
* `cons`: structural ROM step + autocons `evalFBy`;
* opcode 10: intentionally absent from both `State` and ROM.
-/

namespace Nock.NockVMROM.Thm54.OpcodeSemantics

open Nock Nock.Noun
open ComputeTable

noncomputable abbrev enc {K : Type*} [Field K] :=
  GlobalCarryRecognizer.enc (K := K)

/-- One field fingerprint is realized by one concrete noun at NPR seed `z`. -/
def Realizes {K : Type*} [Field K] (z : K) (fp : FP K) (n : Noun) : Prop :=
  fp = enc z n

/-- The exact collision/boundedness package needed to reflect one fingerprint equality.

It is deliberately pair-local.  A global injectivity assumption for `enc` would be false over a
finite field and an unbounded noun universe. -/
structure PairFaithful {K : Type*} [Field K] (z : K) (q : ℕ)
    (left right : Noun) : Prop where
  separates : GlobalCarryRecognizer.SepSeed z left right
  left_bounded : FieldEmbedding.BoundedBy q left
  right_bounded : FieldEmbedding.BoundedBy q right

theorem PairFaithful.eq_of_enc_eq {K : Type*} [Field K] {z : K} {q : ℕ}
    {left right : Noun} (h : PairFaithful z q left right)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (heq : enc z left = enc z right) :
    left = right :=
  GlobalCarryRecognizer.noun_eq_of_enc_eq z left right
    h.separates hcast h.left_bounded h.right_bounded heq

/-- Realization of the always-live root row and the first formula decomposition. -/
structure RootRealization {K : Type*} [Field K]
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) where
  subject : Noun
  formula : Noun
  result : Noun
  head : Noun
  tail : Noun
  subject_realizes : Realizes inp.z pub.s subject
  formula_realizes : Realizes inp.z pub.f formula
  result_realizes : Realizes inp.z pub.e result
  head_realizes : Realizes inp.z dec.f_h head
  tail_realizes : Realizes inp.z dec.f_t tail

/-- Realization of one recursive-call triple `(subject, formula, evaluation)`. -/
structure CallRealization {K : Type*} [Field K] (z : K)
    (s f e : FP K) where
  subject : Noun
  formula : Noun
  result : Noun
  subject_realizes : Realizes z s subject
  formula_realizes : Realizes z f formula
  result_realizes : Realizes z e result

/-- Realization of the two children of the already-realized formula tail. -/
structure TailRealization {K : Type*} [Field K] (z : K) (dec : Dec K) where
  head : Noun
  tail : Noun
  head_realizes : Realizes z dec.f_th head
  tail_realizes : Realizes z dec.f_tt tail

/-- Realization of the second decomposition used only by OP6. -/
structure BranchTailRealization {K : Type*} [Field K] (z : K) (dec : Dec K) where
  head : Noun
  tail : Noun
  head_realizes : Realizes z dec.f_tth head
  tail_realizes : Realizes z dec.f_ttt tail

/-- Noun/axis realization of a non-padding compute-table memory record.

The timestamp remains a field value and is intentionally not interpreted here; timestamp
faithfulness belongs to `Thm54.RecordBridge`. -/
structure RealizesMemRec {K : Type*} [Field K] (z : K) (r : MemRec K)
    (root child : Noun) (axis : ℕ) : Prop where
  root_realizes : Realizes z r.root root
  child_realizes : Realizes z r.child child
  axis_realizes : r.axis = (axis : K)

/-- The bounded power window required by OP3/OP4 to infer "size = z" means one leaf.

This is separate from NPR collision separation: OP3's `qm` gate inspects only the size coordinate. -/
structure SizeWindow {K : Type*} [Field K] (z : K) (n : Noun) : Prop where
  one_lt_order : 1 < orderOf z
  leaves_lt_order : n.leaves < orderOf z

/-- Inside the certified power window, a noun whose size fingerprint is `z` is an atom. -/
theorem atom_of_enc_size_eq {K : Type*} [Field K] {z : K} {n : Noun}
    (hw : SizeWindow z n) (hsize : (enc z n).size = z) :
    ∃ k, n = .atom k := by
  cases n with
  | atom k => exact ⟨k, rfl⟩
  | cell l r =>
      have hp :
          (Noun.cell l r).leaves = 1 :=
        pow_injOn_Iio_orderOf
          (Set.mem_Iio.mpr hw.leaves_lt_order)
          (Set.mem_Iio.mpr hw.one_lt_order)
          (by simpa only [GlobalCarryRecognizer.enc_size, pow_one] using hsize)
      simp only [Noun.leaves] at hp
      have hl := l.one_le_leaves
      have hr := r.one_le_leaves
      omega

/-- A local NPR cons equation, under the pair-local good-seed event, is a genuine noun cell.

The proof intentionally goes through `GlobalCarryRecognizer.formula_cons_sound`, exposing both
axis-2 and axis-3 structural consequences before reassembling the cell. -/
theorem cell_eq_of_cons_encoding {K : Type*} [Field K] {z : K} {q : ℕ}
    (hz : z ≠ 0) (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (root left right : Noun)
    (hfaith : PairFaithful z q root (.cell left right))
    (hcons : FP.cons z (enc z left) (enc z right) = enc z root) :
    root = .cell left right := by
  have hslots :=
    GlobalCarryRecognizer.formula_cons_sound hz root left right
      hfaith.separates hcast hfaith.left_bounded
      hfaith.right_bounded.1 hfaith.right_bounded.2 hcons
  cases root with
  | atom k => simp [Noun.slot] at hslots
  | cell l r =>
      have hl : l = left := by simpa [Noun.slot] using hslots.1
      have hr : r = right := by simpa [Noun.slot] using hslots.2
      subst hl
      subst hr
      rfl

/-- `SVhead` plus a faithful noun realization identifies a numeric opcode head. -/
theorem numeric_head_eq {K : Type*} [Field K] {z : K} {q : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K} {st : State}
    (hstate : pub.state = st) (hne : st ≠ .cons)
    (head : Noun) (hreal : Realizes z dec.f_h head)
    (hz : inp.z = z) (hsv : SVhead inp pub dec)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hfaith : PairFaithful z q head (.atom st.toNat)) :
    head = .atom st.toNat := by
  have hsv' : headAtom dec inp.z (st.toNat : K) := by
    simpa only [SVhead, hstate, if_neg hne] using hsv
  have henc : enc z head = enc z (.atom st.toNat) := by
    calc
      enc z head = dec.f_h := hreal.symm
      _ = FP.atomFP inp.z (st.toNat : K) :=
        FP.ext hsv'.1 hsv'.2.1 hsv'.2.2
      _ = FP.atomFP z (st.toNat : K) := by rw [hz]
      _ = enc z (.atom st.toNat) :=
        (GlobalCarryRecognizer.enc_atom z st.toNat).symm
  exact hfaith.eq_of_enc_eq hcast henc

/-- The `cons` selector cannot be realized by an atom: `SVhead` requires nonzero Dyck coordinate. -/
theorem cons_head_is_cell {K : Type*} [Field K]
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .cons) (head : Noun)
    (hreal : Realizes inp.z dec.f_h head) (hsv : SVhead inp pub dec) :
    ∃ left right, head = .cell left right := by
  have hdyck : dec.f_h.dyck ≠ 0 := by
    simpa only [SVhead, hstate, if_pos, headCell] using hsv
  cases head with
  | atom k =>
      exfalso
      apply hdyck
      calc
        dec.f_h.dyck = (enc inp.z (.atom k)).dyck :=
          congrArg FP.dyck hreal
        _ = (FP.atomFP inp.z (k : K)).dyck :=
          congrArg FP.dyck (GlobalCarryRecognizer.enc_atom inp.z k)
        _ = 0 := rfl
  | cell left right => exact ⟨left, right, rfl⟩

/-! ## Generic row-realization reflectors -/

theorem noun_eq_of_realizes_eq {K : Type*} [Field K] {z : K} {q : ℕ}
    {fp₁ fp₂ : FP K} {left right : Noun}
    (hleft : Realizes z fp₁ left) (hright : Realizes z fp₂ right)
    (hfp : fp₁ = fp₂) (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hfaith : PairFaithful z q left right) :
    left = right := by
  apply hfaith.eq_of_enc_eq hcast
  calc
    enc z left = fp₁ := hleft.symm
    _ = fp₂ := hfp
    _ = enc z right := hright

/-- Every accepted realized row has an actual outer formula cell `[head tail]`. -/
theorem root_formula_eq_cell {K : Type*} [Field K] {q : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hz : inp.z ≠ 0) (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec)
    (hfaith : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (hv : Vcomp inp pub dec) :
    row.formula = .cell row.head row.tail := by
  obtain ⟨hformula, _, _, _, _⟩ := hv
  apply cell_eq_of_cons_encoding hz hcast row.formula row.head row.tail hfaith
  calc
    FP.cons inp.z (enc inp.z row.head) (enc inp.z row.tail) =
        FP.cons inp.z dec.f_h dec.f_t := by
          rw [← row.head_realizes, ← row.tail_realizes]
    _ = pub.f := hformula.symm
    _ = enc inp.z row.formula := row.formula_realizes

/-- Numeric-state specialization of `root_formula_eq_cell`: the realized formula is `[op tail]`. -/
theorem numeric_formula_eq {K : Type*} [Field K] {q : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K} {st : State}
    (hstate : pub.state = st) (hne : st ≠ .cons)
    (hz : inp.z ≠ 0) (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec)
    (hhead : PairFaithful inp.z q row.head (.atom st.toNat))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (hv : Vcomp inp pub dec) :
    row.formula = .cell (.atom st.toNat) row.tail := by
  have hv' := hv
  obtain ⟨_, _, hsv, _, _⟩ := hv'
  have hheadEq :=
    numeric_head_eq hstate hne row.head row.head_realizes rfl hsv hcast hhead
  rw [root_formula_eq_cell hz hcast row hformula hv, hheadEq]

/-- A realized nested tail cons equation is an actual noun cell. -/
theorem realized_tail_eq_cell {K : Type*} [Field K] {q : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hz : inp.z ≠ 0) (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec) (tail : TailRealization inp.z dec)
    (hfaith : PairFaithful inp.z q row.tail (.cell tail.head tail.tail))
    (hcons : FP.cons inp.z dec.f_th dec.f_tt = dec.f_t) :
    row.tail = .cell tail.head tail.tail := by
  apply cell_eq_of_cons_encoding hz hcast row.tail tail.head tail.tail hfaith
  calc
    FP.cons inp.z (enc inp.z tail.head) (enc inp.z tail.tail) =
        FP.cons inp.z dec.f_th dec.f_tt := by
          rw [← tail.head_realizes, ← tail.tail_realizes]
    _ = dec.f_t := hcons
    _ = enc inp.z row.tail := row.tail_realizes

/-- The second OP6 decomposition realizes `f_tt = [f_tth f_ttt]`. -/
theorem realized_branch_tail_eq_cell {K : Type*} [Field K] {q : ℕ}
    {inp : Inputs K} {dec : Dec K}
    (hz : inp.z ≠ 0) (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (tail : TailRealization inp.z dec) (branch : BranchTailRealization inp.z dec)
    (hfaith : PairFaithful inp.z q tail.tail (.cell branch.head branch.tail))
    (hcons : FP.cons inp.z dec.f_tth dec.f_ttt = dec.f_tt) :
    tail.tail = .cell branch.head branch.tail := by
  apply cell_eq_of_cons_encoding hz hcast tail.tail branch.head branch.tail hfaith
  calc
    FP.cons inp.z (enc inp.z branch.head) (enc inp.z branch.tail) =
        FP.cons inp.z dec.f_tth dec.f_ttt := by
          rw [← branch.head_realizes, ← branch.tail_realizes]
    _ = dec.f_tt := hcons
    _ = enc inp.z tail.tail := tail.tail_realizes

/-! ## Root-selected ROM steps

These lemmas are source-level and contain no table assumptions.  They are the target reached after
the row realization identifies the concrete formula shape.
-/

private theorem isTerminal_ofNoun (n : Noun) :
    Verb.isTerminal (Verb.ofNoun n) = true := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr =>
      simp only [Verb.ofNoun, Verb.isTerminal, Action.isNull, ihl, ihr, Bool.and_self]

private theorem getIndex_program (subject formula : Noun) :
    Verb.getIndex (Verb.program subject formula) = some 0 := by
  rw [Verb.getIndex_eq_some_iff]
  constructor
  · exact ⟨Verb.program subject formula, rfl, rfl⟩
  · intro j hj
    obtain ⟨v, hmap, hv⟩ := hj
    have hroot : Verb.map 0 (Verb.program subject formula) =
        some (Verb.program subject formula) := rfl
    by_cases hj0 : j = 0
    · subst hj0
      exact Nat.not_lt_zero 0
    · have hmem := Verb.mem_nodes_of_map hmap
      simp only [Verb.nodes, Verb.program, Verb.enum, List.mem_cons,
        List.mem_append] at hmem
      rcases hmem with hroot' | hleft | hright
      · exact (hj0 (congrArg Prod.fst hroot')).elim
      · have hnon :=
          Verb.enum_nonpending_of_terminal (Verb.ofNoun subject)
            (isTerminal_ofNoun subject) 1 (j, v) hleft
        simp [hv] at hnon
      · have hnon :=
          Verb.enum_nonpending_of_terminal (Verb.ofNoun formula)
            (isTerminal_ofNoun formula) (Verb.enum (Verb.ofNoun subject) 1).1
            (j, v) hright
        simp [hv] at hnon

private theorem nextROM_program_eq_reduceROM (subject formula : Noun)
    (hdom : Verb.inDomain (Verb.program subject formula) = true) :
    Verb.nextROM (Verb.program subject formula) =
      Verb.reduceROM (Verb.program subject formula) := by
  unfold Verb.nextROM
  rw [getIndex_program]
  simp only [show Verb.map 0 (Verb.program subject formula) =
    some (Verb.program subject formula) from rfl]
  rw [if_pos hdom]
  · cases h : Verb.reduceROM (Verb.program subject formula) with
    | none => rfl
    | some v =>
        simp only
        have hreplace : Verb.replaceAt 0 (Verb.program subject formula) v = v := by
          rfl
        rw [hreplace]

private theorem numeric_program_inDomain (subject tail : Noun) (op : ℕ) (hop : op < 11) :
    Verb.inDomain (Verb.program subject (.cell (.atom op) tail)) = true := by
  simp [Verb.inDomain, Verb.inOpcodeDomain, Verb.program, Verb.ofNoun, isTerminal_ofNoun,
    Verb.opHeadOk, Verb.isTerminal, Action.isNull, Verb.opReady, hop]

private theorem cons_program_inDomain (subject left right tail : Noun) :
    Verb.inDomain (Verb.program subject (.cell (.cell left right) tail)) = true := by
  simp [Verb.inDomain, Verb.inOpcodeDomain, Verb.program, Verb.ofNoun, isTerminal_ofNoun,
    Verb.opHeadOk, Verb.isTerminal, Action.isNull, Verb.opReady]

theorem stepROM_s0_exact (subject tail : Noun) :
    Verb.StepROM
      (Verb.program subject (.cell (.atom 0) tail))
      (.node .slot (Verb.ofNoun tail) (Verb.ofNoun subject)) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (numeric_program_inDomain subject tail 0 (by omega))]
  rfl

theorem stepROM_s1_exact (subject tail : Noun) :
    Verb.StepROM
      (Verb.program subject (.cell (.atom 1) tail))
      (Verb.ofNoun tail) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (numeric_program_inDomain subject tail 1 (by omega))]
  rfl

theorem stepROM_s2_exact (subject left right : Noun) :
    Verb.StepROM
      (Verb.program subject (.cell (.atom 2) (.cell left right)))
      (.node .star
        (.node .star (Verb.ofNoun subject) (Verb.ofNoun left))
        (.node .star (Verb.ofNoun subject) (Verb.ofNoun right))) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (numeric_program_inDomain subject (.cell left right) 2 (by omega))]
  rfl

theorem stepROM_s3_exact (subject tail : Noun) :
    Verb.StepROM
      (Verb.program subject (.cell (.atom 3) tail))
      (.node .minus (.leaf 3) (.node .star (Verb.ofNoun subject) (Verb.ofNoun tail))) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (numeric_program_inDomain subject tail 3 (by omega))]
  rfl

theorem stepROM_s4_exact (subject tail : Noun) :
    Verb.StepROM
      (Verb.program subject (.cell (.atom 4) tail))
      (.node .minus (.leaf 4) (.node .star (Verb.ofNoun subject) (Verb.ofNoun tail))) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (numeric_program_inDomain subject tail 4 (by omega))]
  rfl

theorem stepROM_s5_exact (subject left right : Noun) :
    Verb.StepROM
      (Verb.program subject (.cell (.atom 5) (.cell left right)))
      (.node .equal
        (.node .star (Verb.ofNoun subject) (Verb.ofNoun left))
        (.node .star (Verb.ofNoun subject) (Verb.ofNoun right))) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (numeric_program_inDomain subject (.cell left right) 5 (by omega))]
  rfl

/-- The paper's macro-expanded immediate successor for OP6. -/
def s6Successor (subject condition yesBranch noBranch : Noun) : Verb :=
  let inner := Verb.node .star (Verb.ofNoun subject)
    (.node .null (.leaf 4) (.node .null (.leaf 4) (Verb.ofNoun condition)))
  let d0 := Verb.node .null (.leaf 0) inner
  let c0 := Verb.node .star (.node .null (.leaf 2) (.leaf 3)) d0
  let b0 := Verb.node .null (.leaf 0) c0
  let a0 := Verb.node .star
    (.node .null (Verb.ofNoun yesBranch) (Verb.ofNoun noBranch)) b0
  .node .star (Verb.ofNoun subject) a0

theorem stepROM_s6_exact (subject condition yesBranch noBranch : Noun) :
    Verb.StepROM
      (Verb.program subject
        (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch))))
      (s6Successor subject condition yesBranch noBranch) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (numeric_program_inDomain subject
      (.cell condition (.cell yesBranch noBranch)) 6 (by omega))]
  rfl

theorem stepROM_s7_exact (subject first second : Noun) :
    Verb.StepROM
      (Verb.program subject (.cell (.atom 7) (.cell first second)))
      (.node .star
        (.node .star (Verb.ofNoun subject) (Verb.ofNoun first))
        (Verb.ofNoun second)) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (numeric_program_inDomain subject (.cell first second) 7 (by omega))]
  rfl

theorem stepROM_s8_exact (subject first second : Noun) :
    Verb.StepROM
      (Verb.program subject (.cell (.atom 8) (.cell first second)))
      (.node .star
        (.node .null
          (.node .star (Verb.ofNoun subject) (Verb.ofNoun first))
          (Verb.ofNoun subject))
        (Verb.ofNoun second)) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (numeric_program_inDomain subject (.cell first second) 8 (by omega))]
  rfl

theorem stepROM_s9_exact (subject : Noun) (axis : ℕ) (coreFormula : Noun) :
    Verb.StepROM
      (Verb.program subject (.cell (.atom 9) (.cell (.atom axis) coreFormula)))
      (.node .star
        (.node .star (Verb.ofNoun subject) (Verb.ofNoun coreFormula))
        (.node .null (.leaf 2)
          (.node .null
            (.node .null (.leaf 0) (.leaf 1))
            (.node .null (.leaf 0) (.leaf axis))))) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (numeric_program_inDomain subject (.cell (.atom axis) coreFormula) 9 (by omega))]
  rfl

theorem stepROM_cons_exact (subject headLeft headRight tail : Noun) :
    Verb.StepROM
      (Verb.program subject (.cell (.cell headLeft headRight) tail))
      (.node .null
        (.node .star (Verb.ofNoun subject) (Verb.ofNoun (.cell headLeft headRight)))
        (.node .star (Verb.ofNoun subject) (Verb.ofNoun tail))) := by
  unfold Verb.StepROM
  rw [nextROM_program_eq_reduceROM _ _
    (cons_program_inDomain subject headLeft headRight tail)]
  rfl

/-- Every proved immediate ROM step gives the canonical two-verb ROM trace. -/
theorem traceOfROM_pair {before after : Verb} (h : Verb.StepROM before after) :
    Verb.TraceOfROM before [before, after] := by
  exact ⟨rfl, h, trivial⟩

/-! ## Exact noun-level big-step closure rules

These are thin equation lemmas for `evalFBy`.  The row bridge below proves that `Vcomp`'s
fingerprint wiring realizes exactly these premises.
-/

theorem evalFBy_s0_exact {q fuel axis : ℕ} {subject result : Noun}
    (hslot : Noun.slot axis subject = some result) :
    FieldEmbedding.evalFBy q (fuel + 1) subject (.cell (.atom 0) (.atom axis)) =
      some result := by
  simpa only [FieldEmbedding.evalFBy] using hslot

theorem evalFBy_s1_exact (q fuel : ℕ) (subject result : Noun) :
    FieldEmbedding.evalFBy q (fuel + 1) subject (.cell (.atom 1) result) =
      some result := by
  rfl

theorem evalFBy_s2_exact {q fuel : ℕ} {subject left right leftResult rightResult result : Noun}
    (hleft : FieldEmbedding.evalFBy q fuel subject left = some leftResult)
    (hright : FieldEmbedding.evalFBy q fuel subject right = some rightResult)
    (happly : FieldEmbedding.evalFBy q fuel leftResult rightResult = some result) :
    FieldEmbedding.evalFBy q (fuel + 1) subject
      (.cell (.atom 2) (.cell left right)) = some result := by
  simp only [FieldEmbedding.evalFBy, hleft, hright]
  exact happly

theorem evalFBy_s3_exact {q fuel : ℕ} {subject tail value : Noun}
    (hcall : FieldEmbedding.evalFBy q fuel subject tail = some value) :
    FieldEmbedding.evalFBy q (fuel + 1) subject (.cell (.atom 3) tail) =
      some (Noun.wut value) := by
  simp only [FieldEmbedding.evalFBy, hcall, Option.map_some]

theorem evalFBy_s4_exact {q fuel : ℕ} {subject tail value result : Noun}
    (hcall : FieldEmbedding.evalFBy q fuel subject tail = some value)
    (hinc : FieldEmbedding.lusFBy q value = some result) :
    FieldEmbedding.evalFBy q (fuel + 1) subject (.cell (.atom 4) tail) =
      some result := by
  simp only [FieldEmbedding.evalFBy, hcall, Option.bind_some]
  exact hinc

theorem evalFBy_s5_exact {q fuel : ℕ} {subject left right leftResult rightResult : Noun}
    (hleft : FieldEmbedding.evalFBy q fuel subject left = some leftResult)
    (hright : FieldEmbedding.evalFBy q fuel subject right = some rightResult) :
    FieldEmbedding.evalFBy q (fuel + 1) subject
      (.cell (.atom 5) (.cell left right)) =
      some (Noun.tis leftResult rightResult) := by
  simp only [FieldEmbedding.evalFBy, hleft, hright]

theorem evalFBy_s6_zero_exact {q fuel : ℕ}
    {subject condition yesBranch noBranch result : Noun}
    (hcondition : FieldEmbedding.evalFBy q fuel subject condition = some (.atom 0))
    (hbranch : FieldEmbedding.evalFBy q fuel subject yesBranch = some result) :
    FieldEmbedding.evalFBy q (fuel + 1) subject
      (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch))) = some result := by
  simp only [FieldEmbedding.evalFBy, hcondition]
  exact hbranch

theorem evalFBy_s6_one_exact {q fuel : ℕ}
    {subject condition yesBranch noBranch result : Noun}
    (hcondition : FieldEmbedding.evalFBy q fuel subject condition = some (.atom 1))
    (hbranch : FieldEmbedding.evalFBy q fuel subject noBranch = some result) :
    FieldEmbedding.evalFBy q (fuel + 1) subject
      (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch))) = some result := by
  simp only [FieldEmbedding.evalFBy, hcondition]
  exact hbranch

theorem evalFBy_s7_exact {q fuel : ℕ}
    {subject first second intermediate result : Noun}
    (hfirst : FieldEmbedding.evalFBy q fuel subject first = some intermediate)
    (hsecond : FieldEmbedding.evalFBy q fuel intermediate second = some result) :
    FieldEmbedding.evalFBy q (fuel + 1) subject
      (.cell (.atom 7) (.cell first second)) = some result := by
  simp only [FieldEmbedding.evalFBy, hfirst]
  exact hsecond

theorem evalFBy_s8_exact {q fuel : ℕ}
    {subject first second intermediate result : Noun}
    (hfirst : FieldEmbedding.evalFBy q fuel subject first = some intermediate)
    (hsecond : FieldEmbedding.evalFBy q fuel (.cell intermediate subject) second = some result) :
    FieldEmbedding.evalFBy q (fuel + 1) subject
      (.cell (.atom 8) (.cell first second)) = some result := by
  simp only [FieldEmbedding.evalFBy, hfirst]
  exact hsecond

theorem evalFBy_s9_exact {q fuel axis : ℕ}
    {subject coreFormula core arm result : Noun}
    (hcore : FieldEmbedding.evalFBy q fuel subject coreFormula = some core)
    (hslot : Noun.slot axis core = some arm)
    (harm : FieldEmbedding.evalFBy q fuel core arm = some result) :
    FieldEmbedding.evalFBy q (fuel + 1) subject
      (.cell (.atom 9) (.cell (.atom axis) coreFormula)) = some result := by
  simp only [FieldEmbedding.evalFBy, hcore, hslot]
  exact harm

theorem evalFBy_cons_exact {q fuel : ℕ}
    {subject headLeft headRight tail leftResult rightResult : Noun}
    (hleft : FieldEmbedding.evalFBy q fuel subject (.cell headLeft headRight) =
      some leftResult)
    (hright : FieldEmbedding.evalFBy q fuel subject tail = some rightResult) :
    FieldEmbedding.evalFBy q (fuel + 1) subject
      (.cell (.cell headLeft headRight) tail) =
      some (.cell leftResult rightResult) := by
  simp only [FieldEmbedding.evalFBy, hleft, hright]

/-! ## Fingerprint bridges for the primitive operators -/

/-- OP3's size-only `qm` fingerprint agrees with noun `wut` inside the power window. -/
theorem enc_wut_eq {K : Type*} [Field K] {z : K} {value : Noun}
    (hw : SizeWindow z value) :
    enc z (Noun.wut value) = FP.atomFP z (FP.qm z (enc z value)) := by
  cases value with
  | atom k =>
      simp [Noun.wut, GlobalCarryRecognizer.enc_atom, FP.qm]
  | cell left right =>
      have hne : (enc z (.cell left right)).size ≠ z := by
        intro heq
        obtain ⟨k, hk⟩ := atom_of_enc_size_eq hw heq
        simp at hk
      have hpow : z ^ (Noun.cell left right).leaves ≠ z := by
        simpa only [GlobalCarryRecognizer.enc_size] using hne
      simp [Noun.wut, GlobalCarryRecognizer.enc_atom, FP.qm,
        GlobalCarryRecognizer.enc_size, hpow]

/-- OP5's full-fingerprint equality test agrees with structural noun equality off collisions. -/
theorem enc_tis_eq {K : Type*} [Field K] {z : K} {q : ℕ} {left right : Noun}
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hfaith : PairFaithful z q left right) :
    enc z (Noun.tis left right) =
      FP.atomFP z (FP.eqOp (enc z left) (enc z right)) := by
  by_cases heq : left = right
  · subst heq
    simp [Noun.tis, FP.eqOp, GlobalCarryRecognizer.enc_atom]
  · have henc : enc z left ≠ enc z right := by
      intro h
      exact heq (hfaith.eq_of_enc_eq hcast h)
    simp [Noun.tis, FP.eqOp, heq, henc, GlobalCarryRecognizer.enc_atom]

/-- The cell fallback is unreachable under `IncrementNoOverflow`. -/
def incNoWrap : Noun → Noun
  | .atom n => .atom (n + 1)
  | .cell _ _ => .atom 0

/-- It rules out a cell and keeps `n+1 < q`; the
paper's modular OP4 does not require it. -/
def IncrementNoOverflow (q : ℕ) : Noun → Prop
  | .atom n => n + 1 < q
  | .cell _ _ => False

/-- The paper's total noun target for OP4 at modulus `q`.

The cell fallback makes the comparison target total; the accepted OP4 row's size gate proves that
the operand is an atom before this target is consumed. -/
def incMod (q : ℕ) : Noun → Noun
  | .atom n => .atom ((n + 1) % q)
  | .cell _ _ => .atom 0

@[simp]
theorem lusFBy_atom_eq_incMod (q n : ℕ) :
    FieldEmbedding.lusFBy q (.atom n) = some (incMod q (.atom n)) :=
  rfl

/-- At the field characteristic, the table's `FP.inc` is exactly the encoding of modular OP4,
including the top-residue wrap. -/
theorem fp_inc_enc_atom_eq_incMod {K : Type*} [Field K] {q : ℕ} [CharP K q]
    (z : K) (n : ℕ) :
    FP.inc z (enc z (.atom n)) = enc z (incMod q (.atom n)) := by
  apply FP.ext <;>
    simp [incMod, FP.inc, FP.atomFP, GlobalCarryRecognizer.enc_atom,
      ← CharP.cast_eq_mod K q (n + 1)]

theorem op4_top_residue_regression {K : Type*} [Field K] [Fintype K] (z : K) :
    let q := ringChar K
    incMod q (.atom (q - 1)) = .atom 0 ∧
      FieldEmbedding.lusFBy q (.atom (q - 1)) = some (.atom 0) ∧
      FP.inc z (enc z (.atom (q - 1))) = enc z (.atom 0) ∧
      ¬ IncrementNoOverflow q (.atom (q - 1)) := by
  dsimp
  have hq : 0 < ringChar K := (CharP.prime_ringChar K).pos
  have htop : ringChar K - 1 + 1 = ringChar K := Nat.sub_add_cancel hq
  constructor
  · change Noun.atom ((ringChar K - 1 + 1) % ringChar K) = Noun.atom 0
    rw [htop, Nat.mod_self]
  constructor
  · change some (Noun.atom ((ringChar K - 1 + 1) % ringChar K)) =
      some (Noun.atom 0)
    rw [htop, Nat.mod_self]
  constructor
  · rw [fp_inc_enc_atom_eq_incMod]
    simp [incMod, htop]
  · simp [IncrementNoOverflow, htop]

theorem lusFBy_eq_incNoWrap {q : ℕ} {value : Noun}
    (hno : IncrementNoOverflow q value) :
    FieldEmbedding.lusFBy q value = some (incNoWrap value) := by
  cases value with
  | atom n =>
      simp only [IncrementNoOverflow] at hno
      simp [FieldEmbedding.lusFBy, incNoWrap, Nat.mod_eq_of_lt hno]
  | cell left right => exact hno.elim

/-! ## Accepted-row containment -/

/-- OP0 containment.  The row contributes the exact memory request; `hserved` says the matching
request was served by the anchored global-carry reconstruction. -/
theorem s0_vcomp_semantics {K : Type*} [Field K] {q fuel axis : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s0) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec)
    (hhead : PairFaithful inp.z q row.head (.atom 0))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (htail : PairFaithful inp.z q row.tail (.atom axis))
    (hmr : RealizesMemRec inp.z pub.mr2 row.subject row.result axis)
    (hserved : GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun row.subject 1) axis row.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .slot (Verb.ofNoun (.atom axis)) (Verb.ofNoun row.subject))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, _, hmem, _⟩ := hv'
  have hformulaEq : row.formula = .cell (.atom 0) row.tail :=
    numeric_formula_eq hstate (by decide) hz hcast row hhead hformula hv
  simp only [memBlk, hstate] at hmem
  obtain ⟨hmr2, _, _, hsize, hdyck⟩ := hmem
  have haxisField : dec.f_t.leaf = (axis : K) := by
    calc
      dec.f_t.leaf = pub.mr2.axis :=
        (congrArg MemRec.axis hmr2).symm
      _ = (axis : K) := hmr.axis_realizes
  have htailEnc : enc inp.z row.tail = enc inp.z (.atom axis) := by
    calc
      enc inp.z row.tail = dec.f_t := row.tail_realizes.symm
      _ = FP.atomFP inp.z (axis : K) := FP.ext hsize hdyck haxisField
      _ = enc inp.z (.atom axis) :=
        (GlobalCarryRecognizer.enc_atom inp.z axis).symm
  have htailEq : row.tail = .atom axis :=
    htail.eq_of_enc_eq hcast htailEnc
  have hslot : Noun.slot axis row.subject = some row.result :=
    GlobalCarryRecognizer.axis_sound_recognizer' row.subject hserved
  constructor
  · rw [hformulaEq, htailEq]
    exact stepROM_s0_exact row.subject (.atom axis)
  · rw [hformulaEq, htailEq]
    exact evalFBy_s0_exact hslot

/-- OP1 containment: accepted fingerprint equality is reflected to the realized result noun. -/
theorem s1_vcomp_semantics {K : Type*} [Field K] {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s1) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec)
    (hhead : PairFaithful inp.z q row.head (.atom 1))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (hresult : PairFaithful inp.z q row.result row.tail)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula) (Verb.ofNoun row.tail)
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, _, _, heval⟩ := hv'
  have hformulaEq : row.formula = .cell (.atom 1) row.tail :=
    numeric_formula_eq hstate (by decide) hz hcast row hhead hformula hv
  simp only [evalV, hstate] at heval
  have hresultEq : row.result = row.tail :=
    noun_eq_of_realizes_eq row.result_realizes row.tail_realizes heval.1 hcast hresult
  constructor
  · rw [hformulaEq]
    exact stepROM_s1_exact row.subject row.tail
  · rw [hformulaEq, hresultEq]
    exact evalFBy_s1_exact q fuel row.subject row.tail

/-- OP2 containment: the three recursive premises are exactly the three realized `sf` calls. -/
theorem s2_vcomp_semantics {K : Type*} [Field K] {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s2) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec) (tail : TailRealization inp.z dec)
    (call1 : CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (call2 : CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
    (call3 : CallRealization inp.z pub.sf3_s pub.sf3_f pub.sf3_e)
    (hhead : PairFaithful inp.z q row.head (.atom 2))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (htail : PairFaithful inp.z q row.tail (.cell tail.head tail.tail))
    (h1s : PairFaithful inp.z q call1.subject row.subject)
    (h1f : PairFaithful inp.z q call1.formula tail.head)
    (h2s : PairFaithful inp.z q call2.subject row.subject)
    (h2f : PairFaithful inp.z q call2.formula tail.tail)
    (h3s : PairFaithful inp.z q call3.subject call1.result)
    (h3f : PairFaithful inp.z q call3.formula call2.result)
    (hresult : PairFaithful inp.z q row.result call3.result)
    (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
      some call1.result)
    (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
      some call2.result)
    (hcall3 : FieldEmbedding.evalFBy q fuel call3.subject call3.formula =
      some call3.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .star
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun tail.head))
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun tail.tail)))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, _, hmem, heval⟩ := hv'
  have hformulaEq : row.formula = .cell (.atom 2) row.tail :=
    numeric_formula_eq hstate (by decide) hz hcast row hhead hformula hv
  simp only [memBlk, hstate] at hmem
  obtain ⟨_, hcons, _, _⟩ := hmem
  have htailEq : row.tail = .cell tail.head tail.tail :=
    realized_tail_eq_cell hz hcast row tail htail hcons
  simp only [evalV, hstate] at heval
  obtain ⟨he1s, he1f, he2s, he2f, he3s, he3f, heresult⟩ := heval
  have h1sEq : call1.subject = row.subject :=
    noun_eq_of_realizes_eq call1.subject_realizes row.subject_realizes he1s hcast h1s
  have h1fEq : call1.formula = tail.head :=
    noun_eq_of_realizes_eq call1.formula_realizes tail.head_realizes he1f hcast h1f
  have h2sEq : call2.subject = row.subject :=
    noun_eq_of_realizes_eq call2.subject_realizes row.subject_realizes he2s hcast h2s
  have h2fEq : call2.formula = tail.tail :=
    noun_eq_of_realizes_eq call2.formula_realizes tail.tail_realizes he2f hcast h2f
  have h3sEq : call3.subject = call1.result :=
    noun_eq_of_realizes_eq call3.subject_realizes call1.result_realizes he3s hcast h3s
  have h3fEq : call3.formula = call2.result :=
    noun_eq_of_realizes_eq call3.formula_realizes call2.result_realizes he3f hcast h3f
  have hresultEq : row.result = call3.result :=
    noun_eq_of_realizes_eq row.result_realizes call3.result_realizes heresult hcast hresult
  have hc1 := hcall1
  have hc2 := hcall2
  have hc3 := hcall3
  rw [h1sEq, h1fEq] at hc1
  rw [h2sEq, h2fEq] at hc2
  rw [h3sEq, h3fEq] at hc3
  constructor
  · rw [hformulaEq, htailEq]
    exact stepROM_s2_exact row.subject tail.head tail.tail
  · rw [hformulaEq, htailEq, hresultEq]
    exact evalFBy_s2_exact hc1 hc2 hc3

/-- OP3 containment: the size-power window is the extra fact needed because `qm` reads only
the size coordinate, unlike full NPR equality. -/
theorem s3_vcomp_semantics {K : Type*} [Field K] {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s3) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec)
    (call1 : CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (hhead : PairFaithful inp.z q row.head (.atom 3))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (h1s : PairFaithful inp.z q call1.subject row.subject)
    (h1f : PairFaithful inp.z q call1.formula row.tail)
    (hresult : PairFaithful inp.z q row.result (Noun.wut call1.result))
    (hsize : SizeWindow inp.z call1.result)
    (hcall : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
      some call1.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .minus (.leaf 3)
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun row.tail)))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, _, _, heval⟩ := hv'
  have hformulaEq : row.formula = .cell (.atom 3) row.tail :=
    numeric_formula_eq hstate (by decide) hz hcast row hhead hformula hv
  simp only [evalV, hstate] at heval
  have he1s := heval.1
  have he1f := heval.2.1
  have hresultSize := heval.2.2.2.2.1
  have hresultDyck := heval.2.2.2.2.2.1
  have hresultLeaf := heval.2.2.2.2.2.2
  have h1sEq : call1.subject = row.subject :=
    noun_eq_of_realizes_eq call1.subject_realizes row.subject_realizes he1s hcast h1s
  have h1fEq : call1.formula = row.tail :=
    noun_eq_of_realizes_eq call1.formula_realizes row.tail_realizes he1f hcast h1f
  have hresultEnc : enc inp.z row.result = enc inp.z (Noun.wut call1.result) := by
    calc
      enc inp.z row.result = pub.e := row.result_realizes.symm
      _ = FP.atomFP inp.z (FP.qm inp.z pub.sf1_e) :=
        FP.ext hresultSize hresultDyck hresultLeaf
      _ = FP.atomFP inp.z (FP.qm inp.z (enc inp.z call1.result)) :=
        congrArg (FP.atomFP inp.z)
          (congrArg (FP.qm inp.z) call1.result_realizes)
      _ = enc inp.z (Noun.wut call1.result) := (enc_wut_eq hsize).symm
  have hresultEq : row.result = Noun.wut call1.result :=
    hresult.eq_of_enc_eq hcast hresultEnc
  have hc := hcall
  rw [h1sEq, h1fEq] at hc
  constructor
  · rw [hformulaEq]
    exact stepROM_s3_exact row.subject row.tail
  · rw [hformulaEq, hresultEq]
    exact evalFBy_s3_exact hc

/-- OP4 containment at the field characteristic.

The verifier's size gate proves atom shape.  `CharP K (ringChar K)` then identifies field addition
with the canonical modular noun target, including `q-1 ↦ 0`; no `IncrementNoOverflow` premise is
present. -/
theorem s4_vcomp_semantics {K : Type*} [Field K] {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s4) (hz : inp.z ≠ 0)
    (hq : q = ringChar K)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec)
    (call1 : CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (hhead : PairFaithful inp.z q row.head (.atom 4))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (h1s : PairFaithful inp.z q call1.subject row.subject)
    (h1f : PairFaithful inp.z q call1.formula row.tail)
    (hresult : PairFaithful inp.z q row.result (incMod (ringChar K) call1.result))
    (hsize : SizeWindow inp.z call1.result)
    (hcall : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
      some call1.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .minus (.leaf 4)
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun row.tail)))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, _, _, heval⟩ := hv'
  have hformulaEq : row.formula = .cell (.atom 4) row.tail :=
    numeric_formula_eq hstate (by decide) hz hcast row hhead hformula hv
  simp only [evalV, hstate] at heval
  have he1s := heval.1
  have he1f := heval.2.1
  have hvalueSize := heval.2.2.1
  have hresultFP := heval.2.2.2.2.2.2
  have h1sEq : call1.subject = row.subject :=
    noun_eq_of_realizes_eq call1.subject_realizes row.subject_realizes he1s hcast h1s
  have h1fEq : call1.formula = row.tail :=
    noun_eq_of_realizes_eq call1.formula_realizes row.tail_realizes he1f hcast h1f
  have hvalueSize' : (enc inp.z call1.result).size = inp.z := by
    calc
      (enc inp.z call1.result).size = pub.sf1_e.size :=
        congrArg FP.size call1.result_realizes.symm
      _ = inp.z := hvalueSize
  obtain ⟨n, hvalueAtom⟩ := atom_of_enc_size_eq hsize hvalueSize'
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hincEnc :
      FP.inc inp.z (enc inp.z call1.result) =
        enc inp.z (incMod (ringChar K) call1.result) := by
    rw [hvalueAtom]
    exact fp_inc_enc_atom_eq_incMod inp.z n
  have hresultEnc :
      enc inp.z row.result = enc inp.z (incMod (ringChar K) call1.result) := by
    calc
      enc inp.z row.result = pub.e := row.result_realizes.symm
      _ = FP.inc inp.z pub.sf1_e := hresultFP
      _ = FP.inc inp.z (enc inp.z call1.result) :=
        congrArg (FP.inc inp.z) call1.result_realizes
      _ = enc inp.z (incMod (ringChar K) call1.result) := hincEnc
  have hresultEq : row.result = incMod (ringChar K) call1.result :=
    hresult.eq_of_enc_eq hcast hresultEnc
  have hc := hcall
  rw [h1sEq, h1fEq] at hc
  have hinc :
      FieldEmbedding.lusFBy q call1.result =
        some (incMod (ringChar K) call1.result) := by
    rw [hq, hvalueAtom]
    exact lusFBy_atom_eq_incMod (ringChar K) n
  constructor
  · rw [hformulaEq]
    exact stepROM_s4_exact row.subject row.tail
  · rw [hformulaEq, hresultEq]
    exact evalFBy_s4_exact hc hinc

/-- OP5 containment: full-fingerprint equality is reflected to noun equality only through the
pair-local collision/boundedness witness `hcompare`. -/
theorem s5_vcomp_semantics {K : Type*} [Field K] {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s5) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec) (tail : TailRealization inp.z dec)
    (call1 : CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (call2 : CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
    (hhead : PairFaithful inp.z q row.head (.atom 5))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (htail : PairFaithful inp.z q row.tail (.cell tail.head tail.tail))
    (h1s : PairFaithful inp.z q call1.subject row.subject)
    (h1f : PairFaithful inp.z q call1.formula tail.head)
    (h2s : PairFaithful inp.z q call2.subject row.subject)
    (h2f : PairFaithful inp.z q call2.formula tail.tail)
    (hcompare : PairFaithful inp.z q call1.result call2.result)
    (hresult : PairFaithful inp.z q row.result (Noun.tis call1.result call2.result))
    (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
      some call1.result)
    (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
      some call2.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .equal
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun tail.head))
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun tail.tail)))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, _, hmem, heval⟩ := hv'
  have hformulaEq : row.formula = .cell (.atom 5) row.tail :=
    numeric_formula_eq hstate (by decide) hz hcast row hhead hformula hv
  simp only [memBlk, hstate] at hmem
  obtain ⟨_, hcons, _, _⟩ := hmem
  have htailEq : row.tail = .cell tail.head tail.tail :=
    realized_tail_eq_cell hz hcast row tail htail hcons
  simp only [evalV, hstate] at heval
  have he1s := heval.1
  have he1f := heval.2.1
  have he2s := heval.2.2.1
  have he2f := heval.2.2.2.1
  have hresultSize := heval.2.2.2.2.2.1
  have hresultDyck := heval.2.2.2.2.2.2.1
  have hresultLeaf := heval.2.2.2.2.2.2.2
  have h1sEq : call1.subject = row.subject :=
    noun_eq_of_realizes_eq call1.subject_realizes row.subject_realizes he1s hcast h1s
  have h1fEq : call1.formula = tail.head :=
    noun_eq_of_realizes_eq call1.formula_realizes tail.head_realizes he1f hcast h1f
  have h2sEq : call2.subject = row.subject :=
    noun_eq_of_realizes_eq call2.subject_realizes row.subject_realizes he2s hcast h2s
  have h2fEq : call2.formula = tail.tail :=
    noun_eq_of_realizes_eq call2.formula_realizes tail.tail_realizes he2f hcast h2f
  have hresultEnc :
      enc inp.z row.result = enc inp.z (Noun.tis call1.result call2.result) := by
    calc
      enc inp.z row.result = pub.e := row.result_realizes.symm
      _ = FP.atomFP inp.z (FP.eqOp pub.sf1_e pub.sf2_e) :=
        FP.ext hresultSize hresultDyck hresultLeaf
      _ = FP.atomFP inp.z
          (FP.eqOp (enc inp.z call1.result) (enc inp.z call2.result)) := by
        exact congrArg (FP.atomFP inp.z)
          (congrArg₂ FP.eqOp call1.result_realizes call2.result_realizes)
      _ = enc inp.z (Noun.tis call1.result call2.result) :=
        (enc_tis_eq hcast hcompare).symm
  have hresultEq : row.result = Noun.tis call1.result call2.result :=
    hresult.eq_of_enc_eq hcast hresultEnc
  have hc1 := hcall1
  have hc2 := hcall2
  rw [h1sEq, h1fEq] at hc1
  rw [h2sEq, h2fEq] at hc2
  constructor
  · rw [hformulaEq, htailEq]
    exact stepROM_s5_exact row.subject tail.head tail.tail
  · rw [hformulaEq, htailEq, hresultEq]
    exact evalFBy_s5_exact hc1 hc2

/-- OP6 containment.  The verifier's boolean leaf and size constraints are reflected to the
actual condition noun using the bounded atom cast and the size-power window. -/
theorem s6_vcomp_semantics {K : Type*} [Field K] {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s6) (hz : inp.z ≠ 0) (hq : 1 < q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec) (tail : TailRealization inp.z dec)
    (branch : BranchTailRealization inp.z dec)
    (call1 : CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (call2 : CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
    (hhead : PairFaithful inp.z q row.head (.atom 6))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (htail : PairFaithful inp.z q row.tail (.cell tail.head tail.tail))
    (hbranchTail : PairFaithful inp.z q tail.tail (.cell branch.head branch.tail))
    (h1s : PairFaithful inp.z q call1.subject row.subject)
    (h1fZero : PairFaithful inp.z q call1.formula branch.head)
    (h1fOne : PairFaithful inp.z q call1.formula branch.tail)
    (h2s : PairFaithful inp.z q call2.subject row.subject)
    (h2f : PairFaithful inp.z q call2.formula tail.head)
    (hresult : PairFaithful inp.z q row.result call1.result)
    (hconditionBound : FieldEmbedding.BoundedBy q call2.result)
    (hconditionSize : SizeWindow inp.z call2.result)
    (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
      some call1.result)
    (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
      some call2.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (s6Successor row.subject tail.head branch.head branch.tail)
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, _, hmem, heval⟩ := hv'
  have hformulaEq : row.formula = .cell (.atom 6) row.tail :=
    numeric_formula_eq hstate (by decide) hz hcast row hhead hformula hv
  simp only [memBlk, hstate] at hmem
  obtain ⟨_, hconsTail, _, hconsBranch, _⟩ := hmem
  have htailEq : row.tail = .cell tail.head tail.tail :=
    realized_tail_eq_cell hz hcast row tail htail hconsTail
  have hbranchEq : tail.tail = .cell branch.head branch.tail :=
    realized_branch_tail_eq_cell hz hcast tail branch hbranchTail hconsBranch
  simp only [evalV, hstate] at heval
  have he1s := heval.1
  have he1f := heval.2.1
  have heresult := heval.2.2.1
  have he2s := heval.2.2.2.1
  have he2f := heval.2.2.2.2.1
  have hconditionFPSize := heval.2.2.2.2.2.1
  have hconditionLeaf := heval.2.2.2.2.2.2.2.1
  have h1sEq : call1.subject = row.subject :=
    noun_eq_of_realizes_eq call1.subject_realizes row.subject_realizes he1s hcast h1s
  have h2sEq : call2.subject = row.subject :=
    noun_eq_of_realizes_eq call2.subject_realizes row.subject_realizes he2s hcast h2s
  have h2fEq : call2.formula = tail.head :=
    noun_eq_of_realizes_eq call2.formula_realizes tail.head_realizes he2f hcast h2f
  have hresultEq : row.result = call1.result :=
    noun_eq_of_realizes_eq row.result_realizes call1.result_realizes heresult hcast hresult
  have hconditionSizeEq : (enc inp.z call2.result).size = inp.z := by
    calc
      (enc inp.z call2.result).size = pub.sf2_e.size :=
        congrArg FP.size call2.result_realizes.symm
      _ = inp.z := hconditionFPSize
  obtain ⟨n, hconditionAtom⟩ :=
    atom_of_enc_size_eq hconditionSize hconditionSizeEq
  have hnq : n < q := by
    rw [hconditionAtom] at hconditionBound
    exact hconditionBound
  have hleafCast : pub.sf2_e.leaf = (n : K) := by
    calc
      pub.sf2_e.leaf = (enc inp.z call2.result).leaf :=
        congrArg FP.leaf call2.result_realizes
      _ = (enc inp.z (.atom n)).leaf := by rw [hconditionAtom]
      _ = (FP.atomFP inp.z (n : K)).leaf :=
        congrArg FP.leaf (GlobalCarryRecognizer.enc_atom inp.z n)
      _ = (n : K) := rfl
  rcases hconditionLeaf with hleafZero | hleafOne
  · have hn0 : n = 0 := by
      apply hcast (Set.mem_Iio.mpr hnq) (Set.mem_Iio.mpr (by omega))
      simpa using hleafCast.symm.trans hleafZero
    have hconditionEq : call2.result = .atom 0 := by
      rw [hconditionAtom, hn0]
    have he1fZero : pub.sf1_f = dec.f_tth := by
      simpa [hleafZero] using he1f
    have h1fEq : call1.formula = branch.head :=
      noun_eq_of_realizes_eq call1.formula_realizes branch.head_realizes
        he1fZero hcast h1fZero
    have hc1 := hcall1
    have hc2 := hcall2
    rw [h1sEq, h1fEq] at hc1
    rw [h2sEq, h2fEq, hconditionEq] at hc2
    constructor
    · rw [hformulaEq, htailEq, hbranchEq]
      exact stepROM_s6_exact row.subject tail.head branch.head branch.tail
    · rw [hformulaEq, htailEq, hbranchEq, hresultEq]
      exact evalFBy_s6_zero_exact hc2 hc1
  · have hn1 : n = 1 := by
      apply hcast (Set.mem_Iio.mpr hnq) (Set.mem_Iio.mpr (by omega))
      simpa using hleafCast.symm.trans hleafOne
    have hconditionEq : call2.result = .atom 1 := by
      rw [hconditionAtom, hn1]
    have he1fOne : pub.sf1_f = dec.f_ttt := by
      simpa [hleafOne] using he1f
    have h1fEq : call1.formula = branch.tail :=
      noun_eq_of_realizes_eq call1.formula_realizes branch.tail_realizes
        he1fOne hcast h1fOne
    have hc1 := hcall1
    have hc2 := hcall2
    rw [h1sEq, h1fEq] at hc1
    rw [h2sEq, h2fEq, hconditionEq] at hc2
    constructor
    · rw [hformulaEq, htailEq, hbranchEq]
      exact stepROM_s6_exact row.subject tail.head branch.head branch.tail
    · rw [hformulaEq, htailEq, hbranchEq, hresultEq]
      exact evalFBy_s6_one_exact hc2 hc1

/-- OP7 containment.  `sf2` computes the new subject; `sf1` evaluates the second formula there. -/
theorem s7_vcomp_semantics {K : Type*} [Field K] {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s7) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec) (tail : TailRealization inp.z dec)
    (call1 : CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (call2 : CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
    (hhead : PairFaithful inp.z q row.head (.atom 7))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (htail : PairFaithful inp.z q row.tail (.cell tail.head tail.tail))
    (h2s : PairFaithful inp.z q call2.subject row.subject)
    (h2f : PairFaithful inp.z q call2.formula tail.head)
    (h1s : PairFaithful inp.z q call1.subject call2.result)
    (h1f : PairFaithful inp.z q call1.formula tail.tail)
    (hresult : PairFaithful inp.z q row.result call1.result)
    (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
      some call1.result)
    (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
      some call2.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .star
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun tail.head))
          (Verb.ofNoun tail.tail))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, _, hmem, heval⟩ := hv'
  have hformulaEq : row.formula = .cell (.atom 7) row.tail :=
    numeric_formula_eq hstate (by decide) hz hcast row hhead hformula hv
  simp only [memBlk, hstate] at hmem
  obtain ⟨_, hcons, _, _⟩ := hmem
  have htailEq : row.tail = .cell tail.head tail.tail :=
    realized_tail_eq_cell hz hcast row tail htail hcons
  simp only [evalV, hstate] at heval
  obtain ⟨he1s, he1f, heresult, he2s, he2f, _⟩ := heval
  have h2sEq : call2.subject = row.subject :=
    noun_eq_of_realizes_eq call2.subject_realizes row.subject_realizes he2s hcast h2s
  have h2fEq : call2.formula = tail.head :=
    noun_eq_of_realizes_eq call2.formula_realizes tail.head_realizes he2f hcast h2f
  have h1sEq : call1.subject = call2.result :=
    noun_eq_of_realizes_eq call1.subject_realizes call2.result_realizes he1s hcast h1s
  have h1fEq : call1.formula = tail.tail :=
    noun_eq_of_realizes_eq call1.formula_realizes tail.tail_realizes he1f hcast h1f
  have hresultEq : row.result = call1.result :=
    noun_eq_of_realizes_eq row.result_realizes call1.result_realizes heresult hcast hresult
  have hc1 := hcall1
  have hc2 := hcall2
  rw [h1sEq, h1fEq] at hc1
  rw [h2sEq, h2fEq] at hc2
  constructor
  · rw [hformulaEq, htailEq]
    exact stepROM_s7_exact row.subject tail.head tail.tail
  · rw [hformulaEq, htailEq, hresultEq]
    exact evalFBy_s7_exact hc2 hc1

/-- OP8 containment.  The accepted `FP.cons sf2_e s` wiring is reflected through
`formula_cons_sound` to the actual subject cell `[sf2_e-result subject]`. -/
theorem s8_vcomp_semantics {K : Type*} [Field K] {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s8) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec) (tail : TailRealization inp.z dec)
    (call1 : CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (call2 : CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
    (hhead : PairFaithful inp.z q row.head (.atom 8))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (htail : PairFaithful inp.z q row.tail (.cell tail.head tail.tail))
    (h2s : PairFaithful inp.z q call2.subject row.subject)
    (h2f : PairFaithful inp.z q call2.formula tail.head)
    (h1s : PairFaithful inp.z q call1.subject (.cell call2.result row.subject))
    (h1f : PairFaithful inp.z q call1.formula tail.tail)
    (hresult : PairFaithful inp.z q row.result call1.result)
    (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
      some call1.result)
    (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
      some call2.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .star
          (.node .null
            (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun tail.head))
            (Verb.ofNoun row.subject))
          (Verb.ofNoun tail.tail))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, _, hmem, heval⟩ := hv'
  have hformulaEq : row.formula = .cell (.atom 8) row.tail :=
    numeric_formula_eq hstate (by decide) hz hcast row hhead hformula hv
  simp only [memBlk, hstate] at hmem
  obtain ⟨_, hcons, _, _⟩ := hmem
  have htailEq : row.tail = .cell tail.head tail.tail :=
    realized_tail_eq_cell hz hcast row tail htail hcons
  simp only [evalV, hstate] at heval
  obtain ⟨he1s, he1f, heresult, he2s, he2f, _⟩ := heval
  have h2sEq : call2.subject = row.subject :=
    noun_eq_of_realizes_eq call2.subject_realizes row.subject_realizes he2s hcast h2s
  have h2fEq : call2.formula = tail.head :=
    noun_eq_of_realizes_eq call2.formula_realizes tail.head_realizes he2f hcast h2f
  have h1sEq : call1.subject = .cell call2.result row.subject := by
    apply cell_eq_of_cons_encoding hz hcast
      call1.subject call2.result row.subject h1s
    calc
      FP.cons inp.z (enc inp.z call2.result) (enc inp.z row.subject) =
          FP.cons inp.z pub.sf2_e pub.s := by
            rw [← call2.result_realizes, ← row.subject_realizes]
      _ = pub.sf1_s := he1s.symm
      _ = enc inp.z call1.subject := call1.subject_realizes
  have h1fEq : call1.formula = tail.tail :=
    noun_eq_of_realizes_eq call1.formula_realizes tail.tail_realizes he1f hcast h1f
  have hresultEq : row.result = call1.result :=
    noun_eq_of_realizes_eq row.result_realizes call1.result_realizes heresult hcast hresult
  have hc1 := hcall1
  have hc2 := hcall2
  rw [h1sEq, h1fEq] at hc1
  rw [h2sEq, h2fEq] at hc2
  constructor
  · rw [hformulaEq, htailEq]
    exact stepROM_s8_exact row.subject tail.head tail.tail
  · rw [hformulaEq, htailEq, hresultEq]
    exact evalFBy_s8_exact hc2 hc1

/-- OP9 containment.  The verifier pins `f_th` to the exact atom fingerprint shape
`(z, 0, axis)`.  A pair-local NPR separation witness then reflects that fingerprint equality back
to the noun equality `tail.head =.atom axis`; no free axis-syntax premise is accepted. -/
theorem s9_vcomp_semantics {K : Type*} [Field K] {q fuel axis : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s9) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec) (tail : TailRealization inp.z dec)
    (call1 : CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (call2 : CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
    (hhead : PairFaithful inp.z q row.head (.atom 9))
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (htail : PairFaithful inp.z q row.tail (.cell tail.head tail.tail))
    (haxis : PairFaithful inp.z q tail.head (.atom axis))
    (h1s : PairFaithful inp.z q call1.subject row.subject)
    (h1f : PairFaithful inp.z q call1.formula tail.tail)
    (h2s : PairFaithful inp.z q call2.subject call1.result)
    (hresult : PairFaithful inp.z q row.result call2.result)
    (hmr : RealizesMemRec inp.z pub.mr3 call1.result call2.formula axis)
    (hserved : GlobalCarryAxis.ServedLookup
      (GlobalCarryRecognizer.ofNoun call1.result 1) axis call2.formula)
    (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
      some call1.result)
    (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
      some call2.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .star
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun tail.tail))
          (.node .null (.leaf 2)
            (.node .null
              (.node .null (.leaf 0) (.leaf 1))
              (.node .null (.leaf 0) (.leaf axis)))))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, _, hmem, heval⟩ := hv'
  have hformulaEq : row.formula = .cell (.atom 9) row.tail :=
    numeric_formula_eq hstate (by decide) hz hcast row hhead hformula hv
  simp only [memBlk, hstate] at hmem
  obtain ⟨_, hcons, hmr3, _⟩ := hmem
  have htailEq : row.tail = .cell tail.head tail.tail :=
    realized_tail_eq_cell hz hcast row tail htail hcons
  simp only [evalV, hstate] at heval
  obtain ⟨he1s, he1f, he2s, heresult, _, haxisSize, haxisDyck⟩ := heval
  have h1sEq : call1.subject = row.subject :=
    noun_eq_of_realizes_eq call1.subject_realizes row.subject_realizes he1s hcast h1s
  have h1fEq : call1.formula = tail.tail :=
    noun_eq_of_realizes_eq call1.formula_realizes tail.tail_realizes he1f hcast h1f
  have h2sEq : call2.subject = call1.result :=
    noun_eq_of_realizes_eq call2.subject_realizes call1.result_realizes he2s hcast h2s
  have hresultEq : row.result = call2.result :=
    noun_eq_of_realizes_eq row.result_realizes call2.result_realizes heresult hcast hresult
  have haxisField : dec.f_th.leaf = (axis : K) := by
    calc
      dec.f_th.leaf = pub.mr3.axis :=
        (congrArg MemRec.axis hmr3).symm
      _ = (axis : K) := hmr.axis_realizes
  have haxisAtom : tail.head = .atom axis := by
    apply haxis.eq_of_enc_eq hcast
    calc
      enc inp.z tail.head = dec.f_th := tail.head_realizes.symm
      _ = FP.atomFP inp.z (axis : K) :=
        FP.ext haxisSize haxisDyck haxisField
      _ = enc inp.z (.atom axis) :=
        (GlobalCarryRecognizer.enc_atom inp.z axis).symm
  have hslot : Noun.slot axis call1.result = some call2.formula :=
    GlobalCarryRecognizer.axis_sound_recognizer' call1.result hserved
  have hc1 := hcall1
  have hc2 := hcall2
  rw [h1sEq, h1fEq] at hc1
  rw [h2sEq] at hc2
  constructor
  · rw [hformulaEq, htailEq, haxisAtom]
    exact stepROM_s9_exact row.subject axis tail.tail
  · rw [hformulaEq, htailEq, haxisAtom, hresultEq]
    exact evalFBy_s9_exact hc1 hslot hc2

/-- Structural-cons containment.  This is the nonnumeric formula-head case, not opcode 10 and not
standard-Nock hint opcode 11. -/
theorem cons_vcomp_semantics {K : Type*} [Field K] {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .cons) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : RootRealization inp pub dec)
    (call1 : CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (call2 : CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
    (hformula : PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (h1s : PairFaithful inp.z q call1.subject row.subject)
    (h1f : PairFaithful inp.z q call1.formula row.head)
    (h2s : PairFaithful inp.z q call2.subject row.subject)
    (h2f : PairFaithful inp.z q call2.formula row.tail)
    (hresult : PairFaithful inp.z q row.result (.cell call1.result call2.result))
    (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
      some call1.result)
    (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
      some call2.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .null
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun row.head))
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun row.tail)))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula =
        some row.result := by
  have hv' := hv
  obtain ⟨_, _, hsv, _, heval⟩ := hv'
  have hformulaEq : row.formula = .cell row.head row.tail :=
    root_formula_eq_cell hz hcast row hformula hv
  obtain ⟨headLeft, headRight, hheadCell⟩ :=
    cons_head_is_cell hstate row.head row.head_realizes hsv
  simp only [evalV, hstate] at heval
  obtain ⟨he1s, he1f, he2s, he2f, heresult, _⟩ := heval
  have h1sEq : call1.subject = row.subject :=
    noun_eq_of_realizes_eq call1.subject_realizes row.subject_realizes he1s hcast h1s
  have h1fEq : call1.formula = row.head :=
    noun_eq_of_realizes_eq call1.formula_realizes row.head_realizes he1f hcast h1f
  have h2sEq : call2.subject = row.subject :=
    noun_eq_of_realizes_eq call2.subject_realizes row.subject_realizes he2s hcast h2s
  have h2fEq : call2.formula = row.tail :=
    noun_eq_of_realizes_eq call2.formula_realizes row.tail_realizes he2f hcast h2f
  have hresultEq : row.result = .cell call1.result call2.result := by
    apply hresult.eq_of_enc_eq hcast
    calc
      enc inp.z row.result = pub.e := row.result_realizes.symm
      _ = FP.cons inp.z pub.sf1_e pub.sf2_e := heresult
      _ = FP.cons inp.z (enc inp.z call1.result) (enc inp.z call2.result) := by
        exact congrArg₂ (FP.cons inp.z)
          call1.result_realizes call2.result_realizes
      _ = enc inp.z (.cell call1.result call2.result) :=
        (GlobalCarryRecognizer.enc_cons hz call1.result call2.result).symm
  have hc1 := hcall1
  have hc2 := hcall2
  rw [h1sEq, h1fEq] at hc1
  rw [h2sEq, h2fEq] at hc2
  rw [hheadCell] at hc1
  constructor
  · rw [hformulaEq, hheadCell]
    exact stepROM_cons_exact row.subject headLeft headRight row.tail
  · rw [hformulaEq, hheadCell, hresultEq]
    exact evalFBy_cons_exact hc1 hc2

end Nock.NockVMROM.Thm54.OpcodeSemantics

#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.lusFBy_atom_eq_incMod
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.fp_inc_enc_atom_eq_incMod
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.op4_top_residue_regression
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s0_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s1_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s2_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s3_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s4_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s5_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s6_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s7_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s8_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.s9_vcomp_semantics
#print axioms Nock.NockVMROM.Thm54.OpcodeSemantics.cons_vcomp_semantics
