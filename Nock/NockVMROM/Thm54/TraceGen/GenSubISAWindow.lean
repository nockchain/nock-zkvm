/-
  Nock/NockVMROM/Thm54/TraceGen/GenSubISAWindow.lean

  **On the sub-ISA `{cons, OP_0, OP_1, OP_3, OP_4, OP_5, OP_6}` the leaf window is DERIVED.**

  `TraceConfined Λ t` (`GenTraceConfined.lean`) is the generator-side image of the paper's
  membership condition `λ ≤ Λ`.

  This module isolates an opcode fragment on which the measurement is **unnecessary** — the four
  excluded rules are exactly those whose recursion evaluates against a computed subject, so the
  fragment is maximal *for this proof strategy*; that it is the largest such fragment in any sense is
  **not proved here**.  Drop
`OP_2`, `OP_7` (`:1068`), `OP_8` (`:1069`) and `OP_9` (`:1070`), and what
  remains is

      cons, OP_0 (`:1061`), OP_1 (`:1062`),
      OP_3 (`:1064`), OP_4 (`:1065`), OP_5 (`:1066`), OP_6 (`:1067`)

  and on that fragment `genComputeSkeleton` (`Gen.lean:546`) satisfies three invariants,
  simultaneously by induction on fuel:

  1. **Subject invariance.**  Every child is generated against the same subject as its parent
     (cons: both halves; OP_3/OP_4: the single call; OP_5: both operands; OP_6: the condition and
     the taken branch).  So every row's subject *is* the root subject.
  2. **Formula descent.**  Every child's formula is a syntactic subterm of its parent's, hence
     `child.formula.leaves ≤ parent.formula.leaves`.
  3. **Result bound.**  `result.leaves ≤ formula.leaves * subject.leaves`.  `OP_0` returns a slot of
     the subject; `OP_1` the formula tail; `OP_3`/`OP_4`/`OP_5` atoms; `OP_6` the taken branch's
     result; `cons` the pair `[l r]` with `l.leaves + r.leaves ≤ (f_l + f_r) * s.leaves`.

  Hence `Λ := formula.leaves * subject.leaves` — a number read off the **program text and its
  input**, with no evaluation — confines the whole trace, and `TraceConfined` follows as a theorem
  rather than a measurement.

  **Scope, exactly.**  This is a statement about programs whose *whole generated tree* avoids the
  four states, expressed by the decidable predicate `SubISA`.  It is **not** a claim about
  `NockVMROM`: the ROM removes only `OP_10`, so it keeps
  `OP_2`, `OP_7`, `OP_8` and `OP_9`, and on the full ROM the measured premise stays necessary.
  Nothing here weakens `TraceConfined`'s role downstream; it supplies one more way to discharge it.
  `dotTree_not_subISA` below records that Tier A's own program is outside the fragment.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenTierA
import Nock.NockVMROM.Thm54.CensusExtraClosure

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

/-! ## Reading a `bfsRows` quantifier as an `InTree` quantifier

`TraceConfined` and `SubISA` are both stated over `bfsRows` so that they are `List` quantifiers and
therefore decidable.  Both directions of the translation are needed: the induction below produces
`InTree` facts and consumes `InTree` hypotheses. -/

/-- A `bfsRows` quantifier and an `InTree` quantifier are the same statement. -/
theorem forall_bfsRows_iff {P : GenComputeRow K → Prop} (t : NTree (GenComputeRow K)) :
    (∀ g ∈ bfsRows t, P g) ↔ (∀ u, InTree t u → P u.label) := by
  constructor
  · intro h u hu
    refine h u.label ?_
    have hmem : u ∈ bfsForest [t] := (mem_bfsForest [t] u).mpr ⟨t, List.mem_singleton_self t, hu⟩
    exact List.mem_map.mpr ⟨u, hmem, rfl⟩
  · intro h g hg
    simp only [bfsRows, List.mem_map] at hg
    obtain ⟨u, hu, rfl⟩ := hg
    obtain ⟨c, hc, hcu⟩ := (mem_bfsForest [t] u).mp hu
    rw [List.mem_singleton] at hc
    subst hc
    exact h u hcu

/-! ## The fragment predicate -/

/-- One row is on the sub-ISA: its state is none of the four subject-replacing opcodes
`OP_2`, `OP_7` (`:1068`), `OP_8` (`:1069`), `OP_9` (`:1070`).
Decidable: four `State` disequalities. -/
def RowSubISA (g : GenComputeRow K) : Prop :=
  g.skel.state ≠ .s2 ∧ g.skel.state ≠ .s7 ∧ g.skel.state ≠ .s8 ∧ g.skel.state ≠ .s9

instance (g : GenComputeRow K) : Decidable (RowSubISA g) := by
  unfold RowSubISA; infer_instance

/-- **The sub-ISA fragment predicate.**  Stated over `bfsRows` — a `List` quantifier, hence
decidable, exactly as `TraceConfined` is. -/
def SubISA (t : NTree (GenComputeRow K)) : Prop :=
  ∀ g ∈ bfsRows t, RowSubISA g

instance (t : NTree (GenComputeRow K)) : Decidable (SubISA t) := by
  unfold SubISA; infer_instance

/-- `SubISA` read at an `InTree` node — the form the induction consumes. -/
theorem subISA_inTree {t u : NTree (GenComputeRow K)} (h : SubISA t) (hu : InTree t u) :
    RowSubISA u.label :=
  (forall_bfsRows_iff t).mp h u hu

/-- `SubISA` from an `InTree` quantifier — the form the induction produces. -/
theorem subISA_of_inTree {t : NTree (GenComputeRow K)}
    (h : ∀ u, InTree t u → RowSubISA u.label) : SubISA t :=
  (forall_bfsRows_iff t).mpr h

/-! ## Leaf arithmetic

`cell_leaves`, `atom_leaves`, `leaves_pos`, `leaves_le_cell_left`, `leaves_le_cell_right` come from
`GenLeafWindow.lean`; these are the products that the window `formula.leaves * subject.leaves`
needs. -/

/-- The formula alone fits the product window, because a subject has at least one leaf. -/
theorem leaves_le_mul_subject (f s : Noun) : f.leaves ≤ f.leaves * s.leaves := by
  simpa using Nat.mul_le_mul (le_refl f.leaves) (leaves_pos s)

/-- The subject alone fits the product window, because a formula has at least one leaf. -/
theorem leaves_le_mul_formula (f s : Noun) : s.leaves ≤ f.leaves * s.leaves := by
  simpa using Nat.mul_le_mul (leaves_pos f) (le_refl s.leaves)

/-- An atom fits the product window. -/
theorem one_le_mul_leaves (f s : Noun) : 1 ≤ f.leaves * s.leaves :=
  le_trans (leaves_pos f) (leaves_le_mul_subject f s)

/-- A subformula of the formula shrinks the window monotonically. -/
theorem mul_leaves_mono {f f' : Noun} (s : Noun) (h : f'.leaves ≤ f.leaves) :
    f'.leaves * s.leaves ≤ f.leaves * s.leaves :=
  Nat.mul_le_mul h (le_refl _)

/-- **`slot` returns a subtree, so it never grows the leaf count.**
This is what makes `OP_0` fit the window. -/
theorem slot_leaves_le (ax : Nat) (n : Noun) :
    ∀ {m : Noun}, Noun.slot ax n = some m → m.leaves ≤ n.leaves := by
  induction ax, n using Nock.Noun.slot.induct with
  | case1 x => intro m h; simp [Noun.slot] at h
  | case2 n =>
      intro m h
      simp only [Noun.slot] at h
      obtain rfl := Option.some.inj h
      exact le_refl _
  | case3 a n l r hrec ih =>
      intro m h
      have hlr : (Noun.cell l r).leaves ≤ n.leaves := ih hrec
      simp only [Noun.slot, hrec] at h
      split at h
      · obtain rfl := Option.some.inj h
        exact le_trans (leaves_le_cell_left l r) hlr
      · obtain rfl := Option.some.inj h
        exact le_trans (leaves_le_cell_right l r) hlr
  | case4 a n hno _ =>
      intro m h
      simp only [Noun.slot] at h
      cases hs : Noun.slot ((a + 2) / 2) n with
      | none => simp at h
      | some w =>
        cases w with
        | atom k => simp at h
        | cell l r => exact (hno l r hs).elim

/-! ## The derivation -/

/-- **The sub-ISA window, derived.**

On the fragment, every generated row carries the *root* subject, a formula no larger than the root
formula, and an evaluation no larger than `formula.leaves * subject.leaves`; and the program's own
result obeys the same bound.

The four excluded opcodes are discharged by contradiction: `hfrag` read at the root
(`InTree.here`) forbids the state the corresponding skeleton constructor sets.  `OP_10`/`OP_11` are
already `.error.notROM`. -/
theorem genComputeSkeleton_subISA_bound
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hfrag : SubISA t) :
    result.leaves ≤ formula.leaves * subject.leaves ∧
      ∀ u, InTree t u →
        u.label.skel.subject = subject ∧
        u.label.skel.formula.leaves ≤ formula.leaves ∧
        u.label.skel.evaluation.leaves ≤ formula.leaves * subject.leaves := by
  have hfrag' : ∀ u, InTree t u → RowSubISA u.label := fun u hu => subISA_inTree hfrag hu
  clear hfrag
  induction fuel generalizing subject formula t result with
  | zero => simp [genComputeSkeleton] at h
  | succ n ih =>
    cases formula with
    | atom _ => simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        -- `cons`: both halves run against the SAME subject.
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error _ => simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨rfl, rfl⟩ := h
            have hfL : ∀ v, InTree pL.1 v → RowSubISA v.label := fun v hv =>
              hfrag' v (InTree.sub (by simp [NTree.children]) hv)
            have hfR : ∀ v, InTree pR.1 v → RowSubISA v.label := fun v hv =>
              hfrag' v (InTree.sub (by simp [NTree.children]) hv)
            obtain ⟨hresL, hrowL⟩ := ih hL hfL
            obtain ⟨hresR, hrowR⟩ := ih hR hfR
            have hkey : (Noun.cell pL.2 pR.2).leaves ≤
                (Noun.cell (Noun.cell lh lt) tl).leaves * subject.leaves := by
              have := Nat.add_le_add hresL hresR
              simpa [cell_leaves, Nat.add_mul] using this
            refine ⟨hkey, ?_⟩
            intro u hu
            cases hu with
            | here => exact ⟨rfl, le_refl _, hkey⟩
            | sub hs hu' =>
              simp [NTree.children] at hs
              rcases hs with rfl | rfl
              · obtain ⟨h1, h2, h3⟩ := hrowL u hu'
                exact ⟨h1, le_trans h2 (leaves_le_cell_left _ _),
                  le_trans h3 (mul_leaves_mono _ (leaves_le_cell_left _ _))⟩
              · obtain ⟨h1, h2, h3⟩ := hrowR u hu'
                exact ⟨h1, le_trans h2 (leaves_le_cell_right _ _),
                  le_trans h3 (mul_leaves_mono _ (leaves_le_cell_right _ _))⟩
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · -- OP_0: a slot of the subject.
          cases tl with
          | cell _ _ => simp [genComputeSkeleton] at h
          | atom ax =>
            cases hslot : Noun.slot ax subject with
            | none => simp [genComputeSkeleton, hslot] at h
            | some r =>
              simp [genComputeSkeleton, hslot] at h
              obtain ⟨rfl, rfl⟩ := h
              have hkey : r.leaves ≤
                  (Noun.cell (Noun.atom 0) (Noun.atom ax)).leaves * subject.leaves :=
                le_trans (slot_leaves_le ax subject hslot) (leaves_le_mul_formula _ _)
              refine ⟨hkey, ?_⟩
              intro u hu
              cases hu with
              | here => exact ⟨rfl, le_refl _, hkey⟩
              | sub hs _ => simp [NTree.children] at hs
        · -- OP_1: the formula tail.
          simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          have hkey : tl.leaves ≤ (Noun.cell (Noun.atom 1) tl).leaves * subject.leaves :=
            le_trans (leaves_le_cell_right _ _) (leaves_le_mul_subject _ _)
          refine ⟨hkey, ?_⟩
          intro u hu
          cases hu with
          | here => exact ⟨rfl, le_refl _, hkey⟩
          | sub hs _ => simp [NTree.children] at hs
        · -- OP_2 — excluded: the third call runs against the computed `sf1`.
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ => simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact absurd (rfl : _ = State.s2) ((hfrag' _ (InTree.here _)).1)
        · -- OP_3: an atom.
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            have hfc : ∀ v, InTree p.1 v → RowSubISA v.label := fun v hv =>
              hfrag' v (InTree.sub (by simp [NTree.children]) hv)
            obtain ⟨_, hrow⟩ := ih hcall hfc
            have hkey : (Noun.wut p.2).leaves ≤
                (Noun.cell (Noun.atom 3) tl).leaves * subject.leaves := by
              have : (Noun.wut p.2).leaves = 1 := by
                cases p.2 <;> simp [Noun.wut, atom_leaves]
              rw [this]
              exact one_le_mul_leaves _ _
            refine ⟨hkey, ?_⟩
            intro u hu
            cases hu with
            | here => exact ⟨rfl, le_refl _, hkey⟩
            | sub hs hu' =>
              simp [NTree.children] at hs
              cases hs
              obtain ⟨h1, h2, h3⟩ := hrow u hu'
              exact ⟨h1, le_trans h2 (leaves_le_cell_right _ _),
                le_trans h3 (mul_leaves_mono _ (leaves_le_cell_right _ _))⟩
        · -- OP_4: an atom.
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none => simp [genComputeSkeleton, hcall, hlus] at h
            | some r =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              have hfc : ∀ v, InTree p.1 v → RowSubISA v.label := fun v hv =>
                hfrag' v (InTree.sub (by simp [NTree.children]) hv)
              obtain ⟨_, hrow⟩ := ih hcall hfc
              have hratom : r.leaves = 1 := by
                cases hp : p.2 with
                | atom k => rw [hp] at hlus; simp [Noun.lus] at hlus; subst hlus; simp [atom_leaves]
                | cell _ _ => rw [hp] at hlus; simp [Noun.lus] at hlus
              have hkey : r.leaves ≤ (Noun.cell (Noun.atom 4) tl).leaves * subject.leaves := by
                rw [hratom]; exact one_le_mul_leaves _ _
              refine ⟨hkey, ?_⟩
              intro u hu
              cases hu with
              | here => exact ⟨rfl, le_refl _, hkey⟩
              | sub hs hu' =>
                simp [NTree.children] at hs
                cases hs
                obtain ⟨h1, h2, h3⟩ := hrow u hu'
                exact ⟨h1, le_trans h2 (leaves_le_cell_right _ _),
                  le_trans h3 (mul_leaves_mono _ (leaves_le_cell_right _ _))⟩
        · -- OP_5: an atom; both operands run against the SAME subject.
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                have hfB : ∀ v, InTree pB.1 v → RowSubISA v.label := fun v hv =>
                  hfrag' v (InTree.sub (by simp [NTree.children]) hv)
                have hfC : ∀ v, InTree pC.1 v → RowSubISA v.label := fun v hv =>
                  hfrag' v (InTree.sub (by simp [NTree.children]) hv)
                obtain ⟨_, hrowB⟩ := ih hB hfB
                obtain ⟨_, hrowC⟩ := ih hC hfC
                have hbc : b.leaves ≤ (Noun.cell (Noun.atom 5) (Noun.cell b c)).leaves ∧
                    c.leaves ≤ (Noun.cell (Noun.atom 5) (Noun.cell b c)).leaves := by
                  simp only [cell_leaves, atom_leaves]
                  omega
                have hkey : (Noun.tis pB.2 pC.2).leaves ≤
                    (Noun.cell (Noun.atom 5) (Noun.cell b c)).leaves * subject.leaves := by
                  have : (Noun.tis pB.2 pC.2).leaves = 1 := by
                    unfold Noun.tis; split <;> simp [atom_leaves]
                  rw [this]
                  exact one_le_mul_leaves _ _
                refine ⟨hkey, ?_⟩
                intro u hu
                cases hu with
                | here => exact ⟨rfl, le_refl _, hkey⟩
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · obtain ⟨h1, h2, h3⟩ := hrowB u hu'
                    exact ⟨h1, le_trans h2 hbc.1, le_trans h3 (mul_leaves_mono _ hbc.1)⟩
                  · obtain ⟨h1, h2, h3⟩ := hrowC u hu'
                    exact ⟨h1, le_trans h2 hbc.2, le_trans h3 (mul_leaves_mono _ hbc.2)⟩
        · -- OP_6: condition and taken branch both run against the SAME subject.
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              have hsub : b.leaves ≤
                    (Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d))).leaves ∧
                  c.leaves ≤
                    (Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d))).leaves ∧
                  d.leaves ≤
                    (Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d))).leaves := by
                simp only [cell_leaves, atom_leaves]
                omega
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ => simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ => simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ => simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hf1 : ∀ v, InTree pCond.1 v → RowSubISA v.label := fun v hv =>
                        hfrag' v (InTree.sub (by simp [NTree.children]) hv)
                      have hf2 : ∀ v, InTree pTaken.1 v → RowSubISA v.label := fun v hv =>
                        hfrag' v (InTree.sub (by simp [NTree.children]) hv)
                      obtain ⟨_, hrow1⟩ := ih hcond hf1
                      obtain ⟨hres2, hrow2⟩ := ih htaken hf2
                      have hkey := le_trans hres2 (mul_leaves_mono subject hsub.2.1)
                      refine ⟨hkey, ?_⟩
                      intro u hu
                      cases hu with
                      | here => exact ⟨rfl, le_refl _, hkey⟩
                      | sub hs hu' =>
                        simp [NTree.children] at hs
                        rcases hs with rfl | rfl
                        · obtain ⟨h1, h2, h3⟩ := hrow1 u hu'
                          exact ⟨h1, le_trans h2 hsub.1,
                            le_trans h3 (mul_leaves_mono _ hsub.1)⟩
                        · obtain ⟨h1, h2, h3⟩ := hrow2 u hu'
                          exact ⟨h1, le_trans h2 hsub.2.1,
                            le_trans h3 (mul_leaves_mono _ hsub.2.1)⟩
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ => simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        obtain ⟨rfl, rfl⟩ := h
                        have hf1 : ∀ v, InTree pCond.1 v → RowSubISA v.label := fun v hv =>
                          hfrag' v (InTree.sub (by simp [NTree.children]) hv)
                        have hf2 : ∀ v, InTree pTaken.1 v → RowSubISA v.label := fun v hv =>
                          hfrag' v (InTree.sub (by simp [NTree.children]) hv)
                        obtain ⟨_, hrow1⟩ := ih hcond hf1
                        obtain ⟨hres2, hrow2⟩ := ih htaken hf2
                        have hkey := le_trans hres2 (mul_leaves_mono subject hsub.2.2)
                        refine ⟨hkey, ?_⟩
                        intro u hu
                        cases hu with
                        | here => exact ⟨rfl, le_refl _, hkey⟩
                        | sub hs hu' =>
                          simp [NTree.children] at hs
                          rcases hs with rfl | rfl
                          · obtain ⟨h1, h2, h3⟩ := hrow1 u hu'
                            exact ⟨h1, le_trans h2 hsub.1,
                              le_trans h3 (mul_leaves_mono _ hsub.1)⟩
                          · obtain ⟨h1, h2, h3⟩ := hrow2 u hu'
                            exact ⟨h1, le_trans h2 hsub.2.2,
                              le_trans h3 (mul_leaves_mono _ hsub.2.2)⟩
                    | succ _ => simp [genComputeSkeleton, hcond, hval] at h
        · -- OP_7 — excluded: `c` runs against the computed `sb`.
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                exact absurd (rfl : _ = State.s7) ((hfrag' _ (InTree.here _)).2.1)
        · -- OP_8 — excluded: `c` runs against the pushed `[sb a]`.
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                exact absurd (rfl : _ = State.s8) ((hfrag' _ (InTree.here _)).2.2.1)
        · -- OP_9 — excluded: the arm runs against the computed core.
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot ax pCore.2 with
                | none => simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ => simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact absurd (rfl : _ = State.s9) ((hfrag' _ (InTree.here _)).2.2.2)
        · -- OP_10: not in the ROM.
          simp [genComputeSkeleton] at h
        · -- OP_11: not in the ROM.
          simp [genComputeSkeleton] at h
        · -- ≥ 12: malformed.
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

/-- **On the sub-ISA the window is DERIVED, not measured.**

`TraceConfined Λ t` is `∀ g ∈ bfsRows t, subject/formula/evaluation each `≤ Λ``.  Taking
`Λ := formula.leaves * subject.leaves` — a number computed from the program text and its input,
with no evaluation — the three bounds come from `genComputeSkeleton_subISA_bound`: the subject is
the root subject, the formula is a subterm of the root formula, and the evaluation is bounded
directly. -/
theorem genComputeSkeleton_subISA_traceConfined
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hfrag : SubISA t) :
    TraceConfined (formula.leaves * subject.leaves) t := by
  obtain ⟨_, hrow⟩ := genComputeSkeleton_subISA_bound h hfrag
  refine (forall_bfsRows_iff t).mpr ?_
  intro u hu
  obtain ⟨h1, h2, h3⟩ := hrow u hu
  exact ⟨by rw [h1]; exact leaves_le_mul_formula _ _,
    le_trans h2 (leaves_le_mul_subject _ _), h3⟩

/-! ## Non-vacuity

Two checks that the fragment is a real restriction and that the derived theorem is usable.

* Tier A's own program is **outside** the fragment: it is an `OP_6` whose taken branch is an `OP_2`
  wrapping an `OP_9` (`GenTierA.lean`), so `SubISA` fails on it and the measured `TraceConfined 22`
  of `Batch164` remains the only route there.
* A small `OP_4`/`OP_0` program **is** on the fragment, and its window comes out of the theorem
  with no measurement at all. -/

/-- **Tier A's `dotTree` is not on the sub-ISA** — it carries an `OP_9` row (and an `OP_2` row).
So the fragment excludes the repo's own headline generated program, and the derived window below
is not silently covering the measured case. -/
theorem dotTree_not_subISA : ¬ SubISA (dotTree (K := K)) := by
  intro hsub
  obtain ⟨u, hu, hst⟩ := dotTree_has_s9 (K := K)
  have hrow : RowSubISA u.label := by
    refine hsub u.label ?_
    simp only [bfsRows, List.mem_map]
    exact ⟨u, hu, rfl⟩
  exact hrow.2.2.2 hst

/-! ### A program that IS on the fragment: `*[7 [4 [0 1]]] = 8` -/

/-- The sample subject `7`. -/
def sampleSubject : Noun := .atom 7

/-- The sample formula `[4 [0 1]]` — increment the whole subject. -/
def sampleFormula : Noun := .cell (.atom 4) (.cell (.atom 0) (.atom 1))

/-- `*[7 [4 [0 1]]] = 8`. -/
def sampleResult : Noun := .atom 8

theorem sample_slot : Noun.slot 1 sampleSubject = some sampleSubject := by
  simp [Noun.slot]

/-- The `OP_0` leaf row: read axis `1` of the subject. -/
def sampleChild : NTree (GenComputeRow K) :=
  .node (skelNode
    (genSkelOp0 sampleSubject (.cell (.atom 0) (.atom 1)) (.atom 0) (.atom 1) sampleSubject 1)
    [⟨.cell (.atom 0) (.atom 1), .atom 1, 3, 0⟩, ⟨sampleSubject, sampleSubject, 1, 0⟩]) []

/-- The `OP_4` root row with the `OP_0` leaf as its single child. -/
def sampleTree : NTree (GenComputeRow K) :=
  .node (skelNode
    (genSkelOp4 sampleSubject sampleFormula (.atom 4) (.cell (.atom 0) (.atom 1))
      sampleSubject (.cell (.atom 0) (.atom 1)) sampleSubject sampleResult)
    [⟨sampleFormula, .cell (.atom 0) (.atom 1), 3, 0⟩]) [sampleChild]

/-- The generator accepts the sample program. -/
theorem genComputeSkeleton_sample :
    genComputeSkeleton (K := K) 3 sampleSubject sampleFormula
      = .ok (sampleTree, sampleResult) := by
  show genComputeSkeleton (2 + 1) sampleSubject sampleFormula = _
  simp only [genComputeSkeleton, sampleFormula, sample_slot]
  rfl

theorem sampleTree_state : (sampleTree (K := K)).label.skel.state = State.s4 := rfl

theorem sampleChild_state : (sampleChild (K := K)).label.skel.state = State.s0 := rfl

/-- The sample tree is on the fragment: `OP_4` over `OP_0`, no `OP_2`/`OP_7`/`OP_8`/`OP_9`. -/
theorem sampleTree_subISA : SubISA (sampleTree (K := K)) := by
  refine subISA_of_inTree ?_
  intro u hu
  cases hu with
  | here => refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [sampleTree_state] <;> decide
  | sub hs hu' =>
    simp only [sampleTree, NTree.children, List.mem_singleton] at hs
    subst hs
    cases hu' with
    | here => refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [sampleChild_state] <;> decide
    | sub hs' _ => simp [sampleChild, NTree.children] at hs'

/-- **The derived window at the sample program.**  No `decide` on row nouns, no measurement: the
number comes out of `genComputeSkeleton_subISA_traceConfined`. -/
theorem sample_traceConfined :
    TraceConfined (sampleFormula.leaves * sampleSubject.leaves) (sampleTree (K := K)) :=
  genComputeSkeleton_subISA_traceConfined genComputeSkeleton_sample sampleTree_subISA

/-- And the number is `3 = |[4 [0 1]]| * |7|`, read off the program text and its input. -/
theorem sample_window_value : sampleFormula.leaves * sampleSubject.leaves = 3 := by decide

/-- The same statement with the number in place. -/
theorem sample_traceConfined_three : TraceConfined 3 (sampleTree (K := K)) :=
  sample_window_value ▸ sample_traceConfined


/-! ### A second witness, exercising `cons`

The `OP_4`/`OP_0` sample above never builds a pair, so it does not test the case the product window
is actually shaped for: `cons` is the one rule whose result is the *sum* of two sub-results, and it
is harmless here only because both halves are bounded against the **same** subject.  This witness
exercises it. -/

/-- The subject `[1 2]` — two leaves, so the cons result genuinely grows. -/
def consSubject : Noun := .cell (.atom 1) (.atom 2)

/-- `[0 1]`, the whole-subject read. -/
def zeroOne : Noun := .cell (.atom 0) (.atom 1)

/-- `[[0 1] [0 1]]` — autocons of two subject reads, so `*[a [[0 1] [0 1]]] = [a a]`. -/
def consFormula : Noun := .cell zeroOne zeroOne

theorem cons_slot : Noun.slot 1 consSubject = some consSubject := by
  simp [Noun.slot]

def consLeaf : NTree (GenComputeRow K) :=
  .node (skelNode
    (genSkelOp0 consSubject zeroOne (.atom 0) (.atom 1) consSubject 1)
    [⟨zeroOne, .atom 1, 3, 0⟩, ⟨consSubject, consSubject, 1, 0⟩]) []

def consTree : NTree (GenComputeRow K) :=
  .node (skelNode
    (genSkelCons consSubject zeroOne zeroOne consSubject consSubject)
    [⟨consFormula, zeroOne, 3, 0⟩]) [consLeaf, consLeaf]

theorem genComputeSkeleton_consSample :
    genComputeSkeleton (K := K) 3 consSubject consFormula
      = .ok (consTree, .cell consSubject consSubject) := by
  show genComputeSkeleton (2 + 1) consSubject consFormula = _
  simp only [genComputeSkeleton, consFormula, zeroOne, cons_slot]
  rfl

theorem consTree_state : (consTree (K := K)).label.skel.state = State.cons := rfl

theorem consLeaf_state : (consLeaf (K := K)).label.skel.state = State.s0 := rfl

theorem consTree_subISA : SubISA (consTree (K := K)) := by
  refine subISA_of_inTree ?_
  intro u hu
  cases hu with
  | here => refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [consTree_state] <;> decide
  | sub hs hu' =>
    simp only [consTree, NTree.children, List.mem_cons, List.not_mem_nil, or_false,
      or_self] at hs
    subst hs
    cases hu' with
    | here => refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [consLeaf_state] <;> decide
    | sub hs' _ => simp [consLeaf, NTree.children] at hs'

/-- **The derived window at a program that builds a pair.** -/
theorem cons_traceConfined :
    TraceConfined (consFormula.leaves * consSubject.leaves) (consTree (K := K)) :=
  genComputeSkeleton_subISA_traceConfined genComputeSkeleton_consSample consTree_subISA

/-- The derived number is `8 = |[[0 1] [0 1]]| * |[1 2]|`. -/
theorem cons_window_value : consFormula.leaves * consSubject.leaves = 8 := by decide

/-- The trace's largest noun is the result `[a a]`, at four leaves.  So the derived window is
**sound and loose** — a factor two here, which is what `cons`'s `f_l + f_r` costs against the
`(f_l + f_r) · s` bound.  Stated rather than hidden: the fragment result is a usable `Λ`, not the
least one. -/
theorem cons_result_leaves : (Noun.cell consSubject consSubject).leaves = 4 := by decide

theorem cons_traceConfined_eight : TraceConfined 8 (consTree (K := K)) :=
  cons_window_value ▸ cons_traceConfined

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.slot_leaves_le
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_subISA_bound
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_subISA_traceConfined
#print axioms Nock.NockVMROM.Thm54.TraceGen.dotTree_not_subISA
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_sample
#print axioms Nock.NockVMROM.Thm54.TraceGen.sample_traceConfined
#print axioms Nock.NockVMROM.Thm54.TraceGen.sample_traceConfined_three
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_consSample
#print axioms Nock.NockVMROM.Thm54.TraceGen.cons_traceConfined_eight
