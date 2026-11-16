/-
  Nock/NockVMROM/Thm54/TraceGen/GenLeafWindow.lean

  `RowLeafWindow Λ s` (`CensusExtraClosure.lean:1306`) is the per-row form of the paper's
  `Def[Nock Program]` window: subject, formula, evaluation and every subformula
  slot have at most `Λ` leaves.  It is the terminal object of the **parked `census` premise**, and
  the remaining half of `rowBad_card_le_of_shape`'s hypotheses once `GenConsHead` supplies the shape.

  They are
  **program-generic as written**, taking only leaf bounds on the constructor's own arguments, so they
  are ported here verbatim in substance and compiled for the first time.

  **What is NOT ported, and why.** So that step is not carried over.

  **But the growth invariant is the wrong object**.  The paper does *not* bound
  intermediate verbs by deriving a growth bound; it carries `λ ≤ Λ` as a **membership condition** of
  its languages -- `NockVM^Λ` and `FiniteTransitions^Λ` (`:1147`) each conjoin
  `λ ≤ Λ` to the verb, and `Trace.lean:352,356` mirrors that exactly
  (`FiniteΛ Λ F := Finite F ∧ size F ≤ Λ`).  So a per-row window is to be *projected from a
  Λ-confinement hypothesis*, not proved by induction on evaluation growth.  Proving `leaves ≤ Λ`
  outright would establish something the paper does not claim.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenConsHead
import Nock.NockVMROM.Thm54.BelowDefs.CensusExtraClosure

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable
open Nock.NockVMROM.Thm54.CensusExtraClosure

variable {K : Type} [Field K]

/-! ## Leaf arithmetic -/

theorem cell_leaves (a b : Noun) :
    (Noun.cell a b).leaves = a.leaves + b.leaves := rfl

theorem atom_leaves (k : ℕ) : (Noun.atom k).leaves = 1 := rfl

theorem leaves_pos (n : Noun) : 1 ≤ n.leaves := by
  induction n with
  | atom _ => simp [atom_leaves]
  | cell _ _ ihl ihr => simp [cell_leaves]; omega

theorem two_le_cell_leaves (a b : Noun) : 2 ≤ (Noun.cell a b).leaves := by
  have := leaves_pos a
  have := leaves_pos b
  simp [cell_leaves]; omega

theorem leaves_le_cell_left (a b : Noun) :
    a.leaves ≤ (Noun.cell a b).leaves :=
  Nat.le_add_right _ _

theorem leaves_le_cell_right (a b : Noun) :
    b.leaves ≤ (Noun.cell a b).leaves :=
  Nat.le_add_left _ _

theorem atom_leaves_le {Λ : ℕ} (hΛ : 1 ≤ Λ) (k : ℕ) :
    (Noun.atom k).leaves ≤ Λ := by
  simpa [atom_leaves] using hΛ

/-! ## The doubling bound

The reason a leaf window is not simply inherited: `cons` adds its two branches' leaf counts, so an
evaluation can reach twice the max of the formula and subject counts. -/

theorem le_two_mul_of_le_sup {r F S : ℕ} (h : r ≤ F ⊔ S) :
    r ≤ 2 * (F ⊔ S) :=
  le_trans h (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))

theorem add_le_two_mul_max (a b : ℕ) : a + b ≤ 2 * (a ⊔ b) := by
  calc
    a + b ≤ (a ⊔ b) + (a ⊔ b) := Nat.add_le_add le_sup_left le_sup_right
    _ = 2 * (a ⊔ b) := (two_mul _).symm

/-- **The `cons` growth bound**: two branch results within their own windows compose to at most
twice the max of the joined formula and the subject. -/
theorem cons_leaves_two_sup {eL eR FL FR S : ℕ}
    (hL : eL ≤ FL ⊔ S) (hR : eR ≤ FR ⊔ S) :
    eL + eR ≤ 2 * ((FL + FR) ⊔ S) :=
  le_trans (Nat.add_le_add hL hR) <|
    le_trans (add_le_two_mul_max (FL ⊔ S) (FR ⊔ S)) <|
      Nat.mul_le_mul_left 2 <|
        sup_le
          (sup_le (le_trans (Nat.le_add_right FL FR) le_sup_left) le_sup_right)
          (sup_le (le_trans (Nat.le_add_left FR FL) le_sup_left) le_sup_right)

/-! ## OP6 subformula projections (needed by the OP6 window) -/

theorem genSkelOp6_sf0 (subject formula head fTail fTh fTt fTth fTtt cond taken result : Noun)
    (slot : SemanticStrategy.TripleSlot) :
    P8Census.skeletonSubformula
      (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt cond taken result)
      ⟨0, by decide⟩ slot =
      match slot with
      | .subject => subject
      | .formula => taken
      | .result => result := by
  unfold P8Census.skeletonSubformula
  rw [dif_pos (by simp [genSkelOp6, ComputeTable.fanoutComp])]
  rfl

theorem genSkelOp6_sf1 (subject formula head fTail fTh fTt fTth fTtt cond taken result : Noun)
    (slot : SemanticStrategy.TripleSlot) :
    P8Census.skeletonSubformula
      (genSkelOp6 subject formula head fTail fTh fTt fTth fTtt cond taken result)
      ⟨1, by decide⟩ slot =
      match slot with
      | .subject => subject
      | .formula => fTh
      | .result => cond := by
  unfold P8Census.skeletonSubformula
  rw [dif_pos (by simp [genSkelOp6, ComputeTable.fanoutComp])]
  rfl

/-! ## Per-constructor leaf windows

One per skeleton constructor, each taking only leaf bounds on its own arguments. -/

theorem genSkelOp1_leafWindow {Λ : ℕ} {s f r hd : Noun} (hΛ : 1 ≤ Λ)
    (hs : s.leaves ≤ Λ) (hf : f.leaves ≤ Λ) (hr : r.leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelOp1 s f r hd) := by
  refine ⟨hs, hf, hr, ?_⟩
  intro i slot
  have hne : ¬ ((i : ℕ) < fanoutComp (genSkelOp1 s f r hd).state) := by
    simp [genSkelOp1, fanoutComp]
  simp [P8Census.skeletonSubformula, hne]
  exact atom_leaves_le hΛ 0

theorem genSkelOp0_leafWindow {Λ : ℕ} {s f hd tl r : Noun} {ax : ℕ}
    (hΛ : 1 ≤ Λ) (hs : s.leaves ≤ Λ) (hf : f.leaves ≤ Λ) (hr : r.leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelOp0 s f hd tl r ax) := by
  refine ⟨hs, hf, hr, ?_⟩
  intro i slot
  have hne : ¬ ((i : ℕ) < fanoutComp (genSkelOp0 s f hd tl r ax).state) := by
    simp [genSkelOp0, fanoutComp]
  simp [P8Census.skeletonSubformula, hne]
  exact atom_leaves_le hΛ 0

theorem genSkelCons_leafWindow {Λ : ℕ} {s lF rF lR rR : Noun} (hΛ : 1 ≤ Λ)
    (hs : s.leaves ≤ Λ)
    (hf : lF.leaves + rF.leaves ≤ Λ)
    (hlR : lR.leaves ≤ Λ) (hrR : rR.leaves ≤ Λ)
    (he : lR.leaves + rR.leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelCons s lF rF lR rR) := by
  have hlF : lF.leaves ≤ Λ := le_trans (Nat.le_add_right _ _) hf
  have hrF : rF.leaves ≤ Λ := le_trans (Nat.le_add_left _ _) hf
  refine ⟨hs, ?_, ?_, ?_⟩
  · simp [genSkelCons, cell_leaves]; exact hf
  · simp [genSkelCons, cell_leaves]; exact he
  · intro i slot
    fin_cases i
    · have hi : ((0 : Fin 3) : ℕ) <
          fanoutComp (genSkelCons s lF rF lR rR).state := by
        simp [genSkelCons, fanoutComp]
      simp [P8Census.skeletonSubformula, hi, genSkelCons]
      cases slot <;> simp <;> first | exact hs | exact hlF | exact hlR
    · have hi : ((1 : Fin 3) : ℕ) <
          fanoutComp (genSkelCons s lF rF lR rR).state := by
        simp [genSkelCons, fanoutComp]
      simp [P8Census.skeletonSubformula, hi, genSkelCons]
      cases slot <;> simp <;> first | exact hs | exact hrF | exact hrR
    · have hne : ¬ (((2 : Fin 3) : ℕ) <
          fanoutComp (genSkelCons s lF rF lR rR).state) := by
        simp [genSkelCons, fanoutComp]
      simp [P8Census.skeletonSubformula, hne]
      exact atom_leaves_le hΛ 0

theorem genSkelOp4_leafWindow {Λ : ℕ}
    {s f hd tl cS cF cR r : Noun} (hΛ : 1 ≤ Λ)
    (hs : s.leaves ≤ Λ) (hf : f.leaves ≤ Λ) (hr : r.leaves ≤ Λ)
    (hcS : cS.leaves ≤ Λ) (hcF : cF.leaves ≤ Λ) (hcR : cR.leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelOp4 s f hd tl cS cF cR r) := by
  refine ⟨hs, hf, hr, ?_⟩
  intro i slot
  fin_cases i
  · have hi : ((0 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp4 s f hd tl cS cF cR r).state := by
      simp [genSkelOp4, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp4]
    cases slot <;> simp <;> first | exact hcS | exact hcF | exact hcR
  · have hne : ¬ (((1 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp4 s f hd tl cS cF cR r).state) := by
      simp [genSkelOp4, fanoutComp]
    simp [P8Census.skeletonSubformula, hne]
    exact atom_leaves_le hΛ 0
  · have hne : ¬ (((2 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp4 s f hd tl cS cF cR r).state) := by
      simp [genSkelOp4, fanoutComp]
    simp [P8Census.skeletonSubformula, hne]
    exact atom_leaves_le hΛ 0

theorem genSkelOp3_leafWindow {Λ : ℕ}
    {s f hd tl cS cF cR r : Noun} (hΛ : 1 ≤ Λ)
    (hs : s.leaves ≤ Λ) (hf : f.leaves ≤ Λ) (hr : r.leaves ≤ Λ)
    (hcS : cS.leaves ≤ Λ) (hcF : cF.leaves ≤ Λ) (hcR : cR.leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelOp3 s f hd tl cS cF cR r) := by
  refine ⟨hs, hf, hr, ?_⟩
  intro i slot
  fin_cases i
  · have hi : ((0 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp3 s f hd tl cS cF cR r).state := by
      simp [genSkelOp3, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp3]
    cases slot <;> simp <;> first | exact hcS | exact hcF | exact hcR
  · have hne : ¬ (((1 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp3 s f hd tl cS cF cR r).state) := by
      simp [genSkelOp3, fanoutComp]
    simp [P8Census.skeletonSubformula, hne]
    exact atom_leaves_le hΛ 0
  · have hne : ¬ (((2 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp3 s f hd tl cS cF cR r).state) := by
      simp [genSkelOp3, fanoutComp]
    simp [P8Census.skeletonSubformula, hne]
    exact atom_leaves_le hΛ 0

theorem genSkelOp2_leafWindow {Λ : ℕ}
    {s f hd fT fTh fTt sf1 sf2 r : Noun} (hΛ : 1 ≤ Λ)
    (hs : s.leaves ≤ Λ) (hf : f.leaves ≤ Λ) (hr : r.leaves ≤ Λ)
    (hTh : fTh.leaves ≤ Λ) (hTt : fTt.leaves ≤ Λ)
    (h1 : sf1.leaves ≤ Λ) (h2 : sf2.leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelOp2 s f hd fT fTh fTt sf1 sf2 r) := by
  refine ⟨hs, hf, hr, ?_⟩
  intro i slot
  fin_cases i
  · have hi : ((0 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp2 s f hd fT fTh fTt sf1 sf2 r).state := by
      simp [genSkelOp2, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp2]
    cases slot <;> simp <;> first | exact hs | exact hTh | exact h1
  · have hi : ((1 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp2 s f hd fT fTh fTt sf1 sf2 r).state := by
      simp [genSkelOp2, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp2]
    cases slot <;> simp <;> first | exact hs | exact hTt | exact h2
  · have hi : ((2 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp2 s f hd fT fTh fTt sf1 sf2 r).state := by
      simp [genSkelOp2, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp2]
    cases slot <;> simp <;> first | exact h1 | exact h2 | exact hr

theorem genSkelOp5_leafWindow {Λ : ℕ}
    {s f hd fT fTh fTt sf1 sf2 r : Noun} (hΛ : 1 ≤ Λ)
    (hs : s.leaves ≤ Λ) (hf : f.leaves ≤ Λ) (hr : r.leaves ≤ Λ)
    (hTh : fTh.leaves ≤ Λ) (hTt : fTt.leaves ≤ Λ)
    (h1 : sf1.leaves ≤ Λ) (h2 : sf2.leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelOp5 s f hd fT fTh fTt sf1 sf2 r) := by
  refine ⟨hs, hf, hr, ?_⟩
  intro i slot
  fin_cases i
  · have hi : ((0 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp5 s f hd fT fTh fTt sf1 sf2 r).state := by
      simp [genSkelOp5, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp5]
    cases slot <;> simp <;> first | exact hs | exact hTh | exact h1
  · have hi : ((1 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp5 s f hd fT fTh fTt sf1 sf2 r).state := by
      simp [genSkelOp5, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp5]
    cases slot <;> simp <;> first | exact hs | exact hTt | exact h2
  · have hne : ¬ (((2 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp5 s f hd fT fTh fTt sf1 sf2 r).state) := by
      simp [genSkelOp5, fanoutComp]
    simp [P8Census.skeletonSubformula, hne]
    exact atom_leaves_le hΛ 0

theorem genSkelOp6_leafWindow {Λ : ℕ}
    {s f hd fT fTh fTt fTth fTtt cond taken r : Noun} (hΛ : 1 ≤ Λ)
    (hs : s.leaves ≤ Λ) (hf : f.leaves ≤ Λ) (hr : r.leaves ≤ Λ)
    (hTh : fTh.leaves ≤ Λ) (htk : taken.leaves ≤ Λ)
    (hc : cond.leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelOp6 s f hd fT fTh fTt fTth fTtt cond taken r) := by
  refine ⟨hs, hf, hr, ?_⟩
  intro i slot
  fin_cases i
  · rw [genSkelOp6_sf0]
    cases slot <;> simp <;> first | exact hs | exact htk | exact hr
  · rw [genSkelOp6_sf1]
    cases slot <;> simp <;> first | exact hs | exact hTh | exact hc
  · have hne : ¬ (((2 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp6 s f hd fT fTh fTt fTth fTtt cond taken r).state) := by
      simp [genSkelOp6, fanoutComp]
    simp [P8Census.skeletonSubformula, hne]
    exact atom_leaves_le hΛ 0

theorem genSkelOp7_leafWindow {Λ : ℕ}
    {s f hd fT fTh fTt sb r : Noun} (hΛ : 1 ≤ Λ)
    (hs : s.leaves ≤ Λ) (hf : f.leaves ≤ Λ) (hr : r.leaves ≤ Λ)
    (hTh : fTh.leaves ≤ Λ) (hTt : fTt.leaves ≤ Λ) (hsb : sb.leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelOp7 s f hd fT fTh fTt sb r) := by
  refine ⟨hs, hf, hr, ?_⟩
  intro i slot
  fin_cases i
  · have hi : ((0 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp7 s f hd fT fTh fTt sb r).state := by
      simp [genSkelOp7, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp7]
    cases slot <;> simp <;> first | exact hsb | exact hTt | exact hr
  · have hi : ((1 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp7 s f hd fT fTh fTt sb r).state := by
      simp [genSkelOp7, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp7]
    cases slot <;> simp <;> first | exact hs | exact hTh | exact hsb
  · have hne : ¬ (((2 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp7 s f hd fT fTh fTt sb r).state) := by
      simp [genSkelOp7, fanoutComp]
    simp [P8Census.skeletonSubformula, hne]
    exact atom_leaves_le hΛ 0

theorem genSkelOp8_leafWindow {Λ : ℕ}
    {s f hd fT fTh fTt sb r : Noun} (hΛ : 1 ≤ Λ)
    (hs : s.leaves ≤ Λ) (hf : f.leaves ≤ Λ) (hr : r.leaves ≤ Λ)
    (hTh : fTh.leaves ≤ Λ) (hTt : fTt.leaves ≤ Λ) (hsb : sb.leaves ≤ Λ)
    (hpush : (Noun.cell sb s).leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelOp8 s f hd fT fTh fTt sb r) := by
  refine ⟨hs, hf, hr, ?_⟩
  intro i slot
  fin_cases i
  · have hi : ((0 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp8 s f hd fT fTh fTt sb r).state := by
      simp [genSkelOp8, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp8]
    cases slot <;> simp [cell_leaves] <;> first | exact hpush | exact hTt | exact hr
  · have hi : ((1 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp8 s f hd fT fTh fTt sb r).state := by
      simp [genSkelOp8, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp8]
    cases slot <;> simp <;> first | exact hs | exact hTh | exact hsb
  · have hne : ¬ (((2 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp8 s f hd fT fTh fTt sb r).state) := by
      simp [genSkelOp8, fanoutComp]
    simp [P8Census.skeletonSubformula, hne]
    exact atom_leaves_le hΛ 0

theorem genSkelOp9_leafWindow {Λ : ℕ}
    {s f hd fT fTh fTt core arm r : Noun} {ax : ℕ} (hΛ : 1 ≤ Λ)
    (hs : s.leaves ≤ Λ) (hf : f.leaves ≤ Λ) (hr : r.leaves ≤ Λ)
    (hTt : fTt.leaves ≤ Λ) (hcore : core.leaves ≤ Λ) (harm : arm.leaves ≤ Λ) :
    RowLeafWindow Λ (genSkelOp9 s f hd fT fTh fTt core arm r ax) := by
  refine ⟨hs, hf, hr, ?_⟩
  intro i slot
  fin_cases i
  · have hi : ((0 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp9 s f hd fT fTh fTt core arm r ax).state := by
      simp [genSkelOp9, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp9]
    cases slot <;> simp <;> first | exact hs | exact hTt | exact hcore
  · have hi : ((1 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp9 s f hd fT fTh fTt core arm r ax).state := by
      simp [genSkelOp9, fanoutComp]
    simp [P8Census.skeletonSubformula, hi, genSkelOp9]
    cases slot <;> simp <;> first | exact hcore | exact harm | exact hr
  · have hne : ¬ (((2 : Fin 3) : ℕ) <
        fanoutComp (genSkelOp9 s f hd fT fTh fTt core arm r ax).state) := by
      simp [genSkelOp9, fanoutComp]
    simp [P8Census.skeletonSubformula, hne]
    exact atom_leaves_le hΛ 0

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp0_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp1_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp2_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp3_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp4_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp5_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp6_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp7_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp8_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelOp9_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSkelCons_leafWindow
