/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenericSelfPairs.lean

  **Which census comparisons of a generated row are self-pairs, per state.**

  `z ∉ badSeeds` is one of the counted seed events `genSemanticData` carries, and
  `ComparisonCensus.mem_badSeeds_iff` reduces it to `GlobalCarryRecognizer.SepSeed z L R` at every
  pair of `BoundSemanticTrace.skeletonPairs`.  `SepSeed z P P` is trivially true, so the cost of the
  premise at a given program is exactly its **off-diagonal** pairs — the ones where the two compared
  nouns genuinely differ.

  What was missing is the middle layer: **which comparisons are self-pairs by
  construction, at each state, for every program.**  That is what this module supplies, one lemma
  per `genSkelOp*`, read off the constructor's own fields against
  `P8Census.skeletonComparisons`.

  The result is that only two arms have an off-diagonal comparison at all:

  * `.s5` — `equalityOperand (sf 0 result) (sf 1 result)`, i.e. the two OP5 operands, off-diagonal
    exactly when the operands differ;
  * `.s6` — `recursiveFormula (sf 0 formula)` against **both** branch formulas, so the untaken
    branch is off-diagonal exactly when the two branches differ (Tier A's single pair).

  Every other comparison of every other arm is a self-pair for structural reasons, with two stated
  side conditions: `.s0` needs its axis atom to be the record axis (which the generator's own
  emission guarantees), and `.s4` needs `incMod (ringChar K)` to agree with `Noun.lus` on the call's
  result, i.e. no wrap — the same no-overflow condition `FieldEmbedding.evalGBy` carries.
-/
import Nock.NockVMROM.Thm54.BoundSemanticTrace
import Nock.NockVMROM.Thm54.TraceGen.Gen

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.P8Census
open ComputeTable

variable {K : Type} [Field K]

/-! ## `SepSeed` is trivial on a self-pair -/

/-- `SepSeed` has a hypothesis that fails on a diagonal pair, so it holds vacuously. -/
theorem sepSeed_self (z : K) (P : Noun) : GlobalCarryRecognizer.SepSeed z P P :=
  fun h => absurd rfl h

theorem sepSeed_of_eq {z : K} {P Q : Noun} (h : P = Q) :
    GlobalCarryRecognizer.SepSeed z P Q := by
  subst h; exact sepSeed_self z P

/-! ## The arms with no off-diagonal comparison -/

/-- `OP_1`: all three comparisons are self-pairs. -/
theorem selfPairs_genSkelOp1 (subject result : Noun) :
    ∀ c ∈ skeletonComparisons (K := K)
        (genSkelOp1 subject (.cell (.atom 1) result) result (.atom 1)),
      c.left = c.right := by
  intro c hc
  simp only [skeletonComparisons, genSkelOp1, skeletonDec, SemanticStrategy.decActive,
    ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rfl

/-- `OP_0`: all three comparisons are self-pairs, the third because the row's `mr2` axis **is**
the formula-tail atom. -/
theorem selfPairs_genSkelOp0 (subject result : Noun) (ax : ℕ) :
    ∀ c ∈ skeletonComparisons (K := K)
        (genSkelOp0 subject (.cell (.atom 0) (.atom ax)) (.atom 0) (.atom ax) result ax),
      c.left = c.right := by
  intro c hc
  simp only [skeletonComparisons, genSkelOp0, skeletonDec, skeletonMemoryAxis,
    SemanticStrategy.decActive, Nock.Framework.recordCount, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rfl

/-- Autocons: all six comparisons are self-pairs. -/
theorem selfPairs_genSkelCons (subject leftF rightF leftR rightR : Noun) :
    ∀ c ∈ skeletonComparisons (K := K) (genSkelCons subject leftF rightF leftR rightR),
      c.left = c.right := by
  intro c hc
  simp only [skeletonComparisons, genSkelCons, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `OP_3`: all five comparisons are self-pairs — the produced result **is** `Noun.wut` of the
call's result by construction, so the cell-test comparison costs nothing. -/
theorem selfPairs_genSkelOp3 (subject tail callResult : Noun) :
    ∀ c ∈ skeletonComparisons (K := K)
        (genSkelOp3 subject (.cell (.atom 3) tail) (.atom 3) tail subject tail callResult
          (Noun.wut callResult)),
      c.left = c.right := by
  intro c hc
  simp only [skeletonComparisons, genSkelOp3, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `OP_4`: all five comparisons are self-pairs **provided the increment does not wrap** — the
census compares the row's evaluation against the paper's modular target `incMod (ringChar K)`
(`P8Census.lean:311`), while the generator emits `Noun.lus`.  They agree exactly when the call's
result is an atom below the characteristic, which is what `evalGBy`'s `lusGBy` guard already
requires of the program. -/
theorem selfPairs_genSkelOp4 (subject tail callResult result : Noun)
    (hinc : OpcodeSemantics.incMod (ringChar K) callResult = result) :
    ∀ c ∈ skeletonComparisons (K := K)
        (genSkelOp4 subject (.cell (.atom 4) tail) (.atom 4) tail subject tail callResult result),
      c.left = c.right := by
  intro c hc
  simp only [skeletonComparisons, genSkelOp4, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hinc.symm

/-- `OP_7`: all eight comparisons are self-pairs, including the **threaded subject** pair
`(sf 0 subject, sf 1 result)` — slot `0`'s subject is the helper's evaluation by construction. -/
theorem selfPairs_genSkelOp7 (subject fTh fTt sb result : Noun) :
    ∀ c ∈ skeletonComparisons (K := K)
        (genSkelOp7 subject (.cell (.atom 7) (.cell fTh fTt)) (.atom 7) (.cell fTh fTt)
          fTh fTt sb result),
      c.left = c.right := by
  intro c hc
  simp only [skeletonComparisons, genSkelOp7, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `OP_8`: all eight comparisons are self-pairs, including the **pushed subject** pair
`(sf 0 subject,.cell (sf 1 result) subject)`. -/
theorem selfPairs_genSkelOp8 (subject fTh fTt sb result : Noun) :
    ∀ c ∈ skeletonComparisons (K := K)
        (genSkelOp8 subject (.cell (.atom 8) (.cell fTh fTt)) (.atom 8) (.cell fTh fTt)
          fTh fTt sb result),
      c.left = c.right := by
  intro c hc
  simp only [skeletonComparisons, genSkelOp8, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `OP_2`: all eleven comparisons are self-pairs — both the computed subject
`(sf 2 subject, sf 0 result)` and the computed formula `(sf 2 formula, sf 1 result)`. -/
theorem selfPairs_genSkelOp2 (subject fTh fTt sf1 sf2 result : Noun) :
    ∀ c ∈ skeletonComparisons (K := K)
        (genSkelOp2 subject (.cell (.atom 2) (.cell fTh fTt)) (.atom 2) (.cell fTh fTt)
          fTh fTt sf1 sf2 result),
      c.left = c.right := by
  intro c hc
  simp only [skeletonComparisons, genSkelOp2, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `OP_9`: all eight comparisons are self-pairs, including the axis atom against the served
record's axis and the mutated subject `(sf 1 subject, sf 0 result)`. -/
theorem selfPairs_genSkelOp9 (subject fTt core arm result : Noun) (ax : ℕ) :
    ∀ c ∈ skeletonComparisons (K := K)
        (genSkelOp9 subject (.cell (.atom 9) (.cell (.atom ax) fTt)) (.atom 9)
          (.cell (.atom ax) fTt) (.atom ax) fTt core arm result ax),
      c.left = c.right := by
  intro c hc
  simp only [skeletonComparisons, genSkelOp9, skeletonDec, skeletonSubformula,
    skeletonMemoryAxis, SemanticStrategy.decActive, ComputeTable.fanoutComp,
    Nock.Framework.recordCount, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The two arms that do have an off-diagonal comparison -/

/-- `OP_5`: every comparison is a self-pair **except** `equalityOperand`, which compares the two
operands `(sf1, sf2)`.  That one is off-diagonal exactly when the operands differ, and it is the
whole cost of `hbad` at an `OP_5` row. -/
theorem selfPairs_genSkelOp5 (subject fTh fTt sf1 sf2 : Noun) :
    ∀ c ∈ skeletonComparisons (K := K)
        (genSkelOp5 subject (.cell (.atom 5) (.cell fTh fTt)) (.atom 5) (.cell fTh fTt)
          fTh fTt sf1 sf2 (Noun.tis sf1 sf2)),
      c.left = c.right ∨ (c.left = sf1 ∧ c.right = sf2) := by
  intro c hc
  simp only [skeletonComparisons, genSkelOp5, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl rfl

/-- `OP_6`, THEN taken: every comparison is a self-pair **except** the second `recursiveFormula`
occurrence, which compares the taken branch against the **untaken** one.  This is Tier A's single
off-diagonal pair (`Batch180.dot_offdiagonal_count`). -/
theorem selfPairs_genSkelOp6_then (subject fTh c d result : Noun) :
    ∀ u ∈ skeletonComparisons (K := K)
        (genSkelOp6 subject (.cell (.atom 6) (.cell fTh (.cell c d))) (.atom 6)
          (.cell fTh (.cell c d)) fTh (.cell c d) c d (.atom 0) c result),
      u.left = u.right ∨ (u.left = c ∧ u.right = d) := by
  intro u hu
  simp only [skeletonComparisons, genSkelOp6, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- `OP_6`, ELSE taken: the off-diagonal `recursiveFormula` is now the **THEN** branch, because
slot `0`'s formula is the taken ELSE formula `d` and the census still compares it to both
`f_tth = c` and `f_ttt = d`. -/
theorem selfPairs_genSkelOp6_else (subject fTh c d result : Noun) :
    ∀ u ∈ skeletonComparisons (K := K)
        (genSkelOp6 subject (.cell (.atom 6) (.cell fTh (.cell c d))) (.atom 6)
          (.cell fTh (.cell c d)) fTh (.cell c d) c d (.atom 1) d result),
      u.left = u.right ∨ (u.left = d ∧ u.right = c) := by
  intro u hu
  simp only [skeletonComparisons, genSkelOp6, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

/-! ## Role-aware forms, for the generic off-diag classifier -/

/-- `OP_5` off-diagonal comparison is exactly `equalityOperand`. -/
theorem selfPairs_genSkelOp5_off (subject fTh fTt sf1 sf2 : Noun) :
    ∀ c ∈ skeletonComparisons (K := K)
        (genSkelOp5 subject (.cell (.atom 5) (.cell fTh fTt)) (.atom 5) (.cell fTh fTt)
          fTh fTt sf1 sf2 (Noun.tis sf1 sf2)),
      c.left = c.right
        ∨ (c.role = .equalityOperand ∧ c.left = sf1 ∧ c.right = sf2) := by
  intro c hc
  simp only [skeletonComparisons, genSkelOp5, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl rfl

/-- `OP_6` THEN: the off-diagonal comparison is a `recursiveFormula`. -/
theorem selfPairs_genSkelOp6_then_off (subject fTh c d result : Noun) :
    ∀ u ∈ skeletonComparisons (K := K)
        (genSkelOp6 subject (.cell (.atom 6) (.cell fTh (.cell c d))) (.atom 6)
          (.cell fTh (.cell c d)) fTh (.cell c d) c d (.atom 0) c result),
      u.left = u.right
        ∨ (u.role = .recursiveFormula ∧ u.left = c ∧ u.right = d) := by
  intro u hu
  simp only [skeletonComparisons, genSkelOp6, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- `OP_6` ELSE: the off-diagonal comparison is a `recursiveFormula`. -/
theorem selfPairs_genSkelOp6_else_off (subject fTh c d result : Noun) :
    ∀ u ∈ skeletonComparisons (K := K)
        (genSkelOp6 subject (.cell (.atom 6) (.cell fTh (.cell c d))) (.atom 6)
          (.cell fTh (.cell c d)) fTh (.cell c d) c d (.atom 1) d result),
      u.left = u.right
        ∨ (u.role = .recursiveFormula ∧ u.left = d ∧ u.right = c) := by
  intro u hu
  simp only [skeletonComparisons, genSkelOp6, skeletonDec, skeletonSubformula,
    SemanticStrategy.decActive, ComputeTable.fanoutComp, List.mem_cons, List.not_mem_nil,
    or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.sepSeed_self
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp0
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp1
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp2
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp3
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp4
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp5
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp6_then
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp6_else
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp5_off
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp6_then_off
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp6_else_off
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp7
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp8
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp9
#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelCons
