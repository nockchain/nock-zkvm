/-
  Nock/RedTeam/Batch1251Thm54HonestPairNotDiagonal.lean

  * §A `preZNoun_decompose_cell` / `reqPairs_not_diag`: a decompose row whose child list has two
    entries decodes to a cell (`decodePre`'s second clause), the target is `atom 0`, so the pair is
    off the diagonal.  The diagonal hypothesis of `pairBadSeeds_eq_empty_of_diag` is false there
    for every target map that sends `decompose` to `atom 0`, at every `envs`.
  * §B what such a pair costs: an off-diagonal pair whose two leaf counts differ is bad only at
    `z = 0` or at a root of unity of order dividing the leaf-count difference
    (`bad_of_leaves_ne`); an atom against `atom 0` is never bad (`atom_pair_never_bad`).  So the
    decompose / halt pairs are priced by a z-intrinsic set, but read_root / verify_child pairs are
    priced only by their own polynomial roots unless they are diagonal (not proved here).
-/
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.TraceGen.GenWorkloadBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch1251

open Nock Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Polynomial

/-! ## §A  Decompose rows are off the diagonal -/

section NotDiag

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {M : ℕ}

/-- A decompose node with two children decodes to a cell. -/
theorem decodePre_decompose_two {K : Type} [Field K] [Algebra F K] (q : ℕ) (a : F)
    (l r : NTree (MState × F)) :
    decodePre K q (.node (.decompose, a) [l, r]) = .cell (decodePre K q l) (decodePre K q r) := by
  simp [decodePre]

/-- **A decompose row with two in-range children decodes to a cell.** -/
theorem preZNoun_decompose_cell (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M) (i : ℕ)
    (hst : (preLblOfEnvs envs hM i).1 = .decompose)
    (hch : (childIdxsF kroots (preFoOfEnvs envs hM) M i).length = 2) :
    ∃ l r : Noun, preZNounOfEnvs K q kroots envs hM i = .cell l r := by
  unfold preZNounOfEnvs
  obtain ⟨j₁, j₂, hj⟩ : ∃ j₁ j₂, childIdxsF kroots (preFoOfEnvs envs hM) M i = [j₁, j₂] := by
    match h : childIdxsF kroots (preFoOfEnvs envs hM) M i, hch with
    | [j₁, j₂], _ => exact ⟨j₁, j₂, rfl⟩
  rw [buildTF]
  have hlbl : preLblOfEnvs envs hM i = (.decompose, (preLblOfEnvs envs hM i).2) := by
    rw [← hst]
  -- the node's children are the two subtrees
  have hkids : ((childIdxsF kroots (preFoOfEnvs envs hM) M i).attach.map
      (fun j => buildTF kroots (preFoOfEnvs envs hM) (preLblOfEnvs envs hM) M j.1)) =
      [buildTF kroots (preFoOfEnvs envs hM) (preLblOfEnvs envs hM) M j₁,
        buildTF kroots (preFoOfEnvs envs hM) (preLblOfEnvs envs hM) M j₂] := by
    rw [List.attach_map_val (f := fun j => buildTF kroots (preFoOfEnvs envs hM)
      (preLblOfEnvs envs hM) M j), hj]
    rfl
  rw [hkids, hlbl, decodePre_decompose_two]
  exact ⟨_, _, rfl⟩

/-- **The diagonal hypothesis fails at a decompose row**: for any target map sending `decompose` to
`atom 0` (both `requestTargets P.strategy.skeleton` and the built targets do,
`Batch961.requestTargets_decompose`), the route-B pair list has an off-diagonal pair. -/
theorem reqPairs_not_diag (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M) (T : MState → ℕ → Noun)
    (hT : ∀ k, T .decompose k = .atom 0)
    (i : ℕ) (hi1 : 1 ≤ i) (hiM : i ≤ M)
    (hst : (preLblOfEnvs envs hM i).1 = .decompose)
    (hch : (childIdxsF kroots (preFoOfEnvs envs hM) M i).length = 2) :
    ∃ p ∈ reqPairsOfEnvs K q kroots envs hM T, p.1 ≠ p.2 := by
  obtain ⟨l, r, hlr⟩ := preZNoun_decompose_cell K q kroots envs hM i hst hch
  refine ⟨(preZNounOfEnvs K q kroots envs hM i, reqTgtOfEnvs envs hM T i), ?_, ?_⟩
  · unfold reqPairsOfEnvs
    refine List.mem_map.mpr ⟨i, ?_, rfl⟩
    rw [List.mem_range'_1]
    omega
  · show preZNounOfEnvs K q kroots envs hM i ≠ reqTgtOfEnvs envs hM T i
    rw [hlr]
    unfold reqTgtOfEnvs
    rw [hst, hT]
    intro h
    cases h

/-- So `pairBadSeeds_eq_empty_of_diag`'s hypothesis is FALSE at such envs. -/
theorem not_diag_hyp (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M) (T : MState → ℕ → Noun)
    (hT : ∀ k, T .decompose k = .atom 0)
    (i : ℕ) (hi1 : 1 ≤ i) (hiM : i ≤ M)
    (hst : (preLblOfEnvs envs hM i).1 = .decompose)
    (hch : (childIdxsF kroots (preFoOfEnvs envs hM) M i).length = 2) :
    ¬ ∀ p ∈ reqPairsOfEnvs K q kroots envs hM T, p.1 = p.2 := by
  intro hdiag
  obtain ⟨p, hp, hne⟩ := reqPairs_not_diag K q kroots envs hM T hT i hi1 hiM hst hch
  exact hne (hdiag p hp)

theorem requestTargets_decompose_atom (S : SemanticStrategy.SemanticSkeleton) (k : ℕ) :
    requestTargets S .decompose k = .atom 0 := by
  cases k <;> rfl

end NotDiag

/-! ## §B  What an off-diagonal pair costs -/

section Cost

variable {K : Type} [Field K]

/-- **Different leaf counts: bad only at `0` or at a root of unity of the difference.** -/
theorem bad_of_leaves_ne (z : K) (a b : Noun) (hlt : a.leaves < b.leaves)
    (hbad : ¬ GlobalCarryRecognizer.SepSeed z a b) :
    z = 0 ∨ z ^ (b.leaves - a.leaves) = 1 := by
  unfold GlobalCarryRecognizer.SepSeed at hbad
  push Not at hbad
  obtain ⟨-, hfn⟩ := hbad
  have h1 : z ^ a.leaves = z ^ b.leaves := congrArg Prod.fst hfn
  by_cases hz : z = 0
  · exact Or.inl hz
  · right
    have hsplit : z ^ b.leaves = z ^ a.leaves * z ^ (b.leaves - a.leaves) := by
      rw [← pow_add]; congr 1; omega
    have hza : z ^ a.leaves ≠ 0 := pow_ne_zero _ hz
    rw [hsplit] at h1
    have : z ^ a.leaves * 1 = z ^ a.leaves * z ^ (b.leaves - a.leaves) := by rw [mul_one]; exact h1
    exact (mul_left_cancel₀ hza this).symm

/-- `atom 0` has one leaf; a cell has at least two. -/
theorem cell_leaves_ge_two (l r : Noun) : 2 ≤ (Noun.cell l r).leaves := by
  have hl := Noun.one_le_leaves l
  have hr := Noun.one_le_leaves r
  simp only [Noun.leaves]
  omega

/-- **A decompose pair `(cell, atom 0)` is bad only at `0` or a root of unity of order dividing
`leaves − 1`.** -/
theorem decompose_pair_bad_imp (z : K) (l r : Noun)
    (hbad : ¬ GlobalCarryRecognizer.SepSeed z (Noun.cell l r) (.atom 0)) :
    z = 0 ∨ z ^ ((Noun.cell l r).leaves - 1) = 1 := by
  have hsym : ¬ GlobalCarryRecognizer.SepSeed z (.atom 0) (Noun.cell l r) := by
    intro hs
    apply hbad
    intro hne hfn
    exact hs (fun h => hne h.symm) hfn.symm
  have h2 := cell_leaves_ge_two l r
  have ha : (Noun.atom 0).leaves = 1 := rfl
  have := bad_of_leaves_ne z (.atom 0) (Noun.cell l r) (by omega) hsym
  rwa [ha] at this

/-- **An atom against `atom 0` is never bad** (the halt rows). -/
theorem atom_pair_never_bad (z : K) (a : ℕ) :
    GlobalCarryRecognizer.SepSeed z (.atom a) (.atom 0) := by
  intro hne hfn
  apply hne
  have h2 : (NPR.listPoly (NPR.leafF (K := K) (.atom a))).eval z =
      (NPR.listPoly (NPR.leafF (K := K) (.atom 0))).eval z := congrArg (fun t => t.2.1) hfn
  simp [NPR.leafF, Noun.leafList, NPR.listPoly_cons] at h2
  have hd : (Noun.atom a).dyckWord = (Noun.atom 0).dyckWord := rfl
  simp [NPR.leafF, Noun.leafList, NPR.dyckBits, h2, hd]

end Cost


/-- `hF`'s orbit order exports `3·M ≤ p − 1` whenever `M ≤ 2^h`. -/
theorem threeM_le_of_hF {p h M : ℕ} (hp : 2 ≤ p) (hF : 3 * 2 ^ h ∣ p - 1) (hM : M ≤ 2 ^ h) :
    3 * M ≤ p - 1 := by
  have hle : 3 * 2 ^ h ≤ p - 1 := Nat.le_of_dvd (by omega) hF
  omega

/-- The route-(b) budget: the live joint budget plus one pair term `M·(2(M ⊔ Λ) − 1)`. -/
def seedBudgetPairB (Λ rows M : ℕ) : ℕ :=
  TraceGen.GoodSeed.seedBudgetVcomp Λ rows + M * (2 * (M ⊔ Λ) - 1)

/-- The cubic gap, exactly (`6·p³ > 163p² − 367p + 192` from `p = 25`). -/
theorem cubic_gap_pairB {p : ℕ} (hp : 25 ≤ p) :
    6 * (1 + (3 + 13 * (p - 1)) * (2 * (p - 1) - 1)) + 3 * ((p - 1) * p) +
      2 * ((p - 1) * (2 * (p - 1) - 1)) < 6 * p ^ 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 25 := ⟨p - 25, by omega⟩
  have e1 : n + 25 - 1 = n + 24 := by omega
  have e2 : 2 * (n + 24) - 1 = 2 * n + 47 := by omega
  rw [e1, e2]
  ring_nf
  nlinarith [sq_nonneg n, Nat.zero_le n, Nat.zero_le (n ^ 3)]

/-- **Route (b) keeps `hp : 25 ≤ p`**: with `rows, Λ < p` and `3M ≤ p − 1` (from `hF`), the
budget with one pair term is below `p³` at every `p ≥ 25`. -/
theorem seedBudgetPairB_lt_pow {Λ rows M p : ℕ} (hrows : rows < p) (hΛp : Λ < p)
    (hM : 3 * M ≤ p - 1) (hp : 25 ≤ p) :
    seedBudgetPairB Λ rows M < p ^ 3 := by
  have hr : rows ≤ p - 1 := by omega
  have hL : Λ ≤ p - 1 := by omega
  have hMp : M ≤ p - 1 := by omega
  have hmx : 2 * (M ⊔ Λ) - 1 ≤ 2 * (p - 1) - 1 := by
    have : M ⊔ Λ ≤ p - 1 := sup_le hMp hL
    omega
  have hsw : sizeWindowRootBound Λ * 2 = Λ * (Λ + 1) := TraceGen.sizeWindowRootBound_mul_two Λ
  have hsw' : Λ * (Λ + 1) ≤ (p - 1) * p := by
    have : Λ + 1 ≤ p := by omega
    exact Nat.mul_le_mul hL this
  have hb1 : (3 + 13 * rows) * (2 * Λ - 1) ≤ (3 + 13 * (p - 1)) * (2 * (p - 1) - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hb2 : 3 * (M * (2 * (M ⊔ Λ) - 1)) ≤ (p - 1) * (2 * (p - 1) - 1) := by
    calc 3 * (M * (2 * (M ⊔ Λ) - 1)) = (3 * M) * (2 * (M ⊔ Λ) - 1) := by ring
      _ ≤ (p - 1) * (2 * (p - 1) - 1) := Nat.mul_le_mul hM hmx
  have hgap := cubic_gap_pairB hp
  have hexp : seedBudgetPairB Λ rows M =
      1 + (3 + 13 * rows) * (2 * Λ - 1) + sizeWindowRootBound Λ + M * (2 * (M ⊔ Λ) - 1) := by
    unfold seedBudgetPairB TraceGen.GoodSeed.seedBudgetVcomp TraceGen.GoodSeed.seedBudget
    ring
  rw [hexp]
  nlinarith

/-- Negative control 1: without `hF`'s export (`M = p − 1`) the one-pair budget fails at `25`. -/
theorem seedBudgetPair_noHF_fails_25 : ¬ seedBudgetPairB 24 24 24 < 25 ^ 3 := by
  simp only [seedBudgetPairB, TraceGen.GoodSeed.seedBudgetVcomp, TraceGen.GoodSeed.seedBudget,
    sizeWindowRootBound]
  decide

theorem seedBudgetTwoPair_fails_25 :
    ¬ seedBudgetPairB 24 24 8 + 8 * (2 * (8 ⊔ 24) - 1) < 25 ^ 3 := by
  simp only [seedBudgetPairB, TraceGen.GoodSeed.seedBudgetVcomp, TraceGen.GoodSeed.seedBudget,
    sizeWindowRootBound]
  decide

/-- Positive corner: the one-pair budget at the `p = 25` worst case (`rows = Λ = 24`, `M = 8`). -/
theorem seedBudgetPairB_corner_25 : seedBudgetPairB 24 24 8 < 25 ^ 3 := by
  simp only [seedBudgetPairB, TraceGen.GoodSeed.seedBudgetVcomp, TraceGen.GoodSeed.seedBudget,
    sizeWindowRootBound]
  decide

end Nock.RedTeam.Batch1251

#print axioms Nock.RedTeam.Batch1251.preZNoun_decompose_cell
#print axioms Nock.RedTeam.Batch1251.reqPairs_not_diag
#print axioms Nock.RedTeam.Batch1251.not_diag_hyp
#print axioms Nock.RedTeam.Batch1251.bad_of_leaves_ne
#print axioms Nock.RedTeam.Batch1251.decompose_pair_bad_imp
#print axioms Nock.RedTeam.Batch1251.atom_pair_never_bad
#print axioms Nock.RedTeam.Batch1251.threeM_le_of_hF
#print axioms Nock.RedTeam.Batch1251.seedBudgetPairB_lt_pow
#print axioms Nock.RedTeam.Batch1251.seedBudgetPair_noHF_fails_25
#print axioms Nock.RedTeam.Batch1251.seedBudgetTwoPair_fails_25
#print axioms Nock.RedTeam.Batch1251.seedBudgetPairB_corner_25
