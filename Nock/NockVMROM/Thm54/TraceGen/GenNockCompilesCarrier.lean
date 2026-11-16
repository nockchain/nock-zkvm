/-
  Nock/NockVMROM/Thm54/TraceGen/GenNockCompilesCarrier.lean

Group 1 (`p68`): field inhabitants `bas` / `packageOrbit` / `orbit` plus
  `horb` / `hcap` / `hcard` become `hK` / `hF` / `hOrbPos`; the compiler
  constructs the orbits and the cubic basis; `hcard` is
  `28 N² + 4 N < |K| = |F|³` at `N ≤ 2 ^ hOrb`.

  Group 2 (`p69`): least `h = orbitHeight (programFit …)` with both row
  counts and the `+ 1` capacities `≤ 2^h`.  Remain `compilerKsz < char`,
  `programAcc + 3 < orderOf α`, disclosed `seedBudgetVcomp`, and `hF` at
  the chosen height.

  Group 3 (`p70`): `evalN` plus named `RunBoundedBy` (not a growth theorem).
  `htwo` derived from `11 < q = ringChar K`.

  Group 4 (`p71`): the compiler instantiates the guard modulus at
  `ringChar K`.  `hchar`
  leaves; `hq : 11 < q` becomes `hp : 11 < ringChar K` (eleven state
  tags, `NodeEncoding.stateTagChar_of_ringChar_gt_eleven`;
  the paper, `:1893`).

  Group 5 (`p72`): `hs` / `hf` stay (paper typing `:348`, `:1093`).

  Group 6 (`p73`): `hseedcard` → `Λ < p` and `29 ≤ p`.

  Group 7: same binders as `p73`
  (28/12).  `hp : 29 ≤ ringChar K` is the W9 cubic-majorant floor.

  Group 8 (`p75`): compiler picks `Λ := programLeafBound` (`le_rfl`).
  `{Λ}` and `hΛ` leave; `hΛp` is the leaf-count window versus `p`.
  Witness `P.optimized.Λ` is that leaf bound (proof fact, not
  statement).  28/12 → 26/11.

  Group 9 (`p76`): measured floor `p₀ = 25`.  The implication
  `rows < p ∧ Λ < p → seedBudgetVcomp < p³` is **false at 24** and
  **true from 25**; W9's `29` was a loose-majorant artefact, not tight.

  Group 10 (`nockCompiles_zmod`): §1's `ZMod p` spelling, beside the
  general-`F` theorem.  `ringChar K = p` is derived, not assumed
  (literal `p` in every explicit hypothesis).

  No growth theorem, no new program binder. `claim = ⟨subject, formula, result⟩`
  stays. Window spelled as §1's `programLeafBound` (F-2). Counts use
  `programMemShape` (F-8).

  -- the paper
-/
import Nock.NockVMROM.Thm54.CoordinateBasis
import Nock.NockVMROM.Thm54.ExtensionField
import Nock.NockVMROM.Thm54.GoldilocksOrbit
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenRequestAxisBound
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.FieldTheory.Finite.Basic

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GoldilocksOrbit
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.Framework.Thm54

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-! ## Field-arithmetic constructors

Generalisation of `GoldilocksOrbit.goldilocksStrictOrbit` /
`goldilocksExecutionOrbit`: any finite field whose unit-group order is
divisible by `3 · 2^h` hosts a strict RAP generator of that order
, and cubing-then-injecting yields an execution generator
of order `2^h` in the degree-3 extension. -/

/-- A divisor of `|F|ˣ` occurs as an exact multiplicative order. -/
theorem exists_order_of_dvd_card_sub_one (m : ℕ)
    (hm : m ∣ Fintype.card F - 1) :
    ∃ ω : F, orderOf ω = m := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  rw [hcard] at hg
  have hne : orderOf g ≠ 0 := by
    rw [hg]
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hdvd : m ∣ orderOf g := by
    rw [hg]
    exact hm
  let ζ : F := ((g ^ (orderOf g / m) : Fˣ) : F)
  have hζ : orderOf ζ = m := by
    change orderOf (((g ^ (orderOf g / m) : Fˣ) : F)) = m
    rw [orderOf_units]
    exact orderOf_pow_orderOf_div hne hdvd
  exact ⟨ζ, hζ⟩

/-- Chosen base-field generator of exact order `3 · 2^h`. -- the paper -/
def compilerStrictGenerator (hOrb : ℕ)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1) : F :=
  Classical.choose (exists_order_of_dvd_card_sub_one (3 * 2 ^ hOrb) hF)

theorem compilerStrictGenerator_order (hOrb : ℕ)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1) :
    orderOf (compilerStrictGenerator (F := F) hOrb hF) = 3 * 2 ^ hOrb :=
  Classical.choose_spec (exists_order_of_dvd_card_sub_one (3 * 2 ^ hOrb) hF)

/-- Compiler RAP orbit (`Def:RAP` the paper). -/
def compilerPackageOrbit (hOrb : ℕ) (hpos : 1 ≤ hOrb)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1) :
    StrictOrbitDomain F 3 hOrb where
  ω := compilerStrictGenerator (F := F) hOrb hF
  βcoset := 1
  e_pos := by norm_num
  h_pos := hpos
  order_ω := compilerStrictGenerator_order (F := F) hOrb hF
  βcoset_ne_zero := one_ne_zero

/-- Execution generator in `K`: cube in `F`, inject. -- the paper -/
def compilerExecutionGenerator (hOrb : ℕ)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1) : K :=
  algebraMap F K (compilerStrictGenerator (F := F) hOrb hF ^ 3)

theorem compilerExecutionGenerator_order (hOrb : ℕ)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1) :
    orderOf (compilerExecutionGenerator (F := F) (K := K) hOrb hF) = 2 ^ hOrb := by
  change orderOf
    ((algebraMap F K).toMonoidHom (compilerStrictGenerator (F := F) hOrb hF ^ 3))
    = 2 ^ hOrb
  exact
    (orderOf_injective (algebraMap F K).toMonoidHom
      (RingHom.injective (algebraMap F K))
      (compilerStrictGenerator (F := F) hOrb hF ^ 3)).trans
      (orderOf_cube_of_order_three_mul_two_pow
        (compilerStrictGenerator (F := F) hOrb hF)
        (compilerStrictGenerator_order (F := F) hOrb hF))

/-- Compiler execution orbit of exact order `2^hOrb`. -/
def compilerExecutionOrbit (hOrb : ℕ) (_hpos : 1 ≤ hOrb)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1) : OrbitDomain K where
  h := hOrb
  ω := compilerExecutionGenerator (F := F) (K := K) hOrb hF
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := compilerExecutionGenerator_order (F := F) (K := K) hOrb hF

theorem compilerExecutionOrbit_h (hOrb : ℕ) (hpos : 1 ≤ hOrb)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1) :
    (compilerExecutionOrbit (F := F) (K := K) hOrb hpos hF).h = hOrb :=
  rfl

/-- `{1}` as a `Unit`-family is linearly independent. -- the paper -/
theorem one_unit_linearIndependent :
    LinearIndependent F (fun _ : Unit => (1 : K)) :=
  (linearIndependent_unique_iff (R := F) (v := fun _ : Unit => (1 : K))).mpr
    (one_ne_zero : (1 : K) ≠ 0)

/-- Cubic basis extending `{1}` via `sumExtend`, then reindexed so
    `inl  ↦ 0`. -- the paper -/
noncomputable def compilerBasisSum (_hK : Module.finrank F K = 3) :
    Module.Basis
      (Unit ⊕ Module.Basis.sumExtendIndex (one_unit_linearIndependent (F := F) (K := K)))
      F K :=
  Module.Basis.sumExtend (one_unit_linearIndependent (F := F) (K := K))

/-- Equivalence sending `inl ` to `0`. `hK` pins the card at 3. -/
noncomputable def compilerBasisEquiv (hK : Module.finrank F K = 3) :
    (Unit ⊕ Module.Basis.sumExtendIndex (one_unit_linearIndependent (F := F) (K := K))) ≃
      Fin 3 :=
  let b0 := compilerBasisSum (F := F) (K := K) hK
  let _ := FiniteDimensional.fintypeBasisIndex (K := F) (V := K) b0
  have hcard :
      Fintype.card
        (Unit ⊕ Module.Basis.sumExtendIndex (one_unit_linearIndependent (F := F) (K := K))) =
        3 := by
    rw [← Module.finrank_eq_card_basis b0, hK]
  let eFin := Fintype.equivFinOfCardEq hcard
  eFin.trans (Equiv.swap (eFin (Sum.inl ())) (0 : Fin 3))

/-- Cubic coordinate basis from `finrank = 3` that **extends `{1}`**:
    `b 0 = 1`, so `coord b 1 = (1,0,0)`. -- the paper -/
noncomputable def compilerBasis (hK : Module.finrank F K = 3) :
    Module.Basis (Fin 3) F K :=
  (compilerBasisSum (F := F) (K := K) hK).reindex (compilerBasisEquiv (F := F) (K := K) hK)

theorem compilerBasisEquiv_symm_zero (hK : Module.finrank F K = 3) :
    (compilerBasisEquiv (F := F) (K := K) hK).symm 0 = Sum.inl () := by
  unfold compilerBasisEquiv
  simp [Equiv.swap_apply_right]

theorem compilerBasisSum_inl (hK : Module.finrank F K = 3) :
    compilerBasisSum (F := F) (K := K) hK (Sum.inl ()) = 1 := by
  unfold compilerBasisSum Module.Basis.sumExtend
  simp only [Module.Basis.reindex_apply, Equiv.symm_symm]
  rw [Module.Basis.extend_apply_self]
  erw [Equiv.symm_symm]
  erw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
  erw [Equiv.Set.sumDiffSubset_apply_inl]
  rfl

theorem compilerBasis_zero (hK : Module.finrank F K = 3) :
    compilerBasis (F := F) (K := K) hK 0 = 1 := by
  rw [compilerBasis, Module.Basis.reindex_apply, compilerBasisEquiv_symm_zero,
    compilerBasisSum_inl]

/-- `FormRBasis` of the compiler basis. Named SAT hyp retired. -- the paper -/
theorem compilerBasis_formR (hK : Module.finrank F K = 3) :
    OptimizedComputeFinalTrace.FormRBasis (compilerBasis (F := F) (K := K) hK) := by
  have h0 := compilerBasis_zero (F := F) (K := K) hK
  have hrepr : (compilerBasis (F := F) (K := K) hK).repr 1 = Finsupp.single 0 1 := by
    rw [← h0, Module.Basis.repr_self]
  refine ⟨?_, ?_, ?_⟩
  · change (compilerBasis (F := F) (K := K) hK).repr 1 0 = 1
    rw [hrepr]; simp
  · change (compilerBasis (F := F) (K := K) hK).repr 1 (1 : Fin 3) = 0
    rw [hrepr]; simp
  · change (compilerBasis (F := F) (K := K) hK).repr 1 (2 : Fin 3) = 0
    rw [hrepr]; simp

/-! ## Converses (no silent strengthening) -/

theorem finrank_of_basis (bas : Module.Basis (Fin 3) F K) :
    Module.finrank F K = 3 := by
  rw [Module.finrank_eq_card_basis bas]
  exact Fintype.card_fin 3

theorem card_units_eq_card_sub_one : Fintype.card Fˣ = Fintype.card F - 1 :=
  Fintype.card_units (α := F)

theorem strictOrbit_ne_zero {hOrb : ℕ} (o : StrictOrbitDomain F 3 hOrb) :
    o.ω ≠ 0 := by
  intro h
  have hpow := pow_orderOf_eq_one o.ω
  have hpos : 3 * 2 ^ hOrb ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  rw [o.order_ω, h, zero_pow hpos] at hpow
  exact one_ne_zero hpow.symm

/-- `packageOrbit` implies `hF`. -- the paper -/
theorem dvd_card_sub_one_of_strictOrbit {hOrb : ℕ}
    (o : StrictOrbitDomain F 3 hOrb) :
    3 * 2 ^ hOrb ∣ Fintype.card F - 1 := by
  have hω := strictOrbit_ne_zero o
  let u : Fˣ := Units.mk0 o.ω hω
  have hu : orderOf u = 3 * 2 ^ hOrb := by
    rw [← orderOf_units]
    simpa [u] using o.order_ω
  have hdvd : orderOf u ∣ Fintype.card Fˣ := orderOf_dvd_card
  rw [hu, card_units_eq_card_sub_one] at hdvd
  exact hdvd

/-! ## `hcard` from field + capacity

`hcard` is
`28 N² + 4 N < |K|` (`GoldilocksParameters.hcard_iff`). Under `hK`
one has `|K| = |F|³`. Under `hF` one has `|F| ≥ 3 · 2^h + 1`. The
row-count family remaining on `p68` gives `N = compilerNOf ≤ 2^h`. Then `28 N² + 4 N ≤ 28 k² + 4 k < (3k+1)³ ≤ |F|³` at `k = 2^h ≥ 2`
(`h ≥ 1`). -/

theorem card_K_of_finrank3 (hK : Module.finrank F K = 3) :
    Fintype.card K = Fintype.card F ^ 3 := by
  rw [Module.card_eq_pow_finrank (K := F) (V := K), hK]

theorem card_F_ge_of_hF {hOrb : ℕ}
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1) :
    3 * 2 ^ hOrb + 1 ≤ Fintype.card F := by
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hpos : 0 < Fintype.card F - 1 := Nat.sub_pos_of_lt h1
  have hle : 3 * 2 ^ hOrb ≤ Fintype.card F - 1 := Nat.le_of_dvd hpos hF
  have hcard : 1 ≤ Fintype.card F := le_of_lt h1
  omega

theorem hcard_cubic_arith_nine (k : ℕ) (hk : 1 ≤ k) :
    32 * k * k + 4 * k < (3 * k + 1) ^ 3 := by
  have hexp : (3 * k + 1) ^ 3 = 27 * k ^ 3 + 27 * k ^ 2 + 9 * k + 1 := by ring
  have hlin : 32 * k * k + 4 * k = 32 * k ^ 2 + 4 * k := by ring
  rw [hlin, hexp]
  have hcu : k ^ 2 ≤ k ^ 3 := by
    have : k ^ 2 * 1 ≤ k ^ 2 * k := Nat.mul_le_mul_left (k ^ 2) hk
    simpa [pow_succ] using this
  nlinarith

/-- **The 31st, honest budget** (`RecordCarrier.honestIOBound`, nine- and ten-slot events):
`68k² + 8k < (3k + 1)³` once `k ≥ 2` (`k = 2^hOrb`, `hOrb ≥ 1`). -/
theorem hcard_cubic_arith_honest (k : ℕ) (hk : 2 ≤ k) :
    68 * k * k + 8 * k < (3 * k + 1) ^ 3 := by
  have hexp : (3 * k + 1) ^ 3 = 27 * k ^ 3 + 27 * k ^ 2 + 9 * k + 1 := by ring
  have hlin : 68 * k * k + 8 * k = 68 * k ^ 2 + 8 * k := by ring
  rw [hlin, hexp]
  have hcu : 2 * k ^ 2 ≤ k ^ 3 := by
    have : k ^ 2 * 2 ≤ k ^ 2 * k := Nat.mul_le_mul_left (k ^ 2) hk
    nlinarith [this]
  nlinarith

theorem hcard_cubic_arith (k : ℕ) (hk : 1 ≤ k) :
    28 * k * k + 4 * k < (3 * k + 1) ^ 3 := by
  have hexp : (3 * k + 1) ^ 3 = 27 * k ^ 3 + 27 * k ^ 2 + 9 * k + 1 := by
    ring
  have hlin : 28 * k * k + 4 * k = 28 * k ^ 2 + 4 * k := by ring
  rw [hlin, hexp]
  have hcu : k ^ 2 ≤ k ^ 3 := by
    have : k ^ 2 * 1 ≤ k ^ 2 * k := Nat.mul_le_mul_left (k ^ 2) hk
    simpa [pow_succ] using this
  apply Nat.lt_of_succ_le
  rw [Nat.succ_eq_add_one]
  have hL : 28 * k ^ 2 + 4 * k + 1 = (k ^ 2 + 4 * k) + 27 * k ^ 2 + 1 := by ring
  have hR : 27 * k ^ 3 + 27 * k ^ 2 + 9 * k + 1 =
      (27 * k ^ 3 + 9 * k) + 27 * k ^ 2 + 1 := by ring
  rw [hL, hR]
  refine Nat.add_le_add_right (Nat.add_le_add_right ?_ _) _
  have hmid : k ^ 2 + 4 * k ≤ k ^ 3 + 4 * k := Nat.add_le_add_right hcu _
  refine le_trans hmid (Nat.add_le_add ?_ ?_)
  · exact Nat.le_mul_of_pos_left (k ^ 3) (by norm_num : 0 < 27)
  · exact Nat.mul_le_mul_right k (by norm_num : 4 ≤ 9)

theorem compilerNOf_le_two_pow {α : K} {t : NTree (GenComputeRow K)} {h : ℕ}
    (hmem : programMemShape α t ≤ 2 ^ h)
    (hprogCap : programAcc t + 1 ≤ 2 ^ h) :
    compilerNOf (0 : K) α t ≤ 2 ^ h := by
  change max (programAcc t) (programMemRows (0 : K) α t) ≤ 2 ^ h
  refine max_le (Nat.le_of_succ_le hprogCap) ?_
  simpa [programMemShape] using hmem

theorem hcard_of_hF_hK {hOrb : ℕ} (hpos : 1 ≤ hOrb)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1)
    (n : ℕ) (hn : n ≤ 2 ^ hOrb) :
    RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K) := by
  have hKpos : 0 < Fintype.card K := Fintype.card_pos
  rw [Fintype.card_prod, RecordCarrier.honestIOBound_eq]
  have hk : 2 ≤ 2 ^ hOrb := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ hOrb := Nat.pow_le_pow_right (by norm_num) hpos
  have hquad : 68 * n * n + 8 * n ≤ 68 * (2 ^ hOrb) * (2 ^ hOrb) + 8 * (2 ^ hOrb) := by
    have hn2 : n * n ≤ 2 ^ hOrb * 2 ^ hOrb := Nat.mul_le_mul hn hn
    nlinarith
  have harith := hcard_cubic_arith_honest (2 ^ hOrb) hk
  have hFge := card_F_ge_of_hF (F := F) hF
  have hpow : (3 * 2 ^ hOrb + 1) ^ 3 ≤ Fintype.card F ^ 3 :=
    Nat.pow_le_pow_left hFge 3
  have hinner : 68 * n * n + 8 * n < Fintype.card F ^ 3 :=
    lt_of_le_of_lt hquad (lt_of_lt_of_le harith hpow)
  have hltK : 68 * n * n + 8 * n < Fintype.card K := by
    rw [card_K_of_finrank3 (F := F) hK]
    exact hinner
  exact (Nat.mul_lt_mul_left hKpos).mpr hltK

/-! ## `nockCompiles_p68` — group 1

`p67` minus the three inhabitants and `horb`/`hcap`/`hcard`, plus `hK`/`hF`/
`hOrbPos`.  Window is §1's `programLeafBound` (F-2).  Memory counts are
`programMemShape` (F-8). -- the paper -/

namespace GoodSeed

theorem nockCompiles_p68 {q Λ : ℕ} {hOrb : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) ≤ Λ)
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hOrbPos : 1 ≤ hOrb)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1)
    (hcomp : (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length
      ≤ 2 ^ hOrb)
    (hmem : programMemShape α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ 2 ^ hOrb)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ hOrb)
    (hmemCap : programMemShape α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ hOrb)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  -- 28th λ-fix: `λ` is sampled, like `α`, and is a binder beside it; the compiler chooses none.
  -- `hwidth` is `FormRWidth_of_hp64`, and `hax` is discharged on the generated compute rows
  -- (`GenFormRAxisLambda.genComputeRows_rowsFormRAxisBound`): neither is a premise.
  nockCompiles_p67 (hrows := hrows) (hF := hFprime) (F := F) (K := K) (q := q) (Λ := Λ)
    α αW lmb htwo hgrom hs hf (traceConfined_of_leafBound hΛ) hseedcard hq hchar
    (compilerExecutionOrbit (F := F) (K := K) hOrb hOrbPos hF)
    (by
      change 1 ≤ hOrb
      exact hOrbPos)
    hcomp hmem hwin hmemOrd
    (by rw [← compilerKszOf_eq_L]; exact hKszChar) hprogCap hmemCap
    (compilerBasis (F := F) (K := K) hK)
    (compilerPackageOrbit (F := F) hOrb hOrbPos hF)
    (by
      change 2 ^ hOrb ≤ 2 ^ hOrb
      exact le_rfl)
    (hcard_of_hF_hK (F := F) (K := K) hOrbPos hK hF
      (compilerNOfL lmb (0 : K) α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (by
        rw [← compilerNOf_eq_L]
        exact compilerNOf_le_two_pow (α := α)
          (t := romTree (K := K) (evalGRom_le_evalRom hgrom)) hmem hprogCap))
    -- ROOTZERO (Form R, row-level memory): `hfirst` is the guarded run's request-axis bound
    -- `a < p` (`romTree_assigned_request_axes_lt`), and `hmore` — every forest root has
    -- `pt = (0, 0)` — is the honest read cancellation at every sampled `λ`
    -- (`genBuildableOfProgram_laterSeedZeros`).  Both former residual binders are discharged.
    (by
      intro _ _ _ n hn r hr
      rw [← hchar]
      exact romTree_assigned_request_axes_lt (q := q) (by omega) hgrom hs hf n hn r hr)
    (fun _ _ _ _ => genBuildableOfProgram_laterSeedZeros)
    -- `FormRBasis` of the compiler basis (`compilerBasis_formR`, the basis extends `{1}`):
    -- discharged with no new hypothesis.
    (compilerBasis_formR (F := F) (K := K) hK)
    (GenFormRAxisLambda.FormRWidth_of_hp64
      (by rw [Algebra.ringChar_eq F K, ← hchar]; omega) hp64)
    (fun a b c _ =>
      GenFormRAxisLambda.genComputeRows_rowsFormRAxisBound (q := q) (by omega) hs hf
        (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
        (hchar.trans (Algebra.ringChar_eq F K).symm)
        (by rw [hchar, ← Algebra.ringChar_eq F K]; exact hp64)
        (compilerBasis_formR (F := F) (K := K) hK) _ α a b c)

/-- Predecessor from successor: every `p67` hypothesis still yields the
`p67` conclusion, via `p68`.  No silent strengthening. -/
noncomputable def nockCompiles_p67_of_p68 {q Λ : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (hcomp : (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length
      ≤ 2 ^ orbit.h)
    (hmem : programMemShape α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ 2 ^ orbit.h)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    (hmemCap : programMemShape α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ orbit.h)
    {hOrb : ℕ}
    (bas : Module.Basis (Fin 3) F K)
    (packageOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ orbit.h ≤ 2 ^ hOrb)
    (hcard : RecordCarrier.honestIOBound
      (compilerNOf (0 : K) α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOf (0 : K) α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K))
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K) :=
  nockCompiles_p68 (hrows := hrows) (F := F) (K := K) α αW lmb htwo hgrom hs hf
    (leafBound_of_traceConfined hΛ) hseedcard
    hq hchar hp64 packageOrbit.h_pos (finrank_of_basis bas)
    (dvd_card_sub_one_of_strictOrbit packageOrbit)
    (le_trans hcomp hcap) (le_trans hmem hcap) hwin hmemOrd
    hKszChar (le_trans hprogCap hcap) (le_trans hmemCap hcap)

end GoodSeed

/-! ## Group 2 — compiler orbit height

The least `h ≥ 1` with both row counts and the two `+ 1` capacities
`≤ 2^h`.  `hmemCap` / `hprogCap` are *not* consequences of
`rows ≤ 2^h` alone (`mem = 2^h` or `acc = 3 · comp` can overshoot),
so the height is taken at `programFit`, not at the raw row pair.
`hcomp` / `hmem` / `hprogCap` / `hmemCap` / `hcap` then drop out.
-- -/

/-- AIR-ordered compute-row count. -/
abbrev programCompRows (t : NTree (GenComputeRow K)) : ℕ :=
  (bfsRows (airReorder t)).length

/-- Least capacity the RAP column length `2^h` must cover. -/
abbrev programFit (α : K) (t : NTree (GenComputeRow K)) : ℕ :=
  max (max (programCompRows t) (programMemShape α t + 1)) (programAcc t + 1)

/-- Least `h ≥ 1` with `n ≤ 2^h`.  `Nat.clog 2` is `0` at `n ≤ 1`. -- the paper -/
def orbitHeight (n : ℕ) : ℕ := max 1 (Nat.clog 2 n)

theorem orbitHeight_pos (n : ℕ) : 1 ≤ orbitHeight n :=
  le_max_left _ _

theorem le_two_pow_orbitHeight (n : ℕ) : n ≤ 2 ^ orbitHeight n := by
  refine le_trans (Nat.le_pow_clog (by norm_num : 1 < 2) n) ?_
  exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (le_max_right _ _)

theorem orbitHeight_le_of_le {n h : ℕ} (hpos : 1 ≤ h) (hn : n ≤ 2 ^ h) :
    orbitHeight n ≤ h := by
  unfold orbitHeight
  exact max_le hpos ((Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2 hn)

theorem programFit_le_of_caps {α : K} {t : NTree (GenComputeRow K)} {h : ℕ}
    (hcomp : programCompRows t ≤ 2 ^ h)
    (hmemCap : programMemShape α t + 1 ≤ 2 ^ h)
    (hprogCap : programAcc t + 1 ≤ 2 ^ h) :
    programFit α t ≤ 2 ^ h :=
  max_le (max_le hcomp hmemCap) hprogCap

theorem programCompRows_le_fit (α : K) (t : NTree (GenComputeRow K)) :
    programCompRows t ≤ programFit α t :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem programMemShape_succ_le_fit (α : K) (t : NTree (GenComputeRow K)) :
    programMemShape α t + 1 ≤ programFit α t :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem programAcc_succ_le_fit (α : K) (t : NTree (GenComputeRow K)) :
    programAcc t + 1 ≤ programFit α t :=
  le_max_right _ _

theorem programMemShape_le_fit (α : K) (t : NTree (GenComputeRow K)) :
    programMemShape α t ≤ programFit α t :=
  Nat.le_of_succ_le (programMemShape_succ_le_fit α t)

/-- `3 · 2^h ∣ 3 · 2^H` whenever `h ≤ H`. -- the paper -/
theorem three_mul_two_pow_dvd_of_le {h H : ℕ} (hle : h ≤ H) :
    3 * 2 ^ h ∣ 3 * 2 ^ H :=
  Nat.mul_dvd_mul_left _ (pow_dvd_pow (2 : ℕ) hle)

theorem dvd_card_sub_one_of_orbitHeight_le {h H : ℕ}
    (hle : h ≤ H) (hF : 3 * 2 ^ H ∣ Fintype.card F - 1) :
    3 * 2 ^ h ∣ Fintype.card F - 1 :=
  dvd_trans (three_mul_two_pow_dvd_of_le hle) hF

/-- `(2 : K) ≠ 0` from `11 < q = ringChar K`. -/
theorem two_ne_zero_of_hq {q : ℕ} (hq : 11 < q) (hchar : q = ringChar K) :
    (2 : K) ≠ 0 := by
  intro h
  have hdiv : ringChar K ∣ 2 :=
    (CharP.cast_eq_zero_iff K (ringChar K) 2).mp (by exact_mod_cast h)
  have : q ≤ 2 := by
    rw [hchar]
    exact Nat.le_of_dvd (by norm_num) hdiv
  omega

/-- `(2 : K) ≠ 0` from the compiler's `11 < ringChar K`. -- the paper -/
theorem two_ne_zero_of_hp (hp : 11 < ringChar K) : (2 : K) ≠ 0 :=
  two_ne_zero_of_hq (K := K) hp rfl

/-- `α ≠ 0` from any strict bound against `orderOf α` (`§1`'s `hα`
    is a corollary of `hwin`). -/
theorem alpha_ne_zero_of_lt_order {α : K} {n : ℕ} (h : n < orderOf α) : α ≠ 0 := by
  rintro rfl
  have h0 : orderOf (0 : K) = 0 := by
    rw [orderOf_eq_zero_iff']
    intro m hm
    rw [zero_pow (ne_of_gt hm)]
    exact zero_ne_one
  omega

/-! ## Seed-budget arithmetic (`p73`)

`sizeWindowRootBound Λ = ∑_{d=1}^Λ d` is degree-2 (`SizeWindowCounting.lean`). With `rows < p`, `Λ < p` and `29 ≤ p` the joint budget is `< p³ ≤ |K|`. -/

theorem accAt_ge_of_le_length (t : NTree (GenComputeRow K)) :
    ∀ n, n ≤ (bfsRows t).length → n ≤ accAt t n
  | 0, _ => by simp [accAt]
  | n + 1, hn => by
      have hnlt : n < (bfsRows t).length := Nat.lt_of_succ_le hn
      have ih := accAt_ge_of_le_length t n (Nat.le_of_lt hnlt)
      rw [accAt_succ_of_lt t n hnlt]
      have hrc : 1 ≤ Nock.Framework.recordCount (bfsRows t)[n].skel.state :=
        Nock.Framework.recordCount_pos _
      omega

theorem programAcc_ge_compRows (t : NTree (GenComputeRow K)) :
    (bfsRows (airReorder t)).length ≤ programAcc t :=
  accAt_ge_of_le_length (airReorder t) _ le_rfl

/-- `compilerKsz = max(acc, 2 · memRoots)` and every compute row emits at
    least one request (`recordCount_pos`), so
    `hKszChar` is §1's `rows < p`. -/
theorem compilerKszOf_ge_compRows (α : K) (t : NTree (GenComputeRow K)) :
    (bfsRows (airReorder t)).length ≤ compilerKszOf (0 : K) α t :=
  le_trans (programAcc_ge_compRows t) (compilerKsz_acc _ _)

theorem seedRows_lt_char_of_hKszChar (α : K) (t : NTree (GenComputeRow K))
    (h : compilerKszOf (0 : K) α t < ringChar K) :
    (bfsForest [bfsAssign (airReorder t)]).length < ringChar K := by
  rw [bfsForest_bfsAssign_length, ← bfsRows_length]
  exact lt_of_le_of_lt (compilerKszOf_ge_compRows α t) h

theorem cubic_gap_of_twenty_nine {p : ℕ} (hp : 29 ≤ p) :
    27 * p ^ 2 + 22 < p ^ 3 + 48 * p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n _hn ih =>
    have : 27 * (n + 1) ^ 2 + 22 < (n + 1) ^ 3 + 48 * (n + 1) := by
      nlinarith
    exact this

theorem seedBudgetVcomp_le_quad {Λ rows : ℕ} :
    GoodSeed.seedBudget Λ rows + 3 * rows * (2 * Λ - 1)
      ≤ 1 + (3 + 13 * rows) * (2 * Λ) + Λ * Λ := by
  have hsq : sizeWindowRootBound Λ ≤ Λ * Λ :=
    sizeWindowRootBound_le_square Λ
  have hsum :
      (3 + 10 * rows) * (2 * Λ - 1) + 3 * rows * (2 * Λ - 1)
        = (3 + 13 * rows) * (2 * Λ - 1) := by ring
  have hmul : (3 + 13 * rows) * (2 * Λ - 1) ≤ (3 + 13 * rows) * (2 * Λ) :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  unfold GoodSeed.seedBudget
  omega

theorem seedBudgetVcomp_quad_le_of_bounds {Λ rows p : ℕ}
    (hrows : rows < p) (hΛp : Λ < p) (_hp : 0 < p) :
    1 + (3 + 13 * rows) * (2 * Λ) + Λ * Λ
      ≤ 1 + (3 + 13 * (p - 1)) * (2 * (p - 1)) + (p - 1) * (p - 1) := by
  have hr : rows ≤ p - 1 := Nat.le_sub_one_of_lt hrows
  have hL : Λ ≤ p - 1 := Nat.le_sub_one_of_lt hΛp
  have hr13 : 3 + 13 * rows ≤ 3 + 13 * (p - 1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left 13 hr) _
  have h2L : 2 * Λ ≤ 2 * (p - 1) := Nat.mul_le_mul_left 2 hL
  have hLL : Λ * Λ ≤ (p - 1) * (p - 1) := Nat.mul_le_mul hL hL
  exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul hr13 h2L) _) hLL

theorem seed_quad_add_eq {p : ℕ} (hp : 0 < p) :
    1 + (3 + 13 * (p - 1)) * (2 * (p - 1)) + (p - 1) * (p - 1) + 48 * p
      = 27 * p ^ 2 + 22 := by
  cases p with
  | zero => exact (Nat.lt_irrefl _ hp).elim
  | succ n =>
    simp only [Nat.add_sub_cancel]
    ring

theorem seedBudgetVcomp_lt_pow_of_bounds {Λ rows p : ℕ}
    (hrows : rows < p) (hΛp : Λ < p) (hp : 29 ≤ p) :
    GoodSeed.seedBudget Λ rows + 3 * rows * (2 * Λ - 1) < p ^ 3 := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by norm_num : 0 < 29) hp
  have h1 := seedBudgetVcomp_le_quad (Λ := Λ) (rows := rows)
  have h2 := seedBudgetVcomp_quad_le_of_bounds hrows hΛp hp0
  have h3 := seed_quad_add_eq hp0
  have hgap := cubic_gap_of_twenty_nine hp
  have hle :
      GoodSeed.seedBudget Λ rows + 3 * rows * (2 * Λ - 1) + 48 * p
        ≤ 27 * p ^ 2 + 22 := by
    have := le_trans h1 h2
    omega
  have :
      GoodSeed.seedBudget Λ rows + 3 * rows * (2 * Λ - 1) + 48 * p
        < p ^ 3 + 48 * p :=
    lt_of_le_of_lt hle hgap
  exact Nat.add_lt_add_iff_right.mp this

theorem ringChar_eq_of_algebra_field : ringChar F = ringChar K :=
  Algebra.ringChar_eq F K

theorem card_F_ge_ringChar : ringChar F ≤ Fintype.card F := by
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (ringChar F) (K := F)
  have hpos : 0 < ringChar F := Nat.Prime.pos hp
  have hpow : ringChar F ^ 1 ≤ ringChar F ^ (n : ℕ) :=
    Nat.pow_le_pow_right hpos (Nat.succ_le_of_lt n.pos)
  rw [hcard]
  simpa using hpow

theorem card_K_ge_char_cubed (hK : Module.finrank F K = 3) :
    ringChar K ^ 3 ≤ Fintype.card K := by
  rw [card_K_of_finrank3 (F := F) hK, ← ringChar_eq_of_algebra_field (F := F) (K := K)]
  exact Nat.pow_le_pow_left card_F_ge_ringChar 3

/-- Disclosed seed budget from §1-shaped bounds. Floor `29 ≤ p` is
    `cubic_gap_of_twenty_nine`. -/
theorem seedBudget_lt_card_of_bounds {Λ rows : ℕ}
    (hK : Module.finrank F K = 3)
    (hrows : rows < ringChar K)
    (hΛp : Λ < ringChar K)
    (hp : 29 ≤ ringChar K) :
    GoodSeed.seedBudget Λ rows + 3 * rows * (2 * Λ - 1) < Fintype.card K :=
  lt_of_lt_of_le
    (seedBudgetVcomp_lt_pow_of_bounds hrows hΛp hp)
    (card_K_ge_char_cubed (F := F) hK)

/-- Tighter quad: keep the `2Λ − 1` factor (the W9 majorant used `2Λ`). -/
theorem seedBudgetVcomp_le_exact_quad {Λ rows : ℕ} :
    GoodSeed.seedBudget Λ rows + 3 * rows * (2 * Λ - 1)
      ≤ 1 + (3 + 13 * rows) * (2 * Λ - 1) + Λ * Λ := by
  have hsq : sizeWindowRootBound Λ ≤ Λ * Λ :=
    sizeWindowRootBound_le_square Λ
  have hsum :
      (3 + 10 * rows) * (2 * Λ - 1) + 3 * rows * (2 * Λ - 1)
        = (3 + 13 * rows) * (2 * Λ - 1) := by ring
  unfold GoodSeed.seedBudget
  omega

theorem seedBudgetVcomp_exact_quad_le_of_bounds {Λ rows p : ℕ}
    (hrows : rows < p) (hΛp : Λ < p) (_hp : 0 < p) :
    1 + (3 + 13 * rows) * (2 * Λ - 1) + Λ * Λ
      ≤ 1 + (3 + 13 * (p - 1)) * (2 * (p - 1) - 1) + (p - 1) * (p - 1) := by
  have hr : rows ≤ p - 1 := Nat.le_sub_one_of_lt hrows
  have hL : Λ ≤ p - 1 := Nat.le_sub_one_of_lt hΛp
  have hr13 : 3 + 13 * rows ≤ 3 + 13 * (p - 1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left 13 hr) _
  have h2L : 2 * Λ - 1 ≤ 2 * (p - 1) - 1 := by omega
  have hLL : Λ * Λ ≤ (p - 1) * (p - 1) := Nat.mul_le_mul hL hL
  exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul hr13 h2L) _) hLL

/-- Exact-quad cubic gap from `p₀ = 25`.  Measured, not argued: the
    implication fails at 24. -- the paper -/
theorem cubic_gap_of_twenty_five {p : ℕ} (hp : 25 ≤ p) :
    1 + (3 + 13 * (p - 1)) * (2 * (p - 1) - 1) + (p - 1) * (p - 1) < p ^ 3 := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n hn _ih =>
    have hn1 : 1 ≤ n := Nat.le_trans (by norm_num : 1 ≤ 25) hn
    have h2n : 1 ≤ 2 * n := Nat.le_trans (by norm_num : 1 ≤ 2) (Nat.mul_le_mul_left 2 hn1)
    simp only [Nat.add_sub_cancel]
    apply Nat.cast_lt (α := ℤ) |>.mp
    push_cast [Nat.cast_sub h2n]
    nlinarith

theorem seedBudgetVcomp_lt_pow_of_bounds_twenty_five {Λ rows p : ℕ}
    (hrows : rows < p) (hΛp : Λ < p) (hp : 25 ≤ p) :
    GoodSeed.seedBudget Λ rows + 3 * rows * (2 * Λ - 1) < p ^ 3 := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by norm_num : 0 < 25) hp
  have h1 := seedBudgetVcomp_le_exact_quad (Λ := Λ) (rows := rows)
  have h2 := seedBudgetVcomp_exact_quad_le_of_bounds hrows hΛp hp0
  have hgap := cubic_gap_of_twenty_five hp
  exact lt_of_le_of_lt (le_trans h1 h2) hgap

/-- Live seed-budget derivation.  Floor `25 ≤ p` is the measured `p₀`
: least `p` such that `rows < p ∧ Λ < p → budget < p³`.
    Tags still only need `11 < p`. -- the paper -/
theorem seedBudget_lt_card_of_bounds_twenty_five {Λ rows : ℕ}
    (hK : Module.finrank F K = 3)
    (hrows : rows < ringChar K)
    (hΛp : Λ < ringChar K)
    (hp : 25 ≤ ringChar K) :
    GoodSeed.seedBudget Λ rows + 3 * rows * (2 * Λ - 1) < Fintype.card K :=
  lt_of_lt_of_le
    (seedBudgetVcomp_lt_pow_of_bounds_twenty_five hrows hΛp hp)
    (card_K_ge_char_cubed (F := F) hK)

/-- §1-facing spelling of `hF` when `F = ZMod p`. -- the paper -/
theorem dvd_card_sub_one_of_pmod {p h : ℕ} [hp : Fact p.Prime]
    (hm : p ≡ 1 [MOD 3 * 2 ^ h]) :
    3 * 2 ^ h ∣ p - 1 :=
  (Nat.modEq_iff_dvd' (Nat.succ_le_of_lt hp.out.pos)).mp hm.symm

/-- Every atom the ROM run produces stays `< q`.
    Named side condition, not a growth theorem.  Does
    **not** name the result, so it cannot smuggle in `hrun`. -/
def RunBoundedBy (q fuel : ℕ) (subject formula : Noun) : Prop :=
  ∃ result, evalGRom q fuel subject formula = some result

theorem runBoundedBy_of_grom {q fuel : ℕ} {subject formula result : Noun}
    (h : evalGRom q fuel subject formula = some result) :
    RunBoundedBy q fuel subject formula :=
  ⟨result, h⟩

/-- `evalN` plus the named atom-bound identify the guarded ROM result. -/
theorem evalGRom_of_runBounded {q fuel : ℕ} {subject formula result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy q fuel subject formula) :
    evalGRom q fuel subject formula = some result := by
  obtain ⟨r, hr⟩ := hbound
  have heq : r = result :=
    Option.some.inj ((evalGRom_evalN hr).symm.trans hrun)
  rwa [← heq]

/-- `romTree` depends on the ROM equality, not on which proof of the
guarded run produced it. `Eq` is a `Prop`. -/
theorem romTree_grom_irrel {q fuel : ℕ} {subject formula result : Noun}
    (h1 h2 : evalGRom q fuel subject formula = some result) :
    romTree (K := K) (evalGRom_le_evalRom h1) =
      romTree (K := K) (evalGRom_le_evalRom h2) := by
  have : h1 = h2 := Subsingleton.elim _ _
  subst this
  rfl

namespace GoodSeed

/-- `p68` at a *supplied* height, with the four capacity hyps folded into
`programFit ≤ 2^hOrb`.  Used by `p69` (least height) and by the
`p68_of_p69` converse (predecessor height). -- the paper -/
theorem nockCompiles_p69_at {q Λ : ℕ} {hOrb : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) ≤ Λ)
    (hseedcard : seedBudget Λ
        (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
          + 3 *
            (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length *
            (2 * Λ - 1)
          < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hOrbPos : 1 ≤ hOrb)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1)
    (hfit : programFit α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ 2 ^ hOrb)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p68 (hrows := hrows) (hFprime := hFprime) (F := F) (K := K) (q := q) (Λ := Λ) (hOrb := hOrb)
    α αW lmb htwo hgrom hs hf hΛ hseedcard hq hchar hp64 hOrbPos hK hF
    (le_trans (programCompRows_le_fit α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))) hfit)
    (le_trans (programMemShape_le_fit α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))) hfit)
    hwin hmemOrd hKszChar
    (le_trans (programAcc_succ_le_fit α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))) hfit)
    (le_trans (programMemShape_succ_le_fit α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))) hfit)

/-- **Group 2.**  Compiler picks least `h` with `programFit ≤ 2^h`.
    Remain: `compilerKsz < char` (`rows < p`), `programAcc + 3 < orderOf α`,
    disclosed `seedBudget + 3 · rows · (2Λ−1) < |K|`, and `hF` at the
    chosen height. -- the paper -/
theorem nockCompiles_p69 {q Λ : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) ≤ Λ)
    (hseedcard : seedBudget Λ
        (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
          + 3 *
            (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length *
            (2 * Λ - 1)
          < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom hgrom))) ∣ Fintype.card F - 1)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom hgrom)))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p69_at (hrows := hrows) (hFprime := hFprime) (F := F) (K := K) (q := q) (Λ := Λ)
    (hOrb := orbitHeight (programFit α
      (romTree (K := K) (evalGRom_le_evalRom hgrom))))
    α αW lmb htwo hgrom hs hf hΛ hseedcard hq hchar hp64
    (orbitHeight_pos _) hK hF (le_two_pow_orbitHeight _) hwin hmemOrd hKszChar

/-- Predecessor from successor: every `p68` hypothesis still yields the
`p68` conclusion, via `p69_at` at the predecessor height.  No silent
strengthening. -/
noncomputable def nockCompiles_p68_of_p69 {q Λ : ℕ} {hOrb : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) ≤ Λ)
    (hseedcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hOrbPos : 1 ≤ hOrb)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1)
    (hcomp : (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length
      ≤ 2 ^ hOrb)
    (hmem : programMemShape α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ 2 ^ hOrb)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCap : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ hOrb)
    (hmemCap : programMemShape α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ hOrb)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K) :=
  nockCompiles_p69_at (hrows := hrows) (F := F) (K := K) (q := q) (Λ := Λ) (hOrb := hOrb)
    α αW lmb htwo hgrom hs hf hΛ hseedcard hq hchar hp64 hOrbPos hK hF
    (programFit_le_of_caps (α := α)
      (t := romTree (K := K) (evalGRom_le_evalRom hgrom)) hcomp hmemCap hprogCap)
    hwin hmemOrd hKszChar

/-! ## Group 3 — `evalN` plus the named atom-bound

`evalGRom_evalN` is the forward direction.  The converse is the named
hypothesis `RunBoundedBy`, not a growth theorem.
`htwo` is derived from `11 < q = ringChar K`. -- the paper -/

/-- **Group 3.**  `§1`'s `hrun` is `evalN` **plus** `RunBoundedBy`. -- the paper -/
theorem nockCompiles_p70 {q Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy q fuel subject formula)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hseedcard : seedBudget Λ
        (bfsForest [bfsAssign (airReorder (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))]).length
          + 3 *
            (bfsForest [bfsAssign (airReorder (romTree (K := K)
              (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))]).length *
            (2 * Λ - 1)
          < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p69 (hrows := hrows) (hFprime := hFprime) (F := F) (K := K) (q := q) (Λ := Λ)
    α αW lmb (two_ne_zero_of_hq (K := K) hq hchar)
    (evalGRom_of_runBounded hrun hbound) hs hf hΛ hseedcard hq hchar hp64 hK hF
    hwin hmemOrd hKszChar

/-- Predecessor from successor: every `p69` hypothesis still yields the
`p69` conclusion, via `p70`.  No silent strengthening. -/
noncomputable def nockCompiles_p69_of_p70 {q Λ : ℕ}
    (α αW lmb : K) (htwo : (2 : K) ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) ≤ Λ)
    (hseedcard : seedBudget Λ
        (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
          + 3 *
            (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length *
            (2 * Λ - 1)
          < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom hgrom))) ∣ Fintype.card F - 1)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K) :=
  nockCompiles_p70 (hrows := hrows) (F := F) (K := K) (q := q) (Λ := Λ)
    α αW lmb (evalGRom_evalN hgrom) (runBoundedBy_of_grom hgrom) hs hf
    (by
      rwa [romTree_grom_irrel (K := K)
        (evalGRom_of_runBounded (evalGRom_evalN hgrom) (runBoundedBy_of_grom hgrom))
        hgrom])
    (by
      rwa [romTree_grom_irrel (K := K)
        (evalGRom_of_runBounded (evalGRom_evalN hgrom) (runBoundedBy_of_grom hgrom))
        hgrom])
    hq hchar hp64 hK
    (by
      rwa [romTree_grom_irrel (K := K)
        (evalGRom_of_runBounded (evalGRom_evalN hgrom) (runBoundedBy_of_grom hgrom))
        hgrom])
    (by
      rwa [romTree_grom_irrel (K := K)
        (evalGRom_of_runBounded (evalGRom_evalN hgrom) (runBoundedBy_of_grom hgrom))
        hgrom])
    (by
      rwa [romTree_grom_irrel (K := K)
        (evalGRom_of_runBounded (evalGRom_evalN hgrom) (runBoundedBy_of_grom hgrom))
        hgrom])

/-! ## Group 4 — `q` is the compiler's

The generator *chooses* the guard modulus.  Instantiating
every `q` at `ringChar K` makes `hchar` a `rfl` and turns `hq : 11 < q`
into a restriction on the prime (eleven state tags).
`RunBoundedBy (ringChar K)` / `BoundedBy (ringChar K)` now read "atoms
below `p`", the same family as §1's `rowCount < p`. -- the paper -/

/-- **Group 4.**  Guard modulus is `ringChar K`.  `hchar` gone;
    `hp : 11 < ringChar K` is the eleven-tag bound. -- the paper -/
theorem nockCompiles_p71 {Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hseedcard : seedBudget Λ
        (bfsForest [bfsAssign (airReorder (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))]).length
          + 3 *
            (bfsForest [bfsAssign (airReorder (romTree (K := K)
              (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))]).length *
            (2 * Λ - 1)
          < Fintype.card K)
    (hp : 11 < ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p70 (hrows := hrows) (hFprime := hFprime) (F := F) (K := K) (q := ringChar K) (Λ := Λ)
    α αW lmb hrun hbound hs hf hΛ hseedcard hp rfl hp64 hK hF hwin hmemOrd hKszChar

/-- Predecessor from successor: every `p70` hypothesis still yields the
`p70` conclusion, via `p71` after `hchar`.  No silent strengthening. -/
noncomputable def nockCompiles_p70_of_p71 {q Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy q fuel subject formula)
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hseedcard : seedBudget Λ
        (bfsForest [bfsAssign (airReorder (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))]).length
          + 3 *
            (bfsForest [bfsAssign (airReorder (romTree (K := K)
              (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))]).length *
            (2 * Λ - 1)
          < Fintype.card K)
    (hq : 11 < q) (hchar : q = ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K) :=
  nockCompiles_p70 (hrows := hrows) (F := F) (K := K) (q := q) (Λ := Λ)
    α αW lmb hrun hbound hs hf hΛ hseedcard hq hchar hp64 hK hF hwin hmemOrd hKszChar

/-! ## Group 5 — `hs` / `hf` stay (`p72`)

A successful `evalGRom` guards every atom it *reads* (`lusGBy`, `OP_4`)
and every atom it *returns* as a constant (`OP_1` returns `tail` unguarded).
Unvisited subject atoms and unused formula tails are not bounded.  So
`RunBoundedBy` does **not** imply `BoundedBy` of subject or formula
.  `hs` / `hf` remain the paper's typing
.  `RunBoundedBy` is not widened. -/

/-- **Group 5.**  Same binders as `p71`: `hs` / `hf` stay. -- the paper -/
theorem nockCompiles_p72 {Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hseedcard : seedBudget Λ
        (bfsForest [bfsAssign (airReorder (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))]).length
          + 3 *
            (bfsForest [bfsAssign (airReorder (romTree (K := K)
              (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))]).length *
            (2 * Λ - 1)
          < Fintype.card K)
    (hp : 11 < ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p71 (hrows := hrows) (hFprime := hFprime) (F := F) (K := K) (Λ := Λ)
    α αW lmb hrun hbound hs hf hΛ hseedcard hp hp64 hK hF hwin hmemOrd hKszChar

/-- Predecessor from successor: `p72` is `p71`.  No silent strengthening. -/
noncomputable def nockCompiles_p71_of_p72 {Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hseedcard : seedBudget Λ
        (bfsForest [bfsAssign (airReorder (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))]).length
          + 3 *
            (bfsForest [bfsAssign (airReorder (romTree (K := K)
              (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))]).length *
            (2 * Λ - 1)
          < Fintype.card K)
    (hp : 11 < ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K) :=
  nockCompiles_p72 (hrows := hrows) (F := F) (K := K) (Λ := Λ)
    α αW lmb hrun hbound hs hf hΛ hseedcard hp hp64 hK hF hwin hmemOrd hKszChar

/-! ## Group 6 — `hseedcard` in §1 vocabulary (`p73`)

`hKszChar` already is `rows < p` (`compilerKszOf_ge_compRows`). `sizeWindowRootBound` is quadratic, so `rows < p`, `Λ < p` and
`29 ≤ p` give the budget (`seedBudget_lt_card_of_bounds`). `hseedcard` leaves; `hΛp` enters; `11 < p` strengthens to `29 ≤ p`
. **Count unchanged, kind improved.**
This *strengthens*. The predecessor is recovered from the successor by deriving
`hseedcard` and `11 < p`. -/

/-- **Group 6.**  `hseedcard` replaced by `Λ < p` and `29 ≤ p`.
    Count unchanged, kind improved. -- the paper -/
theorem nockCompiles_p73 {Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hΛp : Λ < ringChar K)
    (hp : 29 ≤ ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p72 (hrows := hrows) (hFprime := hFprime) (F := F) (K := K) (Λ := Λ)
    α αW lmb hrun hbound hs hf hΛ
    (seedBudget_lt_card_of_bounds (F := F) (K := K) hK
      (seedRows_lt_char_of_hKszChar (K := K) α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
        hKszChar)
      hΛp hp)
    (Nat.lt_of_lt_of_le (by norm_num : 11 < 29) hp) hp64 hK hF hwin hmemOrd hKszChar

/-- Predecessor conclusion from successor hyps: `p73` derives `hseedcard`
    and `11 < p`, so every `p73` inhabitant is a `p72` inhabitant.
    Strengthening is disclosed. -/
noncomputable def nockCompiles_p72_of_p73 {Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hΛp : Λ < ringChar K)
    (hp : 29 ≤ ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K) :=
  nockCompiles_p73 (hrows := hrows) (F := F) (K := K) (Λ := Λ)
    α αW lmb hrun hbound hs hf hΛ hΛp hp hp64 hK hF hwin hmemOrd hKszChar

/-! ## Group 7 — §1 spellings (`p74` / `nockCompiles`)

`hwin` implies `α ≠ 0` (`alpha_ne_zero_of_lt_order`).  `hF` is
`3 · 2^h ∣ |F| − 1`; when `F = ZMod p` this is `p ≡ 1 (mod 3 · 2^h)`
(`dvd_card_sub_one_of_pmod`).  `hK` stays §1's `finrank = 3`. -/

/-- **Group 7 / north-star name.**  Same binders as `p73`.
    `α ≠ 0` is the one-line corollary `alpha_ne_zero_of_lt_order hwin`.
    `hF` is `p ≡ 1 (mod 3 · 2^h)` at `F = ZMod p`. -- the paper -/
theorem nockCompiles_p74 {Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hΛp : Λ < ringChar K)
    (hp : 29 ≤ ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p73 (hrows := hrows) (hFprime := hFprime) (F := F) (K := K) (Λ := Λ)
    α αW lmb hrun hbound hs hf hΛ hΛp hp hp64 hK hF hwin hmemOrd hKszChar

/-- Predecessor from successor: `p74` is `p73`.  No silent strengthening. -/
noncomputable def nockCompiles_p73_of_p74 {Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hΛp : Λ < ringChar K)
    (hp : 29 ≤ ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K) :=
  nockCompiles_p74 (hrows := hrows) (F := F) (K := K) (Λ := Λ)
    α αW lmb hrun hbound hs hf hΛ hΛp hp hp64 hK hF hwin hmemOrd hKszChar

/-- `α ≠ 0` follows from `hwin` by `alpha_ne_zero_of_lt_order`. -- the paper -/
noncomputable def nockCompiles {Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hΛp : Λ < ringChar K)
    (hp : 29 ≤ ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p74 (hrows := hrows) (hFprime := hFprime) (F := F) (K := K) (Λ := Λ)
    α αW lmb hrun hbound hs hf hΛ hΛp hp hp64 hK hF hwin hmemOrd hKszChar

/-! ## Group 8 — compiler picks `Λ` (`p75`)

`Λ` is a compiler parameter, so the compiler sets it to the program's
own leaf bound.  `{Λ}` and `hΛ` leave (`hΛ` is `le_rfl`).  `hΛp` becomes
`programLeafBound … < ringChar K` — a leaf-count bound on the
program's trace nouns (`GenTraceConfined.lean::programLeafBound`), not a row-count condition (`hKszChar` is that).
`seedBudget_lt_card_of_bounds` is applied at `Λ := programLeafBound`.
`P.optimized.Λ` equals that leaf bound on the *witness* the proof
constructs (not a statement fact: the conclusion is `∃ hOrb, ∃ package`).
Expected **28/12 → 26/11**.

Converse `p74_of_p75` recovers `p74` at arbitrary `Λ` from `p75` by
`programLeafBound ≤ Λ < p → programLeafBound < p` (`hΛ` + `p74`'s own
`hΛp`).  The window is monotone (`traceConfined_of_leafBound` /
`leafBound_of_traceConfined`).  No extra hypothesis. -- the paper -/

/-- **Group 8.**  Compiler sets `Λ := programLeafBound`.  `{Λ}` / `hΛ`
    gone; `hΛp` is the leaf window versus `p`. -- the paper -/
theorem nockCompiles_p75
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛp : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
      < ringChar K)
    (hp : 29 ≤ ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p74 (hrows := hrows) (hFprime := hFprime) (F := F) (K := K)
    (Λ := programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))
    α αW lmb hrun hbound hs hf le_rfl hΛp hp hp64 hK hF hwin hmemOrd hKszChar

/-- Predecessor from successor: `p74` at arbitrary `Λ` follows from
    `p75` by `hΛ` + `hΛp` (`programLeafBound < p`).  No silent
    strengthening; `Λ < p` is `p74`'s own binder. -- the paper -/
noncomputable def nockCompiles_p74_of_p75 {Λ : ℕ}
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛ : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ≤ Λ)
    (hΛp : Λ < ringChar K)
    (hp : 29 ≤ ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K) :=
  nockCompiles_p75 (hrows := hrows) (F := F) (K := K)
    α αW lmb hrun hbound hs hf (lt_of_le_of_lt hΛ hΛp) hp hp64 hK hF hwin hmemOrd hKszChar

/-! ## Group 9 — measured floor `p₀ = 25` (`p76`)

W9's `29 ≤ p` served `rows < p ∧ Λ < p → seedBudgetVcomp < p³` via a
loose `2Λ` majorant.  The exact implication's least **positive** `p`
is **25**.  `hp` restates as
`25 ≤ ringChar K`.  Kind improved, not a lowered field floor: no prime
in `[25, 28]`, and `hF` excludes 29 (`3 ∤ 28`), so the smallest
admissible prime is **31**.  Floor cannot go below 12 (eleven tags).  `seedBudget` / `sizeWindowRootBound` are not
tightened.

Converse `p75_of_p76` is under `p75`'s telescope (`29 ≤ p` implies
`25 ≤ p`).  Empty `typeDiff` vs `p75` except `hp`. -- the paper -/

/-- **Group 9.**  Floor is the measured `p₀ = 25`.
    **Repair (ii).**  The generator builds the memory walk
    at the timestamp coin `α` (`mwa := α`), and `hwin` is the conjunction
    `programAcc t + 3 < orderOf α ∧ programMemShape α t ≤ orderOf α`: distinct timestamps
 and distinct walk line numbers `α^i` over the memory rows (`:835`, `:1005`).
    The second half is exactly `buildFullPackage`'s `hordM`; the new `hwin` subsumes the old one.
    **S2.**  The memory walk now runs at its
    own explicit coin `αW` (`mwa := αW`, a binder right after `α`), `hwin`'s memory half is
    `programMemShape αW t ≤ orderOf αW` (α-irrelevant shape, `programMemShape_alpha_irrel`), and the
    conclusion gains `package.optimized.family.memoryWalkAlpha = αW`.  `hrows.2 :
    programMemShape α t < ringChar K` stays at `α` (the package's memory rows are built at the
    timestamp coin; the shape is α-irrelevant, so this is no restriction on `αW`).
    -- the paper -/
theorem nockCompiles_p76
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛp : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
      < ringChar K)
    (hp : 25 ≤ ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α ∧
      programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K)
    (hFprime : GeneratedField.PrimeFieldElems F) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (F) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  nockCompiles_p72 (hrows := hrows) (hFprime := hFprime) (F := F) (K := K)
    (Λ := programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))
    α αW lmb hrun hbound hs hf le_rfl
    (seedBudget_lt_card_of_bounds_twenty_five (F := F) (K := K) hK
      (seedRows_lt_char_of_hKszChar (K := K) α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
        hKszChar)
      hΛp hp)
    (Nat.lt_of_lt_of_le (by norm_num : 11 < 25) hp) hp64 hK hF hwin.1
    hwin.2 hKszChar

/-- Predecessor from successor: `p75` follows from `p76` because
    `29 ≤ p` gives `25 ≤ p`.  No silent strengthening. -- the paper -/
noncomputable def nockCompiles_p75_of_p76
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛp : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
      < ringChar K)
    (hp : 29 ≤ ringChar K)
    (hp64 : ringChar F < 2 ^ 64)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card F - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α)
    (hmemOrd : programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K)
    (hrows : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))).length < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < ringChar K) :=
  nockCompiles_p76 (hrows := hrows) (F := F) (K := K)
    α αW lmb hrun hbound hs hf hΛp
    (Nat.le_trans (by norm_num : 25 ≤ 29) hp) hp64 hK hF ⟨hwin, hmemOrd⟩ hKszChar

end GoodSeed

/-! ## H1.5b Part 2a — the `rowsBound` bridges

They read the generated package's row counts
back to the program-level counts the §1 binders speak about, so the field's fill on the generated
package is `genPackage_rowsBound_of_hrows` from a program-level `hrows`, and at `F = ZMod p`
`hrows` itself is `GoodSeed.hrows_of_hF` (the orbit-order hypothesis `hF`). Neither needs
`3·compRows + 3 < p` nor a general-`F` `Fintype.card`.
-- -/

section RowsBoundBridges

open BuildablePackage BuildableChips OptimizedComputeCollisionBound

/-- The full package's objects carry the buildable carrier's configuration (`buildObjects`). -/
theorem buildFullPackage_objects_cfg
    (E : BuildableNockExecution F K) (I : BuildableChips.Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    {hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ}
    {hF : GeneratedField.PrimeFieldElems F} :
    (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).objects.cfg = E.cfg :=
  rfl

/-- The generated carrier's row counts are the program-level counts: the BFS row count of the
AIR-ordered tree (`programCompRows`) and the seed- and `λ`-free memory shape
(`programMemShape`). -/
theorem genBuildableOfProgram_rowCounts_eq {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K} :
    (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows = programCompRows t ∧
    (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows = programMemShape α t :=
  ⟨genComputeRows_bfsForest_length z α t, (programMemShape_spec (lmb := chal.lam) z α t).symm⟩

/-- **The generated carrier's `rowsBound` hypothesis** (what `buildFullPackage` takes) from the
program-level `hrows`. -/
theorem genBuildableOfProgram_rowsBound_of_hrows {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K}
    (hrows : 3 * programCompRows t < ringChar K ∧ programMemShape α t < ringChar K) :
    3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K := by
  obtain ⟨hc, hm⟩ := genBuildableOfProgram_rowCounts_eq (F := F) (q := q) (Λ := Λ) (z := z)
    (α := α) (hz := hz) (htwo := htwo) (a := a) (b := b) (c := c) (chal := chal) (hinp := hinp)
    (hmi := hmi) (Ksz := Ksz) (orbit := orbit) (horb := horb) (h := h) (hseed := hseed)
    (hcoins := hcoins) (hΛ := hΛ) (hconf := hconf) (hmempos := hmempos) (hcomp := hcomp)
    (hmem := hmem) (B := B) (hB := hB) (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb)
    (hq := hq) (hchar := hchar) (haxis := haxis) (hbad := hbad) (hout := hout)
    (hKszChar := hKszChar) (hprogCap := hprogCap) (hmemCap := hmemCap) (hfirst := hfirst)
  rw [hc, hm]
  exact hrows

/-- The generated package's row counts (`buildFullPackage` at the generated carrier) are the
program-level counts. -/
theorem genPackage_rowCounts_eq {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K}
    {I : BuildableChips.Inputs (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
      chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
      hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)}
    {R : CommitmentResidual (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
      chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
      hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)}
    {hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K)}
    {hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
      htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
      hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec}
    {hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
      z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
      hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)}
    {hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf I.computeWalkAlpha}
    {hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf I.memoryWalkAlpha}
    {hrowsE : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K}
    {hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ}
    {hF : GeneratedField.PrimeFieldElems F} :
    (buildFullPackage _ I R hzero hprl hmore hord hordM hrowsE hgenF hF).objects.cfg.compRows =
        programCompRows t ∧
      (buildFullPackage _ I R hzero hprl hmore hord hordM hrowsE hgenF hF).objects.cfg.memRows =
        programMemShape α t := by
  rw [buildFullPackage_objects_cfg]
  exact genBuildableOfProgram_rowCounts_eq

/-- **The generated package's `rowsBound`** from the program-level `hrows` binder. -/
theorem genPackage_rowsBound_of_hrows {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K}
    {I : BuildableChips.Inputs (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
      chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
      hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)}
    {R : CommitmentResidual (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
      chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
      hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)}
    {hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K)}
    {hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
      htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
      hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec}
    {hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
      z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
      hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)}
    {hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows ≤
        orderOf I.computeWalkAlpha}
    {hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows →
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows ≤
        orderOf I.memoryWalkAlpha}
    {hrowsE : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K}
    {hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ}
    {hF : GeneratedField.PrimeFieldElems F}
    (hrows : 3 * programCompRows t < ringChar K ∧ programMemShape α t < ringChar K) :
    3 * (buildFullPackage _ I R hzero hprl hmore hord hordM hrowsE hgenF hF).objects.cfg.compRows < ringChar K ∧
      (buildFullPackage _ I R hzero hprl hmore hord hordM hrowsE hgenF hF).objects.cfg.memRows < ringChar K := by
  obtain ⟨hc, hm⟩ := genPackage_rowCounts_eq (I := I) (R := R) (hzero := hzero) (hprl := hprl)
    (hmore := hmore) (hord := hord) (hordM := hordM) (hrowsE := hrowsE) (hgenF := hgenF) (hF := hF)
  rw [hc, hm]
  exact hrows

end RowsBoundBridges

end

/-! ## Group 10 — §1's `ZMod p` spelling

The general-`F` theorem (`p76`) stays; it is the stronger statement.
This specialisation puts the paper prime in every explicit hypothesis
(`ringChar K` still appears in the `[CharP K (ringChar K)]` instance
and as the verifier's modulus in the conclusion, both forced by the
package types and equal to `p` by `ringChar_eq_prime`).  Derives
`ringChar K = p` (`ringChar_eq_of_algebra_field` +
`ZMod.ringChar_zmod_n`), and never assumes it.  Same explicit count
as `p76`.  Converse: `p76` at `F = ZMod p` from this theorem.
-- -/

namespace GoodSeed

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
variable [FiniteDimensional (ZMod p) K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

theorem ringChar_eq_prime : ringChar K = p := by
  rw [← ringChar_eq_of_algebra_field (F := ZMod p) (K := K), ZMod.ringChar_zmod_n]

/-- **`hrows` from the orbit-order hypothesis at `F = ZMod p`** (H1.5b Part 2a, F4): with
`3 · 2^h ∣ p − 1` at `h = orbitHeight (programFit α t)`, both row counts are `≤ 2^h`
(`programCompRows_le_fit`, `programMemShape_le_fit`), so `3·compRows ≤ 3·2^h ≤ p − 1 < p` and
`memRows ≤ 2^h < p`.  This is why `nockCompiles_zmod` needs no `hrows` binder; the general-`F`
theorems carry it (their `hF` divides `|F| − 1`, not `p − 1`). -- the paper -/
theorem hrows_of_hF (α : K) (t : NTree (GenComputeRow K))
    (hF : 3 * 2 ^ orbitHeight (programFit α t) ∣ p - 1) :
    3 * programCompRows t < p ∧ programMemShape α t < p := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hle : 3 * 2 ^ orbitHeight (programFit α t) ≤ p - 1 :=
    Nat.le_of_dvd (by omega) hF
  have hfit : programFit α t ≤ 2 ^ orbitHeight (programFit α t) :=
    le_two_pow_orbitHeight _
  have hc := (programCompRows_le_fit α t).trans hfit
  have hm := (programMemShape_le_fit α t).trans hfit
  constructor <;> omega

/-- **§1 spelling.**  General-`F` theorem specialised at `F = ZMod p`.
    `ringChar K = p` is derived; the literal `p` replaces `ringChar K`
    in every explicit hypothesis.  The Form R leftovers `hfirst`/`hmore` (first-row and
    later-seed `pt = (0, 0)`) are discharged at `p68` (ROOTZERO: the honest read cancels its
    descent at every sampled `λ`, for every axis `1 ≤ a < p`), and `hbasis` by `compilerBasis_formR`.
    28th λ-fix pass 2: `lmb` is the sampled Form R `λ`, a binder beside `α`, and the
    conclusion ties the package to it (`….challenges.lam = lmb`).  `hp64 : p < 2^64` (after `hp`)
    makes the compute-side Form R premises lemmas: `hwidth` is `FormRWidth_of_hp64`, `hax` is
    `GenFormRAxisLambda.genComputeRows_rowsFormRAxisBound`.  No residual premise remains.
    **Repair (ii).**  The generator builds the memory walk
    at the timestamp coin `α` (`mwa := α`), and `hwin` is the conjunction
    `programAcc t + 3 < orderOf α ∧ programMemShape α t ≤ orderOf α`: distinct timestamps
 and distinct walk line numbers `α^i` over the memory rows (`:835`, `:1005`).
    The second half is exactly `buildFullPackage`'s `hordM`; the new `hwin` subsumes the old one.
    **S2.**  The memory walk now runs at its
    own explicit coin `αW` (`mwa := αW`, a binder right after `α`), `hwin`'s memory half is
    `programMemShape αW t ≤ orderOf αW` (α-irrelevant shape, `programMemShape_alpha_irrel`), and the
    conclusion gains `package.optimized.family.memoryWalkAlpha = αW`.  `hrows.2 :
    programMemShape α t < ringChar K` stays at `α` (the package's memory rows are built at the
    timestamp coin; the shape is α-irrelevant, so this is no restriction on `αW`).
    -- the paper -/
theorem nockCompiles_zmod
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject)
    (hf : FieldEmbedding.BoundedBy p formula)
    (hΛp : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) < p)
    (hp : 25 ≤ p)
    (hp64 : p < 2 ^ 64)
    (hK : Module.finrank (ZMod p) K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ p - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α ∧
      programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < p) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K
      (orbitHeight (programFit α
        (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ package.optimized.family.memoryWalkAlpha = αW :=
  let hr := ringChar_eq_prime (p := p) (K := K)
  nockCompiles_p76 (F := ZMod p) (K := K) (hFprime := GeneratedField.primeFieldElems_zmod p)
    (hrows := (fun h => ⟨h.1.trans_eq (ringChar_eq_prime (p := p) (K := K)).symm,
        h.2.trans_eq (ringChar_eq_prime (p := p) (K := K)).symm⟩)
      (hrows_of_hF (p := p) (K := K) α _ hF))
    α αW lmb hrun (hr.symm ▸ hbound) (hr.symm ▸ hs) (hr.symm ▸ hf) (hr.symm ▸ hΛp)
    (hr.symm ▸ hp) (by rw [ZMod.ringChar_zmod_n]; exact hp64) hK (by simpa [ZMod.card] using hF) hwin (hr.symm ▸ hKszChar)

/-- Predecessor from successor: `p76` at `F = ZMod p` from the §1
    spelling, after `ringChar K = p`.  Same explicit binders; Form R
    leftovers residual.  Directly `p76` at `F := ZMod p` (hyps already
    ringChar-shaped; `hK`/`hF` already at `ZMod p`). -- the paper -/
noncomputable def nockCompiles_p76_of_zmod
    (α αW lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy (ringChar K) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar K) subject)
    (hf : FieldEmbedding.BoundedBy (ringChar K) formula)
    (hΛp : programLeafBound
      (airReorder (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
      < ringChar K)
    (hp : 25 ≤ ringChar K)
    (hp64 : ringChar (ZMod p) < 2 ^ 64)
    (hK : Module.finrank (ZMod p) K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α
        (romTree (K := K)
          (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))
        ∣ Fintype.card (ZMod p) - 1)
    (hwin : programAcc
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3
      < orderOf α ∧
      programMemShape αW (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf αW)
    (hKszChar : compilerKszOf (0 : K) α
      (romTree (K := K)
        (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))
      < ringChar K) :=
  nockCompiles_p76 (F := ZMod p) (K := K)
    (hrows := (fun h => ⟨h.1.trans_eq (ringChar_eq_prime (p := p) (K := K)).symm,
        h.2.trans_eq (ringChar_eq_prime (p := p) (K := K)).symm⟩)
      (hrows_of_hF (p := p) (K := K) α _ (by simpa [ZMod.card] using hF)))
    α αW lmb hrun hbound hs hf hΛp hp hp64 hK hF hwin hKszChar
    (GeneratedField.primeFieldElems_zmod p)



end GoodSeed

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.exists_order_of_dvd_card_sub_one
#print axioms Nock.NockVMROM.Thm54.TraceGen.compilerPackageOrbit
#print axioms Nock.NockVMROM.Thm54.TraceGen.compilerExecutionOrbit
#print axioms Nock.NockVMROM.Thm54.TraceGen.hcard_of_hF_hK
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p68
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p67_of_p68
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p69
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p68_of_p69
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p70
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p69_of_p70
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p71
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p70_of_p71
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p72
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p71_of_p72
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p73
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p72_of_p73
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p74
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p73_of_p74
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p75
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p74_of_p75
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p75_of_p76
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76_of_zmod
#print axioms Nock.NockVMROM.Thm54.TraceGen.two_ne_zero_of_hp
#print axioms Nock.NockVMROM.Thm54.TraceGen.alpha_ne_zero_of_lt_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.seedBudget_lt_card_of_bounds
#print axioms Nock.NockVMROM.Thm54.TraceGen.seedBudget_lt_card_of_bounds_twenty_five
#print axioms Nock.NockVMROM.Thm54.TraceGen.compilerKszOf_ge_compRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.buildFullPackage_objects_cfg
#print axioms Nock.NockVMROM.Thm54.TraceGen.genBuildableOfProgram_rowCounts_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.genPackage_rowCounts_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.genBuildableOfProgram_rowsBound_of_hrows
#print axioms Nock.NockVMROM.Thm54.TraceGen.genPackage_rowsBound_of_hrows
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.hrows_of_hF
