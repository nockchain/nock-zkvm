import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestBadPole
import Nock.NockVMROM.Thm54.VclL.Compute.TowerSat
import Nock.NockVMROM.Thm54.VclL.Compute.TowerC2cBase
import Nock.NockVMROM.Thm54.VclL.Compute.TowerWalkGen
import Nock.NockVMROM.Thm54.VclL.Compute.TowerCompChipQ7
import Nock.NockVMROM.Thm54.TraceGen.GenSlotKeys

/-!
# The honest datum of the VCL compute family at the tower chip

* `walkSat_closed`: the explicit closed forms of `Walk.walkSat_exists` satisfy `WalkSat` (a theorem about an
  explicit construction, no choice).
* `honestWalkT`: the honest BFS walk of the generator at the walk coins `(α, γ) = (ι χ₀, ι χ₁)`, explicit.
* `goodCFT_honest`: `GoodCFT` at a verifier datum whose compute nodes are the first `N` orbit points
  `ω^i`, under the size condition `N ≤ 2^h` and the field facts of `V.Checks` (`25 ≤ char F`, `3N < char K`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.ComputeTable Nock.Reified Module
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.ComputeWalkLabel Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.OptimizedComputeCodec

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The closed-form walk columns -/

section Closed
variable {K : Type} [Field K]

/-- The closed-form line column `α^k`. -/
def lnClosed (α : K) : ℕ → K := fun k => α ^ k
/-- The closed-form count column `ic·α^{Sf fo k}`. -/
def cntClosed (fo : ℕ → ℕ) (α ic : K) : ℕ → K := fun k => ic * α ^ (Walk.Sf fo k)
/-- The closed-form (telescoped) accumulator column. -/
def accClosed (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (α seed ic : K) : ℕ → K :=
  fun k => seed - (Walk.nodeListP cur k).eval α + ic * ∑ i ∈ Finset.Icc 1 k, Walk.childSum chld' fo α i

/-- **The closed forms satisfy `WalkSat`** (the witnesses of `Walk.walkSat_exists`, as a theorem about the
explicit columns). -/
theorem walkSat_closed (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (α seed ic : K) {h : ℕ} (hh : 1 ≤ h) :
    Walk.WalkSat cur chld' fo (lnClosed α) (cntClosed fo α ic) (accClosed cur chld' fo α seed ic)
      α seed ic h := by
  refine
    { hpos := hh
      ln1 := by simp [lnClosed]
      lnInc := fun i _ _ => by simp only [lnClosed]; rw [pow_succ]; ring
      count1 := by simp only [cntClosed]; rw [Walk.Sf_one]
      countInc := fun i _ _ => by simp only [cntClosed]; rw [Walk.Sf_succ, pow_add]; ring
      accInit := ?_
      accStep := ?_ }
  · have hnl : (Walk.nodeListP cur 1).eval α = cur 1 * α := by rw [Walk.nodeListP_eval]; simp
    have hkey : ic * (∑ j ∈ Finset.Icc 1 1, Walk.childSum chld' fo α j)
        = ∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * ic * chld' 1 l := by
      rw [Finset.Icc_self, Finset.sum_singleton]
      unfold Walk.childSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [show (1 : ℕ) - 1 = 0 from rfl, Walk.Sf_zero, Nat.add_zero]
      ring
    simp only [lnClosed, accClosed, pow_one]
    rw [hnl]
    linear_combination hkey
  · intro i _ _
    have hnl : (Walk.nodeListP cur (i + 1)).eval α
        = (Walk.nodeListP cur i).eval α + cur (i + 1) * α ^ (i + 1) := by
      rw [Walk.nodeListP_succ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
    have hcssum : (∑ j ∈ Finset.Icc 1 (i + 1), Walk.childSum chld' fo α j)
        = (∑ j ∈ Finset.Icc 1 i, Walk.childSum chld' fo α j) + Walk.childSum chld' fo α (i + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ i + 1)]
    have hkey : ic * Walk.childSum chld' fo α (i + 1)
        = ∑ l ∈ Finset.Icc 1 (fo (i + 1)),
            α ^ l * (ic * α ^ Walk.Sf fo i) * chld' (i + 1) l := by
      unfold Walk.childSum
      rw [Nat.add_sub_cancel, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [pow_add]; ring
    simp only [lnClosed, accClosed, cntClosed]
    rw [hnl, hcssum]
    linear_combination hkey

end Closed

/-! ## 2. The explicit honest walk of the generator -/

section HW
variable {L : Type} [Field L]

/-- The walk node valuation `RLC^γ(label)`. -/
def nodeValG (γ : L) : Walk.NTree (State × DTcomp L) → L := fun u => Walk.rlc γ (labelVecOfPub u.label.2.2.1)

/-- **The explicit honest walk** over the generator's walk tree `root` at `(α, γ)`: the closed-form
columns at `initial_count = α` and the seed `RLC^γ(label₀)·α`. -/
def honestWalkOf (root : Walk.NTree (State × DTcomp L)) (α γ : L)
    (htopo : ∀ t ∈ Walk.bfsForest [root],
      t.label.1 = t.label.2.2.1.state ∧ fanoutComp t.label.1 = t.children.length ∧
        childLinkComp t.label (fun j => t.childLabel j)) : HonestWalk L :=
  let W := Walk.bfsForest [root]
  let cur := Walk.curCol (nodeValG γ) W
  let chld := Walk.chldCol (nodeValG γ) W
  let fo := Walk.foCol W
  let seed := Walk.rlc γ (labelVecOfPub (bfsPubAt root 0)) * α
  { root := root
    nodeVal := nodeValG γ
    α := α
    γ := γ
    seed := seed
    ln := lnClosed α
    cnt := cntClosed fo α α
    acc := accClosed cur chld fo α seed α
    pubAt := bfsPubAt root
    hEnc := fun _ => rfl
    htopo := htopo
    hpub := fun i hi => by simp [bfsPubAt, hi]
    sat := walkSat_closed cur chld fo α seed α (bfsForest_length_pos root)
    seed_eq := rfl }

@[simp] theorem honestWalkOf_root (root : Walk.NTree (State × DTcomp L)) (α γ : L) (h) :
    (honestWalkOf root α γ h).root = root := rfl
@[simp] theorem honestWalkOf_α (root : Walk.NTree (State × DTcomp L)) (α γ : L) (h) :
    (honestWalkOf root α γ h).α = α := rfl
@[simp] theorem honestWalkOf_γ (root : Walk.NTree (State × DTcomp L)) (α γ : L) (h) :
    (honestWalkOf root α γ h).γ = γ := rfl
@[simp] theorem honestWalkOf_pubAt (root : Walk.NTree (State × DTcomp L)) (α γ : L) (h) :
    (honestWalkOf root α γ h).pubAt = bfsPubAt root := rfl

end HW

/-! ## 3. The honest verifier datum: `GoodCFT` -/

section Good
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [CharP K (ringChar K)] [DecidableEq F] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The first `N` orbit points are adjacent. -/
theorem adjacentC_of_pow (V : VerifierData F K hC S)
    (hnodes : ∀ i : Fin V.N, V.computeNodes i = V.orbitC.ω ^ (i : ℕ)) : V.AdjacentC := by
  intro i hi
  rw [hnodes, hnodes]
  simp only
  rw [pow_succ']

/-- The first `N ≤ 2^h` orbit points are distinct (`ω` has order `3·2^h`). -/
theorem injective_of_pow (V : VerifierData F K hC S)
    (hnodes : ∀ i : Fin V.N, V.computeNodes i = V.orbitC.ω ^ (i : ℕ)) (hsize : V.N ≤ 2 ^ hC) :
    Function.Injective V.computeNodes := by
  intro i j hij
  rw [hnodes, hnodes] at hij
  have hord := V.orbitC.order_ω
  have hlt : ∀ k : Fin V.N, (k : ℕ) ∈ Set.Iio (orderOf V.orbitC.ω) := by
    intro k
    simp only [Set.mem_Iio, hord]
    have := k.isLt
    have : 0 < 2 ^ hC := Nat.two_pow_pos hC
    omega
  exact Fin.ext (pow_injOn_Iio_orderOf (hlt i) (hlt j) hij)

/-- The characteristic facts of `GoodCFT` from `25 ≤ char F` (`V.Checks.hp`). -/
theorem hchar_of_hp (hp : 25 ≤ ringChar F) : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1 := by
  intro m hm h1
  have hK : ringChar K = ringChar F := (Algebra.ringChar_eq F K).symm
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · interval_cases m
    simp at h1
  · have h0 : ((m - 1 : ℕ) : K) = 0 := by
      rw [Nat.cast_sub (by omega), h1]; simp
    rw [CharP.cast_eq_zero_iff K (ringChar K)] at h0
    have := Nat.le_of_dvd (by omega) h0
    omega

/-- **`GoodCFT` at the honest datum.** -/
theorem goodCFT_honest (V : VerifierData F K hC S)
    (hnodes : ∀ i : Fin V.N, V.computeNodes i = V.orbitC.ω ^ (i : ℕ)) (hsize : V.N ≤ 2 ^ hC)
    (hp : 25 ≤ ringChar F) (hrowsC : 3 * V.N < ringChar K)
    (ρ : Fin 3 → Quad (algebraMap F K δ)) (hρ : ρ 0 = 0) : GoodCFT δ V ρ :=
  ⟨adjacentC_of_pow V hnodes, injective_of_pow V hnodes hsize, hchar_of_hp hp, by omega, hρ⟩

end Good

/-! ## 4. The honest data at a coin vector -/

section Data
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The base coin `χ k` in `𝕂′`. -/
abbrev ιc (χ : Coins frameVCL K) (k : Fin frameVCL.n) : Quad (algebraMap F K δ) :=
  algebraMap K (Quad (algebraMap F K δ)) (χ k)

/-- The generator row of walk row `j` (0-indexed): the BFS label `j+1` of the AIR-ordered tree. -/
def gRow (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (j : ℕ) : GenComputeRow (Quad (algebraMap F K δ)) :=
  bfsLabelAt (airReorder t) (j + 1)

/-- The row count of the generated tree. -/
def nRows (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) : ℕ := (Walk.bfsForest [airReorder t]).length

/-- The generator's rows, in BFS order. -/
def genRowsT (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) : List (GenComputeRow (Quad (algebraMap F K δ))) :=
  (List.range' 1 (nRows t)).map (bfsLabelAt (airReorder t))

/-- The demand of the run (the memory side's `Demand`). -/
def demT (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) : Demand := demandOfRowsD (genRowsT t)

/-- The state index of walk row `j` (coin-free). -/
def stT (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (j : ℕ) : ℕ :=
  (stateIndex (gRow t j).skel.state : ℕ)

/-- The walk tree at the coins. -/
def walkRootT (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) : Walk.NTree (State × DTcomp (Quad (algebraMap F K δ))) :=
  genWalkRoot (zQuad δ χ) αs (ιc χ ⟨8, by decide⟩) (ιc χ ⟨9, by decide⟩) (ιc χ ⟨10, by decide⟩) t

/-- **The honest walk at the coins** (walk coins `α = ι χ₀`, `γ = ι χ₁`). -/
def walkT (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result)) :
    HonestWalk (Quad (algebraMap F K δ)) :=
  honestWalkOf (walkRootT χ αs t) (ιc χ ⟨0, by decide⟩) (ιc χ ⟨1, by decide⟩)
    (genWalk_htopo _ _ _ _ _ hgen)

/-- The decoded row of walk row `j`. -/
def decT (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ))
    (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (j : ℕ) : Dec (Quad (algebraMap F K δ)) :=
  (renderNode (zQuad δ χ) αs (gRow t j)).row.2.2.2

/-- Serial column. -/
def serT (j : ℕ) : F := (j : F)
/-- Axis column. -/
def axT (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (j : ℕ) : ℕ := honestAx (gRow t j).skel
/-- Formula index column. -/
def fIdxT (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (j : ℕ) : F := (fIdxOf (demT t) (gRow t j) : F)
/-- The slot-`k` key root's cell index (`vIdx`, slots 1 and 2). -/
def vIT (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (k : ℕ) (j : ℕ) : F :=
  ((demT t).cells.idxOf ((((rowSlotKeys (gRow t j))[k]?).map Prod.fst).getD (.atom 0)) : F)

/-- **The honest terminals** (`honestReqCF` at the run's demand). -/
def reqT (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (χ : Coins frameVCL K) :
    Fin 3 → Quad (algebraMap F K δ) :=
  honestReqCF (γC χ) (ρC χ) (zC χ) (demT t).cells (demT t).preads (demT t).reads

/-- **The honest `Msg0`**: the first / last state selector banks (`20..30`, `31..41`), zero elsewhere. -/
def xT (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) : ℕ → F := fun j =>
  if 20 ≤ j ∧ j < 31 then (if j - 20 = stT t 0 then 1 else 0)
  else if 31 ≤ j ∧ j < 42 then (if j - 31 = stT t (nRows t - 1) then 1 else 0) else 0

variable {hC : ℕ} {S : MemShape}

/-- The honest final rows with the accumulator columns given. -/
def rowsAcc (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
    {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
    (accX accP : ℕ → Quad (algebraMap F K δ)) : Fin V.N → TowerRowVals (K := K) δ :=
  rowsFinal V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t) (vIT t 1) (vIT t 2)
    accX accP V.computeNodes V.orbitC.ω (chalVQ7T δ V.basis χ) (pubCFT δ V (xT t) (reqT t χ) χ)

/-- The row environment of the honest trace with given accumulator columns. -/
def envAcc (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
    {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
    (accX accP : ℕ → Quad (algebraMap F K δ)) (j : ℕ) : Env F :=
  if h : j < V.N then
    Reify.envOfTrace (honestQT V.basis V.computeNodes (rowsAcc V χ αs hgen accX accP) vclWidthT) V.orbitC.ω
      (V.computeNodes ⟨j, h⟩) (chalVQ7T δ V.basis χ) (pubCFT δ V (xT t) (reqT t χ) χ)
  else Reify.envOfTrace (fun _ : Fin vclWidthT => 0) 0 0 (fun _ => 0) (fun _ => 0)

/-- **The honest accumulator columns**: prefix sums of the per-row `𝕂′` terms at the rows with the
accumulators zeroed (the terms read no accumulator column). -/
def accXT (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
    {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
    (j : ℕ) : Quad (algebraMap F K δ) :=
  ∑ k ∈ Finset.range j, termQ δ V.basis accSlotsX accSlotsXIm (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) k)
def accPT (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
    {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
    (j : ℕ) : Quad (algebraMap F K δ) :=
  ∑ k ∈ Finset.range j, termQ δ V.basis accSlotsPT accSlotsPImT (envAcc V χ αs hgen (fun _ => 0) (fun _ => 0) k)

/-- **The honest rows.** -/
def rowsT (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
    {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result)) :
    Fin V.N → TowerRowVals (K := K) δ :=
  rowsAcc V χ αs hgen (accXT V χ αs hgen) (accPT V χ αs hgen)

/-- **The honest trace** (`honestQ`): the interpolated honest rows at the compute nodes. -/
def traceT (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
    {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result)) :
    Fin (tableVCLT hC).width → Polynomial F :=
  honestQT V.basis V.computeNodes (rowsT V χ αs hgen) vclWidthT

/-- The honest row environment (`envOfTrace` of `traceT` at node `i`, tower coins / publics). -/
def envT (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
    {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
    (i : Fin V.N) : Env F :=
  Reify.envOfTrace (traceT V χ αs hgen) V.orbitC.ω (V.computeNodes i) (chalVQ7T δ V.basis χ)
    (pubCFT δ V (xT t) (reqT t χ) χ)

theorem badSeedsT_card_self (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) :
    (badSeedsT δ t).card ≤ (badSeedsT δ t).card := le_rfl

/-- **The honest bad list** (C4a's `honestBadCF` at the run, `h := N`, states `stT`). -/
def badT (V : VerifierData F K hC S) (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) :
    List (TSummand F K hC S) :=
  honestBadCF δ t (badSeedsT δ t).card le_rfl
    ((bfsForest [airReorder t]).length * (Fintype.card K * Fintype.card K)) le_rfl V.N V.hN V
    (fun i => stT t i)

end Data

/-! ## 5. Stagedness of the honest trace -/

section Staged
open Nock.NockVMROM.Thm54.VclL
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] {hC : ℕ} {S : MemShape}

/-- Round-`≤ 1` source columns `13..201` read a role `< 58`. -/
theorem role_lt58_of_round (j : ℕ) (h1 : 13 ≤ j) (h2 : j < 202) (hr : colRoundVCLE j ≤ 1) :
    (j - 13) / 3 < 58 := by
  have key : ∀ j : Fin 202, 13 ≤ j.1 → colRoundVCLE j.1 ≤ 1 → (j.1 - 13) / 3 < 58 := by decide +kernel
  exact key ⟨j, h2⟩ h1 hr

/-- The round-`0` columns of `tableVCLT` below `232`. -/
theorem round0_cols (j : ℕ) (h2 : j < 232) (hr : colRoundVCLE j = 0) :
    j < 13 ∨ (202 ≤ j ∧ j < 208) ∨ (220 ≤ j ∧ j < 223) := by
  have key : ∀ j : Fin 232, colRoundVCLE j.1 = 0 →
      j.1 < 13 ∨ (202 ≤ j.1 ∧ j.1 < 208) ∨ (220 ≤ j.1 ∧ j.1 < 223) := by decide +kernel
  exact key ⟨j, h2⟩ hr

/-- Columns `202..231` of round `≤ 1` are the round-`0` VCL columns. -/
theorem vcl_round_le1 (j : ℕ) (h1 : 202 ≤ j) (h2 : j < 232) (hr : colRoundVCLE j ≤ 1) :
    (202 ≤ j ∧ j < 208) ∨ (220 ≤ j ∧ j < 223) := by
  have key : ∀ j : Fin 232, 202 ≤ j.1 → colRoundVCLE j.1 ≤ 1 →
      (202 ≤ j.1 ∧ j.1 < 208) ∨ (220 ≤ j.1 ∧ j.1 < 223) := by decide +kernel
  exact key ⟨j, h2⟩ h1 hr

/-- The round-`0` VCL fill reads no inverse / accumulator. -/
theorem vclFill_round0 (b : Basis (Fin 3) F K) (ser : F) (ax : ℕ) (fIdx vI0 vI1 : F)
    (i0 i1 i2 aX aP : Quad (algebraMap F K δ)) (j : ℕ)
    (hj : (202 ≤ j ∧ j < 208) ∨ (220 ≤ j ∧ j < 223)) :
    vclFill (δ := δ) b ser ax fIdx vI0 vI1 i0 i1 i2 aX aP j =
      vclFill (δ := δ) b ser ax fIdx vI0 vI1 0 0 0 0 0 j := by
  have hl : ∀ (x : K) (base : ℕ), (223 ≤ base ∨ (214 ≤ base ∧ base + 3 ≤ 220)) → limbAt b x base j = 0 := by
    intro x base hb
    unfold limbAt
    rw [dif_neg (by omega)]
  unfold vclFill
  split_ifs <;> first
    | rfl
    | simp only [hl _ inv0Base (Or.inl (by simp [inv0Base])), hl _ (lookupInvBase 0) (Or.inr (by simp [lookupInvBase])),
      hl _ (lookupInvBase 1) (Or.inr (by simp [lookupInvBase])), hl _ accExportBase (Or.inl (by simp [accExportBase])),
      hl _ accPathBase (Or.inl (by simp [accPathBase])), hl _ (invImBase 0) (Or.inl (by simp [invImBase])),
      hl _ (invImBase 1) (Or.inl (by simp [invImBase])), hl _ (invImBase 2) (Or.inl (by simp [invImBase])),
      hl _ accImExport (Or.inl (by simp [accImExport])), hl _ accImPath (Or.inl (by simp [accImPath]))]

/-- **Column congruence below round 2**: two row families agreeing on the base, on every role `< 58`, and on
the round-0 VCL columns agree at every column of round `≤ 1`. -/
theorem vclColT_congr_le1 (b : Basis (Fin 3) F K) {n : ℕ} (rows rows' : Fin n → TowerRowVals (K := K) δ)
    (i : Fin n) (hbase : (rows i).base = (rows' i).base)
    (hext : ∀ r : Fin 63, r.val < 58 → (rows i).ext r = (rows' i).ext r)
    (hvcl : ∀ j, (202 ≤ j ∧ j < 208) ∨ (220 ≤ j ∧ j < 223) → (rows i).vcl j = (rows' i).vcl j)
    (j : ℕ) (hr : (if j < 232 then colRoundVCLE j else if j < 388 then 1 else 2) ≤ 1) :
    vclColT b rows j i = vclColT b rows' j i := by
  by_cases h232 : j < 232
  · rw [if_pos h232] at hr
    by_cases h202 : j < 202
    · simp only [vclColT, h202, if_true]
      by_cases h13 : j < 13
      · simp only [srcColT, h13, dif_pos, hbase]
      · have hr58 := role_lt58_of_round j (by omega) h202 hr
        simp only [srcColT, h13, h202, dif_neg, dif_pos, not_false_eq_true]
        rw [hext _ hr58]
    · have hv := vcl_round_le1 j (by omega) h232 hr
      have hn1 : ¬ ((208 ≤ j ∧ j < 214) ∨ (232 ≤ j ∧ j < 394)) := by omega
      simp only [vclColT, h202, hn1, if_false]
      exact hvcl j hv
  · rw [if_neg h232] at hr
    have h388 : j < 388 := by
      by_contra hc; rw [if_neg hc] at hr; omega
    have h202 : ¬ j < 202 := by omega
    have hin : (208 ≤ j ∧ j < 214) ∨ (232 ≤ j ∧ j < 394) := by omega
    simp only [vclColT, h202, hin, if_false, if_true]
    have e1 : ¬ (j + 95 < 13) := by omega
    have e2 : ¬ (j + 95 < 202) := by omega
    have e3 : ¬ (303 ≤ j + 95 ∧ j + 95 < 309) := by omega
    have e4 : 327 ≤ j + 95 := by omega
    simp only [srcColT, e1, e2, e3, e4, dif_neg, if_true, not_false_eq_true]
    have key : ∀ q : Fin 52, ∃ r, imOwner q.1 = some r ∧ r < 58 := by decide +kernel
    obtain ⟨r, hr1, hr2⟩ := key ⟨(j + 95 - 327) / 3, by omega⟩
    simp only at hr1
    rw [hr1]
    simp only [show r < 63 by omega, dif_pos]
    rw [hext ⟨r, by omega⟩ hr2]

end Staged

/-! ## 6. The honest rows by round -/

section RowsRound
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))] {hC : ℕ} {S : MemShape}

/-- The round-`1` core of walk row `j`: a function of `(z, a, b, c)` (and `αs`, the tree) only. -/
def coreAt (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (αs z a b c : Quad (algebraMap F K δ))
    (j : ℕ) (r : Fin 58) : Quad (algebraMap F K δ) :=
  coreExtensionValue (row309 (F := F) (bfsPubAt (genWalkRoot z αs a b c t) j)
    ((renderNode z αs (gRow t j)).row.2.2.2)
    (honestEx ⟨αs, z, a, b, c⟩ (bfsPubAt (genWalkRoot z αs a b c t) j) ((renderNode z αs (gRow t j)).row.2.2.2))
    (honestOverlay (fun k => childStateTagCol (Walk.bfsForest [genWalkRoot z αs a b c t]) (j + 1) k)
      (bfsPubAt (genWalkRoot z αs a b c t) j))) r

variable (V : VerifierData F K hC S) (χ : Coins frameVCL K) (αs : Quad (algebraMap F K δ)) {fuel : ℕ}
  {subject formula : Noun} {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
  (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))

theorem rowsT_ext_lt (i : Fin V.N) (r : ℕ) (hr : r < 58) :
    (rowsT V χ αs hgen i).ext ⟨r, by omega⟩ =
      coreAt t αs (zQuad δ χ) (ιc χ ⟨8, by decide⟩) (ιc χ ⟨9, by decide⟩) (ιc χ ⟨10, by decide⟩) i ⟨r, hr⟩ := by
  simp only [rowsT, rowsAcc, rowsFinal, rowFinal, rowGen]
  rw [genRowVals_ext_lt _ _ _ _ _ _ _ _ _ _ _ _ _ r hr]
  rfl

theorem rowsT_base (i : Fin V.N) :
    (rowsT V χ αs hgen i).base = fun j : Fin 13 =>
      if (j : ℕ) < 11 then (if (j : ℕ) = (stateIndex ((walkT χ αs hgen).pubAt i).state : ℕ) then (1 : F) else 0)
      else if (j : ℕ) = 11 then (if (i : ℕ) = 0 then (1 : F) else 0)
      else (if (i : ℕ) + 1 = V.N then (1 : F) else 0) := rfl

theorem rowsT_vcl (i : Fin V.N) (j : ℕ) (hj : (202 ≤ j ∧ j < 208) ∨ (220 ≤ j ∧ j < 223)) :
    (rowsT V χ αs hgen i).vcl j =
      vclFill (δ := δ) V.basis (serT i) (axT t i) (fIdxT t i) (vIT t 1 i) (vIT t 2 i) 0 0 0 0 0 j := by
  show vclFill (δ := δ) V.basis _ _ _ _ _ _ _ _ _ _ j = _
  exact vclFill_round0 V.basis _ _ _ _ _ _ _ _ _ _ j hj

/-- The honest `z1` column of row `i` is `[axis = 1]`, at every coin. -/
theorem rowsT_vcl_z1 (i : Fin V.N) :
    (rowsT V χ αs hgen i).vcl z1Col = if axT t i = 1 then 1 else 0 := by
  have h : (rowsT V χ αs hgen i).vcl z1Col =
      vclFill (δ := δ) V.basis (serT i) (axT t i) (fIdxT t i) (vIT t 1 i) (vIT t 2 i)
        (inv0F V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t) (vIT t 1) (vIT t 2)
          (accXT V χ αs hgen) (accPT V χ αs hgen) V.computeNodes V.orbitC.ω (chalVQ7T δ V.basis χ)
          (pubCFT δ V (xT t) (reqT t χ) χ) i)
        (inv1F V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t) (vIT t 1) (vIT t 2)
          (accXT V χ αs hgen) (accPT V χ αs hgen) V.computeNodes V.orbitC.ω (chalVQ7T δ V.basis χ)
          (pubCFT δ V (xT t) (reqT t χ) χ) i)
        (inv2F V.basis χ αs (walkT χ αs hgen) V.N (decT χ αs t) serT (axT t) (fIdxT t) (vIT t 1) (vIT t 2)
          (accXT V χ αs hgen) (accPT V χ αs hgen) V.computeNodes V.orbitC.ω (chalVQ7T δ V.basis χ)
          (pubCFT δ V (xT t) (reqT t χ) χ) i)
        (accXT V χ αs hgen i) (accPT V χ αs hgen i) z1Col := rfl
  rw [h]
  exact vclFill_z1 (δ := δ) V.basis _ _ _ _ _ _ _ _ _ _

/-- **The walk row's state is the generator row's** (coin-free). -/
theorem walkT_state (j : ℕ) (hj : j < nRows t) :
    ((walkT χ αs hgen).pubAt j).state = (gRow t j).skel.state := by
  simp only [walkT, honestWalkOf_pubAt, walkRootT]
  rw [genWalk_bfsPubAt _ _ _ _ _ t j hj, ← renderNode_state_agree', renderNode_state]
  rfl

end RowsRound

/-! ## 7. The honest structure and `honest_staged` -/

section Struct
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Compute.LogUp
variable (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  [DecidableEq K] [DecidableEq F] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (hC : ℕ) (S : MemShape)

/-- **The honest datum of the VCL compute family at the tower chip.**

* `V`: the verifier datum; its compute side is the run's (`hN`, `hnodes`), with the size condition `hsize`
  (`N ≤ 2^h`) and the field facts of `V.Checks` (`hp`, `hrowsC`);
* `fuel t hgen`: the generator run at the claim (`genComputeSkeleton … =.ok (t, result)`);
* `αs`: the free generator `α*` of the compute inputs (data);
*  no field has unproved content: the former `hax1` (SHD-A) is gone — an axis-1 read is now served by
  the chip's `z1` column, which the honest trace fills `z1 = [axis = 1]` (`vclFill_z1`).  The former `hacc`
  (the accumulator gates outside `badT`) is a THEOREM (`TowerAccHonest.lean::HonestVCLT.hacc`), from the per-row
  record identities `hrowX_T` / `hrowP_T`. -/
structure HonestVCLT where
  V : VerifierData F K hC S
  fuel : ℕ
  t : NTree (GenComputeRow (Quad (algebraMap F K δ)))
  hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel V.claim.subject V.claim.formula =
    .ok (t, V.claim.result)
  αs : Quad (algebraMap F K δ)
  hN : V.N = nRows t
  hnodes : ∀ i : Fin V.N, V.computeNodes i = V.orbitC.ω ^ (i : ℕ)
  hsize : V.N ≤ 2 ^ hC
  hp : 25 ≤ ringChar F
  hrowsC : 3 * V.N < ringChar K

variable {F K δ hC S}

/-- **`honest_staged`**: every column of the honest trace reads only the coins sampled before its round. -/
theorem honest_staged_T (H : HonestVCLT F K δ hC S) :
    StagedCols frameVCL (tableVCLT hC).colRound (fun χ => traceT H.V χ H.αs H.hgen) := by
  intro j χ χ' hχ
  have hcr' : (tableVCLT hC).colRound j =
      if j.1 < 232 then colRoundVCLE j.1 else if j.1 < 388 then 1 else if j.1 = z1Col then 1 else 2 := rfl
  -- Off the `z1` column the round is the pre-z1 formula
  have hcr : j.1 ≠ z1Col → (tableVCLT hC).colRound j =
      if j.1 < 232 then colRoundVCLE j.1 else if j.1 < 388 then 1 else 2 := fun hz => by
    rw [hcr']; split_ifs <;> simp_all
  have hst : ∀ (χ : Coins frameVCL K) (i : Fin H.V.N),
      ((walkT χ H.αs H.hgen).pubAt i).state = (gRow H.t i).skel.state := fun χ i =>
    walkT_state χ H.αs H.hgen i (by rw [← H.hN]; exact i.isLt)
  have hbase : ∀ i : Fin H.V.N, (rowsT H.V χ H.αs H.hgen i).base = (rowsT H.V χ' H.αs H.hgen i).base := by
    intro i
    rw [rowsT_base, rowsT_base, hst χ i, hst χ' i]
  have hvcl : ∀ (i : Fin H.V.N) j, (202 ≤ j ∧ j < 208) ∨ (220 ≤ j ∧ j < 223) →
      (rowsT H.V χ H.αs H.hgen i).vcl j = (rowsT H.V χ' H.αs H.hgen i).vcl j := by
    intro i j hj
    rw [rowsT_vcl _ _ _ _ i j hj, rowsT_vcl _ _ _ _ i j hj]
  unfold traceT
  by_cases h2 : (tableVCLT hC).colRound j ≤ 1
  · apply honestQT_congr
    funext i
    by_cases hz1 : j.1 = z1Col
    · -- the honest `z1` column is `[axis = 1]`, coin-free
      have e : ∀ χ'' : Coins frameVCL K, (rowsT H.V χ'' H.αs H.hgen i).vcl z1Col =
          if axT H.t i = 1 then 1 else 0 := fun χ'' =>
        -- `vclFill` at `z1Col` depends on the axis only (no `limbAt` window covers `409`)
        rowsT_vcl_z1 H.V χ'' H.αs H.hgen i
      simp only [vclColT, hz1, z1Col, show ¬ (409 < 202) by omega,
        show ¬ ((208 ≤ 409 ∧ 409 < 214) ∨ (232 ≤ 409 ∧ 409 < 394)) by omega, if_false]
      exact (e χ).trans (e χ').symm
    have hcr := hcr hz1
    by_cases h0 : (tableVCLT hC).colRound j = 0
    · have hj232 : j.1 < 232 := by
        by_contra hc; rw [hcr, if_neg hc] at h0; split_ifs at h0
      rw [hcr, if_pos hj232] at h0
      rcases round0_cols j.1 hj232 h0 with h13 | hv
      · simp only [vclColT, show j.1 < 202 by omega, if_true, srcColT, h13, dif_pos, hbase i]
      · have hn1 : ¬ ((208 ≤ j.1 ∧ j.1 < 214) ∨ (232 ≤ j.1 ∧ j.1 < 394)) := by omega
        simp only [vclColT, show ¬ j.1 < 202 by omega, hn1, if_false]
        exact hvcl i j.1 hv
    · have hc1 : ∀ k : Fin frameVCL.n, frameVCL.sampledAfter k = 0 → χ k = χ' k := fun k hk =>
        hχ k (by rw [hk]; omega)
      have e2 := hc1 ⟨2, by decide⟩ rfl
      have e3 := hc1 ⟨3, by decide⟩ rfl
      have e8 := hc1 ⟨8, by decide⟩ rfl
      have e9 := hc1 ⟨9, by decide⟩ rfl
      have e10 := hc1 ⟨10, by decide⟩ rfl
      have hz : zQuad δ χ = zQuad δ χ' := by simp only [zQuad, e2, e3]
      refine vclColT_congr_le1 H.V.basis _ _ i (hbase i) (fun r hr => ?_) (hvcl i) j.1 (by rw [← hcr]; exact h2)
      have a1 := rowsT_ext_lt H.V χ H.αs H.hgen i r.1 hr
      have a2 := rowsT_ext_lt H.V χ' H.αs H.hgen i r.1 hr
      simp only [Fin.eta] at a1 a2
      rw [a1, a2, hz, ιc, ιc, ιc, ιc, ιc, ιc, e8, e9, e10]
  · have : χ = χ' := funext fun k => hχ k (by
      have : frameVCL.sampledAfter k ≤ 1 := by fin_cases k <;> decide
      omega)
    rw [this]

end Struct

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
