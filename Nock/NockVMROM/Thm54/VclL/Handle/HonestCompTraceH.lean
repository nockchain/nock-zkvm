/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestCompTraceH.lean

* §1 the honest column function `compTrace r c` (row `r`, column `c < 70`): the 43 base columns `colVal` of
    the row `rows r`, the nine slot-inverse columns (`fillTrace`, i.e. `A / D`), the two prefix-sum accumulators
    (`accX`, `accP`: exclusive prefix sums of `termVal`), and the four walk columns `ln / cnt / acc / inv`
    (coordinates of the `𝕂` closed forms at BFS index `r + 1`).  Nothing circular: the accumulator and walk
    columns are never read by `termVal`, `A`, `D`.
  * §2 `compPoly`: column `c` interpolates `compTrace · c` at the row nodes; `compPoly_env_trace` /
    `compPoly_env_next`: the chip environment at row node `i` reads `compTrace i` (current) and
    `compTrace (i + 1)` (next, when `i + 1 < n` and the nodes are `ω`-adjacent).
  * §3 `compPoly_binds`: the two preprocessing masks at columns `11 / 12`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCongH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLowerH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified Module
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.Framework Nock.Framework.Reify Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

noncomputable section

section Trace
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]

def fstF (r : ℕ) : F := if r = 0 then 1 else 0
def lstF (N r : ℕ) : F := if r + 1 = N then 1 else 0

/-- The base environment of chip row `r`: the 43 base columns of `rows r` (current) and `rows (r + 1)` (next). -/
def baseEnvC (cells : List Noun) (rows : ℕ → RowN) (N : ℕ) (chalV pubVal : ℕ → F) (r : ℕ) : Env F :=
  ⟨colVal cells (rows r) (fstF r) (lstF N r), colVal cells (rows (r + 1)) (fstF (r + 1)) (lstF N (r + 1)),
    chalV, pubVal⟩

/-- The row environment with the nine slot-inverse columns at the honest fill. -/
def fillEnvC (b : Basis (Fin 3) F K) (cells : List Noun) (rows : ℕ → RowN) (N : ℕ) (chalV pubVal : ℕ → F)
    (r : ℕ) : Env F :=
  fillEnv b (baseEnvC cells rows N chalV pubVal r)

open Classical in
/-- Exclusive prefix sum of the export per-row terms, in closed form `Σ 1/recDen` over the row's export
entries at the compute coins `limbVal b chalV` (the value `termVal` takes at the honest fill, by
`termValX_honest`; defined directly so that the trace is not circular). -/
def accSumX (b : Basis (Fin 3) F K) (cells : List Noun) (rows : ℕ → RowN) (chalV : ℕ → F) (r : ℕ) : K :=
  ∑ j ∈ Finset.range r, ((exportEntries (rows j)).map fun x =>
    (recDen (limbVal b chalV chalRhoL) (limbVal b chalV chalGammaL) (entryRec (F := F) cells x))⁻¹).sum

open Classical in
def accSumP (b : Basis (Fin 3) F K) (cells : List Noun) (rows : ℕ → RowN) (chalV : ℕ → F) (r : ℕ) : K :=
  ∑ j ∈ Finset.range r, ((consEntries (hn (rows j))).map fun x =>
    (recDenP (limbVal b chalV chalRhoL) (limbVal b chalV chalGammaL) (entRecP (F := F) cells x))⁻¹).sum

/-- **The honest compute column function** (row `r`, column `c`; `0` for `c ≥ 70`). -/
def compTrace (b : Basis (Fin 3) F K) (cells : List Noun) (rows : ℕ → RowN) (N : ℕ) (chalV pubVal : ℕ → F)
    (ln cnt acc : ℕ → K) (r c : ℕ) : F :=
  if c < 52 then fillTrace b (baseEnvC cells rows N chalV pubVal r) c
  else if c < 55 then coordNA b (accSumX b cells rows chalV r) (c - 52)
  else if c < 58 then coordNA b (accSumP b cells rows chalV r) (c - 55)
  else if c < 61 then coordNA b (ln (r + 1)) (c - 58)
  else if c < 64 then coordNA b (cnt (r + 1)) (c - 61)
  else if c < 67 then coordNA b (acc (r + 1)) (c - 64)
  else if c < 70 then coordNA b ((cnt (r + 1) - ln (r + 1))⁻¹) (c - 67)
  else 0

variable (b : Basis (Fin 3) F K) (cells : List Noun) (rows : ℕ → RowN) (N : ℕ) (chalV pubVal : ℕ → F)
  (ln cnt acc : ℕ → K)

theorem compTrace_base (r c : ℕ) (hc : c < 43) :
    compTrace b cells rows N chalV pubVal ln cnt acc r c = colVal cells (rows r) (fstF r) (lstF N r) c := by
  unfold compTrace
  rw [if_pos (by omega)]
  unfold fillTrace
  erw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rfl

theorem compTrace_fill (r c : ℕ) (hc : c < 52) :
    compTrace b cells rows N chalV pubVal ln cnt acc r c = fillTrace b (baseEnvC cells rows N chalV pubVal r) c := by
  unfold compTrace; rw [if_pos hc]

/-- The generic limb read-back. -/
theorem limbVal_comp (r c0 : ℕ) (x : K)
    (h : ∀ k : Fin 3, compTrace b cells rows N chalV pubVal ln cnt acc r (c0 + k) = coordNA b x k) :
    limbVal b (compTrace b cells rows N chalV pubVal ln cnt acc r) c0 = x := by
  refine limbVal_eq_of_coords b x _ c0 fun k => ?_
  rw [h k]; simp [coordNA, k.isLt]

theorem limb_accX (r : ℕ) :
    limbVal b (compTrace b cells rows N chalV pubVal ln cnt acc r) accX = accSumX b cells rows chalV r := by
  refine limbVal_comp b cells rows N chalV pubVal ln cnt acc r accX _ fun k => ?_
  have := k.isLt
  simp only [compTrace, accX]
  erw [if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limb_accP (r : ℕ) :
    limbVal b (compTrace b cells rows N chalV pubVal ln cnt acc r) accP = accSumP b cells rows chalV r := by
  refine limbVal_comp b cells rows N chalV pubVal ln cnt acc r accP _ fun k => ?_
  have := k.isLt
  simp only [compTrace, accP]
  erw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limb_ln (r : ℕ) :
    limbVal b (compTrace b cells rows N chalV pubVal ln cnt acc r) wLn = ln (r + 1) := by
  refine limbVal_comp b cells rows N chalV pubVal ln cnt acc r wLn _ fun k => ?_
  have := k.isLt
  simp only [compTrace, wLn]
  erw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limb_cnt (r : ℕ) :
    limbVal b (compTrace b cells rows N chalV pubVal ln cnt acc r) wCnt = cnt (r + 1) := by
  refine limbVal_comp b cells rows N chalV pubVal ln cnt acc r wCnt _ fun k => ?_
  have := k.isLt
  simp only [compTrace, wCnt]
  erw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limb_acc (r : ℕ) :
    limbVal b (compTrace b cells rows N chalV pubVal ln cnt acc r) wAcc = acc (r + 1) := by
  refine limbVal_comp b cells rows N chalV pubVal ln cnt acc r wAcc _ fun k => ?_
  have := k.isLt
  simp only [compTrace, wAcc]
  erw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  congr 1; omega

theorem limb_inv (r : ℕ) :
    limbVal b (compTrace b cells rows N chalV pubVal ln cnt acc r) wInv = (cnt (r + 1) - ln (r + 1))⁻¹ := by
  refine limbVal_comp b cells rows N chalV pubVal ln cnt acc r wInv _ fun k => ?_
  have := k.isLt
  simp only [compTrace, wInv]
  erw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]
  congr 1; omega


theorem compTrace_zero (r c : ℕ) (hc : 70 ≤ c) :
    compTrace b cells rows N chalV pubVal ln cnt acc r c = 0 := by
  unfold compTrace
  erw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

section Poly
variable {n : ℕ} (nodes : Fin n → F)

/-- **The honest compute trace polynomials**: column `c` interpolates `compTrace · c` at the row nodes
(row `i` of the chip is the `i`-th node; `N = n`). -/
def compPoly (w : ℕ) : Fin w → F[X] := fun c =>
  Lagrange.interpolate Finset.univ nodes (fun i : Fin n =>
    compTrace b cells rows N chalV pubVal ln cnt acc (i : ℕ) (c : ℕ))

theorem compPoly_eval (hinj : Function.Injective nodes) {w : ℕ} (c : Fin w) (i : Fin n) :
    (compPoly b cells rows N chalV pubVal ln cnt acc nodes w c).eval (nodes i) =
      compTrace b cells rows N chalV pubVal ln cnt acc (i : ℕ) (c : ℕ) :=
  Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

theorem compPoly_env_trace (hinj : Function.Injective nodes) {w : ℕ} (hw : 70 ≤ w) (ω : F) (i : Fin n)
    (c : ℕ) :
    (Reify.envOfTrace (compPoly b cells rows N chalV pubVal ln cnt acc nodes w) ω (nodes i) chalV pubVal).trace c
      = compTrace b cells rows N chalV pubVal ln cnt acc (i : ℕ) c := by
  simp only [Reify.envOfTrace]
  by_cases hc : c < w
  · rw [dif_pos hc]; exact compPoly_eval b cells rows N chalV pubVal ln cnt acc nodes hinj ⟨c, hc⟩ i
  · rw [dif_neg hc, compTrace_zero b cells rows N chalV pubVal ln cnt acc _ _ (by omega)]

theorem compPoly_env_next (hinj : Function.Injective nodes) {w : ℕ} (hw : 70 ≤ w) (ω : F) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hadj : nodes ⟨(i : ℕ) + 1, hi⟩ = ω * nodes i) (c : ℕ) :
    (Reify.envOfTrace (compPoly b cells rows N chalV pubVal ln cnt acc nodes w) ω (nodes i) chalV pubVal).traceNext c
      = compTrace b cells rows N chalV pubVal ln cnt acc ((i : ℕ) + 1) c := by
  simp only [Reify.envOfTrace]
  by_cases hc : c < w
  · rw [dif_pos hc, ← hadj]
    exact compPoly_eval b cells rows N chalV pubVal ln cnt acc nodes hinj ⟨c, hc⟩ ⟨(i : ℕ) + 1, hi⟩
  · rw [dif_neg hc, compTrace_zero b cells rows N chalV pubVal ln cnt acc _ _ (by omega)]

theorem compPoly_first (w : ℕ) (hw : 11 < w) :
    compPoly b cells rows N chalV pubVal ln cnt acc nodes w ⟨11, hw⟩ = firstRowMask nodes := by
  unfold compPoly firstRowMask
  congr 1

theorem compPoly_last (hn : 0 < n) (hN : N = n) (w : ℕ) (hw : 12 < w) :
    compPoly b cells rows N chalV pubVal ln cnt acc nodes w ⟨12, hw⟩ = lastRowMask hn nodes := by
  unfold compPoly lastRowMask
  congr 1
  funext i
  show compTrace b cells rows N chalV pubVal ln cnt acc (i : ℕ) 12 = _
  rw [compTrace_base b cells rows N chalV pubVal ln cnt acc _ 12 (by omega)]
  have : (i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩) ↔ (i : ℕ) + 1 = n := by
    constructor
    · intro h; subst h; simp; omega
    · intro h; apply Fin.ext; simp; omega
  simp only [colVal, lstF, hN]
  simp only [show ¬ (12 ≤ 10) from by omega, if_false]
  simp only [this]

end Poly

end Trace

end

end Nock.NockVMROM.Thm54.VclL.Handle
