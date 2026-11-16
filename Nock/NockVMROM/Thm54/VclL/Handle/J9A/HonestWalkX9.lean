/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/HonestWalkX9.lean

* `walkGatesX9_hold` — the nine `𝕂` gates of `walkGatesX9` vanish on a row whose columns are a
    `Walk.WalkSat` walk and whose label reads (`curLX`, `ccLX9`, `cmLX9`) are the walk's (`RowReadsX9`).
  * `rowAt9`, `fl1`, `llW`, `walkEnvF9` — the honest J-9 A row at BFS index `j` (`colX9`, first / last flags).
  * `ReadsAt9` — **the read hypothesis**: at every BFS row `1 ≤ j ≤ |W|`, the three label reads of the twin's
    walk gate, evaluated at the honest columns `colX9` of row `j`, are the tree's walk values (`curCol`, the
    child sum over `chldCol`, `α ^ foCol`) for a node value `nodeV`.  This is the J-9 A twin of J-8's
    `reads_atX` (proved there from the generator's child link); here it is a HYPOTHESIS, discharged by the
    lead from the J-9 A child link.
  * **`walkGatesX9_honest`** — every walk gate at every BFS row `1 ≤ i ≤ |W|`, at the closed-form walk
    (`lnClosed`, `cntClosed`, `accClosed` over `foCol W`), under `ReadsAt9` and `|W| ≤ orderOf α`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ACompRow
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTraceX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.HonestWalkX9

open Nock Nock.Reified Module Nock.Walk Nock.Framework
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle (evalQ_notC evalQ_cc evalMQ evalQ)
open Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (chalAlphaW chalGammaW pubIC pubSeed pubOut cc notC wv kv sumM)
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX (walkEnvKX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 tNode)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9 colS0B colS10B colS10S)

noncomputable section

/-! ## 1. The nine walk gates on a `WalkSat` row -/

section Gates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **What a row of the twin walk reads** (the current row's label, child sum and count multiplier; the next
row's, when there is one), at the 20-state sums `ccLX9` / `cmLX9`. -/
structure RowReadsX9 (eK : Env K) (eF : Env F) (cur ccC cmC : K) (hasNext : Prop) (curN ccN cmN : K) :
    Prop where
  curC : evalMQ (curLX (F := ℚ) .traceCur) eK eF = cur
  ccC : evalMQ (ccLX9 (F := ℚ) .traceCur) eK eF = ccC
  cmC : evalMQ (cmLX9 (F := ℚ) .traceCur) eK eF = cmC
  nxt : hasNext → evalMQ (curLX (F := ℚ) .traceNext) eK eF = curN ∧
    evalMQ (ccLX9 (F := ℚ) .traceNext) eK eF = ccN ∧ evalMQ (cmLX9 (F := ℚ) .traceNext) eK eF = cmN

/-- **The nine walk gates of `computeChipVCLHX9` vanish on a row whose columns are a `WalkSat` walk**
(row `i`, `1`-based, of `h`; the twin of `HonestWalkX.walkGatesX_hold`). -/
theorem walkGatesX9_hold {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln cnt acc : ℕ → K}
    {α seed : K} {h : ℕ}
    (hw : Walk.WalkSat cur chld' fo ln cnt acc α seed α h)
    (eK : Env K) (eF : Env F) (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ h)
    (hα : eK.chal chalAlphaW = α) (hIC : eK.pub pubIC = α) (hseed : eK.pub pubSeed = seed)
    (hlnC : eK.trace wLnX = ln i) (hlnN : eK.traceNext wLnX = ln (i + 1))
    (hcnC : eK.trace wCntX = cnt i) (hcnN : eK.traceNext wCntX = cnt (i + 1))
    (hacC : eK.trace wAccX = acc i) (hacN : eK.traceNext wAccX = acc (i + 1))
    (hinv : i < h → eK.trace wInvX * (cnt i - ln i) = 1)
    (hfirst : eF.trace firstX = if i = 1 then 1 else 0)
    (hlast : eF.trace lastX = if i = h then 1 else 0)
    (hout : eK.pub pubOut = acc h) (hcntlast : cnt h = ln h)
    (hrd : RowReadsX9 eK eF (cur i) (∑ l ∈ Finset.Icc 1 (fo i), α ^ l * chld' i l) (α ^ fo i)
      (i < h) (cur (i + 1)) (∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * chld' (i + 1) l)
      (α ^ fo (i + 1))) :
    ∀ g ∈ (walkGatesX9 : List (MixedExpr ℚ)), evalMQ g eK eF = 0 := by
  intro g hg
  have hnl : algebraMap F K (evalQ (notC (F := ℚ) lastX) eF) = if i = h then 0 else 1 := by
    simp only [evalQ_notC, hlast]; split <;> simp
  have hfl : algebraMap F K (evalQ (cc (F := ℚ) firstX) eF) = if i = 1 then 1 else 0 := by
    simp only [evalQ_cc, hfirst]; split <;> simp
  have hll : algebraMap F K (evalQ (cc (F := ℚ) lastX) eF) = if i = h then 1 else 0 := by
    simp only [evalQ_cc, hlast]; split <;> simp
  simp only [walkGatesX9, List.mem_cons, List.not_mem_nil, or_false] at hg
  have ev : ∀ (a : CoeffExpr ℚ) (u : MixedExpr ℚ), evalMQ (.Scale a u) eK eF =
      algebraMap F K (evalQ a eF) * evalMQ u eK eF := fun a u => rfl
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ev, hnl]
    by_cases hih' : i = h
    · simp [hih']
    · have := hw.lnInc i hi1 (by omega)
      simp [evalMQ, wv, hih', hα, hlnC, hlnN, this]
  · rw [ev, hnl]
    by_cases hih' : i = h
    · simp [hih']
    · have := hw.countInc i hi1 (by omega)
      simp [evalMQ, wv, hih', hcnC, hcnN, (hrd.nxt (by omega)).2.2, this]
  · rw [ev, hnl]
    by_cases hih' : i = h
    · simp [hih']
    · have := hw.accStep i hi1 (by omega)
      have hs : cnt i * ∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * chld' (i + 1) l =
          ∑ l ∈ Finset.Icc 1 (fo (i + 1)), α ^ l * cnt i * chld' (i + 1) l := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
      simp only [evalMQ, wv, hih', if_false, one_mul, hlnN, hacN, hacC, hcnC,
        (hrd.nxt (by omega)).1, (hrd.nxt (by omega)).2.1]
      rw [hs]; linear_combination this
  · rw [ev, hfl]
    by_cases hi' : i = 1
    · subst hi'; simp [evalMQ, wv, hα, hlnC, hw.ln1]
    · simp [hi']
  · rw [ev, hfl]
    by_cases hi' : i = 1
    · subst hi'; simp [evalMQ, wv, hIC, hcnC, hrd.cmC, hw.count1]
    · simp [hi']
  · rw [ev, hfl]
    by_cases hi' : i = 1
    · subst hi'
      have := hw.accInit
      have hs : α * ∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * chld' 1 l =
          ∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * α * chld' 1 l := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
      simp only [evalMQ, wv, if_true, one_mul, hlnC, hacC, hIC, hseed, hrd.curC, hrd.ccC]
      rw [hs]; linear_combination this
    · simp [hi']
  · rw [ev, hnl]
    by_cases hih' : i = h
    · simp [hih']
    · have := hinv (by omega)
      simp [evalMQ, wv, hih', hcnC, hlnC, this]
  · rw [ev, hll]
    by_cases hih' : i = h
    · subst hih'; simp [evalMQ, wv, hcnC, hlnC, hcntlast]
    · simp [hih']
  · rw [ev, hll]
    by_cases hih' : i = h
    · subst hih'; simp [evalMQ, wv, hacC, hout]
    · simp [hih']

end Gates

/-! ## 2. The honest J-9 A rows and the read hypothesis -/

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

/-- A dummy row past the end (a closing `s10T` row at `atom 0`). -/
def rowDflt9 : LX9 := (tNode (.atom 0) (.atom 0)).label

/-- **The honest J-9 A row at BFS index `j`** (`1`-based; the dummy past the end). -/
def rowAt9 (W : List (NTree LX9)) (j : ℕ) : LX9 := ((W[j - 1]?).map NTree.label).getD rowDflt9

/-- The first-row flag of BFS row `j`. -/
def fl1 (j : ℕ) : F := if j = 1 then 1 else 0
/-- The last-row flag of BFS row `j`. -/
def llW (W : List (NTree LX9)) (j : ℕ) : F := if j = W.length then 1 else 0

/-- The honest base environment of BFS row `i` for the walk gates: `colX9` of rows `i` and `i + 1`. -/
def walkEnvF9 (W : List (NTree LX9)) (i : ℕ) : Env F :=
  ⟨colX9 H pd idOf (rowAt9 W i) (fl1 i) (llW W i),
    colX9 H pd idOf (rowAt9 W (i + 1)) (fl1 (i + 1)) (llW W (i + 1)), fun _ => 0, fun _ => 0⟩

/-- **The read hypothesis** (twin of J-8's `reads_atX`): at every BFS row `1 ≤ j ≤ |W|`, the three label reads
of the twin walk gate, at the honest columns of row `j` (current or next environment), are the tree's walk values
for the node value `nodeV`. -/
def ReadsAt9 (W : List (NTree LX9)) (nodeV : NTree LX9 → K) (α γ : K) : Prop :=
  ∀ j, 1 ≤ j → j ≤ W.length → ∀ (kind : VarKind) (eK : Env K) (eF : Env F),
    eK.chal chalAlphaW = α → eK.chal chalGammaW = γ →
    (∀ i, evalQ (.var kind i : CoeffExpr ℚ) eF = colX9 H pd idOf (rowAt9 W j) (fl1 j) (llW W j) i) →
    evalMQ (curLX (F := ℚ) kind) eK eF = Walk.curCol nodeV W j ∧
      evalMQ (ccLX9 (F := ℚ) kind) eK eF =
        ∑ l ∈ Finset.Icc 1 (Walk.foCol W j), α ^ l * Walk.chldCol nodeV W j l ∧
      evalMQ (cmLX9 (F := ℚ) kind) eK eF = α ^ (Walk.foCol W j)

theorem colX9_17 (l : LX9) (fst lst : F) : colX9 H pd idOf l fst lst 17 = fst := by
  rcases l with ⟨row, chip, n, m, rn⟩
  cases chip <;> simp [colX9, colX, colS0B, colS10B, colS10S]

theorem colX9_18 (l : LX9) (fst lst : F) : colX9 H pd idOf l fst lst 18 = lst := by
  rcases l with ⟨row, chip, n, m, rn⟩
  cases chip <;> simp [colX9, colX, colS0B, colS10B, colS10S]

end Rows

/-! ## 3. The walk gates at every honest BFS row -/

section Tree
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {H : Noun → ℕ × ℕ} {pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)} {idOf : ℕ → ℕ}

/-- **The nine walk gates of `computeChipVCLHX9` hold at every honest BFS row** of a J-9 A tree
(`1 ≤ i ≤ |W|`, `W = bfsForest [t9]`), at the closed-form walk over `foCol W`, under the read hypothesis
`ReadsAt9` and `|W| ≤ orderOf α` (the walk coin's honest bad condition). -/
theorem walkGatesX9_honest (t9 : NTree LX9) (nodeV : NTree LX9 → K) (α γ : K)
    (hord : (bfsForest [t9]).length ≤ orderOf α)
    (hrd : ReadsAt9 (F := F) H pd idOf (bfsForest [t9]) nodeV α γ)
    (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ (bfsForest [t9]).length) :
    let W := bfsForest [t9]
    let cur := Walk.curCol nodeV W
    let seed := cur 1 * α
    let ln := lnClosed α
    let cnt := cntClosed (Walk.foCol W) α α
    let acc := accClosed cur (Walk.chldCol nodeV W) (Walk.foCol W) α seed α
    ∀ g ∈ (walkGatesX9 : List (MixedExpr ℚ)),
      evalMQ g (walkEnvKX ln cnt acc α γ seed i) (walkEnvF9 (F := F) H pd idOf W i) = 0 := by
  intro W cur seed ln cnt acc
  have hpos : 1 ≤ W.length := by
    show 1 ≤ (Walk.bfsForest [t9]).length
    rw [Walk.walk_tail_eq t9]; simp
  have hw := walkSat_closed cur (Walk.chldCol nodeV W) (Walk.foCol W) α seed α hpos
  have hseed : seed = cur 1 * α := rfl
  have hacc : acc W.length = 0 :=
    Walk.walk_completeness hw hseed rfl (Walk.bfs_isFullBFT (nodeVal := nodeV) t9)
  have hv : Walk.BFSValidF 1 (Walk.foCol W) W.length :=
    Walk.foCol_BFSValidF [t9] (List.cons_ne_nil _ _)
  have ht : 1 + Walk.Sf (Walk.foCol W) W.length = W.length :=
    Walk.foCol_Sf_tilingF [t9] (List.cons_ne_nil _ _)
  have hlnc : ∀ k, 1 ≤ k → k ≤ W.length → ln k = α ^ k := fun k h1 h2 => Walk.ln_closed hw k h1 h2
  have hcnc : ∀ k, 1 ≤ k → k ≤ W.length → cnt k = α * α ^ Walk.Sf (Walk.foCol W) k :=
    fun k h1 h2 => Walk.count_closed hw k h1 h2
  have hcntlast : cnt W.length = ln W.length := by
    rw [hcnc _ hpos le_rfl, hlnc _ hpos le_rfl, ← pow_succ']
    exact congrArg (fun e => α ^ e) (by omega)
  have hne : ∀ j, 1 ≤ j → j < W.length → cnt j ≠ ln j := by
    intro j hj1 hj
    have hneq := (Nock.RedTeam.Batch478.honest_ratio_gate (K := K) hv ht hord).1 j hj1 hj
    rw [hcnc j hj1 hj.le, hlnc j hj1 hj.le, ← pow_succ', Nat.add_comm]
    exact hneq
  have hrd1 := hrd i hi1 hih .traceCur
    (walkEnvKX ln cnt acc α γ seed i) (walkEnvF9 (F := F) H pd idOf W i)
    (by simp [walkEnvKX, chalAlphaW, chalGammaW]) (by simp [walkEnvKX, chalAlphaW, chalGammaW])
    (fun j => rfl)
  refine walkGatesX9_hold hw (walkEnvKX ln cnt acc α γ seed i) (walkEnvF9 (F := F) H pd idOf W i) i hi1 hih
    (by simp [walkEnvKX, chalAlphaW]) (by simp [walkEnvKX, pubIC])
    (by simp [walkEnvKX, pubSeed, pubIC])
    (by simp [walkEnvKX, wLnX] <;> rfl) (by simp [walkEnvKX, wLnX] <;> rfl)
    (by simp [walkEnvKX, wLnX, wCntX] <;> rfl) (by simp [walkEnvKX, wLnX, wCntX] <;> rfl)
    (by simp [walkEnvKX, wLnX, wCntX, wAccX] <;> rfl) (by simp [walkEnvKX, wLnX, wCntX, wAccX] <;> rfl)
    ?_ ?_ ?_
    (by simp [walkEnvKX, pubOut, pubIC, pubSeed] <;> exact hacc.symm) hcntlast ?_
  · intro hlt
    simp only [walkEnvKX, wLnX, wCntX, wAccX, wInvX]
    simp only [show (120 : ℕ) ≠ 111 by decide, show (120 : ℕ) ≠ 114 by decide,
      show (120 : ℕ) ≠ 117 by decide, if_false, if_true]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne i hi1 hlt))
  · show colX9 H pd idOf (rowAt9 W i) (fl1 i) (llW W i) 17 = _
    rw [colX9_17]; rfl
  · show colX9 H pd idOf (rowAt9 W i) (fl1 i) (llW W i) 18 = _
    rw [colX9_18]; rfl
  · refine ⟨hrd1.1, hrd1.2.1, hrd1.2.2, fun hlt => ?_⟩
    exact hrd (i + 1) (by omega) hlt .traceNext
      (walkEnvKX ln cnt acc α γ seed i) (walkEnvF9 (F := F) H pd idOf W i)
      (by simp [walkEnvKX, chalAlphaW, chalGammaW]) (by simp [walkEnvKX, chalAlphaW, chalGammaW])
      (fun j => rfl)

end Tree

end

end Nock.NockVMROM.Thm54.VclL.HonestWalkX9

section Axioms
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9
#print axioms walkGatesX9_hold
#print axioms colX9_17
#print axioms colX9_18
#print axioms walkGatesX9_honest
end Axioms
