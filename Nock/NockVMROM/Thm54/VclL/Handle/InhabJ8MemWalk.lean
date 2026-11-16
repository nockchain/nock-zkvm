/-
  Nock/NockVMROM/Thm54/VclL/Handle/InhabJ8MemWalk.lean

  **The honest J-8 walk of THE inhabitant.**  New module, additive.

  One row, `kroots = 1`: a root
  (`pre = 1`, `len = 0`, `ridx = idx = 0`), no walked child (`cL = cR = 0`), path-read multiplicities `mL mR`
  PARAMETERS (honest `0`).

  * `wrow`, `walkBase0`, `walkK0`, `walkMixed0`, **`walkOk0`**: the `ok`-gated original walk chip accepts.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCellKW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemWalk

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemCell
open Nock.ComputeTable (FP)

noncomputable section

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

def wbit (k : ℕ) : F := if k = 1 then 0 else if k < 6 then 1 else 0

/-- **The one walk row**: the dummy root `s0` (cell serial `0`); fingerprints `p l r` those of cell row `0`. -/
def wrow (α : K) (z : 𝕂′) (mL mR : ℕ) : WalkVals F K 𝕂′ where
  idx := ((0 : ℕ) : F)
  pre := 1
  ridx := ((0 : ℕ) : F)
  len := 0
  cL := 0
  cR := 0
  e := 0
  mL := (mL : F)
  mR := (mR : F)
  q := 0
  qinv := 0
  u := 0
  bit := wbit
  p := FP.cons z (FP.atomFP z (liftQ δF 0)) (FP.atomFP z (liftQ δF (aRv 0)))
  l := FP.atomFP z (liftQ δF 0)
  r := FP.atomFP z (liftQ δF (aRv 0))
  root := FP.cons z (FP.atomFP z (liftQ δF 0)) (FP.atomFP z (liftQ δF (aRv 0)))
  ln := α
  cnt := α
  acc := 0
  xInv := 0
  pInvL := 0
  pInvR := 0
  xAcc := 0
  pAcc := 0

theorem walkBase0 (α : K) (z : 𝕂′) (mL mR : ℕ) (i : Fin 1) :
    WalkBaseFacts 1 (fun _ : Fin 1 => wrow δF α z mL mR) i := by
  have hi : (i : ℕ) = 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun h => ?_,
    fun h => ?_, fun _ => ?_, fun k _ => ?_⟩
  · simp [wrow]
  · simp [wrow]
  · simp [wrow]
  · simp [wrow, wbit]
  · simp [wrow, wbit]
  · simp [wrow, wbit, Finset.sum_range_succ]; norm_num
  · simp [wrow]
  · simp [wrow]
  · simp [wrow]
  · simp [wrow]
  · omega
  · omega
  · simp [wrow]
  · simp only [wrow, wbit]; split_ifs <;> simp

end Rows

section Acc
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

theorem walkK0 (α γK : K) (z : 𝕂′) (mL mR : ℕ) (i : Fin 1) :
    WalkKFacts δF 1 (fun _ : Fin 1 => wrow δF α z mL mR) α γK i := by
  have hfo : WalkVCL.fanout (lblV δF (wrow δF α z mL mR)).1 = 0 := by
    simp [lblV, wrow, WalkVCL.fanout]
  refine ⟨fun _ => rfl, fun hi => absurd hi (by omega), fun _ => ?_, fun hi => absurd hi (by omega),
    fun _ => ?_, fun hi => absurd hi (by omega), fun _ => rfl⟩
  · show α = α ^ 1 * α ^ WalkVCL.fanout (lblV δF (wrow δF α z mL mR)).1
    rw [hfo]; simp
  · show (0 : K) = α ^ 1 * ccV δF α γK (wrow δF α z mL mR)
    simp [ccV, hfo]

/-- The walk's fingerprint-import terminal (one row). -/
def wxTot (γ ρ : 𝕂′) (α : K) (z : 𝕂′) (mL mR : ℕ) : 𝕂′ :=
  (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wrow δF α z mL mR)))⁻¹

/-- The walk's path-provide terminal (one row): `mL / den(recL) + mR / den(recR)`. -/
def wpTot (γ ρ : 𝕂′) (α : K) (z : 𝕂′) (mL mR : ℕ) : 𝕂′ :=
  liftQ δF (mL : F) * (FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wrow δF α z mL mR)))⁻¹ +
    liftQ δF (mR : F) * (FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wrow δF α z mL mR)))⁻¹

theorem walkMixed0 (γ ρ : 𝕂′) (α : K) (z : 𝕂′) (mL mR : ℕ) (pubs : ℕ → K)
    (hx : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wrow δF α z mL mR)) ≠ 0)
    (hL : FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wrow δF α z mL mR)) ≠ 0)
    (hR : FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wrow δF α z mL mR)) ≠ 0)
    (hXt : wxTot δF γ ρ α z mL mR = Quad.mk _ (pubs 0) (pubs 1))
    (hPt : wpTot δF γ ρ α z mL mR = Quad.mk _ (pubs 2) (pubs 3)) (i : Fin 1) :
    WalkMixedFacts δF 1 pubs (fun j : Fin 1 => walkFill δF γ ρ (fun _ => wrow δF α z mL mR) j) γ ρ i :=
  walkFill_mixed δF γ ρ (fun _ => wrow δF α z mL mR) 1 pubs i (fun _ _ _ => rfl) (fun _ _ => hx)
    (fun _ _ => hL) (fun _ _ => hR) (by rw [← hXt]; simp [wxTot, walkFillInv])
    (by rw [← hPt]; simp [wpTot, wpTermV, walkFillInv]; rfl)

/-- The filled walk rows. -/
abbrev wvals (γ ρ : 𝕂′) (α : K) (z : 𝕂′) (mL mR : ℕ) : Fin 1 → WalkVals F K 𝕂′ :=
  fun j => walkFill δF γ ρ (fun _ => wrow δF α z mL mR) j

/-- **The `ok`-gated original walk chip accepts the honest one-row trace.** -/
theorem walkOk0 (b : Basis (Fin 3) F K) {h : ℕ} (hn : 0 < 1) (nodes : Fin 1 → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (hF : GeneratedField.PrimeFieldElems F)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin 1) (hi : (i : ℕ) + 1 < 1), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ z : 𝕂′) (mL mR : ℕ) (hok : ChalsOK δF chals γ ρ 11)
    (hx : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wrow δF (chals 0) z mL mR)) ≠ 0)
    (hL : FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wrow δF (chals 0) z mL mR)) ≠ 0)
    (hR : FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wrow δF (chals 0) z mL mR)) ≠ 0)
    (hXt : wxTot δF γ ρ (chals 0) z mL mR = Quad.mk _ (pubs 0) (pubs 1))
    (hPt : wpTot δF γ ρ (chals 0) z mL mR = Quad.mk _ (pubs 2) (pubs 3)) :
    RAP.SatisfiesWithPreprocessing (walkChipOk δF 1 b hn nodes orbit chals pubs true)
      (fun j => honestQ hn nodes (walkCol δF b 1 (wvals δF γ ρ (chals 0) z mL mR)) 132
        (Fin.cast (walkChipOk_w δF 1 b hn nodes orbit chals pubs true) j)) :=
  walkOk_sat δF 1 b hn nodes orbit chals pubs (wvals δF γ ρ (chals 0) z mL mR) hF hinj hadj γ ρ hok
    (fun i => walkBaseFacts_fill δF γ ρ _ 1 i (walkBase0 δF (chals 0) z mL mR i))
    (fun i => walkKFacts_fill δF γ ρ _ 1 (chals 0) (chals 1) i (walkK0 δF (chals 0) (chals 1) z mL mR i))
    (fun i => walkMixed0 δF γ ρ (chals 0) z mL mR pubs hx hL hR hXt hPt i)

end Acc

/-! ## The `𝕂′` handle denominators in closed form and the J-8 walk acceptance -/

section HQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [FiniteDimensional F K] [DecidableEq F]
  [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **A `𝕂′` key denominator in closed form**: `ρH′ + Σ_c γH′^c · v_c = compress (γH′, ρH′) (lift v)`. -/
theorem denKeyQ_closed (eK : Env K) (eF : Env F) (l : List (CoeffExpr F)) (v : ℕ → F)
    (hv : ∀ c < l.length, (l.getD c (.const 0)).eval eF = v c) :
    (HQ.denKeyQ δF l).ev δF eK eF = FiniteIO.compress (hcoins δF eK.chal)
      (BalanceQ.liftRec (K := K) (L := 𝕂′) fun c : Fin l.length => algebraMap F K (v c)) := by
  simp only [HQ.denKeyQ, ev_add, HQ.rhoQ, ev_chal, TeleHQ.rlcQ_ev, zero_add, FiniteIO.compress, Walk.rlc,
    BalanceQ.liftRec]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun c => (Quad.mk _ (eK.chal 33) (eK.chal 35)) ^ c *
    algebraMap K 𝕂′ (algebraMap F K (v c))) l.length]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [hv c (Finset.mem_range.mp hc)]

/-- The closed-form handle denominator of a key vector `v` (length `m`). -/
def hden (chals : ℕ → K) (m : ℕ) (v : ℕ → F) : 𝕂′ :=
  FiniteIO.compress (hcoins δF chals) (BalanceQ.liftRec (K := K) (L := 𝕂′) fun c : Fin m => algebraMap F K (v c))

variable (b : Basis (Fin 3) F K) {h : ℕ} (hn : 0 < 1) (nodes : Fin 1 → F) (orbit : StrictOrbitDomain F 3 h)

theorem E_low (chals pubs : ℕ → K) (hinj : Function.Injective nodes) (V : Fin 1 → WalkVals F K 𝕂′)
    (R : WalkTraceH.Roles 1 𝕂′) (i : Fin 1) (j : ℕ) (h2 : 2 ≤ j) (hj : j < 21) :
    (WalkTraceHQ.E δF 1 b hn nodes orbit chals pubs (walkCol δF b 1 V) 0 0 0 0 R i).trace j =
      (V i).base 1 i j := by
  unfold WalkTraceHQ.E
  rw [env_trace hn nodes hinj _ _ _ _ i (show j < (walkTemplateHQ δF 1).width 3 by
    rw [WalkTraceHQ.walkTemplateHQ_width]; omega)]
  simp [fullCol, show j ≠ 0 by omega, show j ≠ 1 by omega, WalkTraceHQ.colHQ, extColF, hj, walkCol]

theorem E_kv (chals pubs : ℕ → K) (hinj : Function.Injective nodes) (V : Fin 1 → WalkVals F K 𝕂′)
    (R : WalkTraceH.Roles 1 𝕂′) (i : Fin 1) (j : ℕ) (h2 : 21 ≤ j) (hj : j < 25) :
    (WalkTraceHQ.E δF 1 b hn nodes orbit chals pubs (walkCol δF b 1 V) 0 0 0 0 R i).trace j = 0 := by
  unfold WalkTraceHQ.E
  rw [env_trace hn nodes hinj _ _ _ _ i (show j < (walkTemplateHQ δF 1).width 3 by
    rw [WalkTraceHQ.walkTemplateHQ_width]; omega)]
  simp only [fullCol, show j ≠ 0 by omega, show j ≠ 1 by omega, if_false, WalkTraceHQ.colHQ, extColF,
    show ¬ j < 21 by omega, hj, if_true, WalkTraceHQ.new]
  split_ifs <;> first | rfl | omega

/-- The three walk handle keys of the dummy root: import `(0,0,0,0,0)`, provides `(0,2,0,0)`, `(0,3,0,0)`. -/
def vX (_ : ℕ) : F := 0
def vPL (c : ℕ) : F := if c = 1 then 2 else 0
def vPR (c : ℕ) : F := if c = 1 then 3 else 0

theorem dRow0 (chals pubs : ℕ → K) (hinj : Function.Injective nodes) (γ ρ z : 𝕂′) (mL mR : ℕ) (i : Fin 1) :
    WalkTraceHQ.dRow δF 1 b hn nodes orbit chals pubs WalkHC.xKeyH
        (walkCol δF b 1 (wvals δF γ ρ (chals 0) z mL mR)) 0 0 0 0 i = hden δF chals 5 vX ∧
    WalkTraceHQ.dRow δF 1 b hn nodes orbit chals pubs WalkHC.recLH
        (walkCol δF b 1 (wvals δF γ ρ (chals 0) z mL mR)) 0 0 0 0 i = hden δF chals 4 vPL ∧
    WalkTraceHQ.dRow δF 1 b hn nodes orbit chals pubs WalkHC.recRH
        (walkCol δF b 1 (wvals δF γ ρ (chals 0) z mL mR)) 0 0 0 0 i = hden δF chals 4 vPR := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have hc : ∀ e : Env F, e.chal = slotVal b 25 chals →
      (gatherEnv b ((walkTemplateHQ δF 1).col0 3) e).chal = chals :=
    fun e he => funext fun r => WalkTraceHQ.gather_chal δF 1 b chals e he r
  have hL := E_low δF b hn nodes orbit chals pubs hinj (wvals δF γ ρ (chals 0) z mL mR)
    (WalkTraceHQ.zeroR (K := K) δF) 0
  have hK := E_kv δF b hn nodes orbit chals pubs hinj (wvals δF γ ρ (chals 0) z mL mR)
    (WalkTraceHQ.zeroR (K := K) δF) 0
  simp only [WalkTraceHQ.dRow, WalkTraceHQ.denAt]
  refine ⟨?_, ?_, ?_⟩
  · rw [denKeyQ_closed δF _ _ _ (vX (F := F))]
    · rw [hc _ rfl]; rfl
    · intro c hc5
      have : c < 5 := hc5
      interval_cases c <;>
        simp [WalkHC.xKeyH, CoeffExpr.eval, vX, WChip.idx, WalkHC.kL, WalkHC.vL, WalkHC.kR, WalkHC.vR,
          hL 3 (by norm_num) (by norm_num), hK 21 le_rfl (by norm_num), hK 22 (by norm_num) (by norm_num),
          hK 23 (by norm_num) (by norm_num), hK 24 (by norm_num) (by norm_num), WalkVals.base, WalkVals.named,
          walkFill, walkFillInv, wrow]
  · rw [denKeyQ_closed δF _ _ _ (vPL (F := F))]
    · rw [hc _ rfl]; rfl
    · intro c hc4
      have : c < 4 := hc4
      interval_cases c <;>
        simp [WalkHC.recLH, CoeffExpr.eval, vPL, WChip.ridx, WChip.pre, WalkHC.kL, WalkHC.vL,
          hL 5 (by norm_num) (by norm_num), hL 4 (by norm_num) (by norm_num), hK 21 le_rfl (by norm_num),
          hK 22 (by norm_num) (by norm_num), WalkVals.base, WalkVals.named, walkFill, walkFillInv, wrow]
  · rw [denKeyQ_closed δF _ _ _ (vPR (F := F))]
    · rw [hc _ rfl]; rfl
    · intro c hc4
      have : c < 4 := hc4
      interval_cases c <;>
        simp [WalkHC.recRH, CoeffExpr.eval, vPR, WChip.ridx, WChip.pre, WalkHC.kR, WalkHC.vR,
          hL 5 (by norm_num) (by norm_num), hL 4 (by norm_num) (by norm_num), hK 23 (by norm_num) (by norm_num),
          hK 24 (by norm_num) (by norm_num), WalkVals.base, WalkVals.named, walkFill, walkFillInv, wrow]
        <;> norm_num

abbrev wcol (chals : ℕ → K) (γ ρ z : 𝕂′) (mL mR : ℕ) : ℕ → Fin 1 → F :=
  walkCol δF b 1 (wvals δF γ ρ (chals 0) z mL mR)

/-- **The honest `walkChipJ8` (166) trace**: the `𝕂′` twin fill, kinds `0`, certificate re-chosen at `len = 0`. -/
def trW0 (chals pubs : ℕ → K) (γ ρ z : 𝕂′) (mL mR : ℕ) : Fin 166 → F[X] :=
  honestQ hn nodes (HonestK8.certUp (WalkTraceHQ.colHQ δF 1 b (wcol δF b chals γ ρ z mL mR) 0 0 0 0
    (WalkTraceHQ.rolesF δF 1 b hn nodes orbit chals pubs (wcol δF b chals γ ρ z mL mR) 0 0 0 0))
    (fun _ => 0)) 166

theorem walkJ8_0 (chals pubs : ℕ → K) (hF : GeneratedField.PrimeFieldElems F) (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin 1) (hi : (i : ℕ) + 1 < 1), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ z : 𝕂′) (mL mR : ℕ) (hok : ChalsOK δF chals γ ρ 11)
    (hx : FiniteIO.compress (m := 11) ⟨γ, ρ⟩ (wxKeyV δF (wrow δF (chals 0) z mL mR)) ≠ 0)
    (hL : FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecLV δF (wrow δF (chals 0) z mL mR)) ≠ 0)
    (hR : FiniteIO.compress (m := 8) ⟨γ, ρ⟩ (wrecRV δF (wrow δF (chals 0) z mL mR)) ≠ 0)
    (hXt : wxTot δF γ ρ (chals 0) z mL mR = Quad.mk _ (pubs 0) (pubs 1))
    (hPt : wpTot δF γ ρ (chals 0) z mL mR = Quad.mk _ (pubs 2) (pubs 3))
    (hpX : hden δF chals 5 vX ≠ 0) (hpL : hden δF chals 4 vPL ≠ 0) (hpR : hden δF chals 4 vPR ≠ 0)
    (hX : Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) = (hden δF chals 5 vX)⁻¹)
    (hP : Quad.mk _ (pubs WalkHQ.pubPQ) (pubs (WalkHQ.pubPQ + 1)) =
      liftQ δF (mL : F) * (hden δF chals 4 vPL)⁻¹ + liftQ δF (mR : F) * (hden δF chals 4 vPR)⁻¹) :
    RAP.SatisfiesWithPreprocessing (WalkJ8.walkChipJ8 δF 1 b hn nodes orbit chals pubs)
      (fun j => trW0 δF b hn nodes orbit chals pubs γ ρ z mL mR
        (Fin.cast (WalkJ8.walkChipJ8_width δF 1 b hn nodes orbit chals pubs) j)) := by
  have hok0 := walkOk0 δF b hn nodes orbit chals pubs hF hinj hadj γ ρ z mL mR hok hx hL hR hXt hPt
  have hd := fun i => dRow0 δF b hn nodes orbit chals pubs hinj γ ρ z mL mR i
  refine HonestK8.walkTwinJ8_accepted δF 1 b hn nodes orbit chals pubs _ 0 0 0 0 hinj hadj hok0
    (fun _ => Or.inl rfl) (fun _ => Or.inl rfl) (fun i => by rw [(hd i).1]; exact hpX)
    (fun i => by rw [(hd i).2.1]; exact hpL) (fun i => by rw [(hd i).2.2]; exact hpR) ?_ ?_ (fun _ => 0) ?_
    (fun _ => le_of_lt (by norm_num))
  · rw [hX, Finset.sum_range_one]
    simp only [WalkTraceHQ.dN, dif_pos (show 0 < 1 by norm_num)]
    rw [(hd ⟨0, by norm_num⟩).1]
  · rw [hP, Finset.sum_range_one]
    simp only [WalkTraceHQ.dN, WalkTraceH.cN, dif_pos (show 0 < 1 by norm_num)]
    rw [(hd ⟨0, by norm_num⟩).2.1, (hd ⟨0, by norm_num⟩).2.2]
    simp [walkCol, WalkVals.base, WalkVals.named, WChip.mL, WChip.mR, walkFill, walkFillInv, wrow]
  · intro i
    simp [walkCol, WalkVals.base, WalkVals.named, WChip.len, walkFill, walkFillInv, wrow]

end HQ

end

end Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemWalk
