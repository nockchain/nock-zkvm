/-
  NockvmE2E/Exec/DagSemWit.lean   (vacuity witnesses for Exec/DagSem.lean; split out: kernel `decide` on concrete data is heavy)
-/
import NockvmE2E.Exec.DagSem
import NockvmE2E.Exec.J8Shape

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

namespace NockvmE2E.Exec.DagSem
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.Tr NockvmE2E.Rap NockvmE2E.Deep NockvmE2E.J8
open NockvmE2E.Exec.E2ELR

/-! ## Vacuity witnesses (kernel-checked instances of the hypotheses) -/
section Witness


/-- the 3-node chip `[.chal 0, .var 0 0, .mul (.ref 0) (.ref 1)]`; one constraint `χ₀ · cur₀` -/
def wChip : Chip :=
  { id := "w", shared := #[.chal 0, .var 0 0], cons := #[{ kind := 0, round := 0, deg := 2, e := .mul (.ref 0) (.ref 1) }],
    colRound := #[0], sharedK := #[false, false], consK := #[false], baseCols := 1, width := 1 }

def wEnv : DEnv := { cur := #[⟨5, 6, 7⟩], next := #[⟨1, 2, 3⟩], pub := #[9], chal := #[⟨4, 5, 6⟩], bc := 1 }

theorem canon3_arr (a : Array VF.K3) (h : ∀ x ∈ a, canon3 x) (i : ℕ) : canon3 a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]; exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg a i hi]; exact canon3_zero

theorem canon_arr (a : Array UInt64) (h : ∀ x ∈ a, canon x) (i : ℕ) : canon a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]; exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg a i hi]; unfold canon; decide

theorem canon3_lit (a b c : UInt64) (ha : a.toNat < 1000) (hb : b.toNat < 1000) (hc : c.toNat < 1000) : canon3 ⟨a, b, c⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold canon p; dsimp only; omega)

/-- `toKV_evalDag` instantiated -/
theorem w_toKV_evalDag : toKV (evalDag wChip wEnv)[0]! = (evalDagK wChip (KEnv.ofD wEnv))[0]! := by
  refine toKV_evalDag wChip wEnv (canon3_arr _ ?_) (canon3_arr _ ?_) (canon_arr _ ?_) (canon3_arr _ ?_) ?_ ?_ 0
  · intro x hx; simp only [wEnv, List.mem_singleton, Array.mem_def] at hx; subst hx; exact canon3_lit _ _ _ (by decide) (by decide) (by decide)
  · intro x hx; simp only [wEnv, List.mem_singleton, Array.mem_def] at hx; subst hx; exact canon3_lit _ _ _ (by decide) (by decide) (by decide)
  · intro x hx; simp only [wEnv, List.mem_singleton, Array.mem_def] at hx; subst hx; unfold canon p; decide
  · intro x hx; simp only [wEnv, List.mem_singleton, Array.mem_def] at hx; subst hx; exact canon3_lit _ _ _ (by decide) (by decide) (by decide)
  · intro s hs; simp [wChip] at hs; rcases hs with rfl | rfl <;> simp [ExCan]
  · intro c hc; simp [wChip] at hc; subst hc; simp [ExCan]

/-- the value is the expected product `χ₀ · cur₀` -/
theorem w_val : (evalDagK wChip (KEnv.ofD wEnv))[0]! = toKV ⟨4, 5, 6⟩ * toKV ⟨5, 6, 7⟩ := by
  simp [evalDagK, memoK, wChip, evKC, KEnv.ofD, wEnv]

/-- `evalDagK_congr` instantiated: change a column the chip does not read (index 1 ≥ w = 1) -/
theorem w_congr : evalDagK wChip (KEnv.ofD wEnv) = evalDagK wChip { KEnv.ofD wEnv with cur := fun i => if i < 1 then toKV wEnv.cur[i]! else 0 } :=
  evalDagK_congr wChip 1 1 1 (by decide +kernel) _ _ rfl rfl (fun i hi => by simp [KEnv.ofD, hi]) (fun i _ => rfl)
    (fun i _ => rfl) (fun i _ => rfl)

/-- `aeval_dagPoly` instantiated -/
theorem w_dagPoly : MvPolynomial.aeval (fun q : ℕ × Fin 2 => if q.2 = 0 then (KEnv.ofD wEnv).cur q.1 else (KEnv.ofD wEnv).next q.1)
    (dagPoly wChip (KEnv.ofD wEnv).chal (KEnv.ofD wEnv).pub)[0]! = (evalDagK wChip (KEnv.ofD wEnv))[0]! :=
  aeval_dagPoly wChip (KEnv.ofD wEnv) rfl 0

/-- F0 on concrete sizes -/
example : flatIdx [2, 3] 3 = (1, 1) := by decide
example : flatIdx [2, 3] 1 = (0, 1) := by decide

/-- `termsAt_get?` instantiated at the J8Shape toy (one table with one constraint) -/
theorem w_termsAt (slots : Array VF.K3) (ζ : VF.K3) (vT : Array (Array VF.K3)) :
    (termsAt J8Shape.toyShape slots ζ vT)[0]? = some (toKV (multOf J8Shape.toyShape ζ J8Shape.toyShape.tabs[0]) *
      toKV (tabCvAt J8Shape.toyShape slots ζ vT J8Shape.toyShape.tabs[0])[0]!) :=
  termsAt_get? J8Shape.toyShape slots ζ vT 0 (by decide +kernel) (by decide +kernel)

/-- `curNxtAt_get` instantiated -/
theorem w_curNxt (ζ : VF.K3) (vT : Array (Array VF.K3)) :
    (curNxtAt J8Shape.toyShape ζ vT).1[0]! = (vT[0]!)[0]! :=
  (curNxtAt_get J8Shape.toyShape ζ vT 0 (by decide +kernel)).1

/-- `toKV_hornerG` instantiated -/
theorem w_horner (z : VF.K3) : toKV (VF.K3.hornerG #[1, 2] z) = ∑ m ∈ Finset.range 2, psiV (#[1, 2] : Array UInt64)[m]! * toKV z ^ m :=
  toKV_hornerG _ z (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> (unfold canon p; decide))

/-- `multOf_Zout` at `hN = 2`, `hN_t = 1` (one real factor), `hShift = 1`, `hGen = 2^48` -/
def wXI : ExecInst := { J8Shape.toyShape with hN := 2 }
def wTab : TabInst := { hN := 1, col0 := 0, nc := 2, npub := 1, pubBase := 0, chip := J8Shape.toyChip }

theorem w_multOf (zeta : VF.K3) (hz : canon3 zeta) :
    toKV (multOf wXI zeta wTab) = eval (toKV zeta)
      (((Zout ((Finset.range wXI.hN).image (fun i => zv wXI.hShift * zv wXI.hGen ^ i))
        ((Finset.range wTab.hN).image (fun i => zv wXI.hShift * zv wXI.hGen ^ i))).map (algebraMap (ZMod p) KC))) := by
  refine multOf_Zout wXI wTab zeta hz (by unfold canon wXI p; decide) _ _ rfl rfl (by decide +kernel) ?_
  have hne : zv wXI.hGen ≠ 1 := by decide +kernel
  intro a ha b hb e
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have h2 : ∀ x : ℕ, x < 2 → x = 0 ∨ x = 1 := fun x hx => by omega
  rcases h2 a (by simpa [wXI] using ha) with rfl | rfl <;> rcases h2 b (by simpa [wXI] using hb) with rfl | rfl
  · rfl
  · exfalso; apply hne; have : zv wXI.hShift = 1 := by decide +kernel
    simpa [this] using e.symm
  · exfalso; apply hne; have : zv wXI.hShift = 1 := by decide +kernel
    simpa [this] using e
  · rfl

end Witness

end NockvmE2E.Exec.DagSem

#print axioms NockvmE2E.Exec.DagSem.w_toKV_evalDag
#print axioms NockvmE2E.Exec.DagSem.w_val
#print axioms NockvmE2E.Exec.DagSem.w_congr
#print axioms NockvmE2E.Exec.DagSem.w_dagPoly
#print axioms NockvmE2E.Exec.DagSem.w_termsAt
#print axioms NockvmE2E.Exec.DagSem.w_curNxt
#print axioms NockvmE2E.Exec.DagSem.w_horner
#print axioms NockvmE2E.Exec.DagSem.w_multOf
