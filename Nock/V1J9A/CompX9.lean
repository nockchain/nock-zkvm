/-
  Nock/V1J9A/CompX9.lean

* `srcX9`: the twin's gates as SOURCE gates (`baseGatesFX9`, the slot pairs of `slotsX9`, `walkGatesFX9`),
    with `gatesHX9_src : gatesHX9 powerBasis3 deltaF = srcX9.flatMap expandS`.
  * `checkCompX9`: every source gate at `Env.viaPerm permX9` of the RAP-order row env (RAP columns `0..136`),
    plus the masks at RAP columns 17 / 18 (fixed by `permX9`).
-/
import Nock.V1J8.CompX
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9RAP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J9A.CompX9

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD (col0Id qGates)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.V1Check Nock.V1J8.Exe Nock.V1J8.CompX

/-- **The twin's source gates**: base, the slot pairs (two `𝕂` gates each), the walk gates over 20 states. -/
def srcX9 : List (SG ) :=
  (baseGatesFX9 (F := ZMod p)).map SG.base ++
    (slotPairsX9 (ZMod p) deltaF).flatMap (fun q => [SG.mix q.1, SG.mix q.2]) ++
    (walkGatesFX9 (F := ZMod p)).map SG.mix

/-- **The twin's gate list is the expansion of the source gates.** -/
theorem gatesHX9_src : gatesHX9 powerBasis3 deltaF = (srcX9 ).flatMap expandS := by
  unfold gatesHX9 srcX9
  rw [List.flatMap_append, List.flatMap_append, base_part, mid_part, walk_part]

theorem rowOK9_iff (e : Env (ZMod p)) :
    (srcX9 ).all (srcOK e) = true ↔ ∀ g ∈ gatesHX9 powerBasis3 deltaF, g.eval e = 0 := by
  rw [gatesHX9_src, List.all_eq_true]
  simp only [List.mem_flatMap]
  constructor
  · rintro h g ⟨s, hs, hg⟩
    exact (srcOK_iff e s).mp (h s hs) g hg
  · intro h s hs
    exact (srcOK_iff e s).mpr fun g hg => h g ⟨s, hs, hg⟩

/-- **An executable twin compute table** (`137` columns in RAP order). -/
structure TabX9 (n : ℕ) where
  nodes : Fin n → ZMod p
  ω : ZMod p
  cols : ℕ → Fin n → ZMod p
  chal : ℕ → ZMod p
  pub : ℕ → ZMod p

/-- The RAP-order row environment at row `i` (the last row's successor is the interpolant extrapolation, as J-8). -/
def TabX9.env {n : ℕ} (T : TabX9  n) (i : Fin n) : Env (ZMod p) where
  trace := fun j => if j < 137 then T.cols j i else 0
  traceNext := fun j => if j < 137 then
      (if h : (i : ℕ) + 1 < n then T.cols j ⟨i + 1, h⟩
        else ∑ k, T.cols j k * lagW T.nodes (T.ω * T.nodes i) k)
    else 0
  chal := T.chal
  pub := T.pub

/-- **The executable twin compute check**: every source gate at every row (twin gates read through `permX9`);
the two masks at RAP columns 17 / 18. -/
def checkCompX9 {n : ℕ} (T : TabX9  n) : Bool :=
  (List.finRange n).all (fun i => (srcX9 ).all (srcOK (Env.viaPerm permX9 (T.env i)))) &&
  ([(17, firstMaskE n), (18, lastMaskE n)] : List (ℕ × (Fin n → ZMod p))).all
    (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i))

theorem checkCompX9_gates_iff {n : ℕ} (T : TabX9  n) :
    ((List.finRange n).all (fun i => (srcX9 ).all (srcOK (Env.viaPerm permX9 (T.env i)))) = true) ↔
    ∀ i : Fin n, ∀ g ∈ gatesHX9P (F := ZMod p) powerBasis3 deltaF, g.eval (T.env i) = 0 := by
  rw [List.all_eq_true]
  constructor
  · intro h i g hg
    have := (gatesHX9P_eval powerBasis3 deltaF (T.env i)).mpr
      ((rowOK9_iff _).mp (h i (List.mem_finRange i))) g hg
    exact this
  · intro h i _
    refine (rowOK9_iff _).mpr ?_
    exact (gatesHX9P_eval powerBasis3 deltaF (T.env i)).mp (h i)

/-! ## Negative control: a 1-row all-zero table -/

def zeroTab : TabX9  1 := ⟨fun _ => 0, 0, fun _ _ => 0, fun _ => 0, fun _ => 0⟩

#eval checkCompX9 zeroTab

#print axioms gatesHX9_src
#print axioms checkCompX9_gates_iff

end Nock.V1J9A.CompX9
