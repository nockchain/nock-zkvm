/-
  Nock/NockVMROM/Thm54/VclL/Handle/EpsVS.lean

  **`ε` at the VS instance.**  Additive.

  * `standaloneVS_sound'`: `standaloneVS_sound` with the two derivable instance arguments discharged
    (`Fact (ringChar F).Prime` from `2^63 < ringChar F`; the `ZMod` algebra is the canonical one, unique
    up to `Subsingleton`).
  * `boundVCLH''`: the summand weights of `sumCVS ++ sumMVS ++ jointVS`, summed as an explicit function
    of `N` (compute rows), `D` (cell rows), `W` (walk rows), the census fuel `Λ` and `|𝕂|, |𝕂′|`;
    `epsilonVS_eq` / `epsilonVS_le` : `epsilonOf (allSummandsG …) = boundVCLH'' …`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.SoundVS
import Nock.NockVMROM.Thm54.VclL.Events.Bound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.EpsVS

open Nock Nock.Walk Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS Nock.NockVMROM.Thm54.VclL.Handle.ServedVS
open Nock.NockVMROM.Thm54.VclL.Handle.ServedPVS Nock.NockVMROM.Thm54.VclL.Handle.WalkGenVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS
open Nock.NockVMROM.Thm54.VclL.Handle.SoundVS
open Nock.NockVMROM.Thm54.FiniteIO
open scoped Polynomial

noncomputable section

section VS
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)

attribute [local instance] ClaimDenVS.quadCharF

/-! ## 1. The instance arguments -/

theorem prime_of_big (hp : 2 ^ 63 < ringChar F) : (ringChar F).Prime :=
  (CharP.char_is_prime_or_zero F (ringChar F)).resolve_right (by omega)

/-- The `ZMod` algebra on `K` (`K` has characteristic `ringChar F`). -/
abbrev zmodAlg : Algebra (ZMod (ringChar F)) K :=
  haveI : CharP K (ringChar F) := by
    rw [← SoundVS.ringChar_KF (F := F) (K := K)]; exact ringChar.charP K
  ZMod.algebra K (ringChar F)

theorem zmodAlg_unique (A : Algebra (ZMod (ringChar F)) K) : A = zmodAlg (F := F) (K := K) :=
  Subsingleton.elim _ _

/-- **`standaloneVS_sound'`**: `standaloneVS_sound` with the two instance arguments discharged. -/
theorem standaloneVS_sound' (hp : 2 ^ 63 < ringChar F) :
    letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
    letI : Algebra (ZMod (ringChar F)) K := zmodAlg
    StandaloneG (compCoreVS δF hT hP hC (sumCVS (F := F) (K := K) hT hP hC))
      (memCoreVS δF hT hP kr hC (sumMVS (F := F) (K := K) δF hT hP kr hC))
      (jointVS (F := F) (K := K) δF hT hP hC) := by
  letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
  letI : Algebra (ZMod (ringChar F)) K := zmodAlg
  exact standaloneVS_sound δF hT hP kr hC


/-! ## 2. The explicit bound -/

/-- **`boundVCLH'' c c' N D W Λ`** (`c = |𝕂|`, `c' = |𝕂′|`, `N` compute rows, `D` cell rows, `W` walk rows,
`Λ` the census fuel):
* over `c²`: dyck roots `D·(2·2^110 − 1)`, the zero seed `1`, the census `pairCount (D+3)·(2Λ − 1)`, and
  the two handle IO summands (coins `γH, ρH ∈ 𝕂`; export `ioFUB 5 (3N+W) D c`, path `ioFUB 5 (2N) (2W) c`);
* over `c⁴`: the validity IO `ioFUB 5 (3+2D) D c'` and the fingerprint export IO `ioFUB 11 W (2D) c'`. -/
def boundVCLH'' (c c' N D W Λ : ℕ) : ℚ :=
  ((6 * N : ℕ) : ℚ) / c + ((2 * N + 2 : ℕ) : ℚ) / c + ((15 * W : ℕ) : ℚ) / c +
  ((D * (2 * fuelChip - 1) + 1 + pairCount (D + 3) * (2 * Λ - 1) : ℕ) : ℚ) / c ^ 2 +
  ((ioFailureUnionBound 5 (3 * N + W) D c + ioFailureUnionBound 5 (2 * N) (2 * W) c : ℕ) : ℚ) / c ^ 2 +
  ((ioFailureUnionBound 5 (3 + 2 * D) D c' + ioFailureUnionBound 11 W (2 * D) c' : ℕ) : ℚ) / c ^ 4

section Eps
variable [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]

/-- The ε of the VS summand lists is `boundVCLH''` (in fact an equality). -/
theorem epsilonVS_eq (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC (sumCVS hT hP hC)) (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC))) :
    epsilonOf (allSummandsG (CC := compCoreVS δF hT hP hC (sumCVS hT hP hC))
        (MC := memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVS δF hT hP hC)) =
      boundVCLH'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
        (V.memRows (tCS hT hP)) (V.memRows (tWS hT hP)) (claimFuel V.claim) := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  have h2 : ∀ (i j : Fin frameVS.n), i ≠ j → ({i, j} : Finset (Fin frameVS.n)).card = 2 :=
    fun i j h => Finset.card_pair h
  have hL : allSummandsG (CC := compCoreVS δF hT hP hC (sumCVS hT hP hC))
        (MC := memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVS δF hT hP hC) =
      [cwalkVS hT hP hC V, ctileVS hT hP hC V, dyckVS δF hT hP hC V, walkChainVS δF hT hP kr hC V,
        fpExportIOVS δF hT hP kr hC V, zeroVS δF hT hP hC, censusVS δF hT hP hC V,
        valSummand δF hT hP hC V msg.msg0C, ioSummandHX hT hP hC V, ioSummandHP hT hP hC V] := rfl
  rw [hL]
  simp only [epsilonOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have e1 : (cwalkVS hT hP hC V).coins.card = 2 := h2 _ _ (by decide)
  have e2 : (ctileVS hT hP hC V).coins.card = 1 := Finset.card_singleton _
  have e3 : (dyckVS δF hT hP hC V).coins.card = 2 := h2 _ _ (by decide)
  have e4 : (walkChainVS δF hT hP kr hC V).coins.card = 2 := h2 _ _ (by decide)
  have e5 : (fpExportIOVS δF hT hP kr hC V).coins.card = 4 := ioSpecVS_dep_card (algebraMap F K δF)
  have e6 : (zeroVS δF hT hP hC (K := K)).coins.card = 2 := h2 _ _ (by decide)
  have e7 : (censusVS δF hT hP hC V).coins.card = 2 := h2 _ _ (by decide)
  have e8 : (valSummand δF hT hP hC V msg.msg0C).coins.card = 4 := ioSpecVS_dep_card (algebraMap F K δF)
  have e9 : (ioSummandHX hT hP hC V).coins.card = 2 := h2 _ _ (by decide)
  have e10 : (ioSummandHP hT hP hC V).coins.card = 2 := h2 _ _ (by decide)
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  have w1 : (cwalkVS hT hP hC V).weight = Fintype.card K * (6 * V.N) := rfl
  have w2 : (ctileVS hT hP hC V).weight = 2 * V.N + 2 := rfl
  have w3 : (dyckVS δF hT hP hC V).weight = V.memRows (tCS hT hP) * (2 * fuelChip - 1) := rfl
  have w4 : (walkChainVS δF hT hP kr hC V).weight = Fintype.card K * (15 * V.memRows (tWS hT hP)) := rfl
  have w5 : (fpExportIOVS δF hT hP kr hC V).weight =
      ioFailureUnionBound 11 (V.memRows (tWS hT hP)) (2 * V.memRows (tCS hT hP)) (Fintype.card (Quad (algebraMap F K δF))) := rfl
  have w6 : (zeroVS δF hT hP hC (K := K)).weight = 1 := rfl
  have w7 : (censusVS δF hT hP hC V).weight = pairCount (V.memRows (tCS hT hP) + 3) * (2 * claimFuel V.claim - 1) := rfl
  have w8 : (valSummand δF hT hP hC V msg.msg0C).weight =
      ioFailureUnionBound 5 (3 + 2 * V.memRows (tCS hT hP)) (V.memRows (tCS hT hP)) (Fintype.card (Quad (algebraMap F K δF))) := rfl
  have w9 : (ioSummandHX hT hP hC V).weight =
      ioFailureUnionBound 5 (3 * V.N + V.memRows (tWS hT hP)) (V.memRows (tCS hT hP)) (Fintype.card K) := rfl
  have w10 : (ioSummandHP hT hP hC V).weight =
      ioFailureUnionBound 5 (2 * V.N) (2 * V.memRows (tWS hT hP)) (Fintype.card K) := rfl
  rw [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10]
  unfold boundVCLH''
  push_cast
  field_simp
  ring

theorem epsilonVS_le (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC (sumCVS hT hP hC)) (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC))) :
    epsilonOf (allSummandsG (CC := compCoreVS δF hT hP hC (sumCVS hT hP hC))
        (MC := memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)) V msg.msg0C msg.msg0M (jointVS δF hT hP hC)) ≤
      boundVCLH'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
        (V.memRows (tCS hT hP)) (V.memRows (tWS hT hP)) (claimFuel V.claim) :=
  (epsilonVS_eq δF hT hP kr hC V msg).le

end Eps

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.EpsVS
