/-
  Nock/RedTeam/Batch4776Thm54NVJetClean.lean  
  **The jet witness feeds `probJ8V_final_clean` with no instance diamond.**
  `probJ8V_final_clean` takes only `[Algebra (ZMod p) K]` and internally builds the `ringChar` instance by `Eq.rec`.
  Mathlib has `Subsingleton (Algebra (ZMod n) R)` (Mathlib/Algebra/Algebra/ZMod.lean), so any two algebra structures
  agree; `eqrec_algebraMap` shows the `Eq.rec` one is the transport of the given one.  The restated witnesses live in
  the clean theorem's own context (the instance found at `KC`), so no transport is needed at the use site.
-/
import Nock.RedTeam.Batch4775Thm54NVJetRegime

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch4776

open Nock.NockVMROM.Thm54.SVFrame Nock.V1J8.Exe Nock.V1J8.Check Nock Nock.TraceGenExe Nock.RedTeam.Batch4771 Nock.RedTeam.Batch4774 Nock.RedTeam.Batch4775 Nock.V1J8
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)

/-- Any two `ZMod n`-algebra structures on `K` coincide (Mathlib `ZMod.instSubsingletonAlgebra`-style instance). -/
theorem algebra_zmod_unique (n : ℕ) (K : Type) [Field K] (i j : Algebra (ZMod n) K) : i = j :=
  Subsingleton.elim i j

/-- The `Eq.rec` instance of `probJ8V_final_clean` is the transport of the given one: same `algebraMap`. -/
theorem eqrec_algebraMap {p q : ℕ} (K : Type) [Field K] [i : Algebra (ZMod p) K] (h : p = q) (x : ZMod p) :
    @algebraMap (ZMod q) K _ _ (@Eq.rec ℕ p (fun q _ => Algebra (ZMod q) K) i _ h) (h ▸ x) = algebraMap (ZMod p) K x := by
  subst h; rfl

/-- The `ringChar` instance used inside `probJ8V_final_clean` equals ANY other instance transported along `hrc`
(in particular the `ZMod.algebra`-style one): `Subsingleton` at `n = ringChar (ZMod p)`. -/
theorem eqrec_unique {p : ℕ} (K : Type) [Field K] [i : Algebra (ZMod p) K] (hrc : ringChar (ZMod p) = p)
    (j : Algebra (ZMod (ringChar (ZMod p))) K) :
    (@Eq.rec ℕ p (fun q _ => Algebra (ZMod q) K) i _ hrc.symm) = j := Subsingleton.elim _ _

/-- **The jetted witness in `probJ8V_final_clean`'s exact context.**  Same statement as `nvJet_in_regime`, with the
instance being the one in scope at `KC` (the only one `probJ8V_final_clean` sees); restated here as a one-liner
`exact` target.  Derived from `nvJet_in_regime`. -/
theorem nvJet_in_regime_clean : ∃ hv : ValidJ8 Ijet,
    Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 (mkPb Ijet hv) RgJ Ijet.c
      (toχ Ijet.χ) Ijet.M.toMsg (mkTr Ijet) EncInjJ8.cornerC Ijet.g ∧ 0 < (mkPb Ijet hv).nJ := by
  obtain ⟨hv, hA, hJ, -⟩ := nvJet_in_regime
  exact ⟨hv, hA, hJ⟩

open Classical in
/-- **`nvJet_hyps_final_clean`**: the witness conjoined with the conclusion of `probJ8V_final_clean` at `K := KC`,
`δ := deltaF`, `b := powerBasis3`, `Pb := mkPb Ijet hv`, `Rg := RgJ`, `c := Ijet.c`, `r := cornerC`, `g := Ijet.g`:
every numeric hypothesis is discharged here.  Taken as arguments: `hQ : StJ8 Q`, and the instances
`[CharP KC p] [CharP 𝕂′ p]`.  The `Algebra Fp 𝕂′` instance is the canonical `AdjoinRoot.instAlgebra`
(the one the witness uses), not a free argument. -/
theorem nvJet_hyps_final_clean [CharP KC Nock.Field.p]
    [CharP (Quad (algebraMap (ZMod Nock.Field.p) KC deltaF)) Nock.Field.p]
    (Q : Coins frameJ8 KC → TrJ8 (ZMod Nock.Field.p)) (hQ : StJ8 Q) :
    ∃ hv : ValidJ8 Ijet,
      Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 (mkPb Ijet hv) RgJ Ijet.c
        (toχ Ijet.χ) Ijet.M.toMsg (mkTr Ijet) EncInjJ8.cornerC Ijet.g ∧
      ((Finset.univ.filter fun χ : Coins frameJ8 KC =>
        (∃ M : MsgJ8' Nock.Field.p KC deltaF, Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V.AcceptsJ8V deltaF powerBasis3
          (mkPb Ijet hv) RgJ Ijet.c χ M (Q χ) EncInjJ8.cornerC Ijet.g) ∧ ¬ Nock.Jet.HoldsN Ijet.c).card : ℚ) /
        Fintype.card (Coins frameJ8 KC) < 1 / (2 : ℚ) ^ 155 := by
  obtain ⟨hv, hA, hJ, hH, hF, hcK, hpG, hr, hqM, hk, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg⟩ := nvJet_in_regime
  exact ⟨hv, hA, Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8.probJ8V_final_clean deltaF powerBasis3 (mkPb Ijet hv) hF
    Ijet.c Q hQ hpG hcK hr hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg⟩

end Nock.RedTeam.Batch4776

#print axioms Nock.RedTeam.Batch4776.algebra_zmod_unique
#print axioms Nock.RedTeam.Batch4776.eqrec_algebraMap
#print axioms Nock.RedTeam.Batch4776.eqrec_unique
#print axioms Nock.RedTeam.Batch4776.nvJet_in_regime_clean
#print axioms Nock.RedTeam.Batch4776.nvJet_hyps_final_clean
