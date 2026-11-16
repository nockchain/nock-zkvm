/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluSatRun.lean

  **The ALU accepts the run's honest
  trace at a good coin.**

  `aluSZChipJ9_sat_run`: at the coins `chalsALJ8 δ χ` and the run's ALU calls (`callsLOf` of `j9alDataOf`), the
  honest table `tblP` at the limb coin `y = yOf χ` satisfies `aluSZChipJ9`, binds the honest preprocessing and meets
  `PregOK`, for every coin `χ` outside the ALU pole family `famAL` (stage 5).  Discharged here (versus the stage 1–3
  theorem): `hy` / `hyp` (`chalsALJ8_y` / `chalsALJ8_ypow`), `hden` (`hden_of_famAL`), and `hblk`'s per-call form
  (`CallOK` from the run, stage 4).  Still carried: `hblk` (block obligations, disclosed), `hnoDec` (disclosed),
  `hlimb` (`PrimLimbs62`, NEW, disclosed), `hinj` / `hadj` / `hlen` (orbit, table fits), `hpV` / `hpS` / `hpX`
  (terminal publics = full sums), the registry facts `hnd` / `hprim` (`CheckedRegP.ndP`, `CompiledByP.2`) and the
  J-9 A run facts `hpG` / `h31`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatPreg
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluCallOK
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluPoles

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSatRun

open Nock Nock.Reified Nock.Framework Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatPreg
open Nock.NockVMROM.Thm54.VclL.Handle.AluCallOK
open Nock.NockVMROM.Thm54.VclL.Handle.AluPoles
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable (callsLOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8 chalsALJ8_y chalsALJ8_ypow)
open Nock.Jet.Prim (PrimOp primSpec)
open Module

noncomputable section

section Run
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (b : Basis (Fin 3) (ZMod p) K)
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (pubs : ℕ → K)
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp))
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- The run's ALU calls. -/
abbrev clsRun : List CallL :=
  callsLOf (j9alDataOf p Rg Rt prims hgen).cells (j9alDataOf p Rg Rt prims hgen).H prims
    (pcallsR (prims.map Prod.fst) (rowsOfT t))

/-- The run's honest ALU table at limb coin `y`. -/
abbrev tblRun (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ) (y : Quad (algebraMap (ZMod p) K δ)) :
    List (BRow (ZMod p) × QRow (Quad (algebraMap (ZMod p) K δ))) :=
  tblP δ p y (pregsP (F := ZMod p) ps vcOf mOf) (clsRun (p := p) Rt prims hgen)

/-- **Stages 1–5: the ALU accepts the run's honest trace at every coin outside `famAL`.** -/
theorem aluSZChipJ9_sat_run (ps : List (ℕ × PrimOp)) (vcOf mOf : ℕ → ℕ) (χ : Coins frameJ8 K)
    (hpG : p = Nock.Atoms.p) (h31 : ComplJ9ARun.Rows31A (j9alDataOf p Rg Rt prims hgen))
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec) (hnoDecP : ∀ q ∈ ps, q.2 ≠ .dec)
    (hlimb : PrimLimbs62 (prims.map Prod.fst) t)
    (hblk : ∀ cl, CallOK p cl → BlockBaseSat (F := ZMod p) p cl ∧ BlockIdentSat (K := K) δ p cl)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hlen : (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ)).length ≤ n)
    (hgood : ∀ e ∈ famAL δ (tblRun δ Rt prims hgen ps vcOf mOf) n, χ ∉ e.ev)
    (hpV : Quad.mk _ (pubs AluSZChipJ9.pubALv) (pubs (AluSZChipJ9.pubALv + 1)) =
      ∑ i : Fin n, tV δ (chalsALJ8 δ χ) (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ)) i)
    (hpS : Quad.mk _ (pubs AluSZChipJ9.pubALs) (pubs (AluSZChipJ9.pubALs + 1)) =
      ∑ i : Fin n, tS δ (chalsALJ8 δ χ) (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ)) i)
    (hpX : Quad.mk _ (pubs AluSZChipJ9.pubALx) (pubs (AluSZChipJ9.pubALx + 1)) =
      ∑ i : Fin n, tX δ (chalsALJ8 δ χ) (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ)) i) :
    (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit (chalsALJ8 δ χ) pubs
        (preLOf δ nodes (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ)))).rap.Satisfies
        (polyAL δ b hn nodes orbit (chalsALJ8 δ χ) pubs
          (preLOf δ nodes (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ)))
          (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ))
          (r2AL δ (chalsALJ8 δ χ) (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ)))) ∧
      (AluSZChipJ9.aluSZChipJ9 δ b hn nodes orbit (chalsALJ8 δ χ) pubs
        (preLOf δ nodes (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ)))).BindsPreprocessing
        (polyAL δ b hn nodes orbit (chalsALJ8 δ χ) pubs
          (preLOf δ nodes (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ)))
          (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ))
          (r2AL δ (chalsALJ8 δ χ) (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ)))) ∧
      AcceptsJ9AL.PregOK nodes ps (preLOf δ nodes (tblRun δ Rt prims hgen ps vcOf mOf (yOf δ χ))) := by
  have hok := callOK_run_G Rt prims hgen hpG h31 hnd hprim hnoDec hlimb
  have hblk' := hblk_run Rt prims hgen δ hblk hok
  have hy : Quad.mk _ (chalsALJ8 δ χ 2) (chalsALJ8 δ χ 3) = yOf δ χ := chalsALJ8_y δ χ
  have hyp : ∀ t ≤ 32, Quad.mk _ (chalsALJ8 δ χ (40 + 2 * t)) (chalsALJ8 δ χ (41 + 2 * t)) = (yOf δ χ) ^ t :=
    fun t ht => chalsALJ8_ypow δ χ t ht
  exact aluSZChipJ9_honest_sat_preg δ b hn nodes orbit (chalsALJ8 δ χ) pubs p (yOf δ χ) ps vcOf mOf
    (clsRun (p := p) Rt prims hgen) hnoDecP hblk' hy hyp hinj hadj hlen
    (hden_of_famAL δ (tblRun δ Rt prims hgen ps vcOf mOf) χ hgood) hpV hpS hpX

end Run

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSatRun
