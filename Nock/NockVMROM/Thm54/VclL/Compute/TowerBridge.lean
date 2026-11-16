import Nock.NockVMROM.Thm54.VclL.Compute.TowerSat

/-!
# Route (d), TWD-4 item (c) : the compress bridge at `Kio := Quad δ`

The `𝕂′` slot equations are the `FiniteIO.compress`
equation over `Kio := Quad δ` at the `𝕂′` IO coins `γ′ = Quad.mk (limbs 21) (limbs 42)`,
`ρ′ = Quad.mk (limbs 24) (limbs 45)` (`coinsQ`), and the accumulators are two `𝕂` accumulators
(`acc_rows` at `Kio := 𝕂`, once on the Re limbs, once on the Im limbs) combined in `𝕂′`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section Compress
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The `𝕂′` IO coins at an environment pair: `γ′ = (21, 42)`, `ρ′ = (24, 45)`. -/
def coinsQ (eK : Env K) (eF : Env F) : FiniteIO.IOCoins (Quad (algebraMap F K δ)) :=
  ⟨Q.val δ (qγ F) eK eF, Q.val δ (qρ F) eK eF⟩

theorem coinsQ_gamma (eK : Env K) (eF : Env F) :
    (coinsQ δ eK eF).gamma = Quad.mk _ (eK.chal 21) (eK.chal 42) := by
  simp [coinsQ, qγ, qvar_val, kread, imVal]

theorem coinsQ_pole (eK : Env K) (eF : Env F) :
    (coinsQ δ eK eF).pole = Quad.mk _ (eK.chal 24) (eK.chal 45) := by
  simp [coinsQ, qρ, qvar_val, kread, imVal]

/-- **`FiniteIO.compress` at the `𝕂′` coins is `denQ`.** -/
theorem compress_denQ (eK : Env K) (eF : Env F) (m : ℕ) (rr : Fin m → Q F) :
    FiniteIO.compress (coinsQ δ eK eF) (fun c => Q.val δ (rr c) eK eF) =
      Q.val δ (denQ F δ m rr) eK eF := by
  rw [denQ_val δ eK eF m rr]
  simp only [FiniteIO.compress, Walk.rlc, coinsQ]

end Compress

section Slots
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The `𝕂′` record value of a record read at the row (`Q.val` of `entryQ`). -/
def recValQ (eK : Env K) (eF : Env F) {m : ℕ} (r : Fin m → Entry) : Fin m → Quad (algebraMap F K δ) :=
  fun c => Q.val δ (entryQ F (r c)) eK eF

/-- **Slot 0 at `Kio := Quad δ`**: the `𝕂′` inverse is the reciprocal of the compressed formula-cell
record at the `𝕂′` coins. -/
theorem slot0Q_sound (eK : Env K) (eF : Env F) (h : Q.IsZero (slot0Q F δ) eK eF) :
    Q.val δ (invQ F inv0Base (invImBase 0)) eK eF *
      FiniteIO.compress (coinsQ δ eK eF) (fun c => Q.val δ (recQ0 F c) eK eF) = 1 := by
  rw [compress_denQ]
  have := (Q.isZero_iff δ eK eF _).mp h
  rw [slot0Q, qsub_val, qmul_val, qconst_val] at this
  simpa using sub_eq_zero.mp this

/-- **Slot 1** (`s0·(1−z1)` path / export): the active-denominator form. -/
theorem slot1Q_sound (eK : Env K) (eF : Env F) (h : Q.IsZero (slot1Q F δ) eK eF) :
    Q.val δ (invQ F (lookupInvBase 0) (invImBase 1)) eK eF *
      (Q.val δ (qlift F (actP0 F)) eK eF *
          FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF op0PathRec) +
        Q.val δ (qlift F (selSum slot1ExportSels)) eK eF *
          FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF tailRec)) =
      Q.val δ (qlift F (actP0 F)) eK eF + Q.val δ (qlift F (selSum slot1ExportSels)) eK eF := by
  have := (Q.isZero_iff δ eK eF _).mp h
  rw [slot1Q, qsub_val, qmul_val, qadd_val, qmul_val, qmul_val, qadd_val] at this
  have e1 := compress_denQ δ eK eF 8 (recQ F op0PathRec)
  have e2 := compress_denQ δ eK eF 10 (recQ F tailRec)
  rw [← e1, ← e2] at this
  exact sub_eq_zero.mp this

/-- **Slot 2** (`s6` export / `s9` path). -/
theorem slot2Q_sound (eK : Env K) (eF : Env F) (h : Q.IsZero (slot2Q F δ) eK eF) :
    Q.val δ (invQ F (lookupInvBase 1) (invImBase 2)) eK eF *
      (Q.val δ (qlift F (selVar 6)) eK eF *
          FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF ttRec) +
        Q.val δ (qlift F (actP9 F)) eK eF *
          FiniteIO.compress (coinsQ δ eK eF) (recValQ δ eK eF op9PathRec)) =
      Q.val δ (qlift F (selVar 6)) eK eF + Q.val δ (qlift F (actP9 F)) eK eF := by
  have := (Q.isZero_iff δ eK eF _).mp h
  rw [slot2Q, qsub_val, qmul_val, qadd_val, qmul_val, qmul_val, qadd_val] at this
  have e1 := compress_denQ δ eK eF 10 (recQ F ttRec)
  have e2 := compress_denQ δ eK eF 8 (recQ F op9PathRec)
  rw [← e1, ← e2] at this
  exact sub_eq_zero.mp this

end Slots

section AccQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

theorem sum_mk {ι : Type*} (s : Finset ι) (f g : ι → K) :
    ∑ i ∈ s, Quad.mk (algebraMap F K δ) (f i) (g i) =
      Quad.mk (algebraMap F K δ) (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Quad.mk_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih,
      Quad.mk_add]

/-- The `𝕂′` per-row term: the Re / Im `𝕂`-terms as a `Quad.mk`. -/
def termQ (slotsRe slotsIm : List (Slot F)) (env : Env F) : Quad (algebraMap F K δ) :=
  Quad.mk _ (termVal b slotsRe env) (termVal b slotsIm env)

/-- **The `𝕂′` accumulator over `N` rows** (export or path, given its two halves): the Re half and
the Im half of `accGatesT` are each an `acc_rows` accumulator over `𝕂`; the terms sum in `𝕂′` to
the `𝕂′` terminal public `Quad.mk (Re pub) (Im pub)`. -/
theorem accQ_rows (slotsRe slotsIm : List (Slot F)) (accRe accIm pubRe pubIm : ℕ) (N : ℕ) (hN : 0 < N)
    (envs : ℕ → Env F)
    (hRe : ∀ i < N, ∀ g ∈ accGates 3 slotsRe accRe pubRe, g.eval (envs i) = 0)
    (hIm : ∀ i < N, ∀ g ∈ accGates 3 slotsIm accIm pubIm, g.eval (envs i) = 0)
    (hshift : ∀ i, i + 1 < N → ∀ j, (envs i).traceNext j = (envs (i + 1)).trace j)
    (hfirst : (envs 0).trace 11 = 1)
    (hnotLast : ∀ i, i + 1 < N → (envs i).trace 12 = 0) (hlast : (envs (N - 1)).trace 12 = 1) :
    ∑ i ∈ Finset.range N, termQ δ b slotsRe slotsIm (envs i) =
      Quad.mk _ (limbVal b (envs (N - 1)).pub pubRe) (limbVal b (envs (N - 1)).pub pubIm) := by
  unfold termQ
  rw [sum_mk, acc_rows b slotsRe accRe pubRe N hN envs hRe hshift hfirst hnotLast hlast _ rfl,
    acc_rows b slotsIm accIm pubIm N hN envs hIm hshift hfirst hnotLast hlast _ rfl]

/-- The four halves of `accGatesT` separated. -/
theorem accGatesT_halves (envF : Env F) (h : ∀ g ∈ (accGatesT : List (CoeffExpr F)), g.eval envF = 0) :
    (∀ g ∈ accGates 3 (accSlotsX : List (Slot F)) accExportBase rhoExportPub, g.eval envF = 0) ∧
    (∀ g ∈ accGates 3 (accSlotsXIm : List (Slot F)) accImExport rhoExportImPub, g.eval envF = 0) ∧
    (∀ g ∈ accGates 3 (accSlotsPT : List (Slot F)) accPathBase rhoPathPub, g.eval envF = 0) ∧
    (∀ g ∈ accGates 3 (accSlotsPImT : List (Slot F)) accImPath rhoPathImPub, g.eval envF = 0) := by
  refine ⟨fun g hg => h g ?_, fun g hg => h g ?_, fun g hg => h g ?_, fun g hg => h g ?_⟩ <;>
    simp only [accGatesT, List.mem_append] <;> tauto

/-- **Export accumulator at `𝕂′`**, from `accGatesT` at every row. -/
theorem accGatesT_export_rows (N : ℕ) (hN : 0 < N) (envs : ℕ → Env F)
    (hg : ∀ i < N, ∀ g ∈ (accGatesT : List (CoeffExpr F)), g.eval (envs i) = 0)
    (hshift : ∀ i, i + 1 < N → ∀ j, (envs i).traceNext j = (envs (i + 1)).trace j)
    (hfirst : (envs 0).trace 11 = 1)
    (hnotLast : ∀ i, i + 1 < N → (envs i).trace 12 = 0) (hlast : (envs (N - 1)).trace 12 = 1) :
    ∑ i ∈ Finset.range N, termQ δ b accSlotsX accSlotsXIm (envs i) =
      Quad.mk _ (limbVal b (envs (N - 1)).pub rhoExportPub)
        (limbVal b (envs (N - 1)).pub rhoExportImPub) :=
  accQ_rows δ b _ _ accExportBase accImExport rhoExportPub rhoExportImPub N hN envs
    (fun i hi => (accGatesT_halves (envs i) (hg i hi)).1)
    (fun i hi => (accGatesT_halves (envs i) (hg i hi)).2.1) hshift hfirst hnotLast hlast

/-- **Path accumulator at `𝕂′`.** -/
theorem accGatesT_path_rows (N : ℕ) (hN : 0 < N) (envs : ℕ → Env F)
    (hg : ∀ i < N, ∀ g ∈ (accGatesT : List (CoeffExpr F)), g.eval (envs i) = 0)
    (hshift : ∀ i, i + 1 < N → ∀ j, (envs i).traceNext j = (envs (i + 1)).trace j)
    (hfirst : (envs 0).trace 11 = 1)
    (hnotLast : ∀ i, i + 1 < N → (envs i).trace 12 = 0) (hlast : (envs (N - 1)).trace 12 = 1) :
    ∑ i ∈ Finset.range N, termQ δ b accSlotsPT accSlotsPImT (envs i) =
      Quad.mk _ (limbVal b (envs (N - 1)).pub rhoPathPub)
        (limbVal b (envs (N - 1)).pub rhoPathImPub) :=
  accQ_rows δ b _ _ accPathBase accImPath rhoPathPub rhoPathImPub N hN envs
    (fun i hi => (accGatesT_halves (envs i) (hg i hi)).2.2.1)
    (fun i hi => (accGatesT_halves (envs i) (hg i hi)).2.2.2) hshift hfirst hnotLast hlast

/-- The Re / Im halves of `invQ` over `𝕂′` at the gathered environment are the `𝕂` limb readings
at the Re and Im inverse columns (so `termQ` is the `𝕂′` sum `Σ_s act_s · inv′_s`). -/
theorem val_invQ (envF : Env F) (re im : ℕ) :
    Q.val δ (invQ F re im) (gatherEnv b envF) envF =
      Quad.mk _ (limbVal b envF.trace re) (limbVal b envF.trace im) := by
  simp only [invQ, qcol, Q.val, MixedExpr.eval, limbVal]
  rfl

end AccQ

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
