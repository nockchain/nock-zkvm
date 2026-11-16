/-
  Nock/V1J9/CheckJ9.lean

  **The assembled executable J-9 checker.**

  * **`seedJ9E`** / **`pubVJ9E`** (the J-9 compute publics, executably) with `seedJ9E_spec` / **`pubVJ9E_spec`**
    (`= pubVJ9 deltaF powerBasis3 …` at the lifted `ρ`, `ρS`).
  * **`checkJ9`** = `validB ∧ checkStaticJ9 ∧ checkPubJ9E ∧ chipsB9` (the seven chip checks of `checkJ8`, the compute
    at `pubVJ9E`), on the J-8 input type `InJ8`.
  * **`checkJ9_iff`**: under the registry premise, `checkJ9 I = true ↔ ∃ hv : ValidJ8 I, AcceptsJ9V deltaF powerBasis3
    (mkPb I hv) Rg I.c (toχ I.χ) I.M.toMsg (mkTr I) I.r I.g`.
-/
import Nock.V1J9.StaticJ9
import Nock.V1J8.CheckJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J9.Check9

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (chalsVCL)
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX qM qW qJ qA qV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L (qAL)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (labelJ9 seedJ9 pubVJ9)
open Nock.V1J8.Exe
open Nock.V1J8.Check
open Nock.V1J8.CompX (TabX checkCompX computeChipX_iff powK toK_powK)
open Nock.V1J8.MemX (TabM checkCellKW checkWalkJ8 checkJOK checkAtomHQ checkAtomHQL checkAWOK prep2 prep3 prepJ
  checkCellKW_iff checkWalkJ8_iff checkJOK_iff checkAtomHQ_iff checkAtomHQL_iff checkAWOK_iff)
open Nock.V1J9 Nock.V1J9.Exe9

/-! ## 1. The J-9 compute publics, executably -/

/-- **The J-9 compute walk seed, executable** (`seedJ9`: `αW · Σ_k γW^k · lift(labelJ9_k)`). -/
def seedJ9E (c : P8PublicClaim) (m : ClaimMsgVS) (χe : CoinsE) : K3 :=
  χe ⟨13, by decide⟩ * sumK3 ((labelJ9 p c m).zipIdx.map fun q =>
    powK (χe ⟨14, by decide⟩) q.2 * g3 (Gold.ofZ q.1))

theorem seedJ9E_spec (c : P8PublicClaim) (m : ClaimMsgVS) (χe : CoinsE) :
    K3.toK (seedJ9E c m χe) = seedJ9 (p := p) (K := KC) c m (toVS (toVSQ (toχ χe))) := by
  unfold seedJ9E seedJ9
  rw [K3.toK_mul, toK_sumK3, List.map_map]
  congr 2
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp_apply, K3.toK_mul, toK_powK, toK_g3, Gold.toZ_ofZ]
  rfl

/-- **The J-9 compute publics, executable**: `labelJ9` at `0..5`, the seed `seedJ9E` at `9..11`, `pubVJ8E` else. -/
def pubVJ9E (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → K6) (ρS : K6) (χe : CoinsE) (j : ℕ) : ZMod p :=
  if j < 6 then (labelJ9 p c m).getD j 0
  else if 9 ≤ j ∧ j < 12 then limbZ (seedJ9E c m χe) (j - 9)
  else pubVJ8E c m ρ ρS χe j

theorem pubVJ9E_spec (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → K6) (ρS : K6) (χe : CoinsE) (j : ℕ) :
    pubVJ9E c m ρ ρS χe j =
      pubVJ9 deltaF powerBasis3 c m (fun i => K6.toQ (ρ i)) (K6.toQ ρS) (toχ χe) j := by
  unfold pubVJ9E pubVJ9
  split_ifs with h1 h2
  · rfl
  · rw [← seedJ9E_spec, coord_K]
  · exact pubVJ8E_spec c m ρ ρS χe j

theorem pubVJ9_eq (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → K6) (ρS : K6) (χe : CoinsE) :
    pubVJ9 deltaF powerBasis3 c m (fun i => K6.toQ (ρ i)) (K6.toQ ρS) (toχ χe) = pubVJ9E c m ρ ρS χe :=
  funext fun j => (pubVJ9E_spec c m ρ ρS χe j).symm

/-! ## 2. The checker -/

def tabX9 (I : InJ8) : TabX I.X.n :=
  ⟨nodesOf I.X, I.X.ω.toZ, I.X.cols, fun j => (chalVJ8E I.χ j).toZ, pubVJ9E I.c I.M.m I.M.ρ I.M.ρS I.χ⟩

/-- **The seven chip checks** (`chipsB` with the compute at `pubVJ9E`). -/
def chipsB9 (I : InJ8) : Bool :=
  checkCompX (tabX9 I) && checkCellKW (tabC I) && checkWalkJ8 I.kroots (tabW I) && checkJOK (tabJ I) &&
  checkAtomHQ (tabA I) && checkAWOK I.krootsV (tabV I) && checkAtomHQL (tabA I)

/-- **The executable J-9 checker**: validity, the static block, the public equations, the chips. -/
def checkJ9 (I : InJ8) : Bool :=
  if hv : validB I = true then
    checkStaticJ9 (mkPb I ((validB_iff I).mp hv)) I.c I.M.m I.r I.g &&
    checkPubJ9E (mkPb I ((validB_iff I).mp hv)) I.c I.χ I.M && chipsB9 I
  else false

/-! ## 3. `checkJ9_iff` -/

section Iff
variable [iA : Algebra Nock.Atoms.Fp KQ] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- **The chip block**: under the static block, `chipsB9` is exactly `ChipsJ9` (the registry premise given). -/
theorem chipsB9_iff (I : InJ8) (hv : ValidJ8 I) (Rg : Nock.Jet.Registry) (hreg : RegOK I Rg)
    (hs : StaticJ9 (mkPb I hv) I.c I.M.m I.r I.g) :
    chipsB9 I = true ↔
      ChipsJ9 deltaF powerBasis3 (mkPb I hv) Rg I.c (toχ I.χ) I.M.toMsg (mkTr I) := by
  have eX := computeChipX_iff (tabX9 I) hv.nX (mkOrbit I.X hv.oX)
    (qX deltaF powerBasis3 (mkPb I hv) (mkTr I) (tabX9 I).chal (tabX9 I).pub)
    hs.hinjX (adj_of I.X hv.oX hs.hadjX) rfl (fun j => rfl)
  have eC := checkCellKW_iff (tabC I) hv.nC (mkOrbit I.C hv.oC)
    (qM deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabC I).chals i)) (fun i => K3.toK ((tabC I).pubs i)))
    hs.hinjC (adj_of I.C hv.oC hs.hadjC) rfl rfl (fun j => rfl)
  have eW := checkWalkJ8_iff I.kroots (tabW I) hv.nW (mkOrbit I.W hv.oW)
    (qW deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabW I).chals i)) (fun i => K3.toK ((tabW I).pubs i)))
    hs.hinjW (adj_of I.W hv.oW hs.hadjW) rfl rfl (fun j => rfl)
  have eJ := checkJOK_iff (tabJ I) (mkOrbit I.J hv.oJ) I.lay
    (qJ deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabJ I).chals i)) (fun i => K3.toK ((tabJ I).pubs i)))
    rfl rfl (fun j => rfl)
  have eA := checkAtomHQ_iff (tabA I) hv.nA (mkOrbit I.A hv.oA)
    (qA deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabA I).chals i)) (fun i => K3.toK ((tabA I).pubs i)))
    hs.hinjA (adj_of I.A hv.oA hs.hadjA) rfl rfl (fun j => rfl)
  have eL := checkAtomHQL_iff (tabA I) hv.nA (mkOrbit I.A hv.oA)
    (qAL deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabA I).chals i))
      (fun i => K3.toK ((tabA I).pubs i)))
    hs.hinjA (adj_of I.A hv.oA hs.hadjA) rfl rfl (fun j => rfl)
  have eV := checkAWOK_iff I.krootsV (tabV I) hv.nV (mkOrbit I.V hv.oV)
    (qV deltaF powerBasis3 (mkPb I hv) (mkTr I) (fun i => K3.toK ((tabV I).chals i)) (fun i => K3.toK ((tabV I).pubs i)))
    rfl rfl (fun j => rfl)
  have hM := chalsMJ8_eq I.χ
  have hAZ := chalsAJ8Z_eq I.χ
  have hJJ := chalsJJ8_eq I.χ
  have hcv := chalVJ8_eq I.χ
  have hpv := pubVJ9_eq I.c I.M.m I.M.ρ I.M.ρS I.χ
  unfold chipsB9
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨hX, hC⟩, hW⟩, hJ⟩, hA⟩, hV⟩, hL⟩
    obtain ⟨sX, bX⟩ := id (eX.mpr hX)
    obtain ⟨sC, bC⟩ := eC.mpr hC
    obtain ⟨sW, bW⟩ := eW.mpr hW
    obtain ⟨sA, bA⟩ := eA.mpr hA
    obtain ⟨sL, bL⟩ := eL.mpr hL
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hreg⟩
    · show RAP.SatisfiesWithPreprocessing _ _
      rw [hcv]
      erw [hpv]
      exact ⟨sX, bX⟩
    · rw [hM]; exact sC
    · rw [hM]; exact bC
    · rw [hM]; exact sW
    · rw [hM]; exact bW
    · rw [hJJ]; exact eJ.mpr hJ
    · rw [hAZ]; exact sA
    · rw [hAZ]; exact bA
    · rw [hAZ]; exact eV.mpr hV
    · rw [hAZ]; exact sL
    · rw [hAZ]; exact bL
  · intro k
    have kX := k.hsatX
    have kC := k.hsatC
    have kbC := k.hbindC
    have kW := k.hsatW
    have kbW := k.hbindW
    have kJ := k.hJk
    have kA := k.hsatA
    have kbA := k.hbindA
    have kV := k.hVk
    have kL := k.hsatL
    have kbL := k.hbindL
    rw [hcv] at kX
    erw [hpv] at kX
    rw [hM] at kC kbC kW kbW
    rw [hJJ] at kJ
    rw [hAZ] at kA kbA kV kL kbL
    exact ⟨⟨⟨⟨⟨⟨eX.mp kX, eC.mp ⟨kC, kbC⟩⟩, eW.mp ⟨kW, kbW⟩⟩, eJ.mp kJ⟩, eA.mp ⟨kA, kbA⟩⟩, eV.mp kV⟩,
      eL.mp ⟨kL, kbL⟩⟩

/-- **`checkJ9_iff`: the J-9 checker is exactly the J-9 verifier.**  Under the registry premise, `checkJ9 I = true`
iff the input is valid and `AcceptsJ9V` holds at the verifier data `mkPb I`, the coins `toχ I.χ`, the message
`I.M.toMsg` and the traces `mkTr I` (the interpolants of the rows), all built from the input. -/
theorem checkJ9_iff (I : InJ8) (Rg : Nock.Jet.Registry) (hreg : RegOK I Rg) :
    checkJ9 I = true ↔ ∃ hv : ValidJ8 I,
      AcceptsJ9V.AcceptsJ9V deltaF powerBasis3 (mkPb I hv) Rg I.c (toχ I.χ) I.M.toMsg (mkTr I) I.r I.g := by
  unfold checkJ9
  constructor
  · intro h
    by_cases hb : validB I = true
    · rw [dif_pos hb] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hs, hp⟩, hc⟩ := h
      have hv := (validB_iff I).mp hb
      have hs' := (checkStaticJ9_iff _ _ _ _ _).mp hs
      refine ⟨hv, (acceptsJ9V_iff_exe _ Rg I.c I.χ I.M (mkTr I) I.r I.g).mpr ⟨hs, hp, ?_⟩⟩
      exact (chipsB9_iff I hv Rg hreg hs').mp hc
    · rw [dif_neg hb] at h; exact absurd h Bool.false_ne_true
  · rintro ⟨hv, h⟩
    obtain ⟨hs, hp, hc⟩ := (acceptsJ9V_iff_exe _ Rg I.c I.χ I.M (mkTr I) I.r I.g).mp h
    have hb : validB I = true := (validB_iff I).mpr hv
    rw [dif_pos hb]
    simp only [Bool.and_eq_true]
    have hs' := (checkStaticJ9_iff _ _ _ _ _).mp hs
    exact ⟨⟨hs, hp⟩, (chipsB9_iff I hv Rg hreg hs').mpr hc⟩

end Iff

end Nock.V1J9.Check9
