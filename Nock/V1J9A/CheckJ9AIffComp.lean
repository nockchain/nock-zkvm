/-
  Nock/V1J9A/CheckJ9AIffComp.lean

FINDING (F3): `Hc` as stated in `checkJ9A_iff_of_comp` (`∀ hv, compOK I = true ↔ Sat …`) is NOT provable from
  `ValidJ9A` alone: `computeChipX9_iff` needs `Function.Injective (mkPbA I hv).nodes` (nodes `ω^i`, `i < n`), which
  `validB`/`OrbOK` do not give (n is not tied to the order of ω).  Adjacency is automatic and, since `TabX9.env`
  extrapolates the last row (L5b), F2 (the cyclic wrap) is gone.  Injectivity IS available from the static block
  `StaticJ9A` (field `hinjX`), which `checkJ9A` checks before the chips; so `Hc` is proved UNDER `StaticJ9A`
  (`hcX9`), and `checkJ9AX_iff` re-runs the body of `checkJ9A_iff_of_comp` (copied, with `Hc hv hs'`) — no extra
  hypothesis on the final statement.
-/
import Nock.V1J9A.GenJ9AX
import Nock.V1J9A.CheckJ9AIff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.V1J9A.CheckJ9AIffComp

open Nock Nock.Reified Nock.Framework Nock.Walk Nock.TraceGenExe Nock.Field Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.V1Check
open Nock.V1J8.CompX (ofFn_get_map mapC_id firstMaskE lastMaskE)
open Nock.V1J9A.CompX9
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff

/-- The twin compute table as a `TableData` with the chip's (permuted RAP-order) gates. -/
noncomputable def _root_.Nock.V1J9A.CompX9.TabX9.toT {n : ℕ} (T : TabX9 n) : TableData (ZMod p) n :=
  ⟨137, T.nodes, T.ω, T.cols, gatesHX9P powerBasis3 deltaF, T.chal, T.pub,
    [(17, firstMaskE n), (18, lastMaskE n)]⟩

/-- **The executable twin check is the table check**: `checkCompX9 T = true` iff every gate of the twin chip vanishes at every row of `T` (`T.toT.checkTable = true`). -/
theorem checkCompX9_iff {n : ℕ} (T : TabX9 n) : checkCompX9 T = true ↔ T.toT.checkTable = true := by
  have key : (∀ i : Fin n, ∀ g ∈ gatesHX9P (F := ZMod p) powerBasis3 deltaF, g.eval (T.env i) = 0) ↔
      (T.toT.gates.all fun g => (List.finRange n).all fun i => decide (g.eval (T.toT.env i) = 0)) = true := by
    simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
    exact ⟨fun h g hg i => h i g hg, fun h i g hg => h g hg i⟩
  unfold checkCompX9 TableData.checkTable
  rw [Bool.and_eq_true, Bool.and_eq_true, checkCompX9_gates_iff, key]
  exact Iff.rfl

/-- **`computeChipX9_iff`: the J-9 A twin compute chip, finitely.** -/
theorem computeChipX9_iff {n h : ℕ} (T : TabX9 n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (computeChipVCLHX9 hn T.nodes powerBasis3 deltaF T.chal T.pub orbit).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 hn T.nodes powerBasis3 deltaF T.chal T.pub orbit) P ↔
      checkCompX9 T = true := by
  rw [checkCompX9_iff]
  refine satisfies_iff_checkTable (RingHom.id (ZMod p)) T.toT _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · show List.ofFn (fun i : Fin (gatesHX9P (F := ZMod p) powerBasis3 deltaF).length =>
        coeffToMv T.chal T.pub ((gatesHX9P (F := ZMod p) powerBasis3 deltaF).get i)) = _
    refine (ofFn_get_map (gatesHX9P (F := ZMod p) powerBasis3 deltaF) _).trans ?_
    simp only [TabX9.toT, List.map_map]
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply, mapC_id]
    rfl
  · simp only [List.ofFn_succ, List.ofFn_zero, computeChipVCLHX9, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, TabX9.toT, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl)
    · show firstRowMask _ = _
      unfold firstRowMask
      congr 1
    · show lastRowMask hn _ = _
      unfold lastRowMask
      congr 1; funext i
      simp only [lastMaskE, Fin.ext_iff]
      have := i.2
      by_cases h : (i : ℕ) + 1 = n
      · simp [h]; omega
      · simp [h]; omega

section Iff
variable [iA : Algebra Nock.Atoms.Fp KQ] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- The executable twin compute table of the input (as wired in `checkJ9AX`). -/
def tabOf (I : InJ9A) : TabX9 I.X.n :=
  ⟨(tabX9A I).nodes, (tabX9A I).ω, (tabX9A I).cols, (tabX9A I).chal, (tabX9A I).pub⟩

/-- **`Hc`, under the static block** (injectivity / adjacency of the compute nodes): `checkCompX9` decides the twin
compute RAP. -/
theorem hcX9 (I : InJ9A) (hv : ValidJ9A I) (hs : StaticJ9A (mkPbA I hv) I.c I.M.m I.toRows I.g) :
    checkCompX9 (tabOf I) = true ↔ RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (mkPbA I hv).hn (mkPbA I hv).nodes powerBasis3 deltaF (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ)) (mkPbA I hv).orbit)
      (qX9 deltaF powerBasis3 (mkPbA I hv) I.toTr (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ))) := by
  have hcv := Nock.V1J8.Check.chalVJ8_eq I.χ
  have hpv := Nock.V1J9.Check9.pubVJ9_eq I.c I.M.m I.M.ρ I.M.ρS I.χ
  have eX := computeChipX9_iff (tabOf I) hv.nX (mkOrbit I.X hv.oX)
    (qX9 deltaF powerBasis3 (mkPbA I hv) I.toTr (tabOf I).chal (tabOf I).pub)
    hs.1 (Nock.V1J8.Check.adj_of I.X hv.oX hs.2.1) rfl (fun j => rfl)
  rw [← eX]
  show RAP.SatisfiesWithPreprocessing _ _ ↔ RAP.SatisfiesWithPreprocessing _ _
  rw [hcv]
  erw [hpv]
  exact Iff.rfl

/-- **`checkJ9AX_iff`**: the wired J-9 A checker holds iff the input is valid and `AcceptsJ9A` holds at the verifier
data built from the input (under the registry premise only). -/
theorem checkJ9AX_iff (I : InJ9A) (Rg : Nock.Jet.Registry) (hreg : RegOK I.toInJ8 Rg) :
    GenJ9AX.checkJ9AX I = true ↔ ∃ hv : ValidJ9A I,
      AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 (mkPbA I hv) Rg I.c (toχ I.χ) I.toMsg I.toTr I.toRows I.g := by
  unfold GenJ9AX.checkJ9AX checkJ9A
  constructor
  · intro h
    by_cases hb : validB I.toInJ8 = true
    · rw [dif_pos hb] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨hax, hs⟩, hp⟩, hc⟩ := h
      have hv : ValidJ9A I := ValidJ9A.mk' I ((validB_iff _).mp hb) ((validAXSPB_iff I).mp hax)
      have hs' := (checkStaticJ9A_iff (mkPbA I hv) I.c I.M.m I.toRows I.g).mp hs
      refine ⟨hv, (acceptsJ9A_iff deltaF powerBasis3 _ Rg I.c (toχ I.χ) I.toMsg I.toTr I.toRows I.g).mpr
        ⟨hs', (checkPubJ9AE_iff (mkPbA I hv) I.c I.χ I.M I.pubsX I.pubsS).mp hp, ?_⟩⟩
      exact (chipsBJ9A_iff _ I hv Rg hreg hs' (hcX9 I hv hs')).mp hc
    · rw [dif_neg hb] at h; exact absurd h Bool.false_ne_true
  · rintro ⟨hv, h⟩
    obtain ⟨hs, hp, hc⟩ := (acceptsJ9A_iff deltaF powerBasis3 _ Rg I.c (toχ I.χ) I.toMsg I.toTr I.toRows I.g).mp h
    have hb : validB I.toInJ8 = true := (validB_iff _).mpr hv.toValidJ8
    rw [dif_pos hb]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨(validAXSPB_iff I).mpr ⟨hv.nAX, hv.oAX, hv.nSP, hv.oSP⟩,
      (checkStaticJ9A_iff (mkPbA I hv) I.c I.M.m I.toRows I.g).mpr hs⟩,
      (checkPubJ9AE_iff (mkPbA I hv) I.c I.χ I.M I.pubsX I.pubsS).mpr hp⟩,
      (chipsBJ9A_iff _ I hv Rg hreg hs (hcX9 I hv hs)).mpr hc⟩

end Iff

end Nock.V1J9A.CheckJ9AIffComp

section Axioms
open Nock.V1J9A.CheckJ9AIffComp
#print axioms checkCompX9_iff
#print axioms computeChipX9_iff
#print axioms hcX9
#print axioms checkJ9AX_iff
end Axioms
