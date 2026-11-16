/-
  Nock/NockVMROM/Thm54/P8Core/SVCompute/ChipData.lean

  **Route-2 compute generalization — `ChipData` / `ChipLayout`.**

  * `SharedGateSet`, `ChipLayout`: what the SHARED compute theorems read of a chip — the width,
    the round map, the base prefix `13 ≤ w`, the `𝕂`-role block (`role r = 13 + 3 r`), the B0 row
    serial column, the gate families, plus the three facts a chip builder must supply
    (`build_w`, `sat_iff`, `masks_of_bind`; V4's obligations).
  * `chipOf D L c = L.build D c`; `layout309` (the live package chip `computeChipAt`, physical
    width `303`, serial `302`).
  * `toCD`, `rowEnvAtD`, `rowEnvD`, `RowFacts` (the per-row facts the chain skeletons read) and
    the bridges to the live package-typed definitions (`rfl`).
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0
import Nock.NockVMROM.Thm54.Unhosted309Realization
import Nock.NockVMROM.Thm54.P8Core.RepartitionedStaging

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVCompute

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler

noncomputable section

/-! ## 1. `ChipData` -/

structure ChipData (F K : Type) [Field F] [Field K] [Algebra F K] (h : ℕ) where
  N : ℕ
  hN : 0 < N
  nodes : Fin N → F
  basis : Module.Basis (Fin 3) F K
  orbit : StrictExtension.StrictOrbitDomain F 3 h
  claim : P8PublicClaim
  pub : ℕ → F
  chal : ℕ → F

section ToCD

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}

/-- The `ChipData` of the package's compute side (the only place a package is read). -/
def toCD (O : OptimizedStrictNockVMROMPackage F K hOrb) : ChipData F K hOrb where
  N := O.family.problem.cfg.compRows
  hN := O.family.problem.cfg.compRows_pos
  nodes := O.computeNodes
  basis := O.basis
  orbit := O.orbit
  claim := O.verifier.raw.claim
  pub := O.computePublic
  chal := O.computeChallenge

end ToCD

/-- The row-adjacency premise (`computeAdjacentOrbit`), as a property of the datum. -/
def ChipData.Adjacent {F K : Type} [Field F] [Field K] [Algebra F K] {h : ℕ}
    (D : ChipData F K h) : Prop :=
  ∀ (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N), D.nodes ⟨(i : ℕ) + 1, hi⟩ = D.orbit.ω * D.nodes i

/-- The row-injectivity premise (`computeNodes_injective`). -/
def ChipData.Injective {F K : Type} [Field F] [Field K] [Algebra F K] {h : ℕ}
    (D : ChipData F K h) : Prop :=
  Function.Injective D.nodes

section Pkg

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}

theorem toCD_adjacent (O : OptimizedStrictNockVMROMPackage F K hOrb) : (toCD O).Adjacent :=
  O.computeAdjacentOrbit

theorem toCD_injective (O : OptimizedStrictNockVMROMPackage F K hOrb) : (toCD O).Injective :=
  O.computeNodes_injective

end Pkg

/-! ## 2. The generic row environments -/

section Envs

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] {h : ℕ}

/-- The base-field family row environment at the tuple. -/
abbrev envFAtD (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F) {w : ℕ}
    (Qc : Fin w → F[X]) (i : Fin D.N) : Env F :=
  envOfTrace Qc D.orbit.ω (D.nodes i) (computeChalValOfTuple D.basis c)
    (computePublicOfTuple D.basis D.claim D.pub c)

def rowEnvAtD (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F) {w : ℕ}
    (Qc : Fin w → F[X]) (i : Fin D.N) : CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv D.basis
    (envOfTrace Qc D.orbit.ω (D.nodes i) (computeChalValOfTuple D.basis c)
      (computePublicOfTuple D.basis D.claim D.pub c))

/-- The honest-chip gather of `Qc` (the package's own challenge and public maps). -/
def rowEnvD (D : ChipData F K h) {w : ℕ} (Qc : Fin w → F[X]) (i : Fin D.N) :
    CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv D.basis (envOfTrace Qc D.orbit.ω (D.nodes i) D.chal D.pub)

theorem rowEnvAtD_eq_gather (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F)
    {w : ℕ} (Qc : Fin w → F[X]) (i : Fin D.N) :
    rowEnvAtD D c Qc i = gatherCorrectedFinalTypedEnv D.basis (envFAtD D c Qc i) := rfl

end Envs

/-! ## 3. `ChipLayout` -/

section Layout

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] {h : ℕ}

/-- The gate families the SHARED theorems invoke: the base transition, the walk / chain core, the
accumulator anchors and the serial (exponent carrier) step. -/
structure SharedGateSet (F : Type) [Field F] where
  base : List (CoeffExpr F)
  walk : List (CoeffExpr F)
  acc : List (CoeffExpr F)
  serial : List (CoeffExpr F)

/-- All members of a gate set, as one list. -/
def SharedGateSet.toList {F : Type} [Field F] (G : SharedGateSet F) : List (CoeffExpr F) :=
  G.base ++ G.walk ++ G.acc ++ G.serial

/-- **What the SHARED compute theorems read of a compute chip.**  The chip builder `build`, its
width `w`, the round map, the base prefix (state one-hot / fanout / count cells `0..10`, masks
`11`, `12`), the `𝕂`-role block, the B0 row-serial column and the gate families, plus the three
facts a builder must supply: its width (`build_w`), its satisfaction language (`sat_iff`: the
gathered source obligations at every row and the bound preprocessing; also every listed gate
evaluates to `0`), and the preprocessing masks (`masks_of_bind`). -/
structure ChipLayout (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] (h : ℕ) where
  w : ℕ
  colRound : Fin w → ℕ
  base : 13 ≤ w
  role : ℕ → ℕ
  role_eq : ∀ r, role r = 13 + 3 * r
  nRoles : ℕ
  roles_fit : 13 + 3 * nRoles ≤ w
  serial : Fin w
  serial_round0 : colRound serial = 0
  gates : ChipData F K h → SharedGateSet F
  allGates : ChipData F K h → List (CoeffExpr F)
  build : ChipData F K h → OptimizedProductionChallengeTuple K F → FixedPreprocessingRAP F
  build_w : ∀ D c, (build D c).rap.w = w
  sat_iff : ∀ (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F)
      (Q : Fin (build D c).rap.w → F[X]),
    RAP.SatisfiesWithPreprocessing (build D c) Q ↔
      ((build D c).BindsPreprocessing Q ∧
        ∀ x ∈ rowNodeSet D.nodes,
          CorrectedComputeSourceObligations D.N
            (gatherCorrectedFinalTypedEnv D.basis
              (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
                (computePublicOfTuple D.basis D.claim D.pub c)))
            (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
              (computePublicOfTuple D.basis D.claim D.pub c)) ∧
          ∀ g ∈ allGates D,
            g.eval (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
              (computePublicOfTuple D.basis D.claim D.pub c)) = 0)
  masks_of_bind : ∀ (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F)
      (Q : Fin (build D c).rap.w → F[X]), (build D c).BindsPreprocessing Q →
    ∀ (h11 : 11 < (build D c).rap.w) (h12 : 12 < (build D c).rap.w),
      Q ⟨11, h11⟩ = firstRowMask D.nodes ∧ Q ⟨12, h12⟩ = lastRowMask D.hN D.nodes

/-- **The chip of a datum at a layout and a tuple** (`ProductionNamedComputeRAP…` at `309`). -/
def chipOf (D : ChipData F K h) (L : ChipLayout F K h) (c : OptimizedProductionChallengeTuple K F) :
    FixedPreprocessingRAP F :=
  L.build D c

theorem chipOf_w (D : ChipData F K h) (L : ChipLayout F K h)
    (c : OptimizedProductionChallengeTuple K F) : (chipOf D L c).rap.w = L.w :=
  L.build_w D c

/-- `L.gates ⊆ (chipOf D L c).gates`: every shared gate is a gate of the chip. -/
def ChipLayout.GatesOK (L : ChipLayout F K h) (D : ChipData F K h) : Prop :=
  ∀ g ∈ (L.gates D).toList, g ∈ L.allGates D

end Layout

/-! ## 4. The two layouts at the existing chips -/

section Layouts

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] {h : ℕ}

/-- The round map shared by both widths (`RepartitionedStaging.newComputeColRound`). -/
def colRoundOf (w : ℕ) : Fin w → ℕ := fun j => RepartitionedStaging.newComputeColRound j

theorem colRound_serial : RepartitionedStaging.newComputeColRound 302 = 0 := by decide

/-- The gate families of the deployed compute chip: base transition, the walk / chain core, the
accumulator anchors (`correctedEndpoint2`) and the exponent carrier gates. -/
def gates309 (D : ChipData F K h) : SharedGateSet F where
  base := OptimizedComputeFinal.finalBaseTransitionGates (F := F) D.N
  walk := correctedCore D.basis
  acc := correctedCompileList D.basis correctedEndpoint2
  serial := computeExpGates (F := F)

theorem gates309_sub (D : ChipData F K h) :
    ∀ g ∈ (gates309 D).toList, g ∈ correctedFinalComputeAllGates D.N D.basis := by
  intro g hg
  simp only [SharedGateSet.toList, gates309, List.mem_append, correctedFinalComputeAllGates] at hg ⊢
  tauto

/-- **The live package compute chip** (`computeChipAt`, physical width `303`, serial column `302`).
Named `layout309` for the design's `chipOf (toCD O) layout309 = computeChipAt …` bridge; the
package chip itself is `303` columns wide (the `309`-wide chip is `layoutUn309`). -/
def layout309 : ChipLayout F K h where
  w := 303
  colRound := colRoundOf 303
  base := by norm_num
  role := fun r => 13 + 3 * r
  role_eq := fun _ => rfl
  nRoles := 63
  roles_fit := by norm_num
  serial := ⟨302, by norm_num⟩
  serial_round0 := colRound_serial
  gates := gates309
  allGates := fun D => correctedFinalComputeAllGates D.N D.basis
  build := fun D c =>
    DeployedChipFamily.computeChipAt D.hN D.nodes D.basis
      (computePublicOfTuple D.basis D.claim D.pub c) D.orbit c
  build_w := fun _ _ => rfl
  sat_iff := by
    intro D c Q
    have key := productionNamedComputeRAP_satisfies_iff_compiledLanguage D.hN D.nodes D.basis
      (computeChalValOfTuple D.basis c) (computePublicOfTuple D.basis D.claim D.pub c) D.orbit Q
    have key2 := productionNamedComputeRAP_satisfies_iff_sourceLanguage D.hN D.nodes D.basis
      (computeChalValOfTuple D.basis c) (computePublicOfTuple D.basis D.claim D.pub c) D.orbit Q
    change RAP.SatisfiesWithPreprocessing (ProductionNamedComputeRAP D.hN D.nodes D.basis
      (computeChalValOfTuple D.basis c) (computePublicOfTuple D.basis D.claim D.pub c) D.orbit) Q ↔ _
    constructor
    · intro hs
      have hl := key.1 hs
      have hsrc := key2.1 hs
      refine ⟨hsrc.1, fun x hx => ⟨hsrc.2 x hx, fun g hg => hl.2 x hx g hg⟩⟩
    · rintro ⟨hb, hall⟩
      refine key.2 ⟨hb, fun x hx g hg => (hall x hx).2 g hg⟩
  masks_of_bind := by
    intro D c Q hb h11 h12
    have h0 := hb ⟨0, by change 0 < 2; norm_num⟩
    have h1 := hb ⟨1, by change 1 < 2; norm_num⟩
    exact ⟨h0, h1⟩


/-- **`layoutVCL`, a STUB for V4**: the layout of a compute chip of arbitrary width `w` whose B0 row
serial sits at the TAIL column `w - 1` (round `0`), with the role block `13 + 3 r` and the gate
families (base, walk, accumulator, serial step) supplied by the chip.  V4 instantiates it by giving
its builder, width, round map and gate lists together with the three facts a builder must supply
(`build_w`, `sat_iff`, `masks_of_bind`); nothing here is a theorem about a particular chip.  (The
carrier twins that read the typed environment's `expCol` need `serial = computeExpCol`, i.e.
`w = 303`; a VCL chip with another tail column reads its serial through its own typed environment.) -/
def layoutVCL (w : ℕ) (hw : 14 ≤ w) (colRound : Fin w → ℕ)
    (hround : colRound ⟨w - 1, by omega⟩ = 0)
    (nRoles : ℕ) (hroles : 13 + 3 * nRoles ≤ w)
    (gates : ChipData F K h → SharedGateSet F) (allGates : ChipData F K h → List (CoeffExpr F))
    (build : ChipData F K h → OptimizedProductionChallengeTuple K F → FixedPreprocessingRAP F)
    (build_w : ∀ D c, (build D c).rap.w = w)
    (sat_iff : ∀ (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F)
      (Q : Fin (build D c).rap.w → F[X]),
      RAP.SatisfiesWithPreprocessing (build D c) Q ↔
        ((build D c).BindsPreprocessing Q ∧
          ∀ x ∈ rowNodeSet D.nodes,
            CorrectedComputeSourceObligations D.N
              (gatherCorrectedFinalTypedEnv D.basis
                (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
                  (computePublicOfTuple D.basis D.claim D.pub c)))
              (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
                (computePublicOfTuple D.basis D.claim D.pub c)) ∧
            ∀ g ∈ allGates D,
              g.eval (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
                (computePublicOfTuple D.basis D.claim D.pub c)) = 0))
    (masks_of_bind : ∀ (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F)
      (Q : Fin (build D c).rap.w → F[X]), (build D c).BindsPreprocessing Q →
      ∀ (h11 : 11 < (build D c).rap.w) (h12 : 12 < (build D c).rap.w),
        Q ⟨11, h11⟩ = firstRowMask D.nodes ∧ Q ⟨12, h12⟩ = lastRowMask D.hN D.nodes) :
    ChipLayout F K h where
  w := w
  colRound := colRound
  base := by omega
  role := fun r => 13 + 3 * r
  role_eq := fun _ => rfl
  nRoles := nRoles
  roles_fit := hroles
  serial := ⟨w - 1, by omega⟩
  serial_round0 := hround
  gates := gates
  allGates := allGates
  build := build
  build_w := build_w
  sat_iff := sat_iff
  masks_of_bind := masks_of_bind

theorem layoutVCL_serial (w : ℕ) (hw : 14 ≤ w) (colRound : Fin w → ℕ)
    (hround : colRound ⟨w - 1, by omega⟩ = 0) (nRoles : ℕ) (hroles : 13 + 3 * nRoles ≤ w)
    (gates allGates build build_w sat_iff masks_of_bind) :
    ((layoutVCL (F := F) (K := K) (h := h) w hw colRound hround nRoles hroles gates allGates build
      build_w sat_iff masks_of_bind).serial : ℕ) = w - 1 := rfl

end Layouts


/-! ## 5. The per-row facts of an accepted trace, and the bridges -/

section Facts

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] {h : ℕ}

/-- **What an accepted trace gives at every row**: the gathered source obligations, every listed
gate at the row's environment, and the preprocessing masks at base columns `11`, `12`. -/
structure RowFacts (D : ChipData F K h) (L : ChipLayout F K h)
    (c : OptimizedProductionChallengeTuple K F) (Q : Fin (chipOf D L c).rap.w → F[X]) : Prop where
  obl : ∀ i : Fin D.N,
    CorrectedComputeSourceObligations D.N (rowEnvAtD D c Q i) (envFAtD D c Q i)
  gates : ∀ i : Fin D.N, ∀ g ∈ L.allGates D, g.eval (envFAtD D c Q i) = 0
  masks : ∀ i : Fin D.N,
    (rowEnvAtD D c Q i).baseTrace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
    (rowEnvAtD D c Q i).baseTrace 12 = (if (i : ℕ) = D.N - 1 then 1 else 0)

/-- **Acceptance gives the row facts** at any layout (the `ChipLayout` fields are the premises). -/
theorem RowFacts.of_sat (D : ChipData F K h) (L : ChipLayout F K h)
    (c : OptimizedProductionChallengeTuple K F) (Q : Fin (chipOf D L c).rap.w → F[X])
    (hinj : D.Injective) (hsat : RAP.SatisfiesWithPreprocessing (chipOf D L c) Q) :
    RowFacts D L c Q := by
  have hs := (L.sat_iff D c Q).1 hsat
  have hw : 12 < (chipOf D L c).rap.w := by
    rw [chipOf_w]; have := L.base; omega
  have hw11 : 11 < (chipOf D L c).rap.w := by omega
  obtain ⟨m0, m1⟩ := L.masks_of_bind D c Q hs.1 hw11 hw
  have hmem : ∀ i : Fin D.N, D.nodes i ∈ rowNodeSet D.nodes := fun i => by simp [rowNodeSet]
  refine ⟨fun i => (hs.2 _ (hmem i)).1, fun i => (hs.2 _ (hmem i)).2, fun i => ⟨?_, ?_⟩⟩
  · show (envOfTrace Q D.orbit.ω (D.nodes i) (computeChalValOfTuple D.basis c)
      (computePublicOfTuple D.basis D.claim D.pub c)).trace 11 = _
    simp only [envOfTrace, dif_pos hw11]
    rw [show Q ⟨11, hw11⟩ = firstRowMask D.nodes from m0, Nock.Framework.firstRowMask_eval _ hinj]
  · show (envOfTrace Q D.orbit.ω (D.nodes i) (computeChalValOfTuple D.basis c)
      (computePublicOfTuple D.basis D.claim D.pub c)).trace 12 = _
    simp only [envOfTrace, dif_pos hw]
    rw [show Q ⟨12, hw⟩ = lastRowMask D.hN D.nodes from m1, Nock.Framework.lastRowMask_eval _ _ hinj]
    simp only [Fin.ext_iff]

end Facts

/-! ## 6. Bridges to the live package-typed definitions (all `rfl`) -/

section Bridges

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}
  (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-- **The chip bridge**: `chipOf (toCD O) layout309` is the package's `computeChipAt`. -/
theorem chipOf_toCD_layout309 (c : OptimizedProductionChallengeTuple K F) :
    chipOf (toCD O) layout309 c =
      DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes O.basis
        (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c := rfl

/-- The family width of the package chip is the layout's. -/
theorem layout309_w : (layout309 (F := F) (K := K) (h := hOrb)).w = 303 := rfl

theorem rowEnvAtD_toCD (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (chipOf (toCD O) layout309 c).rap.w → F[X])
    (i : Fin O.family.problem.cfg.compRows) :
    rowEnvAtD (toCD O) c Qc i = FamilyEnvCore.rowEnvAt O c Qc i := rfl

/-- The honest-chip gather is `StrategyOfTracesLift.rowEnv`. -/
theorem rowEnvD_toCD
    (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos O.computeNodes O.basis
      O.computeChallenge O.computePublic O.orbit).rap.w → F[X])
    (i : Fin O.family.problem.cfg.compRows) :
    rowEnvD (toCD O) Qc i = StrategyOfTracesLift.rowEnv O Qc i := rfl

/-- The row facts at the package: from the live acceptance. -/
theorem rowFacts_toCD (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (chipOf (toCD O) layout309 c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing
      (DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes O.basis
        (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c) Qc) :
    RowFacts (toCD O) layout309 c Qc :=
  RowFacts.of_sat _ _ c Qc (toCD_injective O) hsat

/-- Dischargeability of `hL` at the deployed layout (`gates309_sub`). -/
theorem layout309_gatesOK (D : ChipData F K hOrb) : layout309.GatesOK D :=
  gates309_sub D

end Bridges

end

end Nock.NockVMROM.Thm54.SVCompute
