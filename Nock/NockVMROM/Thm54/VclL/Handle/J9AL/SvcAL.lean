/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/SvcAL.lean

  **The service assembly with the ALU provides.** The twin of `AxisSoundX9.provP_service9` at the S8 provider list
  `jet ++ inc ++ walk ++ (TAG_ax ++ ALU) ++ split` (the ALU provides `pA` inside the axis share `pX`, as
  `RR49AL.provsAL` orders them).  Pass 1 (`Φ₀`): the ALU keys have a nonzero entry at position `7` (tags `7 / 6 / 3`),
  so `Φ₀` holds vacuously on them (`provP_phi0_wide`); the limb consumes are served by the whole list; pass 2: the
  ALU share `pA` meets `RecOK9I` by hypothesis (`AluShareAL.regProv_ok`, `jetProv_ok`).  `svc_absentAL`: the axis
  chip absent (`pX = pA`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.AxisSoundX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SvcAL

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf natKey)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9 RecOK9I WalkAOK9)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)
open Nock.NockVMROM.Thm54.VclL.Handle.AxisSoundX9
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (z1a)
open Module
open scoped Polynomial

noncomputable section

section Chip
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))]
  (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

/-- **The service assembly with the ALU share** (`provP_service9` at `pJ ++ pI ++ pW ++ (TAG_ax ++ pA) ++ pS`). -/
theorem provP_service9AL [DecidableEq (ZMod p)] (hpG : p = Nock.Atoms.p)
    (hsat : (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (AxisChipJ9.axisChipJ9 δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    {V : ℕ → Option ℕ} {D : LocalVSX.HX → Option Noun} (Rg : Nock.Jet.Registry) (hD : LocalVSX9.DenOKX9 p D V)
    {pJ pI pW pS pA : List ((Fin 8 → K) × K)}
    (hJ : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pJ)
    (hI : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pI)
    (hW : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pW)
    (hS : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pS)
    (hA : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pA)
    (hAw : ∀ q ∈ pA, ∃ c : Fin (mOf .s), 4 ≤ (c : ℕ) ∧ q.1 c ≠ 0)
    {extS : List (Fin 8 → K)}
    (hsvS : ∀ c ∈ extS,
      c ∈ (pJ ++ pI ++ pW ++ (AxisChipJ9.axTagProvs b nodes orbit chals pubs Q ++ pA) ++ pS).map Prod.fst)
    (hsubS : ∀ i : Fin n,
      AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodes orbit chals pubs Q i) ∈ extS)
    {Φp : List ℕ × Bal → Prop}
    (hΦp : ∀ a b c d, Φp ([a, b, c, d], .p) →
      ∃ Rt C, D (1, a) = some Rt ∧ D (c, d) = some C ∧ Noun.slot b Rt = some C)
    {pP : List ((Fin (mOf .p) → K) × K)} {extP : List (Fin (mOf .p) → K)}
    (hsvP : ∀ c ∈ extP, c ∈ pP.map Prod.fst)
    (hsubP : ∀ i : Fin n, (AxisChipJ9.axEF b nodes orbit chals pubs Q i).trace z1a = 0 →
      AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodes orbit chals pubs Q i) ∈ extP)
    (hP : ProvP (p := p) (K := K) Φp .p pP) :
    ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s
      (pJ ++ pI ++ pW ++ (AxisChipJ9.axTagProvs b nodes orbit chals pubs Q ++ pA) ++ pS) := by
  have hp5 : 5 < p := by have := hp63 hpG; omega
  -- pass 1
  have h0 : ProvP (p := p) (K := K) (Phi0 V) .s
      (pJ ++ pI ++ pW ++ (AxisChipJ9.axTagProvs b nodes orbit chals pubs Q ++ pA) ++ pS) := by
    refine ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr
      ⟨ServiceJ8.provP_append.mpr ⟨provP_phi0_of_I hJ, provP_phi0_of_I hI⟩, provP_phi0_of_9 hW⟩,
      ServiceJ8.provP_append.mpr ⟨provP_phi0_TAGax δF b hn nodes orbit chals pubs Q hp5, provP_phi0_wide hAw⟩⟩,
      provP_phi0_of_9 hS⟩
  have hL := served_limb_cons δF b hn nodes orbit chals pubs Q
    (fun a b c d h => h rfl rfl) hsvS hsubS h0
  have hPP := served_path_cons δF b hn nodes orbit chals pubs Q hΦp hsvP hsubP hP
  have hT := provP_TAGax δF b hn nodes orbit chals pubs Q hpG hsat hbind hinj hadj Rg hD hL hPP
  -- pass 2
  have hI9 : ∀ {pl : List ((Fin 8 → K) × K)}, ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pl →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pl :=
    fun h q hq l hl hlt hk _ => h q hq l hl hlt hk
  exact ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr
    ⟨ServiceJ8.provP_append.mpr ⟨hJ, hI⟩, hI9 hW⟩, ServiceJ8.provP_append.mpr ⟨hI9 hT, hA⟩⟩, hI9 hS⟩

end Chip

/-- **The service assembly, axis chip absent** (`pX = [] ++ pA`). -/
theorem svc_absentAL {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {V : ℕ → Option ℕ} {D : LocalVSX.HX → Option Noun} {Rg : Nock.Jet.Registry}
    {pJ pI pW pS pA : List ((Fin 8 → K) × K)}
    (hJ : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pJ)
    (hI : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pI)
    (hW : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pW)
    (hS : ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pS)
    (hA : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pA) :
    ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s (pJ ++ pI ++ pW ++ ([] ++ pA) ++ pS) := by
  have hI9 : ∀ {pl : List ((Fin 8 → K) × K)}, ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pl →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pl :=
    fun h q hq l hl hlt hk _ => h q hq l hl hlt hk
  rw [List.nil_append]
  exact ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr
    ⟨ServiceJ8.provP_append.mpr ⟨hJ, hI⟩, hI9 hW⟩, hA⟩, hI9 hS⟩

end

end Nock.NockVMROM.Thm54.VclL.Handle.SvcAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.SvcAL
#print axioms provP_service9AL
#print axioms svc_absentAL
end Axioms
