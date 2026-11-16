/-
  Nock/RedTeam/Batch1971Thm54WalkW2Chip.lean

  Modules: `VclL/Chips/LayoutW.lean` (columns per round, `21 / 72 / 39`, width `132`, MEASURED by
  `rfl` and `decide +kernel`), `VclL/Chips/WalkChip.lean` (`walkTemplate` / `walkChip` via
  `expandChip` beside `pathTemplate`: the in-gate forest walk, the depth certificate with its
  `{62, 63}` exclusion, the root gate on `rootMask` rows, the base-field queue counter, one export
  consume per row at side slot `0`, two path records per row with multiplicities `mL mR`; coins
  `αC = χ₀`, `γ = χ₁`).

  Deviation from WALK-F §9's `115`: B2 `24 → 39` (`𝕂′`
  inverses / accumulators are two `𝕂`-roles each, as in the path chip) and B0 `19 → 21` (`e = cL·cR`
  for degree 4; `u = b₁ b₂` for the certificate exclusion).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.WalkChip

set_option autoImplicit false

namespace Nock.RedTeam.Batch1971

open Nock.NockVMROM.Thm54.VclL.Chips
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

/-- The layout's widths per round and in total. -/
theorem layout_widths :
    WalkW.b0Count = 21 ∧ WalkW.b1Count = 72 ∧ WalkW.b2Count = 39 ∧ WalkW.width = 132 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The walk chip vs the path chip it replaces: `132` vs `112` columns, `112` vs `122` gates. -/
theorem walk_vs_path {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (δF : F) (kroots : ℕ) (b : Module.Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : Nock.NockVMROM.Thm54.StrictExtension.StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    (walkChip δF kroots b hn nodes orbit chals pubs).rap.w = 132 ∧
      (walkChip δF kroots b hn nodes orbit chals pubs).rap.s = 112 ∧
      (pathChip δF b hn nodes orbit chals pubs).rap.w = 112 ∧
      (pathChip δF b hn nodes orbit chals pubs).rap.s = 122 :=
  ⟨(walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).1,
    (walkChip_fingerprint δF kroots b hn nodes orbit chals pubs).2.1,
    (pathChip_fingerprint δF b hn nodes orbit chals pubs).1,
    (pathChip_fingerprint δF b hn nodes orbit chals pubs).2.1⟩

#print axioms WalkW.width_eq
#print axioms WalkW.width_le_stop
#print axioms WalkW.card_round0
#print axioms WalkW.card_round1
#print axioms WalkW.card_round2
#print axioms walkBase_deg
#print axioms walkMixed_deg
#print axioms walkBase_length
#print axioms walkMixed_length
#print axioms walkChip_fingerprint
#print axioms walkChip_width_layout
#print axioms walkChip_deg
#print axioms rootRowMaskW_eval
#print axioms layout_widths
#print axioms walk_vs_path

end Nock.RedTeam.Batch1971
