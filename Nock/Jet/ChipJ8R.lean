/-
  Nock/Jet/ChipJ8R.lean

  In `jetTemplateJ8T` the `.reg` row's handle
  `(kN, vN)` is consumed by no slot, so JB's `hReg` (`D (kN, vN) = compile p (R id)`) is a free witness.

  **The fix (no new coin).**  `jetTemplateJ8R = jetTemplateJ8T` plus
  * the base gate `sel_reg · (kN − 1)` (`regKindGate`): a registry handle is a CELL handle, kind `1`;
  * one `𝕂′` consume slot on `.reg` rows into the CELL VALIDITY balance (coins `γ′ρ′`, the frame's
    validity pair; chip-local challenge leaves `8 / 10`, `9 / 11`), of the cell-table claim key
    `(E (compile p (R id)), hi, lo, vN)` (`vKeyP` shape: fingerprint, rank, serial):
    `inv_V · sel_reg · (ρ′ + A + γ′⁴ · vN) − sel_reg`, where `A = Σ_{k<4} γ′^k e_k` is the RLC of the
    key's PUBLIC part (fingerprint `E (compile p (R id))` and the rank of `c_T`, both computed by the
    verifier after `z`) — a verifier-computed `𝕂′` column (`𝕂`-roles `18 / 19`) fixed per registry row;
  * the validity-consume accumulator (`𝕂`-roles `16 / 17`): init / step / terminal at the public
    `(pub₄, pub₅)`, the J share of the cell validity balance's consumers (one per registry row).

  `𝕂`-roles `0..13` and every `jetTemplateJ8T` gate are unchanged, so an accepted `J8R` trace restricts
  to an accepted `J8T` trace (`jetTemplateJ8R_restrict`, `expandChip_restrict`) and all of `RapJetJ8`
  applies to the restriction.

  * `jetRapJ8R` (template level) and `jetRapJ8R_restrict_sat`: the restriction is a `jetChipJ8` trace.
-/
import Nock.Jet.ChipJ8T
import Nock.NockVMROM.Thm54.VclL.Handle.ProvideH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.Jet.ChipJ8

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp
open Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.Reified Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial

/- The new `𝕂′` roles (`𝕂`-role pairs): the validity-consume inverse, its accumulator, the public
column `A`. -/
namespace ColR
def invV : ℕ := 14
def accV : ℕ := 16
def pubA : ℕ := 18
def extW : ℕ := 20
end ColR

section GatesR
variable {F : Type} [Field F]

/-- **`sel_reg · (kN − 1)`**: a registry row's handle is a cell handle. -/
def regKindGate : CoeffExpr F := .mul (cv (Kd.sel .reg)) (.sub (cv Col.kN) (.const 1))

def baseGatesJR : List (CoeffExpr F) := baseGatesJ ++ [regKindGate]

/-- The validity coins `γ′ = (χ₈, χ₁₀)`, `ρ′ = (χ₉, χ₁₁)` (chip-local leaves; the frame's `γ′ρ′`). -/
def gamV : QE F := QE.chal 8 10
def rhoV : QE F := QE.chal 9 11

/-- **The registry consume's denominator** `ρ′ + A + γ′⁴ · vN` (`A` = the RLC of the public part). -/
def denV (δ : F) : QE F :=
  QE.add rhoV (QE.add (QE.var ColR.pubA) (QE.mul δ (gpowJ δ gamV 4) (QE.base (cv Col.vN))))

/-- **The registry consume slot**: `inv_V · sel_reg · den_V − sel_reg`. -/
def slotGateV (δ : F) : QE F :=
  QE.sub (QE.mul δ (QE.var ColR.invV) (QE.scale (cv (Kd.sel .reg)) (denV δ)))
    (QE.base (cv (Kd.sel .reg)))

def contribV (rd : ℕ → CoeffExpr F) (iv : ℕ → QE F) : QE F := QE.scale (rd (Kd.sel .reg)) (iv ColR.invV)

/-- **The validity-consume accumulator** (init / step / terminal = public `(pub₄, pub₅)`). -/
def accGatesV : List (QE F) :=
  [ QE.scale (cv Col.isFirst) (QE.sub (QE.var ColR.accV) (contribV cv QE.var)),
    QE.scale (notE (cv Col.isLast))
      (QE.sub (QE.sub (QE.next ColR.accV) (QE.var ColR.accV)) (contribV nv QE.next)),
    QE.scale (cv Col.isLast) (QE.sub (QE.var ColR.accV) (QE.pub 4)) ]

/-- The new `𝕂`-valued gates. -/
def gatesV (δ : F) : List (MixedExpr F) := (slotGateV δ :: accGatesV).flatMap QE.gates

/-- **The `𝕂`-valued gates of `J8R`**: `J8T`'s, then the registry consume. -/
def gatesJR (δ : F) : List (MixedExpr F) := gatesJT δ ++ gatesV δ

theorem gatesV_deg_all (δ : F) : (gatesV δ).all (fun g => decide (g.degree ≤ 4)) = true := by
  simp [gatesV, slotGateV, accGatesV, contribV, denV, gpowJ, gamV, rhoV, ColR.invV, ColR.accV,
    ColR.pubA, Kd.sel, QE.gates, QE.var, QE.next, QE.chal, QE.pub, QE.base, QE.zero, QE.one,
    QE.add, QE.sub, QE.mul, QE.scale, MixedExpr.degree, CoeffExpr.degree]

theorem gatesJR_degree (δ : F) : ∀ g ∈ gatesJR δ, g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact gatesJT_degree δ g h
  · simpa using List.all_eq_true.mp (gatesV_deg_all δ) g h

theorem baseGatesJR_deg : ∀ g ∈ (baseGatesJR : List (CoeffExpr F)), g.degree ≤ 4 := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact baseGatesJ_deg g h
  · simp only [List.mem_singleton] at h; subst h; simp [regKindGate, CoeffExpr.degree]

/-- **The registry-consume J chip template** (base `29`, `𝕂`-roles `0 / 20`). -/
def jetTemplateJ8R (δ : F) : ChipTemplate F where
  rounds := 2
  rounds_pos := by decide
  baseColsOf := ![29, 0]
  extColsOf := ![0, 20]
  baseTransition := baseGatesJR
  extTransition := []
  mixedTransition := gatesJR δ
  extDeg1 := []
  extDeg3 := []
  equalityChecks := []
  baseTransition_deg := baseGatesJR_deg
  extTransition_deg := by simp
  mixedTransition_deg := gatesJR_degree δ
  extDeg1_deg := by simp
  extDeg3_deg := by simp
  equalityChecks_deg := by simp

/-- **Width, MEASURED: `89`** (`71` + the `𝕂′` inverse, accumulator and public column `A`: `+ 6·3`). -/
theorem jetTemplateJ8R_width (δ : F) : (jetTemplateJ8R δ).width 3 = 89 := rfl

theorem jetTemplateJ8R_baseCols (δ : F) : (jetTemplateJ8R δ).baseCols = 29 := by
  show (∑ r : Fin 2, (![29, 0] : Fin 2 → ℕ) r) = 29
  decide

theorem jetTemplateJ8R_extCols (δ : F) : (jetTemplateJ8R δ).extCols = 20 := by
  show (∑ r : Fin 2, (![0, 20] : Fin 2 → ℕ) r) = 20
  decide

theorem jetTemplateJ8T_extCols (δ : F) : (jetTemplateJ8T δ).extCols = 14 := by
  show (∑ r : Fin 2, (![0, 14] : Fin 2 → ℕ) r) = 14
  decide

/-! ### The restriction to `J8T` -/

theorem baseGatesJ_below_all : (baseGatesJ : List (CoeffExpr F)).all (colsBelow 29) = true := by
  simp [baseGatesJ, colsBelow, Kd.sel, Col.val, Col.n1, Col.v1, Col.v2, Col.kN]

theorem gatesJT_below_all (δ : F) : (gatesJT δ).all (mixBelow 14 29) = true := by
  simp [gatesJT, slotGatesT, accGates, slotGate, contribT, contribX, denJ, rlcJ, gpowJ, sumQE, selSum,
    CoeffExpr.sumList, ents0T, ents1T, ents2T, entsT, tagLast, ents0, ents1, ents2, ents3, entsX, keyV,
    keyRg, keyJet, keyX, KE.expr, gamT, rhoT, gamX, rhoX, Kd.sel, QE.gates, QE.var, QE.next, QE.chal,
    QE.pub, QE.base, QE.zero, QE.one, QE.add, QE.sub, QE.mul, QE.scale, mixBelow, colsBelow,
    Col.inv0, Col.inv1, Col.inv2, Col.inv3, Col.invX, Col.accT, Col.accX, Col.isFirst, Col.isLast,
    Col.id, Col.cid, Col.nid, Col.n1, Col.n2, Col.m, Col.mv, Col.val, Col.v1, Col.v2, Col.kN, Col.vN,
    Col.kL, Col.vL, Col.kR, Col.vR]

end GatesR


theorem gatesV_keyOK : (gatesV (F := ℚ) 7).all keyOKJe = true := by decide +kernel

theorem gatesJR_keyOK : (gatesJR (F := ℚ) 7).all keyOKJe = true := by
  rw [gatesJR, List.all_append, gatesJT_keyOK, gatesV_keyOK]; rfl

/-- The base gates read no serial column (`regKindGate` reads `kN`, a kind). -/
theorem baseGatesJR_serialFree : (baseGatesJR (F := ℚ)).all serialFreeJ = true := by
  rw [baseGatesJR, List.all_append, baseGatesJ_serialFree]; decide +kernel

/-- **Positive control**: the slot without the RLC (a bare `inv · vN`) is flagged. -/
theorem keyOKJR_flags :
    keyOKJe (F := ℚ) (.Mul (.Var .traceCur ColR.invV) (.Lift (cv Col.vN))) = false := by decide +kernel

/-! ## The template-level RAP and the restriction to `J8T`

`FixedPreprocessingRAP` fixes only round-0 columns, by
coin-independent polynomials (`preprocessingIndex : Fin fixedCount ↪ Fin (wRAP firstRound)`), so `A`
cannot be bound as preprocessing in this framework; `jetRapJ8R` below leaves roles `18 / 19` as
plain trace columns. -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The `J8R` RAP (template level; `A` unbound, see above). -/
noncomputable def jetRapJ8R (δ : F) (b : Basis (Fin 3) F K) {h n : ℕ} (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) : RAP F :=
  expandChip (jetTemplateJ8R δ) b (slotVal b 29 chals) (slotVal b 29 pubs) orbit (rowNodeSet nodes)

theorem jetRapJ8R_width (δ : F) (b : Basis (Fin 3) F K) {h n : ℕ} (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) :
    (jetRapJ8R δ b nodes orbit chals pubs).w = 89 := jetTemplateJ8R_width δ

theorem shiftCol_29 (j : ℕ) : shiftCol 29 29 j = j := by unfold shiftCol; split_ifs <;> omega

variable (δ : F) (b : Basis (Fin 3) F K) {h n : ℕ} (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (lay : Fin n → PRow)

/-- The restriction of a `J8R` trace to `jetChipJ8`'s `71` columns (identity on columns `< 71`). -/
noncomputable def restrictJR (Q : Fin (jetRapJ8R δ b nodes orbit chals pubs).w → F[X]) :
    Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → F[X] :=
  restrictQ 29 29 (fun j hj => by
    have : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w = 71 := jetChipJ8_width δ b nodes orbit chals pubs lay
    rw [jetRapJ8R_width, shiftCol_29]; omega) Q

/-- **`restrict`** (`expandChip_restrict`): a `J8R`-accepted trace restricts to a `jetChipJ8`-accepted
trace — every `J8T` gate is a `J8R` gate, reading base columns `< 29` and `𝕂`-roles `< 14`.  So every
`RapJetJ8` theorem (telescopes, `bal_of_service`, `accepted_of_sat`, `jetProvOK_of_sat`) applies to
`restrictJR Q`. -/
theorem jetRapJ8R_restrict_sat (Q : Fin (jetRapJ8R δ b nodes orbit chals pubs).w → F[X])
    (hsat : (jetRapJ8R δ b nodes orbit chals pubs).Satisfies Q) :
    (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies (restrictJR δ b nodes orbit chals pubs lay Q) :=
  expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (jetTemplateJ8T δ) (jetTemplateJ8R δ) 29 29
    (jetTemplateJ8T_baseCols δ) (jetTemplateJ8R_baseCols δ) le_rfl
    (by rw [jetTemplateJ8T_extCols, jetTemplateJ8R_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, List.all_eq_true.mp baseGatesJ_below_all g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, List.all_eq_true.mp (gatesJT_below_all δ) g hg⟩)
    rfl rfl Q hsat

end Chip

end Nock.Jet.ChipJ8
