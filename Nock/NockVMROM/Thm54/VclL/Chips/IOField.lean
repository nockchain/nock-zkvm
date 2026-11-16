/-
  Nock/NockVMROM/Thm54/VclL/Chips/IOField.lean

  * §1 `ioSpecVCLQuad δ` — R-LC6's `ioSpecVCL` at `Kio := Quad δ` with `mk := Quad.mk δ`
    (injective: `Quad.mk_eq_mk_iff`), `|Kio| = |𝕂|²` (`quad_card`), four IO coins (`dep.card = 4`):
    exactly the two hypotheses `hI` / `hKio` of R-V3b's `epsilon_vcll_eq`; `CharP 𝕂′ p` from
    `CharP 𝕂 p` (what `serves_of_weighted_lookup` asks of `Kio`).  Closes R-LC6's unconfirmed item
    (the `Quad` instantiation of `ioSpecVCL`).
  * Records at `𝕂′` entries:
    validity `(fp′, lo + hi·√δ, idx)` = `5`, export `(fp′ p, l, r, idx)` = `10`, path
    `(fp′ root, child, acc, rootIdx)` = `8` (= V3's `mVCL`); supersedes `Layout.record_widths`
    (`9/19/14` over `𝕂`) and `Batch1700` §B.
  * §3 degree: the `𝕂′` LogUp gates in coordinates.  `inv·(ρ′ − RLC′) = 1` is two `𝕂`-equations
    bilinear in `(inv, ρ′ − RLC′)` (`inverse_gate_coords`); the weighted provider step
    `Δacc = w·inv` with `w ∈ 𝔽` is two `𝕂`-equations bilinear in `(w, inv)`
    (`weighted_step_coords`); `RLC′` is `𝕂′`-linear in the record with coin coefficients.  So each
    coordinate gate has degree `2` in the trace columns before masking (`d = 4` holds with two
    masks).  **Unconfirmed at the chip level**: the chips are not yet `FixedPreprocessingRAP`s on
    this branch; this is the coordinate algebra the gate compiler will see.
      - path (`N` compute consumers, no internal): `N < p` from `Checks.hrowsC` (`path_count_lt`);
      - **export (`3N` compute + `P` path edge rows): `3N + P < p` is NOT derivable from the row
        bounds** — `export_count_not_derivable` exhibits `p = 97`, `h = 5`, `N = P = 32` meeting
        `3N < p`, `P < p`, `N, P ≤ 2^5`, `3·2^5 ∣ p − 1`, `25 ≤ p` with `3N + P = 128 ≥ 97`.
-/
import Nock.NockVMROM.Thm54.VclL.Events.Summands
import Nock.NockVMROM.Thm54.VclL.Chips.Layout
import Nock.NockVMROM.Thm54.P8Core.Batch1541Thm54T0Tower

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Chips

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower

/-! ## 1. `ioSpecVCL` at `Kio := Quad δ` -/

section Quad
variable {K : Type} [Field K] (δ : K) [Fact (¬ IsSquare δ)]

/-- `Quad.mk δ` is injective in the shape `IOCoinSpec.ofExt` asks for. -/
theorem quadMk_inj : ∀ a b c d : K, Quad.mk δ a b = Quad.mk δ c d → a = c ∧ b = d :=
  fun a b c d h => (Quad.mk_eq_mk_iff δ a b c d).mp h

/-- **The VCL-L IO coins in `𝕂′ = Quad δ`**: `γ′ = χ₄ + χ₆·√δ`, `ρ′ = χ₅ + χ₇·√δ`. -/
noncomputable def ioSpecVCLQuad : IOCoinSpec frameVCL K (Quad δ) :=
  ioSpecVCL (Quad.mk δ) (quadMk_inj δ)

theorem ioSpecVCLQuad_coins (χ : Coins frameVCL K) :
    (ioSpecVCLQuad δ).ioCoins χ =
      ⟨Quad.mk δ (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩), Quad.mk δ (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)⟩ :=
  rfl

/-- `hI` of `epsilon_vcll_eq`: four IO coins. -/
theorem ioSpecVCLQuad_dep_card : (ioSpecVCLQuad δ).dep.card = 4 :=
  ioSpecVCL_dep_card _ _

/-- The four IO coins are M2 coins (sampled after B1). -/
theorem ioSpecVCLQuad_round : ∀ i ∈ (ioSpecVCLQuad δ).dep, frameVCL.sampledAfter i = 1 :=
  ioSpecVCL_round _ _

/-- `hKio` of `epsilon_vcll_eq`: `|𝕂′| = |𝕂|²`. -/
theorem ioSpecVCLQuad_card [Fintype K] : Fintype.card (Quad δ) = Fintype.card K ^ 2 :=
  quad_card δ

/-- `𝕂′` has the characteristic of `𝕂` (the `[CharP Kio p]` of `serves_of_weighted_lookup`). -/
theorem quad_charP (p : ℕ) [CharP K p] : CharP (Quad δ) p :=
  charP_of_injective_algebraMap (algebraMap K (Quad δ)).injective p

end Quad

/-! ## 2. The tower layouts and the record widths at `𝕂′` entries -/

/-- `𝕂`-roles per `𝕂′` element (Re/Im). -/
def towerRoles : ℕ := 2

namespace Cell

def b2CountT218 : ℕ := towerRoles * kRolesB2 * eK
def widthT218 : ℕ := b0Count + b1Count + b2CountT218
theorem widthT218_eq : widthT218 = 218 := rfl

/-- **** one more B0 column (`mx1`, position `128`, after the rank
bits) and one more `𝕂′` role (the side-1 export provider inverse): B0 `129`, B2 `7` `𝕂′` roles. -/
def b0CountS : ℕ := b0Count + 1
def kRolesB2S : ℕ := kRolesB2 + 1
/-- The `mx1` column. -/
def mx1Pos : ℕ := b0Count

/-- B2 at `𝕂′` IO coins: the seven `𝕂′` roles (validity provide / consume-L / consume-R inverses,
export provide inverses for sides `0` and `1`, validity and export accumulators), two `𝕂`-roles each. -/
def b2CountT : ℕ := towerRoles * kRolesB2S * eK

def widthT : ℕ := b0CountS + b1Count + b2CountT

theorem b2CountT_eq : b2CountT = 42 := rfl
/-- **The cell chip's width** (`= ChipRAP.cellChip_fingerprint`'s `225`). -/
theorem widthT_eq : widthT = 225 := rfl

def colRoundT (j : Fin widthT) : ℕ :=
  if (j : ℕ) < b0CountS then 0 else if (j : ℕ) < b0CountS + b1Count then 1 else 2

theorem card_roundT0 : (Finset.univ.filter fun j : Fin widthT => colRoundT j = 0).card = 129 := by
  decide +kernel
theorem card_roundT1 : (Finset.univ.filter fun j : Fin widthT => colRoundT j = 1).card = 54 := by
  decide +kernel
theorem card_roundT2 : (Finset.univ.filter fun j : Fin widthT => colRoundT j = 2).card = 42 := by
  decide +kernel

/-- The multiplicities `mv`, `mx`, `mx1` are round-0 base columns (unbounded `𝔽`, no range bits: the
`110` rank bits are the only bits on the table). -/
theorem mult_round0 : colRoundT ⟨b0Pos .mv, by decide⟩ = 0 ∧ colRoundT ⟨b0Pos .mx, by decide⟩ = 0 ∧
    colRoundT ⟨mx1Pos, by decide⟩ = 0 := by
  decide

end Cell

namespace Path

/-- B2 at `𝕂′` IO coins: four `𝕂′` roles (export consume inverse, path provide inverse, export and
path accumulators). -/
def b2CountT : ℕ := towerRoles * kRolesB2 * eK

def widthT : ℕ := b0Count + b1Count + b2CountT

theorem b2CountT_eq : b2CountT = 24 := rfl
theorem widthT_eq : widthT = 112 := rfl

def colRoundT (j : Fin widthT) : ℕ :=
  if (j : ℕ) < b0Count then 0 else if (j : ℕ) < b0Count + b1Count then 1 else 2

theorem card_roundT0 : (Finset.univ.filter fun j : Fin widthT => colRoundT j = 0).card = 16 := by
  decide +kernel
theorem card_roundT1 : (Finset.univ.filter fun j : Fin widthT => colRoundT j = 1).card = 72 := by
  decide +kernel
theorem card_roundT2 : (Finset.univ.filter fun j : Fin widthT => colRoundT j = 2).card = 24 := by
  decide +kernel

theorem mult_round0 : colRoundT ⟨b0Pos .m, by decide⟩ = 0 := by decide

end Path

/-- `𝕂′` entries per fingerprint `FP 𝕂′` (size, dyck, leaf). -/
def fpEntriesT : ℕ := 3

/-- Validity key `(fp′ p, lo + hi·√δ, idx)`. -/
def mValidityT : ℕ := fpEntriesT + 1 + 1
def mExportT : ℕ := 3 * fpEntriesT + 1 + 1
/-- Path record `(fp′ root, fp′ child, acc, rootIdx)`. -/
def mPathT : ℕ := 2 * fpEntriesT + 1 + 1

theorem record_widths_tower : mValidityT = 5 ∧ mExportT = 11 ∧ mPathT = 8 := ⟨rfl, rfl, rfl⟩

/-- They are V3's `mVCL` (the widths `epsilon_vcll_eq` / `boundVCL'` price). -/
theorem mVCL_eq_tower : Events.mVCL = ![mValidityT, mExportT, mPathT] := by
  funext a; fin_cases a <;> rfl

/-- The validity rank entry `lo + hi·√δ` determines `(lo, hi)` (base-field limbs embed injectively
through `𝔽 → 𝕂 → 𝕂′`), so the `5`-entry key carries the same data as the `9`-entry one. -/
theorem rank_entry_inj {F K : Type} [Field F] [Field K] [Algebra F K] (δ : K) [Fact (¬ IsSquare δ)]
    {lo hi lo' hi' : F}
    (h : Quad.mk δ (algebraMap F K lo) (algebraMap F K hi) =
      Quad.mk δ (algebraMap F K lo') (algebraMap F K hi')) : lo = lo' ∧ hi = hi' := by
  obtain ⟨h1, h2⟩ := (Quad.mk_eq_mk_iff δ _ _ _ _).mp h
  exact ⟨(algebraMap F K).injective h1, (algebraMap F K).injective h2⟩

/-! ## 3. Degree: the `𝕂′` LogUp gates in `𝕂` coordinates -/

section Degree
variable {K : Type} [Field K] (δ : K) [Fact (¬ IsSquare δ)]

/-- **`inv·(ρ′ − RLC′) = 1` in coordinates**: with `inv = i₀ + i₁√δ` (B2) and
`ρ′ − RLC′ = d₀ + d₁√δ` (affine in the B1 record columns, coin coefficients), the gate is the two
`𝕂`-equations `i₀d₀ + δ·i₁d₁ = 1`, `i₀d₁ + i₁d₀ = 0` — degree `2` in the trace columns. -/
theorem inverse_gate_coords (i₀ i₁ d₀ d₁ : K) :
    Quad.mk δ i₀ i₁ * Quad.mk δ d₀ d₁ = 1 ↔ i₀ * d₀ + δ * (i₁ * d₁) = 1 ∧ i₀ * d₁ + i₁ * d₀ = 0 := by
  rw [Quad.mk_mul, ← Quad.mk_one' δ, Quad.mk_eq_mk_iff]

/-- **The weighted provider step `acc′ − acc = w·inv`** (`w ∈ 𝔽` the B0 multiplicity): two
`𝕂`-equations, each bilinear in `(w, inv)` — degree `2`. -/
theorem weighted_step_coords {F : Type} [Field F] [Algebra F K] (w : F) (a₀ a₁ b₀ b₁ i₀ i₁ : K) :
    Quad.mk δ b₀ b₁ - Quad.mk δ a₀ a₁ = algebraMap K (Quad δ) (algebraMap F K w) * Quad.mk δ i₀ i₁ ↔
      b₀ - a₀ = algebraMap F K w * i₀ ∧ b₁ - a₁ = algebraMap F K w * i₁ := by
  rw [Quad.mk_sub, Quad.mk_smul, Quad.mk_eq_mk_iff]

/-- **`RLC′` term by term**: a coin `γ′ᵏ = g₀ + g₁√δ` times a record entry `e₀ + e₁√δ` has
coordinates `g₀e₀ + δg₁e₁`, `g₀e₁ + g₁e₀` — linear in the entry's columns (the coins are constants
of the gate), so `ρ′ − RLC′` is affine in the B1 columns. -/
theorem rlc_term_coords (g₀ g₁ e₀ e₁ : K) :
    Quad.mk δ g₀ g₁ * Quad.mk δ e₀ e₁ = Quad.mk δ (g₀ * e₀ + δ * (g₁ * e₁)) (g₀ * e₁ + g₁ * e₀) :=
  Quad.mk_mul δ g₀ g₁ e₀ e₁

end Degree

/-! ## 4. `serves` through the weighted lookup; the consumer-count bounds -/

section Serves
variable {F K Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  (δ : K) [Fact (¬ IsSquare δ)] [DecidableEq (Quad δ)]

/-- The earlier `k₁ + k₂ < char 𝕂` hypothesis is retired; the instance's
`serves` is `serves_holds_of_weighted_lookup` itself. -/
theorem vcl_serves_of_count [Algebra F (Quad δ)] (χ : Coins frameVCL K) {mw : ℕ}
    (reqs internal : List (Fin mw → Quad δ)) (ρ : Quad δ)
    (M : IOFacts F (FiniteIO.compress (m := mw) ((ioSpecVCLQuad δ).ioCoins χ))
      (ρ + (internal.map fun r => (FiniteIO.compress (m := mw) ((ioSpecVCLQuad δ).ioCoins χ) r)⁻¹).sum))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := mw) ((ioSpecVCLQuad δ).ioCoins χ) r)⁻¹).sum = ρ)
    (hne : ∀ r ∈ reqs, FiniteIO.compress (m := mw) ((ioSpecVCLQuad δ).ioCoins χ) r ≠ 0)
    (hine : ∀ r ∈ internal, FiniteIO.compress (m := mw) ((ioSpecVCLQuad δ).ioCoins χ) r ≠ 0)
    (hio : (ioSpecVCLQuad δ).pair χ ∉ FiniteIO.IOFailureEventW (reqs ++ internal) (liftWts M.records))
    (hcount : (reqs ++ internal).length < ringChar (Quad δ)) :
    ∀ r ∈ reqs, r ∈ M.records.map Prod.fst :=
  serves_of_weighted_lookup (Φ := frameVCL) (K := K) (F := F) (I := ioSpecVCLQuad δ)
    (nAcc := 1) (m := fun _ => mw) (p := ringChar (Quad δ)) χ 0 reqs internal ρ M hsum hne hine hio hcount

/-- The IO characteristic `Checks.hcons` compares against is the base one (`ringChar 𝕂′ = ringChar 𝕂`). -/
theorem quad_ringChar_eq : ringChar (Quad δ) = ringChar K :=
  (Algebra.ringChar_eq K (Quad δ)).symm

theorem reqCondVCL_any_length {Kio : Type} {m : Fin 3 → ℕ} (reqs : ∀ a : Fin 3, List (Fin (m a) → Kio))
    (χ : Coins frameVCL K) : reqCondVCL reqs χ :=
  trivial

end Serves

/-- **Path accumulator**: `N` compute consumers (slot 1 on `s0`, slot 2 on `s9`, one per row), no
internal consumer: `N + 0 < p` from `Checks.hrowsC : 3N < p`. -/
theorem path_count_lt {N p : ℕ} (hrowsC : 3 * N < p) : N + 0 < p := by omega

/-- `2D + 2 < p`
follows from the cell table's height (`D ≤ 2^h`, `Checks.hcapM`), its orbit (`3·2^h ∣ p − 1`: the
order of `orbitM`'s generator in the prime field) and `25 ≤ p` (`Checks.hp`) — not from
`hrowsM : D < p` alone. -/
theorem validity_count_lt {D h p : ℕ} (hcap : D ≤ 2 ^ h) (horb : 3 * 2 ^ h ∣ p - 1) (hp : 25 ≤ p) :
    2 * D + 2 < p := by
  have hle : 3 * 2 ^ h ≤ p - 1 := Nat.le_of_dvd (by omega) horb
  omega

/-- `hrowsM : D < p` alone does not give the validity count (`p = 31`, `D = 30`). -/
theorem validity_count_not_from_hrowsM : ∃ D p : ℕ, D < p ∧ 25 ≤ p ∧ ¬ 2 * D + 2 < p :=
  ⟨30, 31, by decide, by decide, by decide⟩

/-- `3N` compute
consumers (`kc = 3`) and `P` path edge rows: at `p = 97`, heights `5`, `N = P = 32`, every
numeric row check holds — `3N < p` (`hrowsC`), `P < p` (`hrowsM`), `N, P ≤ 2^5` (`hcapC`,
`hcapM`), `3·2^5 ∣ p − 1` (both orbits), `25 ≤ p` (`hp`), `p` prime — and `3N + P = 128 ≥ p`. -/
theorem export_count_not_derivable :
    ∃ p hC hP N P : ℕ, p.Prime ∧ 25 ≤ p ∧ 3 * 2 ^ hC ∣ p - 1 ∧ 3 * 2 ^ hP ∣ p - 1 ∧
      N ≤ 2 ^ hC ∧ P ≤ 2 ^ hP ∧ 3 * N < p ∧ P < p ∧ ¬ 3 * N + P < p :=
  ⟨97, 5, 5, 32, 32, by norm_num, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

end Nock.NockVMROM.Thm54.VclL.Chips
