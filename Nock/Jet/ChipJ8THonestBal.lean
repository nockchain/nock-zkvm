/-
  Nock/Jet/ChipJ8THonestBal.lean

  **The honest J terminal in closed form (the `mv` fix and the
  verifier-side registry pins), and the matmul `n = 2` instance of `jetChipJ8_honest_sat`.**

  * `sum_count`: LogUp counting over a duplicate-free provider key list.
  * **`termJ_sum_of_mv`**: if every provided in-chip key is provided once (`hnd`), every consumed key and
    every verifier-side registry pin is provided (`hcov`), and each provider's `mv` is the number of its
    in-chip consumers plus its pins (`hmv`), then the J terminal is
    `Σ_rows termJ = − Σ_{pins} den⁻¹ − Σ_rows m · Σ_{TAG_jet} den⁻¹`: the in-chip balance cancels, the
    registry pins (JR2's public pin: one consume of `(id, 1, idx_id, …, 2)` per registered id, added by
    the verifier in the J tagged balance) and the service provides are what the terminal carries into
    the merged service balance.
  * **`jetChipJ8_honest_sat_pins`**: `jetChipJ8_honest_sat` with `(pub₀, pub₁)` stated in that form.
  * The toy (`p = 1009`, `R = matmulT 2`, one call on J-2's toy subject, 237 rows): the verifier pin
    `toyPins`, the corrected rows `toyPinRows` (`mv` = in-chip consumers + pins); kernel checks of the
    layout, the base gates, provider uniqueness, coverage and `hmv`; **`toy_honest_sat`**: RAP-level
    honest acceptance of `jetChipJ8` on the toy trace, with only the orbit facts, the coin pole
    exclusions and the four publics as hypotheses.
-/
import Nock.Jet.ChipJ8THonestRAP
import Nock.Jet.ChipJ8THonest

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.Jet.ChipJ8T.HonestBal

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8
open Nock.Jet.ChipJ8T.HonestRAP Nock.Jet.ChipJ8T.Honest
open Nock.Framework Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Counting -/

section Count
variable {α R : Type} [BEq α] [LawfulBEq α] [CommRing R]

theorem sum_ite_count (f : α → R) (x : α) : ∀ L : List α,
    (L.map fun κ => if (x == κ) = true then f κ else 0).sum = (L.count x : R) * f x
  | [] => by simp
  | y :: L => by
    rw [List.map_cons, List.sum_cons, sum_ite_count f x L, List.count_cons]
    by_cases h : x = y
    · subst h; simp; ring
    · have h1 : (x == y) = false := by simpa using h
      have h2 : (y == x) = false := by simpa using Ne.symm h
      simp [h1, h2]

theorem sum_map_sub' {β M : Type} [AddCommGroup M] (f g : β → M) :
    ∀ l : List β, (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_sub' f g l]; abel

theorem sum_map_add' {β M : Type} [AddCommMonoid M] (f g : β → M) :
    ∀ l : List β, (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_add' f g l]; abel

/-- **LogUp counting**: over a duplicate-free key list `L` covering `C`,
`Σ_{x ∈ C} f x = Σ_{κ ∈ L} #C(κ) · f κ`. -/
theorem sum_count (f : α → R) (L : List α) (hL : L.Nodup) : ∀ C : List α, (∀ x ∈ C, x ∈ L) →
    (C.map f).sum = (L.map fun κ => (C.count κ : R) * f κ).sum
  | [], _ => by simp
  | x :: C, h => by
    have ih := sum_count f L hL C (fun y hy => h y (by simp [hy]))
    have hx : (L.map fun κ => if (x == κ) = true then f κ else 0).sum = f x := by
      rw [sum_ite_count, List.count_eq_one_of_mem hL (h x (by simp))]; simp
    rw [List.map_cons, List.sum_cons, ih, ← hx, ← sum_map_add']
    congr 1
    apply List.map_congr_left
    intro κ _
    by_cases hk : x = κ
    · subst hk; simp [List.count_cons]; ring
    · have h' : (x == κ) = false := by simpa using hk
      simp [h', List.count_cons]

end Count

/-! ## 2. The J terminal in closed form -/

section Terminal
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (δ : ZMod p)
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (chals : ℕ → K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The honest J terminal** under the `mv` fix with the verifier-side registry pins `pins`. -/
theorem termJ_sum_of_mv (L : List (CRow (ZMod p))) (pins : List (List (ZMod p)))
    (hnd : (L.flatMap provKT).Nodup)
    (hcov : ∀ κ ∈ L.flatMap consKT ++ pins, κ ∈ L.flatMap provKT)
    (hmv : ∀ r ∈ L, ∀ κ ∈ provKT r,
      r.w.mv = (((L.flatMap consKT).count κ + pins.count κ : ℕ) : ZMod p)) :
    (L.map (termJ δ chals)).sum =
      -(pins.map (dJ δ chals)).sum - (L.map fun r => liftQ δ r.w.m * sT δ chals ents3 r).sum := by
  set f : List (ZMod p) → 𝕂′ := dJ δ chals with hf
  set C := L.flatMap consKT with hC
  set Pv := L.flatMap provKT with hPv
  have hT : (L.map (termJ δ chals)).sum =
      (L.map fun r => ((consKT r).map f).sum).sum
        - (L.map fun r => liftQ δ r.w.mv * ((provKT r).map f).sum).sum
        - (L.map fun r => liftQ δ r.w.m * sT δ chals ents3 r).sum := by
    rw [← sum_map_sub', ← sum_map_sub']
    congr 1
    apply List.map_congr_left
    intro r _
    rw [termJ_eq]
    rfl
  have h1 : (L.map fun r => liftQ δ r.w.mv * ((provKT r).map f).sum).sum =
      (Pv.map fun κ => ((C.count κ : 𝕂′) + (pins.count κ : 𝕂′)) * f κ).sum := by
    rw [hPv, sum_flatMap]
    congr 1
    apply List.map_congr_left
    intro r hr
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro κ hκ
    rw [hmv r hr κ hκ]
    simp [liftQ]
  have hcons : (L.map fun r => ((consKT r).map f).sum).sum = (C.map f).sum := by
    rw [hC, sum_flatMap]
  have hcC := sum_count f Pv hnd C (fun x hx => hcov x (List.mem_append_left _ hx))
  have hcP := sum_count f Pv hnd pins (fun x hx => hcov x (List.mem_append_right _ hx))
  have h2 : (Pv.map fun κ => ((C.count κ : 𝕂′) + (pins.count κ : 𝕂′)) * f κ).sum =
      (C.map f).sum + (pins.map f).sum := by
    rw [hcC, hcP]
    simp only [add_mul]
    exact sum_map_add' (fun κ => (C.count κ : 𝕂′) * f κ) (fun κ => (pins.count κ : 𝕂′) * f κ) Pv
  rw [hT, hcons, h1, h2]
  ring

/-- The same over a `Fin`-indexed row family. -/
theorem termJ_sum_of_mv_fin {n : ℕ} (rows : Fin n → CRow (ZMod p)) (pins : List (List (ZMod p)))
    (hnd : ((List.ofFn rows).flatMap provKT).Nodup)
    (hcov : ∀ κ ∈ (List.ofFn rows).flatMap consKT ++ pins, κ ∈ (List.ofFn rows).flatMap provKT)
    (hmv : ∀ r ∈ List.ofFn rows, ∀ κ ∈ provKT r,
      r.w.mv = ((((List.ofFn rows).flatMap consKT).count κ + pins.count κ : ℕ) : ZMod p)) :
    ∑ i, termJ δ chals (rows i) =
      -(pins.map (dJ δ chals)).sum - ((List.ofFn rows).map fun r => liftQ δ r.w.m * sT δ chals ents3 r).sum := by
  rw [← termJ_sum_of_mv δ chals (List.ofFn rows) pins hnd hcov hmv, List.map_ofFn, List.sum_ofFn]
  rfl

end Terminal

/-! ## 3. Honest acceptance with the terminal in closed form -/

section Pins
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)
  {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (rows : Fin n → CRow (ZMod p))

/-- **RAP-level honest acceptance of `jetChipJ8`, the J terminal as the registry pins and the service
provides**: `(pub₀, pub₁) = − Σ_{pins} den⁻¹ − Σ_rows m · Σ_{TAG_jet} den⁻¹`, `(pub₂, pub₃)` = the export
sum. -/
theorem jetChipJ8_honest_sat_pins (pins : List (List (ZMod p))) (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hgate : ∀ i, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (envOf (rows i)) = 0)
    (hnd : ((List.ofFn rows).flatMap provKT).Nodup)
    (hcov : ∀ κ ∈ (List.ofFn rows).flatMap consKT ++ pins, κ ∈ (List.ofFn rows).flatMap provKT)
    (hmv : ∀ r ∈ List.ofFn rows, ∀ κ ∈ provKT r,
      r.w.mv = ((((List.ofFn rows).flatMap consKT).count κ + pins.count κ : ℕ) : ZMod p))
    (hpT : ∀ i, ∀ κ ∈ consKT (rows i) ++ provKT (rows i) ++ keysOf ents3 (rows i),
      compress (coinsJ δ chals) (liftRec (keyK (K := K) 8 κ)) ≠ 0)
    (hpX : ∀ i, ∀ κ ∈ keysOf entsX (rows i),
      compress (coinsJX δ chals) (liftRec (keyK (K := K) 5 κ)) ≠ 0)
    (hp01 : Quad.mk _ (pubs 0) (pubs 1) = -(pins.map (dJ δ chals)).sum -
      ((List.ofFn rows).map fun r => liftQ δ r.w.m * sT δ chals ents3 r).sum)
    (hp23 : Quad.mk _ (pubs 2) (pubs 3) = ∑ i, sX δ chals (rows i)) :
    RAP.SatisfiesWithPreprocessing (jetChipJ8 δ b nodes orbit chals pubs (layJ rows))
      (polyJC δ b nodes orbit chals pubs rows) :=
  jetChipJ8_honest_sat δ b nodes orbit chals pubs rows hinj hn hadj hgate hpT hpX
    (hp01.trans (termJ_sum_of_mv_fin δ chals rows pins hnd hcov hmv).symm) hp23

end Pins

/-! ## 4. The toy: matmul `n = 2`, `p = 1009` -/

/-- The verifier's registry pin for id `i` at memory index `idx`: the tag-last key
`(i, 1, idx, 0, 0, 0, 0, TAG_reg)`. -/
def regPin (i idx : ℕ) : List (ZMod 1009) := [(i : ZMod 1009), 1, (idx : ZMod 1009), 0, 0, 0, 0, 2]

/-- The toy's pins: one registry id, `0`, whose compiled formula sits in `toyMem`. -/
def toyPins : List (List (ZMod 1009)) := [regPin 0 (toyMem.idxOf (compile 1009 (matmulT 2)))]

/-- The honest `mv` with the pins: in-chip consumers plus pins of the row's provided key. -/
def mvPin (rows : List (CRow (ZMod 1009))) (pins : List (List (ZMod 1009))) (r : CRow (ZMod 1009)) :
    ZMod 1009 :=
  match provKT r with
  | [k] => (((rows.flatMap consKT).count k + pins.count k : ℕ) : ZMod 1009)
  | _ => 0

def rowsPin (rows : List (CRow (ZMod 1009))) (pins : List (List (ZMod 1009))) : List (CRow (ZMod 1009)) :=
  rows.map fun r => { r with w := { r.w with mv := mvPin rows pins r } }

/-- **The toy's corrected rows** (237 rows). -/
def toyPinRows : List (CRow (ZMod 1009)) := rowsPin toyRowsJ toyPins

theorem toyPin_length : toyPinRows.length = 237 := by
  simp [toyPinRows, rowsPin, toyRowsJ_length]

theorem toyPin_layout : toyPinRows.map CRow.pre = layoutJ8 ChipJ8.toyR [0] [0] := by decide +kernel

theorem toyPin_gates : ∀ r ∈ toyPinRows, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod 1009))),
    g.eval (envOf r) = 0 := by decide +kernel

theorem toyPin_nodup : (toyPinRows.flatMap provKT).Nodup := by decide +kernel

theorem toyPin_cov : ∀ κ ∈ toyPinRows.flatMap consKT ++ toyPins, κ ∈ toyPinRows.flatMap provKT := by
  decide +kernel

theorem toyPin_mv : ∀ r ∈ toyPinRows, ∀ κ ∈ provKT r,
    r.w.mv = (((toyPinRows.flatMap consKT).count κ + toyPins.count κ : ℕ) : ZMod 1009) := by
  decide +kernel

theorem toyPin_ofFn : List.ofFn toyPinRows.get = toyPinRows := List.ofFn_get _

/-- **RAP-level honest acceptance of the tag-last J chip on the matmul `n = 2` toy trace**
(`p = 1009`): only the orbit facts, the coin pole exclusions and the publics remain. -/
theorem toy_honest_sat {K : Type} [Field K] [Algebra (ZMod 1009) K] [FiniteDimensional (ZMod 1009) K]
    [Fintype K] (δ : ZMod 1009) [Fact (¬ IsSquare (algebraMap (ZMod 1009) K δ))]
    (b : Basis (Fin 3) (ZMod 1009) K) {h : ℕ} (nodes : Fin toyPinRows.length → ZMod 1009)
    (orbit : StrictOrbitDomain (ZMod 1009) 3 h) (chals pubs : ℕ → K)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin toyPinRows.length) (hi : (i : ℕ) + 1 < toyPinRows.length),
      nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hpT : ∀ r ∈ toyPinRows, ∀ κ ∈ consKT r ++ provKT r ++ keysOf ents3 r,
      compress (coinsJ δ chals) (liftRec (keyK (K := K) 8 κ)) ≠ 0)
    (hpX : ∀ r ∈ toyPinRows, ∀ κ ∈ keysOf entsX r,
      compress (coinsJX δ chals) (liftRec (keyK (K := K) 5 κ)) ≠ 0)
    (hp01 : Quad.mk _ (pubs 0) (pubs 1) = -(toyPins.map (dJ δ chals)).sum -
      (toyPinRows.map fun r => liftQ δ r.w.m * sT δ chals ents3 r).sum)
    (hp23 : Quad.mk _ (pubs 2) (pubs 3) = (toyPinRows.map (sX δ chals)).sum) :
    RAP.SatisfiesWithPreprocessing (jetChipJ8 δ b nodes orbit chals pubs (layJ toyPinRows.get))
      (polyJC δ b nodes orbit chals pubs toyPinRows.get) := by
  have hn : 0 < toyPinRows.length := by rw [toyPin_length]; norm_num
  refine jetChipJ8_honest_sat_pins δ b nodes orbit chals pubs toyPinRows.get toyPins hinj hn hadj
    (fun i => toyPin_gates _ (List.get_mem _ _)) (by rw [toyPin_ofFn]; exact toyPin_nodup)
    (by rw [toyPin_ofFn]; exact toyPin_cov) (by rw [toyPin_ofFn]; exact toyPin_mv)
    (fun i => hpT _ (List.get_mem _ _)) (fun i => hpX _ (List.get_mem _ _))
    (by rw [toyPin_ofFn]; exact hp01) ?_
  rw [hp23, ← List.sum_ofFn]
  exact (congrArg List.sum (List.ofFn_getElem_eq_map toyPinRows (sX δ chals))).symm

end

end Nock.Jet.ChipJ8T.HonestBal
