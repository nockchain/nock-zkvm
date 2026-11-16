/-
  Nock/NockVMROM/Thm54/VclL/Handle/Lift40J8.lean

The 40th's summands (`PullVSQ.sumCVSQ` / `sumMVSQ` / `jointVSQ`) are events of the 40th's traces (`TrVSQ`: the
  85-column compute chip).  The J-8 compute chip is `computeChipVCLHX` with its own walk rows (`rowsWX`), so a
  projection of J-8 traces onto `TrVSQ` that carries the J-8 walk event to the 40th's walk event does not exist.
  What `DataJ8` needs of #1 is a `frameVSQ` list with `epsilonOf = boundVCLHQ''` (`eps40`) and a staged
  projection (`hπ40`).  This module builds that list from J-8 readouts, summand by summand in the 40th's shape:
  the same ten coin sets, read sets and weights as `epsilonVSQ_eq`'s list, each event the 40th's event at the J-8
  readout (the compute walk event `cwEvent` / `tileSet` at the J-8 rows `RowVSX`, the dyck / census / zero-seed
  events at the J-8 cell rows, the walk-chain event at the J-8 walk data, the five IO events at the J-8 lists).

  * §1 generic `specSummandF` / `ioSummandF` (any frame), the `frameVSQ` coin specs `specVQ` (`γ′ρ′`) / `specHQ`
    (`γH′ρH′`) and the pair specs `(0, 1)`, `(13, 14)`.
  * §2 the staging `St40 St` (a `frameJ8` strategy with `y` fixed), `hπ40_id`.
  * §3 `Data40J8`: the readouts; the ten summands `cwalkL … hpL`; `sum40`; **`epsilon_sum40`** (`= boundVCLHQ''`).
  * §4 **`withLift R L`**: any `DataJ8` with #1 replaced by `sum40 L` (`Tr40 := Tr`, `π40 := id`).
  * §5 outside `allJ8 (withLift R L)`: `outside40` and the ten events, at `frameJ8` coins.
  * §6 the `FinalJ8` shapes: **`hw_of_outside40`** (`(α, γ) ∉ cwEvent rows n`), **`hα_of_outside40`**
    (`α ∉ tileSet`), at `α = limbVal b (chalVJ8 b χ) chalAlphaW`, `γ = … chalGammaW` (`XCtx.hα / hγ`);
    **`hout_p_of_outside40`** (`hout .p` at `coinsCV (chalVJ8 b χ)`); **`hz_of_outside40`** (the cell table's
    `hz` at the memory vector `chalsMJ8`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
import Nock.NockVMROM.Thm54.VclL.Handle.HonestClaimH
import Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (RowVSX)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX (foOf foOf_le)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX (cwEvent cwEvent_card_le tileSet tileSet_card)

noncomputable section

/-! ## 1. Generic summands and the `frameVSQ` coin specs -/

section Spec
variable {Φ : CoinFrame} {K Kio : Type} [Field K] [Fintype K] [DecidableEq K] [Field Kio] [Fintype Kio]
  [DecidableEq Kio]

open Classical in
/-- `WeightsJ8.specSummand` at any frame. -/
def specSummandF (I : IOCoinSpec Φ K Kio) (dep : Finset (Fin Φ.n)) (hdisj : Disjoint I.dep dep)
    {Tr : Type} (St : (Coins Φ K → Tr) → Prop) (bad : Tr → Coins Φ K → Finset (Kio × Kio))
    (W : ℕ) (hW : ∀ tr χ, (bad tr χ).card ≤ W)
    (hreads : ∀ Q, St Q → ReadsOnC Φ dep (fun χ => bad (Q χ) χ)) :
    BadSummand Φ K Tr St where
  coins := I.dep
  dep := dep
  disj := hdisj
  badSet tr χ := Finset.univ.filter fun v => I.pair (extIO I v) ∈ bad tr χ
  weight := W
  card_le tr χ := by
    refine le_trans (Finset.card_le_card_of_injOn (fun v => I.pair (extIO I v)) ?_ ?_) (hW tr χ)
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h; exact extIO_inj _ h
  readsOn Q hQ χ χ' h := by
    have e : bad (Q χ) χ = bad (Q χ') χ' := hreads Q hQ χ χ' h
    show Finset.univ.filter _ = Finset.univ.filter _
    rw [e]

theorem mem_specSummandF (I : IOCoinSpec Φ K Kio) (dep : Finset (Fin Φ.n)) (hdisj : Disjoint I.dep dep)
    {Tr : Type} (St : (Coins Φ K → Tr) → Prop) (bad : Tr → Coins Φ K → Finset (Kio × Kio)) (W : ℕ) (hW hreads)
    (tr : Tr) (χ : Coins Φ K) :
    (specSummandF I dep hdisj St bad W hW hreads).mem tr χ ↔ I.pair χ ∈ bad tr χ := by
  unfold BadSummand.mem
  show (fun i : I.dep => χ i) ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter, pair_extIO]
  simp

/-- `WeightsJ8.ioSummandJ8` at any frame: the guarded weighted IO event, weight `ioFUB m k₁ k₂ |Kio|`. -/
def ioSummandF (I : IOCoinSpec Φ K Kio) (dep : Finset (Fin Φ.n)) (hdisj : Disjoint I.dep dep)
    {Tr : Type} (St : (Coins Φ K → Tr) → Prop) {m : ℕ}
    (reqs : Tr → Coins Φ K → List (Fin m → Kio)) (provs : Tr → Coins Φ K → List ((Fin m → Kio) × Kio))
    (k₁ k₂ : ℕ) (hreads : ∀ Q, St Q → ReadsOnC Φ dep (fun χ => (reqs (Q χ) χ, provs (Q χ) χ))) :
    BadSummand Φ K Tr St :=
  specSummandF I dep hdisj St (fun tr χ => evIO (reqs tr χ) (provs tr χ) k₁ k₂)
    (ioFailureUnionBound m k₁ k₂ (Fintype.card Kio)) (fun _ _ => evIO_card _ _ _ _)
    (fun Q hQ χ χ' h => by
      have e := hreads Q hQ χ χ' h
      simp only [Prod.mk.injEq] at e
      show evIO _ _ _ _ = evIO _ _ _ _
      rw [e.1, e.2])

theorem mem_ioSummandF (I : IOCoinSpec Φ K Kio) (dep : Finset (Fin Φ.n)) (hdisj : Disjoint I.dep dep)
    {Tr : Type} (St : (Coins Φ K → Tr) → Prop) {m : ℕ}
    (reqs : Tr → Coins Φ K → List (Fin m → Kio)) (provs : Tr → Coins Φ K → List ((Fin m → Kio) × Kio))
    (k₁ k₂ : ℕ) (hreads) (tr : Tr) (χ : Coins Φ K) :
    (ioSummandF I dep hdisj St reqs provs k₁ k₂ hreads).mem tr χ ↔
      I.pair χ ∈ evIO (reqs tr χ) (provs tr χ) k₁ k₂ :=
  mem_specSummandF _ _ _ _ _ _ _ _ tr χ

end Spec

def v0 : Fin frameVSQ.n := ⟨0, by decide⟩
def v1 : Fin frameVSQ.n := ⟨1, by decide⟩
def v2 : Fin frameVSQ.n := ⟨2, by decide⟩
def v3 : Fin frameVSQ.n := ⟨3, by decide⟩
def v4 : Fin frameVSQ.n := ⟨4, by decide⟩
def v5 : Fin frameVSQ.n := ⟨5, by decide⟩
def v6 : Fin frameVSQ.n := ⟨6, by decide⟩
def v7 : Fin frameVSQ.n := ⟨7, by decide⟩
def v11 : Fin frameVSQ.n := ⟨11, by decide⟩
def v12 : Fin frameVSQ.n := ⟨12, by decide⟩
def v13 : Fin frameVSQ.n := ⟨13, by decide⟩
def v14 : Fin frameVSQ.n := ⟨14, by decide⟩

section Specs
variable {K Kio : Type} [Field K] (mk : K → K → Kio) (hmk : ∀ a b c d, mk a b = mk c d → a = c ∧ b = d)

/-- `γ′ = mk χ₄ χ₆`, `ρ′ = mk χ₅ χ₇` at `frameVSQ` (the 40th's `ioSpecVS`). -/
def specVQ : IOCoinSpec frameVSQ K Kio := IOCoinSpec.ofExt frameVSQ mk hmk (v4, v6) (v5, v7)
/-- `γH′ = mk χ₁₁ χ₁₅`, `ρH′ = mk χ₁₂ χ₁₆` at `frameVSQ` (the 40th's `ioSpecHQ`). -/
def specHQ : IOCoinSpec frameVSQ K Kio := IOCoinSpec.ofExt frameVSQ mk hmk (v11, cGamHi) (v12, cRhoHi)
/-- The walk-chain pair `(χ₀, χ₁)` (the 40th's `walkChainVS`). -/
def spec01 : IOCoinSpec frameVSQ K K := IOCoinSpec.ofPair frameVSQ K v0 v1
/-- The compute-walk pair `(αW, γW) = (χ₁₃, χ₁₄)` (the 40th's `cwalkVS`). -/
def spec1314 : IOCoinSpec frameVSQ K K := IOCoinSpec.ofPair frameVSQ K v13 v14

theorem specVQ_dep_card : (specVQ mk hmk).dep.card = 4 := rfl
theorem specHQ_dep_card : (specHQ mk hmk).dep.card = 4 := rfl
theorem spec01_dep_card : (spec01 (K := K)).dep.card = 2 := rfl
theorem spec1314_dep_card : (spec1314 (K := K)).dep.card = 2 := rfl

theorem specVQ_disj : Disjoint (specVQ mk hmk).dep (coinsBelow frameVSQ 1) := by
  show Disjoint ({v4, v6, v5, v7} : Finset (Fin frameVSQ.n)) (coinsBelow frameVSQ 1); decide
theorem specHQ_disj : Disjoint (specHQ mk hmk).dep ∅ := Finset.disjoint_empty_right _
theorem spec01_disj : Disjoint (spec01 (K := K)).dep (coinsBelow frameVSQ 1) := by
  show Disjoint ({v0, v1} : Finset (Fin frameVSQ.n)) (coinsBelow frameVSQ 1); decide
theorem spec1314_disj : Disjoint (spec1314 (K := K)).dep ∅ := Finset.disjoint_empty_right _
theorem v13_not_mem : v13 ∉ (∅ : Finset (Fin frameVSQ.n)) := Finset.notMem_empty _

end Specs

/-! ## 2. The staging of #1 -/

section Stage
variable {K : Type} {Tr : Type}

/-- **The `frameVSQ` staging of #1**: a `frameJ8` staged strategy with the limb coin `y` fixed. -/
def St40 (St : (Coins frameJ8 K → Tr) → Prop) : (Coins frameVSQ K → Tr) → Prop :=
  fun Q => ∃ Q', St Q' ∧ ∃ y₁ y₂ : K, Q = fun ψ => Q' (extY ψ y₁ y₂)

/-- `DataJ8.hπ40` at `π40 = id`. -/
theorem hπ40_id (St : (Coins frameJ8 K → Tr) → Prop) :
    ∀ Q', St Q' → ∀ y₁ y₂ : K, St40 St fun ψ => id (Q' (extY ψ y₁ y₂)) :=
  fun Q' hQ' y₁ y₂ => ⟨Q', hQ', y₁, y₂, rfl⟩

end Stage

/-! ## 3. The J-8 readouts of #1 and the ten summands -/

section Data
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  (δ : K) [Fact (¬ IsSquare δ)]

local notation "𝕂′" => Quad δ
local notation "qmk" => Chips.quadMk_inj δ

/-- **The J-8 readouts of the 40th's class** (row counts `r.N r.D r.W r.Λ`), each staged along `St40 St` with the
40th summand's read set: the compute walk rows (round 0), the cell table's round-0 rows and census skeleton, the
walk chip's walk data (rounds `≤ 0`), the fingerprint-export and validity lists (rounds `≤ 0`), the handle-class
export and path lists (round 0). -/
structure Data40J8 (Tr : Type) (St : (Coins frameJ8 K → Tr) → Prop) (r : RowsJ8) where
  /-- compute walk rows and their count -/
  cRows : Tr → ℕ → RowVSX
  cH : Tr → ℕ
  cH_le : ∀ tr, cH tr ≤ r.N
  c_const : ∀ Q, St40 St Q → ∀ ψ ψ', cRows (Q ψ) = cRows (Q ψ') ∧ cH (Q ψ) = cH (Q ψ')
  /-- the cell table's round-0 rows and census skeleton -/
  rowsD : Tr → List (CellRowB0 q)
  skelD : Tr → List Nock.Noun
  rowsD_le : ∀ tr, (rowsD tr).length ≤ r.D
  skelD_le : ∀ tr, (skelD tr).length ≤ 3
  rowsD_const : ∀ Q, St40 St Q → ∀ ψ ψ', rowsD (Q ψ) = rowsD (Q ψ') ∧ skelD (Q ψ) = skelD (Q ψ')
  /-- the walk chip's walk data -/
  wdW : Tr → Coins frameVSQ K → WalkVCL.WalkData q 𝕂′
  wdW_le : ∀ tr ψ, (wdW tr ψ).h ≤ r.W
  wdW_reads : ∀ Q, St40 St Q → ReadsOnC frameVSQ (coinsBelow frameVSQ 1) fun ψ => wdW (Q ψ) ψ
  /-- the fingerprint-export lists (arity 11, `γ′ρ′`) -/
  fxReqs : Tr → Coins frameVSQ K → List (Fin 11 → 𝕂′)
  fxProvs : Tr → Coins frameVSQ K → List ((Fin 11 → 𝕂′) × 𝕂′)
  fx_reads : ∀ Q, St40 St Q → ReadsOnC frameVSQ (coinsBelow frameVSQ 1) fun ψ => (fxReqs (Q ψ) ψ, fxProvs (Q ψ) ψ)
  /-- the cell validity lists (arity 5, `γ′ρ′`) -/
  vReqs : Tr → Coins frameVSQ K → List (Fin 5 → 𝕂′)
  vProvs : Tr → Coins frameVSQ K → List ((Fin 5 → 𝕂′) × 𝕂′)
  v_reads : ∀ Q, St40 St Q → ReadsOnC frameVSQ (coinsBelow frameVSQ 1) fun ψ => (vReqs (Q ψ) ψ, vProvs (Q ψ) ψ)
  /-- the handle-class cell-export lists (`γH′ρH′`) -/
  xReqs : Tr → Coins frameVSQ K → List (Fin 5 → 𝕂′)
  xProvs : Tr → Coins frameVSQ K → List ((Fin 5 → 𝕂′) × 𝕂′)
  x_reads : ∀ Q, St40 St Q → ReadsOnC frameVSQ ∅ fun ψ => (xReqs (Q ψ) ψ, xProvs (Q ψ) ψ)
  /-- the handle-class path lists (`γH′ρH′`) -/
  pReqs : Tr → Coins frameVSQ K → List (Fin 5 → 𝕂′)
  pProvs : Tr → Coins frameVSQ K → List ((Fin 5 → 𝕂′) × 𝕂′)
  p_reads : ∀ Q, St40 St Q → ReadsOnC frameVSQ ∅ fun ψ => (pReqs (Q ψ) ψ, pProvs (Q ψ) ψ)

variable {δ} {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8}

/-- **#1.1 the compute walk** (`(αW, γW)`, `dep = ∅`, weight `|𝕂|·6N`; the 40th's `cwalkVS`). -/
def cwalkL (L : Data40J8 (q := q) δ Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  specSummandF spec1314 ∅ spec1314_disj (St40 St) (fun tr _ => cwEvent (K := K) (L.cRows tr) (L.cH tr))
    (Fintype.card K * (6 * r.N)) (fun tr _ => cwEvent_card_le _ (L.cH_le tr))
    (fun Q hQ ψ ψ' _ => by simp only [(L.c_const Q hQ ψ ψ').1, (L.c_const Q hQ ψ ψ').2])

/-- **#1.2 the `αW`-tiling** (coin `13`, weight `2N + 2`; the 40th's `ctileVS`). -/
def ctileL (L : Data40J8 (q := q) δ Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  Compute.SummandsQ7.coinSummand v13 ∅ v13_not_mem (fun tr _ => tileSet (K := K) (foOf (L.cRows tr)) (L.cH tr))
    (2 * r.N + 2) (fun tr _ => (tileSet_card _ (foOf_le _) _).trans (by have := L.cH_le tr; omega))
    (fun Q hQ ψ ψ' _ => by simp only [(L.c_const Q hQ ψ ψ').1, (L.c_const Q hQ ψ ψ').2])

/-- **#1.3 the dyck roots** (coins `2, 3`, weight `D·(2·fuelChip − 1)`; the 40th's `dyckVS`). -/
def dyckL (L : Data40J8 (q := q) δ Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  cellDyckRootSummand δ frameVSQ v2 v3 (St40 St) L.rowsD r.D fuelChip L.rowsD_le
    (fun Q hQ ψ ψ' => (L.rowsD_const Q hQ ψ ψ').1)

/-- **#1.4 the walk chain** (coins `0, 1`, reading round `0`, weight `|𝕂|·15W`; the 40th's `walkChainVS`). -/
def wchainL (L : Data40J8 (q := q) δ Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  specSummandF spec01 (coinsBelow frameVSQ 1) spec01_disj (St40 St) (fun tr ψ => WalkVCL.walkEvent δ (L.wdW tr ψ))
    (Fintype.card K * (15 * r.W)) (fun tr ψ => WalkVCL.walkEvent_card δ _ (L.wdW_le tr ψ))
    (fun Q hQ ψ ψ' h => by simp only [L.wdW_reads Q hQ ψ ψ' h])

/-- **#1.5 the fingerprint export** (`γ′ρ′`, arity 11, budgets `(W, 2D)`; the 40th's `fpExportIOVS`). -/
def fpxL (L : Data40J8 (q := q) δ Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  ioSummandF (specVQ (Quad.mk δ) qmk) _ (specVQ_disj _ _) (St40 St) L.fxReqs L.fxProvs r.W (2 * r.D) L.fx_reads

/-- **#1.6 the zero seed** (`z = 0`, weight `1`; the 40th's `zeroVS`). -/
def zeroL (L : Data40J8 (q := q) δ Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  towerSeedSummand δ frameVSQ v2 v3 (St40 St) (fun _ => {0}) 1 (fun _ => by simp) (fun _ _ _ _ => rfl)

/-- **#1.7 the T2 + claim census** (coins `2, 3`, weight `pairCount (D + 3)·(2Λ − 1)`; the 40th's `censusVS`). -/
def censusL (L : Data40J8 (q := q) δ Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  tableCensusSummand δ frameVSQ v2 v3 (St40 St) L.rowsD L.skelD r.D 3 r.Λ L.rowsD_le L.skelD_le L.rowsD_const

/-- **#1.8 cell validity** (`γ′ρ′`, budgets `(3 + 2D, D)`; the 40th's `valSummand`). -/
def valL (L : Data40J8 (q := q) δ Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  ioSummandF (specVQ (Quad.mk δ) qmk) _ (specVQ_disj _ _) (St40 St) L.vReqs L.vProvs (3 + 2 * r.D) r.D L.v_reads

/-- **#1.9 handle export** (`γH′ρH′`, budgets `(3N + W, D)`; the 40th's `ioSummandHXQ`). -/
def hxL (L : Data40J8 (q := q) δ Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  ioSummandF (specHQ (Quad.mk δ) qmk) ∅ (specHQ_disj _ _) (St40 St) L.xReqs L.xProvs (3 * r.N + r.W) r.D L.x_reads

/-- **#1.10 handle path** (`γH′ρH′`, budgets `(2N, 2W)`; the 40th's `ioSummandHPQ`). -/
def hpL (L : Data40J8 (q := q) δ Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  ioSummandF (specHQ (Quad.mk δ) qmk) ∅ (specHQ_disj _ _) (St40 St) L.pReqs L.pProvs (2 * r.N) (2 * r.W) L.p_reads

/-- **The J-8 list of the 40th's class** (in `epsilonVSQ_eq`'s order). -/
def sum40 (L : Data40J8 (q := q) δ Tr St r) : List (BadSummand frameVSQ K Tr (St40 St)) :=
  [cwalkL L, ctileL L, dyckL L, wchainL L, fpxL L, zeroL L, censusL L, valL L, hxL L, hpL L]

/-- **`eps40`: the `ε` of the J-8 list of the 40th's class is `boundVCLHQ''`** (an equality, as `epsilonVSQ_eq`). -/
theorem epsilon_sum40 (L : Data40J8 (q := q) δ Tr St r) :
    epsilonOf (sum40 L) = boundVCLHQ'' (Fintype.card K) (Fintype.card 𝕂′) r.N r.D r.W r.Λ := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  simp only [sum40, epsilonOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have e1 : (cwalkL L).coins.card = 2 := rfl
  have e2 : (ctileL L).coins.card = 1 := Finset.card_singleton _
  have e3 : (dyckL L).coins.card = 2 := Finset.card_pair (by decide)
  have e4 : (wchainL L).coins.card = 2 := rfl
  have e5 : (fpxL L).coins.card = 4 := rfl
  have e6 : (zeroL L).coins.card = 2 := Finset.card_pair (by decide)
  have e7 : (censusL L).coins.card = 2 := Finset.card_pair (by decide)
  have e8 : (valL L).coins.card = 4 := rfl
  have e9 : (hxL L).coins.card = 4 := rfl
  have e10 : (hpL L).coins.card = 4 := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  have w1 : (cwalkL L).weight = Fintype.card K * (6 * r.N) := rfl
  have w2 : (ctileL L).weight = 2 * r.N + 2 := rfl
  have w3 : (dyckL L).weight = r.D * (2 * fuelChip - 1) := rfl
  have w4 : (wchainL L).weight = Fintype.card K * (15 * r.W) := rfl
  have w5 : (fpxL L).weight = ioFailureUnionBound 11 r.W (2 * r.D) (Fintype.card 𝕂′) := rfl
  have w6 : (zeroL L).weight = 1 := rfl
  have w7 : (censusL L).weight = pairCount (r.D + 3) * (2 * r.Λ - 1) := rfl
  have w8 : (valL L).weight = ioFailureUnionBound 5 (3 + 2 * r.D) r.D (Fintype.card 𝕂′) := rfl
  have w9 : (hxL L).weight = ioFailureUnionBound 5 (3 * r.N + r.W) r.D (Fintype.card 𝕂′) := rfl
  have w10 : (hpL L).weight = ioFailureUnionBound 5 (2 * r.N) (2 * r.W) (Fintype.card 𝕂′) := rfl
  rw [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10]
  unfold boundVCLHQ''
  push_cast
  field_simp
  ring

/-! ## 4. `DataJ8` with #1 at the J-8 traces -/

variable {P : ℕ} [Algebra Nock.Atoms.Fp (Quad δ)]

/-- **`withLift R L`**: `R` with summand #1 replaced by the J-8 list of the 40th's class (`Tr40 := Tr`,
`St40 := St40 St`, `π40 := id`, `hπ40 := hπ40_id`, `eps40 := epsilon_sum40`). -/
def withLift (R : DataJ8 (q := q) δ Tr St r P) (L : Data40J8 (q := q) δ Tr St r) : DataJ8 (q := q) δ Tr St r P :=
  { R with Tr40 := Tr, St40 := St40 St, l40 := sum40 L, π40 := id, hπ40 := hπ40_id St, eps40 := epsilon_sum40 L }

/-- `withLift` keeps every other field. -/
theorem withLift_sumJ8 (R : DataJ8 (q := q) δ Tr St r P) (L : Data40J8 (q := q) δ Tr St r) (s : SummandM)
    (hs : s ≠ .fortieth) : sumJ8 (withLift R L) s = sumJ8 R s := by
  cases s <;> first | exact absurd rfl hs | rfl

/-! ## 5. Outside `allJ8 (withLift R L)` -/

/-- Outside the J-8 list, outside every summand of the 40th's class at `toVSQ χ`. -/
theorem outside40 (R : DataJ8 (q := q) δ Tr St r P) (L : Data40J8 (q := q) δ Tr St r) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8 (withLift R L), ¬ s.mem tr χ) :
    ∀ s ∈ sum40 L, ¬ s.mem tr (toVSQ χ) := by
  intro s hs hm
  have h1 := outside_sumJ8 (withLift R L) h .fortieth
  refine h1 (liftJ8 s id (hπ40_id St)) (List.mem_map.mpr ⟨s, hs, rfl⟩) ?_
  rw [mem_liftJ8]
  exact hm

theorem cw_out (L : Data40J8 (q := q) δ Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40 L, ¬ s.mem tr ψ) : (ψ v13, ψ v14) ∉ cwEvent (K := K) (L.cRows tr) (L.cH tr) := by
  have := h (cwalkL L) (by simp [sum40])
  erw [cwalkL, mem_specSummandF] at this; exact this

theorem tile_out (L : Data40J8 (q := q) δ Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40 L, ¬ s.mem tr ψ) : ψ v13 ∉ tileSet (K := K) (foOf (L.cRows tr)) (L.cH tr) := by
  have := h (ctileL L) (by simp [sum40])
  erw [ctileL, Compute.SummandsQ7.coinSummand_mem] at this; exact this

theorem dyck_out (L : Data40J8 (q := q) δ Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40 L, ¬ s.mem tr ψ) :
    Quad.mk δ (ψ v2) (ψ v3) ∉ cellDyckRootSeeds (Kfp := 𝕂′) fuelChip (L.rowsD tr) := by
  have := h (dyckL L) (by simp [sum40])
  unfold dyckL cellDyckRootSummand at this
  rwa [towerSeedSummand_mem_iff] at this

theorem wchain_out (L : Data40J8 (q := q) δ Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40 L, ¬ s.mem tr ψ) : (ψ v0, ψ v1) ∉ WalkVCL.walkEvent δ (L.wdW tr ψ) := by
  have := h (wchainL L) (by simp [sum40])
  erw [wchainL, mem_specSummandF] at this; exact this

theorem fpx_out (L : Data40J8 (q := q) δ Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40 L, ¬ s.mem tr ψ) (h1 : (L.fxReqs tr ψ).length ≤ r.W) (h2 : (L.fxProvs tr ψ).length ≤ 2 * r.D) :
    (Quad.mk δ (ψ v4) (ψ v6), Quad.mk δ (ψ v5) (ψ v7)) ∉ IOFailureEventW (L.fxReqs tr ψ) (L.fxProvs tr ψ) := by
  have := h (fpxL L) (by simp [sum40])
  rw [fpxL, mem_ioSummandF, evIO_of_guard h1 h2] at this
  exact this

theorem zero_out (L : Data40J8 (q := q) δ Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40 L, ¬ s.mem tr ψ) : Quad.mk δ (ψ v2) (ψ v3) ≠ 0 := by
  have := h (zeroL L) (by simp [sum40])
  rw [zeroL, towerSeedSummand_mem_iff, Finset.mem_singleton] at this
  exact this

theorem census_out (L : Data40J8 (q := q) δ Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40 L, ¬ s.mem tr ψ) :
    Quad.mk δ (ψ v2) (ψ v3) ∉ tableBadSeeds (Kfp := 𝕂′) r.Λ (L.rowsD tr) (L.skelD tr) := by
  have := h (censusL L) (by simp [sum40])
  rwa [censusL, tableCensusSummand_mem_iff] at this

theorem val_out (L : Data40J8 (q := q) δ Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40 L, ¬ s.mem tr ψ) (h1 : (L.vReqs tr ψ).length ≤ 3 + 2 * r.D) (h2 : (L.vProvs tr ψ).length ≤ r.D) :
    (Quad.mk δ (ψ v4) (ψ v6), Quad.mk δ (ψ v5) (ψ v7)) ∉ IOFailureEventW (L.vReqs tr ψ) (L.vProvs tr ψ) := by
  have := h (valL L) (by simp [sum40])
  rw [valL, mem_ioSummandF, evIO_of_guard h1 h2] at this
  exact this

theorem hx_out (L : Data40J8 (q := q) δ Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40 L, ¬ s.mem tr ψ) (h1 : (L.xReqs tr ψ).length ≤ 3 * r.N + r.W)
    (h2 : (L.xProvs tr ψ).length ≤ r.D) :
    (Quad.mk δ (ψ v11) (ψ cGamHi), Quad.mk δ (ψ v12) (ψ cRhoHi)) ∉
      IOFailureEventW (L.xReqs tr ψ) (L.xProvs tr ψ) := by
  have := h (hxL L) (by simp [sum40])
  rw [hxL, mem_ioSummandF, evIO_of_guard h1 h2] at this
  exact this

theorem hp_out (L : Data40J8 (q := q) δ Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40 L, ¬ s.mem tr ψ) (h1 : (L.pReqs tr ψ).length ≤ 2 * r.N)
    (h2 : (L.pProvs tr ψ).length ≤ 2 * r.W) :
    (Quad.mk δ (ψ v11) (ψ cGamHi), Quad.mk δ (ψ v12) (ψ cRhoHi)) ∉
      IOFailureEventW (L.pReqs tr ψ) (L.pProvs tr ψ) := by
  have := h (hpL L) (by simp [sum40])
  rw [hpL, mem_ioSummandF, evIO_of_guard h1 h2] at this
  exact this

end Data

/-! ## 6. The `FinalJ8` shapes -/

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 chalsMJ8 coinsCV_J8)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- The compute walk coin `αW` at `frameJ8`: `XCtx.hα`'s value is `χ₁₃`. -/
theorem limb_alphaW_J8 (b : Module.Basis (Fin 3) (ZMod p) K) (χ : Coins frameJ8 K) :
    limbVal b (chalVJ8 b χ) ChipH.chalAlphaW = χ c13 := by
  have e : limbVal b (chalVJ8 b χ) ChipH.chalAlphaW =
      limbVal b (FrameVS.chalVH b (toVS (toVSQ χ))) ChipH.chalAlphaW := by
    unfold limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := k.isLt
    rw [VerJ8.chalVJ8, chalVHQ_old b (toVSQ χ) _ (by simp only [ChipH.chalAlphaW]; omega)]
  rw [e, FrameVS.limb_chal_alpha]
  rfl

/-- The compute walk coin `γW` at `frameJ8`: `XCtx.hγ`'s value is `χ₁₄`. -/
theorem limb_gammaW_J8 (b : Module.Basis (Fin 3) (ZMod p) K) (χ : Coins frameJ8 K) :
    limbVal b (chalVJ8 b χ) ChipH.chalGammaW = χ c14 := by
  have e : limbVal b (chalVJ8 b χ) ChipH.chalGammaW =
      limbVal b (FrameVS.chalVH b (toVS (toVSQ χ))) ChipH.chalGammaW := by
    unfold limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := k.isLt
    rw [VerJ8.chalVJ8, chalVHQ_old b (toVSQ χ) _ (by simp only [ChipH.chalGammaW]; omega)]
  rw [e, FrameVS.limb_chal_gamma]
  rfl

/-- **`FinalJ8`'s `hw`**: outside the J-8 list, if the readout's compute rows are `rows` (length `n`), the walk
coins `(α, γ)` (`XCtx.hα / hγ`) are outside `cwEvent rows n`. -/
theorem hw_of_outside40 (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (b : Module.Basis (Fin 3) (ZMod p) K)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8 (withLift R L), ¬ s.mem tr χ)
    {rows : ℕ → RowVSX} {n : ℕ} (hr : L.cRows tr = rows) (hn : L.cH tr = n) {α γ : K}
    (hα : limbVal b (chalVJ8 b χ) ChipH.chalAlphaW = α) (hγ : limbVal b (chalVJ8 b χ) ChipH.chalGammaW = γ) :
    (α, γ) ∉ cwEvent (K := K) rows n := by
  rw [← hα, ← hγ, limb_alphaW_J8, limb_gammaW_J8, ← hr, ← hn]
  exact cw_out L (outside40 R L h)

/-- **`FinalJ8`'s `hα`**: outside the J-8 list, `α ∉ tileSet (foOf rows) n`. -/
theorem hα_of_outside40 (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (b : Module.Basis (Fin 3) (ZMod p) K)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8 (withLift R L), ¬ s.mem tr χ)
    {rows : ℕ → RowVSX} {n : ℕ} (hr : L.cRows tr = rows) (hn : L.cH tr = n) {α : K}
    (hα : limbVal b (chalVJ8 b χ) ChipH.chalAlphaW = α) :
    α ∉ tileSet (K := K) (foOf rows) n := by
  rw [← hα, limb_alphaW_J8, ← hr, ← hn]
  exact tile_out L (outside40 R L h)

/-- **`FinalJ8`'s `hout .p`**: outside the J-8 list, if the readout's path lists at `toVSQ χ` are the `p`
balance's (`reqsJ8 … ext .p`, `liftP (provs .p)`) and fit `(2N, 2W)`, the compute coins `coinsCV (chalVJ8 b χ)`
are outside their IO event. -/
theorem hout_p_of_outside40 (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (b : Module.Basis (Fin 3) (ZMod p) K)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8 (withLift R L), ¬ s.mem tr χ)
    (reqs : List (Fin 5 → 𝕂′)) (provs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hr : L.pReqs tr (toVSQ χ) = reqs) (hp : L.pProvs tr (toVSQ χ) = provs)
    (h1 : reqs.length ≤ 2 * r.N) (h2 : provs.length ≤ 2 * r.W) :
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW reqs provs := by
  rw [coinsCV_J8 δ b χ]
  subst hr hp
  exact hp_out L (outside40 R L h) h1 h2

/-- **The cell table's `hz`** (`provOK_x`'s first premise) at any memory vector agreeing with `chalsMJ8` at leaves
`2, 3`: outside the J-8 list, `z ≠ 0` (the 40th's zero-seed summand, in #1). -/
theorem hz_of_outside40 (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8 (withLift R L), ¬ s.mem tr χ)
    (chals : ℕ → K) (h2 : chals 2 = chalsMJ8 δ χ 2) (h3 : chals 3 = chalsMJ8 δ χ 3) :
    Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ≠ 0 := by
  rw [h2, h3, chalsMJ8_lo δ χ 2 (by norm_num), chalsMJ8_lo δ χ 3 (by norm_num)]
  have hz := zero_out L (outside40 R L h)
  have e2 : FrameVS.chalsVS δ (toVS (toVSQ χ)) 2 = toVSQ χ v2 := by
    simp [FrameVS.chalsVS, Chips.ChipRAP.chalsVCL, CellH.hGam, CellH.hRho, FrameVS.toVCL, toVS, v2]
  have e3 : FrameVS.chalsVS δ (toVS (toVSQ χ)) 3 = toVSQ χ v3 := by
    simp [FrameVS.chalsVS, Chips.ChipRAP.chalsVCL, CellH.hGam, CellH.hRho, FrameVS.toVCL, toVS, v3]
  rw [e2, e3]
  exact hz

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8
