/-
  Nock/NockVMROM/Thm54/VclL/Handle/WeightsJ8.lean

`FrameJ8.weightJ8` lists the ten weights as SHAPES (U).  Here each summand is a
  `BadSummand frameJ8 K Tr St` (so `card_le` is a field, i.e. proved), built from the chip's record
  lists / rows / walk data, which enter as readouts of an abstract trace type `Tr` (`DataJ8`): the
  J-8 trace shape (`tableJ8` / `shapeJ8` / `VerifierData`) does not exist yet.  Every event is a
  Finset over the summand's coins (the `classJ8` coins; no new coin):

  * §1 coin specs: `specV` = `γ′ρ′` (`4,6 / 5,7`), `specH` = `γH′ρH′` (`11,15 / 12,16`), `specZY` =
    `(z, y)` (`2,3 / 17,18`), the walk pair `13, 14` (`αW γW`), `y` = `17, 18`.
  * §2 `specSummand`: any bad set of coin pairs `(I.pair χ) ∈ bad tr χ` as a summand on `I.dep`
    (`card_le` via `extIO_inj`).
  * §3 `evIO` (the weighted IO failure event, guarded by the row budgets `k₁ k₂`), `evIO_card`
    `≤ ioFUB m k₁ k₂ |𝕂′|`; `ioSummandJ8`.  #2–#5 and the merged #6/#7 (W2).
  * §4 the atom census at `y` (#8): the cell table's dyck-root, T2 census and zero-seed summands
    instantiated at coins `17, 18` (the 40th's `dyckVS` / `censusVS` / `zeroVS` shapes).
  * §5 the atom walk (#9): `walkEvent` at `(αW, γW)` with the walk data a readout depending on `y`
    (`dep = {17, 18}`), weight `|𝕂|·15·AW`.
  * §6 the bivariate census: `bivEvent`, the union over the census pairs of
    `{(z, y) | leafSum y z ns = leafSum y z ms}`, card `≤ P·(|𝕂′|(k−1) + |𝕂′|(M−1))`
    (A-1 `card_leafSum_collision_le`).
  * §7 the J chip's slot counts (`consK ≤ 2`, `provK ≤ 1`, service / export-read slots `≤ 1` per
    row): the #7 budget `(2J, J)` and the #5 / #6 J parts are chip facts.
  * §8 `liftJ8`: a `frameVSQ` summand as a `frameJ8` summand (`dep ∪ {y₁, y₂}`), same weight and
    coin count (`epsilonOf_map_liftJ8`): summand #1.
  * §9 `DataJ8`, `sumJ8 : SummandM → List BadSummand`, `epsilon_sumJ8` (each summand's `ε` is
    `weightJ8P`), `epsilon_allJ8 = boundJ8P`.
  * §10 figures at `|𝕂| = p³`: `boundJ8P < 2^-155` at every row count `≤ 2^31` (`figJ8_155`),
    tight at the corner (`figJ8_not_156`); the new dominant term is the atom walk `15·AW/|𝕂|`.

  **W2: #6 service and #7 J in-chip are MERGED** into one IO summand (`SummandM.service`,
  nine summands): arity 8, consumers `N + 2J`, providers `calls + heads + blocks + J`; `DataJ8` has one
  field group `sv*` for it.  `epsilon_allJ8`, `figJ8_155`, `figJ8_not_156` re-proved over the merged list.

  **Not kernel-checked here (P3 / J-8b obligations, recorded as fields of `DataJ8`):** that the
  chip-derived record lists of the J-8 traces are the readouts (lengths within the budgets, read-sets
  as stated), and that the 40th's list lifts (`hπ`).  The guards make every card bound
  unconditional; outside a guard the event is empty, so an assembly must show the guard holds.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
import Nock.NockVMROM.Thm54.VclL.Walk.WalkEvent
import Nock.NockVMROM.Thm54.P8Core.VclL.DyckRoot
import Nock.Atoms.Fingerprint
import Nock.Jet.ChipJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Events

noncomputable section

/-! ## 1. Coin specs at `frameJ8` -/

def c2 : Fin frameJ8.n := ⟨2, by decide⟩
def c3 : Fin frameJ8.n := ⟨3, by decide⟩
def c4 : Fin frameJ8.n := ⟨4, by decide⟩
def c5 : Fin frameJ8.n := ⟨5, by decide⟩
def c6 : Fin frameJ8.n := ⟨6, by decide⟩
def c7 : Fin frameJ8.n := ⟨7, by decide⟩
def c11 : Fin frameJ8.n := ⟨11, by decide⟩
def c12 : Fin frameJ8.n := ⟨12, by decide⟩
def c13 : Fin frameJ8.n := ⟨13, by decide⟩
def c14 : Fin frameJ8.n := ⟨14, by decide⟩
def c15 : Fin frameJ8.n := ⟨15, by decide⟩
def c16 : Fin frameJ8.n := ⟨16, by decide⟩

/-- The limb coin's two coordinates. -/
def yDep : Finset (Fin frameJ8.n) := {cY1, cY2}

section Specs
variable {K Kio : Type} [Field K] (mk : K → K → Kio) (hmk : ∀ a b c d, mk a b = mk c d → a = c ∧ b = d)

/-- `γ′ = mk χ₄ χ₆`, `ρ′ = mk χ₅ χ₇` (validity class). -/
def specV : IOCoinSpec frameJ8 K Kio := IOCoinSpec.ofExt frameJ8 mk hmk (c4, c6) (c5, c7)
/-- `γH′ = mk χ₁₁ χ₁₅`, `ρH′ = mk χ₁₂ χ₁₆` (handle class). -/
def specH : IOCoinSpec frameJ8 K Kio := IOCoinSpec.ofExt frameJ8 mk hmk (c11, c15) (c12, c16)
/-- `z = mk χ₂ χ₃`, `y = mk χ₁₇ χ₁₈`. -/
def specZY : IOCoinSpec frameJ8 K Kio := IOCoinSpec.ofExt frameJ8 mk hmk (c2, c3) (cY1, cY2)
/-- `(αW, γW) = (χ₁₃, χ₁₄)` in `𝕂`. -/
def specW : IOCoinSpec frameJ8 K K := IOCoinSpec.ofPair frameJ8 K c13 c14

theorem specV_dep_card : (specV mk hmk).dep.card = 4 := rfl
theorem specH_dep_card : (specH mk hmk).dep.card = 4 := rfl
theorem specZY_dep_card : (specZY mk hmk).dep.card = 4 := rfl
theorem specW_dep_card : (specW (K := K)).dep.card = 2 := rfl

theorem specV_disj : Disjoint (specV mk hmk).dep (coinsBelow frameJ8 1) := by
  show Disjoint ({c4, c6, c5, c7} : Finset (Fin frameJ8.n)) (coinsBelow frameJ8 1); decide
theorem specH_disj_y : Disjoint (specH mk hmk).dep yDep := by
  show Disjoint ({c11, c15, c12, c16} : Finset (Fin frameJ8.n)) yDep; decide
theorem specH_disj : Disjoint (specH mk hmk).dep ∅ := Finset.disjoint_empty_right _
theorem specZY_disj : Disjoint (specZY mk hmk).dep ∅ := Finset.disjoint_empty_right _
theorem specW_disj_y : Disjoint (specW (K := K)).dep yDep := by
  show Disjoint ({c13, c14} : Finset (Fin frameJ8.n)) yDep; decide

/-- The classes of `classJ8`: each spec's coins (and read set) are the listed indices. -/
theorem specV_class : ((specV mk hmk).dep.image Fin.val) = {4, 6, 5, 7} := by
  show (({c4, c6, c5, c7} : Finset (Fin frameJ8.n)).image Fin.val) = _; decide
theorem specH_class : ((specH mk hmk).dep.image Fin.val) = {11, 15, 12, 16} := by
  show (({c11, c15, c12, c16} : Finset (Fin frameJ8.n)).image Fin.val) = _; decide
theorem specZY_class : ((specZY mk hmk).dep.image Fin.val) = {2, 3, 17, 18} := by
  show (({c2, c3, cY1, cY2} : Finset (Fin frameJ8.n)).image Fin.val) = _; decide
theorem specW_class : ((specW (K := K)).dep.image Fin.val) = {13, 14} := by
  show (({c13, c14} : Finset (Fin frameJ8.n)).image Fin.val) = _; decide
theorem yDep_class : yDep.image Fin.val = {17, 18} := by decide

end Specs

/-! ## 2. A bad set of coin pairs as a summand -/

section Spec
variable {K Kio : Type} [Field K] [Fintype K] [DecidableEq K] [Field Kio] [Fintype Kio] [DecidableEq Kio]

open Classical in
/-- **`specSummand`**: the event `I.pair χ ∈ bad tr χ` on the coins `I.dep`, reading `dep`. -/
def specSummand (I : IOCoinSpec frameJ8 K Kio) (dep : Finset (Fin frameJ8.n)) (hdisj : Disjoint I.dep dep)
    {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop) (bad : Tr → Coins frameJ8 K → Finset (Kio × Kio))
    (W : ℕ) (hW : ∀ tr χ, (bad tr χ).card ≤ W)
    (hreads : ∀ Q, St Q → ReadsOnC frameJ8 dep (fun χ => bad (Q χ) χ)) :
    BadSummand frameJ8 K Tr St where
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

theorem mem_specSummand (I : IOCoinSpec frameJ8 K Kio) (dep : Finset (Fin frameJ8.n))
    (hdisj : Disjoint I.dep dep) {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
    (bad : Tr → Coins frameJ8 K → Finset (Kio × Kio)) (W : ℕ) (hW hreads) (tr : Tr) (χ : Coins frameJ8 K) :
    (specSummand I dep hdisj St bad W hW hreads).mem tr χ ↔ I.pair χ ∈ bad tr χ := by
  unfold BadSummand.mem
  show (fun i : I.dep => χ i) ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter, pair_extIO]
  simp

theorem specSummand_weight (I : IOCoinSpec frameJ8 K Kio) (dep : Finset (Fin frameJ8.n))
    (hdisj : Disjoint I.dep dep) {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
    (bad : Tr → Coins frameJ8 K → Finset (Kio × Kio)) (W : ℕ) (hW hreads) :
    (specSummand I dep hdisj St bad W hW hreads).weight = W ∧
      (specSummand I dep hdisj St bad W hW hreads).coins = I.dep := ⟨rfl, rfl⟩

theorem eps_specSummand (I : IOCoinSpec frameJ8 K Kio) (dep : Finset (Fin frameJ8.n))
    (hdisj : Disjoint I.dep dep) {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
    (bad : Tr → Coins frameJ8 K → Finset (Kio × Kio)) (W : ℕ) (hW hreads) :
    epsilonOf [specSummand I dep hdisj St bad W hW hreads] = (W : ℚ) / (Fintype.card K : ℚ) ^ I.dep.card := by
  simp only [epsilonOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rfl

end Spec

/-! ## 3. The IO events (#2–#7) -/

section IO
variable {K Kio : Type} [Field K] [Fintype K] [DecidableEq K] [Field Kio] [Fintype Kio] [DecidableEq Kio]

open Classical in
/-- **The guarded weighted IO failure event**: the 40th's `IOFailureEventW` of the round's record
lists when they fit the row budgets (`≤ k₁` consumers, `≤ k₂` providers), else `∅`. -/
def evIO {m : ℕ} (reqs : List (Fin m → Kio)) (provs : List ((Fin m → Kio) × Kio)) (k₁ k₂ : ℕ) :
    Finset (Kio × Kio) :=
  if reqs.length ≤ k₁ ∧ provs.length ≤ k₂ then IOFailureEventW reqs provs else ∅

theorem evIO_card {m : ℕ} (reqs : List (Fin m → Kio)) (provs : List ((Fin m → Kio) × Kio)) (k₁ k₂ : ℕ) :
    (evIO reqs provs k₁ k₂).card ≤ ioFailureUnionBound m k₁ k₂ (Fintype.card Kio) := by
  unfold evIO
  split_ifs with h
  · exact (IOFailureEventW_card_le _ _).trans (ioFUB_mono _ _ h.1 h.2)
  · simp

theorem evIO_of_guard {m : ℕ} {reqs : List (Fin m → Kio)} {provs : List ((Fin m → Kio) × Kio)} {k₁ k₂ : ℕ}
    (h1 : reqs.length ≤ k₁) (h2 : provs.length ≤ k₂) : evIO reqs provs k₁ k₂ = IOFailureEventW reqs provs := by
  unfold evIO; rw [if_pos ⟨h1, h2⟩]

/-- **An IO summand at `frameJ8`**: arity `m`, budgets `k₁ k₂`, weight `ioFUB m k₁ k₂ |𝕂′|`. -/
def ioSummandJ8 (I : IOCoinSpec frameJ8 K Kio) (dep : Finset (Fin frameJ8.n)) (hdisj : Disjoint I.dep dep)
    {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop) {m : ℕ}
    (reqs : Tr → Coins frameJ8 K → List (Fin m → Kio)) (provs : Tr → Coins frameJ8 K → List ((Fin m → Kio) × Kio))
    (k₁ k₂ : ℕ) (hreads : ∀ Q, St Q → ReadsOnC frameJ8 dep (fun χ => (reqs (Q χ) χ, provs (Q χ) χ))) :
    BadSummand frameJ8 K Tr St :=
  specSummand I dep hdisj St (fun tr χ => evIO (reqs tr χ) (provs tr χ) k₁ k₂)
    (ioFailureUnionBound m k₁ k₂ (Fintype.card Kio)) (fun _ _ => evIO_card _ _ _ _)
    (fun Q hQ χ χ' h => by
      have e := hreads Q hQ χ χ' h
      simp only [Prod.mk.injEq] at e
      show evIO _ _ _ _ = evIO _ _ _ _
      rw [e.1, e.2])

end IO

/-! ## 4. The atom census at `y` (#8) -/

section Census
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] (δ : K) [Fact (¬ IsSquare δ)] {q : ℕ}

/-- **The atom table's dyck-root summand at `y`** (coins `17, 18`, weight `A·(2·fuelChip − 1)`). -/
def atomDyckJ8 {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop) (rowsA : Tr → List (CellRowB0 q)) (A : ℕ)
    (hA : ∀ tr, (rowsA tr).length ≤ A) (hc : ∀ Q, St Q → ∀ χ χ', rowsA (Q χ) = rowsA (Q χ')) :
    BadSummand frameJ8 K Tr St :=
  cellDyckRootSummand δ frameJ8 cY1 cY2 St rowsA A fuelChip hA hc

/-- **The atom table's T2 census at `y`** (skeleton `≤ 3`, weight `pairCount (A + 3)·(2Λ − 1)`). -/
def atomCensusJ8 {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop) (rowsA : Tr → List (CellRowB0 q))
    (skelA : Tr → List Nock.Noun) (A Λ : ℕ) (hA : ∀ tr, (rowsA tr).length ≤ A) (hs : ∀ tr, (skelA tr).length ≤ 3)
    (hc : ∀ Q, St Q → ∀ χ χ', rowsA (Q χ) = rowsA (Q χ') ∧ skelA (Q χ) = skelA (Q χ')) :
    BadSummand frameJ8 K Tr St :=
  tableCensusSummand δ frameJ8 cY1 cY2 St rowsA skelA A 3 Λ hA hs hc

/-- **The zero limb coin** `y = 0` (weight `1`). -/
def zeroYJ8 {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop) : BadSummand frameJ8 K Tr St :=
  towerSeedSummand δ frameJ8 cY1 cY2 St (fun _ => {0}) 1 (fun _ => by simp) (fun _ _ _ _ => rfl)

theorem mem_zeroYJ8 {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop) (tr : Tr) (χ : Coins frameJ8 K) :
    (zeroYJ8 δ St).mem tr χ ↔ Quad.mk δ (χ cY1) (χ cY2) = 0 := by
  unfold zeroYJ8
  rw [towerSeedSummand_mem_iff, Finset.mem_singleton]

end Census

/-! ## 5. The atom walk (#9) -/

section Walk
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  (δ : K) [Fact (¬ IsSquare δ)]

/-- **The atom-walk summand** (coins `(αW, γW) = (13, 14)`, reading `y`): `walkEvent` at the atom
walk's data (labels at `y`), weight `|𝕂|·15·AW`. -/
def atomWalkJ8 {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
    (wd : Tr → Coins frameJ8 K → WalkVCL.WalkData q (Quad δ)) (AW : ℕ) (hAW : ∀ tr χ, (wd tr χ).h ≤ AW)
    (hreads : ∀ Q, St Q → ReadsOnC frameJ8 yDep (fun χ => wd (Q χ) χ)) : BadSummand frameJ8 K Tr St :=
  specSummand (specW (K := K)) yDep specW_disj_y St (fun tr χ => WalkVCL.walkEvent δ (wd tr χ))
    (Fintype.card K * (15 * AW)) (fun tr χ => WalkVCL.walkEvent_card δ _ (hAW tr χ))
    (fun Q hQ χ χ' h => by simp only [hreads Q hQ χ χ' h])

theorem mem_atomWalkJ8 {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop)
    (wd : Tr → Coins frameJ8 K → WalkVCL.WalkData q (Quad δ)) (AW : ℕ) (hAW hreads) (tr : Tr)
    (χ : Coins frameJ8 K) :
    (atomWalkJ8 δ St wd AW hAW hreads).mem tr χ ↔ (χ c13, χ c14) ∈ WalkVCL.walkEvent δ (wd tr χ) :=
  mem_specSummand _ _ _ _ _ _ _ _ tr χ

end Walk

/-! ## 6. The bivariate census -/

section Biv
open Nock.Atoms
variable {Kio : Type} [Field Kio] [Algebra Fp Kio] [Fintype Kio] [DecidableEq Kio]

open Classical in
/-- One census pair's event: same-length, distinct, `≤ k` leaves, every atom `≤ M` limbs, and equal
bivariate leaf coordinates at `(z, y)`. -/
def pairEv (k M : ℕ) (pr : List ℕ × List ℕ) : Finset (Kio × Kio) :=
  if pr.1.length = pr.2.length ∧ pr.1 ≠ pr.2 ∧ pr.1.length ≤ k ∧ (∀ a ∈ pr.1, lenL a ≤ M) ∧
      (∀ a ∈ pr.2, lenL a ≤ M) then
    Finset.univ.filter fun zy : Kio × Kio => leafSum zy.2 zy.1 pr.1 = leafSum zy.2 zy.1 pr.2
  else ∅

theorem pairEv_card (k M : ℕ) (pr : List ℕ × List ℕ) :
    (pairEv (Kio := Kio) k M pr).card ≤ Fintype.card Kio * (k - 1) + Fintype.card Kio * (M - 1) := by
  unfold pairEv
  split_ifs with h
  · obtain ⟨hlen, hne, hk, hM1, hM2⟩ := h
    have : ∃ j, ∃ hj : j < pr.1.length, pr.1[j] ≠ pr.2[j]'(hlen ▸ hj) := by
      by_contra hno
      push Not at hno
      exact hne (List.ext_getElem hlen fun j h1 _ => hno j h1)
    obtain ⟨j, hj, hd⟩ := this
    have hM : max (lenL pr.1[j]) (lenL (pr.2[j]'(hlen ▸ hj))) ≤ M :=
      max_le (hM1 _ (List.getElem_mem _)) (hM2 _ (List.getElem_mem _))
    refine (card_leafSum_collision_le hlen hj hd hM).trans ?_
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hk 1)) _
  · simp

open Classical in
/-- **The bivariate census event**: some census pair collides at `(z, y)`. -/
def bivEvent (prs : List (List ℕ × List ℕ)) (k M : ℕ) : Finset (Kio × Kio) :=
  prs.toFinset.biUnion (pairEv k M)

theorem bivEvent_card (prs : List (List ℕ × List ℕ)) (k M P : ℕ) (hP : prs.length ≤ P) :
    (bivEvent (Kio := Kio) prs k M).card ≤ P * (Fintype.card Kio * (k - 1) + Fintype.card Kio * (M - 1)) := by
  unfold bivEvent
  refine (Finset.card_biUnion_le_card_mul _ _ _ fun pr _ => pairEv_card k M pr).trans ?_
  exact Nat.mul_le_mul_right _ ((List.toFinset_card_le _).trans hP)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] (mk : K → K → Kio)
  (hmk : ∀ a b c d, mk a b = mk c d → a = c ∧ b = d)

/-- **The bivariate census summand** (coins `2, 3, 17, 18`, round-0 pairs, weight
`P·(|𝕂′|(k−1) + |𝕂′|(M−1))`). -/
def bivJ8 {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop) (prs : Tr → List (List ℕ × List ℕ)) (k M P : ℕ)
    (hP : ∀ tr, (prs tr).length ≤ P) (hc : ∀ Q, St Q → ∀ χ χ', prs (Q χ) = prs (Q χ')) :
    BadSummand frameJ8 K Tr St :=
  specSummand (specZY mk hmk) ∅ (specZY_disj mk hmk) St (fun tr _ => bivEvent (prs tr) k M)
    (P * (Fintype.card Kio * (k - 1) + Fintype.card Kio * (M - 1))) (fun tr _ => bivEvent_card _ _ _ _ (hP tr))
    (fun Q hQ χ χ' _ => by simp only [hc Q hQ χ χ'])

theorem mem_bivJ8 {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop) (prs : Tr → List (List ℕ × List ℕ))
    (k M P : ℕ) (hP hc) (tr : Tr) (χ : Coins frameJ8 K) :
    (bivJ8 mk hmk St prs k M P hP hc).mem tr χ ↔
      (mk (χ c2) (χ c3), mk (χ cY1) (χ cY2)) ∈ bivEvent (prs tr) k M :=
  mem_specSummand _ _ _ _ _ _ _ _ tr χ

/-- Outside the event, a census pair's leaf coordinates separate. -/
theorem leafSum_ne_of_not_mem {prs : List (List ℕ × List ℕ)} {k M : ℕ} {z y : Kio}
    (h : (z, y) ∉ bivEvent prs k M) {pr : List ℕ × List ℕ} (hpr : pr ∈ prs)
    (hlen : pr.1.length = pr.2.length) (hne : pr.1 ≠ pr.2) (hk : pr.1.length ≤ k)
    (hM1 : ∀ a ∈ pr.1, lenL a ≤ M) (hM2 : ∀ a ∈ pr.2, lenL a ≤ M) :
    leafSum y z pr.1 ≠ leafSum y z pr.2 := by
  intro heq
  apply h
  unfold bivEvent
  rw [Finset.mem_biUnion]
  refine ⟨pr, List.mem_toFinset.mpr hpr, ?_⟩
  unfold pairEv
  rw [if_pos ⟨hlen, hne, hk, hM1, hM2⟩]
  simpa using heq

end Biv

/-! ## 7. The J chip's slot counts (#5 / #6 / #7 budgets from `jetChipJ8`) -/

section JChip
open Nock.Jet.ChipJ8
variable {F : Type} [Field F]

theorem keysOf_ents0_le (r : CRow F) : (keysOf ents0 r).length ≤ 1 := by
  unfold keysOf; rw [List.length_map]; cases r.pre.kd <;> decide
theorem keysOf_ents1_le (r : CRow F) : (keysOf ents1 r).length ≤ 1 := by
  unfold keysOf; rw [List.length_map]; cases r.pre.kd <;> decide
theorem keysOf_ents2_le (r : CRow F) : (keysOf ents2 r).length ≤ 1 := by
  unfold keysOf; rw [List.length_map]; cases r.pre.kd <;> decide
theorem keysOf_ents3_le (r : CRow F) : (keysOf ents3 r).length ≤ 1 := by
  unfold keysOf; rw [List.length_map]; cases r.pre.kd <;> decide
theorem keysOf_entsX_le (r : CRow F) : (keysOf entsX r).length ≤ 1 := by
  unfold keysOf; rw [List.length_map]; cases r.pre.kd <;> decide

/-- **Two in-chip consumes, one in-chip provide per J row.** -/
theorem consK_length_le (r : CRow F) : (consK r).length ≤ 2 := by
  unfold consK; rw [List.length_append]
  have := keysOf_ents0_le r; have := keysOf_ents1_le r; omega
theorem provK_length_le (r : CRow F) : (provK r).length ≤ 1 := keysOf_ents2_le r

theorem length_flatMap_le' {α β : Type} (l : List α) (f : α → List β) (c : ℕ) (h : ∀ a, (f a).length ≤ c) :
    (l.flatMap f).length ≤ c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.length_append, List.length_cons]; have := h a; nlinarith

/-- The J rows' in-chip consumer list has `≤ 2J` entries, the provider list `≤ J`, the service
provides and export reads `≤ J` (the #7 budget `(2J, J)`; the J parts of #5 / #6). -/
theorem jLists_le (rows : List (CRow F)) {J : ℕ} (hJ : rows.length ≤ J) :
    (rows.flatMap consK).length ≤ 2 * J ∧ (rows.flatMap provK).length ≤ J ∧
      (rows.flatMap (keysOf ents3)).length ≤ J ∧ (rows.flatMap (keysOf entsX)).length ≤ J := by
  refine ⟨(length_flatMap_le' _ _ 2 consK_length_le).trans (by omega),
    (length_flatMap_le' _ _ 1 provK_length_le).trans (by omega),
    (length_flatMap_le' _ _ 1 keysOf_ents3_le).trans (by omega),
    (length_flatMap_le' _ _ 1 keysOf_entsX_le).trans (by omega)⟩

end JChip

/-! ## 8. Summand #1: lifting `frameVSQ` summands -/

section Lift
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The seventeen `frameVSQ` coins inside the nineteen. -/
def embJ8 : Fin frameVSQ.n ↪ Fin frameJ8.n :=
  ⟨fun i => ⟨i, lt_frameJ8 i⟩, fun _ _ h => Fin.ext (congrArg Fin.val h :)⟩

/-- A `frameVSQ` vector with the limb coin `(y₁, y₂)` appended. -/
def extY (ψ : Coins frameVSQ K) (y₁ y₂ : K) : Coins frameJ8 K := fun i =>
  if h : (i : ℕ) < 17 then ψ ⟨i, h⟩ else if (i : ℕ) = 17 then y₁ else y₂

theorem extY_toVSQ (χ : Coins frameJ8 K) : extY (toVSQ χ) (χ cY1) (χ cY2) = χ := by
  funext i
  unfold extY toVSQ
  have hi := i.isLt; change (i : ℕ) < 19 at hi
  split_ifs with h1 h2
  · rfl
  · congr 1; exact Fin.ext h2.symm
  · congr 1; exact Fin.ext (show 18 = (i : ℕ) by omega)

theorem embJ8_disj_y (s : Finset (Fin frameVSQ.n)) : Disjoint (s.map embJ8) yDep := by
  rw [Finset.disjoint_left]
  intro a ha hy
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp ha
  have := i.isLt; change (i : ℕ) < 17 at this
  simp only [yDep, Finset.mem_insert, Finset.mem_singleton, cY1, cY2, embJ8] at hy
  rcases hy with h | h <;> (have h' := congrArg Fin.val h; change (i : ℕ) = _ at h'; simp at h'; omega)

/-- **A `frameVSQ` summand at `frameJ8`**: coins mapped, read set mapped plus `y` (round-0 coins of
`frameJ8` the 40th's round-1 columns may now depend on).  Same weight.  `hπ`: fixing `y`, the
projected J-8 strategy is a staged 40th strategy. -/
def liftJ8 {Tr Tr' : Type} {St : (Coins frameVSQ K → Tr) → Prop} {St' : (Coins frameJ8 K → Tr') → Prop}
    (s : BadSummand frameVSQ K Tr St) (π : Tr' → Tr)
    (hπ : ∀ Q', St' Q' → ∀ y₁ y₂ : K, St fun ψ => π (Q' (extY ψ y₁ y₂))) :
    BadSummand frameJ8 K Tr' St' where
  coins := s.coins.map embJ8
  dep := s.dep.map embJ8 ∪ yDep
  disj := Finset.disjoint_union_right.mpr ⟨(Finset.disjoint_map embJ8).mpr s.disj, embJ8_disj_y _⟩
  badSet tr χ := Finset.univ.filter fun v : (s.coins.map embJ8) → K =>
    (fun i : s.coins => v ⟨embJ8 i, Finset.mem_map_of_mem _ i.2⟩) ∈ s.badSet (π tr) (toVSQ χ)
  weight := s.weight
  card_le tr χ := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun v : (s.coins.map embJ8) → K => fun i : s.coins => v ⟨embJ8 i, Finset.mem_map_of_mem _ i.2⟩) ?_ ?_)
      (s.card_le (π tr) (toVSQ χ))
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h
      funext x
      obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp x.2
      have := congrFun h ⟨i, hi⟩
      have hx : x = ⟨embJ8 i, Finset.mem_map_of_mem _ hi⟩ := Subtype.ext hix.symm
      rw [hx]; exact this
  readsOn Q' hQ' χ χ' hχ := by
    have hy1 : χ cY1 = χ' cY1 := hχ cY1 (Finset.mem_union_right _ (by simp [yDep]))
    have hy2 : χ cY2 = χ' cY2 := hχ cY2 (Finset.mem_union_right _ (by simp [yDep]))
    have hQ := hπ Q' hQ' (χ cY1) (χ cY2)
    have hr := s.readsOn _ hQ (toVSQ χ) (toVSQ χ')
      (fun j hj => hχ (embJ8 j) (Finset.mem_union_left _ (Finset.mem_map_of_mem _ hj)))
    have h1 : π (Q' χ) = π (Q' (extY (toVSQ χ) (χ cY1) (χ cY2))) := by rw [extY_toVSQ]
    have h2 : π (Q' χ') = π (Q' (extY (toVSQ χ') (χ cY1) (χ cY2))) := by rw [hy1, hy2, extY_toVSQ]
    show Finset.univ.filter _ = Finset.univ.filter _
    rw [h1, h2]
    simp only at hr
    rw [hr]

theorem mem_liftJ8 {Tr Tr' : Type} {St : (Coins frameVSQ K → Tr) → Prop} {St' : (Coins frameJ8 K → Tr') → Prop}
    (s : BadSummand frameVSQ K Tr St) (π : Tr' → Tr) (hπ) (tr : Tr') (χ : Coins frameJ8 K) :
    (liftJ8 (St' := St') s π hπ).mem tr χ ↔ s.mem (π tr) (toVSQ χ) := by
  unfold BadSummand.mem
  exact Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem epsilonOf_map_liftJ8 {Tr Tr' : Type} {St : (Coins frameVSQ K → Tr) → Prop}
    {St' : (Coins frameJ8 K → Tr') → Prop} (l : List (BadSummand frameVSQ K Tr St)) (π : Tr' → Tr) (hπ) :
    epsilonOf (l.map fun s => liftJ8 (St' := St') s π hπ) = epsilonOf l := by
  unfold epsilonOf
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  simp only [Function.comp_apply, liftJ8, Finset.card_map]

end Lift

/-! ## 9. The J-8 data, the summand list, `ε` -/

/-- **W2: the nine merged summands.**  `FrameJ8.SummandJ8`'s #6 (service) and #7 (J in-chip) are ONE
IO summand `service`, over the merged lists: consumers `N + 2J`, providers `calls + heads + blocks + J`, arity 8. -/
inductive SummandM
  | fortieth | cellValidity2 | atomValidity | atomExport | cellExport3 | service | atomCensus | atomWalk
  | bivariateCensus
  deriving DecidableEq, Fintype

/-- **The proved weights** (`c = |𝕂|`, `c′ = |𝕂′|`, `P` census pairs).  Replaces `FrameJ8.weightJ8`
(shapes): budgets are the per-summand row counts of `DataJ8`. -/
def weightJ8P (c c' : ℕ) (r : RowsJ8) (P : ℕ) : SummandM → ℚ
  | .fortieth => boundVCLHQ'' c c' r.N r.D r.W r.Λ
  | .cellValidity2 => (ioFailureUnionBound 5 (3 + 2 * r.D) (r.D + r.mb) c' : ℚ) / c ^ 4
  | .atomValidity => (ioFailureUnionBound 5 (3 + 2 * r.A) r.A c' : ℚ) / c ^ 4
  | .atomExport => (ioFailureUnionBound 5 (r.A + r.inc + r.AW) r.A c' : ℚ) / c ^ 4
  | .cellExport3 => (ioFailureUnionBound 5 (3 * r.N + r.W + r.rd) r.D c' : ℚ) / c ^ 4
  | .service => (ioFailureUnionBound 8 (r.N + 2 * r.J) (r.calls + r.heads + r.blocks + r.J) c' : ℚ) / c ^ 4
  | .atomCensus => ((r.A * (2 * fuelChip - 1) : ℕ) : ℚ) / c ^ 2 +
      ((pairCount (r.A + 3) * (2 * r.Λ - 1) : ℕ) : ℚ) / c ^ 2 + (1 : ℚ) / c ^ 2
  | .atomWalk => ((c * (15 * r.AW) : ℕ) : ℚ) / c ^ 2
  | .bivariateCensus => ((P * (c' * (r.leaves - 1) + c' * (r.maxlen - 1)) : ℕ) : ℚ) / c ^ 4

/-- **`boundJ8P`**: the sum of the ten proved weights. -/
def boundJ8P (c c' : ℕ) (r : RowsJ8) (P : ℕ) : ℚ := ∑ s : SummandM, weightJ8P c c' r P s

section Data
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  (δ : K) [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]

local notation "𝕂′" => Quad δ

/-- **The J-8 readouts of a trace type `Tr`** (staging `St`) at the row counts `r` (`P` census pairs):
for each summand the record lists / rows / walk data, their budgets and their read sets.  These are
the obligations of the J-8 trace frame (P3 / J-8b); every card bound below uses only them. -/
structure DataJ8 (Tr : Type) (St : (Coins frameJ8 K → Tr) → Prop) (r : RowsJ8) (P : ℕ) where
  /-- #1: the 40th's list, its trace projection and its `ε`. -/
  Tr40 : Type
  St40 : (Coins frameVSQ K → Tr40) → Prop
  l40 : List (BadSummand frameVSQ K Tr40 St40)
  π40 : Tr → Tr40
  hπ40 : ∀ Q', St Q' → ∀ y₁ y₂ : K, St40 fun ψ => π40 (Q' (extY ψ y₁ y₂))
  eps40 : epsilonOf l40 = boundVCLHQ'' (Fintype.card K) (Fintype.card 𝕂′) r.N r.D r.W r.Λ
  /-- #2 cell validity, two providers (`γ′ρ′`, round ≤ 1). -/
  valReqs : Tr → Coins frameJ8 K → List (Fin 5 → 𝕂′)
  valProvs : Tr → Coins frameJ8 K → List ((Fin 5 → 𝕂′) × 𝕂′)
  val_reads : ∀ Q, St Q → ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ => (valReqs (Q χ) χ, valProvs (Q χ) χ)
  /-- #3 atom validity at `y` (`γ′ρ′`). -/
  avReqs : Tr → Coins frameJ8 K → List (Fin 5 → 𝕂′)
  avProvs : Tr → Coins frameJ8 K → List ((Fin 5 → 𝕂′) × 𝕂′)
  av_reads : ∀ Q, St Q → ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ => (avReqs (Q χ) χ, avProvs (Q χ) χ)
  /-- #4 atom export (`γH′ρH′`, fingerprints at `y`). -/
  axReqs : Tr → Coins frameJ8 K → List (Fin 5 → 𝕂′)
  axProvs : Tr → Coins frameJ8 K → List ((Fin 5 → 𝕂′) × 𝕂′)
  ax_reads : ∀ Q, St Q → ReadsOnC frameJ8 yDep fun χ => (axReqs (Q χ) χ, axProvs (Q χ) χ)
  /-- #5 cell export, third consumer (`γH′ρH′`, round 0). -/
  cxReqs : Tr → Coins frameJ8 K → List (Fin 5 → 𝕂′)
  cxProvs : Tr → Coins frameJ8 K → List ((Fin 5 → 𝕂′) × 𝕂′)
  cx_reads : ∀ Q, St Q → ReadsOnC frameJ8 ∅ fun χ => (cxReqs (Q χ) χ, cxProvs (Q χ) χ)
  /-- #6 (merged with the J in-chip balance): service + J (`γH′ρH′`, round 0, arity 8). -/
  svReqs : Tr → Coins frameJ8 K → List (Fin 8 → 𝕂′)
  svProvs : Tr → Coins frameJ8 K → List ((Fin 8 → 𝕂′) × 𝕂′)
  sv_reads : ∀ Q, St Q → ReadsOnC frameJ8 ∅ fun χ => (svReqs (Q χ) χ, svProvs (Q χ) χ)
  /-- #8 the atom table's round-0 rows and census skeleton. -/
  rowsA : Tr → List (CellRowB0 q)
  skelA : Tr → List Nock.Noun
  rowsA_le : ∀ tr, (rowsA tr).length ≤ r.A
  skelA_le : ∀ tr, (skelA tr).length ≤ 3
  rowsA_const : ∀ Q, St Q → ∀ χ χ', rowsA (Q χ) = rowsA (Q χ') ∧ skelA (Q χ) = skelA (Q χ')
  /-- #9 the atom walk's data (labels at `y`). -/
  wdA : Tr → Coins frameJ8 K → WalkVCL.WalkData q 𝕂′
  wdA_le : ∀ tr χ, (wdA tr χ).h ≤ r.AW
  wdA_reads : ∀ Q, St Q → ReadsOnC frameJ8 yDep fun χ => wdA (Q χ) χ

  prs : Tr → List (List ℕ × List ℕ)
  prs_le : ∀ tr, (prs tr).length ≤ P
  prs_const : ∀ Q, St Q → ∀ χ χ', prs (Q χ) = prs (Q χ')

variable {δ} {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P : ℕ}

local notation "qmk" => Chips.quadMk_inj δ

/-- **The summands of each `SummandM`** (#8 is three: dyck, census, zero seed). -/
def sumJ8 (R : DataJ8 (q := q) δ Tr St r P) : SummandM → List (BadSummand frameJ8 K Tr St)
  | .fortieth => R.l40.map fun s => liftJ8 s R.π40 R.hπ40
  | .cellValidity2 => [ioSummandJ8 (specV (Quad.mk δ) qmk) _ (specV_disj _ _) St R.valReqs R.valProvs
      (3 + 2 * r.D) (r.D + r.mb) R.val_reads]
  | .atomValidity => [ioSummandJ8 (specV (Quad.mk δ) qmk) _ (specV_disj _ _) St R.avReqs R.avProvs
      (3 + 2 * r.A) r.A R.av_reads]
  | .atomExport => [ioSummandJ8 (specH (Quad.mk δ) qmk) _ (specH_disj_y _ _) St R.axReqs R.axProvs
      (r.A + r.inc + r.AW) r.A R.ax_reads]
  | .cellExport3 => [ioSummandJ8 (specH (Quad.mk δ) qmk) _ (specH_disj _ _) St R.cxReqs R.cxProvs
      (3 * r.N + r.W + r.rd) r.D R.cx_reads]
  | .service => [ioSummandJ8 (specH (Quad.mk δ) qmk) _ (specH_disj _ _) St R.svReqs R.svProvs
      (r.N + 2 * r.J) (r.calls + r.heads + r.blocks + r.J) R.sv_reads]
  | .atomCensus => [atomDyckJ8 δ St R.rowsA r.A R.rowsA_le (fun Q hQ χ χ' => (R.rowsA_const Q hQ χ χ').1),
      atomCensusJ8 δ St R.rowsA R.skelA r.A r.Λ R.rowsA_le R.skelA_le R.rowsA_const, zeroYJ8 δ St]
  | .atomWalk => [atomWalkJ8 δ St R.wdA r.AW R.wdA_le R.wdA_reads]
  | .bivariateCensus => [bivJ8 (Quad.mk δ) qmk St R.prs r.leaves r.maxlen P R.prs_le R.prs_const]

theorem eps_single (s : BadSummand frameJ8 K Tr St) :
    epsilonOf [s] = (s.weight : ℚ) / (Fintype.card K : ℚ) ^ s.coins.card := by
  simp [epsilonOf]

theorem eps_of {s : BadSummand frameJ8 K Tr St} {w n : ℕ} (hw : s.weight = w) (hn : s.coins.card = n) :
    epsilonOf [s] = (w : ℚ) / (Fintype.card K : ℚ) ^ n := by
  rw [eps_single, hw, hn]

theorem eps_three (a b c : BadSummand frameJ8 K Tr St) :
    epsilonOf [a, b, c] = (a.weight : ℚ) / (Fintype.card K : ℚ) ^ a.coins.card +
      ((b.weight : ℚ) / (Fintype.card K : ℚ) ^ b.coins.card + (c.weight : ℚ) / (Fintype.card K : ℚ) ^ c.coins.card) := by
  simp [epsilonOf]

/-- **Each summand's `ε` is its proved weight.** -/
theorem epsilon_sumJ8 (R : DataJ8 (q := q) δ Tr St r P) (s : SummandM) :
    epsilonOf (sumJ8 R s) = weightJ8P (Fintype.card K) (Fintype.card (Quad δ)) r P s := by
  cases s
  · rw [sumJ8, epsilonOf_map_liftJ8, R.eps40]; rfl
  · erw [sumJ8, ioSummandJ8, eps_specSummand, specV_dep_card]; rfl
  · erw [sumJ8, ioSummandJ8, eps_specSummand, specV_dep_card]; rfl
  · erw [sumJ8, ioSummandJ8, eps_specSummand, specH_dep_card]; rfl
  · erw [sumJ8, ioSummandJ8, eps_specSummand, specH_dep_card]; rfl
  · erw [sumJ8, ioSummandJ8, eps_specSummand, specH_dep_card]; rfl
  · rw [sumJ8, eps_three]
    have h1 : (atomDyckJ8 δ St R.rowsA r.A R.rowsA_le fun Q hQ χ χ' => (R.rowsA_const Q hQ χ χ').1).coins.card = 2 :=
      Finset.card_pair (by decide)
    have h2 : (atomCensusJ8 δ St R.rowsA R.skelA r.A r.Λ R.rowsA_le R.skelA_le R.rowsA_const).coins.card = 2 :=
      Finset.card_pair (by decide)
    have h3 : (zeroYJ8 δ St (Tr := Tr)).coins.card = 2 := Finset.card_pair (by decide)
    have w1 : (atomDyckJ8 δ St R.rowsA r.A R.rowsA_le fun Q hQ χ χ' => (R.rowsA_const Q hQ χ χ').1).weight =
        r.A * (2 * fuelChip - 1) := rfl
    have w2 : (atomCensusJ8 δ St R.rowsA R.skelA r.A r.Λ R.rowsA_le R.skelA_le R.rowsA_const).weight =
        pairCount (r.A + 3) * (2 * r.Λ - 1) := rfl
    have w3 : (zeroYJ8 δ St (Tr := Tr)).weight = 1 := rfl
    rw [h1, h2, h3, w1, w2, w3]
    simp only [weightJ8P, Nat.cast_one]
    ring
  · erw [sumJ8, atomWalkJ8, eps_specSummand, specW_dep_card]; rfl
  · erw [sumJ8, bivJ8, eps_specSummand, specZY_dep_card]; rfl

/-- The order of the summands. -/
def orderJ8 : List SummandM :=
  [.fortieth, .cellValidity2, .atomValidity, .atomExport, .cellExport3, .service, .atomCensus,
    .atomWalk, .bivariateCensus]

/-- **The J-8 summand list.** -/
def allJ8 (R : DataJ8 (q := q) δ Tr St r P) : List (BadSummand frameJ8 K Tr St) := orderJ8.flatMap (sumJ8 R)

theorem epsilonOf_append (l l' : List (BadSummand frameJ8 K Tr St)) :
    epsilonOf (l ++ l') = epsilonOf l + epsilonOf l' := by
  simp [epsilonOf, List.map_append, List.sum_append]

theorem epsilonOf_flatMap (o : List SummandM) (f : SummandM → List (BadSummand frameJ8 K Tr St)) :
    epsilonOf (o.flatMap f) = (o.map fun s => epsilonOf (f s)).sum := by
  induction o with
  | nil => simp [epsilonOf]
  | cons a o ih => rw [List.flatMap_cons, epsilonOf_append, ih, List.map_cons, List.sum_cons]

theorem sum_univ_SummandM (g : SummandM → ℚ) : ∑ s : SummandM, g s = (orderJ8.map g).sum := by
  rw [show (Finset.univ : Finset SummandM) = orderJ8.toFinset from by decide,
    List.sum_toFinset _ (by decide)]

/-- **`ε` of the J-8 list is `boundJ8P`** (every weight proved). -/
theorem epsilon_allJ8 (R : DataJ8 (q := q) δ Tr St r P) :
    epsilonOf (allJ8 R) = boundJ8P (Fintype.card K) (Fintype.card (Quad δ)) r P := by
  rw [allJ8, epsilonOf_flatMap, boundJ8P, sum_univ_SummandM]
  congr 1
  exact List.map_congr_left fun s _ => epsilon_sumJ8 R s

end Data

/-! ## 10. Figures at `|𝕂| = p³` -/

/-- The numerator over `|𝕂|⁴` at `|𝕂′| = |𝕂|²`. -/
def numJ8 (c : ℕ) (r : RowsJ8) (P : ℕ) : ℕ :=
  numHQ c r.N r.D r.W r.Λ +
  (ioFailureUnionBound 5 (3 + 2 * r.D) (r.D + r.mb) (c ^ 2) + ioFailureUnionBound 5 (3 + 2 * r.A) r.A (c ^ 2) +
    ioFailureUnionBound 5 (r.A + r.inc + r.AW) r.A (c ^ 2) +
    ioFailureUnionBound 5 (3 * r.N + r.W + r.rd) r.D (c ^ 2) +
    ioFailureUnionBound 8 (r.N + 2 * r.J) (r.calls + r.heads + r.blocks + r.J) (c ^ 2)) +
  c ^ 2 * (r.A * (2 * fuelChip - 1) + pairCount (r.A + 3) * (2 * r.Λ - 1) + 1) +
  c ^ 3 * (15 * r.AW) +
  P * (c ^ 2 * (r.leaves - 1) + c ^ 2 * (r.maxlen - 1))

theorem boundJ8P_eq (c : ℕ) (r : RowsJ8) (P : ℕ) (hc : 0 < c) :
    boundJ8P c (c ^ 2) r P = (numJ8 c r P : ℚ) / (c : ℚ) ^ 4 := by
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [boundJ8P, sum_univ_SummandM]
  simp only [orderJ8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weightJ8P]
  rw [boundVCLHQ''_eq c r.N r.D r.W r.Λ hc]
  unfold numJ8
  push_cast
  field_simp
  ring

/-- Row counts bounded by a corner. -/
def RowsLe (r r₀ : RowsJ8) : Prop :=
  r.N ≤ r₀.N ∧ r.D ≤ r₀.D ∧ r.W ≤ r₀.W ∧ r.Λ = r₀.Λ ∧ r.A ≤ r₀.A ∧ r.AW ≤ r₀.AW ∧ r.J ≤ r₀.J ∧
    r.mb ≤ r₀.mb ∧ r.inc ≤ r₀.inc ∧ r.calls ≤ r₀.calls ∧ r.heads ≤ r₀.heads ∧ r.blocks ≤ r₀.blocks ∧
    r.rd ≤ r₀.rd ∧ r.leaves ≤ r₀.leaves ∧ r.maxlen ≤ r₀.maxlen

theorem numJ8_corner {c : ℕ} {r r₀ : RowsJ8} {P P₀ : ℕ} (h : RowsLe r r₀) (hP : P ≤ P₀) :
    numJ8 c r P ≤ numJ8 c r₀ P₀ := by
  obtain ⟨hN, hD, hW, hΛ, hA, hAW, hJ, hmb, hinc, hcalls, hheads, hblocks, hrd, hlv, hml⟩ := h
  have e0 := numHQ_corner (c := c) r.Λ hN hD hW
  rw [hΛ] at e0
  have i1 := ioFUB_mono 5 (c ^ 2) (a := 3 + 2 * r.D) (a' := 3 + 2 * r₀.D) (b := r.D + r.mb) (b' := r₀.D + r₀.mb)
    (by omega) (by omega)
  have i2 := ioFUB_mono 5 (c ^ 2) (a := 3 + 2 * r.A) (a' := 3 + 2 * r₀.A) (b := r.A) (b' := r₀.A) (by omega) hA
  have i3 := ioFUB_mono 5 (c ^ 2) (a := r.A + r.inc + r.AW) (a' := r₀.A + r₀.inc + r₀.AW) (b := r.A) (b' := r₀.A)
    (by omega) hA
  have i4 := ioFUB_mono 5 (c ^ 2) (a := 3 * r.N + r.W + r.rd) (a' := 3 * r₀.N + r₀.W + r₀.rd) (b := r.D)
    (b' := r₀.D) (by omega) hD
  have i5 := ioFUB_mono 8 (c ^ 2) (a := r.N + 2 * r.J) (a' := r₀.N + 2 * r₀.J)
    (b := r.calls + r.heads + r.blocks + r.J) (b' := r₀.calls + r₀.heads + r₀.blocks + r₀.J) (by omega) (by omega)
  have hp : pairCount (r.A + 3) ≤ pairCount (r₀.A + 3) := pairCount_mono (by omega)
  have hl : r.leaves - 1 ≤ r₀.leaves - 1 := Nat.sub_le_sub_right hlv 1
  have hm : r.maxlen - 1 ≤ r₀.maxlen - 1 := Nat.sub_le_sub_right hml 1
  unfold numJ8
  rw [hΛ]
  gcongr

theorem boundJ8P_lt_of_num {r : RowsJ8} {P b : ℕ} (h : numJ8 cK r P * 2 ^ b < cK ^ 4) :
    boundJ8P cK (cK ^ 2) r P < 1 / (2 : ℚ) ^ b := by
  rw [boundJ8P_eq _ _ _ cK_pos]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ hc (by positivity), one_mul]
  exact_mod_cast h

theorem not_boundJ8P_le_of_num {r : RowsJ8} {P b : ℕ} (h : cK ^ 4 < numJ8 cK r P * 2 ^ b) :
    ¬ boundJ8P cK (cK ^ 2) r P ≤ 1 / (2 : ℚ) ^ b := by
  rw [boundJ8P_eq _ _ _ cK_pos, not_le]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ (by positivity) hc, one_mul]
  exact_mod_cast h

/-- **The `2^31` corner**: every row count `2^31`, `Λ = leaves = fuelChip`, `maxlen = P = 2^31`. -/
def corner31 : RowsJ8 where
  N := 2 ^ 31
  D := 2 ^ 31
  W := 2 ^ 31
  Λ := fuelChip
  A := 2 ^ 31
  AW := 2 ^ 31
  J := 2 ^ 31
  mb := 2 ^ 31
  inc := 2 ^ 31
  calls := 2 ^ 31
  heads := 2 ^ 31
  blocks := 2 ^ 31
  rd := 2 ^ 31
  leaves := fuelChip
  maxlen := 2 ^ 31

theorem numJ8_31 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numJ8 c corner31 (2 ^ 31) * 2 ^ 155 < c ^ 4 := by
  subst hc; unfold numJ8 numHQ corner31 fuelChip pairCount ioFailureUnionBound; decide +kernel

theorem numJ8_31_not (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numJ8 c corner31 (2 ^ 31) * 2 ^ 156 := by
  subst hc; unfold numJ8 numHQ corner31 fuelChip pairCount ioFailureUnionBound; decide +kernel

/-- **`epsJ8 < 2^-155`** at every row count `≤ 2^31` (compute, cell, walk, atom, atom-walk, J, and
each auxiliary count), `Λ = fuelChip`, `leaves ≤ fuelChip`, `maxlen ≤ 2^31`, `≤ 2^31` census pairs. -/
theorem figJ8_155 (r : RowsJ8) (P : ℕ) (h : RowsLe r corner31) (hP : P ≤ 2 ^ 31) :
    boundJ8P cK (cK ^ 2) r P < 1 / (2 : ℚ) ^ 155 :=
  boundJ8P_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numJ8_corner h hP)) (numJ8_31 cK cK_eq))

/-- **Tight**: at the corner, not `≤ 2^-156`. -/
theorem figJ8_not_156 : ¬ boundJ8P cK (cK ^ 2) corner31 (2 ^ 31) ≤ 1 / (2 : ℚ) ^ 156 :=
  not_boundJ8P_le_of_num (numJ8_31_not cK cK_eq)

/-- **The figure for the J-8 list itself**: at Goldilocks (`|𝕂| = p³`, `|𝕂′| = |𝕂|²`), `ε < 2^-155`. -/
theorem epsJ8_lt_155 {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime]
    [Algebra (ZMod q) K] {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
    {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P : ℕ} (R : DataJ8 (q := q) δ Tr St r P)
    (hcK : Fintype.card K = cK) (h : RowsLe r corner31) (hP : P ≤ 2 ^ 31) :
    epsilonOf (allJ8 R) < 1 / (2 : ℚ) ^ 155 := by
  rw [epsilon_allJ8, quad_card, hcK]
  exact figJ8_155 r P h hP

end

end Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
