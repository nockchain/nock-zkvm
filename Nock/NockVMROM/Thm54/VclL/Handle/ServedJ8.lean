/-
  Nock/NockVMROM/Thm54/VclL/Handle/ServedJ8.lean

The three handle-class balances of `computeChipVCLHX` (`x` cell export, `p` walk path, `s` SERVICE),
  each at its own compression width `mOf bl` (`DenXJ8`), are stated against ABSTRACT memory sides:
  * `provs bl : List ((Fin (mOf bl) → K) × K)` — the providers' keys with multiplicities (cell export
    `keyH` / `mh`; walk-path records; J `TAG_jet` calls, atom-table inc chain heads `mi`, atom-walk
    blocks, zero-padded to `8`);
  * `ext bl : List (Fin (mOf bl) → K)` — the OTHER consumers of the same balance (walk instance 1 and
    J `rd` reads on `x`; none on `p` / `s`).

  * **`GoodCJ8`** (the verifier's check on the publics): `ρ_bl + T_ext bl = T_prov bl` for every
    balance, at terminal values the memory chips publish; `balJ8_of_good` turns it, with the memory
    telescopes (`Σ ext = T_ext`, `Σ provs = T_prov`), into the balance identity `BalJ8`.

  * `slotsX_tags` / `consQX_tags` / `reVal_lt`: the consumed records' entries are `< p` (`4 < p`).
  * `den_prov_ne_of_out`: outside the weighted IO event every PROVIDER denominator is nonzero.
  * **`served_of_balancesJ8`**: on an accepted `computeChipVCLHX` trace (`BCtx`), under `BalJ8`, outside
    each balance's IO failure event at the compute coins `(γH′, ρH′)`, with consumer counts `< p` and
    `ProvOK`, EVERY record a row consumes satisfies `RecOK` — i.e. `RowsAccX.served`.  No `hden`: the
    pair denominators are nonzero outside the IO event (`DenXJ8.hden_of_reqs`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ServeH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (rEF envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (activeX reVal RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX)

noncomputable section

/-! ## 1. The consumed records' tag constants are `≤ 4` -/

theorem slotsX_tags : ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)),
    (∀ x ∈ S.ents, ∀ c, RE.k c ∈ x.rcd → c ≤ 4) ∧
      ∀ fl a c bl, S.pair = some (fl, a, c, bl) → ∀ t, RE.k t ∈ a ++ c → t ≤ 4 := by
  intro S hS
  simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl <;> refine ⟨?_, fun fl a c bl h => ?_⟩
  all_goals first
    | (simp [slot0X, slot1X, slot2X, slot3X, cellRecX, walkRecX, recOf, ChipH.cellRec, ChipH.walkRec, incRecX,
        jetRecX, walkRecAX]; done)
    | (simp only [slot0X, slot1X, slot2X, slot3X, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
       try (obtain ⟨-, rfl, rfl, rfl⟩ := h; simp [walkRecX, recOf, ChipH.walkRec, walkRecAX]))

theorem consQX_tags {F : Type} [Field F] [DecidableEq F] (eF : Env F) (bl : Bal) :
    ∀ r ∈ consQX eF bl, ∀ t, RE.k t ∈ r → t ≤ 4 := by
  intro r hr t ht
  obtain ⟨S, hS, hr0⟩ := List.mem_flatMap.mp hr
  obtain ⟨hents, hpair⟩ := slotsX_tags S hS
  rcases List.mem_append.mp hr0 with hr1 | hr2
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr1
    exact hents x (List.mem_filter.mp (List.mem_filter.mp hx).1).1 t ht
  · unfold pairRecsB at hr2
    cases hp : S.pair with
    | none => rw [hp] at hr2; simp at hr2
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      rw [hp] at hr2
      simp only at hr2
      have := hpair fl a c b' hp t
      by_cases hc : b' = bl ∧ eF.trace fl = 1
      · rw [if_pos hc] at hr2
        rcases List.mem_pair.mp hr2 with rfl | rfl
        · exact this (List.mem_append_left _ ht)
        · exact this (List.mem_append_right _ ht)
      · rw [if_neg hc] at hr2; simp at hr2

section ZModFacts
variable {p : ℕ} [Fact p.Prime]

theorem reVal_lt (hp4 : 4 < p) (env : Env (ZMod p)) (bl : Bal) :
    ∀ r ∈ consQX env bl, ∀ e ∈ r.map (reVal env), e < p := by
  intro r hr e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  cases x with
  | col i => exact ZMod.val_lt _
  | k c => exact lt_of_le_of_lt (consQX_tags env bl r hr c hx) hp4

end ZModFacts

/-! ## 2. Provider denominators outside the IO event -/

theorem den_prov_ne_of_out {K : Type} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}
    (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K)) (γ ρ : K)
    (hout : (γ, ρ) ∉ IOFailureEventW reqs provs) :
    ∀ q ∈ provs, compress ⟨γ, ρ⟩ q.1 ≠ 0 := by
  intro q hq h0
  apply hout
  rw [mem_IOFailureEventW_iff]
  right; left
  simp only [IOPoleHitEvent, recordsW]
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  exact ⟨q.1, List.mem_append_right _ (List.mem_map_of_mem hq), h0⟩

/-! ## 3. The balance checks and the served records -/

section Served
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}
open Compute.LogUp (limbVal)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "EN" => envsN hn nodes chalV pubVal orbit P
local notation "CV" => coinsCV b δ chalV

/-- The providers' keys and weights, lifted to `𝕂′`. -/
def liftP {m : ℕ} (l : List ((Fin m → K) × K)) : List ((Fin m → 𝕂′) × 𝕂′) :=
  l.map fun q => (liftRec (L := 𝕂′) q.1, algebraMap K 𝕂′ q.2)

/-- The compute balance publics `(Re ρ_bl, Im ρ_bl)`. -/
def rhoX (bl : Bal) : 𝕂′ :=
  Quad.mk (algebraMap (ZMod p) K δ) (limbVal b pubVal (balCols bl).2.1) (limbVal b pubVal (balCols bl).2.2.2)

/-- **`GoodCJ8`, the verifier's three handle-class balance checks** on the published terminals: for
each balance, the compute terminal plus the other consumers' terminals equals the providers'. -/
def GoodCJ8 (Tprov Text : Bal → 𝕂′) : Prop :=
  ∀ bl, rhoX (b := b) (δ := δ) (pubVal := pubVal) bl + Text bl = Tprov bl

/-- **The balance identity** (after the memory telescopes). -/
def BalJ8 (provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)) (ext : (bl : Bal) → List (Fin (mOf bl) → K)) :
    Prop :=
  ∀ bl, rhoX (b := b) (δ := δ) (pubVal := pubVal) bl +
      ((ext bl).map fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹).sum =
    ((provs bl).map fun q => algebraMap K 𝕂′ q.2 * (compress CV (liftRec (L := 𝕂′) q.1))⁻¹).sum

theorem balJ8_of_good {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)}
    {ext : (bl : Bal) → List (Fin (mOf bl) → K)} {Tprov Text : Bal → 𝕂′}
    (hG : GoodCJ8 (b := b) (δ := δ) (pubVal := pubVal) Tprov Text)
    (hext : ∀ bl, ((ext bl).map fun r => (compress CV (liftRec (L := 𝕂′) r))⁻¹).sum = Text bl)
    (hprov : ∀ bl, ((provs bl).map fun q => algebraMap K 𝕂′ q.2 * (compress CV (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Tprov bl) :
    BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext := by
  intro bl; rw [hext, hprov]; exact hG bl

/-- **A provider-side obligation** `Φ`: every small `ℕ` record whose key is provided into `bl`
satisfies `Φ`. -/
def ProvP (Φ : List ℕ × Bal → Prop) (bl : Bal) (provs : List ((Fin (mOf bl) → K) × K)) : Prop :=
  ∀ q ∈ provs, ∀ l : List ℕ, l.length ≤ mOf bl → (∀ e ∈ l, e < p) →
    natKey (p := p) (K := K) (mOf bl) l = q.1 → Φ (l, bl)

/-- **The memory side's genuineness obligation**: `ProvP` at `RecOK`. -/
abbrev ProvOK (D : HX → Option Noun) (R : Nock.Jet.Registry) (limbA : ℕ → ℕ → HX) (bl : Bal)
    (provs : List ((Fin (mOf bl) → K) × K)) : Prop :=
  ProvP (p := p) (K := K) (RecOK D R limbA) bl provs

/-- **The walk chip's axis obligation** on path records `(root, axis, k, v)`: the axis is in
`[2, 2^62)` (`WalkJ8.walkJ8_axis_lt` for a provided walk record). -/
def AxOK : List ℕ × Bal → Prop
  | ([_, ax, _, _], .p) => 2 ≤ ax ∧ ax < 2 ^ 62
  | _ => True

/-- The request list of a balance: the compute's and the other consumers', lifted. -/
def reqsJ8 (ext : (bl : Bal) → List (Fin (mOf bl) → K)) (bl : Bal) : List (Fin (mOf bl) → 𝕂′) :=
  (compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal) (orbit := orbit)
    (P := P) bl ++ ext bl).map (liftRec (L := 𝕂′))

/-- **Every consumed record satisfies the providers' obligation `Φ`.**  On an accepted `computeChipVCLHX` trace, under
the balance identity, outside each balance's weighted IO failure event at the compute coins, with
consumer counts `< p` and the providers' genuineness obligation, every record any row consumes is
genuine. -/
theorem servedP_of_balancesJ8 [CharP 𝕂′ p] (C : BCtx hn nodes b δ chalV pubVal orbit P) (hp4 : 4 < p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    {Φ : List ℕ × Bal → Prop}
    (hprov : ∀ bl, ProvP (p := p) (K := K) Φ bl (provs bl)) :
    ∀ r < n, ∀ x ∈ activeX (EN r), Φ x := by
  have hd : ∀ bl, ∀ r ∈ reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, compress ⟨(CV).gamma, (CV).pole⟩ r ≠ 0 :=
    fun bl => TeleC.den_ne_of_out _ _ _ _ (hout bl)
  have hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
      (orbit := orbit) (P := P) bl, compress CV (liftRec (L := 𝕂′) r) ≠ 0 :=
    fun bl r hr => hd bl _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hserved : ∀ bl, ∀ r ∈ reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, r ∈ (liftP (provs bl)).map Prod.fst := by
    intro bl
    refine ServeH.served_of_balance (p := p) _ _ _ _ (hd bl)
      (den_prov_ne_of_out _ _ _ _ (hout bl)) ?_ (hcount bl) (hout bl)
    have h1 := compReqsX_sum C hne bl
    have h2 := hbal bl
    unfold reqsJ8 liftP
    rw [List.map_map, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1]
    exact h2
  intro i hi x hx
  obtain ⟨l, bl⟩ := x
  have hmem : l ∈ ((activeX (EN i)).filter fun r => decide (r.2 = bl)).map (·.1) :=
    List.mem_map.mpr ⟨(l, bl), List.mem_filter.mpr ⟨hx, by simp⟩, rfl⟩
  rw [consQX_activeX] at hmem
  obtain ⟨rec, hrec, rfl⟩ := List.mem_map.mp hmem
  have hk : keyX (K := K) (mOf bl) rec (EN i) ∈
      compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
        (orbit := orbit) (P := P) bl :=
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map_of_mem hrec⟩
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp
    (hserved bl _ (List.mem_map_of_mem (List.mem_append_left _ hk)))
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  have hkey : q0.1 = keyX (K := K) (mOf bl) rec (EN i) := liftRec_inj hqe
  refine hprov bl q0 hq0 _ ?_ (reVal_lt hp4 _ bl rec hrec) ?_
  · rw [List.length_map]; exact consQX_len _ bl rec hrec
  · rw [hkey, keyX_natKey]

/-- **`RowsAccX.served` from the memory providers.**  On an accepted `computeChipVCLHX` trace, under
the balance identity, outside each balance's weighted IO failure event at the compute coins, with
consumer counts `< p` and the providers' genuineness obligation, every record any row consumes is
genuine. -/
theorem served_of_balancesJ8 [CharP 𝕂′ p] (C : BCtx hn nodes b δ chalV pubVal orbit P) (hp4 : 4 < p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    {D : HX → Option Noun} {R : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}
    (hprov : ∀ bl, ProvOK (p := p) (K := K) D R limbA bl (provs bl)) :
    ∀ r < n, ∀ x ∈ activeX (EN r), RecOK D R limbA x :=
  servedP_of_balancesJ8 C hp4 hbal hout hcount hprov

/-- **`RowsAccX.ax` from the path balance**: on an `s10L` row (base gates, one-hot at `12`) whose
consumed records satisfy `AxOK`, the sibling-read axis `val xM.v` is in `[2, 2^62)` — the row consumes
the path record `walkRec xSf1 xM.v xFtth` under `pr = 1` (`ChipHX.s10L_row`). -/
theorem ax_of_axOK {env : Env (ZMod p)} (hB : BaseHoldsX env) (hOH : OneHotAt env 12)
    (hA : ∀ x ∈ activeX env, AxOK x) :
    2 ≤ (env.trace xM.v).val ∧ (env.trace xM.v).val < 2 ^ 62 := by
  obtain ⟨-, -, -, -, hpr, -⟩ := s10L_row hB (RowSemChipX.oh_one hOH (by decide))
    (RowSemChipX.oh_zero hOH (by decide) (by decide)) (RowSemChipX.oh_zero hOH (by decide) (by decide))
  have hpm := RowSemChipX.pair_mem (env := env) (S := slot2X) (fl := prX) (a := walkRecX xSf1 xM.v xFtth)
    (b := walkRecX xSf2 xM.v xFttt) (bl := .p) (by simp [ChipHX.slotsX]) rfl hpr
  have := hA _ hpm.1
  simpa [AxOK, walkRecX, recOf, ChipH.walkRec, reVal] using this

end Served

end

end Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
