/-
  Nock/NockVMROM/Thm54/VclL/Handle/DenXJ8.lean

  New module, additive.

  * `keyX m r eF : Fin m → K` — a record `r : List RE` read on a row (columns and tag constants),
    lifted to `𝕂` and padded by `0` to length `m`.
  * Validity / export stay at `m = 5`.
  * `consQX_len`: every record a row consumes into `x` / `p` has length `≤ 5`, into `s` length `≤ 8`
    (`mOf`).
  * `keyX_natKey` (at `ZMod p`): `keyX m r env = natKey m (r.map (reVal env))` — the compressed key is
    the cast of the `ℕ` record `RecOK` is stated about (`RowSemChipX.activeX`).
  * **`compute_balanceX_keys`**: `compute_balanceX` in `compress` form, at the coins read off the
    challenge vector (`TeleCQ.coinsCV`), every balance at its own `m = mOf bl`.
  * `compReqsX bl` (the compute request list), **`hden_of_reqs`** (`compute_balanceX`'s named `hden`
    discharged by nonzero request denominators, which each balance's IO event excludes:
    `TeleC.den_ne_of_out`), **`compReqsX_sum`** (the compute side in list form, `hden`-free).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS prodL mapC chalGammaL chalRhoL pubRhoX pubRhoP)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (sumQ qγH qρH chalGammaIm chalRhoIm pubRhoXIm pubRhoPIm)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (rEF envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCQ coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)

noncomputable section

/-! ## 1. Keys -/

section Key
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- A record entry read on a row, lifted to `𝕂` (beyond the record: the constant `0`). -/
def keyXN (r : List RE) (eF : Env F) (c : ℕ) : K := algebraMap F K ((r.getD c (.k 0)).ev eF.trace)

/-- **A record's key**: its entries read on the row, lifted to `𝕂`, zero-padded to length `m`. -/
def keyX (m : ℕ) (r : List RE) (eF : Env F) : Fin m → K := fun c => keyXN r eF c

/-- Zero padding of a key `Fin m → K` to `Fin m' → K`. -/
def padK {m m' : ℕ} (v : Fin m → K) : Fin m' → K := fun c => if h : (c : ℕ) < m then v ⟨c, h⟩ else 0

theorem keyXN_ge (r : List RE) (eF : Env F) {c : ℕ} (hc : r.length ≤ c) : (keyXN r eF c : K) = 0 := by
  rw [keyXN, List.getD_eq_default _ _ hc]; simp [RE.ev]

/-- A key read at a larger width is the zero padding of the narrower one. -/
theorem keyX_pad {m m' : ℕ} (r : List RE) (eF : Env F) (hr : r.length ≤ m) :
    (keyX m' r eF : Fin m' → K) = padK (keyX m r eF) := by
  funext c
  unfold padK keyX
  split_ifs with h
  · rfl
  · exact keyXN_ge r eF (by omega)

theorem liftRec_padK {L : Type} [Field L] [Algebra K L] {m m' : ℕ} (v : Fin m → K) :
    liftRec (L := L) (padK (m' := m') v) = padK (liftRec (L := L) v) := by
  funext c
  unfold liftRec padK
  split_ifs <;> simp

/-- **Zero padding does not move `compress`.** -/
theorem compress_padK {L : Type} [Field L] (coins : IOCoins L) {m m' : ℕ} (hm : m ≤ m') (v : Fin m → L) :
    compress coins (padK (m' := m') v) = compress coins v := by
  unfold compress Walk.rlc
  congr 1
  let g : ℕ → L := fun c => coins.gamma ^ c * (if h : c < m then v ⟨c, h⟩ else 0)
  have h1 : (∑ c : Fin m', coins.gamma ^ (c : ℕ) * padK (m' := m') v c) = ∑ c ∈ Finset.range m', g c := by
    rw [← Fin.sum_univ_eq_sum_range g m']; rfl
  have h2 : (∑ c : Fin m, coins.gamma ^ (c : ℕ) * v c) = ∑ c ∈ Finset.range m, g c := by
    rw [← Fin.sum_univ_eq_sum_range g m]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [g, c.isLt]
  rw [h1, h2, ← Finset.sum_subset (Finset.range_subset_range.mpr hm)]
  intro c _ hc
  rw [Finset.mem_range] at hc
  simp [g, hc]

end Key

/-! ## 2. `DX` is `compress` of the lifted key -/

section Val
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (eK : Env K) (eF : Env F)

local notation "𝕂′" => Quad (algebraMap F K δ)

theorem RE_q_val (x : RE) :
    Q.val δ (x.q F) eK eF = algebraMap K 𝕂′ (algebraMap F K (x.ev eF.trace)) := by
  cases x with
  | col i =>
    rw [RE.q, ComputeSatHQ.qlift_val']
    simp [cc, CoeffExpr.eval, RE.ev]
  | k c =>
    rw [RE.q, qconst_val]
    simp [RE.ev]

theorem rlcKeyQX_val' : ∀ (r : List RE) (m : ℕ), Q.val δ (rlcKeyQX F δ m r) eK eF =
    ∑ c ∈ Finset.range r.length, (coinsCQ δ eK).gamma ^ (m + c) *
      algebraMap K 𝕂′ (algebraMap F K ((r.getD c (.k 0)).ev eF.trace))
  | [], m => by simp [rlcKeyQX, qconst_val]
  | x :: r, m => by
    rw [rlcKeyQX, qadd_val, qmul_val, qpow_val, rlcKeyQX_val' r (m + 1), RE_q_val, List.length_cons,
      Finset.sum_range_succ']
    have hg : Q.val δ (qγH F) eK eF = (coinsCQ δ eK).gamma := by
      rw [qγH, qvar_val]; rfl
    rw [hg]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show m + 1 + c = m + (c + 1) by omega]

/-- **The closed form of `DX`**: a compute record's `𝕂′` denominator is `compress` of its lifted key at
the compute's `𝕂′` coins `(γH′, ρH′)`, at every width `m ≥ r.length`. -/
theorem denQX_val (r : List RE) (m : ℕ) (hr : r.length ≤ m) :
    DX δ eK eF r = compress (coinsCQ δ eK) (liftRec (L := 𝕂′) (keyX (K := K) m r eF)) := by
  rw [DX, denQX, qadd_val, rlcKeyQX_val' δ eK eF r 0]
  have hr' : Q.val δ (qρH F) eK eF = (coinsCQ δ eK).pole := by
    rw [qρH, qvar_val]; rfl
  rw [hr']
  simp only [compress, Walk.rlc, zero_add]
  congr 1
  let g : ℕ → 𝕂′ := fun c => (coinsCQ δ eK).gamma ^ c * algebraMap K 𝕂′ (keyXN r eF c)
  have hR : (∑ c : Fin m, (coinsCQ δ eK).gamma ^ (c : ℕ) * liftRec (L := 𝕂′) (keyX (K := K) m r eF) c) =
      ∑ c ∈ Finset.range m, g c := by
    rw [← Fin.sum_univ_eq_sum_range g m]; rfl
  rw [hR, ← Finset.sum_subset (Finset.range_subset_range.mpr hr)]
  · rfl
  · intro c _ hc
    rw [Finset.mem_range] at hc
    simp [g, keyXN_ge r eF (not_lt.mp hc)]

end Val

/-! ## 3. Record lengths per balance -/

/-- The compression width of a balance: the SERVICE balance at `8` (`jetRecX`), the rest at `5`. -/
def mOf : Bal → ℕ
  | .s => 8
  | _ => 5

theorem slotsX_len : ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)),
    (∀ x ∈ S.ents, x.rcd.length ≤ mOf x.bal) ∧
      ∀ fl a c bl, S.pair = some (fl, a, c, bl) → a.length ≤ mOf bl ∧ c.length ≤ mOf bl := by
  intro S hS
  simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl <;> refine ⟨?_, fun fl a c bl h => ?_⟩
  all_goals first
    | (simp [slot0X, slot1X, slot2X, slot3X, cellRecX, walkRecX, recOf, ChipH.cellRec, ChipH.walkRec, incRecX,
        jetRecX, walkRecAX, mOf]; done)
    | (simp only [slot0X, slot1X, slot2X, slot3X, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
       try (obtain ⟨-, rfl, rfl, rfl⟩ := h; simp [walkRecX, recOf, ChipH.walkRec, walkRecAX, mOf]))

/-- **Every record a row consumes into `bl` has length `≤ mOf bl`.** -/
theorem consQX_len {F : Type} [Field F] [DecidableEq F] (eF : Env F) (bl : Bal) :
    ∀ r ∈ consQX eF bl, r.length ≤ mOf bl := by
  intro r hr
  obtain ⟨S, hS, hr0⟩ := List.mem_flatMap.mp hr
  obtain ⟨hents, hpair⟩ := slotsX_len S hS
  rcases List.mem_append.mp hr0 with hr1 | hr2
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr1
    have hx1 := (List.mem_filter.mp hx).1
    have hb := of_decide_eq_true (List.mem_filter.mp hx1).2
    rw [← hb]
    exact hents x (List.mem_filter.mp hx1).1
  · unfold pairRecsB at hr2
    cases hp : S.pair with
    | none => rw [hp] at hr2; simp at hr2
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      rw [hp] at hr2
      simp only at hr2
      have := hpair fl a c b' hp
      by_cases hc : b' = bl ∧ eF.trace fl = 1
      · rw [if_pos hc] at hr2
        obtain ⟨rfl, -⟩ := hc
        rcases List.mem_pair.mp hr2 with rfl | rfl
        · exact this.1
        · exact this.2
      · rw [if_neg hc] at hr2; simp at hr2

/-! ## 4. At `ZMod p`: the key is the cast of the `ℕ` record -/

section ZModKey
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (reVal)

theorem RE_ev_reVal (env : Env (ZMod p)) (x : RE) : x.ev env.trace = ((reVal env x : ℕ) : ZMod p) := by
  cases x <;> simp [RE.ev, reVal, ZMod.natCast_zmod_val]

/-- The key of an `ℕ` record: its entries cast to `ZMod p`, lifted to `𝕂`, zero-padded. -/
def natKey (m : ℕ) (l : List ℕ) : Fin m → K := fun c => algebraMap (ZMod p) K ((l.getD c 0 : ℕ) : ZMod p)

/-- **The compressed key of a consumed record is the key of the `ℕ` record `RecOK` reads.** -/
theorem keyX_natKey (env : Env (ZMod p)) (r : List RE) (m : ℕ) :
    (keyX m r env : Fin m → K) = natKey (p := p) m (r.map (reVal env)) := by
  funext c
  simp only [keyX, keyXN, natKey]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : r[(c : ℕ)]? with
  | none => simp [RE.ev, reVal]
  | some x =>
    cases x <;> simp only [Option.map_some, Option.getD_some, RE.ev, reVal, ZMod.natCast_zmod_val]

end ZModKey

/-! ## 5. The compute balances in `compress` form -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → F} {b : Basis (Fin 3) F K} {δ : F}
  [Fact (¬ IsSquare (algebraMap F K δ))]
  {chalV pubVal : ℕ → F} {orbit : StrictOrbitDomain F 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X]}
open Compute.LogUp (limbVal)

local notation "𝕂′" => Quad (algebraMap F K δ)
local notation "EN" => envsN hn nodes chalV pubVal orbit P

theorem chalN (r : ℕ) : (EN r).chal = chalV := by
  unfold envsN; split_ifs <;> rfl

/-- The coins every row reads are the coins of the challenge vector. -/
theorem coinsCQ_EN (r : ℕ) : coinsCQ δ (gatherEnv b (EN r)) = coinsCV b δ chalV := by
  unfold coinsCQ coinsCV
  simp only [Compute.TowerD.gatherEnv, chalN]

/-- **`compute_balanceX` in `compress` form**: on an accepted `computeChipVCLHX` trace, for each
balance `bl`, `Σ_rows Σ_{r ∈ consQX bl} compress(γH′, ρH′)(lift (keyX (mOf bl) r))⁻¹ = (Re ρ_bl, Im ρ_bl)`. -/
theorem compute_balanceX_keys (C : BCtx hn nodes b δ chalV pubVal orbit P)
    (hden : ∀ r < n, ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), pairFX (EN r) S = 1 →
      pairDaX δ (gatherEnv b (EN r)) (EN r) S ≠ 0 ∧ pairDbX δ (gatherEnv b (EN r)) (EN r) S ≠ 0)
    (bl : Bal) :
    ∑ i ∈ Finset.range n, ((consQX (EN i) bl).map fun r =>
        (compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) (keyX (K := K) (mOf bl) r (EN i))))⁻¹).sum =
      Quad.mk (algebraMap F K δ) (limbVal b pubVal (balCols bl).2.1) (limbVal b pubVal (balCols bl).2.2.2) := by
  rw [← compute_balanceX C hden bl]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine List.map_congr_left fun r hr => ?_
  rw [denQX_val δ _ _ r (mOf bl) (consQX_len _ bl r hr), coinsCQ_EN]

theorem sum_flatMap_range {M : Type} [AddCommMonoid M] (f : ℕ → List M) :
    ∀ n, ((List.range n).flatMap f).sum = ∑ i ∈ Finset.range n, (f i).sum
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.sum_append, sum_flatMap_range f n, Finset.sum_range_succ]
    simp

/-- **The compute request list of balance `bl`**: the keys of the records every row consumes into `bl`
(rows `0..n-1` in order), at width `mOf bl`. -/
def compReqsX (bl : Bal) : List (Fin (mOf bl) → K) :=
  (List.range n).flatMap fun i => (consQX (EN i) bl).map fun r => keyX (mOf bl) r (EN i)

theorem pair_mem_consQX (eF : Env F) {S : SlotX ℚ} (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ)))
    {fl : ℕ} {a c : List RE} {bl : Bal} (hp : S.pair = some (fl, a, c, bl)) (hf : eF.trace fl = 1) :
    a ∈ consQX eF bl ∧ c ∈ consQX eF bl := by
  have hpr : pairRecsB eF bl S = [a, c] := by
    unfold pairRecsB; rw [hp]; simp [hf]
  refine ⟨List.mem_flatMap.mpr ⟨S, hS, List.mem_append_right _ ?_⟩,
    List.mem_flatMap.mpr ⟨S, hS, List.mem_append_right _ ?_⟩⟩ <;> rw [hpr] <;> simp

/-- **`hden` of `compute_balanceX` is discharged** by the nonzero denominators of the compute request
lists (which the IO event of each balance excludes, `TeleC.den_ne_of_out`). -/
theorem hden_of_reqs
    (hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
      (orbit := orbit) (P := P) bl, compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r) ≠ 0) :
    ∀ r < n, ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), pairFX (EN r) S = 1 →
      pairDaX δ (gatherEnv b (EN r)) (EN r) S ≠ 0 ∧ pairDbX δ (gatherEnv b (EN r)) (EN r) S ≠ 0 := by
  intro i hi S hS hf
  unfold pairFX at hf
  unfold pairDaX pairDbX
  cases hp : S.pair with
  | none => rw [hp] at hf; exact absurd hf (by simp)
  | some q =>
    obtain ⟨fl, a, c, bl⟩ := q
    rw [hp] at hf
    simp only at hf ⊢
    obtain ⟨ha, hc⟩ := pair_mem_consQX (EN i) hS hp hf
    have hmem : ∀ r ∈ consQX (EN i) bl, keyX (K := K) (mOf bl) r (EN i) ∈
        compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
          (orbit := orbit) (P := P) bl := fun r hr =>
      List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map_of_mem hr⟩
    refine ⟨?_, ?_⟩
    · rw [denQX_val δ _ _ a (mOf bl) (consQX_len _ bl a ha), coinsCQ_EN]
      exact hne bl _ (hmem a ha)
    · rw [denQX_val δ _ _ c (mOf bl) (consQX_len _ bl c hc), coinsCQ_EN]
      exact hne bl _ (hmem c hc)

/-- **The compute side of each J-8 handle-class balance, in list form**: on an accepted
`computeChipVCLHX` trace with nonzero request denominators,
`Σ_{r ∈ compReqsX bl} compress(γH′, ρH′)(lift r)⁻¹ = (Re ρ_bl, Im ρ_bl)`. -/
theorem compReqsX_sum (C : BCtx hn nodes b δ chalV pubVal orbit P)
    (hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
      (orbit := orbit) (P := P) bl, compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r) ≠ 0)
    (bl : Bal) :
    ((compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
        (orbit := orbit) (P := P) bl).map fun r => (compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk (algebraMap F K δ) (limbVal b pubVal (balCols bl).2.1) (limbVal b pubVal (balCols bl).2.2.2) := by
  rw [← compute_balanceX_keys C (hden_of_reqs hne) bl, compReqsX, List.map_flatMap, sum_flatMap_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.map_map]
  rfl

end Chip

end

end Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8
