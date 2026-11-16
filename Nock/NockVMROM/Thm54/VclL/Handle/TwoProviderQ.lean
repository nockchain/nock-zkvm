/-
  Nock/NockVMROM/Thm54/VclL/Handle/TwoProviderQ.lean

The cell validity balance under `γ′ρ′` has TWO providers at J-8: the cell rows (`mv`, `vKeyP`) and the
  atom roots (`mb`, g5, an EXTERNAL provider list `xs` here, with weights).  Its consumers are the cell
  rows' weighted children (`cellVInternal`) and the claim records `reqs`.

  * table level: `served2_of_balanced2` (A-3r's `ValidityBalanced2` ⇒ `ValidityServed2`),
    `rowOK_of_gates2` (`RowGates` + two-provider served with rank-`(0,0)` external keys ⇒ `RowOK`);
  * **consumer-side served lemma for weighted child keys** (`cell_child_served2`): outside the weighted IO
    failure event of `reqs ++ internal` against `cell providers ++ xs`, under the verifier balance
    `Σ_reqs den⁻¹ = (pub₀, pub₁) + Σ_xs w·den⁻¹` and the count `< p`, every weighted child key is a cell
    row's `vKeyP` or an external key;
  * **key decoding** (`child_key_decode`): a child key equal to the claim-shaped vector `claimVec e idx hi lo`
    (`ClaimVS`) names `e`, `hi`, `lo`, `idx`;
  * `cell_validityServed2` — `ValidityServed2 (cellTableOf …) vp` when every external vector is
    `claimVec` of a key of `vp` (ranks and serial below `p`);
  * **rank-0 match against `RowOK`**: `cellTable_accepts2` (`TableAccepts2`, with `rowOK_of_gates2` where
    the external keys' rank is `(0, 0)`), and **`cell_row_genuine2`** — the chip-level two-provider
    `row_genuine` (`DecodeTree.row_genuine2` on the accepted table; `AtomLeaves` — the atom table's T1 at
    `y` on its roots — is the one remaining hypothesis on the external keys);
  * the wire kind (item 3): `keyHK` (`keyH` with kind entries `w + kb`), `side_kind`, **`keyHK_eval`** —
    the provided wire key is `recFK (exportRecK c)` of the row's round-0 data (with
    `DecodeTree.exportRecK_grounded`, the export record is grounded at all three kinds), and
    **`exportHK_genuine`** — `exportH_genuine` re-proved at the wire kind on `cellChipHQK` (restriction
    `cellChipHQK_restrict_cell_sat` to `cellChip`, the two-provider accepted table, `keyHK_eval`).
-/
import Nock.NockVMROM.Thm54.P8Core.VclL.DecodeTree
import Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Table level -/

section Table
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp]

/-- **A-3r's two-provider ℕ balance gives the two-provider served form.** -/
theorem served2_of_balanced2 {t : List (CellRow q Kfp)} {vp vl : List (VKey Kfp)}
    (hbal : CellTwinK.ValidityBalanced2 t vp vl) : ValidityServed2 t vp := by
  intro c hc s hw
  have hmem : (c.fpS s, c.b0.hiS s, c.b0.loS s, c.b0.idS s) ∈ expand (vCons t ++ vl.map (·, 1)) := by
    rw [mem_expand]
    refine ⟨((c.fpS s, c.b0.hiS s, c.b0.loS s, c.b0.idS s), 1), ?_, one_ne_zero, rfl⟩
    apply List.mem_append_left
    simp only [vCons, List.mem_flatMap]
    refine ⟨c, hc, ?_⟩
    cases s
    · simp [CellRowB0.wS] at hw; simp [CellRow.fpS, CellRowB0.hiS, CellRowB0.loS, CellRowB0.idS, hw]
    · simp [CellRowB0.wS] at hw; simp [CellRow.fpS, CellRowB0.hiS, CellRowB0.loS, CellRowB0.idS, hw]
  have hprov := hbal.mem_iff.mpr hmem
  rw [expand, List.flatMap_append, List.mem_append] at hprov
  rcases hprov with hp | hp
  · left
    have hp' : (c.fpS s, c.b0.hiS s, c.b0.loS s, c.b0.idS s) ∈ expand (vProv t) := hp
    rw [mem_expand] at hp'
    obtain ⟨kc, hkc, -, hk⟩ := hp'
    simp only [vProv, List.mem_map] at hkc
    obtain ⟨c', hc', rfl⟩ := hkc
    simp only [Prod.mk.injEq] at hk
    exact ⟨c', hc', hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩
  · right
    simpa [List.mem_flatMap, List.mem_replicate] using hp

/-- **`RowOK` from the row gates under two providers**: a weighted child's limbs are a providing cell
row's (ranged by that row's bits) or an external key's, which are `(0, 0)`. -/
theorem rowOK_of_gates2 {z : Kfp} {t : List (CellRow q Kfp)} {vp : List (VKey Kfp)}
    (hg : ∀ c ∈ t, RowGates z c) (hs : ValidityServed2 t vp)
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0) :
    ∀ c ∈ t, RowOK z c := by
  intro c hc
  have g := hg c hc
  have side : ∀ s, c.b0.wS s = true → c.b0.loS s < 2 ^ 62 ∧ c.b0.hiS s < 2 ^ 48 := by
    intro s hw
    rcases hs c hc s hw with ⟨c', hc', -, hhi, hlo, -⟩ | hv
    · rw [hhi, hlo]; exact ⟨(hg c' hc').lo_lt, (hg c' hc').hi_lt⟩
    · obtain ⟨h1, h2⟩ := hvp0 _ hv
      simp only at h1 h2
      rw [h1, h2]; omega
  have hL : c.b0.loL < 2 ^ 62 ∧ c.b0.hiL < 2 ^ 48 := by
    cases hw : c.b0.wL with
    | false => obtain ⟨-, h1, h2⟩ := g.atomL hw; rw [h1, h2]; omega
    | true => exact side .L hw
  have hR : c.b0.loR < 2 ^ 62 ∧ c.b0.hiR < 2 ^ 48 := by
    cases hw : c.b0.wR with
    | false => obtain ⟨-, h1, h2⟩ := g.atomR hw; rw [h1, h2]; omega
    | true => exact side .R hw
  exact ⟨g.cons, g.lo_lt, hL.1, hR.1, g.hi_lt, hL.2, hR.2, g.carry_le, g.limbLo, g.limbHi,
    g.atomL, g.atomR⟩

end Table

/-! ## 2. Chip level -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **Key decoding**: a child key equal to a claim-shaped vector names its fingerprint, limbs and serial. -/
theorem child_key_decode (i : Fin n) (lR loL hiL idL : ℕ) (e : FP 𝕂′) (idx hi lo : F)
    (hk : cellKey δF b hn nodes orbit chals pubs Q 5
        ((QFP.var lR).entries ++ [QE.mk2 (cv loL) (cv hiL), QE.base (cv idL)]) i =
      ClaimVS.claimVec δF e idx hi lo) :
    (QFP.var lR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i) = e ∧
      cellB δF b hn nodes orbit chals pubs Q hiL i = hi ∧
      cellB δF b hn nodes orbit chals pubs Q loL i = lo ∧
      cellB δF b hn nodes orbit chals pubs Q idL i = idx := by
  have ex : ∀ c : Fin 5, _ := fun c => congrFun hk c
  have e0 := ex 0; have e1 := ex 1; have e2 := ex 2; have e3 := ex 3; have e4 := ex 4
  simp only [ClaimVS.claimVec, cellKey, keyVec, QFP.var, QFP.entries, List.cons_append,
    List.nil_append, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero,
    List.getD_cons_succ] at e0 e1 e2 e3 e4
  have e3' : (3 : Fin 5).val = 3 := rfl
  have e4' : (4 : Fin 5).val = 4 := rfl
  simp only [e3', e4', List.getD_cons_succ, List.getD_cons_zero] at e3 e4
  rw [ev_mk2, Quad.mk_eq_mk_iff] at e3
  rw [ev_base, liftQ, ← Quad.mk_base, Quad.mk_eq_mk_iff] at e4
  refine ⟨?_, (algebraMap F K).injective e3.2, (algebraMap F K).injective e3.1,
    (algebraMap F K).injective e4.1⟩
  cases e
  simp only [QFP.ev, QFP.var] at e0 e1 e2 ⊢
  rw [e0, e1, e2]

variable [Fintype K] [DecidableEq (Quad (algebraMap F K δF))]

/-- **The consumer-side served lemma for weighted child keys (two providers).**  Outside the weighted IO
failure event of `reqs ++ internal` against `cell providers ++ xs`, under the verifier balance
`Σ_reqs den⁻¹ = (pub₀, pub₁) + Σ_xs w·den⁻¹` and the consumer count `< p`: every weighted child key is a
cell row's provider key or the vector of an external provider. -/
theorem cell_child_served2
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : 𝕂′) (hok : ChalsOK δF chals γ ρ 11)
    {p : ℕ} [CharP 𝕂′ p] (reqs : List (Fin 5 → 𝕂′)) (xs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum =
      Quad.mk _ (pubs 0) (pubs 1) + (xs.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1)⁻¹).sum)
    (hout : (γ, ρ) ∉ FiniteIO.IOFailureEventW (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q)
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs Q) ++ xs))
    (hxne : ∀ x ∈ xs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1 ≠ 0)
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q).length < p) :
    ∀ r ∈ cellVInternal δF b hn nodes orbit chals pubs Q,
      (∃ j : Fin n, cellKey δF b hn nodes orbit chals pubs Q 5 Cell.vKeyP j = r) ∨ r ∈ xs.map Prod.fst := by
  set M := cellValidityFacts δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj γ ρ hok with hM
  have hd := TeleC.den_ne_of_out _ _ γ ρ hout
  have hlook := ServeH.served_of_balance (p := p) _ _ γ ρ hd
    (by
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
        exact M.ne_zero r hr
      · exact hxne q hq)
    (by
      rw [List.map_append, List.sum_append, hsum, List.map_append, List.sum_append]
      have hv := cell_validity_sum δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj γ ρ hok
      simp only [SVFrame.liftWts, List.map_map, Function.comp_def]
      rw [hv]; ring)
    hcount hout
  intro r hr
  have := hlook r (List.mem_append_right _ hr)
  rw [List.map_append, List.mem_append, SVFrame.liftWts_fst] at this
  rcases this with h | h
  · obtain ⟨q, hq, hqr⟩ := List.mem_map.mp h
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq
    exact Or.inl ⟨j, hqr⟩
  · exact Or.inr h

variable [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))]

/-- **`ValidityServed2` on the cell table read off an accepted trace**: every external vector is the
claim-shaped vector of a key of `vp` whose ranks and serial lie below `p`. -/
theorem cell_validityServed2 (hF : GeneratedField.PrimeFieldElems F)
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : 𝕂′) (hok : ChalsOK δF chals γ ρ 11)
    {p : ℕ} [CharP 𝕂′ p] (reqs : List (Fin 5 → 𝕂′)) (xs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum =
      Quad.mk _ (pubs 0) (pubs 1) + (xs.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1)⁻¹).sum)
    (hout : (γ, ρ) ∉ FiniteIO.IOFailureEventW (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q)
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs Q) ++ xs))
    (hxne : ∀ x ∈ xs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1 ≠ 0)
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q).length < p)
    (vp : List (VKey 𝕂′))
    (hx : ∀ x ∈ xs, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δF k.1 (k.2.2.2 : F) (k.2.1 : F) (k.2.2.1 : F))
    (hvpr : ∀ k ∈ vp, k.2.1 < ringChar F ∧ k.2.2.1 < ringChar F ∧ k.2.2.2 < ringChar F) :
    ValidityServed2 (cellTableOf δF b nodes orbit chals pubs Q) vp := by
  have hfind := cell_child_served2 δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj γ ρ hok
    reqs xs hsum hout hxne hcount
  have hmem : ∀ j : Fin n, cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q j)
      (cellEnvF b nodes orbit chals pubs Q j) ∈ cellTableOf δF b nodes orbit chals pubs Q :=
    fun j => List.mem_ofFn.mpr ⟨j, rfl⟩
  intro c hc s hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  -- one side, parametrised by its columns
  have key : ∀ (lR loL hiL idL wL : ℕ)
      (hwk : cellB δF b hn nodes orbit chals pubs Q wL i = 1)
      (hin : cellKey δF b hn nodes orbit chals pubs Q 5
          ((QFP.var lR).entries ++ [QE.mk2 (cv loL) (cv hiL), QE.base (cv idL)]) i ∈
        cellVInternal δF b hn nodes orbit chals pubs Q),
      (∃ c' ∈ cellTableOf δF b nodes orbit chals pubs Q,
        (QFP.var lR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i) = c'.p ∧
        natOf (cellB δF b hn nodes orbit chals pubs Q hiL i) = c'.b0.hi ∧
        natOf (cellB δF b hn nodes orbit chals pubs Q loL i) = c'.b0.lo ∧
        natOf (cellB δF b hn nodes orbit chals pubs Q idL i) = c'.b0.idx) ∨
      ((QFP.var lR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i),
        natOf (cellB δF b hn nodes orbit chals pubs Q hiL i), natOf (cellB δF b hn nodes orbit chals pubs Q loL i),
        natOf (cellB δF b hn nodes orbit chals pubs Q idL i)) ∈ vp := by
    intro lR loL hiL idL wL _ hin
    rcases hfind _ hin with ⟨j, hj⟩ | hxs
    · obtain ⟨hfp, hhi, hlo, hid⟩ :=
        vKey_decode δF b hn nodes orbit chals pubs Q i j lR loL hiL idL hj.symm
      exact Or.inl ⟨_, hmem j, hfp, natOf_congr hhi, natOf_congr hlo, natOf_congr hid⟩
    · obtain ⟨x, hx', hxe⟩ := List.mem_map.mp hxs
      obtain ⟨k, hk, hkx⟩ := hx x hx'
      rw [hkx] at hxe
      obtain ⟨hfp, hhi, hlo, hid⟩ :=
        child_key_decode δF b hn nodes orbit chals pubs Q i lR loL hiL idL _ _ _ _ hxe.symm
      obtain ⟨r1, r2, r3⟩ := hvpr k hk
      refine Or.inr ?_
      rw [hfp, hhi, hlo, hid, natOf_natCast hF r1, natOf_natCast hF r2, natOf_natCast hF r3]
      exact hk
  cases s with
  | L =>
    have hw1 : cellB δF b hn nodes orbit chals pubs Q Cell.wL i = 1 := by
      simpa [cellRowOf, cellB0Of, CellRowB0.wS] using hw
    exact key Cell.lR Cell.loL Cell.hiL Cell.idL Cell.wL hw1
      (List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
        List.mem_append_left _ (by rw [if_pos hw1]; exact List.mem_singleton_self _)⟩)
  | R =>
    have hw1 : cellB δF b hn nodes orbit chals pubs Q Cell.wR i = 1 := by
      simpa [cellRowOf, cellB0Of, CellRowB0.wS] using hw
    exact key Cell.rR Cell.loR Cell.hiR Cell.idR Cell.wR hw1
      (List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
        List.mem_append_right _ (by rw [if_pos hw1]; exact List.mem_singleton_self _)⟩)

/-- **The accepted two-provider cell table** (`TableAccepts2`): serial gate, `RowOK` through
`rowOK_of_gates2` (an external key has rank `(0, 0)`: the rank-0 match against `RowOK`), and
`cell_validityServed2`. -/
theorem cellTable_accepts2 (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (γ ρ : 𝕂′) (hok : ChalsOK δF chals γ ρ 11)
    {p : ℕ} [CharP 𝕂′ p] (reqs : List (Fin 5 → 𝕂′)) (xs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum =
      Quad.mk _ (pubs 0) (pubs 1) + (xs.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1)⁻¹).sum)
    (hout : (γ, ρ) ∉ FiniteIO.IOFailureEventW (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q)
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs Q) ++ xs))
    (hxne : ∀ x ∈ xs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1 ≠ 0)
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q).length < p)
    (vp : List (VKey 𝕂′))
    (hx : ∀ x ∈ xs, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δF k.1 (k.2.2.2 : F) (k.2.1 : F) (k.2.2.1 : F))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar F) :
    TableAccepts2 (Quad.mk (algebraMap F K δF) (chals 2) (chals 3))
      (cellTableOf δF b nodes orbit chals pubs Q) vp := by
  have hp : 0 < ringChar F := by omega
  have hs := cell_validityServed2 δF b hn nodes orbit chals pubs Q hF hsat hbind hinj hadj γ ρ hok
    reqs xs hsum hout hxne hcount vp hx (fun k hk => by
      obtain ⟨h1, h2, h3⟩ := hvp0 k hk; exact ⟨by omega, by omega, h3⟩)
  exact ⟨cellTable_serial δF b hn nodes orbit chals pubs Q hsat hF hbind hinj hadj hnp,
    rowOK_of_gates2 (cellTable_rowGates δF b hn nodes orbit chals pubs Q hsat hF hq hz) hs
      (fun k hk => ⟨(hvp0 k hk).1, (hvp0 k hk).2.1⟩),
    hs⟩

/-- **The chip-level two-provider `row_genuine`.**  On an accepted cell trace, outside the two-provider
validity IO event, with the external keys atom roots (`AtomLeaves`, the atom table's T1 at `y`), at any
encoder `E` that is the cons gate on cells and the inline-atom gate on small atoms (the bivariate `(z, y)`
encoder at J-8, frame wiring J-8a): every row decodes (`decodeTree` at `leaf2 ext`) to `[L R]` with
`p = E [L R]`, `l = E L`, `r = E R`; a
weighted rank-`(0, 0)` child is the atom of its atom-table serial; any other weighted child is the decoded
noun of its cell serial; a zero-weight child is its inline atom. -/
theorem cell_row_genuine2 (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    [Fact (ringChar F).Prime]
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (γ ρ : 𝕂′) (hok : ChalsOK δF chals γ ρ 11)
    {p : ℕ} [CharP 𝕂′ p] (reqs : List (Fin 5 → 𝕂′)) (xs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum =
      Quad.mk _ (pubs 0) (pubs 1) + (xs.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1)⁻¹).sum)
    (hout : (γ, ρ) ∉ FiniteIO.IOFailureEventW (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q)
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs Q) ++ xs))
    (hxne : ∀ x ∈ xs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1 ≠ 0)
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q).length < p)
    (vp : List (VKey 𝕂′))
    (hx : ∀ x ∈ xs, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δF k.1 (k.2.2.2 : F) (k.2.1 : F) (k.2.2.1 : F))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar F)
    (E : Noun → FP 𝕂′)
    (hcons : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap F K δF) (chals 2) (chals 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar F) (Quad.mk (algebraMap F K δF) (chals 2) (chals 3)) E)
    (ext : ℕ → Option Noun) (hvp : AtomLeaves E vp ext)
    {c : CellRow (ringChar F) 𝕂′} (hc : c ∈ cellTableOf δF b nodes orbit chals pubs Q) :
    ∃ L R, preZNounOfTable2 ((cellTableOf δF b nodes orbit chals pubs Q).map (·.b0)) ext c.b0.idx =
        some (.cell L R) ∧
      c.p = E (.cell L R) ∧ c.l = E L ∧ c.r = E R ∧
      (∀ s, c.b0.wS s = true → c.b0.hiS s = 0 ∧ c.b0.loS s = 0 →
        ext (c.b0.idS s) = some (if s = .L then L else R) ∧ ∃ v, ext (c.b0.idS s) = some (.atom v)) ∧
      (∀ s, c.b0.wS s = true → ¬ (c.b0.hiS s = 0 ∧ c.b0.loS s = 0) →
        preZNounOfTable2 ((cellTableOf δF b nodes orbit chals pubs Q).map (·.b0)) ext (c.b0.idS s) =
          some (if s = .L then L else R)) ∧
      (c.b0.wL = false → L = .atom c.b0.aL.val) ∧ (c.b0.wR = false → R = .atom c.b0.aR.val) :=
  row_genuine2 hq hcons hE (cellTable_accepts2 δF b hn nodes orbit chals pubs Q hF hq hz hsat hbind hinj hadj hnp
    γ ρ hok reqs xs hsum hout hxne hcount vp hx hvp0) hvp hc

end Chip


/-! ## 3. The wire kind `k = w + kb` in the provided export key -/

section WireKind
variable {F : Type} [Field F] [DecidableEq F]

/-- **`keyHK`** — `keyH` with its two kind entries edited to `k = w + kb` (SPEC §2.1; the 5-entry shape is
unchanged). -/
def keyHK : List (CoeffExpr F) :=
  [ cv Cell.idx, .add (cv Cell.wL) (cv CellTwinK.kbL), CellH.valE Cell.wL Cell.idL Cell.aL,
    .add (cv Cell.wR) (cv CellTwinK.kbR), CellH.valE Cell.wR Cell.idR Cell.aR ]

/-- A wire export record as its five field entries. -/
def recFK (r : ℕ × KHandle × KHandle) : List F :=
  [(r.1 : F), (r.2.1.1 : F), (r.2.1.2 : F), (r.2.2.1 : F), (r.2.2.2 : F)]

theorem natOf_eq_zero_iff (hF : GeneratedField.PrimeFieldElems F) (hp : 0 < ringChar F) (x : F) :
    natOf x = 0 ↔ x = 0 := by
  constructor
  · intro h; rw [← natOf_cast hF x, h, Nat.cast_zero]
  · rintro rfl; exact natOf_zero hF hp

/-- **One side's wire kind**: under the five side gates and a boolean weight, `w + kb` is the field image
of `kindS` read through `natOf` (`0` atom, `1` cell, `2` big atom). -/
theorem side_kind (hF : GeneratedField.PrimeFieldElems F) (hp : 0 < ringChar F) (eF : Env F)
    (kb inv w lo hi : ℕ) (hg : ∀ g ∈ (CellTwinK.sideGates (F := F) kb inv w lo hi), g.eval eF = 0)
    (hw : eF.trace w = 0 ∨ eF.trace w = 1) :
    eF.trace w + eF.trace kb =
      ((if decide (eF.trace w = 1) then
          (if natOf (eF.trace hi) = 0 ∧ natOf (eF.trace lo) = 0 then 2 else 1) else 0 : ℕ) : F) := by
  have hk := CellTwinK.sideGates_kind kb inv w lo hi eF hg
  have hb := hg (boolE (cv kb)) (by simp [CellTwinK.sideGates])
  have h5 := hg (.mul (cv kb) (notE (cv w))) (by simp [CellTwinK.sideGates])
  simp only [CoeffExpr.eval, boolE, cv, notE] at hb h5
  rcases hw with h0 | h1
  · have hk0 : eF.trace kb = 0 := by rw [h0] at h5; simpa using h5
    have : ¬ (eF.trace w = 1) := by rw [h0]; exact zero_ne_one
    simp [h0, hk0, this]
  · simp only [natOf_eq_zero_iff hF hp]
    by_cases hr : eF.trace hi = 0 ∧ eF.trace lo = 0
    · have hk1 : eF.trace kb = 1 := hk.mpr ⟨h1, hr.2, hr.1⟩
      simp [h1, hk1, hr]; norm_num
    · have hk0 : eF.trace kb = 0 := by
        rcases bool_val hb with h | h
        · exact h
        · exact absurd (hk.mp h) (fun ⟨_, a, b⟩ => hr ⟨b, a⟩)
      simp [h1, hk0, hr]

/-- **The provided wire key IS the row's wire export record**: on a base env where the kind gates hold and
the weights are boolean, `keyHK` evaluates to `recFK (exportRecK (cellB0Of eF))`. -/
theorem keyHK_eval [Fact (ringChar F).Prime] (hF : GeneratedField.PrimeFieldElems F) (hp : 0 < ringChar F) (eF : Env F)
    (hg : ∀ g ∈ (CellTwinK.kindGates (F := F)), g.eval eF = 0)
    (hwL : eF.trace Cell.wL = 0 ∨ eF.trace Cell.wL = 1)
    (hwR : eF.trace Cell.wR = 0 ∨ eF.trace Cell.wR = 1) :
    (keyHK : List (CoeffExpr F)).map (fun g => g.eval eF) = recFK (exportRecK (cellB0Of eF)) := by
  have hk := keyH_eval hF eF hwL hwR
  simp only [CellH.keyH, recF, hF2, exportRec, hL, hR, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.cons.injEq, and_true] at hk
  obtain ⟨e0, -, e2, -, e4⟩ := hk
  have kL := side_kind hF hp eF _ _ _ _ _ (fun g hg' => hg g (List.mem_append_left _ hg')) hwL
  have kR := side_kind hF hp eF _ _ _ _ _ (fun g hg' => hg g (List.mem_append_right _ hg')) hwR
  simp only [keyHK, recFK, exportRecK, hK, kindS, List.map_cons, List.map_nil, List.cons.injEq,
    and_true]
  refine ⟨e0, ?_, e2, ?_, e4⟩
  · simp [CoeffExpr.eval, cv, cellB0Of, CellRowB0.wS, CellRowB0.hiS, CellRowB0.loS] at kL ⊢; split_ifs at kL ⊢ <;> first | exact kL | (simp_all; done) | (erw [Nat.cast_ite]; simp_all; done) | (norm_cast; simp_all; done) | (rename_i h1 h2; erw [if_neg (fun h => h2 h.1 h.2)]; simp)
  · simp [CoeffExpr.eval, cv, cellB0Of, CellRowB0.wS, CellRowB0.hiS, CellRowB0.loS] at kR ⊢; split_ifs at kR ⊢ <;> first | exact kR | (simp_all; done) | (erw [Nat.cast_ite]; simp_all; done) | (norm_cast; simp_all; done) | (rename_i h1 h2; erw [if_neg (fun h => h2 h.1 h.2)]; simp)

end WireKind


/-! ## 4. `exportH_genuine` at the wire kind, on `cellChipHQK` -/

section ExportK
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

theorem hqkCell_shift : ∀ j < (cellTemplate δF).width 3,
    shiftCol 129 134 j < (CellTwinK.cellTemplateHQK δF).width 3 :=
  shift_lt _ _ 129 134 (cellTemplate_baseCols δF) (CellTwinK.cellTemplateHQK_baseCols δF) (by omega)
    (by rw [cellTemplate_extCols, CellTwinK.cellTemplateHQK_extCols]; omega)

/-- Restriction of a `cellChipHQK` trace to `cellChip`'s `225` columns. -/
noncomputable def restrictHQKCell
    (Q : Fin (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).rap.w → F[X]) :
    Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X] :=
  restrictQ 129 134 (hqkCell_shift δF) Q

/-- **`restrict`**: `cellChipHQK`-accepted ⇒ `cellChip`-accepted on the restriction. -/
theorem cellChipHQK_restrict_cell_sat
    (Q : Fin (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies
      (restrictHQKCell δF b hn nodes orbit chals pubs Q) := by
  have hR : (cellTemplate δF).extCols = 32 := cellTemplate_extCols δF
  exact expandChip_restrict b orbit (rowNodeSet nodes) chals pubs (cellTemplate δF)
    (CellTwinK.cellTemplateHQK δF) 129 134 (cellTemplate_baseCols δF)
    (CellTwinK.cellTemplateHQK_baseCols δF)
    (by omega) (by rw [hR, CellTwinK.cellTemplateHQK_extCols]; omega)
    (fun g hg => ⟨List.mem_append_left _ hg, cellBase_below g hg⟩)
    (fun g hg => ⟨List.mem_append_left _ hg, by rw [hR]; exact cellMixed_below δF g hg⟩)
    rfl rfl Q hsat

theorem cellChipHQK_restrict_bind
    (Q : Fin (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hbind : (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).BindsPreprocessing Q) :
    (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing
      (restrictHQKCell δF b hn nodes orbit chals pubs Q) := by
  intro j
  have hj := hbind j
  fin_cases j
  · exact hj
  · exact hj

/-- Row `i`'s base environment on `cellChipHQK`. -/
abbrev hqkEF {w : ℕ} (Q : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 134 chals) (slotVal b 134 pubs)

theorem hqkEF_trace (Q : Fin (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).rap.w → F[X])
    (i : Fin n) {j : ℕ} (hj : j < 129) :
    (hqkEF b nodes orbit chals pubs Q i).trace j =
      (cellEnvF b nodes orbit chals pubs (restrictHQKCell δF b hn nodes orbit chals pubs Q) i).trace j := by
  have hw : (cellChip δF b hn nodes orbit chals pubs).rap.w = 225 :=
    (cellChip_fingerprint δF b hn nodes orbit chals pubs).1
  have h0 : j < (cellChip δF b hn nodes orbit chals pubs).rap.w := by rw [hw]; omega
  have h1 : j < (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).rap.w := by
    rw [CellTwinK.cellChipHQK_width]; omega
  simp only [cellEnvF, Reify.envOfTrace, dif_pos h0, dif_pos h1, restrictHQKCell, restrictQ]
  congr 2
  apply Fin.ext
  simp [shiftCol, hj]

theorem cellB0Of_hqk (Q : Fin (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).rap.w → F[X])
    (i : Fin n) :
    cellB0Of (hqkEF b nodes orbit chals pubs Q i) =
      cellB0Of (cellEnvF b nodes orbit chals pubs (restrictHQKCell δF b hn nodes orbit chals pubs Q) i) := by
  simp only [cellB0Of, hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idx < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idL < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idR < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.wL < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.wR < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.aL < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.aR < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.lo < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hi < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.loL < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hiL < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.loR < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hiR < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.carry < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.mv < 129),
    hqkEF_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.mx < 129)]

variable [Fintype K] [DecidableEq (Quad (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))] [Fact (ringChar F).Prime]

/-- **`exportHK_genuine`** — `exportH_genuine` re-proved for the wire kind `k = w + kb`.  On a trace accepted
by `cellChipHQK`, outside the two-provider validity IO event (the hypotheses of `cellTable_accepts2` on the
restriction) with atom-root external keys: at every row the wire key the chip provides (`keyHK`) is
`recFK (exportRecK c)` of the row's round-0 data `c`, `c` is a row of the decoded table, and the record is
grounded at all three kinds (`denK (1, idx) = [denK hK_L, denK hK_R]`). -/
theorem exportHK_genuine (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    (Q : Fin (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (CellTwinK.cellChipHQK δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (γ ρ : 𝕂′) (hok : ChalsOK δF chals γ ρ 11)
    {p : ℕ} [CharP 𝕂′ p] (reqs : List (Fin 5 → 𝕂′)) (xs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum =
      Quad.mk _ (pubs 0) (pubs 1) + (xs.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1)⁻¹).sum)
    (hout : (γ, ρ) ∉ FiniteIO.IOFailureEventW
      (reqs ++ cellVInternal δF b hn nodes orbit chals pubs (restrictHQKCell δF b hn nodes orbit chals pubs Q))
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs
        (restrictHQKCell δF b hn nodes orbit chals pubs Q)) ++ xs))
    (hxne : ∀ x ∈ xs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1 ≠ 0)
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs
      (restrictHQKCell δF b hn nodes orbit chals pubs Q)).length < p)
    (vp : List (VKey 𝕂′))
    (hx : ∀ x ∈ xs, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δF k.1 (k.2.2.2 : F) (k.2.1 : F) (k.2.2.1 : F))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar F)
    (E : Noun → FP 𝕂′)
    (hcons : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap F K δF) (chals 2) (chals 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar F) (Quad.mk (algebraMap F K δF) (chals 2) (chals 3)) E)
    (ext : ℕ → Option Noun) (hvp : AtomLeaves E vp ext) (i : Fin n) :
    let tb := (cellTableOf δF b nodes orbit chals pubs
      (restrictHQKCell δF b hn nodes orbit chals pubs Q)).map (·.b0)
    let c := cellB0Of (hqkEF b nodes orbit chals pubs Q i)
    (keyHK : List (CoeffExpr F)).map (fun g => g.eval (hqkEF b nodes orbit chals pubs Q i)) =
        recFK (exportRecK c) ∧ c ∈ tb ∧
      ∃ L R, denK tb ext (1, c.idx) = some (.cell L R) ∧ denK tb ext (hK c .L) = some L ∧
        denK tb ext (hK c .R) = some R := by
  intro tb c
  set Q0 := restrictHQKCell δF b hn nodes orbit chals pubs Q
  have hsat0 := cellChipHQK_restrict_cell_sat δF b hn nodes orbit chals pubs Q hsat
  have hbind0 := cellChipHQK_restrict_bind δF b hn nodes orbit chals pubs Q hbind
  have hacc := cellTable_accepts2 δF b hn nodes orbit chals pubs Q0 hF hq hz hsat0 hbind0 hinj hadj hnp
    γ ρ hok reqs xs hsum hout hxne hcount vp hx hvp0
  have hbase := ((expandChip_satisfies_iff_language _ b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)).1
  have hbool : ∀ w, boolE (cv w) ∈ Cell.baseGates (F := F) →
      (hqkEF b nodes orbit chals pubs Q i).trace w = 0 ∨ (hqkEF b nodes orbit chals pubs Q i).trace w = 1 := by
    intro w hw
    have g := hbase _ (List.mem_append_left _ hw)
    simp only [CoeffExpr.eval, cv] at g
    exact bool_val g
  have hkind : ∀ g ∈ (CellTwinK.kindGates (F := F)), g.eval (hqkEF b nodes orbit chals pubs Q i) = 0 :=
    fun g hg => hbase g (List.mem_append_right _ hg)
  have hc : cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q0 i)
      (cellEnvF b nodes orbit chals pubs Q0 i) ∈ cellTableOf δF b nodes orbit chals pubs Q0 :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  have hcb : c = (cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q0 i)
      (cellEnvF b nodes orbit chals pubs Q0 i)).b0 := cellB0Of_hqk δF b hn nodes orbit chals pubs Q i
  refine ⟨keyHK_eval hF (by omega) _ hkind (hbool Cell.wL (by simp [Cell.baseGates]))
      (hbool Cell.wR (by simp [Cell.baseGates])),
    by rw [hcb]; exact List.mem_map_of_mem hc, ?_⟩
  rw [hcb]
  exact exportRecK_grounded hq hcons hE hacc hvp hc

end ExportK

end

end Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
