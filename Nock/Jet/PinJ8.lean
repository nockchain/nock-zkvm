/-
  Nock/Jet/PinJ8.lean

  New module, additive; the J chip stays `jetTemplateJ8T` (width 71, no new coin,
  column or gate); `jetTemplateJ8R` (89) stays on the branch as history, unused.

  The verifier adds, for each registered id `id ∈ regs` (with its public serial `idx id` and the
  public rank `rk id` of the compiled formula):
  * **(J side)** one consume of the in-chip registry key `(id, 1, idx id, tag 2)` (`pinKey`, tag-last
    `tlF`) in the J tagged balance (`pinCons`), i.e. among the other service consumers `reqO` of
    `RapJetJ8.bal_of_service`.

  * `inchip_served`: the served half of `bal_of_service` for ANY in-chip-shaped key among the
    consumers (not only the chip's own); `pin_served`: each pin is provided by a row's in-chip
    provide.
  * `reg_filterMap` / `reg_unique`: with `regs` nodup (a public check), a registry row is determined
    by its id.
  * **`pin_forces`**: on an `Accepted` trace whose pins are served, every `.reg` row has handle
    `(kN, vN) = (1, idx id)`.
  * **`hReg_of_pin`**: JB's `hReg` (`denK (kN, vN) = compile p (R id)`) from the pin and the served
    claim keys, through `RegJ8R.hReg_of_served` at `vN = idx id` (the `regKindGate` hypothesis is
    discharged by `kN = 1`: under the pin no new gate is needed).
-/
import Nock.Jet.RegJ8R
import Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.Jet.PinJ8

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8
open Nock.Jet.RegJ8R
open Nock.Framework Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The pin keys -/

section Key
variable {F : Type} [Field F]

/-- **The verifier's in-chip registry pin** for `id` (tag-first, the `provK` form of a `.reg` row):
`(2, id, 1, idx)`. -/
def pinKey (id idx : ℕ) : List F := [((2 : ℕ) : F), (id : F), 1, (idx : F)]

theorem pinKey_shape (id idx : ℕ) : (∃ a b c d : F, (pinKey id idx : List F) = [((1 : ℕ) : F), a, b, c, d]) ∨
    ∃ a b c : F, (pinKey id idx : List F) = [((2 : ℕ) : F), a, b, c] :=
  Or.inr ⟨_, _, _, rfl⟩

end Key

/-- **The pin consumes** the verifier adds to the J tagged (service) balance: one per registered id,
tag last, as `K`-vectors (the `jCons` encoding). -/
def pinCons {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (regs : List ℕ)
    (idx : ℕ → ℕ) : List (Fin 8 → K) :=
  regs.map fun id => keyK 8 (tlF (pinKey (F := ZMod p) id (idx id)))

/-! ## 2. The served half of the in-chip balance, for any in-chip key -/

section Served
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "RJ" => rowJ b nodes orbit chals pubs lay P

/-- **Every in-chip-shaped consumed key is provided in-chip** (the served half of
`bal_of_service`, for any key among `reqO ++ jCons`, in particular the verifier's pins). -/
theorem inchip_served [DecidableEq K] [DecidableEq 𝕂′] [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hO7 : ∀ q ∈ provO, q.1 ⟨7, by norm_num⟩ = 0)
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        ((jProv b nodes orbit chals pubs lay P ++ provO).map
          fun q => (liftRec (L := 𝕂′) q.1, algebraMap K 𝕂′ q.2)))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p) :
    ∀ κ : List (ZMod p), ((∃ a b c d : ZMod p, κ = [((1 : ℕ) : ZMod p), a, b, c, d]) ∨
        ∃ a b c : ZMod p, κ = [((2 : ℕ) : ZMod p), a, b, c]) →
      keyK 8 (tlF κ) ∈ reqO ++ jCons b nodes orbit chals pubs lay P →
      ∃ r' ∈ rowsJ b nodes orbit chals pubs lay P, κ ∈ provK r' := by
  set reqs := (reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)) with hreqs
  set provs := (jProv b nodes orbit chals pubs lay P ++ provO).map
    (fun q => (liftRec (L := 𝕂′) q.1, algebraMap K 𝕂′ q.2)) with hprovs
  have hts := jet_tagged_sum hsat hbind hinj hn hadj
  have hsum : (reqs.map fun r => (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ r)⁻¹).sum =
      (provs.map fun q => q.2 * (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ q.1)⁻¹).sum := by
    simp only [hreqs, hprovs, List.map_map, Function.comp_def, List.map_append, List.sum_append]
    have e1 := hts
    change (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum +
        ((jCons b nodes orbit chals pubs lay P).map fun c =>
          (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      ((jProv b nodes orbit chals pubs lay P).map fun q =>
          algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum +
        (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum
    rw [e1]
    linear_combination hG
  have hserved := ServeH.served_of_balance (p := p) reqs provs _ _
    (TeleC.den_ne_of_out reqs provs _ _ hout) (ServedJ8.den_prov_ne_of_out reqs provs _ _ hout) hsum
    (by simpa [hreqs] using hcount) hout
  have h1 : (1 : ℕ) < p := by omega
  have h2 : (2 : ℕ) < p := by omega
  have h0 : (0 : ℕ) < p := by omega
  intro κ hshape hκm
  have hmem : liftRec (L := 𝕂′) (keyK (K := K) 8 (tlF κ)) ∈ reqs := List.mem_map_of_mem hκm
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hserved _ hmem)
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  have hkey : q0.1 = keyK 8 (tlF κ) := liftRec_inj hqe
  obtain ⟨hlen, htag⟩ := tlF_shape hshape
  have h7 : q0.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((tlF κ).getD 7 0) := by rw [hkey]; rfl
  have hinjK := (algebraMap (ZMod p) K).injective
  rcases List.mem_append.mp hq0 with hJ | hO
  · obtain ⟨i', -, hq'⟩ := List.mem_flatMap.mp hJ
    rcases List.mem_append.mp hq' with hP | hJet
    · obtain ⟨κ', hκ', rfl⟩ := List.mem_map.mp hP
      rw [provKT_eq] at hκ'
      obtain ⟨κ1, hκ1, rfl⟩ := List.mem_map.mp hκ'
      have hs1 := provK_shape _ κ1 hκ1
      have e := keyK_inj (tlF_shape hs1).1 hlen hkey
      rw [tlF_inj (ne_cast h1 h2 (by norm_num)) hs1 hshape e] at hκ1
      exact ⟨RJ i', List.mem_ofFn.mpr ⟨i', rfl⟩, hκ1⟩
    · obtain ⟨κj, hκj, rfl⟩ := List.mem_map.mp hJet
      exfalso
      have hj7 := (jet_tag _ κj hκj).1
      have e7 : algebraMap (ZMod p) K (κj.getD 7 0) = algebraMap (ZMod p) K ((tlF κ).getD 7 0) := h7
      rw [hj7] at e7
      have e7' := hinjK e7
      rcases htag with ht | ht <;> rw [ht] at e7'
      · exact ne_cast (by omega) h1 (by norm_num) e7'
      · exact ne_cast (by omega) h2 (by norm_num) e7'
  · exfalso
    have := hO7 q0 hO
    rw [h7, show (0 : K) = algebraMap (ZMod p) K ((0 : ℕ) : ZMod p) by simp] at this
    have e7' := hinjK this
    rcases htag with ht | ht <;> rw [ht] at e7'
    · exact ne_cast h1 h0 (by norm_num) e7'
    · exact ne_cast h2 h0 (by norm_num) e7'

/-- **The pins are served**: with the verifier's pin consumes among the other service consumers,
each registered id's pin `(2, id, 1, idx id)` is some row's in-chip provide. -/
theorem pin_served [DecidableEq K] [DecidableEq 𝕂′] [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hO7 : ∀ q ∈ provO, q.1 ⟨7, by norm_num⟩ = 0)
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        ((jProv b nodes orbit chals pubs lay P ++ provO).map
          fun q => (liftRec (L := 𝕂′) q.1, algebraMap K 𝕂′ q.2)))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p)
    {regs : List ℕ} {idx : ℕ → ℕ} (hpin : pinCons (p := p) (K := K) regs idx ⊆ reqO) :
    ∀ id ∈ regs, ∃ r' ∈ rowsJ b nodes orbit chals pubs lay P, pinKey id (idx id) ∈ provK r' := by
  intro id hid
  exact inchip_served hp3 hsat hbind hinj hn hadj reqO provO hO7 hG hout hcount _ (pinKey_shape id (idx id))
    (List.mem_append_left _ (hpin (List.mem_map_of_mem hid)))

end Served

/-! ## 3. The pin forces the registry handle -/

section Forces
variable {p : ℕ} [Fact p.Prime]

/-- With `regs` nodup, the ids of the `.reg` rows of an `Accepted` trace are `regs` itself. -/
theorem reg_filterMap {R : ℕ → Tpl} {regs ids : List ℕ} {rows : List (CRow (ZMod p))}
    (hA : Accepted R regs ids rows) :
    rows.filterMap (fun r : CRow (ZMod p) => if r.pre.kd = .reg then some r.pre.id else none) = regs := by
  have e : rows.filterMap (fun r : CRow (ZMod p) => if r.pre.kd = .reg then some r.pre.id else none) =
      (rows.map CRow.pre).filterMap (fun q : PRow => if q.kd = .reg then some q.id else none) := by
    rw [List.filterMap_map]; rfl
  rw [e, hA.lay, layoutJ8, List.filterMap_append]
  have hb : (blocks R 0 ids).filterMap (fun q : PRow => if q.kd = .reg then some q.id else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro q hq
    simp [(blocks_kd R ids 0 q hq).1]
  rw [hb, List.append_nil, List.filterMap_map]
  have : ((fun q : PRow => if q.kd = .reg then some q.id else none) ∘ regPre) = some := by
    funext i; simp [regPre]
  rw [this, List.filterMap_some]

/-- **A registry row is determined by its id** (public check `regs.Nodup`). -/
theorem reg_unique {R : ℕ → Tpl} {regs ids : List ℕ} {rows : List (CRow (ZMod p))}
    (hA : Accepted R regs ids rows) (hnd : regs.Nodup) {r r' : CRow (ZMod p)} (hr : r ∈ rows)
    (hr' : r' ∈ rows) (hk : r.pre.kd = .reg) (hk' : r'.pre.kd = .reg) (he : r.pre.id = r'.pre.id) :
    r = r' := by
  have hnd' := (reg_filterMap hA).symm ▸ hnd
  exact eq_of_filterMap_nodup _ rows hnd' r hr r' hr' r.pre.id (by simp [hk]) (by simp [hk', he])

/-- **The pin forces the handle**: on an `Accepted` trace whose registry pins `(2, id, 1, idx id)` are
each some row's in-chip provide, with `regs` nodup, every `.reg` row has `(kN, vN) = (1, idx id)`. -/
theorem pin_forces {R : ℕ → Tpl} {regs ids : List ℕ} {rows : List (CRow (ZMod p))}
    (hp3 : 3 < p) (hA : Accepted R regs ids rows) (hnd : regs.Nodup) {idx : ℕ → ℕ}
    (hpin : ∀ id ∈ regs, ∃ r' ∈ rows, pinKey id (idx id) ∈ provK r') :
    ∀ r ∈ rows, r.pre.kd = .reg → r.w.kN = 1 ∧ r.w.vN = ((idx r.pre.id : ℕ) : ZMod p) := by
  intro r hr hk
  have hid : r.pre.id ∈ regs := layout_reg (pre_mem hA hr) hk
  obtain ⟨r', hr', hκ⟩ := hpin _ hid
  have h1 : (1 : ℕ) < p := by omega
  have h2 : (2 : ℕ) < p := by omega
  by_cases hk' : r'.pre.kd = .reg
  · rw [provK_reg r' hk'] at hκ
    simp only [pinKey, List.mem_singleton, List.cons.injEq] at hκ
    obtain ⟨-, hid', hN, hV, -⟩ := hκ
    have hlt : r.pre.id < p := (hA.small _ (pre_mem hA hr)).1
    have hlt' : r'.pre.id < p := (hA.small _ (pre_mem hA hr')).1
    have e := natCast_inj_lt hlt hlt' hid'
    have := reg_unique hA hnd hr hr' hk hk' e
    subst this
    exact ⟨hN.symm, hV.symm⟩
  · rw [provK_eq r' hk'] at hκ
    simp only [pinKey, List.mem_singleton, List.cons.injEq] at hκ
    exact absurd hκ.1 (ne_cast h2 h1 (by norm_num))

/-- **`hReg` from the pin** (G-J1, option (b)): JB's registry binding
`denK (kN, vN) = compile p (R id)` on every `.reg` row of an `Accepted` trace, from
* the J-side pin (`hpin`: each `(2, id, 1, idx id)` provided in-chip; `pin_served`), `regs` nodup and
  `idx id < p` (public checks);
* the cell-side pin (`hclaim`: each claim key `(E (compile p (R id)), rk id, idx id)` provided in the
  two-provider validity balance; `regClaims_provided`); -/
theorem hReg_of_pin (hq : 2 ^ 63 < p) {Kfp : Type} [Field Kfp] [Algebra (ZMod p) Kfp]
    {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms p z E)
    {t : List (CellRow p Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (htab : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext)
    {R : ℕ → Tpl} {regs ids : List ℕ} {rows : List (CRow (ZMod p))}
    (hA : Accepted R regs ids rows) (hnd : regs.Nodup) {idx : ℕ → ℕ} (hidx : ∀ id ∈ regs, idx id < p)
    (hpin : ∀ id ∈ regs, ∃ r' ∈ rows, pinKey id (idx id) ∈ provK r')
    {rk : ℕ → ℕ × ℕ}
    (hclaim : ∀ id ∈ regs,
      (∃ c ∈ t, (E (compile p (R id)), (rk id).1, (rk id).2, idx id) = (c.p, c.b0.hi, c.b0.lo, c.b0.idx)) ∨
        (E (compile p (R id)), (rk id).1, (rk id).2, idx id) ∈ vp)
    (hrk : ∀ id ∈ regs, rk id ≠ (0, 0))
    (hinj : ∀ id ∈ regs, ∀ d ∈ decodedNouns2 (t.map (·.b0)) ext,
      E (compile p (R id)) = E d → compile p (R id) = d) :
    ∀ r ∈ rows, r.pre.kd = .reg →
      denK (t.map (·.b0)) ext (r.w.kN.val, r.w.vN.val) = some (compile p (R r.pre.id)) := by
  have hp3 : 3 < p := by have : (3 : ℕ) < 2 ^ 63 := by norm_num
                         omega
  have hf := pin_forces hp3 hA hnd hpin
  have hreg : ∀ r ∈ rows, r.pre.kd = .reg → r.pre.id ∈ regs := fun r hr hk => layout_reg (pre_mem hA hr) hk
  refine hReg_of_served hq hcons hE htab hvp (R := R) (rk := rk) (rows := rows) ?_ ?_ ?_ ?_
  · intro r hr
    by_cases hk : r.pre.kd = .reg
    · exact regKind_on (hf r hr hk).1
    · exact regKind_off hk
  · intro r hr hk
    have hid := hreg r hr hk
    rw [(hf r hr hk).2, ZMod.val_natCast, Nat.mod_eq_of_lt (hidx _ hid)]
    exact hclaim _ hid
  · intro r hr hk; exact hrk _ (hreg r hr hk)
  · intro r hr hk; exact hinj _ (hreg r hr hk)

end Forces

/-! ## 4. -/

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- `claimVec` is injective. -/
theorem claimVec_inj {e e' : FP 𝕂′} {i hi lo i' hi' lo' : F}
    (hk : ClaimVS.claimVec δF e i hi lo = ClaimVS.claimVec δF e' i' hi' lo') :
    e = e' ∧ i = i' ∧ hi = hi' ∧ lo = lo' := by
  have e0 : e.size = e'.size := congrFun hk 0
  have e1 : e.dyck = e'.dyck := congrFun hk 1
  have e2 : e.leaf = e'.leaf := congrFun hk 2
  have e3 : Quad.mk _ (algebraMap F K lo) (algebraMap F K hi) =
      Quad.mk (algebraMap F K δF) (algebraMap F K lo') (algebraMap F K hi') := congrFun hk 3
  have e4 : Quad.mk _ (algebraMap F K i) 0 = Quad.mk (algebraMap F K δF) (algebraMap F K i') 0 :=
    congrFun hk 4
  rw [Quad.mk_eq_mk_iff] at e3 e4
  refine ⟨?_, (algebraMap F K).injective e4.1, (algebraMap F K).injective e3.2,
    (algebraMap F K).injective e3.1⟩
  obtain ⟨s, d, l⟩ := e
  obtain ⟨s', d', l'⟩ := e'
  simp only at e0 e1 e2
  subst e0 e1 e2
  rfl

variable [Fintype K] [DecidableEq (Quad (algebraMap F K δF))]

/-- **The external consumers of the two-provider validity balance are served** (the `reqs` half of
`TwoProviderQ.cell_child_served2`): each is a cell row's provider key or an external key. -/
theorem claims_served2
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
    ∀ r ∈ reqs,
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
  have := hlook r (List.mem_append_left _ hr)
  rw [List.map_append, List.mem_append, SVFrame.liftWts_fst] at this
  rcases this with h | h
  · obtain ⟨q, hq, hqr⟩ := List.mem_map.mp h
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq
    exact Or.inl ⟨j, hqr⟩
  · exact Or.inr h

variable [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))]

theorem regClaims_provided (hF : GeneratedField.PrimeFieldElems F)
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
    (hvpr : ∀ k ∈ vp, k.2.1 < ringChar F ∧ k.2.2.1 < ringChar F ∧ k.2.2.2 < ringChar F)
    {regs : List ℕ} {Ef : ℕ → FP 𝕂′} {rk : ℕ → ℕ × ℕ} {idx : ℕ → ℕ}
    (hpin : ∀ id ∈ regs, ClaimVS.claimVec δF (Ef id) (idx id : F) ((rk id).1 : F) ((rk id).2 : F) ∈ reqs)
    (hlt : ∀ id ∈ regs, (rk id).1 < ringChar F ∧ (rk id).2 < ringChar F ∧ idx id < ringChar F) :
    ∀ id ∈ regs,
      (∃ c ∈ cellTableOf δF b nodes orbit chals pubs Q,
        (Ef id, (rk id).1, (rk id).2, idx id) = (c.p, c.b0.hi, c.b0.lo, c.b0.idx)) ∨
      (Ef id, (rk id).1, (rk id).2, idx id) ∈ vp := by
  intro id hid
  obtain ⟨l1, l2, l3⟩ := hlt id hid
  rcases claims_served2 δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj γ ρ hok reqs xs hsum hout
      hxne hcount _ (hpin id hid) with ⟨j, hj⟩ | hxs
  · have hv := ClaimVS.claim_decode δF b hn nodes orbit chals pubs Q _ _ _ _ j hj.symm
    rw [natOf_natCast hF l1, natOf_natCast hF l2, natOf_natCast hF l3] at hv
    exact Or.inl hv
  · obtain ⟨x, hx', hxe⟩ := List.mem_map.mp hxs
    obtain ⟨k, hk, hkx⟩ := hx x hx'
    rw [hkx] at hxe
    obtain ⟨hfp, hi, hhi, hlo⟩ := claimVec_inj δF hxe
    obtain ⟨r1, r2, r3⟩ := hvpr k hk
    have a1 : k.2.1 = (rk id).1 := by rw [← natOf_natCast hF r1, hhi, natOf_natCast hF l1]
    have a2 : k.2.2.1 = (rk id).2 := by rw [← natOf_natCast hF r2, hlo, natOf_natCast hF l2]
    have a3 : k.2.2.2 = idx id := by rw [← natOf_natCast hF r3, hi, natOf_natCast hF l3]
    have hkeq : k = (Ef id, (rk id).1, (rk id).2, idx id) := Prod.ext hfp (Prod.ext a1 (Prod.ext a2 a3))
    rw [← hkeq]
    exact Or.inr hk

end Cell

end

end Nock.Jet.PinJ8
