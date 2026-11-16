/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/SubJ9A.lean

  Proof text otherwise verbatim. -/
import Nock.Jet.SubJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.SubJ9A

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8
open Nock.Jet.RegJ8R Nock.Jet.PinJ8 Nock.Jet.FibreJ8 Nock.Jet.SubJ8
open Nock.Framework Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Module
open scoped Polynomial

noncomputable section

/-- **Entry `7` is not an in-chip J tag.** -/
def NotJ7 {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (v : Fin 8 → K) : Prop :=
  v ⟨7, by norm_num⟩ ≠ algebraMap (ZMod p) K ((1 : ℕ) : ZMod p) ∧
    v ⟨7, by norm_num⟩ ≠ algebraMap (ZMod p) K ((2 : ℕ) : ZMod p)

theorem notJ7_of_tag {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {t : ℕ} (ht : t < p)
    (h1 : t ≠ 1) (h2 : t ≠ 2) (hp2 : 2 < p) {v : Fin 8 → K}
    (hv : v ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((t : ℕ) : ZMod p)) : NotJ7 (p := p) v := by
  have e1 := ne_cast ht (by omega : 1 < p) h1
  have e2 := ne_cast ht hp2 h2
  refine ⟨?_, ?_⟩ <;> rw [hv] <;> intro e
  · exact e1 ((algebraMap (ZMod p) K).injective e)
  · exact e2 ((algebraMap (ZMod p) K).injective e)

theorem notJ7_of_zero {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (hp2 : 2 < p)
    {v : Fin 8 → K} (hv : v ⟨7, by norm_num⟩ = 0) : NotJ7 (p := p) v :=
  notJ7_of_tag (t := 0) (by omega) (by norm_num) (by norm_num) hp2 (by rw [hv]; simp)

section Eff
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "RJ" => rowJ b nodes orbit chals pubs lay P
local notation "JP" => jProv b nodes orbit chals pubs lay P

/-- **`SubJ8.inchip_servedE` with `hO7J`** (proof verbatim; the last case reads `hO7J`). -/
theorem inchip_servedE9 [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hO7J : ∀ q ∈ provO, NotJ7 (p := p) q.1)
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        (effP (liftS (δ := δ) (JP ++ provO))))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p) :
    ∀ κ : List (ZMod p), ((∃ a b c d : ZMod p, κ = [((1 : ℕ) : ZMod p), a, b, c, d]) ∨
        ∃ a b c : ZMod p, κ = [((2 : ℕ) : ZMod p), a, b, c]) →
      keyK 8 (tlF κ) ∈ reqO ++ jCons b nodes orbit chals pubs lay P →
      ∃ r' ∈ rowsJ b nodes orbit chals pubs lay P, κ ∈ provK r' := by
  set reqs := (reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)) with hreqs
  set provs := liftS (δ := δ) (JP ++ provO) with hprovs
  have hts := jet_tagged_sum hsat hbind hinj hn hadj
  have hsum : (reqs.map fun r => (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ r)⁻¹).sum =
      (provs.map fun q => q.2 * (compress ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩ q.1)⁻¹).sum := by
    simp only [hreqs, hprovs, liftS, List.map_map, Function.comp_def, List.map_append, List.sum_append]
    have e1 := hts
    change (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum +
        ((jCons b nodes orbit chals pubs lay P).map fun c =>
          (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      ((jProv b nodes orbit chals pubs lay P).map fun q =>
          algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum +
        (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum
    rw [e1]
    linear_combination hG
  have hout' := hout
  rw [mem_IOFailureEventW_iff] at hout'
  push Not at hout'
  have hserved : ∀ r ∈ reqs, r ∈ provs.map Prod.fst := by
    intro r hr
    have := served_effective (p := p) reqs provs ⟨(coinsJ δ chals).gamma, (coinsJ δ chals).pole⟩
      (TeleC.den_ne_of_out reqs (effP provs) _ _ hout) (ServedJ8.den_prov_ne_of_out reqs (effP provs) _ _ hout)
      hsum (by simpa [hreqs] using hcount) hout'.1 hout'.2.2 r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp this
    exact List.mem_map_of_mem (List.mem_of_mem_filter hq)
  have h1 : (1 : ℕ) < p := by omega
  have h2 : (2 : ℕ) < p := by omega
  have h0 : (0 : ℕ) < p := by omega
  intro κ hshape hκm
  have hmem : liftRec (L := 𝕂′) (keyK (K := K) 8 (tlF κ)) ∈ reqs := List.mem_map_of_mem hκm
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hserved _ hmem)
  rw [hprovs, liftS] at hq
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
    obtain ⟨n1, n2⟩ := hO7J q0 hO
    rw [h7] at n1 n2
    rcases htag with ht | ht
    · rw [ht] at n1; exact n1 rfl
    · rw [ht] at n2; exact n2 rfl

/-- **`SubJ8.bal_of_serviceE` with `hO7J`.** -/
theorem bal_of_serviceE9 [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hO7J : ∀ q ∈ provO, NotJ7 (p := p) q.1)
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        (effP (liftS (δ := δ) (JP ++ provO))))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p) :
    ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, ∀ κ ∈ consK r,
      ∃ r' ∈ rowsJ b nodes orbit chals pubs lay P, κ ∈ provK r' := by
  intro r hr κ hκ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  refine inchip_servedE9 hp3 hsat hbind hinj hn hadj reqO provO hO7J hG hout hcount κ (consK_shape _ κ hκ)
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩))
  have : tlF κ ∈ consKT (RJ i) := by rw [consKT_eq]; exact List.mem_map_of_mem hκ
  exact List.mem_map_of_mem this

/-- **`SubJ8.pin_servedE` with `hO7J`.** -/
theorem pin_servedE9 [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hO7J : ∀ q ∈ provO, NotJ7 (p := p) q.1)
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        (effP (liftS (δ := δ) (JP ++ provO))))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p)
    {regs : List ℕ} {idx : ℕ → ℕ} (hpin : pinCons (p := p) (K := K) regs idx ⊆ reqO) :
    ∀ id ∈ regs, ∃ r' ∈ rowsJ b nodes orbit chals pubs lay P, pinKey id (idx id) ∈ provK r' := by
  intro id hid
  exact inchip_servedE9 hp3 hsat hbind hinj hn hadj reqO provO hO7J hG hout hcount _ (pinKey_shape id (idx id))
    (List.mem_append_left _ (hpin (List.mem_map_of_mem hid)))

end Eff

end

end Nock.NockVMROM.Thm54.VclL.Handle.SubJ9A

open Nock.NockVMROM.Thm54.VclL.Handle.SubJ9A in
#print axioms bal_of_serviceE9
open Nock.NockVMROM.Thm54.VclL.Handle.SubJ9A in
#print axioms pin_servedE9
