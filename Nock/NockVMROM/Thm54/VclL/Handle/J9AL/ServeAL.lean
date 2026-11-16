/-

  * **`served_JAL`**: from the J chip's tagged balance with the other providers `provO` (the S8 share `hG`, the
    effective IO event `hout`, the count `hcount`; exactly `SubJ9A.inchip_servedE9`'s premises, without `hO7J`),
    every consumed key of `reqO` is the key of a J provide or of an other provide (`jProv ++ provO`).  The proof is
    the first half of `inchip_servedE9` (Lean twin: `served_effective` on the lifted lists, then `liftRec_inj`).
  * `jProv_tag`: a J provide's entry `7` is `1`, `2` or `3` (the in-chip tags and `TAG_jet`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.SubJ9A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ServeAL

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

section Eff
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "JP" => jProv b nodes orbit chals pubs lay P

/-- **ONE served lemma over the J and the other provides** (the `served_of_balance` half of
`SubJ9A.inchip_servedE9`, at the effective providers, without any tag hypothesis on `provO`). -/
theorem served_JAL [CharP 𝕂′ p]
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (reqO : List (Fin 8 → K)) (provO : List ((Fin 8 → K) × K))
    (hG : Quad.mk _ (pubs 0) (pubs 1) +
        (reqO.map fun c => (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (provO.map fun q => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum)
    (hout : ((coinsJ δ chals).gamma, (coinsJ δ chals).pole) ∉
      IOFailureEventW ((reqO ++ jCons b nodes orbit chals pubs lay P).map (liftRec (L := 𝕂′)))
        (effP (liftS (δ := δ) (JP ++ provO))))
    (hcount : (reqO ++ jCons b nodes orbit chals pubs lay P).length < p) :
    ∀ c ∈ reqO, c ∈ (JP ++ provO).map Prod.fst := by
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
  intro c hc
  have hmem : liftRec (L := 𝕂′) c ∈ reqs := List.mem_map_of_mem (List.mem_append_left _ hc)
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hserved _ hmem)
  rw [hprovs, liftS] at hq
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨q0, hq0, liftRec_inj hqe⟩

/-- **A J provide's entry `7` is an in-chip tag `1`, `2` or `TAG_jet = 3`.** -/
theorem jProv_tag : ∀ q ∈ JP, q.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((1 : ℕ) : ZMod p) ∨
    q.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((2 : ℕ) : ZMod p) ∨
    q.1 ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((3 : ℕ) : ZMod p) := by
  intro q hq
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq
  rcases List.mem_append.mp hi with h1 | h1
  · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp h1
    rw [provKT_eq] at hκ
    obtain ⟨κ1, hκ1, rfl⟩ := List.mem_map.mp hκ
    obtain ⟨-, htag⟩ := tlF_shape (provK_shape _ κ1 hκ1)
    rcases htag with ht | ht
    · left; simp only [keyK]; rw [ht]
    · right; left; simp only [keyK]; rw [ht]
  · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp h1
    obtain ⟨h7, -, -, -⟩ := jet_tag _ κ hκ
    right; right; simp only [keyK]; rw [h7]

end Eff

end

end Nock.NockVMROM.Thm54.VclL.Handle.ServeAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ServeAL
#print axioms served_JAL
#print axioms jProv_tag
end Axioms
