/-
  Nock/NockVMROM/Thm54/VclL/Handle/ProvXJ8.lean

  **Card J-8a part 5, step 3 (kind `x`) : `ProvOK` at the cell export balance from
  `exportHKW_genuine`.**  New module, additive.

  The cell export providers of the wire-key twin (`CellTwinKW.cellProvsW`, field `ZMod p`) satisfy the
  compute's provider obligation `ServedJ8.ProvOK` at `Bal.x` with the denotation `D := denK tb ext` (the
  two-provider decode of the accepted cell table, kinds `0 / 1 / 2`): every 5-entry `ℕ` record whose key a
  row provides is `Cell3 D (1, idx) (hK L) (hK R)`, i.e. `RowSemChipX.RecOK` at `x`.
  * `exportRecK_lt`: the entries of a decoded row's wire export record are `< p` (`natOf`, kinds `≤ 2`);
  * `natKey_inj5`: `natKey 5` is injective on 5-entry records with entries `< p`;
  * **`provOK_x`**: `ProvOK (denK tb ext) R limbA.x (cellProvsW …)` under the hypotheses of
    `exportHKW_genuine` (the two-provider validity balance outside its IO event, atom-root external keys,
    `AtomLeaves`, the encoder facts).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW
import Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ProvXJ8

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (natKey mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP ProvOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

section Keys
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]

/-- **`natKey 5` is injective on records with entries `< p`.** -/
theorem natKey_inj5 {a b : List ℕ} (ha : a.length = 5) (hb : b.length = 5) (hal : ∀ e ∈ a, e < p)
    (hbl : ∀ e ∈ b, e < p) (h : (natKey (p := p) (K := K) 5 a) = natKey (p := p) (K := K) 5 b) : a = b := by
  apply List.ext_getElem (ha.trans hb.symm)
  intro j hja hjb
  have hj5 : j < 5 := ha ▸ hja
  have e := congrFun h ⟨j, hj5⟩
  simp only [natKey] at e
  have e' := (algebraMap (ZMod p) K).injective e
  rw [List.getD_eq_getElem _ _ hja, List.getD_eq_getElem _ _ hjb] at e'
  have h1 := hal _ (List.getElem_mem hja)
  have h2 := hbl _ (List.getElem_mem hjb)
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at e'
  exact e'

end Keys

section ProvX
variable {p : ℕ} [hpF : Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))]
  (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δF)

theorem ringChar_zmod : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p

/-- The entries of a decoded row's wire export record are `< p`. -/
theorem exportRecK_lt (hp2 : 2 < p) (eF : Env (ZMod p)) :
    ∀ e ∈ [(cellB0Of eF).idx, (hK (cellB0Of eF) .L).1, (hK (cellB0Of eF) .L).2,
      (hK (cellB0Of eF) .R).1, (hK (cellB0Of eF) .R).2], e < p := by
  have hn : ∀ x : ZMod p, natOf x < p := fun x => by
    have := natOf_lt (GeneratedField.primeFieldElems_zmod p) x
    rwa [ringChar_zmod] at this
  have hk : ∀ s, kindS (cellB0Of eF) s < p := by
    intro s; unfold kindS; split_ifs <;> omega
  have hv : ∀ s, (hK (cellB0Of eF) s).2 < p := by
    intro s
    simp only [hK]
    split_ifs
    · cases s <;> simp [CellRowB0.idS, cellB0Of, hn]
    · haveI : NeZero (ringChar (ZMod p)) := ⟨by rw [ringChar_zmod]; exact hpF.out.ne_zero⟩
      exact lt_of_lt_of_eq (ZMod.val_lt ((cellB0Of eF).aS s)) ringChar_zmod
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact hn _
  · exact hk _
  · exact hv _
  · exact hk _
  · exact hv _

end ProvX

section ProvXThm
variable {p : ℕ} [hpF : Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))]
  (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  [Fintype K] [DecidableEq (Quad (algebraMap (ZMod p) K δF))]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δF))] [Fact (ringChar (ZMod p)).Prime]
  [CharP (Quad (algebraMap (ZMod p) K δF)) p]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δF)

/-- **`ProvOK` at the cell export balance `x`**: every 5-entry record whose key a `cellChipHQKW` row provides
is `Cell3 (denK tb ext) (1, idx) (hK L) (hK R)` — `RecOK` at `x` — under the hypotheses of
`exportHKW_genuine`. -/
theorem provOK_x (hp2 : 2 < p) (hq : 2 ^ 63 < ringChar (ZMod p))
    (hz : Quad.mk (algebraMap (ZMod p) K δF) (chals 2) (chals 3) ≠ 0)
    (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])
    (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChipHQKW δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar (ZMod p))
    (γ ρ : 𝕂′) (hok : ChalsOK δF chals γ ρ 11)
    (reqs : List (Fin 5 → 𝕂′)) (xs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum =
      Quad.mk _ (pubs 0) (pubs 1) + (xs.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1)⁻¹).sum)
    (hout : (γ, ρ) ∉ FiniteIO.IOFailureEventW
      (reqs ++ cellVInternal δF b hn nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q))
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs
        (restrictHQKWCell δF b hn nodes orbit chals pubs Q)) ++ xs))
    (hxne : ∀ x ∈ xs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1 ≠ 0)
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs
      (restrictHQKWCell δF b hn nodes orbit chals pubs Q)).length < p)
    (vp : List (VKey 𝕂′))
    (hx : ∀ x ∈ xs, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δF k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p))
    (E : Noun → FP 𝕂′)
    (hcons : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap (ZMod p) K δF) (chals 2) (chals 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δF) (chals 2) (chals 3)) E)
    (ext : ℕ → Option Noun) (hvp : AtomLeaves E vp ext)
    (R : Nock.Jet.Registry) (limbA : ℕ → ℕ → ℕ × ℕ) :
    ProvOK (p := p) (K := K)
      (denK ((cellTableOf δF b nodes orbit chals pubs
        (restrictHQKWCell δF b hn nodes orbit chals pubs Q)).map (·.b0)) ext) R limbA Bal.x
      (cellProvsW b nodes orbit chals pubs Q) := by
  intro q hqm l hlen hlt hkey
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hqm
  obtain ⟨hk, -, L, R', h1, h2, h3⟩ := exportHKW_genuine δF b hn nodes orbit chals pubs
    (GeneratedField.primeFieldElems_zmod p) hq hz Q hsat hbind hinj hadj hnp γ ρ hok reqs xs hsum hout hxne
    hcount vp hx hvp0 E hcons hE ext hvp i
  simp only [keyHK, recFK, exportRecK, List.map_cons, List.map_nil, List.cons.injEq] at hk
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := hk
  have hkr : ServeH.keyVec5 (keyHK (F := ZMod p)) (hqkEF b nodes orbit chals pubs Q i) =
      natKey (p := p) (K := K) 5 [(cellB0Of (hqkEF b nodes orbit chals pubs Q i)).idx,
        (hK (cellB0Of (hqkEF b nodes orbit chals pubs Q i)) .L).1,
        (hK (cellB0Of (hqkEF b nodes orbit chals pubs Q i)) .L).2,
        (hK (cellB0Of (hqkEF b nodes orbit chals pubs Q i)) .R).1,
        (hK (cellB0Of (hqkEF b nodes orbit chals pubs Q i)) .R).2] := by
    funext j
    fin_cases j
    · exact congrArg (algebraMap (ZMod p) K) e0
    · exact congrArg (algebraMap (ZMod p) K) e1
    · exact congrArg (algebraMap (ZMod p) K) e2
    · exact congrArg (algebraMap (ZMod p) K) e3
    · exact congrArg (algebraMap (ZMod p) K) e4
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, t⟩⟩⟩⟩⟩⟩
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · have hl := natKey_inj5 (p := p) (K := K) rfl rfl hlt (exportRecK_lt hp2 _) (hkey.trans hkr)
    rw [hl]
    exact ⟨L, R', h1, h2, h3⟩
  · simp only [List.length_cons, mOf] at hlen; omega

end ProvXThm

end

end Nock.NockVMROM.Thm54.VclL.Handle.ProvXJ8
