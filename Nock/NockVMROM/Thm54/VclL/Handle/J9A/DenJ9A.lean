/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/DenJ9A.lean

* `denJ9A t p rA V`: kinds `0, 1, 2` as J-9 B's `denK t (extB p rA)`; kind `3` (the segment handle
    `(3, 64·id + m)`) reads `segD (V id) m`.
  * `denOK9_denJ9A`: `DenOKX9 p (denJ9A t p rA V) V` from three facts on `V` alone (`k2`: big rows read through
    `V`; `vpos`; `idlt`, the A0 Q1 per-row id bound: every id with a value has `64·id + 64 ≤ p`).
  * At `V = valId nA rA sv`: `k2` from the `hden2` fact (a big denoted row is an atom-table row `< nA`); `vpos`
    from `TopNZ` (`B ≤ val l`) and the split side's `hi ≠ 0`; `idlt` from `sv` vanishing past `nS` and
    `64·(nA + nS) ≤ p` (`hnAS`, A0 Q1: an id is defined only below `nA + nS`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.LocalVSX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.NounAx
import Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesBJ8
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ProvNewX9
import Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.DenJ9A

open Nock Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX Cell3)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 (DenOKX9)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (TopNZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA extA_of_denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB extB_big denOKX_extB extA_some)
open Nock.J9A.NounAx (valId segD valId_of_denotes valId_of_lt valId_of_ge atomOf)
open Nock.Atoms (val B)

noncomputable section

/-- **The J-9 A denotation.** -/
def denJ9A {q : ℕ} (t : List (CellRowB0 q)) (p : ℕ) (rA : ℕ → ARow) (V : ℕ → Option ℕ) : HX → Option Noun :=
  fun k => if k.1 = 3 then ((V (k.2 / 64)).bind fun n => segD n (k.2 % 64)).map Noun.atom
    else denK t (extB p rA) k

theorem denJ9A_ne3 {q : ℕ} (t : List (CellRowB0 q)) (p : ℕ) (rA : ℕ → ARow) (V : ℕ → Option ℕ) {k : HX}
    (hk : k.1 ≠ 3) : denJ9A t p rA V k = denK t (extB p rA) k := if_neg hk

/-- **`DenOKX9` at `denJ9A`**, from `k2` / `vpos` / `idlt` on `V`. -/
theorem denOK9_denJ9A {q : ℕ} (t : List (CellRowB0 q)) (p : ℕ) (rA : ℕ → ARow) (V : ℕ → Option ℕ)
    (hk2 : ∀ i n, extB p rA i = some (.atom n) → V i = some n)
    (hvpos : ∀ i n, V i = some n → n ≠ 0) (hidlt : ∀ i n, V i = some n → 64 * i + 64 ≤ p) :
    DenOKX9 p (denJ9A t p rA V) V where
  base :=
    { atom := fun v => by rw [denJ9A_ne3 t p rA V (by simp)]; exact (denOKX_extB t p rA).atom v
      cell := fun i X h => by
        rw [denJ9A_ne3 t p rA V (by simp)] at h; exact (denOKX_extB t p rA).cell i X h
      big := fun i X h => by
        rw [denJ9A_ne3 t p rA V (by simp)] at h; exact (denOKX_extB t p rA).big i X h }
  seg := fun i m hm => by
    have h1 : (64 * i + m) / 64 = i := by omega
    have h2 : (64 * i + m) % 64 = m := by omega
    simp only [denJ9A, h1, h2, if_true, ite_true]
  k2 := fun i n h => by
    rw [denJ9A_ne3 t p rA V (by simp)] at h; exact hk2 i n h
  vpos := hvpos
  idlt := hidlt

/-! ## At `V = valId nA rA sv` -/

section ValId
variable {nA : ℕ} {rA : ℕ → ARow} {sv : ℕ → Option ℕ}

/-- `k2`: a big denoted row lies in the atom table, where `valId` reads `extA`. -/
theorem k2_valId {p : ℕ} (hden2 : ∀ j l, Denotes rA j l → p ≤ val l → j < nA) :
    ∀ i n, extB p rA i = some (.atom n) → valId nA rA sv i = some n := by
  classical
  intro i n h
  unfold extB at h
  split_ifs at h with he
  obtain ⟨hd, hq⟩ := Classical.choose_spec he
  rw [valId_of_denotes (hden2 _ _ hd hq) hd]
  have := Option.some.inj h
  cases this
  rfl

/-- `vpos`: a defined `valId` is nonzero (`TopNZ`: a denoted value is `≥ B`; the split side nonzero). -/
theorem vpos_valId (hT : TopNZ rA) (hsv : ∀ s n, sv s = some n → n ≠ 0) :
    ∀ i n, valId nA rA sv i = some n → n ≠ 0 := by
  intro i n h
  rcases Nat.lt_or_ge i nA with hi | hi
  · rw [valId_of_lt hi] at h
    rcases he : extA rA i with _ | X
    · rw [he] at h; simp at h
    · rw [he] at h
      obtain ⟨l, hd, rfl⟩ := extA_some he
      simp only [Option.bind_some, atomOf, Option.some.injEq] at h
      subst h
      have := AtomLeavesBJ8.B_le_val hT hd
      have hB : 0 < B := by norm_num [B]
      omega
  · rw [valId_of_ge hi] at h
    exact hsv _ _ h

/-- `idlt` (A0 Q1): an id with a value is below `nA + nS`, so `64·id + 64 ≤ 64·(nA + nS) ≤ p`. -/
theorem idlt_valId {p nS : ℕ} (hsvn : ∀ s n, sv s = some n → s < nS) (hnAS : 64 * (nA + nS) ≤ p) :
    ∀ i n, valId nA rA sv i = some n → 64 * i + 64 ≤ p := by
  intro i n h
  rcases Nat.lt_or_ge i nA with hi | hi
  · omega
  · rw [valId_of_ge hi] at h
    have := hsvn _ _ h
    omega

/-- **`DenOKX9` at `denJ9A t p rA (valId nA rA sv)`** (obligation 1). -/
theorem denOK9_valId {q : ℕ} (t : List (CellRowB0 q)) (p nS : ℕ)
    (hden2 : ∀ j l, Denotes rA j l → p ≤ val l → j < nA) (hT : TopNZ rA)
    (hsv0 : ∀ s n, sv s = some n → n ≠ 0) (hsvn : ∀ s n, sv s = some n → s < nS)
    (hnAS : 64 * (nA + nS) ≤ p) :
    DenOKX9 p (denJ9A t p rA (valId nA rA sv)) (valId nA rA sv) :=
  denOK9_denJ9A t p rA _ (k2_valId hden2) (vpos_valId hT hsv0) (idlt_valId hsvn hnAS)

end ValId

#print axioms denOK9_denJ9A
#print axioms denOK9_valId

/-! ## The split side: `sv = splitSV` -/

section Split
open Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9 (splitChipJ9 spEF sp_rowEqs sp_limbs splitValN)
open Nock.NockVMROM.Thm54.VclL.Handle.ProvNewX9 (splitSV)
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))] (nA : ℕ)
  (b : Module.Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

theorem splitSV_lt : ∀ s v, splitSV δF nA b hn nodes orbit chals pubs Q s = some v → s < n := by
  intro s v hs
  unfold splitSV at hs
  split_ifs at hs with h1
  · exact h1

theorem splitSV_ne0 (hp : 2 ^ 32 < p) (hsat : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ s v, splitSV δF nA b hn nodes orbit chals pubs Q s = some v → v ≠ 0 := by
  intro s v hs
  unfold splitSV at hs
  split_ifs at hs with h1
  have hv := (Option.some.inj hs).symm
  subst hv
  obtain ⟨-, -, hnz⟩ := sp_limbs hp (sp_rowEqs δF nA b hn nodes orbit chals pubs Q hsat ⟨s, h1⟩)
  unfold splitValN
  have : 1 ≤ ((spEF b nodes orbit chals pubs Q ⟨s, h1⟩).trace SplitChipJ9.hi).val := Nat.one_le_iff_ne_zero.mpr hnz
  have h2 : 0 < 2 ^ 32 := by norm_num
  positivity

/-- **`DenOKX9` at the J-9 A denotation with `V = valId nA rA (splitSV …)`** (obligation 1, the LINK instance). -/
theorem denOK9_split {q : ℕ} (t : List (CellRowB0 q)) {rA : ℕ → ARow} (hp : 2 ^ 32 < p)
    (hsat : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hden2 : ∀ j l, Denotes rA j l → p ≤ val l → j < nA) (hT : TopNZ rA) (hnAS : 64 * (nA + n) ≤ p) :
    DenOKX9 p (denJ9A t p rA (valId nA rA (splitSV δF nA b hn nodes orbit chals pubs Q)))
      (valId nA rA (splitSV δF nA b hn nodes orbit chals pubs Q)) :=
  denOK9_valId t p n hden2 hT (splitSV_ne0 δF nA b hn nodes orbit chals pubs Q hp hsat)
    (splitSV_lt δF nA b hn nodes orbit chals pubs Q) hnAS

end Split

#print axioms denOK9_split

/-! ## Transfer of the J-8 obligations from `denK` to `denJ9A` (class `0`) -/

section Transfer
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9 RecOK9I recClass PreI9)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8 (RecOKI PreI PreS)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8 (RecOKA IsWalkA)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)

/-- **The kinds a class-`0` record names are not the segment kind `3`.** -/
def KindsOK : List ℕ × Bal → Prop
  | ([_, lk, _, rk, _], .x) => lk ≠ 3 ∧ rk ≠ 3
  | ([_, _, ck, _], .p) => ck ≠ 3
  | ([ok, _, nk, _, 4], .s) => ok ≠ 3 ∧ nk ≠ 3
  | ([_, ck, _, sk, _, ek, _, 3], .s) => ck ≠ 3 ∧ sk ≠ 3 ∧ ek ≠ 3
  | _ => True

variable {D D' : HX → Option Noun} (hag : ∀ k : HX, k.1 ≠ 3 → D' k = D k)
include hag

theorem cell3_transfer {a b c : HX} (ha : a.1 ≠ 3) (hb : b.1 ≠ 3) (hc : c.1 ≠ 3) (h : Cell3 D a b c) :
    Cell3 D' a b c := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨A, B, by rw [hag a ha]; exact h1, by rw [hag b hb]; exact h2, by rw [hag c hc]; exact h3⟩

/-- `RecOK` transfers along an agreement off kind `3`, on records whose kinds are not `3`. -/
theorem recOK_transfer {R : Nock.Jet.Registry} {lA : ℕ → ℕ → HX} (r : List ℕ × Bal) (hk : KindsOK r)
    (h : RecOK D R lA r) : RecOK D' R lA r := by
  unfold RecOK at h ⊢
  split
  next pv lk lv rk rv => exact cell3_transfer hag (by simp) hk.1 hk.2 h
  next rv ax ck cv =>
    obtain ⟨Rt, C, h1, h2, h3⟩ := h
    exact ⟨Rt, C, by rw [hag _ (by simp)]; exact h1, by rw [hag (ck, cv) (show ck ≠ 3 from hk)]; exact h2, h3⟩
  next rv ax lk lv =>
    obtain ⟨n, h1, h2⟩ := h
    exact ⟨n, by rw [hag _ (by simp)]; exact h1, h2⟩
  next ok ov nk nv =>
    obtain ⟨n, h1, h2⟩ := h
    exact ⟨n, by rw [hag _ hk.1]; exact h1, by rw [hag _ hk.2]; exact h2⟩
  next id ck cv sk sv ek ev =>
    obtain ⟨j, h0, h1, S, E, h2, h3, h4⟩ := h
    exact ⟨j, h0, by rw [hag _ hk.1]; exact h1, S, E, by rw [hag _ hk.2.1]; exact h2,
      by rw [hag _ hk.2.2]; exact h3, h4⟩
  next => trivial

/-- `PreI` transfers back (the antecedent on `D'` gives it on `D`) on class-`0` records whose kinds are not `3`. -/
theorem preI_back (r : List ℕ × Bal) (hk : KindsOK r) (hc : recClass r = 0) (h : PreI D' r) : PreI D r := by
  obtain ⟨l, bl⟩ := r
  unfold PreI at h ⊢
  by_cases hs : bl = .s
  · subst hs
    simp only [if_true] at h ⊢
    unfold PreS at h ⊢
    split
    next ok ov a b =>
      have ho3 : ok ≠ 3 := hk.1
      rw [← hag (ok, ov) ho3]; exact h
    next rv a b c => simp [recClass] at hc
    next a b c sk sv d e =>
      have hs3 : sk ≠ 3 := hk.2.1
      rw [← hag (sk, sv) hs3]
      revert h
      rcases sv with _ | _ | _ | _ | _ | sv <;> intro h <;> exact h
    next => trivial
  · simp only [hs, if_false]

/-- **`recOK9I_of_I`**: a J-9 B class-`0` obligation `RecOKI D` gives `RecOK9I D'` (`D'` agreeing with `D` off
kind `3`), on records whose kinds are not `3`. -/
theorem recOK9I_of_I {V : ℕ → Option ℕ} {R : Nock.Jet.Registry} (r : List ℕ × Bal) (hc : recClass r = 0)
    (hk : KindsOK r) (h : RecOKI D R combN r) : RecOK9I D' V R combN r := by
  intro hpre
  have hp := preI_back hag r hk hc (hpre hc)
  have ha := h hp
  have hw : ¬ IsWalkA r := by
    obtain ⟨l, bl⟩ := r
    rintro ⟨hs, h4⟩
    simp only at hs h4
    subst hs
    simp [recClass, h4] at hc
  unfold RecOKA at ha
  rw [if_neg hw] at ha
  unfold RecOK9
  rw [hc, if_neg (by omega), if_neg (by omega)]
  exact recOK_transfer hag r hk ha

end Transfer

#print axioms recOK9I_of_I

/-- **The `hden2` fact at the reader**: rows past the table pad to `⟨k, 0, 0, 0, 1, …⟩`, which denotes `[0, 1]` of value
`B < p`; so a big denoted row lies in the table. -/
theorem hden2_valReader {p n : ℕ} [Fact p.Prime] (e : Fin n → Nock.Reified.Env (ZMod p))
    (hB : B < p) : ∀ j l, Denotes (LinkQ2J8.valReader e) j l → p ≤ val l → j < n := by
  intro j l hd hq
  by_contra hj
  have hr : LinkQ2J8.valReader e j = ⟨j, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩ := by
    unfold LinkQ2J8.valReader; rw [dif_neg hj]
  cases hd with
  | top hw =>
    rw [hr] at hq
    simp only [val, Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero, zero_add, mul_one] at hq
    omega
  | step hw _ =>
    rw [hr] at hw
    simp at hw

#print axioms hden2_valReader

end

end Nock.NockVMROM.Thm54.VclL.Handle.DenJ9A
