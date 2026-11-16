/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ProvKindsX9.lean

* §1 Transfer: `denK (3, v) = none`, so every `D`-lookup a `RecOK` fact makes is off kind `3`
    (`recOK_transfer3`): the NON-implication obligations (cell `.x`, walk `.p`, `hReg`) transfer with no kind
    lemma at all (`provP9I_off`, `hReg_transfer3`).
  * §2 The implication-form obligations (inc OLD handle, jet SUBJECT) are NOT transferred: their J-9 B lemmas
    (`ChainUJ8.atomInc_provOKIU`, `JetProvIJ8.jetProvOKI`) are generic in `D` and are applied at `D' = denJ9A`
    directly (hypotheses on kinds `0`, `2` and `DenOKX` only).
  * §3 Class `0`: a provider key with entry `7 ≠ 5` and some entry `≥ 4` nonzero decodes only to class-`0`
    records (`cls0_of_key`), so `RecOKI` / the pre-form becomes `RecOK9I` (`provP9I_of_I`, `provP9I_of_pre`).
    Inc keys: entry `4` = `TAG_inc = 4`, entry `7 = 0`; jet keys: entry `7 ∈ {1, 2, 3}`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.DenJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.ChainUJ8
import Nock.NockVMROM.Thm54.VclL.Handle.JetProvIJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ProvKindsX9

open Nock Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX Cell3)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9 RecOK9I recClass PreI9)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8 (RecOKI PreI PreS)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8 (RecOKA IsWalkA recOK_congr recOKA_iff_off)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP ProvOK)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf padK natKey)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open scoped Polynomial
open Module

noncomputable section

/-! ## 1. Transfer off kind `3` -/

theorem denK_three {q : ℕ} (t : List (CellRowB0 q)) (e : ℕ → Option Noun) (v : ℕ) : denK t e (3, v) = none := rfl

section Transfer
variable {D D' : HX → Option Noun} (hD3 : ∀ v, D (3, v) = none) (hag : ∀ k : HX, k.1 ≠ 3 → D' k = D k)
include hD3 hag

theorem agree_some {k : HX} {X : Noun} (h : D k = some X) : D' k = some X := by
  have hk : k.1 ≠ 3 := by
    obtain ⟨a, v⟩ := k
    rintro (rfl : a = 3)
    rw [hD3] at h
    cases h
  rw [hag k hk]; exact h

/-- **`RecOK` transfers to any `D'` agreeing off kind `3`** when `D` has no kind `3`. -/
theorem recOK_transfer3 {R : Nock.Jet.Registry} {lA : ℕ → ℕ → HX} (r : List ℕ × Bal) (h : RecOK D R lA r) :
    RecOK D' R lA r := by
  unfold RecOK at h ⊢
  split
  next pv lk lv rk rv =>
    obtain ⟨A, B, h1, h2, h3⟩ := h
    exact ⟨A, B, agree_some hD3 hag h1, agree_some hD3 hag h2, agree_some hD3 hag h3⟩
  next rv ax ck cv =>
    obtain ⟨Rt, C, h1, h2, h3⟩ := h
    exact ⟨Rt, C, agree_some hD3 hag h1, agree_some hD3 hag h2, h3⟩
  next rv ax lk lv =>
    obtain ⟨n, h1, h2⟩ := h
    exact ⟨n, agree_some hD3 hag h1, h2⟩
  next ok ov nk nv =>
    obtain ⟨n, h1, h2⟩ := h
    exact ⟨n, agree_some hD3 hag h1, agree_some hD3 hag h2⟩
  next id ck cv sk sv ek ev =>
    obtain ⟨j, h0, h1, S, E, h2, h3, h4⟩ := h
    exact ⟨j, h0, agree_some hD3 hag h1, S, E, agree_some hD3 hag h2, agree_some hD3 hag h3, h4⟩
  next => trivial

section Prov
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]

/-- **The off-service providers (`.x`, `.p`)**: J-9 B's `ProvOK` at `D` gives `RecOK9I` at `D'`. -/
theorem provP9I_off {V : ℕ → Option ℕ} {R : Nock.Jet.Registry} {comb : ℕ → Noun} {lA : ℕ → ℕ → HX}
    {bl : Bal} (hbl : bl ≠ .s) {provs : List ((Fin (mOf bl) → K) × K)}
    (h : ProvOK (p := p) (K := K) D R lA bl provs) :
    ProvP (p := p) (K := K) (RecOK9I D' V R comb) bl provs := by
  intro q hq l hl hlt hk _
  have hc : recClass (l, bl) = 0 := by
    cases bl with
    | s => exact absurd rfl hbl
    | x => rfl
    | p => rfl
  have hw : ¬ IsWalkA (l, bl) := fun hw => hbl hw.1
  unfold RecOK9
  rw [hc, if_neg (by omega), if_neg (by omega)]
  exact recOK_congr hw (recOK_transfer3 hD3 hag _ (h q hq l hl hlt hk))

end Prov

end Transfer

/-- **`hReg` transfers** (its right-hand side is `some`). -/
theorem hReg_transfer3 {D D' : HX → Option Noun} (hD3 : ∀ v, D (3, v) = none)
    (hag : ∀ k : HX, k.1 ≠ 3 → D' k = D k) {ι : Type} (rows : List ι) (key : ι → HX) (val : ι → Noun)
    (sel : ι → Prop) (h : ∀ r ∈ rows, sel r → D (key r) = some (val r)) :
    ∀ r ∈ rows, sel r → D' (key r) = some (val r) :=
  fun r hr hs => agree_some hD3 hag (h r hr hs)

/-! ## 3. Class `0` from the key -/

section Cls
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]

/-- **A service key that decodes only to class-`0` records**: entry `7 ≠ 5`, and an entry `≥ 4` nonzero. -/
def ClsKey (v : Fin 8 → K) : Prop :=
  v ⟨7, by norm_num⟩ ≠ algebraMap (ZMod p) K ((5 : ℕ) : ZMod p) ∧ ∃ c : Fin 8, 4 ≤ (c : ℕ) ∧ v c ≠ 0

theorem cls0_of_key {v : Fin 8 → K} (hv : ClsKey (p := p) v) (l : List ℕ) (hl : l.length ≤ 8)
    (hk : natKey (p := p) (K := K) 8 l = v) : recClass (l, .s) = 0 := by
  obtain ⟨h7, c, hc4, hc⟩ := hv
  show (if l.length = 8 ∧ l.getLast? = some 5 then 1 else if l.length = 4 then 2 else 0) = 0
  split_ifs with h1 h2
  · exfalso
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ := Nock.Jet.RapJetJ8.eight l h1.1
    have hx : x7 = 5 := by simpa using h1.2
    subst hx
    apply h7
    rw [← hk]
    simp [natKey]
  · exfalso
    apply hc
    rw [← hk]
    simp only [natKey]
    rw [List.getD_eq_default _ _ (by omega)]
    simp
  · rfl

/-- **`RecOK9I` from the pre-form** (`PreI → RecOK` at the trivial `limbA`) on class-`0` keys. -/
theorem provP9I_of_pre {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Nock.Jet.Registry} {comb : ℕ → Noun}
    {provs : List ((Fin 8 → K) × K)} (hcls : ∀ q ∈ provs, ClsKey (p := p) q.1)
    (h : ProvP (p := p) (K := K) (fun r => PreI D r → RecOK D R (fun _ _ => (0, 0)) r) .s provs) :
    ProvP (p := p) (K := K) (RecOK9I D V R comb) .s provs := by
  intro q hq l hl hlt hk hpre
  have hc : recClass (l, Bal.s) = 0 := cls0_of_key (hcls q hq) l hl hk
  unfold RecOK9
  rw [hc, if_neg (by omega), if_neg (by omega)]
  exact h q hq l hl hlt hk (hpre hc)

/-- **`RecOK9I` from `RecOKI`** on class-`0` keys. -/
theorem provP9I_of_I {D : HX → Option Noun} {V : ℕ → Option ℕ} {R : Nock.Jet.Registry} {comb : ℕ → Noun}
    {provs : List ((Fin 8 → K) × K)} (hcls : ∀ q ∈ provs, ClsKey (p := p) q.1)
    (h : ProvP (p := p) (K := K) (RecOKI D R comb) .s provs) :
    ProvP (p := p) (K := K) (RecOK9I D V R comb) .s provs := by
  refine provP9I_of_pre hcls ?_
  intro q hq l hl hlt hk hpre
  have hc : recClass (l, Bal.s) = 0 := cls0_of_key (hcls q hq) l hl hk
  have hw : ¬ IsWalkA (l, Bal.s) := by
    rintro ⟨-, h4⟩
    simp only at h4
    simp [recClass, h4] at hc
  exact (recOKA_iff_off hw).mp (h q hq l hl hlt hk hpre)

/-- A tag `t ∉ {0, 5}` (below `p`, `5 < p`) at entry `7` makes a class-`0` key. -/
theorem clsKey_of_tag7 (hp5 : 5 < p) {t : ℕ} (ht : t < p) (h0 : t ≠ 0) (h5 : t ≠ 5) {v : Fin 8 → K}
    (hv : v ⟨7, by norm_num⟩ = algebraMap (ZMod p) K ((t : ℕ) : ZMod p)) : ClsKey (p := p) v := by
  have hne5 : ((t : ℕ) : ZMod p) ≠ ((5 : ℕ) : ZMod p) := Nock.Jet.RapJetJ8.ne_cast ht hp5 h5
  have hne0 : ((t : ℕ) : ZMod p) ≠ ((0 : ℕ) : ZMod p) := Nock.Jet.RapJetJ8.ne_cast ht (by omega) h0
  refine ⟨?_, ⟨7, by norm_num⟩, by norm_num, ?_⟩
  · rw [hv]; exact fun e => hne5 ((algebraMap (ZMod p) K).injective e)
  · rw [hv]; intro e
    apply hne0
    apply (algebraMap (ZMod p) K).injective
    rw [e]; simp

end Cls

/-! ## 4. The inc providers -/

section Inc
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}
  {QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}

/-- **The inc keys are class `0`**: entry `4` is `TAG_inc = 4`, entry `7` is the padding `0`. -/
theorem inc_cls (hp5 : 5 < p) :
    ∀ q ∈ pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA), ClsKey (p := p) q.1 := by
  have h4 : ((4 : ℕ) : ZMod p) ≠ ((0 : ℕ) : ZMod p) := Nock.Jet.RapJetJ8.ne_cast (by omega) (by omega) (by norm_num)
  have h5 : ((0 : ℕ) : ZMod p) ≠ ((5 : ℕ) : ZMod p) := Nock.Jet.RapJetJ8.ne_cast (by omega) hp5 (by norm_num)
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq'
  split_ifs at hi with h0
  · simp at hi
  · simp only [List.mem_singleton] at hi
    subst hi
    refine ⟨?_, ⟨4, by norm_num⟩, by norm_num, ?_⟩
    · simp only [padK]
      rw [dif_neg (by norm_num)]
      intro e
      apply h5
      apply (algebraMap (ZMod p) K).injective
      simpa using e
    · simp only [padK]
      rw [dif_pos (by norm_num)]
      simp only [ServeH.keyVec5, AtomChipHQ.incKey, List.getD_cons_succ, List.getD_cons_zero,
        Nock.NockVMROM.Thm54.CoordinateCompiler.CoeffExpr.eval, AtomChipHQ.tagInc]
      intro e
      apply h4
      apply (algebraMap (ZMod p) K).injective
      simpa using e

/-- **The inc providers at the J-9 A denotation** (`atomInc_provOKIU` applied at `D` directly, then class `0`). -/
theorem incProv9 (hp5 : 5 < p) (hq : 2 ^ 63 < p)
    (hsat : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    {r : ℕ → AtomChipHQ.ARow}
    (hR : ∀ k : Fin nA, AtomChipHQ.Reads (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k) (r k))
    (hs : ∀ k : Fin nA, ReaderR3bJ8.SmallU (r k)) (hidx : ∀ k : Fin nA, (r k).idx = k)
    {D : HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hD0 : ∀ v, D (0, v) = some (.atom v))
    (hDenB : ∀ j l, AtomChipHQ.Denotes r j l → p ≤ Nock.Atoms.val l → D (2, j) = some (.atom (Nock.Atoms.val l)))
    (hDenB' : ∀ j X, D (2, j) = some X → ∃ l, AtomChipHQ.Denotes r j l ∧ p ≤ Nock.Atoms.val l)
    (hchain : ∀ k : Fin nA, (r k).inc = 1 → ∀ lold, AtomChipHQ.Denotes r (r k).idxO lold →
      ∃ lnew, AtomChipHQ.Denotes r k lnew ∧ Nock.Atoms.val lnew = Nock.Atoms.val lold + 1)
    (hpG : p = Nock.Atoms.p) :
    ProvP (p := p) (K := K) (RecOK9I D V Rg comb) .s (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA)) :=
  provP9I_of_I (inc_cls hp5)
    (ChainUJ8.atomInc_provOKIU (Rg := Rg) (comb := comb) hq hsat hR hs hidx hD0 hDenB hDenB' hchain hpG)

end Inc

/-! ## 5. The jet providers -/

section Jet
open Nock.Jet.ChipJ8 (jetChipJ8 PRow Accepted axPosB)
open Nock.Jet.RapJetJ8 (jProv rowsJ rowJ keyK provKT provKT_eq provK_shape tlF_shape jet_tag)
open Nock.Jet.SubJ8 (jProvE)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {hJ nJ : ℕ} {nodes : Fin nJ → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 hJ} {chals pubs : ℕ → K} {lay : Fin nJ → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

/-- **The J service keys are class `0`**: entry `7` is an in-chip tag `1`, `2` or `TAG_jet = 3`. -/
theorem jProv_cls (hp5 : 5 < p) : ∀ q ∈ jProv b nodes orbit chals pubs lay P, ClsKey (p := p) q.1 := by
  intro q hq
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq
  rcases List.mem_append.mp hi with h1 | h1
  · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp h1
    rw [provKT_eq] at hκ
    obtain ⟨κ1, hκ1, rfl⟩ := List.mem_map.mp hκ
    obtain ⟨-, htag⟩ := tlF_shape (provK_shape _ κ1 hκ1)
    rcases htag with ht | ht
    · exact clsKey_of_tag7 hp5 (t := 1) (by omega) (by norm_num) (by norm_num) (by simp only [keyK]; rw [ht])
    · exact clsKey_of_tag7 hp5 (t := 2) (by omega) (by norm_num) (by norm_num) (by simp only [keyK]; rw [ht])
  · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp h1
    obtain ⟨h7, -, -, -⟩ := jet_tag _ κ hκ
    exact clsKey_of_tag7 hp5 (t := 3) (by omega) (by norm_num) (by norm_num) (by simp only [keyK]; rw [h7])

theorem jProvE_cls (hp5 : 5 < p) (provO : List ((Fin 8 → K) × K)) :
    ∀ q ∈ jProvE (δ := δ) (b := b) (nodes := nodes) (orbit := orbit) (chals := chals) (pubs := pubs)
      (lay := lay) (P := P) provO, ClsKey (p := p) q.1 :=
  fun q hq => jProv_cls hp5 q (List.mem_filter.mp hq).1

/-- **The J service providers at any denotation `D`** (`jetProvOKI` at `D`, then class `0`). -/
theorem jetProv9 (hp5 : 5 < p) {R : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ}
    (hA : Accepted R regs ids (rowsJ b nodes orbit chals pubs lay P))
    {D : HX → Option Noun} {V : ℕ → Option ℕ} {Rg : Nock.Jet.Registry} {comb : ℕ → Noun} (hD : DenOKX p D)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(R i).toTemplate p, Nock.Jet.Autogen.compile p (R i)⟩ ∧ axPosB (R i) = true ∧
      (R i).WellTyped p)
    (hRd : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK D Rg (fun _ _ => (0, 0)) ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x))
    (hReg : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .reg →
      D (r.w.kN.val, r.w.vN.val) = some (Nock.Jet.Autogen.compile p (R r.pre.id)))
    (provO : List ((Fin 8 → K) × K)) :
    ProvP (p := p) (K := K) (RecOK9I D V Rg comb) .s
      (jProvE (δ := δ) (b := b) (nodes := nodes) (orbit := orbit) (chals := chals) (pubs := pubs)
        (lay := lay) (P := P) provO) :=
  provP9I_of_pre (jProvE_cls hp5 provO) (JetProvIJ8.jetProvOKI (by omega) hA hD hTpl hRd hReg provO)

end Jet

end

end Nock.NockVMROM.Thm54.VclL.Handle.ProvKindsX9

open Nock.NockVMROM.Thm54.VclL.Handle.ProvKindsX9 in
#print axioms recOK_transfer3
open Nock.NockVMROM.Thm54.VclL.Handle.ProvKindsX9 in
#print axioms provP9I_off
open Nock.NockVMROM.Thm54.VclL.Handle.ProvKindsX9 in
#print axioms provP9I_of_I
open Nock.NockVMROM.Thm54.VclL.Handle.ProvKindsX9 in
#print axioms incProv9
open Nock.NockVMROM.Thm54.VclL.Handle.ProvKindsX9 in
#print axioms jetProv9
