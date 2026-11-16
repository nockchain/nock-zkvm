/-
  Nock/Jet/RegJ8R.lean

  **`hReg` from `claimK_genuine_cell`, and the provider obligations on
  WEIGHTED providers (`hSub` narrowed).**

  * `RegServedV` is the same statement
    whichever way the registry key's public part is bound (the module report's options), so this
    lemma does not depend on that choice.
  * **`jetProvOK_R`**: JB's `jetProvOK` at `D := denK tb ext` with `hReg` discharged.
-/
import Nock.Jet.ChipJ8R
import Nock.Jet.RapJetJ8
import Nock.NockVMROM.Thm54.P8Core.VclL.DecodeTree

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.Jet.RegJ8R

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8
open Nock.Framework Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

/-! ## 1. The kind gate -/

section Kind
variable {p : ℕ} [Fact p.Prime]

/-- **`regKindGate` on a `.reg` row: `kN = 1`.** -/
theorem kN_of_regKind {r : CRow (ZMod p)} (hk : r.pre.kd = .reg)
    (hg : (regKindGate : CoeffExpr (ZMod p)).eval (envOf r) = 0) : r.w.kN = 1 := by
  simp only [regKindGate, CoeffExpr.eval, envOf] at hg
  have h0 : colOf r (Kd.sel .reg) = 1 := by simp [colOf, hk, Kd.sel]
  have hN : colOf r Col.kN = r.w.kN := rfl
  rw [h0, hN, one_mul] at hg
  exact sub_eq_zero.1 hg

/-- The gate is vacuous off `.reg` rows. -/
theorem regKind_off {r : CRow (ZMod p)} (hk : r.pre.kd ≠ .reg) :
    (regKindGate : CoeffExpr (ZMod p)).eval (envOf r) = 0 := by
  have h0 : colOf r (Kd.sel .reg) = 0 := by
    obtain ⟨⟨kd, _, _, _, _, _⟩, _⟩ := r
    cases kd <;> first | exact absurd rfl hk | rfl
  simp only [regKindGate, CoeffExpr.eval, envOf]
  rw [h0, zero_mul]

/-- The gate holds on a `.reg` row with `kN = 1`. -/
theorem regKind_on {r : CRow (ZMod p)} (h1 : r.w.kN = 1) :
    (regKindGate : CoeffExpr (ZMod p)).eval (envOf r) = 0 := by
  simp only [regKindGate, CoeffExpr.eval, envOf]
  have hN : colOf r Col.kN = r.w.kN := rfl
  rw [hN, h1, sub_self, mul_zero]

end Kind

/-! ## 2. The registry consume served ⇒ `hReg` -/

section Reg
variable {p : ℕ} [Fact p.Prime] {Kfp : Type} [Field Kfp] [Algebra (ZMod p) Kfp]

/-- **The registry consume in existence form**: every `.reg` row's claim key
`(E (compile p (R id)), hi, lo, vN)` (`(hi, lo) = rk id`, the verifier's rank of `c_T`) is served by the
two-provider cell validity balance — some cell row's key, or an external (atom-root) key. -/
def RegServedV (E : Noun → FP Kfp) (rk : ℕ → ℕ × ℕ) (t : List (CellRow p Kfp)) (vp : List (VKey Kfp))
    (R : ℕ → Tpl) (rows : List (CRow (ZMod p))) : Prop :=
  ∀ r ∈ rows, r.pre.kd = .reg →
    (∃ c ∈ t, (E (compile p (R r.pre.id)), (rk r.pre.id).1, (rk r.pre.id).2, r.w.vN.val) =
      (c.p, c.b0.hi, c.b0.lo, c.b0.idx)) ∨
    (E (compile p (R r.pre.id)), (rk r.pre.id).1, (rk r.pre.id).2, r.w.vN.val) ∈ vp

/-- **`hReg` (JB) from the registry consume** — `claimK_genuine_cell`. -/
theorem hReg_of_served (hq : 2 ^ 63 < p) {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms p z E)
    {t : List (CellRow p Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (h : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext)
    {R : ℕ → Tpl} {rk : ℕ → ℕ × ℕ} {rows : List (CRow (ZMod p))}
    (hgate : ∀ r ∈ rows, (regKindGate : CoeffExpr (ZMod p)).eval (envOf r) = 0)
    (hsrv : RegServedV E rk t vp R rows)
    (hrk : ∀ r ∈ rows, r.pre.kd = .reg → rk r.pre.id ≠ (0, 0))
    (hinj : ∀ r ∈ rows, r.pre.kd = .reg → ∀ d ∈ decodedNouns2 (t.map (·.b0)) ext,
      E (compile p (R r.pre.id)) = E d → compile p (R r.pre.id) = d) :
    ∀ r ∈ rows, r.pre.kd = .reg →
      denK (t.map (·.b0)) ext (r.w.kN.val, r.w.vN.val) = some (compile p (R r.pre.id)) := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  intro r hr hk
  have hN : r.w.kN = 1 := kN_of_regKind hk (hgate r hr)
  rw [hN, ZMod.val_one]
  rcases hsrv r hr hk with hc | hv
  · exact claimK_genuine_cell hq hcons hE h hvp (hinj r hr hk) hc
  · exfalso
    obtain ⟨h1, h2, -⟩ := hvp _ hv
    exact hrk r hr hk (Prod.ext h1 h2)

end Reg

/-! ## 3. `jetProvOK` with `hReg` discharged -/

section ProvR
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}
  {Kfp : Type} [Field Kfp] [Algebra (ZMod p) Kfp]

/-- **`JetProvOK` at the cell denotation, `hReg` discharged** (G-J1 closed modulo `RegServedV`). -/
theorem jetProvOK_R (hp3 : 3 < p) (hq : 2 ^ 63 < p) {R : ℕ → Tpl} {regs ids : List ℕ}
    (hA : Accepted R regs ids (rowsJ b nodes orbit chals pubs lay P))
    {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms p z E)
    {t : List (CellRow p Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (htab : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext)
    {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX} (hD : DenOKX p (denK (t.map (·.b0)) ext))
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(R i).toTemplate p, compile p (R i)⟩ ∧ axPosB (R i) = true ∧
      (R i).WellTyped p)
    (hRd : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK (denK (t.map (·.b0)) ext) Rg limbA ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x))
    {rk : ℕ → ℕ × ℕ}
    (hgate : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, (regKindGate : CoeffExpr (ZMod p)).eval (envOf r) = 0)
    (hsrv : RegServedV E rk t vp R (rowsJ b nodes orbit chals pubs lay P))
    (hrk : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .reg → rk r.pre.id ≠ (0, 0))
    (hinj : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .reg →
      ∀ d ∈ decodedNouns2 (t.map (·.b0)) ext, E (compile p (R r.pre.id)) = E d → compile p (R r.pre.id) = d)
    (hSub : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .call →
      ∃ S, denK (t.map (·.b0)) ext (r.w.kL.val, r.w.vL.val) = some S) :
    ServedJ8.ProvP (p := p) (K := K) (RecOK (denK (t.map (·.b0)) ext) Rg limbA) .s
      (jProv b nodes orbit chals pubs lay P) :=
  jetProvOK hp3 hA hD hTpl hRd (hReg_of_served hq hcons hE htab hvp hgate hsrv hrk hinj) hSub

end ProvR

/-! ## 4. Weighted providers -/

section Weighted

/-- **Dropping weight-0 providers leaves a provider-side sum unchanged.** -/
theorem sum_filter_weighted {ι K L : Type} [Field K] [DecidableEq K] [Field L] (l : List (ι × K))
    (g : K → L) (hg : g 0 = 0) (f : ι → L) :
    (l.map fun q => g q.2 * f q.1).sum = ((l.filter fun q => q.2 ≠ 0).map fun q => g q.2 * f q.1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a.2 = 0
    · simp [ha, hg, ih]
    · simp [ha, ih]

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

local notation "RJ" => rowJ b nodes orbit chals pubs lay P

noncomputable def jProvW (b : Basis (Fin 3) (ZMod p) K) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (chals pubs : ℕ → K) (lay : Fin n → PRow) (P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]) :
    List ((Fin 8 → K) × K) :=
  (jProv b nodes orbit chals pubs lay P).filter fun q => q.2 ≠ 0

/-- **`JetProvOK` on weighted providers.**  As `jetProvOK`, with the subject obligation `hSub` only on
call rows of weight `m ≠ 0`: an unweighted `TAG_jet` provide is not a provider of the balance. -/
theorem jetProvOKW (hp3 : 3 < p) {R : ℕ → Tpl} {regs ids : List ℕ}
    (hA : Accepted R regs ids (rowsJ b nodes orbit chals pubs lay P))
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX} (hD : DenOKX p D)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(R i).toTemplate p, compile p (R i)⟩ ∧ axPosB (R i) = true ∧
      (R i).WellTyped p)
    (hRd : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK D Rg limbA ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x))
    (hReg : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .reg →
      D (r.w.kN.val, r.w.vN.val) = some (compile p (R r.pre.id)))
    (hSubW : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .call → r.w.m ≠ 0 →
      ∃ S, D (r.w.kL.val, r.w.vL.val) = some S) :
    ServedJ8.ProvP (p := p) (K := K) (RecOK D Rg limbA) .s (jProvW (δ := δ) b nodes orbit chals pubs lay P) := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hM : MemoryBB R (rowsJ b nodes orbit chals pubs lay P) (fun hh => D (hh.1.val, hh.2.val)) :=
    { den0 := fun v => by simp only [ZMod.val_zero]; exact hD.atom v.val
      gen := fun r hr hk => by
        obtain ⟨A, B, h1, h2, h3⟩ := hRd r hr hk
        unfold recB
        simp only [ZMod.val_one, h2, h3, h1]
        simp
      reg := hReg }
  have h1 : (1 : ℕ) < p := by omega
  have h2 : (2 : ℕ) < p := by omega
  have h3 : (3 : ℕ) < p := by omega
  have h0 : (0 : ℕ) < p := by omega
  intro q hqW l hl hlt hnk
  obtain ⟨hq, hq2⟩ := List.mem_filter.mp hqW
  have hq2' : q.2 ≠ 0 := by simpa using hq2
  change l.length ≤ 8 at hl
  change DenXJ8.natKey (p := p) (K := K) 8 l = q.1 at hnk
  obtain ⟨i, -, hq'⟩ := List.mem_flatMap.mp hq
  have hrc : RJ i ∈ rowsJ b nodes orbit chals pubs lay P := List.mem_ofFn.mpr ⟨i, rfl⟩
  rcases List.mem_append.mp hq' with hP | hJ
  · obtain ⟨κ', hκ', rfl⟩ := List.mem_map.mp hP
    rw [provKT_eq] at hκ'
    obtain ⟨κ1, hκ1, rfl⟩ := List.mem_map.mp hκ'
    obtain ⟨-, htag⟩ := tlF_shape (provK_shape _ κ1 hκ1)
    have h7ne : (tlF κ1).getD 7 0 ≠ 0 := by
      rcases htag with ht | ht <;> rw [ht]
      · simp
      · simpa using ne_cast h2 h0 (by norm_num)
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ := eight l (len8_of_tag hl hnk h7ne)
    have e7 := natKey_keyK hnk 7 (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at e7
    have hx7 : x7 < p := hlt x7 (by simp)
    rcases htag with ht | ht <;> rw [ht] at e7
    · obtain rfl := natCast_inj_lt hx7 h1 e7; simp [RecOK]
    · obtain rfl := natCast_inj_lt hx7 h2 e7; simp [RecOK]
  · obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hJ
    have hm : (RJ i).w.m ≠ 0 := by
      intro hm0; apply hq2'; simp [hm0]
    obtain ⟨h7, hlen, hkd, rfl⟩ := jet_tag _ κ hκ
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ :=
      eight l (len8_of_tag hl hnk (by rw [h7]; simpa using ne_cast h3 h0 (by norm_num)))
    have e : ∀ c (hc : c < 8), (([x0, x1, x2, x3, x4, x5, x6, x7].getD c 0 : ℕ) : ZMod p) =
        (keyJet.map (KE.ev (colOf (RJ i)))).getD c 0 := fun c hc => natKey_keyK hnk c hc
    have e0 := e 0 (by norm_num); have e1 := e 1 (by norm_num); have e2 := e 2 (by norm_num)
    have e3 := e 3 (by norm_num); have e4 := e 4 (by norm_num); have e5 := e 5 (by norm_num)
    have e6 := e 6 (by norm_num); have e7 := e 7 (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero, keyJet, List.map_cons, List.map_nil, KE.ev,
      colOf, Col.id, Col.kN, Col.vN, Col.kL, Col.vL, Col.kR, Col.vR] at e0 e1 e2 e3 e4 e5 e6 e7
    have hlt' : ∀ x ∈ [x0, x1, x2, x3, x4, x5, x6, x7], x < p := hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt'
    obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩ := hlt'
    obtain rfl := natCast_inj_lt hx7 h3 e7
    have hpm := pre_mem hA hrc
    obtain ⟨c, i0, hc, hpre⟩ := layout_call hpm hkd
    have hi0 : i0 < p := by have := (hA.small _ hpm).1; rw [hpre] at this; exact this
    have hid : (RJ i).pre.id = i0 := by rw [hpre]; rfl
    rw [hid] at e0
    obtain rfl := natCast_inj_lt hx0 hi0 e0
    obtain rfl := val_of_cast hx1 e1; obtain rfl := val_of_cast hx2 e2
    obtain rfl := val_of_cast hx3 e3; obtain rfl := val_of_cast hx4 e4
    obtain rfl := val_of_cast hx5 e5; obtain rfl := val_of_cast hx6 e6
    have hreg := call_reg hA hrc hpre
    obtain ⟨hRg, hax, hT⟩ := hTpl x0 hreg
    obtain ⟨S, hS⟩ := hSubW _ hrc hkd hm
    obtain ⟨hcomp, E, hE, hsem, -⟩ := jetChip_holds R regs ids (rowsJ b nodes orbit chals pubs lay P)
      (fun hh => D (hh.1.val, hh.2.val)) hA hM c x0 hc hax hT (RJ i) hrc hpre S hS
    exact ⟨_, hRg, hcomp, S, E, hS, hE, hsem⟩

/-- **The J provider sum over weighted providers** equals the full one (any `𝕂′` lift, `g 0 = 0`). -/
theorem jProvW_sum {L : Type} [Field L] (g : K → L) (hg : g 0 = 0) (f : (Fin 8 → K) → L) :
    ((jProv b nodes orbit chals pubs lay P).map fun q => g q.2 * f q.1).sum =
      ((jProvW (δ := δ) b nodes orbit chals pubs lay P).map fun q => g q.2 * f q.1).sum :=
  sum_filter_weighted _ g hg f

end Weighted

end Nock.Jet.RegJ8R
