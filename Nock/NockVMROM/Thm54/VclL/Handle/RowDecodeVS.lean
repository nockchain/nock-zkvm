/-
  Nock/NockVMROM/Thm54/VclL/Handle/RowDecodeVS.lean

* `hdF eF h` — the handle a row commits in `ChipH.Hd` columns `h`: `(kind = 1, natOf value)`;
    `stOf j₀`, `rowOf eF j₀` — the decoded `RowVS`.
  * `activeXRecs` / `activePRecs` — the export / walk records a row consumes (the records whose keys
    are `TeleC.rowXReqs` / `rowPReqs`).
  * `XOK` / `POK` — what a served, genuine record says on a denotation `D`: an export record
    `(p, l, r)` names `D (1, p) = [D l, D r]`; a walk record `(root, ax, ch)` names
    `/[ax] (D (1, root)) = D ch`.
  * **`rowSem_of_chip`**: a row whose base template gates vanish (`RowSel` at `j₀`), under
    `PrimeFieldElems 𝔽` and `11 < char 𝔽`, and whose consumed records are `XOK` / `POK`, satisfies
    `RowSem D (char 𝔽) (rowOf eF j₀)` — per state, from the equality tests, the kind-bit /
    atom-only arithmetic, and the served records (OP5 "≠" from `neGate` only: kinds, atom-value
    inverse, or the read pair).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleC
import Nock.NockVMROM.Thm54.VclL.Handle.LocalVS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS

open Nock Nock.Reified Nock.Framework
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (natOf natOf_natCast natOf_inj natOf_lt natOf_cast)

noncomputable section

-- disjunction search for membership
syntax "eqmR" : tactic
macro_rules
  | `(tactic| eqmR) =>
    `(tactic| first | exact trivial | exact rfl | (apply Or.inl; eqmR) | (apply Or.inr; eqmR))

/-- Membership of a concrete equality test. -/
macro "eqm" : tactic => `(tactic| (unfold ChipH.eqGates ChipH.heq ChipH.hpub; simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]; eqmR))

set_option hygiene false in
/-- Evaluate a selector at the row's one-hot state (`sv`). -/
macro "selv" : tactic => `(tactic| simp [evalQ, evalQ_cc, evalQ_prodL, prodL, notC, sv, sel_one hs])

section Decode
variable {F : Type} [Field F] [DecidableEq F]

/-- The handle committed in columns `(k, v)`. -/
def hdc (eF : Env F) (k v : ℕ) : VHandle := (decide (eF.trace k = 1), natOf (eF.trace v))

def hdF (eF : Env F) (h : Hd) : VHandle := hdc eF h.k h.v

/-- The state of one-hot index `j₀` (`cons` at `10`). -/
def stOf : ℕ → State
  | 0 => .s0 | 1 => .s1 | 2 => .s2 | 3 => .s3 | 4 => .s4 | 5 => .s5 | 6 => .s6 | 7 => .s7
  | 8 => .s8 | 9 => .s9 | _ => .cons

/-- **The decoded row.** -/
def rowOf (eF : Env F) (j0 : ℕ) : RowVS where
  st := stOf j0
  s := hdF eF hS
  f := hdF eF hF
  e := hdF eF hE
  sf1 := hdF eF hSf1
  sf2 := hdF eF hSf2
  fh := hdF eF hFh
  ft := hdF eF hFt
  fth := hdF eF hFth
  ftt := hdF eF hFtt
  ftth := hdF eF hFtth
  fttt := hdF eF hFttt
  m := hdF eF hM

/-- The export records a row consumes. -/
def activeXRecs (eF : Env F) : List (List ℕ) :=
  (slots : List (SlotSpec ℚ)).flatMap fun S => (activeX S eF).map Ent.rcd

def pairRecs (S : SlotSpec ℚ) (eF : Env F) : List (List ℕ) :=
  match S.pair with
  | some (fl, a, b) => if eF.trace fl = 1 then [a, b] else []
  | none => []

/-- The walk records a row consumes. -/
def activePRecs (eF : Env F) : List (List ℕ) :=
  (slots : List (SlotSpec ℚ)).flatMap fun S => (activeP S eF).map Ent.rcd ++ pairRecs S eF

variable (D : VHandle → Option Noun)

/-- A served genuine export record `[p, lk, lv, rk, rv]`: `D (1, p) = [D l, D r]`. -/
def XOK (eF : Env F) (r : List ℕ) : Prop :=
  ∀ pv lk lv rk rv, r = [pv, lk, lv, rk, rv] →
    Cell3 D (true, natOf (eF.trace pv)) (hdc eF lk lv) (hdc eF rk rv)

/-- A served genuine walk record `[root, ax, ck, cv]`: `/[ax] (D (1, root)) = D ch`. -/
def POK (eF : Env F) (r : List ℕ) : Prop :=
  ∀ rv ax ck cv, r = [rv, ax, ck, cv] →
    ∃ R C, D (true, natOf (eF.trace rv)) = some R ∧ D (hdc eF ck cv) = some C ∧
      Noun.slot (natOf (eF.trace ax)) R = some C

end Decode

/-! ## Gate facts -/

section Facts
variable {F : Type} [Field F] [DecidableEq F] {eF : Env F} {j0 : ℕ}

theorem eq_fact (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t eF = 0) (g : EqG ℚ)
    (hg : g ∈ (eqGates : List (EqG ℚ))) : evalQ (EqG.gate g) eF = 0 :=
  hbase _ (List.mem_append_right _ (List.mem_map_of_mem hg))

theorem kind_bool (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t eF = 0) (j : ℕ) (hj : j < 12) :
    eF.trace (hd j).k = 0 ∨ eF.trace (hd j).k = 1 := by
  have := gate_q hbase (.mul (cc (hd j).k) (.sub (cc (hd j).k) (.const 1)))
    (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨hd j, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, rfl⟩)))
  simp only [evalQ, evalQ_cc, Rat.cast_one] at this
  exact bool_of this

theorem hdc_zero (k v : ℕ) (h : eF.trace k = 0) : hdc eF k v = (false, natOf (eF.trace v)) := by
  simp [hdc, h]

theorem hdc_one (k v : ℕ) (h : eF.trace k = 1) : hdc eF k v = (true, natOf (eF.trace v)) := by
  simp [hdc, h]

/-- Equality-test facts (generic in the selector). -/
theorem eqv (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t eF = 0) (σ : CoeffExpr ℚ) (x y : ℕ)
    (hg : (⟨σ, x, .col y⟩ : EqG ℚ) ∈ (eqGates : List (EqG ℚ))) :
    evalQ σ eF * (eF.trace x - eF.trace y) = 0 := by
  simpa [EqG.gate, evalQ, Opnd.expr, evalQ_cc] using eq_fact hbase _ hg

theorem xmem (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ (slots : List (SlotSpec ℚ))) (x : Ent ℚ)
    (hx : x ∈ S.ents) (hp : x.path = false) (hj : j0 ∈ x.states) (he : evalQ x.extra eF = 1) :
    x.rcd ∈ activeXRecs eF := by
  refine List.mem_flatMap.mpr ⟨S, hS, List.mem_map.mpr ⟨x, ?_, rfl⟩⟩
  refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hx, by simp [hp]⟩, ?_⟩
  simp [act_val hs S hS x hx, hj, he]

theorem pmem (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ (slots : List (SlotSpec ℚ))) (x : Ent ℚ)
    (hx : x ∈ S.ents) (hp : x.path = true) (hj : j0 ∈ x.states) (he : evalQ x.extra eF = 1) :
    x.rcd ∈ activePRecs eF := by
  refine List.mem_flatMap.mpr ⟨S, hS, List.mem_append_left _ (List.mem_map.mpr ⟨x, ?_, rfl⟩)⟩
  refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hx, by simp [hp]⟩, ?_⟩
  simp [act_val hs S hS x hx, hj, he]

theorem pairmem (hpr : eF.trace prC = 1) :
    walkRec hSf1 hM.v hFtth ∈ activePRecs eF ∧ walkRec hSf2 hM.v hFttt ∈ activePRecs eF := by
  have h2 : (slot2 : SlotSpec ℚ) ∈ slots := by simp [slots]
  have hp : pairRecs slot2 eF = [walkRec hSf1 hM.v hFtth, walkRec hSf2 hM.v hFttt] := by
    simp [pairRecs, slot2, hpr]
  refine ⟨List.mem_flatMap.mpr ⟨_, h2, List.mem_append_right _ ?_⟩,
    List.mem_flatMap.mpr ⟨_, h2, List.mem_append_right _ ?_⟩⟩ <;> rw [hp] <;> simp

variable (D : VHandle → Option Noun)

theorem cell3_rec (hX : ∀ r ∈ activeXRecs eF, XOK D eF r) (p l r : Hd)
    (hmem : cellRec p l r ∈ activeXRecs eF) (hk : eF.trace p.k = 1) :
    Cell3 D (hdF eF p) (hdF eF l) (hdF eF r) := by
  rw [hdF, hdc_one _ _ hk]
  exact hX _ hmem _ _ _ _ _ rfl

theorem walk_rec (hP : ∀ r ∈ activePRecs eF, POK D eF r) (root : Hd) (ax : ℕ) (ch : Hd)
    (hmem : walkRec root ax ch ∈ activePRecs eF) (hk : eF.trace root.k = 1) :
    ∃ R C, D (hdF eF root) = some R ∧ D (hdF eF ch) = some C ∧
      Noun.slot (natOf (eF.trace ax)) R = some C := by
  rw [hdF, hdc_one _ _ hk]
  exact hP _ hmem _ _ _ _ rfl

theorem col_fact (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t eF = 0) (σ : CoeffExpr ℚ) (x y : ℕ)
    (hg : (⟨σ, x, .col y⟩ : EqG ℚ) ∈ (eqGates : List (EqG ℚ))) (h1 : evalQ σ eF = 1) :
    eF.trace x = eF.trace y := by
  have := eqv hbase σ x y hg
  rw [h1, one_mul] at this
  exact sub_eq_zero.mp this

theorem heq_fact (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t eF = 0) (σ : CoeffExpr ℚ) (a b : Hd)
    (h1 : (⟨σ, a.k, .col b.k⟩ : EqG ℚ) ∈ (eqGates : List (EqG ℚ)))
    (h2 : (⟨σ, a.v, .col b.v⟩ : EqG ℚ) ∈ (eqGates : List (EqG ℚ))) (hσ : evalQ σ eF = 1) :
    hdF eF a = hdF eF b := by
  have hk := col_fact hbase σ a.k b.k h1 hσ
  have hv := col_fact hbase σ a.v b.v h2 hσ
  simp [hdF, hdc, hk, hv]

theorem arith_fact (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t eF = 0) (t : CoeffExpr ℚ)
    (ht : t ∈ arithGates (F := ℚ)) : evalQ t eF = 0 := gate_q hbase t ht

omit [DecidableEq F] in
theorem sel_one (hs : RowSel eF j0) : eF.trace j0 = 1 := by
  have := hs.sel j0 hs.lt; simpa using this

omit [DecidableEq F] in
theorem sel_zero (hs : RowSel eF j0) (j : ℕ) (hj : j < 11) (hne : j ≠ j0) : eF.trace j = 0 := by
  have := hs.sel j hj; simpa [hne] using this

/-- **Item 5, the chip half: a compute row decodes to `RowSem`.** -/
theorem rowSem_of_chip (hD : DenOK D) (hFe : GeneratedField.PrimeFieldElems F) (hc : 11 < ringChar F)
    (hbase : ∀ t ∈ baseGatesH (F := ℚ), evalQ t eF = 0) (hs : RowSel eF j0)
    (hX : ∀ r ∈ activeXRecs eF, XOK D eF r) (hP : ∀ r ∈ activePRecs eF, POK D eF r) :
    RowSem D (ringChar F) (rowOf eF j0) := by
  have A : ∀ t ∈ arithGates (F := ℚ), evalQ t eF = 0 := fun t ht => gate_q hbase t ht
  have E := eqv hbase
  have hfk : eF.trace hF.k = 1 := by
    have := A (.sub (cc hF.k) (.const 1)) (by simp [arithGates])
    simpa [evalQ, evalQ_cc, sub_eq_zero] using this
  have L1 : Cell3 D (hdF eF hF) (hdF eF hFh) (hdF eF hFt) :=
    cell3_rec D hX hF hFh hFt (xmem hs slot0 (by simp [slots])
      ⟨ChipH.allStates, .const 1, cellRec hF hFh hFt, false⟩ (by simp [slot0]) rfl
      (by simp [ChipH.allStates, hs.lt]) (by simp [evalQ])) hfk
  have fhJ : ∀ J, J < 10 → j0 = J → hdF eF hFh = (false, J) := by
    intro J hJ hj
    have hk : eF.trace hFh.k = 0 := by
      have := A (.sub (cc consCol) (cc hFh.k)) (by simp [arithGates])
      have h10 := sel_zero hs 10 (by decide) (by omega)
      simp only [evalQ, evalQ_cc, consCol] at this
      rw [h10] at this; linear_combination -this
    have hv : eF.trace hFh.v = (J : F) := by
      have hm : (⟨cc J, hFh.v, .cst (J : ℚ)⟩ : EqG ℚ) ∈
          (List.range 10).map (fun j : ℕ => (⟨cc j, hFh.v, .cst (j : ℚ)⟩ : EqG ℚ)) :=
        List.mem_map.2 ⟨J, List.mem_range.2 hJ, rfl⟩
      have := eq_fact hbase ⟨cc J, hFh.v, .cst (J : ℚ)⟩
        (by unfold eqGates; simp only [List.mem_append]; repeat' apply Or.inl
            exact hm)
      simp only [EqG.gate, evalQ, Opnd.expr, evalQ_cc] at this
      rw [show eF.trace J = 1 from hj ▸ sel_one hs, one_mul, Rat.cast_natCast] at this
      exact sub_eq_zero.mp this
    rw [hdF, hdc_zero _ _ hk, hv, natOf_natCast hFe (by omega)]
  have nat1 : natOf (1 : F) = 1 := by simpa using natOf_natCast hFe (k := 1) (by omega)
  have nat0 : natOf (0 : F) = 0 := by simpa using natOf_natCast hFe (k := 0) (by omega)
  have L2 : j0 ∈ l2States → Cell3 D (hdF eF hFt) (hdF eF hFth) (hdF eF hFtt) := by
    intro hj
    have hk : eF.trace hFt.k = 1 := by
      have := arith_fact hbase (.mul (selS l2States) (notC hFt.k)) (by simp [arithGates])
      have hsum : evalQ (selS l2States : CoeffExpr ℚ) eF = 1 := by
        rw [evalQ_selS]
        simp only [l2States] at hj ⊢
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [hs.sel 2 (by decide), hs.sel 5 (by decide), hs.sel 6 (by decide), hs.sel 7 (by decide),
          hs.sel 8 (by decide), hs.sel 9 (by decide)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
      simp only [evalQ, notC, evalQ_cc, Rat.cast_one] at this hsum
      rw [hsum, one_mul, sub_eq_zero] at this
      exact this.symm
    exact cell3_rec D hX hFt hFth hFtt (xmem hs slot1 (by simp [slots])
      ⟨l2States, .const 1, cellRec hFt hFth hFtt, false⟩ (by simp [slot1]) rfl hj (by simp [evalQ])) hk
  have hlt := hs.lt
  have sv := hs.sel
  interval_cases j0
  · -- OP0
    have hftk : eF.trace hFt.k = 0 := by
      have := arith_fact hbase (.mul (cc 0) (cc hFt.k)) (by simp [arithGates])
      simpa [evalQ, evalQ_cc, sv] using this
    refine ⟨L1, fhJ 0 (by decide) rfl, natOf (eF.trace hFt.v), by simp [rowOf, hdF, hdc, hftk], ?_⟩
    rcases hs.z1 with hz | hz
    · right
      have hsk : eF.trace hS.k = 1 := by
        have := arith_fact hbase (prodL [cc 0, notC z1C, notC hS.k]) (by simp [arithGates])
        simp [evalQ_prodL, evalQ, evalQ_cc, notC, sv, hz, sub_eq_zero] at this
        exact this.symm
      exact walk_rec D hP hS hFt.v hE (pmem hs slot1 (by simp [slots])
        ⟨[0], notC z1C, walkRec hS hFt.v hE, true⟩ (by simp [slot1]) rfl (by simp)
        (by simp [evalQ, notC, evalQ_cc, hz])) hsk
    · left
      have hv1 : eF.trace vC = 1 := by
        have := arith_fact hbase (prodL [cc 0, cc z1C, .sub (cc vC) (.const 1)]) (by simp [arithGates])
        simp [evalQ_prodL, evalQ, evalQ_cc, sv, hz, sub_eq_zero] at this
        exact this
      have hvf := col_fact hbase (cc 0) vC hFt.v (by eqm) (by simp [evalQ, evalQ_cc, sv])
      refine ⟨by rw [← hvf, hv1, nat1],
        heq_fact hbase (.mul (cc 0) (cc z1C)) hE hS (by eqm) (by eqm) (by selv; simp [hz])⟩
  · -- OP1
    exact ⟨L1, fhJ 1 (by decide) rfl, heq_fact hbase (cc 1) hE hFt (by eqm) (by eqm) (by selv)⟩
  · -- OP2
    exact ⟨L1, fhJ 2 (by decide) rfl, L2 (by simp [l2States])⟩
  · -- OP3
    have hek : eF.trace hE.k = 0 := by
      have := arith_fact hbase (.mul (cc 3) (cc hE.k)) (by simp [arithGates])
      simpa [evalQ, evalQ_cc, sv] using this
    have hev := col_fact hbase (cc 3) hE.v betaC (by eqm) (by selv)
    have hb := arith_fact hbase (.mul (cc 3) (.add (.sub (cc betaC) (.const 1)) (cc hSf1.k)))
      (by simp [arithGates])
    simp only [evalQ, evalQ_cc, sel_one hs, Rat.cast_one, one_mul] at hb
    refine ⟨L1, fhJ 3 (by decide) rfl, ?_⟩
    have he : hdF eF hE = (false, natOf (eF.trace betaC)) := by
      rw [hdF, hdc_zero _ _ hek, hev]
    rcases hs.k1 with hk | hk
    · refine ⟨.atom (natOf (eF.trace hSf1.v)), by
        show D (hdF eF hSf1) = _; rw [hdF, hdc_zero _ _ hk]; exact hD.atom _, ?_⟩
      have hβ : eF.trace betaC = 1 := by rw [hk] at hb; linear_combination hb
      show D (hdF eF hE) = _
      rw [he, hβ, nat1, hD.atom]; rfl
    · have hc3 := cell3_rec D hX hSf1 hFtth hFttt (xmem hs slot2 (by simp [slots])
        ⟨[3], cc hSf1.k, cellRec hSf1 hFtth hFttt, false⟩ (by simp [slot2]) rfl (by simp)
        (by simp [evalQ, evalQ_cc, hk])) hk
      obtain ⟨A1, B1, hA, -, -⟩ := hc3
      refine ⟨_, hA, ?_⟩
      have hβ : eF.trace betaC = 0 := by rw [hk] at hb; linear_combination hb
      show D (hdF eF hE) = _
      rw [he, hβ, nat0, hD.atom]; rfl
  · -- OP4
    have hsk : eF.trace hSf1.k = 0 := by
      have := arith_fact hbase (.mul (cc 4) (cc hSf1.k)) (by simp [arithGates])
      simpa [evalQ, evalQ_cc, sv] using this
    have hek : eF.trace hE.k = 0 := by
      have := arith_fact hbase (.mul (cc 4) (cc hE.k)) (by simp [arithGates])
      simpa [evalQ, evalQ_cc, sv] using this
    have hv := col_fact hbase (cc 4) vC hSf1.v (by eqm) (by selv)
    have hev := col_fact hbase (cc 4) hE.v v2C (by eqm) (by selv)
    have hinc := arith_fact hbase (.mul (cc 4) (.sub (.sub (cc v2C) (cc vC)) (.const 1)))
      (by simp [arithGates])
    simp only [evalQ, evalQ_cc, sel_one hs, Rat.cast_one, one_mul] at hinc
    refine ⟨L1, fhJ 4 (by decide) rfl, natOf (eF.trace hSf1.v), ?_, ?_⟩
    · show D (hdF eF hSf1) = _; rw [hdF, hdc_zero _ _ hsk]; exact hD.atom _
    · show D (hdF eF hE) = _
      rw [hdF, hdc_zero _ _ hek, hev, hD.atom]
      have hp : 0 < ringChar F := by omega
      have h2 : eF.trace v2C = (((natOf (eF.trace hSf1.v) + 1) % ringChar F : ℕ) : F) := by
        rw [← CharP.cast_eq_mod F (ringChar F), Nat.cast_add, natOf_cast hFe, Nat.cast_one, ← hv]
        linear_combination hinc
      rw [h2, natOf_natCast hFe (Nat.mod_lt _ hp)]
  · -- OP5 (item 6)
    have hek : eF.trace hE.k = 0 := by
      have := arith_fact hbase (.mul (cc 5) (cc hE.k)) (by simp [arithGates])
      simpa [evalQ, evalQ_cc, sv] using this
    have hev := col_fact hbase (cc 5) hE.v betaC (by eqm) (by selv)
    have he : hdF eF hE = (false, natOf (eF.trace betaC)) := by rw [hdF, hdc_zero _ _ hek, hev]
    refine ⟨L1, fhJ 5 (by decide) rfl, L2 (by simp [l2States]), ?_⟩
    rcases hs.beta with hb | hb
    · left
      refine ⟨heq_fact hbase (prodL [cc 5, notC betaC]) hSf1 hSf2 (by eqm) (by eqm) (by selv; simp [hb]), ?_⟩
      show hdF eF hE = _; rw [he, hb, nat0]
    · right
      refine ⟨by show hdF eF hE = _; rw [he, hb, nat1], ?_⟩
      -- the first-difference leaves differ
      have hk9 : eF.trace hFtth.k = 0 ∨ eF.trace hFtth.k = 1 := kind_bool hbase 9 (by decide)
      have hk10 : eF.trace hFttt.k = 0 ∨ eF.trace hFttt.k = 1 := kind_bool hbase 10 (by decide)
      have hboth := arith_fact hbase (prodL [cc 5, cc betaC, cc hFtth.k, cc hFttt.k]) (by simp [arithGates])
      have hne := arith_fact hbase neGate (by simp [arithGates])
      have hva := col_fact hbase (prodL [cc 5, cc betaC, notC hFtth.k]) vC hFtth.v (by eqm)
      have hvb := col_fact hbase (prodL [cc 5, cc betaC, notC hFttt.k]) v2C hFttt.v (by eqm)
      simp only [evalQ_prodL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        evalQ, evalQ_cc, notC, sel_one hs, hb, Rat.cast_one, one_mul, mul_one] at hboth hva hvb
      simp only [neGate, prodL, List.foldr, evalQ, evalQ_cc, sel_one hs, hb, Rat.cast_one, one_mul,
        mul_one] at hne
      have hdiff : Differ (hdF eF hFtth) (hdF eF hFttt) := by
        rcases hk9 with h9 | h9 <;> rcases hk10 with h10 | h10
        · right
          refine ⟨by simp [hdF, hdc, h9], by simp [hdF, hdc, h10], ?_⟩
          simp only [hdF, hdc]
          intro hnat
          have hx := natOf_inj hFe hnat
          rw [h9, h10] at hne
          rw [hva (by simp [h9]), hvb (by simp [h10]), hx] at hne
          simp at hne
        · left; simp [hdF, hdc, h9, h10]
        · left; simp [hdF, hdc, h9, h10]
        · exfalso; rw [h9, h10] at hboth; simp at hboth
      rcases hs.z1 with hz | hz
      · right
        have hpr : eF.trace prC = 1 := by rw [hs.pr, sel_one hs, hb, hz]; ring
        have hs1 : eF.trace hSf1.k = 1 := by
          have := arith_fact hbase (.mul (cc prC) (notC hSf1.k)) (by simp [arithGates])
          simp only [evalQ, evalQ_cc, notC, hpr, Rat.cast_one, one_mul, sub_eq_zero] at this
          exact this.symm
        have hs2 : eF.trace hSf2.k = 1 := by
          have := arith_fact hbase (.mul (cc prC) (notC hSf2.k)) (by simp [arithGates])
          simp only [evalQ, evalQ_cc, notC, hpr, Rat.cast_one, one_mul, sub_eq_zero] at this
          exact this.symm
        obtain ⟨m1, m2⟩ := pairmem hpr
        obtain ⟨X1, A1, hX1, hA1, hs1'⟩ := walk_rec D hP hSf1 hM.v hFtth m1 hs1
        obtain ⟨X2, A2, hX2, hA2, hs2'⟩ := walk_rec D hP hSf2 hM.v hFttt m2 hs2
        exact ⟨_, X1, X2, A1, A2, hX1, hX2, hs1', hs2', hA1, hA2, hdiff⟩
      · left
        have h1 := heq_fact hbase (prodL [cc 5, cc betaC, cc z1C]) hFtth hSf1 (by eqm) (by eqm)
          (by selv; simp [hb, hz])
        have h2 := heq_fact hbase (prodL [cc 5, cc betaC, cc z1C]) hFttt hSf2 (by eqm) (by eqm)
          (by selv; simp [hb, hz])
        show Differ (hdF eF hSf1) (hdF eF hSf2)
        rw [← h1, ← h2]; exact hdiff
  · -- OP6
    have httk : eF.trace hFtt.k = 1 := by
      have := arith_fact hbase (.mul (cc 6) (notC hFtt.k)) (by simp [arithGates])
      simp only [evalQ, evalQ_cc, notC, sel_one hs, Rat.cast_one, one_mul, sub_eq_zero] at this
      exact this.symm
    have hL3 := cell3_rec D hX hFtt hFtth hFttt (xmem hs slot2 (by simp [slots])
      ⟨[6], .const 1, cellRec hFtt hFtth hFttt, false⟩ (by simp [slot2]) rfl (by simp) (by simp [evalQ])) httk
    have hs2k : eF.trace hSf2.k = 0 := by
      have := arith_fact hbase (.mul (cc 6) (cc hSf2.k)) (by simp [arithGates])
      simpa [evalQ, evalQ_cc, sel_one hs] using this
    have hv := col_fact hbase (cc 6) vC hSf2.v (by eqm) (by selv)
    have hvb := arith_fact hbase (prodL [cc 6, cc vC, .sub (cc vC) (.const 1)]) (by simp [arithGates])
    simp only [evalQ_prodL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, evalQ, evalQ_cc,
      sel_one hs, Rat.cast_one, one_mul, mul_one] at hvb
    have he := heq_fact hbase (cc 6) hE hSf1 (by eqm) (by eqm) (by selv)
    refine ⟨L1, fhJ 6 (by decide) rfl, L2 (by simp [l2States]), hL3, natOf (eF.trace vC), ?_, ?_, ?_, he⟩
    · rcases bool_of hvb with h | h <;> rw [h] <;> simp [nat0, nat1]
    · show hdF eF hSf2 = _; rw [hdF, hdc_zero _ _ hs2k, hv]
    · rcases bool_of hvb with h | h
      · rw [h, nat0, if_pos rfl]
        exact heq_fact hbase (.mul (cc 6) (notC vC)) hM hFtth (by eqm) (by eqm)
          (by simp [evalQ, evalQ_cc, notC, sel_one hs, h])
      · rw [h, nat1, if_neg (by norm_num)]
        exact heq_fact hbase (.mul (cc 6) (cc vC)) hM hFttt (by eqm) (by eqm)
          (by simp [evalQ, evalQ_cc, sel_one hs, h])
  · -- OP7
    exact ⟨L1, fhJ 7 (by decide) rfl, L2 (by simp [l2States]),
      heq_fact hbase (cc 7) hE hSf1 (by eqm) (by eqm) (by selv)⟩
  · -- OP8
    have hmk : eF.trace hM.k = 1 := by
      have := arith_fact hbase (.mul (cc 8) (notC hM.k)) (by simp [arithGates])
      simp only [evalQ, evalQ_cc, notC, sel_one hs, Rat.cast_one, one_mul, sub_eq_zero] at this
      exact this.symm
    exact ⟨L1, fhJ 8 (by decide) rfl, L2 (by simp [l2States]),
      cell3_rec D hX hM hSf2 hS (xmem hs slot2 (by simp [slots])
        ⟨[8], .const 1, cellRec hM hSf2 hS, false⟩ (by simp [slot2]) rfl (by simp) (by simp [evalQ])) hmk,
      heq_fact hbase (cc 8) hE hSf1 (by eqm) (by eqm) (by selv)⟩
  · -- OP9
    have hthk : eF.trace hFth.k = 0 := by
      have := arith_fact hbase (.mul (cc 9) (cc hFth.k)) (by simp [arithGates])
      simpa [evalQ, evalQ_cc, sel_one hs] using this
    refine ⟨L1, fhJ 9 (by decide) rfl, L2 (by simp [l2States]),
      ⟨natOf (eF.trace hFth.v), by show hdF eF hFth = _; rw [hdF, hdc_zero _ _ hthk], ?_⟩,
      heq_fact hbase (cc 9) hE hSf2 (by eqm) (by eqm) (by selv)⟩
    rcases hs.z1 with hz | hz
    · right
      have hsk : eF.trace hSf1.k = 1 := by
        have := arith_fact hbase (prodL [cc 9, notC z1C, notC hSf1.k]) (by simp [arithGates])
        simp [evalQ_prodL, evalQ, evalQ_cc, notC, sel_one hs, hz, sub_eq_zero] at this
        exact this.symm
      exact walk_rec D hP hSf1 hFth.v hM (pmem hs slot2 (by simp [slots])
        ⟨[9], notC z1C, walkRec hSf1 hFth.v hM, true⟩ (by simp [slot2]) rfl (by simp)
        (by simp [evalQ, notC, evalQ_cc, hz])) hsk
    · left
      have hv1 : eF.trace vC = 1 := by
        have := arith_fact hbase (prodL [cc 9, cc z1C, .sub (cc vC) (.const 1)]) (by simp [arithGates])
        simp [evalQ_prodL, evalQ, evalQ_cc, sel_one hs, hz, sub_eq_zero] at this
        exact this
      have hvf := col_fact hbase (cc 9) vC hFth.v (by eqm) (by selv)
      exact ⟨by rw [← hvf, hv1, nat1],
        heq_fact hbase (.mul (cc 9) (cc z1C)) hM hSf1 (by eqm) (by eqm) (by selv; simp [hz])⟩
  · -- cons
    have hfh : eF.trace hFh.k = 1 := by
      have := arith_fact hbase (.sub (cc consCol) (cc hFh.k)) (by simp [arithGates])
      simp only [evalQ, evalQ_cc, consCol, sel_one hs] at this
      linear_combination -this
    have hek : eF.trace hE.k = 1 := by
      have := arith_fact hbase (.mul (cc consCol) (notC hE.k)) (by simp [arithGates])
      simp only [evalQ, evalQ_cc, notC, consCol, sel_one hs, Rat.cast_one, one_mul, sub_eq_zero] at this
      exact this.symm
    exact ⟨L1, by simp [rowOf, hdF, hdc, hfh],
      cell3_rec D hX hE hSf1 hSf2 (xmem hs slot2 (by simp [slots])
        ⟨[consCol], .const 1, cellRec hE hSf1 hSf2, false⟩ (by simp [slot2]) rfl (by simp [consCol])
        (by simp [evalQ])) hek⟩

end Facts

end

end Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
