/-
  Nock/NockVMROM/Thm54/VclL/Walk/WalkInstance.lean

  **The walk instance for the VCL path reads.**

  * Label `LT = St × DT`, `St = Bool × Bool` (continue L / R), `DT = (fp node, prefix, fp root,
    rootIdx, len)`.
  * `F X Dmax`: depth guard `len.val < Dmax`, the dynamic clause, and ONE export key
    `k = (p, l, r, idx) ∈ X` with `p = fp node` covering both children: child `b` has
    `fp = (b ? r : l)`, prefix `2p + b`, same fp root / rootIdx, `len + 1`.
  * `stateSep` (2-bit states, fanout `cL + cR`), `F_respects : RespectsChildLabels F Prod.snd`.
  * `enc : LT → Fin 15 → 𝕂` (each tower fp as its 6 `𝕂` coordinates, base entries through
    `algebraMap`), `enc_det` (label determination with `labelOf = Prod.snd`).
-/
import Nock.Walk
import Nock.NockVMROM.Thm54.P8Core.VclL.DyckRoot
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.WalkVCL

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.VclL
open Nock.ComputeTable (FP)

/-! ## 1. Label, F -/

@[ext] structure DT (q : ℕ) (Kfp : Type) where
  node : FP Kfp
  pre : ZMod q
  root : FP Kfp
  ridx : ZMod q
  len : ZMod q

abbrev St := Bool × Bool
abbrev LT (q : ℕ) (Kfp : Type) := St × DT q Kfp

def fanout (s : St) : ℕ := (if s.1 then 1 else 0) + (if s.2 then 1 else 0)

section Model
variable {q : ℕ} {Kfp : Type} [Field Kfp] [DecidableEq Kfp]

def bitZ (b : Bool) : ZMod q := if b then 1 else 0
def bitN (b : Bool) : ℕ := if b then 1 else 0

/-- The edge a row's export key `k = (p, l, r, idx)` gives at side `b` (`Chain.lean` `Edge`). -/
def keyEdge (k : XKey Kfp) (b : Bool) : Edge Kfp := ⟨k.1, k.2.1, k.2.2.1, b, k.2.2.2⟩

/-- The fingerprint the key names at side `b`. -/
def tgt (k : XKey Kfp) (b : Bool) : FP Kfp := childOf (keyEdge k b)

/-- The key an edge consumes. -/
def edgeKey (e : Edge Kfp) : XKey Kfp := (e.p, e.l, e.r, e.cellIdx)

def ChildOK (k : XKey Kfp) (b : Bool) (d : DT q Kfp) (c : LT q Kfp) : Prop :=
  c.2.node = tgt k b ∧ c.2.pre = 2 * d.pre + bitZ b ∧ c.2.root = d.root ∧ c.2.ridx = d.ridx ∧
    c.2.len = d.len + 1

def OptOK (k : XKey Kfp) (b : Bool) (d : DT q Kfp) (o : Option (LT q Kfp)) : Prop :=
  ∃ c, o = some c ∧ ChildOK k b d c

/-- **The walk labelling `F`** (min-diff, fp labels): depth guard, dynamic clause, one export key
of the node covering both children. -/
def F (X : List (XKey Kfp)) (Dmax : ℕ) (l : LT q Kfp) (xout : Fin 2 → Option (LT q Kfp)) : Prop :=
  l.2.len.val < Dmax ∧ (∀ i : Fin 2, ((i : ℕ) < fanout l.1 ↔ xout i ≠ none)) ∧
    ∃ k ∈ X, k.1 = l.2.node ∧ (l.1.1 = true → OptOK k false l.2 (xout 0)) ∧
      (l.1.2 = true → OptOK k true l.2 (xout (if l.1.1 then 1 else 0)))

/-! ## 2. `StateSep`, `RespectsChildLabels F Prod.snd` -/

theorem fanout_le (s : St) : fanout s ≤ 2 := by
  rcases s with ⟨_ | _, _ | _⟩ <;> simp [fanout]

theorem childLabel_zero_none {LT' : Type*} (t : NTree LT') (h : t.childLabel 0 = none) :
    t.isLeaf := by
  rcases t with ⟨l, ch⟩
  cases ch with
  | nil => rfl
  | cons c cs => simp [NTree.childLabel, NTree.childOpt] at h

def stateSep (X : List (XKey Kfp)) (Dmax : ℕ) : StateSep (F (q := q) X Dmax) where
  Sleaf s := fanout s = 0
  fanout := fanout
  fanout_le := fanout_le
  fanout_leaf _ h := h
  solely := by
    intro t hrvt
    rcases t with ⟨⟨s, d⟩, ch⟩
    have hF : F X Dmax (s, d) (fun i => (NTree.node (s, d) ch).childLabel i) := by
      unfold RVT at hrvt; exact hrvt.1
    have hdyn : 0 < fanout s ↔ (NTree.node (s, d) ch).childLabel 0 ≠ none := by
      simpa using hF.2.1 ⟨0, by norm_num⟩
    change fanout s = 0 ↔ _
    constructor
    · intro h0
      apply childLabel_zero_none
      by_contra hne
      have := hdyn.mpr hne
      omega
    · intro hleaf
      have hn : (NTree.node (s, d) ch).childLabel 0 = none := by
        simp [NTree.isLeaf] at hleaf; simp [NTree.childLabel, NTree.childOpt, hleaf]
      by_contra hne
      exact (hdyn.mp (by omega)) hn
  dynamic s d xout h := h.2.1

theorem optOK_congr {k : XKey Kfp} {b : Bool} {d : DT q Kfp} {o o' : Option (LT q Kfp)}
    (h : o.map Prod.snd = o'.map Prod.snd) (ho : OptOK k b d o) : OptOK k b d o' := by
  obtain ⟨c, rfl, hc⟩ := ho
  cases o' with
  | none => simp at h
  | some c' =>
    simp only [Option.map_some, Option.some.injEq] at h
    refine ⟨c', rfl, ?_⟩
    unfold ChildOK at hc ⊢
    rw [← h]; exact hc

/-- `F` reads children only through their data part (state not in the walk RLC). -/
theorem F_respects (X : List (XKey Kfp)) (Dmax : ℕ) :
    RespectsChildLabels (F (q := q) X Dmax) (Prod.snd : LT q Kfp → DT q Kfp) := by
  intro lbl xout xout' hx hF
  obtain ⟨hw, hdyn, k, hk, hki, h1, h2⟩ := hF
  have hnone : ∀ i, (xout i ≠ none ↔ xout' i ≠ none) := by
    intro i; have := hx i
    rcases h1 : xout i <;> rcases h2 : xout' i <;> simp_all
  exact ⟨hw, fun i => (hdyn i).trans (hnone i), k, hk, hki,
    fun hs => optOK_congr (hx 0) (h1 hs), fun hs => optOK_congr (hx _) (h2 hs)⟩

end Model

/-! ## 3. The walk RLC encoding over the coin field `𝕂` (`node_size = 15`) -/

section Enc
open Nock.NockVMROM.Thm54.T0Tower
variable {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod q) K] (δ : K) [Fact (¬ IsSquare δ)]

/-- **The walk RLC encoding, `node_size = 15`**: each tower fp `FP 𝕂′` as its 6 `𝕂` coordinates
(`Quad.re`/`Quad.im` of size, dyck, leaf), the base-field entries through `algebraMap`. -/
noncomputable def enc (a : LT q (Quad δ)) : Fin 15 → K :=
  ![Quad.re δ a.2.node.size, Quad.im δ a.2.node.size, Quad.re δ a.2.node.dyck,
    Quad.im δ a.2.node.dyck, Quad.re δ a.2.node.leaf, Quad.im δ a.2.node.leaf,
    algebraMap (ZMod q) K a.2.pre,
    Quad.re δ a.2.root.size, Quad.im δ a.2.root.size, Quad.re δ a.2.root.dyck,
    Quad.im δ a.2.root.dyck, Quad.re δ a.2.root.leaf, Quad.im δ a.2.root.leaf,
    algebraMap (ZMod q) K a.2.ridx, algebraMap (ZMod q) K a.2.len]

theorem quad_eq {x y : Quad δ} (h1 : Quad.re δ x = Quad.re δ y) (h2 : Quad.im δ x = Quad.im δ y) :
    x = y := by
  rw [← Quad.mk_re_im δ x, ← Quad.mk_re_im δ y, h1, h2]

/-- Label determination (`hEnc` of the forest theorem, `labelOf = Prod.snd`). -/
theorem enc_det : ∀ a b : LT q (Quad δ), enc δ a = enc δ b → a.2 = b.2 := by
  intro a b h
  have e : ∀ i : Fin 15, enc δ a i = enc δ b i := fun i => congrFun h i
  have hi := (algebraMap (ZMod q) K).injective
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8; have e9 := e 9
  have e10 := e 10; have e11 := e 11; have e12 := e 12; have e13 := e 13; have e14 := e 14
  simp only [enc] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  simp at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  exact DT.ext (FP.ext (quad_eq δ e0 e1) (quad_eq δ e2 e3) (quad_eq δ e4 e5)) e6
    (FP.ext (quad_eq δ e7 e8) (quad_eq δ e9 e10) (quad_eq δ e11 e12)) e13 e14

end Enc

end Nock.NockVMROM.Thm54.VclL.WalkVCL
