/-
  Nock/Jet/RapJetJ8.lean

* Rows: `rowJ P i` = the public layout row `lay i` + the witness columns `18..28` of the trace;
    `col_eq` (every base column but the masks is the trace's), `pre_eval` (preprocessing binding).
  * `base_rows` (J-3b's base gates on every row), `slot_val` (a tagged slot gate under one-hot
    selectors: `inv = den⁻¹`, `den ≠ 0`), `jet_telescope` (the tagged accumulator telescopes to the
    public `(pub₀, pub₁)`), **`jet_tagged_sum`** (the J share of the service balance:
    `Σ_{J consumes} den⁻¹ = T_J + Σ_{J in-chip provides} mv·den⁻¹ + Σ_{TAG_jet provides} m·den⁻¹`),
    **`jet_export_sum`** (the J export reads' terminal `(pub₂, pub₃)`, the J `T_ext` of the `x` balance).
  * **`bal_of_service`**: under the MERGED service identity (the J terminal + the other consumers =
    the other providers, at the J tagged coins), outside its weighted IO failure event, with the
    request count `< p` and the other providers' keys zero at entry 7: J-3b's `Accepted.bal`.
  * **`accepted_of_sat`**: an accepted `jetChipJ8` trace realizing the public layout is J-3b
    `Accepted` (layout, `small`, `uniq` are public-layout checks).
  * **`jetProvOK`**: every service provide of the J chip (the `TAG_jet` records AND the in-chip
    provides that share the accumulator) satisfies `RecOK` at `.s`: a `TAG_jet` record
    `(id, h_c, h_S, h_E, 3)` has `R id = (template, compile p T)`, `h_c ↦ compile p T`, and
    `T.rel S E` — through `jetChip_holds` with `MemoryBB` from `DenOKX`, the export reads' `RecOK .x`
    and the registry claim binding.
-/
import Nock.Jet.ChipJ8T
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
import Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.Jet.RapJetJ8

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp Nock.Jet.ChipJ8
open Nock.Framework Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX Cell3)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Keys -/

section Keys
variable {F : Type} [Field F]

/-- `tagLast` on values: `(t, x₁, …, x_k) ↦ (x₁, …, x_k, 0, …, 0, t)`. -/
def tlF (l : List F) : List F := l.tail ++ List.replicate (8 - l.length) 0 ++ l.take 1

theorem tagLast_map (f : ℕ → F) (l : List KE) : (tagLast l).map (KE.ev f) = tlF (l.map (KE.ev f)) := by
  simp [tagLast, tlF, List.map_tail, List.map_replicate, List.map_take, KE.ev]

theorem keysOf_entsT (es : List (Kd × List KE)) (r : CRow F) :
    keysOf (entsT es) r = (keysOf es r).map tlF := by
  simp only [keysOf, entsT, List.filter_map, List.map_map]
  congr 1
  funext x
  exact tagLast_map _ _

theorem selSum_entsT (rd : ℕ → CoeffExpr F) (es : List (Kd × List KE)) :
    ChipJ8.selSum rd (entsT es) = ChipJ8.selSum rd es := by
  simp [ChipJ8.selSum, CoeffExpr.sumList, entsT, List.foldr_map]

/-- The in-chip key shapes (J-3b): `(1, a, b, c, d)` or `(2, a, b, c)`. -/
def shapeB : List KE → Bool
  | [.k 1, _, _, _, _] => true
  | [.k 2, _, _, _] => true
  | _ => false

theorem shape_ev (f : ℕ → F) : ∀ l : List KE, shapeB l = true →
    (∃ a b c d : F, l.map (KE.ev f) = [((1 : ℕ) : F), a, b, c, d]) ∨
      ∃ a b c : F, l.map (KE.ev f) = [((2 : ℕ) : F), a, b, c]
  | [.k 1, x1, x2, x3, x4], _ => Or.inl ⟨_, _, _, _, rfl⟩
  | [.k 2, x1, x2, x3], _ => Or.inr ⟨_, _, _, rfl⟩
  | [], h => by simp [shapeB] at h
  | [_], h => by simp [shapeB] at h
  | [_, _], h => by simp [shapeB] at h
  | [_, _, _], h => by simp [shapeB] at h
  | [.col _, _, _, _], h => by simp [shapeB] at h
  | [.k 0, _, _, _], h => by simp [shapeB] at h
  | [.k 1, _, _, _], h => by simp [shapeB] at h
  | [.k (c + 3), _, _, _], h => by simp [shapeB] at h
  | [.col _, _, _, _, _], h => by simp [shapeB] at h
  | [.k 0, _, _, _, _], h => by simp [shapeB] at h
  | [.k 2, _, _, _, _], h => by simp [shapeB] at h
  | [.k (c + 3), _, _, _, _], h => by simp [shapeB] at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp [shapeB] at h

theorem ents_shape : (ents0.all fun e => shapeB e.2) = true ∧ (ents1.all fun e => shapeB e.2) = true ∧
    (ents2.all fun e => shapeB e.2) = true := by decide

theorem keysOf_shape {es : List (Kd × List KE)} (hes : (es.all fun e => shapeB e.2) = true) (r : CRow F) :
    ∀ κ ∈ keysOf es r, (∃ a b c d : F, κ = [((1 : ℕ) : F), a, b, c, d]) ∨
      ∃ a b c : F, κ = [((2 : ℕ) : F), a, b, c] := by
  intro κ hκ
  simp only [keysOf, List.mem_map, List.mem_filter] at hκ
  obtain ⟨e, ⟨he, -⟩, rfl⟩ := hκ
  exact shape_ev _ e.2 (List.all_eq_true.mp hes e he)

theorem consK_shape (r : CRow F) : ∀ κ ∈ consK r, (∃ a b c d : F, κ = [((1 : ℕ) : F), a, b, c, d]) ∨
    ∃ a b c : F, κ = [((2 : ℕ) : F), a, b, c] := by
  intro κ hκ
  rcases List.mem_append.mp hκ with h | h
  · exact keysOf_shape ents_shape.1 r κ h
  · exact keysOf_shape ents_shape.2.1 r κ h

theorem provK_shape (r : CRow F) : ∀ κ ∈ provK r, (∃ a b c d : F, κ = [((1 : ℕ) : F), a, b, c, d]) ∨
    ∃ a b c : F, κ = [((2 : ℕ) : F), a, b, c] :=
  keysOf_shape ents_shape.2.2 r

theorem tlF_one (a b c d : F) : tlF [((1 : ℕ) : F), a, b, c, d] = [a, b, c, d, 0, 0, 0, ((1 : ℕ) : F)] := rfl
theorem tlF_two (a b c : F) : tlF [((2 : ℕ) : F), a, b, c] = [a, b, c, 0, 0, 0, 0, ((2 : ℕ) : F)] := rfl

/-- `tlF` is injective on the in-chip shapes (needs `1 ≠ 2`). -/
theorem tlF_inj (h12 : ((1 : ℕ) : F) ≠ ((2 : ℕ) : F)) {κ κ' : List F}
    (hκ : (∃ a b c d : F, κ = [((1 : ℕ) : F), a, b, c, d]) ∨ ∃ a b c : F, κ = [((2 : ℕ) : F), a, b, c])
    (hκ' : (∃ a b c d : F, κ' = [((1 : ℕ) : F), a, b, c, d]) ∨ ∃ a b c : F, κ' = [((2 : ℕ) : F), a, b, c])
    (h : tlF κ = tlF κ') : κ = κ' := by
  rcases hκ with ⟨a, b, c, d, rfl⟩ | ⟨a, b, c, rfl⟩ <;>
    rcases hκ' with ⟨a', b', c', d', rfl⟩ | ⟨a', b', c', rfl⟩
  · rw [tlF_one, tlF_one] at h; simp only [List.cons.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h; rfl
  · rw [tlF_one, tlF_two] at h; simp only [List.cons.injEq] at h; exact absurd h.2.2.2.2.2.2.2.1 h12
  · rw [tlF_two, tlF_one] at h; simp only [List.cons.injEq] at h; exact absurd h.2.2.2.2.2.2.2.1.symm h12
  · rw [tlF_two, tlF_two] at h; simp only [List.cons.injEq] at h; obtain ⟨rfl, rfl, rfl, -⟩ := h; rfl

end Keys

/-! ## 2. Keys as vectors -/

section Vec
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- A key list as a width-`m` vector over `K` (zero-padded). -/
def keyK (m : ℕ) (κ : List F) : Fin m → K := fun c => algebraMap F K (κ.getD c 0)

theorem keyK_inj {m : ℕ} {κ κ' : List F} (h1 : κ.length = m) (h2 : κ'.length = m)
    (h : (keyK m κ : Fin m → K) = keyK m κ') : κ = κ' := by
  apply List.ext_getElem (h1.trans h2.symm)
  intro c hc hc'
  have := congrFun h ⟨c, h1 ▸ hc⟩
  simp only [keyK] at this
  have e := (algebraMap F K).injective this
  rwa [List.getD_eq_getElem _ _ hc, List.getD_eq_getElem _ _ hc'] at e

end Vec

/-! ## 3. `𝕂′` values of the J gates -/

section Eval
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

local notation "𝕂′" => Quad (algebraMap F K δ)

theorem gpowJ_ev (eK : Env K) (eF : Env F) (g : QE F) :
    ∀ k, (gpowJ δ g k).ev δ eK eF = (g.ev δ eK eF) ^ k
  | 0 => by simp [gpowJ, ev_one]
  | k + 1 => by rw [gpowJ, ev_mul, gpowJ_ev eK eF g k]; ring

theorem rlcJ_ev (eK : Env K) (eF : Env F) (g : QE F) : ∀ (l : List KE) (k : ℕ),
    (rlcJ δ g k l).ev δ eK eF =
      ∑ c ∈ Finset.range l.length, (g.ev δ eK eF) ^ (k + c) * liftQ δ ((l.getD c (.k 0)).expr.eval eF)
  | [], k => by simp [rlcJ, ev_zero]
  | e :: l, k => by
    rw [rlcJ, ev_add, ev_mul, ev_base, gpowJ_ev, rlcJ_ev eK eF g l (k + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show k + 1 + c = k + (c + 1) by omega]

/-- **A J key denominator is `compress` of the lifted (zero-padded) key** at the slot's coins. -/
theorem denJ_val (eK : Env K) (eF : Env F) (g ρ : QE F) (f : ℕ → F) (m : ℕ) (l : List KE)
    (hl : l.length ≤ m) (hag : ∀ x ∈ l, x.expr.eval eF = KE.ev f x) :
    (denJ δ g ρ l).ev δ eK eF =
      compress ⟨g.ev δ eK eF, ρ.ev δ eK eF⟩ (liftRec (L := 𝕂′) (keyK (K := K) m (l.map (KE.ev f)))) := by
  rw [denJ, ev_add, rlcJ_ev]
  simp only [compress, Walk.rlc, liftRec, keyK, zero_add]
  congr 1
  have key : ∀ c, (g.ev δ eK eF) ^ c * liftQ δ ((l.getD c (.k 0)).expr.eval eF) =
      (g.ev δ eK eF) ^ c * algebraMap K 𝕂′ (algebraMap F K ((l.map (KE.ev f)).getD c 0)) := by
    intro c
    by_cases hc : c < l.length
    · rw [List.getD_eq_getElem _ _ hc, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map,
        hag _ (List.getElem_mem hc)]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
      simp [KE.expr, CoeffExpr.eval]
  rw [Finset.sum_congr rfl (fun c _ => key c),
    Fin.sum_univ_eq_sum_range (fun c => (g.ev δ eK eF) ^ c *
      algebraMap K 𝕂′ (algebraMap F K ((l.map (KE.ev f)).getD c 0))) m]
  refine Finset.sum_subset (Finset.range_mono hl) fun c _ hc => ?_
  rw [Finset.mem_range] at hc
  rw [List.getD_eq_default _ _ (by simp; omega)]
  simp

theorem sumQE_ev (eK : Env K) (eF : Env F) :
    ∀ l : List (QE F), (sumQE l).ev δ eK eF = (l.map fun e => e.ev δ eK eF).sum
  | [] => by simp [sumQE, ev_zero]
  | e :: l => by
    show (QE.add e (sumQE l)).ev δ eK eF = _
    rw [ev_add, sumQE_ev eK eF l]
    simp

theorem sum_sel_filter (kd : Kd) (sel : Kd → F) (hsel : ∀ k, sel k = if k = kd then 1 else 0)
    (f : Kd × List KE → 𝕂′) : ∀ es : List (Kd × List KE),
    (es.map fun e => liftQ δ (sel e.1) * f e).sum = ((es.filter fun e => e.1 == kd).map f).sum
  | [] => by simp
  | e :: es => by
    rw [List.map_cons, List.sum_cons, sum_sel_filter kd sel hsel f es, hsel]
    by_cases he : e.1 = kd
    · simp [he, List.filter_cons, liftQ]
    · simp [he, List.filter_cons, liftQ]

theorem sel_count (kd : Kd) (sel : Kd → F) (hsel : ∀ k, sel k = if k = kd then 1 else 0) :
    ∀ es : List (Kd × List KE),
    (es.map fun e => sel e.1).sum = ((es.filter fun e => e.1 == kd).length : F)
  | [] => by simp
  | e :: es => by
    rw [List.map_cons, List.sum_cons, sel_count kd sel hsel es, hsel]
    by_cases he : e.1 = kd
    · simp [he, List.filter_cons]; ring
    · simp [he, List.filter_cons]

theorem filter_le_one (kd : Kd) (es : List (Kd × List KE)) (hnd : (es.map Prod.fst).Nodup) :
    (es.filter fun e => e.1 == kd) = [] ∨ ∃ e ∈ es, e.1 = kd ∧ (es.filter fun e => e.1 == kd) = [e] := by
  have hnd' : ((es.filter fun e => e.1 == kd).map Prod.fst).Nodup :=
    hnd.sublist (List.Sublist.map _ List.filter_sublist)
  have hall : ∀ e ∈ es.filter (fun e => e.1 == kd), e ∈ es ∧ e.1 = kd := fun e he => by
    rw [List.mem_filter] at he; exact ⟨he.1, by simpa using he.2⟩
  generalize es.filter (fun e => e.1 == kd) = fl at hnd' hall ⊢
  match fl, hnd', hall with
  | [], _, _ => exact Or.inl rfl
  | [e], _, hall => exact Or.inr ⟨e, (hall e (by simp)).1, (hall e (by simp)).2, rfl⟩
  | a :: b :: t, hnd', hall =>
    have ha := (hall a (by simp)).2
    have hb := (hall b (by simp)).2
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnd'
    exact absurd (Or.inl (ha.trans hb.symm)) hnd'.1

/-- **The slot lemma.**  At a row whose selectors are one-hot at its kind, a slot gate with
pairwise distinct kinds gives: every key the row puts in the slot has a nonzero denominator, and
`Σ sel · inv = Σ_{keys} den⁻¹`. -/
theorem slot_val (eK : Env K) (eF : Env F) (r : CRow F) (g ρ : QE F) (inv m : ℕ)
    (es : List (Kd × List KE))
    (hsel : ∀ k : Kd, eF.trace k.sel = if k = r.pre.kd then 1 else 0)
    (hnd : (es.map Prod.fst).Nodup)
    (hes : ∀ e ∈ es, e.2.length ≤ m ∧ ∀ x ∈ e.2, x.expr.eval eF = KE.ev (colOf r) x)
    (hg : (slotGate δ g ρ inv es).ev δ eK eF = 0) :
    (∀ κ ∈ keysOf es r, compress ⟨g.ev δ eK eF, ρ.ev δ eK eF⟩ (liftRec (L := 𝕂′) (keyK (K := K) m κ)) ≠ 0) ∧
    liftQ δ ((ChipJ8.selSum cv es).eval eF) * Quad.mk _ (eK.trace inv) (eK.trace (inv + 1)) =
      ((keysOf es r).map fun κ =>
        (compress ⟨g.ev δ eK eF, ρ.ev δ eK eF⟩ (liftRec (L := 𝕂′) (keyK (K := K) m κ)))⁻¹).sum := by
  set D : List F → 𝕂′ := fun κ =>
    compress ⟨g.ev δ eK eF, ρ.ev δ eK eF⟩ (liftRec (L := 𝕂′) (keyK (K := K) m κ)) with hD
  have hden : ∀ e ∈ es, (denJ δ g ρ e.2).ev δ eK eF = D (e.2.map (KE.ev (colOf r))) := fun e he =>
    denJ_val δ eK eF g ρ (colOf r) m e.2 (hes e he).1 (hes e he).2
  have hsel' : ∀ k, (fun k : Kd => eF.trace k.sel) k = if k = r.pre.kd then 1 else 0 := hsel
  have hsum : (ChipJ8.selSum (cv (F := F)) es).eval eF =
      ((es.filter fun e => e.1 == r.pre.kd).length : F) := by
    rw [ChipJ8.selSum, CoeffExpr.eval_sumList]
    exact sel_count r.pre.kd _ hsel' es
  unfold slotGate at hg
  rw [ev_sub, ev_mul, ev_var, sumQE_ev, ev_base, hsum, List.map_map] at hg
  have hg2 : (es.map fun e => (QE.scale (cv e.1.sel) (denJ δ g ρ e.2)).ev δ eK eF) =
      es.map fun e => liftQ δ (eF.trace e.1.sel) * D (e.2.map (KE.ev (colOf r))) := by
    refine List.map_congr_left fun e he => ?_
    rw [ev_scale, hden e he]; rfl
  rw [Function.comp_def, hg2, sum_sel_filter δ r.pre.kd _ hsel'
    (fun e => D (e.2.map (KE.ev (colOf r)))) es] at hg
  have hk : keysOf es r = (es.filter fun e => e.1 == r.pre.kd).map fun e => e.2.map (KE.ev (colOf r)) := rfl
  rw [hsum, hk]
  rcases filter_le_one r.pre.kd es hnd with h0 | ⟨e, he, -, h1⟩
  · rw [h0]; simp
  · rw [h1] at hg ⊢
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_singleton,
      Nat.cast_one, map_one, sub_eq_zero] at hg ⊢
    have h1' : liftQ (K := K) δ (1 : F) = 1 := by simp [liftQ]
    rw [h1'] at hg ⊢
    refine ⟨fun κ hκ => ?_, ?_⟩
    · rw [List.mem_singleton] at hκ; subst hκ; exact right_ne_zero_of_mul_eq_one hg
    · rw [one_mul]; exact eq_inv_of_mul_eq_one_left hg

theorem contribT_next (eK eK' : Env K) (eF eF' : Env F) (hF : ∀ j, eF.traceNext j = eF'.trace j)
    (hK : ∀ j, eK.traceNext j = eK'.trace j) :
    (contribT nv QE.next).ev δ eK eF = (contribT cv QE.var).ev δ eK' eF' := by
  simp only [contribT, sumQE, List.foldr, ev_add, ev_scale, ev_next, ev_var, ev_zero, ChipJ8.selSum,
    CoeffExpr.eval_sumList, CoeffExpr.eval, hF, hK]

theorem contribX_next (eK eK' : Env K) (eF eF' : Env F) (hF : ∀ j, eF.traceNext j = eF'.trace j)
    (hK : ∀ j, eK.traceNext j = eK'.trace j) :
    (contribX nv QE.next).ev δ eK eF = (contribX cv QE.var).ev δ eK' eF' := by
  simp only [contribX, ev_scale, ev_next, ev_var, ChipJ8.selSum, CoeffExpr.eval_sumList, CoeffExpr.eval, hF, hK]

theorem sum_flatMap {α β M : Type} [AddCommMonoid M] (f : α → List β) (g : β → M) :
    ∀ l : List α, ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum
  | [] => by simp
  | a :: l => by simp [List.flatMap_cons, List.sum_append, sum_flatMap f g l]

end Eval

/-! ## 4. The rows of a `jetChipJ8` trace -/

/-- Row `i`'s base-field environment. -/
abbrev jEF {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ}
    (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K) {w : ℕ}
    (Q : Fin w → (ZMod p)[X]) (i : Fin n) : Env (ZMod p) :=
  Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 29 chals) (slotVal b 29 pubs)

/-- Row `i`'s gathered `𝕂` environment. -/
abbrev jEK {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (δ : ZMod p) (b : Basis (Fin 3) (ZMod p) K)
    {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K) {w : ℕ}
    (Q : Fin w → (ZMod p)[X]) (i : Fin n) : Env K :=
  gatherEnv b ((jetTemplateJ8T δ).col0 3) (jEF b nodes orbit chals pubs Q i)

/-- **Row `i` as a J-3b row**: the public layout row, the witness columns `18..28` of the trace. -/
def rowJ {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ}
    (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
    (lay : Fin n → PRow) {w : ℕ} (Q : Fin w → (ZMod p)[X]) (i : Fin n) : CRow (ZMod p) :=
  ⟨lay i, ⟨(jEF b nodes orbit chals pubs Q i).trace 18, (jEF b nodes orbit chals pubs Q i).trace 19,
    (jEF b nodes orbit chals pubs Q i).trace 20, (jEF b nodes orbit chals pubs Q i).trace 21,
    (jEF b nodes orbit chals pubs Q i).trace 22, (jEF b nodes orbit chals pubs Q i).trace 23,
    (jEF b nodes orbit chals pubs Q i).trace 24, (jEF b nodes orbit chals pubs Q i).trace 25,
    (jEF b nodes orbit chals pubs Q i).trace 26, (jEF b nodes orbit chals pubs Q i).trace 27,
    (jEF b nodes orbit chals pubs Q i).trace 28⟩⟩

/-- The tag-last in-chip consumes / provides of a row. -/
def consKT {F : Type} [Field F] (r : CRow F) : List (List F) := keysOf ents0T r ++ keysOf ents1T r
def provKT {F : Type} [Field F] (r : CRow F) : List (List F) := keysOf ents2T r

theorem consKT_eq {F : Type} [Field F] (r : CRow F) : consKT r = (consK r).map tlF := by
  simp [consKT, consK, ents0T, ents1T, keysOf_entsT]
theorem provKT_eq {F : Type} [Field F] (r : CRow F) : provKT r = (provK r).map tlF := by
  simp [provKT, provK, ents2T, keysOf_entsT]

/-- Column / length check of a slot's key table. -/
def colsOK (m : ℕ) (es : List (Kd × List KE)) : Bool :=
  es.all fun e => decide (e.2.length ≤ m) && e.2.all fun x => match x with
    | .col j => decide (j < 29 ∧ j ≠ 11 ∧ j ≠ 12)
    | .k _ => true

theorem colsOK_all : colsOK 8 ents0T = true ∧ colsOK 8 ents1T = true ∧ colsOK 8 ents2T = true ∧
    colsOK 8 ents3 = true ∧ colsOK 5 entsX = true := by decide

theorem kinds_nodup : (ents0T.map Prod.fst).Nodup ∧ (ents1T.map Prod.fst).Nodup ∧
    (ents2T.map Prod.fst).Nodup ∧ (ents3.map Prod.fst).Nodup ∧ (entsX.map Prod.fst).Nodup := by decide

/-- The J chip's tagged coins `(γ, ρ) = ((χ₀, χ₂), (χ₁, χ₃))`. -/
def coinsJ {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (δ : ZMod p) (chals : ℕ → K) :
    IOCoins (Quad (algebraMap (ZMod p) K δ)) :=
  ⟨Quad.mk _ (chals 0) (chals 2), Quad.mk _ (chals 1) (chals 3)⟩

/-- The J chip's export coins `((χ₄, χ₆), (χ₅, χ₇))`. -/
def coinsJX {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (δ : ZMod p) (chals : ℕ → K) :
    IOCoins (Quad (algebraMap (ZMod p) K δ)) :=
  ⟨Quad.mk _ (chals 4) (chals 6), Quad.mk _ (chals 5) (chals 7)⟩

/-- `den⁻¹` of a tagged key at the J coins. -/
abbrev dJ {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (δ : ZMod p)
    [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (chals : ℕ → K) (κ : List (ZMod p)) :
    Quad (algebraMap (ZMod p) K δ) :=
  (compress (coinsJ δ chals) (liftRec (keyK (K := K) 8 κ)))⁻¹

/-- `den⁻¹` of an export key at the J export coins. -/
abbrev dJX {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (δ : ZMod p)
    [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (chals : ℕ → K) (κ : List (ZMod p)) :
    Quad (algebraMap (ZMod p) K δ) :=
  (compress (coinsJX δ chals) (liftRec (keyK (K := K) 5 κ)))⁻¹


/-! ## 5. The trace's key lists -/

/-- The rows of the trace. -/
def rowsJ {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (b : Basis (Fin 3) (ZMod p) K)
    {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
    (lay : Fin n → PRow) {w : ℕ} (Q : Fin w → (ZMod p)[X]) : List (CRow (ZMod p)) :=
  List.ofFn (rowJ b nodes orbit chals pubs lay Q)

/-- **The J consumes** (in-chip, tag-last, 8 entries) of the trace, as `K`-vectors. -/
def jCons {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (b : Basis (Fin 3) (ZMod p) K)
    {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
    (lay : Fin n → PRow) {w : ℕ} (Q : Fin w → (ZMod p)[X]) : List (Fin 8 → K) :=
  (List.finRange n).flatMap fun i => (consKT (rowJ b nodes orbit chals pubs lay Q i)).map (keyK 8)

/-- **The J providers of the service accumulator**: per row, the in-chip provides (multiplicity
`mv`) and the `TAG_jet` provide (multiplicity `m`). -/
def jProv {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (b : Basis (Fin 3) (ZMod p) K)
    {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
    (lay : Fin n → PRow) {w : ℕ} (Q : Fin w → (ZMod p)[X]) : List ((Fin 8 → K) × K) :=
  (List.finRange n).flatMap fun i =>
    (provKT (rowJ b nodes orbit chals pubs lay Q i)).map
        (fun κ => (keyK 8 κ, algebraMap (ZMod p) K (rowJ b nodes orbit chals pubs lay Q i).w.mv)) ++
      (keysOf ents3 (rowJ b nodes orbit chals pubs lay Q i)).map
        (fun κ => (keyK 8 κ, algebraMap (ZMod p) K (rowJ b nodes orbit chals pubs lay Q i).w.m))

/-- **The J export reads** (5 entries, `keyH` shape) — the J consumers of the cell export balance. -/
def jRd {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] (b : Basis (Fin 3) (ZMod p) K)
    {h n : ℕ} (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
    (lay : Fin n → PRow) {w : ℕ} (Q : Fin w → (ZMod p)[X]) : List (Fin 5 → K) :=
  (List.finRange n).flatMap fun i => (keysOf entsX (rowJ b nodes orbit chals pubs lay Q i)).map (keyK 5)

section Rows
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "EF" => jEF b nodes orbit chals pubs P
local notation "EK" => jEK δ b nodes orbit chals pubs P
local notation "RJ" => rowJ b nodes orbit chals pubs lay P

theorem pre_eval (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) {j : ℕ} (hj : j < 18) :
    (EF i).trace j = jetPre lay j i := by
  have hw : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w = 71 :=
    jetChipJ8_width δ b nodes orbit chals pubs lay
  rw [envOfTrace_trace P _ _ _ _ (show j < (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w by
    rw [hw]; omega)]
  have e : P ⟨j, by rw [hw]; omega⟩ = Lagrange.interpolate Finset.univ nodes (fun i => jetPre lay j i) :=
    hbind ⟨j, hj⟩
  rw [e]
  exact Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

/-- **Every base column but the masks is the trace's.** -/
theorem col_eq (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) {j : ℕ} (hj : j < 29) (h11 : j ≠ 11) (h12 : j ≠ 12) :
    colOf (RJ i) j = (EF i).trace j := by
  by_cases h18 : j < 18
  · rw [pre_eval hbind hinj i h18]
    interval_cases j <;> simp_all [colOf, rowJ, jetPre, preCol] <;> rfl
  · interval_cases j <;> first | omega | rfl

theorem sel_eq (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) (k : Kd) :
    (EF i).trace k.sel = if k = (RJ i).pre.kd then 1 else 0 := by
  rw [pre_eval hbind hinj i (by cases k <;> decide)]
  show jetPre lay k.sel i = if k = (lay i).kd then 1 else 0
  have h11 : k.sel ≠ 11 := by cases k <;> decide
  have h12 : k.sel ≠ 12 := by cases k <;> decide
  have h0 : k.sel < 11 := by cases k <;> decide
  simp only [jetPre, if_neg h11, if_neg h12, preCol, if_pos h0]
  generalize (lay i).kd = kd
  cases k <;> cases kd <;> simp [Kd.sel]

theorem masks (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (EF i).trace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (EF i).trace 12 = (if (i : ℕ) = n - 1 then 1 else 0) := by
  rw [pre_eval hbind hinj i (by norm_num), pre_eval hbind hinj i (by norm_num)]
  simp [jetPre]

theorem sat_lang (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P) (i : Fin n) :
    (∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (EF i) = 0) ∧
      ∀ e ∈ slotGatesT δ ++ accGates, e.ev δ (EK i) (EF i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (jetTemplateJ8T δ) b _ _ orbit _ P).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  exact ⟨hl.1, fun e he => ev_eq_zero_of_gates δ _ _ e fun g hg =>
    hl.2.2.2 g (List.mem_flatMap.mpr ⟨e, he, hg⟩)⟩

/-- **J-3b's base gates hold on every row.** -/
theorem base_row (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) :
    ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod p))), g.eval (envOf (RJ i)) = 0 := by
  have hb := (sat_lang hsat i).1
  have c := fun j (hj : j < 29) (h11 : j ≠ 11) (h12 : j ≠ 12) => col_eq hbind hinj i hj h11 h12
  have e2 := c 2 (by norm_num) (by norm_num) (by norm_num)
  have e3 := c 3 (by norm_num) (by norm_num) (by norm_num)
  have e4 := c 4 (by norm_num) (by norm_num) (by norm_num)
  have e5 := c 5 (by norm_num) (by norm_num) (by norm_num)
  have e6 := c 6 (by norm_num) (by norm_num) (by norm_num)
  have e7 := c 7 (by norm_num) (by norm_num) (by norm_num)
  have e16 := c 16 (by norm_num) (by norm_num) (by norm_num)
  have e20 := c 20 (by norm_num) (by norm_num) (by norm_num)
  have e21 := c 21 (by norm_num) (by norm_num) (by norm_num)
  have e22 := c 22 (by norm_num) (by norm_num) (by norm_num)
  have e23 := c 23 (by norm_num) (by norm_num) (by norm_num)
  intro g hg
  have := hb g hg
  simp only [baseGatesJ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
  · simp only [CoeffExpr.eval, envOf, cv, Kd.sel, Col.val, Col.n1, Col.v1, Col.v2, Col.kN] at this ⊢
    simp only [e2, e3, e4, e5, e6, e7, e16, e20, e21, e22, e23]
    exact this

theorem hes_of (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) {m : ℕ} {es : List (Kd × List KE)}
    (hok : colsOK m es = true) :
    ∀ e ∈ es, e.2.length ≤ m ∧ ∀ x ∈ e.2, x.expr.eval (EF i) = KE.ev (colOf (RJ i)) x := by
  intro e he
  have h1 := List.all_eq_true.mp hok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨h1.1, fun x hx => ?_⟩
  have h2 := List.all_eq_true.mp h1.2 x hx
  cases x with
  | col j =>
    simp only [decide_eq_true_eq] at h2
    simp only [KE.expr, KE.ev, cv, CoeffExpr.eval]
    exact (col_eq hbind hinj i h2.1 h2.2.1 h2.2.2).symm
  | k c => simp [KE.expr, KE.ev, CoeffExpr.eval]

theorem coinsJ_ev (i : Fin n) :
    (⟨(gamT : QE (ZMod p)).ev δ (EK i) (EF i), (rhoT : QE (ZMod p)).ev δ (EK i) (EF i)⟩ : IOCoins 𝕂′) =
      coinsJ δ chals := by
  simp only [gamT, rhoT, ev_chal, coinsJ,
    TeleH.gather_chal_T b (jetTemplateJ8T δ) 29 (jetTemplateJ8T_baseCols δ) (EF i) chals rfl]

theorem coinsJX_ev (i : Fin n) :
    (⟨(gamX : QE (ZMod p)).ev δ (EK i) (EF i), (rhoX : QE (ZMod p)).ev δ (EK i) (EF i)⟩ : IOCoins 𝕂′) =
      coinsJX δ chals := by
  simp only [gamX, rhoX, ev_chal, coinsJX,
    TeleH.gather_chal_T b (jetTemplateJ8T δ) 29 (jetTemplateJ8T_baseCols δ) (EF i) chals rfl]

/-- The slot facts of row `i` (tagged slots at the J coins). -/
theorem slotT (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) (inv : ℕ) (es : List (Kd × List KE))
    (hnd : (es.map Prod.fst).Nodup) (hok : colsOK 8 es = true)
    (hg : slotGate δ gamT rhoT inv es ∈ slotGatesT δ ++ accGates) :
    (∀ κ ∈ keysOf es (RJ i), compress (coinsJ δ chals) (liftRec (keyK (K := K) 8 κ)) ≠ 0) ∧
    liftQ δ ((ChipJ8.selSum cv es).eval (EF i)) * Quad.mk _ ((EK i).trace inv) ((EK i).trace (inv + 1)) =
      ((keysOf es (RJ i)).map (dJ δ chals)).sum := by
  have := slot_val δ (EK i) (EF i) (RJ i) gamT rhoT inv 8 es (sel_eq hbind hinj i) hnd
    (hes_of hbind hinj i hok) ((sat_lang hsat i).2 _ hg)
  rwa [coinsJ_ev] at this

/-- **The row term of the tagged accumulator.** -/
theorem termT_eq (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (contribT cv QE.var).ev δ (EK i) (EF i) =
      ((consKT (RJ i)).map (dJ δ chals)).sum
        - liftQ δ ((EF i).trace 19) * ((provKT (RJ i)).map (dJ δ chals)).sum
        - liftQ δ ((EF i).trace 18) * ((keysOf ents3 (RJ i)).map (dJ δ chals)).sum := by
  obtain ⟨-, s0⟩ := slotT hsat hbind hinj i Col.inv0 ents0T kinds_nodup.1 colsOK_all.1 (by simp [slotGatesT])
  obtain ⟨-, s1⟩ := slotT hsat hbind hinj i Col.inv1 ents1T kinds_nodup.2.1 colsOK_all.2.1
    (by simp [slotGatesT])
  obtain ⟨-, s2⟩ := slotT hsat hbind hinj i Col.inv2 ents2T kinds_nodup.2.2.1 colsOK_all.2.2.1
    (by simp [slotGatesT])
  obtain ⟨-, s3⟩ := slotT hsat hbind hinj i Col.inv3 ents3 kinds_nodup.2.2.2.1 colsOK_all.2.2.2.1
    (by simp [slotGatesT])
  rw [show ChipJ8.selSum (cv (F := ZMod p)) ents0T = ChipJ8.selSum cv ents0 from selSum_entsT _ _] at s0
  rw [show ChipJ8.selSum (cv (F := ZMod p)) ents1T = ChipJ8.selSum cv ents1 from selSum_entsT _ _] at s1
  rw [show ChipJ8.selSum (cv (F := ZMod p)) ents2T = ChipJ8.selSum cv ents2 from selSum_entsT _ _] at s2
  have h3 : (ChipJ8.selSum (cv (F := ZMod p)) ents3).eval (EF i) = (EF i).trace (Kd.sel .call) := by
    simp [ChipJ8.selSum, CoeffExpr.sumList, ents3, CoeffExpr.eval]
  rw [h3] at s3
  rw [consKT, provKT, List.map_append, List.sum_append, ← s0, ← s1, ← s2, ← s3]
  simp only [contribT, sumQE, List.foldr, ev_add, ev_scale, ev_var, ev_zero, CoeffExpr.eval, cv, Col.mv,
    Col.m, liftQ, map_neg, map_mul]
  ring

theorem next_F (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) : ∀ j, (EF i).traceNext j = (EF ⟨(i : ℕ) + 1, hi⟩).trace j :=
  fun j => traceNext_eq nodes orbit P _ _ hadj i hi j

theorem next_K (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) : ∀ j, (EK i).traceNext j = (EK ⟨(i : ℕ) + 1, hi⟩).trace j :=
  fun j => TeleH.gather_next_T b _ _ _ (next_F hadj i hi) j

/-- **The tagged accumulator telescopes to the public `(pub₀, pub₁)`.** -/
theorem jet_telescope (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i, (contribT cv QE.var).ev δ (EK i) (EF i) = Quad.mk _ (pubs 0) (pubs 1) := by
  have hg := fun i => (sat_lang hsat i).2
  refine TeleHQ.qTelescope δ hn (fun i => (EF i).trace 11) (fun i => (EF i).trace 12)
    (fun i => Quad.mk _ ((EK i).trace 10) ((EK i).trace 11)) _ _
    (fun i => (masks hbind hinj i).1) (fun i => (masks hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i (QE.scale (cv Col.isFirst) (QE.sub (QE.var Col.accT) (contribT cv QE.var)))
      (by simp [accGates])
    rw [ev_scale, ev_sub, ev_var] at g
    simpa only [cv, CoeffExpr.eval, Col.isFirst, Col.accT] using g
  · intro i hi
    have g := hg i (QE.scale (notE (cv Col.isLast)) (QE.sub (QE.sub (QE.next Col.accT) (QE.var Col.accT))
      (contribT nv QE.next))) (by simp [accGates])
    rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var,
      contribT_next δ _ _ _ _ (next_F hadj i hi) (next_K hadj i hi)] at g
    simp only [notE, cv, CoeffExpr.eval, Col.isLast, Col.accT, next_K hadj i hi] at g
    simpa only [liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i (QE.scale (cv Col.isLast) (QE.sub (QE.var Col.accT) (QE.pub 0))) (by simp [accGates])
    rw [ev_scale, ev_sub, ev_var, ev_pub,
      TeleH.gather_pub_T b (jetTemplateJ8T δ) 29 (jetTemplateJ8T_baseCols δ) (EF i) pubs rfl,
      TeleH.gather_pub_T b (jetTemplateJ8T δ) 29 (jetTemplateJ8T_baseCols δ) (EF i) pubs rfl] at g
    simpa only [cv, CoeffExpr.eval, Col.isLast, Col.accT] using g

/-- **The J share of the service balance** (the tagged telescope, per key):
`Σ_{J consumes} den⁻¹ = (pub₀, pub₁) + Σ_{J providers} mult · den⁻¹` at the J coins. -/
theorem jet_tagged_sum (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((jCons b nodes orbit chals pubs lay P).map fun c =>
        (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      Quad.mk _ (pubs 0) (pubs 1) + ((jProv b nodes orbit chals pubs lay P).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
  have ht := jet_telescope hsat hbind hinj hn hadj
  rw [Fin.sum_univ_def] at ht
  have hi : ∀ i : Fin n, (((consKT (RJ i)).map (keyK (K := K) 8)).map fun c =>
        (compress (coinsJ δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum =
      (contribT cv QE.var).ev δ (EK i) (EF i) +
        (((provKT (RJ i)).map (fun κ => (keyK 8 κ, algebraMap (ZMod p) K (RJ i).w.mv)) ++
          (keysOf ents3 (RJ i)).map (fun κ => (keyK 8 κ, algebraMap (ZMod p) K (RJ i).w.m))).map
            fun (q : (Fin 8 → K) × K) => algebraMap K 𝕂′ q.2 * (compress (coinsJ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
    intro i
    rw [termT_eq hsat hbind hinj i]
    simp only [List.map_map, Function.comp_def, List.map_append, List.sum_append, List.sum_map_mul_left]
    have hmv : (RJ i).w.mv = (EF i).trace 19 := rfl
    have hm : (RJ i).w.m = (EF i).trace 18 := rfl
    rw [hmv, hm]
    ring
  rw [jCons, jProv, sum_flatMap, sum_flatMap, List.map_congr_left (fun i _ => hi i), List.sum_map_add, ht]

theorem slotX (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (∀ κ ∈ keysOf entsX (RJ i), compress (coinsJX δ chals) (liftRec (keyK (K := K) 5 κ)) ≠ 0) ∧
    liftQ δ ((ChipJ8.selSum cv entsX).eval (EF i)) *
        Quad.mk _ ((EK i).trace Col.invX) ((EK i).trace (Col.invX + 1)) =
      ((keysOf entsX (RJ i)).map (dJX δ chals)).sum := by
  have := slot_val δ (EK i) (EF i) (RJ i) gamX rhoX Col.invX 5 entsX (sel_eq hbind hinj i)
    kinds_nodup.2.2.2.2 (hes_of hbind hinj i colsOK_all.2.2.2.2)
    ((sat_lang hsat i).2 _ (by simp [slotGatesT]))
  rwa [coinsJX_ev] at this

/-- **The J export reads' terminal**: `Σ_{J reads} den⁻¹ = (pub₂, pub₃)` at the J export coins (the J
`T_ext` of the cell export balance `x`). -/
theorem jet_export_sum (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((jRd b nodes orbit chals pubs lay P).map fun c =>
        (compress (coinsJX δ chals) (liftRec (L := 𝕂′) c))⁻¹).sum = Quad.mk _ (pubs 2) (pubs 3) := by
  have hg := fun i => (sat_lang hsat i).2
  have ht : ∑ i, (contribX cv QE.var).ev δ (EK i) (EF i) = Quad.mk _ (pubs 2) (pubs 3) := by
    refine TeleHQ.qTelescope δ hn (fun i => (EF i).trace 11) (fun i => (EF i).trace 12)
      (fun i => Quad.mk _ ((EK i).trace 12) ((EK i).trace 13)) _ _
      (fun i => (masks hbind hinj i).1) (fun i => (masks hbind hinj i).2) ?_ ?_ ?_
    · intro i
      have g := hg i (QE.scale (cv Col.isFirst) (QE.sub (QE.var Col.accX) (contribX cv QE.var)))
        (by simp [accGates])
      rw [ev_scale, ev_sub, ev_var] at g
      simpa only [cv, CoeffExpr.eval, Col.isFirst, Col.accX] using g
    · intro i hi
      have g := hg i (QE.scale (notE (cv Col.isLast)) (QE.sub (QE.sub (QE.next Col.accX) (QE.var Col.accX))
        (contribX nv QE.next))) (by simp [accGates])
      rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var,
        contribX_next δ _ _ _ _ (next_F hadj i hi) (next_K hadj i hi)] at g
      simp only [notE, cv, CoeffExpr.eval, Col.isLast, Col.accX, next_K hadj i hi] at g
      simpa only [liftQ, map_sub, map_one] using g
    · intro i
      have g := hg i (QE.scale (cv Col.isLast) (QE.sub (QE.var Col.accX) (QE.pub 2))) (by simp [accGates])
      rw [ev_scale, ev_sub, ev_var, ev_pub,
        TeleH.gather_pub_T b (jetTemplateJ8T δ) 29 (jetTemplateJ8T_baseCols δ) (EF i) pubs rfl,
        TeleH.gather_pub_T b (jetTemplateJ8T δ) 29 (jetTemplateJ8T_baseCols δ) (EF i) pubs rfl] at g
      simpa only [cv, CoeffExpr.eval, Col.isLast, Col.accX] using g
  rw [Fin.sum_univ_def] at ht
  rw [jRd, sum_flatMap, ← ht]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [List.map_map]
  have e : (contribX cv QE.var).ev δ (EK i) (EF i) = liftQ δ ((ChipJ8.selSum cv entsX).eval (EF i)) *
      Quad.mk _ ((EK i).trace Col.invX) ((EK i).trace (Col.invX + 1)) := by
    simp only [contribX, ev_scale, ev_var]
  rw [e, (slotX hsat hbind hinj i).2]
  rfl

end Rows

/-! ## 6. The public layout: kinds -/

section Layout

theorem chainPre_kd (c dst : ℕ) : ∀ (src ctr : ℕ) (bs : List Bool),
    ∀ q ∈ chainPre c dst src ctr bs, q.kd ≠ .reg ∧ q.kd ≠ .call
  | src, ctr, [] => by intro q hq; simp [chainPre] at hq; subst hq; simp
  | src, ctr, b :: bs => by
    intro q hq
    simp only [chainPre, List.mem_cons] at hq
    rcases hq with rfl | hq
    · cases b <;> simp
    · exact chainPre_kd c dst ctr (ctr + 1) bs q hq

theorem nodePre_kd (c S ctr : ℕ) (nd : JNode) : ∀ q ∈ nodePre c S ctr nd, q.kd ≠ .reg ∧ q.kd ≠ .call := by
  intro q hq
  unfold nodePre at hq
  split at hq <;> first
    | exact chainPre_kd _ _ _ _ _ q hq
    | (simp only [List.mem_singleton] at hq; subst hq; simp)

theorem nodesPre_kd (c S : ℕ) : ∀ (ctr : ℕ) (nds : List JNode),
    ∀ q ∈ nodesPre c S ctr nds, q.kd ≠ .reg ∧ q.kd ≠ .call
  | _, [] => by simp [nodesPre]
  | ctr, nd :: nds => by
    intro q hq
    simp only [nodesPre, List.mem_append] at hq
    rcases hq with hq | hq
    · exact nodePre_kd c S ctr nd q hq
    · exact nodesPre_kd c S _ nds q hq

theorem blocks_kd (R : ℕ → Tpl) : ∀ (ids : List ℕ) (c0 : ℕ), ∀ q ∈ blocks R c0 ids,
    q.kd ≠ .reg ∧ (q.kd = .call → ∃ c i, ids[c]? = some i ∧ q = callPre R (c0 + c) i)
  | [], _ => by simp [blocks]
  | i :: is, c0 => by
    intro q hq
    simp only [blocks, blockPre, List.mem_append, List.mem_cons] at hq
    rcases hq with (rfl | hq) | hq
    · exact ⟨by simp [callPre], fun _ => ⟨0, i, rfl, by simp⟩⟩
    · have := nodesPre_kd _ _ _ _ q hq
      exact ⟨this.1, fun h => absurd h this.2⟩
    · obtain ⟨h1, h2⟩ := blocks_kd R is (c0 + 1) q hq
      refine ⟨h1, fun h => ?_⟩
      obtain ⟨c, i', hc, rfl⟩ := h2 h
      exact ⟨c + 1, i', by simpa using hc, by rw [show c0 + (c + 1) = c0 + 1 + c by omega]⟩

theorem layout_reg {R : ℕ → Tpl} {regs ids : List ℕ} {q : PRow} (hq : q ∈ layoutJ8 R regs ids)
    (hk : q.kd = .reg) : q.id ∈ regs := by
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h; exact hi
  · exact absurd hk (blocks_kd R ids 0 q h).1

theorem layout_call {R : ℕ → Tpl} {regs ids : List ℕ} {q : PRow} (hq : q ∈ layoutJ8 R regs ids)
    (hk : q.kd = .call) : ∃ c i, ids[c]? = some i ∧ q = callPre R c i := by
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h; simp [regPre] at hk
  · obtain ⟨c, i, hc, he⟩ := (blocks_kd R ids 0 q h).2 hk
    exact ⟨c, i, hc, by simpa using he⟩

/-- **A call's template is registered**: its `(TAG_reg, i, h_c)` consume is served by a registry row. -/
theorem call_reg {p : ℕ} [Fact p.Prime] {R : ℕ → Tpl} {regs ids : List ℕ} {rows : List (CRow (ZMod p))}
    (hA : Accepted R regs ids rows) {rc : CRow (ZMod p)} (hrc : rc ∈ rows) {c i : ℕ}
    (hpre : rc.pre = callPre R c i) : i ∈ regs := by
  obtain ⟨pre, w⟩ := rc
  simp only at hpre
  subst hpre
  have hip : i < p := (hA.small _ (pre_mem hA hrc)).1
  obtain ⟨r', hr', hκ⟩ := hA.bal _ hrc [((2 : ℕ) : ZMod p), (i : ZMod p), w.kN, w.vN]
    (by rw [show callPre R c i = ⟨.call, i, c, 0, 0, (nodesOf (R i)).length⟩ from rfl, consK_call];
        exact List.mem_cons_self ..)
  by_cases hk : r'.pre.kd = .reg
  · rw [provK_reg r' hk] at hκ
    simp only [List.mem_singleton, List.cons.injEq] at hκ
    have hid := (hA.small _ (pre_mem hA hr')).1
    have e := natCast_inj_lt hip hid hκ.2.1
    have := layout_reg (pre_mem hA hr') hk
    rwa [← e] at this
  · rw [provK_eq r' hk] at hκ; simp at hκ

end Layout

/-! ## 7. Tags at entry 7 -/

section Tags
variable {F : Type} [Field F]

theorem tlF_shape {κ : List F}
    (hκ : (∃ a b c d : F, κ = [((1 : ℕ) : F), a, b, c, d]) ∨ ∃ a b c : F, κ = [((2 : ℕ) : F), a, b, c]) :
    (tlF κ).length = 8 ∧ ((tlF κ).getD 7 0 = ((1 : ℕ) : F) ∨ (tlF κ).getD 7 0 = ((2 : ℕ) : F)) := by
  rcases hκ with ⟨a, b, c, d, rfl⟩ | ⟨a, b, c, rfl⟩
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

theorem jet_tag (r : CRow F) : ∀ κ ∈ keysOf ents3 r, κ.getD 7 0 = ((3 : ℕ) : F) ∧ κ.length = 8 ∧
    r.pre.kd = .call ∧ κ = keyJet.map (KE.ev (colOf r)) := by
  intro κ hκ
  simp only [keysOf, ents3, List.mem_map, List.mem_filter, List.mem_singleton] at hκ
  obtain ⟨e, ⟨rfl, he⟩, rfl⟩ := hκ
  refine ⟨by simp [keyJet, KE.ev], by simp [keyJet], ?_, rfl⟩
  have he' : Kd.call = r.pre.kd := by simpa using he
  exact he'.symm

end Tags

theorem ne_cast {p : ℕ} [Fact p.Prime] {a b : ℕ} (ha : a < p) (hb : b < p) (hab : a ≠ b) :
    ((a : ℕ) : ZMod p) ≠ (b : ZMod p) := fun h => hab (natCast_inj_lt ha hb h)

section Bridge
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "RJ" => rowJ b nodes orbit chals pubs lay P

/-- **The J in-chip balance in existence form (J-3b's `Accepted.bal`) from the MERGED service
identity.**  The J terminal `(pub₀, pub₁)` plus the other service consumers `reqO` (compute's
`TAG_inc` / `TAG_jet` / `walkRecA` consumes) equals the other service providers `provO` (atom-table
inc heads, atom-walk records; zero-padded, so entry 7 is `0`) at the J tagged coins; outside the
weighted IO failure event of the merged lists, with the request count `< p`, every in-chip consume
is provided by some row of the chip. -/
theorem bal_of_service [DecidableEq K] [DecidableEq 𝕂′] [CharP 𝕂′ p] (hp3 : 3 < p)
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
    ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, ∀ κ ∈ consK r,
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
  intro r hr κ hκ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  have hκT : tlF κ ∈ consKT (RJ i) := by rw [consKT_eq]; exact List.mem_map_of_mem hκ
  have hmem : liftRec (L := 𝕂′) (keyK (K := K) 8 (tlF κ)) ∈ reqs :=
    List.mem_map_of_mem (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_map_of_mem hκT⟩))
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hserved _ hmem)
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  have hkey : q0.1 = keyK 8 (tlF κ) := liftRec_inj hqe
  have hshape := consK_shape (RJ i) κ hκ
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

/-- **J-3b `Accepted` from an accepted `jetChipJ8` trace.**  The rows realize the public layout
`lay = layoutJ8 R regs ids` (`small`, `uniq` are checks on that public layout), the base gates hold
on every row (`base_row`), and the in-chip balance is the existence form `hbal` (`bal_of_service`). -/
theorem accepted_of_sat (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) {R : ℕ → Tpl} {regs ids : List ℕ}
    (hlay : List.ofFn lay = layoutJ8 R regs ids)
    (hsmall : ∀ q ∈ layoutJ8 R regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 R regs ids).filterMap tvKey).Nodup)
    (hbal : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, ∀ κ ∈ consK r,
      ∃ r' ∈ rowsJ b nodes orbit chals pubs lay P, κ ∈ provK r') :
    Accepted R regs ids (rowsJ b nodes orbit chals pubs lay P) where
  lay := by rw [rowsJ, List.map_ofFn, ← hlay]; rfl
  small := hsmall
  uniq := huniq
  gate := by
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact base_row hsat hbind hinj i
  bal := hbal

end Bridge

/-! ## 8. `JetProvOK`: the J chip's service provides are genuine -/

theorem eight {α : Type} : ∀ l : List α, l.length = 8 →
    ∃ x0 x1 x2 x3 x4 x5 x6 x7, l = [x0, x1, x2, x3, x4, x5, x6, x7]
  | [x0, x1, x2, x3, x4, x5, x6, x7], _ => ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h
  | [_, _, _, _, _, _], h | [_, _, _, _, _, _, _], h => by simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

section Prov
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

local notation "RJ" => rowJ b nodes orbit chals pubs lay P

theorem natKey_keyK {l : List ℕ} {κ : List (ZMod p)}
    (h : DenXJ8.natKey (p := p) (K := K) 8 l = keyK 8 κ) (c : ℕ) (hc : c < 8) :
    ((l.getD c 0 : ℕ) : ZMod p) = κ.getD c 0 :=
  (algebraMap (ZMod p) K).injective (congrFun h ⟨c, hc⟩)

theorem len8_of_tag {l : List ℕ} {κ : List (ZMod p)} (hl : l.length ≤ 8)
    (h : DenXJ8.natKey (p := p) (K := K) 8 l = keyK 8 κ) (h7 : κ.getD 7 0 ≠ 0) : l.length = 8 := by
  by_contra hne
  have e := natKey_keyK h 7 (by norm_num)
  rw [List.getD_eq_default _ _ (by omega)] at e
  exact h7 (by simpa using e.symm)

theorem val_of_cast {x : ℕ} (hx : x < p) {v : ZMod p} (h : ((x : ℕ) : ZMod p) = v) : x = v.val := by
  rw [← h, ZMod.val_cast_of_lt hx]

/-- **`JetProvOK`.**  On rows that are J-3b `Accepted` (from `accepted_of_sat` + `bal_of_service`),
with `D` a denotation (`DenOKX`), the registry `Rg` binding every registered id to its template and
`compile p (R id)` (public; with the template checks `axPosB`, `WellTyped`), the export reads'
records genuine (`RecOK .x`, from the cell export balance), the registry rows' claim binding, and
every call's subject handle denoted: **every service provide of the J chip satisfies `RecOK` at
`.s`** — the `TAG_jet` provides `(id, h_c, h_S, h_E, 3)` by `jetChip_holds`, the in-chip provides
(tags `1 / 2` at entry 7) vacuously. -/
theorem jetProvOK (hp3 : 3 < p) {R : ℕ → Tpl} {regs ids : List ℕ}
    (hA : Accepted R regs ids (rowsJ b nodes orbit chals pubs lay P))
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX} (hD : DenOKX p D)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(R i).toTemplate p, compile p (R i)⟩ ∧ axPosB (R i) = true ∧
      (R i).WellTyped p)
    (hRd : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK D Rg limbA ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x))
    (hReg : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .reg →
      D (r.w.kN.val, r.w.vN.val) = some (compile p (R r.pre.id)))
    (hSub : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .call →
      ∃ S, D (r.w.kL.val, r.w.vL.val) = some S) :
    ServedJ8.ProvP (p := p) (K := K) (RecOK D Rg limbA) .s (jProv b nodes orbit chals pubs lay P) := by
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
  intro q hq l hl hlt hnk
  change l.length ≤ 8 at hl
  change DenXJ8.natKey (p := p) (K := K) 8 l = q.1 at hnk
  obtain ⟨i, -, hq'⟩ := List.mem_flatMap.mp hq
  have hrc : RJ i ∈ rowsJ b nodes orbit chals pubs lay P := List.mem_ofFn.mpr ⟨i, rfl⟩
  rcases List.mem_append.mp hq' with hP | hJ
  · -- in-chip provide: tag `1` / `2` at entry 7, so `RecOK` is `True`
    obtain ⟨κ', hκ', rfl⟩ := List.mem_map.mp hP
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
  · -- `TAG_jet` provide: `jetChip_holds`
    obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hJ
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
    -- the call row
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
    obtain ⟨S, hS⟩ := hSub _ hrc hkd
    obtain ⟨hcomp, E, hE, hsem, -⟩ := jetChip_holds R regs ids (rowsJ b nodes orbit chals pubs lay P)
      (fun hh => D (hh.1.val, hh.2.val)) hA hM c x0 hc hax hT (RJ i) hrc hpre S hS
    exact ⟨_, hRg, hcomp, S, E, hS, hE, hsem⟩

end Prov

/-! ## 9. The finding, at the obligation level, and the combined `JetProvOK` -/

section Finding
variable {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}

/-- **Finding (J-3b tag-first keys).**  The service balance's providers must satisfy `RecOK .s` on
every small record their key equals (`ProvP`).  A J-3b registry provide `(2, id, k, v)` IS the
`walkRecA` record `(rootIdx = 2, ax = id, k, v)`, whose obligation is the atom-walk's — not
something the J chip can supply. -/
theorem oldRegKey_recOK (id k v : ℕ) :
    RecOK D Rg limbA ([2, id, k, v], .s) ↔ ∃ m, D (2, 2) = some (.atom m) ∧ limbA m id = (k, v) := Iff.rfl

/-- **Finding (J-3b tag-first keys).**  A J-3b node-value provide `(1, cid, n, k, 4)` IS the inc record
`(old = (1, cid), new = (n, k), TAG_inc)`, whose obligation is the atom table's increment. -/
theorem oldValKey_recOK (cid n k : ℕ) :
    RecOK D Rg limbA ([1, cid, n, k, 4], .s) ↔
      ∃ m : ℕ, D (1, cid) = some (.atom m) ∧ D (n, k) = some (.atom (m + 1)) := Iff.rfl

/-- **The fix.**  The tag-last in-chip records carry no service obligation. -/
theorem newKeys_recOK (x0 x1 x2 x3 x4 x5 x6 : ℕ) :
    RecOK D Rg limbA ([x0, x1, x2, x3, x4, x5, x6, 1], .s) ∧
      RecOK D Rg limbA ([x0, x1, x2, x3, x4, x5, x6, 2], .s) := by
  simp [RecOK]

end Finding

section Combined
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K} {lay : Fin n → PRow}
  {P : Fin (jetChipJ8 δ b nodes orbit chals pubs lay).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **J-3b `Accepted` from an accepted `jetChipJ8` trace and the merged service identity.** -/
theorem accepted_of_service [DecidableEq K] [DecidableEq 𝕂′] [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    {R : ℕ → Tpl} {regs ids : List ℕ} (hlay : List.ofFn lay = layoutJ8 R regs ids)
    (hsmall : ∀ q ∈ layoutJ8 R regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 R regs ids).filterMap tvKey).Nodup)
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
    Accepted R regs ids (rowsJ b nodes orbit chals pubs lay P) :=
  accepted_of_sat hsat hbind hinj hlay hsmall huniq
    (bal_of_service hp3 hsat hbind hinj hn hadj reqO provO hO7 hG hout hcount)

/-- **`JetProvOK`, from the chip.**  An accepted `jetChipJ8` trace realizing the public layout, under
the merged service identity outside its IO event, with the memory-side facts of `jetProvOK`:
every J service provide satisfies `RecOK .s`. -/
theorem jetProvOK_of_sat [DecidableEq K] [DecidableEq 𝕂′] [CharP 𝕂′ p] (hp3 : 3 < p)
    (hsat : (jetChipJ8 δ b nodes orbit chals pubs lay).rap.Satisfies P)
    (hbind : (jetChipJ8 δ b nodes orbit chals pubs lay).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (hn : 0 < n)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    {R : ℕ → Tpl} {regs ids : List ℕ} (hlay : List.ofFn lay = layoutJ8 R regs ids)
    (hsmall : ∀ q ∈ layoutJ8 R regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 R regs ids).filterMap tvKey).Nodup)
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
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX} (hD : DenOKX p D)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(R i).toTemplate p, compile p (R i)⟩ ∧ axPosB (R i) = true ∧
      (R i).WellTyped p)
    (hRd : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK D Rg limbA ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x))
    (hReg : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .reg →
      D (r.w.kN.val, r.w.vN.val) = some (compile p (R r.pre.id)))
    (hSub : ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, r.pre.kd = .call →
      ∃ S, D (r.w.kL.val, r.w.vL.val) = some S) :
    ServedJ8.ProvP (p := p) (K := K) (RecOK D Rg limbA) .s (jProv b nodes orbit chals pubs lay P) :=
  jetProvOK hp3 (accepted_of_service hp3 hsat hbind hinj hn hadj hlay hsmall huniq reqO provO hO7 hG hout
    hcount) hD hTpl hRd hReg hSub

/-- **The J export reads' `RecOK .x` from the cell export balance**: if every J read key is a provider
key of the `x` balance and the `x` providers satisfy `ProvP RecOK` (P5's `hprov .x`), every
`rp / sl / sr` row's record `(h_N.v, h_L, h_R)` is genuine (`jetProvOK`'s `hRd`). -/
theorem rd_recOK {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}
    (provsX : List ((Fin 5 → K) × K))
    (hprov : ServedJ8.ProvP (p := p) (K := K) (RecOK D Rg limbA) .x provsX)
    (hserved : ∀ c ∈ jRd b nodes orbit chals pubs lay P, c ∈ provsX.map Prod.fst) :
    ∀ r ∈ rowsJ b nodes orbit chals pubs lay P, (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
      RecOK D Rg limbA ([r.w.vN.val, r.w.kL.val, r.w.vL.val, r.w.kR.val, r.w.vR.val], .x) := by
  intro r hr hk
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  set r := rowJ b nodes orbit chals pubs lay P i
  have hκ : [r.w.vN, r.w.kL, r.w.vL, r.w.kR, r.w.vR] ∈ keysOf entsX r := by
    simp only [keysOf, entsX, List.mem_map, List.mem_filter]
    rcases hk with hk | hk | hk
    · exact ⟨(.rp, keyX), ⟨by simp, by simp [hk]⟩, rfl⟩
    · exact ⟨(.sl, keyX), ⟨by simp, by simp [hk]⟩, rfl⟩
    · exact ⟨(.sr, keyX), ⟨by simp, by simp [hk]⟩, rfl⟩
  have hc : keyK (K := K) 5 [r.w.vN, r.w.kL, r.w.vL, r.w.kR, r.w.vR] ∈ jRd b nodes orbit chals pubs lay P :=
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_map_of_mem hκ⟩
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hserved _ hc)
  refine hprov q hq _ (by simp [DenXJ8.mOf]) ?_ ?_
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> exact ZMod.val_lt _
  · rw [hqe]
    funext c
    fin_cases c <;> simp [DenXJ8.natKey, keyK]

end Combined

end

end Nock.Jet.RapJetJ8
