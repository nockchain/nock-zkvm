/-
  Nock/NockVMROM/Thm54/VclL/Handle/IncHeadJ8.lean

  **The atom table's inc heads are genuine service
  providers.**  New module, additive.

  The atom table provides into the service balance `s` the inc records `(h_old, h_new, TAG_inc)`
  (`AtomChipHQ.incKey`, weight `mi`, zero-padded to `8`: `ServiceJ8.pad8 atomIncProvs`).  Their obligation
  `RecOK (·,.s)` at `[ok, ov, nk, nv, 4]` is `D (ok, ov) = atom n ∧ D (nk, nv) = atom (n + 1)`.

  * §1 (ℕ level) `incHead_recOK_inc`: an inc row whose old handle denotes `l_old` and whose chain step
    holds (A-2 `inc_chain_sound(_of_served)`'s conclusion) provides a genuine `(2, idx_o) ↦ (2, i)`;
    `incHead_recOK_conv`: a conversion row (`aL = 1`, `wR = 0`, `aR = B − 1`, g8) provides a genuine
    `(0, p_G − 1) ↦ (2, i)` (A-1 `crossing`, `conv_sound`).
  * **FINDING (kernel) `conv_recOK_iff`**: the conversion record `(0, q − 1) ↦ (2, i)` the chip writes at
    a field of characteristic `q` (its `ov` entry is `−1`) is genuine IFF `q = p_G` (the Goldilocks
    prime `Nock.Atoms.p`): row `i` denotes the limbs `[1, B − 1]` of `p_G` whatever the field.  So the
    service soundness of the atom table holds at Goldilocks only; `atomInc_provOK` carries `hpG`.
  * §2 **`atomInc_provOK`**: `ProvP RecOK.s (pad8 atomIncProvs)` on an accepted `atomChipHQ` trace,
    from the gates (head gate `mi·(1 − inc − conv)`, booleanities, `inc·conv`, g8), the ℕ reading `r` of
    the rows (`Reads`, `Small`, serials `idx = k`), `2^63 < p`, `p = p_G`, and three named facts:
    `hDen` (the atom-table handle `(2, j)` denotes the value of the limb list row `j` denotes — the
    definition of `ext`, item 3), `hold` (an inc row's old handle denotes some limb list) and `hchain`
    (A-2's chain step; `inc_chain_sound_of_served` with `consumeServedQ_of_balance`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.IncHeadJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf padK)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads atomChipHQ incKey tagInc atomGates)
open Nock.Atoms (val B limbs)

noncomputable section

/-! ## 1. The ℕ level -/

section Nat
variable {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}

/-- **An inc row's head is genuine**: old `(2, idx_o)` denotes `val l_old`, new `(2, i)` its successor. -/
theorem incHead_recOK_inc {r : ℕ → ARow}
    (hDen : ∀ j l, Denotes r j l → D (2, j) = some (.atom (val l)))
    {i : ℕ} {lold : List ℕ} (hold : Denotes r (r i).idxO lold)
    (hchain : ∃ lnew, Denotes r i lnew ∧ val lnew = val lold + 1) :
    RecOK D Rg limbA ([2, (r i).idxO, 2, i, 4], .s) := by
  obtain ⟨lnew, hd, hv⟩ := hchain
  exact ⟨val lold, hDen _ _ hold, by rw [hDen _ _ hd, hv]⟩

/-- **A conversion row's head is genuine** at Goldilocks: `(0, p_G − 1) ↦ (2, i)` with row `i = [1, B − 1]`. -/
theorem incHead_recOK_conv {r : ℕ → ARow} (hD0 : ∀ v, D (0, v) = some (.atom v))
    (hDen : ∀ j l, Denotes r j l → D (2, j) = some (.atom (val l)))
    {i : ℕ} (h1 : (r i).aL = 1) (hw : (r i).wR = 0) (ht : (r i).aR = B - 1) :
    RecOK D Rg limbA ([0, Nock.Atoms.p - 1, 2, i, 4], .s) := by
  obtain ⟨hd, -, hv⟩ := AtomChipHQ.conv_sound h1 hw ht
  exact ⟨Nock.Atoms.p - 1, hD0 _, by rw [hDen _ _ hd, hv]⟩

/-- **FINDING: the conversion record is genuine only at Goldilocks.**  At a field of characteristic `q`
the conversion row writes the record `(0, q − 1) ↦ (2, i)` (its `ov` entry is `−1`), and row `i` denotes
`[1, B − 1]`, i.e. `p_G`, whatever `q` is: the record is genuine iff `q = p_G`. -/
theorem conv_recOK_iff {r : ℕ → ARow} (hD0 : ∀ v, D (0, v) = some (.atom v))
    (hDen : ∀ j l, Denotes r j l → D (2, j) = some (.atom (val l)))
    {i : ℕ} (h1 : (r i).aL = 1) (hw : (r i).wR = 0) (ht : (r i).aR = B - 1) {q : ℕ} (hq : 1 ≤ q) :
    RecOK D Rg limbA ([0, q - 1, 2, i, 4], .s) ↔ q = Nock.Atoms.p := by
  obtain ⟨hd, -, hv⟩ := AtomChipHQ.conv_sound h1 hw ht
  have hpG : 1 ≤ Nock.Atoms.p := by
    show 1 ≤ Nock.Field.p
    unfold Nock.Field.p; norm_num
  show (∃ n : ℕ, D (0, q - 1) = some (.atom n) ∧ D (2, i) = some (.atom (n + 1))) ↔ _
  rw [hD0, hDen _ _ hd, hv]
  constructor
  · rintro ⟨n, e1, e2⟩
    simp only [Option.some.injEq, Noun.atom.injEq] at e1 e2
    omega
  · intro e
    exact ⟨q - 1, rfl, by rw [e]⟩

end Nat

/-! ## 2. The field level: `ProvP RecOK.s` for the padded inc heads -/

theorem len_cases8 {α : Type} (l : List α) (h : l.length ≤ 8) :
    l.length < 5 ∨ (∃ a0 a1 a2 a3 a4, l = [a0, a1, a2, a3, a4]) ∨
      (∃ a0 a1 a2 a3 a4 a5, l = [a0, a1, a2, a3, a4, a5]) ∨
      (∃ a0 a1 a2 a3 a4 a5 a6, l = [a0, a1, a2, a3, a4, a5, a6]) ∨
      (∃ a0 a1 a2 a3 a4 a5 a6 a7, l = [a0, a1, a2, a3, a4, a5, a6, a7]) :=
  match l, h with
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _ => Or.inl (by simp)
  | [a0, a1, a2, a3, a4], _ => Or.inr (Or.inl ⟨a0, a1, a2, a3, a4, rfl⟩)
  | [a0, a1, a2, a3, a4, a5], _ => Or.inr (Or.inr (Or.inl ⟨a0, a1, a2, a3, a4, a5, rfl⟩))
  | [a0, a1, a2, a3, a4, a5, a6], _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨a0, a1, a2, a3, a4, a5, a6, rfl⟩)))
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
      Or.inr (Or.inr (Or.inr (Or.inr ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩)))
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h; omega

section Field
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K}
  {Q : Fin (atomChipHQ δ b hn nodes orbit chals pubs).rap.w → (ZMod p)[X]}

local notation "AE" => AtomServedQ.aEF b nodes orbit chals pubs Q

/-- **`ProvOK.s` for the atom table's inc heads.** -/
theorem atomInc_provOK (hq : 2 ^ 63 < p)
    (hsat : (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies Q)
    {r : ℕ → ARow} (hR : ∀ k : Fin n, Reads (AE k) (r k)) (hs : ∀ k : Fin n, (r k).Small)
    (hidx : ∀ k : Fin n, (r k).idx = k)
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}
    (hD0 : ∀ v, D (0, v) = some (.atom v))
    (hDen : ∀ j l, Denotes r j l → D (2, j) = some (.atom (val l)))
    (hold : ∀ k : Fin n, (r k).inc = 1 → ∃ l, Denotes r (r k).idxO l)
    (hchain : ∀ k : Fin n, (r k).inc = 1 → ∀ lold, Denotes r (r k).idxO lold →
      ∃ lnew, Denotes r k lnew ∧ val lnew = val lold + 1)
    (hpG : p = Nock.Atoms.p) :
    ProvP (p := p) (K := K) (RecOK D Rg limbA) .s (pad8 (atomIncProvs b nodes orbit chals pubs Q)) := by
  have hqF : 2 ^ 63 < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hq
  have ce : ∀ {x y : ℕ}, x < 2 ^ 63 → y < 2 ^ 63 → ((x : ℕ) : ZMod p) = y → x = y :=
    fun hx hy e => AtomChipHQ.cast_inj hqF hx hy e
  intro q hq' l hl hlt hnk
  change l.length ≤ 8 at hl
  obtain ⟨q5, hq5, rfl⟩ := List.mem_map.mp hq'
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq5
  split_ifs at hi with hmi
  · simp at hi
  rw [List.mem_singleton] at hi
  subst hi
  set e := AE i with he
  change DenXJ8.natKey (p := p) (K := K) 8 l = padK (ServeH.keyVec5 incKey e) at hnk
  have hent : ∀ c (hc : c < 5), ((l.getD c 0 : ℕ) : ZMod p) =
      ((incKey : List (CoeffExpr (ZMod p))).getD c (.const 0)).eval e := by
    intro c hc
    have := congrFun hnk ⟨c, by omega⟩
    simp only [DenXJ8.natKey, padK, ServeH.keyVec5, dif_pos hc] at this
    exact (algebraMap (ZMod p) K).injective this
  have hent' : ∀ c, 5 ≤ c → c < 8 → ((l.getD c 0 : ℕ) : ZMod p) = 0 := by
    intro c hc5 hc8
    have := congrFun hnk ⟨c, hc8⟩
    simp only [DenXJ8.natKey, padK, dif_neg (show ¬ c < 5 by omega)] at this
    exact (algebraMap (ZMod p) K).injective (this.trans (map_zero _).symm)
  -- the gates at row `i`
  have hg := AtomServedQ.atom_base δ b hn nodes orbit chals pubs Q hsat i
  have g := fun x (hx : x ∈ (atomGates : List (CoeffExpr (ZMod p)))) => hg x (List.mem_append_right _ hx)
  have gInc := g _ (by simp [atomGates, AtomChipHQ.g70] : boolE (cv AtomChipHQ.inc) ∈ (atomGates : List (CoeffExpr (ZMod p))))
  have gHead := g _ (by simp [atomGates, AtomChipHQ.g70] :
    CoeffExpr.mul (cv AtomChipHQ.mi) (.sub (notE (cv AtomChipHQ.inc)) (cv AtomChipHQ.conv)) ∈
      (atomGates : List (CoeffExpr (ZMod p))))
  have g8a := g _ (by simp [atomGates, AtomChipHQ.g8] :
    CoeffExpr.mul (cv AtomChipHQ.conv) (.sub (cv Cell.aL) (.const 1)) ∈ (atomGates : List (CoeffExpr (ZMod p))))
  have g8b := g _ (by simp [atomGates, AtomChipHQ.g8] :
    CoeffExpr.mul (cv AtomChipHQ.conv) (.sub (cv Cell.aR) (.const (AtomChipHQ.Bf - 1))) ∈
      (atomGates : List (CoeffExpr (ZMod p))))
  have g8c := g _ (by simp [atomGates, AtomChipHQ.g8] :
    CoeffExpr.mul (cv AtomChipHQ.conv) (cv Cell.wR) ∈ (atomGates : List (CoeffExpr (ZMod p))))
  simp only [boolE, notE, cv, CoeffExpr.eval] at gInc gHead g8a g8b g8c
  have hconv : e.trace AtomChipHQ.conv = 1 - e.trace AtomChipHQ.inc := by
    have := (mul_eq_zero.mp gHead).resolve_left hmi
    linear_combination -this
  have hp4 : 4 < p := by omega
  have hRi := hR i
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hs i
  have hip : (i : ℕ) < 2 ^ 62 := by rw [← hidx i]; exact s1
  rcases len_cases8 l hl with hlt5 | ⟨a0, a1, a2, a3, a4, rfl⟩ | ⟨a0, a1, a2, a3, a4, a5, rfl⟩ |
      ⟨a0, a1, a2, a3, a4, a5, a6, rfl⟩ | ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
  · exfalso
    have e4 := hent 4 (by norm_num)
    rw [List.getD_eq_default _ _ (by omega)] at e4
    simp only [incKey, tagInc, List.getD_cons_succ, List.getD_cons_zero, CoeffExpr.eval, Nat.cast_zero] at e4
    have := ce (x := 0) (y := 4) (by norm_num) (by norm_num) (by exact_mod_cast e4)
    omega
  · have hlt' : ∀ x ∈ [a0, a1, a2, a3, a4], x < p := hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt'
    obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := hlt'
    have e0 := hent 0 (by norm_num); have e1 := hent 1 (by norm_num); have e2 := hent 2 (by norm_num)
    have e3 := hent 3 (by norm_num); have e4 := hent 4 (by norm_num)
    simp only [incKey, tagInc, notE, cv, List.getD_cons_succ, List.getD_cons_zero, CoeffExpr.eval] at e0 e1 e2 e3 e4
    have ha4 : a4 = 4 := Nock.Jet.ChipJ8.natCast_inj_lt hx4 (by omega) (by exact_mod_cast e4)
    have ha2 : a2 = 2 := Nock.Jet.ChipJ8.natCast_inj_lt hx2 (by omega) (by exact_mod_cast e2)
    have ha3 : a3 = i := by
      rw [hRi.idx, hidx i] at e3
      exact Nock.Jet.ChipJ8.natCast_inj_lt (p := p) hx3 (show (i : ℕ) < p by omega) e3
    subst ha4 ha2 ha3
    rw [hRi.inc] at gInc hconv
    rcases mul_eq_zero.mp gInc with h0 | h1
    · -- conversion row
      have hc1 : e.trace AtomChipHQ.conv = 1 := by rw [hconv, h0, sub_zero]
      rw [hc1] at e0 e1
      rw [hc1, one_mul] at g8a g8b g8c
      have ha0 : a0 = 0 := Nock.Jet.ChipJ8.natCast_inj_lt hx0 (by omega) (by rw [e0]; simp)
      have ha1 : a1 = p - 1 := by
        have h1' : ((a1 + 1 : ℕ) : ZMod p) = 0 := by push_cast; rw [e1]; ring
        rw [ZMod.natCast_eq_zero_iff] at h1'
        obtain ⟨c, hc⟩ := h1'
        rcases c with _ | _ | c
        · omega
        · omega
        · nlinarith
      subst ha0 ha1
      have haL : (r i).aL = 1 := ce (by omega) (by norm_num)
        (by rw [← hRi.aL]; exact (sub_eq_zero.mp g8a).trans Nat.cast_one.symm)
      have hwR : (r i).wR = 0 := ce (by omega) (by norm_num) (by rw [← hRi.wR, g8c, Nat.cast_zero])
      have haR : (r i).aR = B - 1 := by
        apply ce (by omega) (by norm_num [B])
        rw [← hRi.aR, sub_eq_zero.mp g8b, AtomChipHQ.Bf_eq, Nat.cast_sub (by norm_num [B]), Nat.cast_one]
      rw [hpG]
      exact incHead_recOK_conv hD0 hDen haL hwR haR
    · -- inc row
      have hinc : (r i).inc = 1 := ce (by omega) (by norm_num) ((sub_eq_zero.mp h1).trans Nat.cast_one.symm)
      have hc0 : e.trace AtomChipHQ.conv = 0 := by rw [hconv, sub_eq_zero.mp h1, sub_self]
      rw [hc0] at e0 e1
      have ha0 : a0 = 2 := Nock.Jet.ChipJ8.natCast_inj_lt hx0 (by omega) (by rw [e0]; norm_num)
      have ha1 : a1 = (r i).idxO := by
        rw [hRi.idxO] at e1
        exact Nock.Jet.ChipJ8.natCast_inj_lt hx1 (by omega) (by rw [e1]; ring)
      subst ha0 ha1
      obtain ⟨lold, hl0⟩ := hold i hinc
      exact incHead_recOK_inc hDen hl0 (hchain i hinc lold hl0)
  · simp [RecOK]
  · simp [RecOK]
  · have hx7 : a7 < p := hlt a7 (by simp)
    have e7 := hent' 7 (by norm_num) (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at e7
    have : a7 = 0 := Nock.Jet.ChipJ8.natCast_inj_lt hx7 (by omega) (by exact_mod_cast e7)
    subst this
    simp [RecOK]

end Field

end

end Nock.NockVMROM.Thm54.VclL.Handle.IncHeadJ8
