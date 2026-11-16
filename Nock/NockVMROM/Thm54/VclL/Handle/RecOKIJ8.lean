/-
  Nock/NockVMROM/Thm54/VclL/Handle/RecOKIJ8.lean

  New module, additive (`RecOKAJ8`, `AtomBigJ8` are not edited).

  * **`PreI D r`**: the antecedent of a service record — an inc-shaped key `[ok, ov, nk, nv, 4]` needs its OLD
    handle to denote, a `walkRecA`-shaped key `[rv, ax, lk, lv]` its ROOT `(2, rv)`, a jet key
    `[id, ck, cv, sk, sv, ek, ev, 3]` its SUBJECT `(sk, sv)` (step 3: this replaces the compute subject fact
    `hcomp`, `JetProvIJ8`); every other record `True`.
  * **`RecOKI D R comb r := PreI D r → RecOKA D R comb r`**.  `RecOKA → RecOKI` (`provPI_of_provPA`): every
    existing provider transfers.
  * **`atomInc_provOKI`**: the inc heads WITHOUT `hOldBig` (and without `hold`): an inc row's old handle
    `(2, idxO)` denotes by the antecedent, so it is a big row (`hDenB'`: at `extB` by construction), and the new row
    is `val old + 1 ≥ p` (`hchain`).  The conversion row is unchanged.
  * **`hAW_extBI`**: the atom walk's providers WITHOUT `hRootBig`: under the antecedent the root `(2, rv)`
    denotes under `extB`, hence under `extA` with the same value, and `walkAOK_row` (at `extA`) applies
    (`walkAOKI_extB`, `provPI_pad8_walk`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf padK natKey)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads atomChipHQ incKey tagInc atomGates)
open Nock.NockVMROM.Thm54.VclL.Handle.IncHeadJ8 (len_cases8)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA extA_of_denotes denotes_unique)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (recNat natKey_walk)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB extB_of_denotes extA_some)
open Nock.Atoms (val B limbs)

noncomputable section

/-! ## 1. The implication-form obligation -/

/-- The antecedent on a service record's key list: the inc record's OLD handle, the `walkRecA` record's ROOT, the
jet record's SUBJECT. -/
def PreS (D : HX → Option Noun) : List ℕ → Prop
  | [ok, ov, _, _, 4] => D (ok, ov) ≠ none
  | [rv, _, _, _] => D (2, rv) ≠ none
  | [_, _, _, sk, sv, _, _, 3] => D (sk, sv) ≠ none
  | _ => True

/-- **The antecedent of a record**: on the service balance, `PreS`; elsewhere `True`. -/
def PreI (D : HX → Option Noun) (r : List ℕ × Bal) : Prop := if r.2 = .s then PreS D r.1 else True

def RecOKI (D : HX → Option Noun) (R : Nock.Jet.Registry) (comb : ℕ → Noun) (r : List ℕ × Bal) : Prop :=
  PreI D r → RecOKA D R comb r

theorem preI_off {D : HX → Option Noun} {l : List ℕ} {bl : Bal} (h : bl ≠ .s) : PreI D (l, bl) := by
  simp [PreI, h]

theorem recOKI_off {D : HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun} {l : List ℕ} {bl : Bal}
    (h : bl ≠ .s) (hr : RecOKI D R comb (l, bl)) : RecOKA D R comb (l, bl) := hr (preI_off h)

section Prov
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  {D : HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun}

/-- `ProvP` is monotone in the obligation. -/
theorem provP_mono {Φ Ψ : List ℕ × Bal → Prop} (hΦΨ : ∀ r, Φ r → Ψ r) {bl : Bal}
    {provs : List ((Fin (mOf bl) → K) × K)} (h : ProvP (p := p) (K := K) Φ bl provs) :
    ProvP (p := p) (K := K) Ψ bl provs :=
  fun q hq l hl hlt hk => hΦΨ _ (h q hq l hl hlt hk)

/-- **Every `RecOKA` provider meets `RecOKI`.** -/
theorem provPI_of_provPA {bl : Bal} {provs : List ((Fin (mOf bl) → K) × K)}
    (h : ProvP (p := p) (K := K) (RecOKA D R comb) bl provs) :
    ProvP (p := p) (K := K) (RecOKI D R comb) bl provs :=
  provP_mono (Ψ := RecOKI D R comb) (fun _ hr _ => hr) h

/-- **A provider whose implication-form `RecOK` obligation holds at EVERY `limbA`** meets `RecOKI` (the
`provPA_of_forall` argument under the antecedent). -/
theorem provPI_of_forall {bl : Bal} {provs : List ((Fin (mOf bl) → K) × K)}
    (h : ∀ limbA : ℕ → ℕ → HX, ProvP (p := p) (K := K) (fun r => PreI D r → RecOK D R limbA r) bl provs) :
    ProvP (p := p) (K := K) (RecOKI D R comb) bl provs := by
  intro q hq l hl hlt hk hpre
  by_cases hw : IsWalkA (l, bl)
  · exfalso
    obtain ⟨hs, h4⟩ := hw
    simp only at hs h4
    subst hs
    match l, h4, hpre with
    | [a, b, c, d], _, hpre =>
      have := h (fun _ _ => (c + 1, d)) q hq [a, b, c, d] hl hlt hk hpre
      simp only [RecOK, Prod.mk.injEq] at this
      obtain ⟨_, _, h1, _⟩ := this
      omega
  · exact (recOKA_iff_off hw).mpr (h (fun _ _ => (0, 0)) q hq l hl hlt hk hpre)

end Prov

/-! ## 2. `extB`: the converse direction -/

theorem extB_some {q : ℕ} {r : ℕ → ARow} {j : ℕ} {X : Noun} (h : extB q r j = some X) :
    ∃ l, Denotes r j l ∧ q ≤ val l ∧ X = .atom (val l) := by
  unfold extB at h
  split_ifs at h with he
  · exact ⟨_, (Classical.choose_spec he).1, (Classical.choose_spec he).2, (Option.some.inj h).symm⟩

/-- **`hDenB'` at `extB`**: a denoting kind-2 handle is a big denoted row. -/
theorem hDenB'_extB {q : ℕ} (t : List (CellRowB0 q)) (p : ℕ) (r : ℕ → ARow) :
    ∀ j X, denK t (extB p r) (2, j) = some X → ∃ l, Denotes r j l ∧ p ≤ val l :=
  fun _ _ h => let ⟨l, hl, hq, _⟩ := extB_some h; ⟨l, hl, hq⟩

/-! ## 3. The inc heads in implication form -/

section Field
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K}
  {Q : Fin (atomChipHQ δ b hn nodes orbit chals pubs).rap.w → (ZMod p)[X]}

local notation "AE" => AtomServedQ.aEF b nodes orbit chals pubs Q

/-- **The inc heads at the implication form, at every `limbA`**: no `hOldBig`, no `hold`.  `hDenB'` (a
denoting kind-2 handle is a big denoted row) holds at `extB` by construction (`hDenB'_extB`). -/
theorem atomInc_provOKI_limb (hq : 2 ^ 63 < p)
    (hsat : (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies Q)
    {r : ℕ → ARow} (hR : ∀ k : Fin n, Reads (AE k) (r k)) (hs : ∀ k : Fin n, (r k).Small)
    (hidx : ∀ k : Fin n, (r k).idx = k)
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} (limbA : ℕ → ℕ → HX)
    (hD0 : ∀ v, D (0, v) = some (.atom v))
    (hDenB : ∀ j l, Denotes r j l → p ≤ val l → D (2, j) = some (.atom (val l)))
    (hDenB' : ∀ j X, D (2, j) = some X → ∃ l, Denotes r j l ∧ p ≤ val l)
    (hchain : ∀ k : Fin n, (r k).inc = 1 → ∀ lold, Denotes r (r k).idxO lold →
      ∃ lnew, Denotes r k lnew ∧ val lnew = val lold + 1)
    (hpG : p = Nock.Atoms.p) :
    ProvP (p := p) (K := K) (fun x => PreI D x → RecOK D Rg limbA x) .s
      (pad8 (atomIncProvs b nodes orbit chals pubs Q)) := by
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
  · intro hpre
    have hlt' : ∀ x ∈ [a0, a1, a2, a3, a4], x < p := hlt
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
      obtain ⟨hd, -, hv⟩ := AtomChipHQ.conv_sound haL hwR haR
      show ∃ n : ℕ, D (0, p - 1) = some (.atom n) ∧ D (2, i) = some (.atom (n + 1))
      refine ⟨p - 1, hD0 _, ?_⟩
      rw [hDenB _ _ hd (by rw [hv, hpG]; omega), hv, hpG]
    · -- inc row: the antecedent makes the old row a big denoted row
      have hinc : (r i).inc = 1 := ce (by omega) (by norm_num) ((sub_eq_zero.mp h1).trans Nat.cast_one.symm)
      have hc0 : e.trace AtomChipHQ.conv = 0 := by rw [hconv, sub_eq_zero.mp h1, sub_self]
      rw [hc0] at e0 e1
      have ha0 : a0 = 2 := Nock.Jet.ChipJ8.natCast_inj_lt hx0 (by omega) (by rw [e0]; norm_num)
      have ha1 : a1 = (r i).idxO := by
        rw [hRi.idxO] at e1
        exact Nock.Jet.ChipJ8.natCast_inj_lt hx1 (by omega) (by rw [e1]; ring)
      subst ha0 ha1
      have hpre' : D (2, (r i).idxO) ≠ none := hpre
      obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hpre'
      obtain ⟨lold, hl0, hb0⟩ := hDenB' _ _ hX
      obtain ⟨lnew, hd, hv⟩ := hchain i hinc lold hl0
      exact ⟨val lold, hDenB _ _ hl0 hb0, by rw [hDenB _ _ hd (by omega), hv]⟩
  · intro _; simp [RecOK]
  · intro _; simp [RecOK]
  · intro _
    have hx7 : a7 < p := hlt a7 (by simp)
    have e7 := hent' 7 (by norm_num) (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at e7
    have : a7 = 0 := Nock.Jet.ChipJ8.natCast_inj_lt hx7 (by omega) (by exact_mod_cast e7)
    subst this
    simp [RecOK]

/-- **`atomInc_provOKI`: the inc heads meet `RecOKI`** (no `hOldBig`, no `hold`). -/
theorem atomInc_provOKI (hq : 2 ^ 63 < p)
    (hsat : (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies Q)
    {r : ℕ → ARow} (hR : ∀ k : Fin n, Reads (AE k) (r k)) (hs : ∀ k : Fin n, (r k).Small)
    (hidx : ∀ k : Fin n, (r k).idx = k)
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hD0 : ∀ v, D (0, v) = some (.atom v))
    (hDenB : ∀ j l, Denotes r j l → p ≤ val l → D (2, j) = some (.atom (val l)))
    (hDenB' : ∀ j X, D (2, j) = some X → ∃ l, Denotes r j l ∧ p ≤ val l)
    (hchain : ∀ k : Fin n, (r k).inc = 1 → ∀ lold, Denotes r (r k).idxO lold →
      ∃ lnew, Denotes r k lnew ∧ val lnew = val lold + 1)
    (hpG : p = Nock.Atoms.p) :
    ProvP (p := p) (K := K) (RecOKI D Rg comb) .s (pad8 (atomIncProvs b nodes orbit chals pubs Q)) :=
  provPI_of_forall fun limbA =>
    atomInc_provOKI_limb hq hsat hR hs hidx limbA hD0 hDenB hDenB' hchain hpG

end Field

/-! ## 4. The atom walk's providers in implication form -/

/-- The walk antecedent per record. -/
def WalkAOKI (D : HX → Option Noun) (comb : ℕ → Noun) : List ℕ → Prop
  | [rv, ax, lk, lv] => D (2, rv) ≠ none → WalkAOK D comb [rv, ax, lk, lv]
  | _ => True

/-- **`WalkAOK` at `extA` gives the implication form at `extB`** (no root-big premise). -/
theorem walkAOKI_extB {q' : ℕ} (tC : List (CellRowB0 q')) (p : ℕ) {rA : ℕ → ARow} {comb : ℕ → Noun}
    {r : List ℕ} (h : WalkAOK (denK tC (extA rA)) comb r) :
    WalkAOKI (denK tC (extB p rA)) comb r := by
  match r, h with
  | [rv, ax, lk, lv], ⟨n, hn, h1, h2⟩ =>
    intro hne
    obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨l, hl, hbig, rfl⟩ := extB_some (q := p) (r := rA) (j := rv) hX
    obtain ⟨l', hl', hX'⟩ := extA_some (r := rA) (j := rv) hn
    have hll := denotes_unique hl hl'
    subst hll
    have hv : n = val l := by simpa using hX'
    refine ⟨n, ?_, h1, h2⟩
    show extB p rA rv = some (.atom n)
    rw [hv]; exact hX
  | [], _ => trivial
  | [_], _ => trivial
  | [_, _], _ => trivial
  | [_, _, _], _ => trivial
  | _ :: _ :: _ :: _ :: _ :: _, _ => trivial

section Pad
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {D : LocalVSX.HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun}

/-- **`AtomWalkProvJ8.provPA_pad8_walk` in implication form.** -/
theorem provPI_pad8_walk {h n : ℕ} (b : Basis (Fin 3) (ZMod p) K) (nodes : Fin n → ZMod p)
    (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K) {w : ℕ} (Q : Fin w → (ZMod p)[X])
    (hrow : ∀ j : Fin n, ∀ bb : Bool, WalkAOKI D comb (recNat (TeleH.wEF b nodes orbit chals pubs Q j) bb)) :
    ProvP (p := p) (K := K) (RecOKI D R comb) .s (pad8 (ServeH.walkPProvs b nodes orbit chals pubs Q)) := by
  intro q hq l hlen hlt hkey hpre
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hq0
  set e := TeleH.wEF b nodes orbit chals pubs Q j
  obtain ⟨bb, hbb⟩ : ∃ bb : Bool, q0.1 = ServeH.keyVec5 (if bb then WalkHC.recRH else WalkHC.recLH) e := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  simp only [DenXJ8.mOf] at hkey hlen
  have hent : ∀ c : Fin 8, ((l.getD c 0 : ℕ) : ZMod p) =
      if (c : ℕ) < 5 then ((if bb then WalkHC.recRH else WalkHC.recLH).getD c (.const 0)).eval e else 0 := by
    intro c
    have := congrFun hkey c
    by_cases hc : (c : ℕ) < 5
    · simp only [natKey, padK, hbb, ServeH.keyVec5, dif_pos hc] at this
      rw [if_pos hc]
      exact (algebraMap (ZMod p) K).injective this
    · simp only [natKey, padK, dif_neg hc] at this
      rw [if_neg hc]
      exact (algebraMap (ZMod p) K).injective (this.trans (map_zero _).symm)
  have hz : ∀ c, 4 ≤ c → c < 8 → l.getD c 0 = 0 := by
    intro c hc4 hc8
    have hlt' : l.getD c 0 < p := by
      rcases Nat.lt_or_ge c l.length with hcl | hcl
      · rw [List.getD_eq_getElem _ _ hcl]; exact hlt _ (List.getElem_mem hcl)
      · rw [List.getD_eq_default _ _ hcl]; exact (Fact.out : p.Prime).pos
    have h0 : ((l.getD c 0 : ℕ) : ZMod p) = 0 := by
      have h1 := hent ⟨c, hc8⟩
      rcases (show c = 4 ∨ 5 ≤ c by omega) with rfl | h5
      · rw [h1]
        cases bb <;> simp [WalkHC.recLH, WalkHC.recRH, CoeffExpr.eval]
      · rw [h1, if_neg (by simp only; omega)]
    have := congrArg ZMod.val h0
    rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hlt', ZMod.val_zero] at this
  by_cases hw : IsWalkA (l, .s)
  · rw [recOKA_walk hw]
    obtain ⟨-, h4⟩ := hw
    simp only at h4
    match l, h4, hlt, hkey, hpre with
    | [a0, a1, a2, a3], _, hlt, hkey, hpre =>
      have hk5 : natKey (p := p) (K := K) 5 [a0, a1, a2, a3] =
          ServeH.keyVec5 (if bb then WalkHC.recRH else WalkHC.recLH) e := by
        funext c
        have := congrFun hkey ⟨c, by omega⟩
        simpa [natKey, padK, hbb, show (c : ℕ) < 5 from c.2] using this
      have hr := hrow j bb
      rw [← natKey_walk e bb a0 a1 a2 a3 hlt hk5] at hr
      exact hr hpre
  · rw [recOKA_iff_off (limbA := fun _ _ => (0, 0)) hw]
    have h4 := hz 4 (le_refl _) (by norm_num)
    have h7 := hz 7 (by norm_num) (by norm_num)
    have n5 : ∀ a b c d, l ≠ [a, b, c, d, 4] := by rintro a b c d rfl; simp at h4
    have n8 : ∀ a b c d e f g, l ≠ [a, b, c, d, e, f, g, 3] := by rintro a b c d e f g rfl; simp at h7
    unfold RecOK
    split
    all_goals first
      | trivial
      | (rename_i heq; exact absurd heq (n5 _ _ _ _))
      | (rename_i heq; exact absurd heq (n8 _ _ _ _ _ _ _))
      | simp_all [IsWalkA]

end Pad

section HAW
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (kroots : ℕ) (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipHQK δ kroots b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

open scoped Classical in
/-- **`hAW` at `extB` in implication form**: `AtomBigJ8.hAW_extB` WITHOUT `hRootBig`. -/
theorem hAW_extBI
    (hsat : (walkChipHQK δ kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQK δ kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar (ZMod p))
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ≠ 0)
    {tb : List (CellRow (ringChar (ZMod p)) (Quad (algebraMap (ZMod p) K δ)))}
    {vl : List (VKey (Quad (algebraMap (ZMod p) K δ)))}
    (htab : TableAccepts (Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3)) tb vl)
    (hseeds : AtomWalkProvJ8.AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3)) tb)
    (hX : KeysExported tb (walkDataOf δ kroots b hn nodes orbit chals pubs
      (restrictWalkK δ kroots b hn nodes orbit chals pubs Q)).X)
    (hHX : ∀ j < n, ∃ c ∈ tb,
      (natOf ((walkEnvFA δ kroots b hn nodes orbit chals pubs Q j).trace WChip.idx),
        childHOf (walkEnvFA δ kroots b hn nodes orbit chals pubs Q j) false,
        childHOf (walkEnvFA δ kroots b hn nodes orbit chals pubs Q j) true) = exportRec c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (walkDataOf δ kroots b hn nodes orbit chals pubs
        (restrictWalkK δ kroots b hn nodes orbit chals pubs Q)))
    (hs : SerialOK (tb.map (·.b0))) (htb : tb.length ≤ ringChar (ZMod p)) {rA : ℕ → ARow}
    (hag : ∀ c ∈ tb.map (·.b0), AgreeRow c (rA c.idx))
    {q' : ℕ} (tC : List (CellRowB0 q')) (R : Nock.Jet.Registry) :
    ProvP (p := p) (K := K) (RecOKI (denK tC (extB p rA)) R combN) .s
      (pad8 (ServeH.walkPProvs b nodes orbit chals pubs Q)) :=
  provPI_pad8_walk b nodes orbit chals pubs Q fun j bb => by
    have := AtomWalkProvJ8.walkAOK_row δ kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hk hkn hkp hq
      hz htab hseeds.1 hseeds.2 hX hHX hout hs htb hag tC j j.2 bb
    rw [AtomWalkProvJ8.walkEnvFA_eq_wEF] at this
    exact walkAOKI_extB tC p this

end HAW

end

end Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8
