/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomBigJ8.lean

  New
  module, additive.

  * **`extB q r`**: handle `(2, j)` denotes `val l` when row `j` denotes the limb list `l` AND `q ≤ val l`.
    `extB_of_denotes`, `extB_of_extA`.
  * **`denOKX_extB`**: `DenOKX p (denK t (extB p r))` — no premise (`atom` by `rfl`, `cell`: every decoded
    serial is a cell, `decodeTree_cell`; `big` by construction).
  * **`atomInc_provOKB`**: `IncHeadJ8.atomInc_provOK` with `hDen` restricted to big rows (`hDenB`, at `extB`:
    `hDenB_extB`) and one new named premise **`hOldBig`**: every inc head's OLD row denotes a big atom.
  * **`hAW_extB`**: the atom walk's providers at `extB` from `walkAOK_row` (at `extA`) and one new named premise
    **`hRootBig`**: every atom-walk record's root row denotes a big atom.
  * `hold` (`AtomCombJ8.hold_of_served`) reads no denotation: unaffected.

  The inc head's old row is any `mh`-exported row (`ConsumeServedQ`); with `old = [0, B − 1]`
  (value `p − 1`, not big) g7.1/g7.2 give `new = [1, B − 1] = p`, which passes `bnd mi`.  The atom walk's roots
  are any table rows (`KeysExported`).  Under the restricted denotation such a provided record has no
  `RecOK` / `WalkAOK`, so the existence-form provider obligations of `RecOKA` cannot be met at `extB` from the
  gates alone.  Either a gate (old head big: `mi·inc·(1 − kR_o)·(l_o·inv − 1) = 0`, and a root-big check on the
  atom walk) or implication-form obligations ("if the old / root handle denotes, …", the compute side supplies
  the antecedent) close it.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CorJ8A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf padK)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads atomChipHQ incKey tagInc atomGates)
open Nock.NockVMROM.Thm54.VclL.Handle.IncHeadJ8 (len_cases8)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA extA_of_denotes denotes_unique)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (recNat)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.Atoms (val B limbs)

noncomputable section

/-! ## 1. The big-row denotation -/

open Classical in
/-- **The external-atom denotation restricted to big rows**: `(2, j)` denotes `val l` when row `j` denotes `l`
and `q ≤ val l`. -/
def extB (q : ℕ) (r : ℕ → ARow) (j : ℕ) : Option Noun :=
  if h : ∃ l, Denotes r j l ∧ q ≤ val l then some (.atom (val (Classical.choose h))) else none

theorem extB_of_denotes {q : ℕ} {r : ℕ → ARow} {j : ℕ} {l : List ℕ} (h : Denotes r j l) (hq : q ≤ val l) :
    extB q r j = some (.atom (val l)) := by
  have he : ∃ l, Denotes r j l ∧ q ≤ val l := ⟨l, h, hq⟩
  simp only [extB, dif_pos he]
  rw [denotes_unique (Classical.choose_spec he).1 h]

theorem extB_big {q : ℕ} {r : ℕ → ARow} {j : ℕ} {X : Noun} (h : extB q r j = some X) :
    ∃ n, X = .atom n ∧ q ≤ n := by
  unfold extB at h
  split_ifs at h with he
  · exact ⟨_, (Option.some.inj h).symm, (Classical.choose_spec he).2⟩

theorem extA_some {r : ℕ → ARow} {j : ℕ} {X : Noun} (h : extA r j = some X) :
    ∃ l, Denotes r j l ∧ X = .atom (val l) := by
  unfold extA at h
  split_ifs at h with he
  · exact ⟨_, Classical.choose_spec he, (Option.some.inj h).symm⟩

/-- Every decoded serial is a cell. -/
theorem decodeTree_cell {q : ℕ} (t : List (CellRowB0 q)) (leaf : CellRowB0 q → Side → Option (Option Noun))
    (fuel i : ℕ) {X : Noun} (h : decodeTree t leaf fuel i = some X) : ∃ a c, X = .cell a c := by
  cases fuel with
  | zero => simp [decodeTree] at h
  | succ f =>
    simp only [decodeTree, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, a, _, c, _, hX⟩ := h
    exact ⟨a, c, (Option.some.inj hX).symm⟩

/-- **`DenOKX` at the big-row denotation**, no premise. -/
theorem denOKX_extB {q : ℕ} (t : List (CellRowB0 q)) (p : ℕ) (r : ℕ → ARow) :
    DenOKX p (denK t (extB p r)) where
  atom := fun _ => rfl
  cell := fun i X h => decodeTree_cell t _ _ i h
  big := fun i X h => extB_big h

/-- **`hDen` at `extB`**, on big rows. -/
theorem hDenB_extB {q : ℕ} (t : List (CellRowB0 q)) (p : ℕ) (r : ℕ → ARow) :
    ∀ j l, Denotes r j l → p ≤ val l → denK t (extB p r) (2, j) = some (.atom (val l)) :=
  fun _ _ h hq => extB_of_denotes h hq

/-! ## 2. The inc heads at `extB` -/

section Field
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p}
  {orbit : StrictOrbitDomain (ZMod p) 3 h} {chals pubs : ℕ → K}
  {Q : Fin (atomChipHQ δ b hn nodes orbit chals pubs).rap.w → (ZMod p)[X]}

local notation "AE" => AtomServedQ.aEF b nodes orbit chals pubs Q

/-- **`IncHeadJ8.atomInc_provOK` at a big-row denotation**: `hDen` only on big rows (`hDenB`), and every inc
head's old row big (`hOldBig`, named; see the module docstring). -/
theorem atomInc_provOKB (hq : 2 ^ 63 < p)
    (hsat : (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies Q)
    {r : ℕ → ARow} (hR : ∀ k : Fin n, Reads (AE k) (r k)) (hs : ∀ k : Fin n, (r k).Small)
    (hidx : ∀ k : Fin n, (r k).idx = k)
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}
    (hD0 : ∀ v, D (0, v) = some (.atom v))
    (hDenB : ∀ j l, Denotes r j l → p ≤ val l → D (2, j) = some (.atom (val l)))
    (hold : ∀ k : Fin n, (r k).inc = 1 → ∃ l, Denotes r (r k).idxO l)
    (hOldBig : ∀ k : Fin n, (r k).inc = 1 → ∀ lold, Denotes r (r k).idxO lold → p ≤ val lold)
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
      obtain ⟨hd, -, hv⟩ := AtomChipHQ.conv_sound haL hwR haR
      have hpG1 : 1 ≤ Nock.Atoms.p := by
        show 1 ≤ Nock.Field.p
        unfold Nock.Field.p; norm_num
      show ∃ n : ℕ, D (0, p - 1) = some (.atom n) ∧ D (2, i) = some (.atom (n + 1))
      refine ⟨p - 1, hD0 _, ?_⟩
      rw [hDenB _ _ hd (by rw [hv, hpG]; omega), hv, hpG]
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
      obtain ⟨lnew, hd, hv⟩ := hchain i hinc lold hl0
      have hb0 := hOldBig i hinc lold hl0
      exact ⟨val lold, hDenB _ _ hl0 hb0, by rw [hDenB _ _ hd (by omega), hv]⟩
  · simp [RecOK]
  · simp [RecOK]
  · have hx7 : a7 < p := hlt a7 (by simp)
    have e7 := hent' 7 (by norm_num) (by norm_num)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at e7
    have : a7 = 0 := Nock.Jet.ChipJ8.natCast_inj_lt hx7 (by omega) (by exact_mod_cast e7)
    subst this
    simp [RecOK]

end Field

/-! ## 3. The atom walk's providers at `extB` -/

/-- `WalkAOK` passes from `extA` to `extB` when the record's root row is big. -/
theorem walkAOK_extB {q' : ℕ} (tC : List (CellRowB0 q')) (p : ℕ) {rA : ℕ → ARow} {comb : ℕ → Noun}
    {r : List ℕ} (h : WalkAOK (denK tC (extA rA)) comb r)
    (hbig : ∀ l, Denotes rA (r.headD 0) l → p ≤ val l) :
    WalkAOK (denK tC (extB p rA)) comb r := by
  match r, h, hbig with
  | [rv, ax, lk, lv], ⟨n, hn, h1, h2⟩, hbig =>
    obtain ⟨l, hl, hX⟩ := extA_some hn
    refine ⟨n, ?_, h1, h2⟩
    have hv : n = val l := by simpa using hX
    show extB p rA rv = some (.atom n)
    rw [hv]; exact extB_of_denotes hl (hbig l hl)
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | [_, _], _, _ => trivial
  | [_, _, _], _, _ => trivial
  | _ :: _ :: _ :: _ :: _ :: _, _, _ => trivial

section HAW
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (kroots : ℕ) (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipHQK δ kroots b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

open scoped Classical in
/-- **`hAW` at `extB`**: `AtomWalkProvJ8.hAW_of_atomWalk'` with the denotation restricted to big rows, under
`hRootBig` (every atom-walk record's root row denotes a big atom; named, see the module docstring). -/
theorem hAW_extB
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
    {q' : ℕ} (tC : List (CellRowB0 q')) (R : Nock.Jet.Registry)
    (hRootBig : ∀ j : Fin n, ∀ l, Denotes rA (natOf ((TeleH.wEF b nodes orbit chals pubs Q j).trace WChip.ridx)) l →
      p ≤ val l) :
    ProvP (p := p) (K := K) (RecOKA (denK tC (extB p rA)) R combN) .s
      (pad8 (ServeH.walkPProvs b nodes orbit chals pubs Q)) :=
  AtomWalkProvJ8.provPA_pad8_walk b nodes orbit chals pubs Q fun j bb => by
    have := AtomWalkProvJ8.walkAOK_row δ kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hk hkn hkp hq
      hz htab hseeds.1 hseeds.2 hX hHX hout hs htb hag tC j j.2 bb
    rw [AtomWalkProvJ8.walkEnvFA_eq_wEF] at this
    exact walkAOK_extB tC p this (hRootBig j)

end HAW

/-! ## 4. The ℕ-level witness for the FINDING (`hOldBig` is not implied by the inc relation) -/

/-- Two rows: row `0` is the two-limb `[0, B − 1]` (value `p − 1`), row `1` an inc head on it, `[1, B − 1]`. -/
def exOld : ℕ → ARow := fun i =>
  if i = 0 then ⟨0, 0, 0, 0, B - 1, 0, 0, 0, 0, 0, 0⟩ else ⟨1, 1, 0, 0, B - 1, 1, 0, 0, 0, 0, B - 1⟩

/-- **ℕ-level witness (kernel):** an inc head whose old row denotes `p − 1 < p` (not big) while its new row denotes
`p`, with the boundary condition of an `mi` row (`aR = B − 1`, `aL ≠ 0`) and the stop link (`aL = l_o + 1`,
`wR = kR_o`, `valR = vR_o`) holding.  So `hOldBig` does not follow from the inc relation and `bnd mi`; the
gate-level trace is not compiled here (argument in the module docstring). -/
theorem oldBig_not_implied :
    (exOld 1).inc = 1 ∧ Denotes exOld (exOld 1).idxO [0, B - 1] ∧ val [0, B - 1] < Nock.Atoms.p ∧
      Denotes exOld 1 [1, B - 1] ∧ val [1, B - 1] = val [0, B - 1] + 1 ∧ Nock.Atoms.p ≤ val [1, B - 1] ∧
      (exOld 1).aR = B - 1 ∧ (exOld 1).aL ≠ 0 ∧ (exOld 1).aL = (exOld 1).lO + 1 ∧
      (exOld 1).wR = (exOld 1).kRO ∧ (exOld 1).aR = (exOld 1).vRO := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, by decide, rfl, rfl, rfl⟩
  · exact Denotes.top (r := exOld) (i := 0) rfl
  · simp [val, B, Nock.Field.p, Nat.ofDigits]
  · exact Denotes.top (r := exOld) (i := 1) rfl
  · simp [val, B, Nat.ofDigits]
  · simp [val, B, Nock.Field.p, Nat.ofDigits]

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8
