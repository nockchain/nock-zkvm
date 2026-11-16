/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomWalkProvJ8.lean

  New module, additive.

  * **`walkAOK_row`**: on a `walkChipHQK`-accepted atom-walk trace, outside the SAME `walkEvent`, over an
    accepted one-provider table (`TableAccepts` at the walk's limb coin, `hT2`, `hdy`, `KeysExported`, the
    handle-export lookup `hHX`, i.e. `AtomWalkAW.atomWalk_records_genuine`'s premises), whose rows agree with
    the ℕ reading `rA` (`AtomCombJ8.AgreeRow`) under `SerialOK`: every row's record `recNat` (both sides) meets
    `WalkAOK (denK t (extA rA)) combN` — the root denotes `atom (val l)` with `Denotes rA root l`, its comb is
    the canonical `combN (val l)`, a kind-0 child is the comb's limb, a kind-1 child a comb node.
  * **`provPA_pad8_walk`**: a padded walk provider list (`pad8 (walkPProvs …)`) meets `ProvP RecOKA.s` once
    every row's `recNat` meets `WalkAOK`: a 4-entry key is the row's `recNat` (`WalkKJ8.natKey_walk`); any
    other length is not `walkRecA`-shaped and its padded zero entries 4 / 7 miss the inc / jet tags.
  * **`hAW_of_atomWalk`**: the two composed: `FinalJ8A`'s `hAW`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8
import Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8
import Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (recNat bitF zq_val zq_axis natKey_walk childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA extA_of_denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (natKey padK)
open Nock.ComputeTable (FP)
open Nock.Atoms (val)
open Module
open scoped Polynomial

noncomputable section

section Row
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (kroots : ℕ) (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipHQK δ kroots b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

open scoped Classical in
/-- **Every atom-walk record meets the weakened clause `WalkAOK`** (see the module docstring). -/
theorem walkAOK_row
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
    (hT2 : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
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
    {q' : ℕ} (tC : List (CellRowB0 q')) :
    ∀ j < n, ∀ bb : Bool,
      WalkAOK (denK tC (extA rA)) combN (recNat (walkEnvFA δ kroots b hn nodes orbit chals pubs Q j) bb) := by
  have hF := GeneratedField.primeFieldElems_zmod p
  intro j hj bb
  haveI : NeZero (ringChar (ZMod p)) := ⟨(Fact.out : (ringChar (ZMod p)).Prime).ne_zero⟩
  obtain ⟨ri, rt, nn, h1, h2, h3, h4⟩ := atomWalk_records_genuine δ kroots b hn nodes orbit chals pubs Q hsat
    hbind hinj hadj hF hk hkn hkp hq hz htab hT2 hdy hX hHX hout (j + 1) (by omega) (by omega) bb
  simp only [Nat.add_sub_cancel] at h3
  set eA := walkEnvFA δ kroots b hn nodes orbit chals pubs Q j
  have hr : (walkEnvF b hn nodes orbit chals pubs (restrictWalkK δ kroots b hn nodes orbit chals pubs Q) j).trace
      WChip.ridx = eA.trace WChip.ridx :=
    (walkEnvFA_trace δ kroots b hn nodes orbit chals pubs Q j (by decide)).symm
  have hpre : (walkEnvF b hn nodes orbit chals pubs (restrictWalkK δ kroots b hn nodes orbit chals pubs Q) j).trace
      WChip.pre = eA.trace WChip.pre :=
    (walkEnvFA_trace δ kroots b hn nodes orbit chals pubs Q j (by decide)).symm
  have h1' : zq (eA.trace WChip.ridx) = (ri : ZMod (ringChar (ZMod p))) := by rw [← hr]; exact h1
  have hri_lt : ri < ringChar (ZMod p) := lt_of_lt_of_le (denH_true_lt h2) (by simpa using htb)
  have hri : natOf (eA.trace WChip.ridx) = ri := by
    have := congrArg ZMod.val h1'
    rw [zq_val hF, ZMod.val_natCast, Nat.mod_eq_of_lt hri_lt] at this
    exact this
  have hax : natOf (2 * eA.trace WChip.pre + bitF bb) =
      (2 * zq ((walkEnvF b hn nodes orbit chals pubs (restrictWalkK δ kroots b hn nodes orbit chals pubs Q)
        j).trace WChip.pre) + bitZ bb).val := by
    rw [hpre, ← zq_axis hF, zq_val hF]
  obtain ⟨l, hl, hrt, hcomb⟩ := denH_denotes hs hag h2
  have h4' : Noun.slot (2 * zq ((walkEnvF b hn nodes orbit chals pubs
      (restrictWalkK δ kroots b hn nodes orbit chals pubs Q) j).trace WChip.pre) + bitZ bb).val rt = some nn := h4
  -- the child, by kind
  have hkid : ∀ (k v : ZMod p), childHOf eA bb = (decide (k = 1), natOf v) →
      (natOf k = 0 → nn = .atom (natOf v)) ∧ (natOf k = 1 → ∃ a c, nn = .cell a c) := by
    intro k v hc
    rw [hc] at h3
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · have : k = 0 := by rw [← natOf_cast hF k, h0]; simp
      subst this
      simpa using h3.symm
    · have : k = 1 := by rw [← natOf_cast hF k, h1]; simp
      subst this
      exact denH_true_cell (by simpa using h3)
  have hkid' := hkid (if bb then eA.trace WalkHC.kR else eA.trace WalkHC.kL)
    (if bb then eA.trace WalkHC.vR else eA.trace WalkHC.vL) (by cases bb <;> rfl)
  simp only [recNat, childHOfK, WalkAOK]
  refine ⟨val l, ?_, ?_, ?_⟩
  · rw [hri]; exact extA_of_denotes hl
  · intro hk0
    have e := hkid'.1 (by cases bb <;> simpa using hk0)
    rw [hax, hcomb, ← hrt, h4', e]
    cases bb <;> rfl
  · intro hk1
    obtain ⟨a, c, e⟩ := hkid'.2 (by cases bb <;> simpa using hk1)
    refine ⟨a, c, ?_⟩
    rw [hax, hcomb, ← hrt, h4', e]

end Row

section Pad
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {D : LocalVSX.HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun}

/-- **The padded walk provider list meets `RecOKA` at `.s`** once every row's `recNat` meets `WalkAOK`. -/
theorem provPA_pad8_walk {h n : ℕ} (b : Basis (Fin 3) (ZMod p) K) (nodes : Fin n → ZMod p)
    (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K) {w : ℕ} (Q : Fin w → (ZMod p)[X])
    (hrow : ∀ j : Fin n, ∀ bb : Bool, WalkAOK D comb (recNat (TeleH.wEF b nodes orbit chals pubs Q j) bb)) :
    ProvP (p := p) (K := K) (RecOKA D R comb) .s (pad8 (ServeH.walkPProvs b nodes orbit chals pubs Q)) := by
  intro q hq l hlen hlt hkey
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hq0
  set e := TeleH.wEF b nodes orbit chals pubs Q j
  obtain ⟨bb, hbb⟩ : ∃ bb : Bool, q0.1 = ServeH.keyVec5 (if bb then WalkHC.recRH else WalkHC.recLH) e := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  -- the key, entrywise
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
    match l, h4, hlt, hkey with
    | [a0, a1, a2, a3], _, hlt, hkey =>
      have hk5 : natKey (p := p) (K := K) 5 [a0, a1, a2, a3] =
          ServeH.keyVec5 (if bb then WalkHC.recRH else WalkHC.recLH) e := by
        funext c
        have := congrFun hkey ⟨c, by omega⟩
        simpa [natKey, padK, hbb, show (c : ℕ) < 5 from c.2] using this
      rw [natKey_walk e bb a0 a1 a2 a3 hlt hk5]
      exact hrow j bb
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

theorem walkEnvFA_eq_wEF (j : Fin n) :
    walkEnvFA δ kroots b hn nodes orbit chals pubs Q j = TeleH.wEF b nodes orbit chals pubs Q j := by
  simp [walkEnvFA, TeleH.wEF, j.2]

open scoped Classical in
/-- **`hAW`** (`FinalJ8A.acceptsJ8_holdsN'`): the atom walk's padded providers meet `RecOKA` at `.s`, at
`D = denK tC (extA rA)` and `comb = combN`, under `walkAOK_row`'s hypotheses. -/
theorem hAW_of_atomWalk
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
    (hT2 : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
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
    ProvP (p := p) (K := K) (RecOKA (denK tC (extA rA)) R combN) .s
      (pad8 (ServeH.walkPProvs b nodes orbit chals pubs Q)) :=
  provPA_pad8_walk b nodes orbit chals pubs Q fun j bb => by
    have := walkAOK_row δ kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hk hkn hkp hq hz htab hT2
      hdy hX hHX hout hs htb hag tC j j.2 bb
    rwa [walkEnvFA_eq_wEF] at this

/-- The atom walk's two table-side seed events at its limb coin (`hT2`, `hdy` of `atomWalk_records_genuine`), as
one proposition whose decidability instances are fixed here. -/
def AWSeedsOK (z : Quad (algebraMap (ZMod p) K δ))
    (tb : List (CellRow (ringChar (ZMod p)) (Quad (algebraMap (ZMod p) K δ)))) : Prop :=
  z ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [] ∧ z ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0))

open scoped Classical in
/-- `hAW_of_atomWalk` with the two seed events bundled (`AWSeedsOK`). -/
theorem hAW_of_atomWalk'
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
    (hseeds : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3)) tb)
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
    ProvP (p := p) (K := K) (RecOKA (denK tC (extA rA)) R combN) .s
      (pad8 (ServeH.walkPProvs b nodes orbit chals pubs Q)) :=
  hAW_of_atomWalk δ kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hk hkn hkp hq hz htab hseeds.1
    hseeds.2 hX hHX hout hs htb hag tC R

end HAW

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8
