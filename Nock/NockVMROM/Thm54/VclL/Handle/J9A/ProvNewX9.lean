/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ProvNewX9.lean

* `provP_split` (design S2): the split chip's providers `(sid, 2, 0, lo)`, `(sid, 3, 0, hi)` meet `RecOK9`
    at `V = valId nA rA (splitSV Q)`; every zero-padded variant of the 4-entry key is not class `1` / `2`, and
    `RecOK`'s clauses on it are `True` (`recOK9_pad`).
  * `provP_walkV9`: the atom walk's padded providers meet `RecOK9` at
    `V = valId nA rA sv`, for any `sv`, UNGUARDED; needs the table length tie `tb.length = nA` so that the
    exported root `ri < tb.length = nA` reads the atom table through `extA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RowSemChipX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.NounAx
import Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8
import Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8
import Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ProvNewX9

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
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9 RecOK9I WalkAOK9 recClass PreI9)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA extA_of_denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (ProvP)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (natKey padK)
open Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9 (splitProvs spEF splitValN sp_rowEqs sp_ctr sp_limbs
  splitVal_comb key2 key3 keyVecL splitChipJ9)
open Nock.J9A.NounAx (valId)
open Nock.Atoms (val)
open Module
open scoped Polynomial

noncomputable section

section Pad
variable {p : ℕ} [Fact p.Prime]

/-- **A padded variant of a 4-entry key is neither class `1` nor class `2`, and `RecOK`'s clauses on it are
`True`**: length `≠ 4` with zero entries `4` and `7`. -/
theorem recOK9_pad (D : LocalVSX.HX → Option Noun) (V : ℕ → Option ℕ) (R : Nock.Jet.Registry) (l : List ℕ)
    (h4 : l.length ≠ 4) (hz4 : l.getD 4 0 = 0) (hz7 : l.getD 7 0 = 0) (hlen : l.length ≤ 8) :
    RecOK9 D V R combN (l, .s) := by
  have hc1 : ¬ (l.length = 8 ∧ l.getLast? = some 5) := by
    rintro ⟨h8, hl⟩
    rw [List.getLast?_eq_getElem?, h8] at hl
    have h7 : 7 < l.length := by omega
    have : l[7]? = some 0 := by
      rw [List.getD_eq_getElem _ _ h7] at hz7
      rw [List.getElem?_eq_getElem h7, hz7]
    simp only [show 8 - 1 = 7 from rfl] at hl
    rw [this] at hl
    simp at hl
  have hr0 : recClass (l, Bal.s) = 0 := by
    simp only [recClass]; rw [if_neg hc1, if_neg h4]
  unfold RecOK9
  have h01 : ¬ (0 : ℕ) = 1 := by omega
  have h02 : ¬ (0 : ℕ) = 2 := by omega
  rw [hr0, if_neg h01, if_neg h02]
  have n5 : ∀ a b c d, l ≠ [a, b, c, d, 4] := by rintro a b c d rfl; simp at hz4
  have n8 : ∀ a b c d e f g, l ≠ [a, b, c, d, e, f, g, 3] := by rintro a b c d e f g rfl; simp at hz7
  unfold RecOK
  split
  all_goals first
    | trivial
    | (rename_i heq; exact absurd heq (n5 _ _ _ _))
    | (rename_i heq; exact absurd heq (n8 _ _ _ _ _ _ _))
    | simp_all

/-- **The key-4 core**: a list `l` (entries `< p`, length `≤ 8`) whose zero-padded entries cast to the 4 field
values `a0 .. a3` (zero afterwards) is, when of length `4`, exactly the `ℕ` record of their `val`s (so
`WalkAOK9` applies) and otherwise a padded variant (`recOK9_pad`). -/
theorem recOK9_key4 (D : LocalVSX.HX → Option Noun) (V : ℕ → Option ℕ) (R : Nock.Jet.Registry) (l : List ℕ)
    (hlen : l.length ≤ 8) (hlt : ∀ e ∈ l, e < p) (a0 a1 a2 a3 : ZMod p)
    (hent : ∀ c, c < 8 → ((l.getD c 0 : ℕ) : ZMod p) = [a0, a1, a2, a3].getD c 0)
    (hw : WalkAOK9 V combN [a0.val, a1.val, a2.val, a3.val]) : RecOK9 D V R combN (l, .s) := by
  have hv : ∀ c, c < 8 → l.getD c 0 = ([a0, a1, a2, a3].getD c 0).val := by
    intro c hc
    have hl : l.getD c 0 < p := by
      rcases Nat.lt_or_ge c l.length with hcl | hcl
      · rw [List.getD_eq_getElem _ _ hcl]; exact hlt _ (List.getElem_mem hcl)
      · rw [List.getD_eq_default _ _ hcl]; exact (Fact.out : p.Prime).pos
    have := congrArg ZMod.val (hent c hc)
    rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hl] at this
  by_cases h4 : l.length = 4
  · match l, h4 with
    | [x0, x1, x2, x3], _ =>
      have e0 := hv 0 (by norm_num)
      have e1 := hv 1 (by norm_num)
      have e2 := hv 2 (by norm_num)
      have e3 := hv 3 (by norm_num)
      simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3
      have hc : recClass ([x0, x1, x2, x3], Bal.s) = 2 := by simp [recClass]
      unfold RecOK9
      rw [if_neg (show ¬ recClass ([x0, x1, x2, x3], Bal.s) = 1 by rw [hc]; omega), if_pos hc]
      simp only
      rw [e0, e1, e2, e3]
      exact hw
  · refine recOK9_pad D V R l h4 ?_ ?_ hlen
    · rw [hv 4 (by norm_num)]; simp
    · rw [hv 7 (by norm_num)]; simp

end Pad

/-! ## 1. S2: the split providers -/

section Split
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))] (nA : ℕ)
  (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

/-- **The split values** `sv s = splitValN hi.val lo.val` of row `s`; `none` past the last row. -/
def splitSV : ℕ → Option ℕ := fun s =>
  if hs : s < n then
    some (SplitChipJ9.splitValN ((spEF b nodes orbit chals pubs Q ⟨s, hs⟩).trace SplitChipJ9.hi).val
      ((spEF b nodes orbit chals pubs Q ⟨s, hs⟩).trace SplitChipJ9.lo).val)
  else none

/-- **S2 `provP_split`**: the split providers meet `RecOK9` at `V = valId nA rA (splitSV Q)`, for any `D`, `Rg`,
`rA`. -/
theorem provP_split (D : LocalVSX.HX → Option Noun) (Rg : Nock.Jet.Registry) (rA : ℕ → ARow)
    (hp : 2 ^ 32 < p)
    (hsat : (splitChipJ9 δF nA b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (splitChipJ9 δF nA b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnAS : nA + n < p) :
    ProvP (p := p) (K := K) (RecOK9 D (valId nA rA (splitSV δF nA b hn nodes orbit chals pubs Q)) Rg combN) .s
      (splitProvs b nodes orbit chals pubs Q) := by
  classical
  intro q hq l hlen hlt hkey
  simp only [DenXJ8.mOf] at hlen hkey
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hq
  set e := spEF b nodes orbit chals pubs Q i with he
  have H := sp_rowEqs δF nA b hn nodes orbit chals pubs Q hsat i
  obtain ⟨-, hid⟩ := sp_ctr δF nA b hn nodes orbit chals pubs Q hsat hbind hinj hadj i
  obtain ⟨hhi, hlo, hnz⟩ := sp_limbs hp H
  have hs2 := (splitVal_comb hhi hlo hnz).2.1
  have hs3 := (splitVal_comb hhi hlo hnz).2.2
  have hpp : 2 < p := by
    have : 2 < 2 ^ 32 := by norm_num
    omega
  have v2 : ((2 : ZMod p)).val = 2 := RowSemChipX9.val_two hpp
  have v3 : ((3 : ZMod p)).val = 3 := by
    simpa using RowSemChipX.val_nat (p := p) (n := 3) (by omega)
  have hSV : valId nA rA (splitSV δF nA b hn nodes orbit chals pubs Q) (nA + (i : ℕ)) =
      some (SplitChipJ9.splitValN (e.trace SplitChipJ9.hi).val (e.trace SplitChipJ9.lo).val) := by
    simp [valId, splitSV, i.isLt, he]
  have hsid : (e.trace SplitChipJ9.sid).val = nA + (i : ℕ) := by
    rw [hid, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  by_cases hm : e.trace SplitChipJ9.mult = 0
  · rw [if_pos hm] at hi; exact absurd hi (List.not_mem_nil)
  · rw [if_neg hm] at hi
    rcases List.mem_cons.mp hi with rfl | hi2
    · refine recOK9_key4 D _ Rg l hlen hlt (e.trace SplitChipJ9.sid) 2 0 (e.trace SplitChipJ9.lo) ?_ ?_
      · intro c hc
        have := congrFun hkey ⟨c, hc⟩
        simp only [natKey, keyVecL] at this
        have h2 := (algebraMap (ZMod p) K).injective this
        interval_cases c <;> simpa [SplitChipJ9.key2, CoeffExpr.eval, SplitChipJ9.sid, SplitChipJ9.lo] using h2
      · simp only [WalkAOK9]
        refine ⟨SplitChipJ9.splitValN (e.trace SplitChipJ9.hi).val (e.trace SplitChipJ9.lo).val, ?_, ?_, ?_⟩
        · rw [hsid, hSV]
        · intro _
          rw [v2]; exact hs2
        · intro h1; rw [ZMod.val_zero] at h1; omega
    · rcases List.mem_cons.mp hi2 with rfl | hi3
      · refine recOK9_key4 D _ Rg l hlen hlt (e.trace SplitChipJ9.sid) 3 0 (e.trace SplitChipJ9.hi) ?_ ?_
        · intro c hc
          have := congrFun hkey ⟨c, hc⟩
          simp only [natKey, keyVecL] at this
          have h2 := (algebraMap (ZMod p) K).injective this
          interval_cases c <;> simpa [SplitChipJ9.key3, CoeffExpr.eval, SplitChipJ9.sid, SplitChipJ9.hi] using h2
        · simp only [WalkAOK9]
          refine ⟨SplitChipJ9.splitValN (e.trace SplitChipJ9.hi).val (e.trace SplitChipJ9.lo).val, ?_, ?_, ?_⟩
          · rw [hsid, hSV]
          · intro _
            rw [v3]; exact hs3
          · intro h1; rw [ZMod.val_zero] at h1; omega
      · exact absurd hi3 (List.not_mem_nil)

end Split


section Row
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (kroots : ℕ) (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipHQK δ kroots b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

open scoped Classical in
/-- **`walkAOK_row` with the atom read through `valId`**: same premises plus the length tie `tb.length = nA`;
the exported root `ri < tb.length = nA` reads the atom table through `extA`, whatever `sv`. -/
theorem walkAOK9_row
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
    {nA : ℕ} (htl : tb.length = nA) (sv : ℕ → Option ℕ) :
    ∀ j < n, ∀ bb : Bool,
      WalkAOK9 (valId nA rA sv) combN (recNat (walkEnvFA δ kroots b hn nodes orbit chals pubs Q j) bb) := by
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
  simp only [recNat, childHOfK, WalkAOK9]
  refine ⟨val l, ?_, ?_, ?_⟩
  · rw [hri]
    have hlt' : ri < nA := by
      have := denH_true_lt h2
      simpa [htl] using this
    simp [valId, hlt', extA_of_denotes hl, Nock.J9A.NounAx.atomOf]
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

/-- **The padded walk provider list meets `RecOK9` at `.s`** once every row's `recNat` meets `WalkAOK9`. -/
theorem provP_pad8_walk9 {h n : ℕ} (b : Basis (Fin 3) (ZMod p) K) (nodes : Fin n → ZMod p)
    (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K) {w : ℕ} (Q : Fin w → (ZMod p)[X])
    (D : LocalVSX.HX → Option Noun) (V : ℕ → Option ℕ) (R : Nock.Jet.Registry)
    (hrow : ∀ j : Fin n, ∀ bb : Bool, WalkAOK9 V combN (recNat (TeleH.wEF b nodes orbit chals pubs Q j) bb)) :
    ProvP (p := p) (K := K) (RecOK9 D V R combN) .s (pad8 (ServeH.walkPProvs b nodes orbit chals pubs Q)) := by
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
  by_cases h4 : l.length = 4
  · match l, h4, hlt, hkey with
    | [a0, a1, a2, a3], _, hlt, hkey =>
      have hk5 : natKey (p := p) (K := K) 5 [a0, a1, a2, a3] =
          ServeH.keyVec5 (if bb then WalkHC.recRH else WalkHC.recLH) e := by
        funext c
        have := congrFun hkey ⟨c, by omega⟩
        simpa [natKey, padK, hbb, show (c : ℕ) < 5 from c.2] using this
      have hc : recClass ([a0, a1, a2, a3], Bal.s) = 2 := by simp [recClass]
      unfold RecOK9
      rw [if_neg (show ¬ recClass ([a0, a1, a2, a3], Bal.s) = 1 by rw [hc]; omega), if_pos hc]
      simp only
      rw [natKey_walk e bb a0 a1 a2 a3 hlt hk5]
      exact hrow j bb
  · exact recOK9_pad D V R l h4 (hz 4 (le_refl _) (by norm_num)) (hz 7 (by norm_num) (by norm_num)) hlen


end Pad

section HAW
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (kroots : ℕ) (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipHQK δ kroots b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

open scoped Classical in
/-- **`provP_walkV9`**: the atom walk's padded providers meet `RecOK9` at
`V = valId nA rA sv` for ANY `sv`, UNGUARDED (no `PreI`), under `hAW_extBI`'s premises and the length tie
`tb.length = nA`. -/
theorem provP_walkV9
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
    {nA : ℕ} (htl : tb.length = nA) (sv : ℕ → Option ℕ)
    (D : LocalVSX.HX → Option Noun) (Rg : Nock.Jet.Registry) :
    ProvP (p := p) (K := K) (RecOK9 D (valId nA rA sv) Rg combN) .s
      (pad8 (ServeH.walkPProvs b nodes orbit chals pubs Q)) :=
  provP_pad8_walk9 b nodes orbit chals pubs Q D (valId nA rA sv) Rg fun j bb => by
    have := walkAOK9_row δ kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hk hkn hkp hq hz htab
      hseeds.1 hseeds.2 hX hHX hout hs htb hag htl sv j j.2 bb
    rwa [AtomWalkProvJ8.walkEnvFA_eq_wEF] at this

end HAW

/-! ## 3. Corollaries at `RecOK9I` -/

section Cor
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]

theorem provP_I {D : LocalVSX.HX → Option Noun} {V : ℕ → Option ℕ} {R : Nock.Jet.Registry} {bl : Bal}
    {provs : List ((Fin (DenXJ8.mOf bl) → K) × K)}
    (h : ProvP (p := p) (K := K) (RecOK9 D V R combN) bl provs) :
    ProvP (p := p) (K := K) (RecOK9I D V R combN) bl provs :=
  fun q hq l hl hlt hk _ => h q hq l hl hlt hk

end Cor

#print axioms provP_split
#print axioms provP_walkV9
#print axioms provP_I

end

end Nock.NockVMROM.Thm54.VclL.Handle.ProvNewX9
