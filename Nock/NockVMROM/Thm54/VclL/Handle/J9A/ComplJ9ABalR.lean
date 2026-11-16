/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalR.lean

* `xConsumesX9_mem`, `xEnt_s10S`: the twin analogue of J-8's `xConsumesP_mem`; no active `.x` entry on `s10S`.
  * `xcons9_row_range`: the twin `.x` consumes of one J-9 A row have in-range serials (from `xEnt_par9`; the serial
    is the round-0 handle `hv (hN l.rn kP)` of a cell of the table, `idxOf` of a member).
  * **`hrangeA_of`**: the `hrangeA` binder of `ComplJ9ABalG1.hGx_A_of`, verbatim, from the walk-node fact `hwcellA`
    (the exact `hwcellA` binder of `hGx_A_of`), `|cells| < p`, the J export `kN = 1` row fact (`jReads_range`) and
    the row-level cell fact `hrowsA` (every J-9 A row's cell handle nouns are cells of the table, with the row facts
    `RowOKX` / `s3` of `ComplJ9ABase.old_facts`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalCX
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalG1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalR

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc selS)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
  (slotsX9 slot0X9 slot1X9 slot2X9 slot3X9 statesX9 extSlot ents0New ents1New ents2New ents3New sS0B sS10B sS10S)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 ChipSt9 SemN9 rowsOfT9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf hdlP hdlOK_hdlP NamedRecs cellPairs)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalCX (ent_cases9 states_okX selS_eval9 xEnt_par9)

noncomputable section

section Row
variable {p : ℕ} [Fact p.Prime]

/-- Membership in the twin's export consumes (twin of `ComplJ8Data.xConsumesP_mem`). -/
theorem xConsumesX9_mem {e : Nock.Reified.Env (ZMod p)} {q : ℕ × ℕ}
    (hq : q ∈ ComplJ9ADataRec.xConsumesX9 p e) :
    ∃ S ∈ (slotsX9 : List (SlotX (ZMod p))), ∃ x ∈ S.ents, x.bal = .x ∧
      x.act.eval e ≠ 0 ∧ ∃ i tail, x.rcd = .col i :: tail ∧ q.1 = (e.trace i).val := by
  unfold ComplJ9ADataRec.xConsumesX9 at hq
  obtain ⟨S, hS, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨x, hx, hq⟩ := List.mem_filterMap.mp hq
  obtain ⟨hx, hb⟩ := List.mem_filter.mp hx
  refine ⟨S, hS, x, hx, by simpa using hb, ?_⟩
  simp only at hq
  split_ifs at hq with h0
  refine ⟨fun h => h0 (by rw [h]; exact ZMod.val_zero), ?_⟩
  split at hq
  · rename_i i tail hr
    simp only [Option.some.injEq] at hq
    exact ⟨i, tail, hr, by rw [← hq]⟩
  · simp at hq

/-- **No active `.x` entry on an `s10S` row.** -/
theorem xEnt_s10S (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (l : LX9)
    (fst lst : ZMod p) (hc : l.chip = .s10S)
    (S : SlotX (ZMod p)) (hS : S ∈ (slotsX9 : List (SlotX (ZMod p)))) (x : EntX (ZMod p)) (hx : x ∈ S.ents)
    (hb : x.bal = .x)
    (hact : x.act.eval (⟨colX9 H pd idOf l fst lst, colX9 H pd idOf l fst lst, fun _ => 0, fun _ => 0⟩ :
      Nock.Reified.Env (ZMod p)) ≠ 0) : False := by
  have hsel : (selS x.states : CoeffExpr (ZMod p)).eval
      (⟨colX9 H pd idOf l fst lst, colX9 H pd idOf l fst lst, fun _ => 0, fun _ => 0⟩ :
        Nock.Reified.Env (ZMod p)) ≠ 0 := fun h => hact (by simp [EntX.act, CoeffExpr.eval, h])
  rw [selS_eval9] at hsel
  rcases ent_cases9 S hS x hx with ⟨S0, hS0, hx0⟩ | h0 | h1 | h2 | h3
  · have hlt := states_okX S0 hS0 x hx0
    apply hsel
    refine List.sum_eq_zero fun v hv => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    have := hlt i hi
    simp [colX9, hc, colS10S, this]
  · simp only [ents0New, List.mem_singleton] at h0
    subst h0
    apply hsel
    simp [colX9, hc, colS10S, sS0B, sS10B]
  · simp only [ents1New, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl
    · apply hsel
      simp [colX9, hc, colS10S, sS10B]
    · simp at hb
  · simp only [ents2New, List.mem_singleton] at h2
    subst h2
    apply hsel
    simp [colX9, hc, colS10S, sS10B]
  · simp only [ents3New, List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with rfl | rfl <;> simp at hb

/-- **The twin `.x` consumes of one J-9 A row are cells of the table** (in range): the serial of a consume is the
round-0 handle of a cell handle noun (`xEnt_par9`), i.e. the `idxOf` of a member of the table. -/
theorem xcons9_row_range {R : Nock.Jet.Registry} (cs acs : List Noun) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (idOf : ℕ → ℕ) (l : LX9) (fst lst : ZMod p) (hsem : SemN9 R l)
    (hok : l.chip = .old → HonestCompX.RowOKX p l.rn)
    (hs3 : l.chip = .old → l.rn.st = .s3 → l.rn.sf1.isCell = true → l.rn.sf1 = .cell l.rn.ftth l.rn.fttt)
    (hcell : ∀ k < 12, (HonestCompX.hN l.rn k).isCell = true → HonestCompX.hN l.rn k ∈ cs)
    (hlen : cs.length < p) :
    ∀ q ∈ ComplJ9ADataRec.xConsumesX9 p (⟨colX9 (hdlP p cs acs) pd idOf l fst lst,
      colX9 (hdlP p cs acs) pd idOf l fst lst, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p)),
      q.1 < cs.length := by
  intro q hq
  obtain ⟨S, hS, x, hx, hb, hact, i, tail, hr, hq1⟩ := xConsumesX9_mem hq
  obtain ⟨kP, kL, kR, hr', hcellEq, hk, -, -⟩ :=
    xEnt_par9 (R := R) (hdlP p cs acs) pd idOf l fst lst hsem hok (hdlOK_hdlP p cs acs) hs3 S hS x hx hb hact
  rw [hr'] at hr
  simp only [ChipHX.cellRecX, ChipHX.recOf, ChipH.cellRec, List.map_cons, List.cons.injEq, ChipHX.RE.col.injEq] at hr
  have hX : Nock.V1J8.FillX.colXE (F := ZMod p) (hdlP p cs acs) pd l.rn fst lst (ChipHX.hdX kP).v =
      HonestCompX.hv (hdlP p cs acs) (HonestCompX.hN l.rn kP) := by
    have h1 : ¬ (ChipHX.hdX kP).v < 17 := by simp only [ChipHX.hdX]; omega
    have h2 : (ChipHX.hdX kP).v < 49 := by simp only [ChipHX.hdX]; omega
    simp only [Nock.V1J8.FillX.colXE, ChipHX.hdX] at h1 h2 ⊢
    erw [if_neg h1, if_neg (show ¬ (26 + 2 * kP = 17) by omega), if_neg (show ¬ (26 + 2 * kP = 18) by omega), if_neg (show ¬ (26 + 2 * kP = 19) by omega), if_neg (show ¬ (26 + 2 * kP = 20) by omega), if_neg (show ¬ (26 + 2 * kP = 21) by omega), if_neg (show ¬ (26 + 2 * kP = 22) by omega), if_neg (show ¬ (26 + 2 * kP = 23) by omega), if_neg (show ¬ (26 + 2 * kP = 24) by omega), if_pos h2,
      if_neg (show ¬ ((26 + 2 * kP - 25) % 2 = 0) by omega)]
    congr 2; omega
  have hX' : HonestCompX.colX (hdlP p cs acs) pd l.rn fst lst (ChipHX.hdX kP).v =
      HonestCompX.hv (hdlP p cs acs) (HonestCompX.hN l.rn kP) := by
    rw [← hX, Nock.V1J8.FillX.colXE_eq]
  have hmid1 : 17 ≤ (ChipHX.hdX kP).v := by simp only [ChipHX.hdX]; omega
  have hmid2 : (ChipHX.hdX kP).v < 123 := by simp only [ChipHX.hdX]; omega
  have hcol : colX9 (hdlP p cs acs) pd idOf l fst lst (ChipHX.hdX kP).v =
      HonestCompX.hv (hdlP p cs acs) (HonestCompX.hN l.rn kP) := by
    cases hc : l.chip
    · rw [colX9_old _ _ _ l fst lst hc]; exact hX'
    · simp only [colX9, hc]
      rw [colS0B_mid (h1 := hmid1) (h2 := hmid2)]; exact hX'
    · simp only [colX9, hc]
      rw [colS10B_mid (h1 := hmid1) (h2 := hmid2)]; exact hX'
    · exact (xEnt_s10S (hdlP p cs acs) pd idOf l fst lst hc S hS x hx hb hact).elim
  have hcl : (HonestCompX.hN l.rn kP).isCell = true := by rw [hcellEq]; rfl
  have hmem := hcell kP hk hcl
  have hq1' : q.1 = (colX9 (hdlP p cs acs) pd idOf l fst lst i).val := hq1
  rw [hq1', ← hr.1, hcol]
  rcases hN : HonestCompX.hN l.rn kP with v | ⟨a, b⟩
  · rw [hN] at hcl; simp [Noun.isCell] at hcl
  · rw [hN] at hmem
    have hlt := ComplJ8Data.idxOf_lt cs _ hmem
    simp only [HonestCompX.hv, hdlP]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    exact hlt

end Row

/-! ## `hrangeA` -/

section Range
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalX (xRecsA basesA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (WalkDepthOK9A)
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => j9aDataOf p Rg Rt hgen

/-- **`hrangeA`** (the `hrangeA` binder of `ComplJ9ABalG1.hGx_A_of`, verbatim): the serial range of the `hGx`
consumers.  Compute: `xcons9_row_range` at every J-9 A row; walk: `cellPairs_range` with the walk-node fact
`hwcellA` (the exact `hwcellA` binder of `hGx_A_of`); J: `ComplJ8Data.jReads_range`. -/
theorem hrangeA_of [Fact (ringChar (ZMod p)).Prime] (hwalk9 : WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwcellA : ∀ u ∈ walkRows (DA).cells (DA).reads, u.label.node ∈ (DA).cells)
    (hlen : (DA).cells.length < p)
    (hkN : ∀ x ∈ (j8DataOf p Rg Rt hgen).jrows,
      (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1)
    (hrowsA : ∀ l ∈ (rowsOfT9 t).toList,
      (l.chip = .old → HonestCompX.RowOKX p l.rn) ∧
      (l.chip = .old → l.rn.st = .s3 → l.rn.sf1.isCell = true → l.rn.sf1 = .cell l.rn.ftth l.rn.fttt) ∧
      ∀ k < 12, (HonestCompX.hN l.rn k).isCell = true → HonestCompX.hN l.rn k ∈ (DA).cells) :
    ∀ q ∈ (xRecsA (DA) (basesA p Rg Rt hgen)).flatMap ComplJ8Data.NamedRecs.recs, 0 < q.2 →
      q.1 < (DA).cells.length := by
  intro q hq _
  simp only [xRecsA, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hq
  rcases hq with hq | hq | hq
  · -- compute
    obtain ⟨b, hb, hq⟩ := List.mem_flatMap.mp hq
    simp only [basesA, ComplJ9ADataRec.basesA9, List.mem_map, List.mem_range] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    have hl : HonestWalkX9.rowAt9 (bfsForest [ComplJ9AGen.genX9T t]) (j + 1) ∈ (rowsOfT9 t).toList := by
      simp only [rowsOfT9, List.toList_toArray, List.mem_map, HonestWalkX9.rowAt9]
      refine ⟨(bfsForest [ComplJ9AGen.genX9T t])[j], List.getElem_mem _, ?_⟩
      simp [List.getElem?_eq_getElem hj]
    obtain ⟨hok, hs3, hc⟩ := hrowsA _ hl
    exact xcons9_row_range (R := Rg.R) _ _ _ _ _ _ _ (ComplJ9AGen.rowsOfT9_semN9 hgen _ hl) hok hs3 hc hlen q hq
  · -- walk
    refine ComplJ8Data.cellPairs_range _ _ ?_ q hq
    intro a b hab
    obtain ⟨w, hw, e⟩ := List.mem_map.mp hab
    have hperm := ComplJ8OfBal.walkGen_nodes_perm (DA).cells (DA).reads
      (ComplJ9ABalGen.hall_readsA Rt hgen) (fun r hr => (ComplJ9ADataRec.walkDepthOK_readsA Rt hgen hwalk9 r hr).trans (by norm_num))
    have hws : (DA).ws = (Nock.V1J8.Gen.walkGen ((DA).cells.headD (.atom 0)) (DA).reads).1 := rfl
    rw [hws] at hw
    have hm := (hperm.mem_iff).mp (List.mem_map.mpr ⟨w, hw, rfl⟩)
    obtain ⟨u, hu, hue⟩ := List.mem_map.mp hm
    rw [e] at hue
    rw [← hue]
    exact hwcellA u hu
  · -- J
    exact ComplJ8Data.jReads_range p Rg Rt hgen hlen hkN q hq

end Range

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalR

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalR
#print axioms xConsumesX9_mem
#print axioms xEnt_s10S
#print axioms xcons9_row_range
#print axioms hrangeA_of
end Axioms
