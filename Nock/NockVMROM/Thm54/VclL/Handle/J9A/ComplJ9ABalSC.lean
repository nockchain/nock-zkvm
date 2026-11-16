/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalSC.lean

* `sSum9`: twin of `ComplJ8OfBalG.sSum` over `slotsX9` / `HonestTraceX9.env0` (`Bal.s`).
  * `incT9 jetT9 awT9 axT1 axT2 limbT9`, `sSum9_expand`.
  * `termQX9_s`: the stage-2 row term at `.s` is `sSum9` (twin of `ComplJ9ABalPC.termQX9_p`).
  * `rhoS_rows9`: `accTA 4/5` public = Σ_j termQX9 .s.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalPC

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC

noncomputable section

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX castEntX DX invQX)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (slotsX9 slot0X9 slot1X9 slot2X9 slot3X9 extSlot
  ents0New ents1New ents2New ents3New axRecX limbRecX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 ChipSt9 SemN9 segRow)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow (colX9)

section S9
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
  (chalV pubVal : ℕ → ZMod p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The `.s` reciprocal sum of a J-9 A compute row: twin of `ComplJ8OfBalG.sSum` over `slotsX9`. -/
def sSum9 (j : ℕ) : 𝕂′ :=
  ((slotsX9 (F := ℚ)).map fun S => ((S.ents.filter fun x => decide (x.bal = Bal.s)).map fun x =>
    algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act (HonestTraceX9.env0 H pd idOf W chalV pubVal j)) *
      (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
        (HonestTraceX9.env0 H pd idOf W chalV pubVal j) x.rcd)⁻¹).sum +
    (match S.pair with
     | some (fl, a, c, bb) => if bb = Bal.s then
         algebraMap (ZMod p) 𝕂′ ((HonestTraceX9.env0 H pd idOf W chalV pubVal j).trace fl) *
          ((DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
              (HonestTraceX9.env0 H pd idOf W chalV pubVal j) a)⁻¹ +
           (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
              (HonestTraceX9.env0 H pd idOf W chalV pubVal j) c)⁻¹)
         else 0
     | none => 0)).sum

/-- Row `j`'s inc consume (`s4`, slow) at the twin environment. -/
def incT9 (j : ℕ) : 𝕂′ :=
  algebraMap (ZMod p) 𝕂′ ((HonestTraceX9.env0 H pd idOf W chalV pubVal j).trace 4 *
      (1 - (HonestTraceX9.env0 H pd idOf W chalV pubVal j).trace 61)) *
    (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
      (HonestTraceX9.env0 H pd idOf W chalV pubVal j) ChipHX.incRecX)⁻¹

/-- Row `j`'s jet consume (`s11j`). -/
def jetT9 (j : ℕ) : 𝕂′ :=
  algebraMap (ZMod p) 𝕂′ ((HonestTraceX9.env0 H pd idOf W chalV pubVal j).trace 16) *
    (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
      (HonestTraceX9.env0 H pd idOf W chalV pubVal j) ChipHX.jetRecX)⁻¹

/-- Row `j`'s atom-walk pair consume (`pr2`). -/
def awT9 (j : ℕ) : 𝕂′ :=
  algebraMap (ZMod p) 𝕂′ ((HonestTraceX9.env0 H pd idOf W chalV pubVal j).trace 64) *
    ((DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
        (HonestTraceX9.env0 H pd idOf W chalV pubVal j) (ChipHX.walkRecAX ChipHX.xFtth ChipHX.xL1))⁻¹ +
      (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
        (HonestTraceX9.env0 H pd idOf W chalV pubVal j) (ChipHX.walkRecAX ChipHX.xFttt ChipHX.xL2))⁻¹)

/-- A `[col]`-gated consume of a record at the twin environment. -/
def gT9 (c : ℕ) (r : List ChipHX.RE) (j : ℕ) : 𝕂′ :=
  algebraMap (ZMod p) 𝕂′ ((HonestTraceX9.env0 H pd idOf W chalV pubVal j).trace c) *
    (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
      (HonestTraceX9.env0 H pd idOf W chalV pubVal j) r)⁻¹

theorem sSum9_expand (j : ℕ) :
    sSum9 δ b H pd idOf W chalV pubVal j = incT9 δ b H pd idOf W chalV pubVal j +
      jetT9 δ b H pd idOf W chalV pubVal j + awT9 δ b H pd idOf W chalV pubVal j +
      gT9 δ b H pd idOf W chalV pubVal 123 (axRecX ChipHX.xS ChipHX.xFt ChipHX.xE) j +
      gT9 δ b H pd idOf W chalV pubVal 124 (axRecX ChipHX.xE ChipHX.xFtth ChipHX.xSf1) j +
      gT9 δ b H pd idOf W chalV pubVal 125 limbRecX j := by
  unfold sSum9 incT9 jetT9 awT9 gT9
  simp [slotsX9, slot0X9, slot1X9, slot2X9, slot3X9, extSlot, ents0New, ents1New, ents2New, ents3New,
    ChipHX.slotsX, ChipHX.slot0X, ChipHX.slot1X, ChipHX.slot2X, ChipHX.slot3X,
    EntX.act, ChipHX.evalQX, ChipH.selS, ChipH.notC, ChipH.cc, CoeffExpr.sumList, ChipHX.fastX, ChipHX.sS11j,
    ChipHX.pr2X, ChipHX9.sS0B, ChipHX9.sS10B, ChipHX9.sS10S]
  ring

end S9

section Col64
variable {F : Type} [Field F] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)

/-- **The pair flag column `64` (`pr2`) is boolean on every honest row.** -/
theorem col64_bool (l : LX9) (fst lst : F) :
    ComplJ9ACompRow.colX9 H pd idOf l fst lst 64 = 0 ∨ ComplJ9ACompRow.colX9 H pd idOf l fst lst 64 = 1 := by
  have hc2 : ∀ r : RowNX, HonestCompX.cPr2 (F := F) H r = 0 ∨ HonestCompX.cPr2 (F := F) H r = 1 := by
    intro r
    unfold HonestCompX.cPr2
    split_ifs
    · right; rfl
    · left; rfl
  cases hc : l.chip with
  | old => rw [ComplJ9ACompRow.colX9_old H pd idOf l fst lst hc, HonestCompX.cx64]; exact hc2 _
  | s0B =>
    have : ComplJ9ACompRow.colX9 H pd idOf l fst lst 64 = HonestCompX.cPr2 (F := F) H l.rn := by
      simp [ComplJ9ACompRow.colX9, hc, ComplJ9ACompRow.colS0B, HonestCompX.colX]
    rw [this]; exact hc2 _
  | s10B =>
    have : ComplJ9ACompRow.colX9 H pd idOf l fst lst 64 = HonestCompX.cPr2 (F := F) H l.rn := by
      simp [ComplJ9ACompRow.colX9, hc, ComplJ9ACompRow.colS10B, HonestCompX.colX]
    rw [this]; exact hc2 _
  | s10S =>
    left
    simp [ComplJ9ACompRow.colX9, hc, ComplJ9ACompRow.colS10S]

end Col64

section TermS9
open Nock.NockVMROM.Thm54.VclL.HonestTraceX9 (env0 env1 preT9 invV9 baseT9 r0 r0_iff okFs9 trX9_pre limb_inv9
  limb_invIm9 slot_index9)
open Nock.NockVMROM.Thm54.VclL.HonestWalkX9 (rowAt9 fl1 llW)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleX9 (termQX9)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
  (chalV pubVal : ℕ → ZMod p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

set_option maxHeartbeats 2000000 in
/-- **The compute row's `.s` balance term (twin of `termQX9_p`)**: at the stage-2 environment it is `sSum9`
(the `.s` pair, slot 3's `pr2X`, needs its two denominators nonzero when its flag is `1`). -/
theorem termQX9_s (j : ℕ)
    (hl10 : (rowAt9 W (j + 1)).chip = .s10B → (rowAt9 W (j + 1)).rn.st = .s10)
    (hpair : ∀ S ∈ (slotsX9 : List (SlotX ℚ)), ∀ fl a c bb, S.pair = some (fl, a, c, bb) →
      (env0 H pd idOf W chalV pubVal j).trace fl = 1 →
      TeleCQX.DX δ (Compute.TowerD.gatherEnv b (env0 H pd idOf W chalV pubVal j))
          (env0 H pd idOf W chalV pubVal j) a ≠ 0 ∧
        TeleCQX.DX δ (Compute.TowerD.gatherEnv b (env0 H pd idOf W chalV pubVal j))
          (env0 H pd idOf W chalV pubVal j) c ≠ 0) :
    termQX9 δ b (env1 b δ H pd idOf W chalV pubVal j) .s = ComplJ9ABalSC.sSum9 δ b H pd idOf W chalV pubVal j := by
  set e0 := env0 H pd idOf W chalV pubVal j with he0
  set e1 := env1 b δ H pd idOf W chalV pubVal j with he1
  have hT : e0.trace = colX9 H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) := rfl
  have hOH := ComplJ9ABalPC.onehot9 H pd idOf (rowAt9 W (j + 1)) (fl1 (j + 1)) (llW W (j + 1)) e0 hT
  unfold termQX9 sSum9
  congr 1
  refine List.map_congr_left fun S hS => ?_
  have hS' : castSlotX (F := ZMod p) S ∈ slotsX9 (F := ZMod p) := by
    rw [← TeleX9.slotsX9_cast]; exact List.mem_map_of_mem hS
  have htr : ∀ c, r0 c = true → e1.trace c = e0.trace c := fun c hc => by
    rw [r0_iff] at hc
    show preT9 b δ H pd idOf W chalV pubVal j c = HonestTraceX9.baseT9 H pd idOf W j c
    unfold preT9
    split_ifs <;> first | rfl | omega
  have hcong : ∀ g : CoeffExpr ℚ, HonestTraceX.okC okFs9 g = true →
      ChipHX.evalQX g e1 = ChipHX.evalQX g e0 := by
    intro g hg
    rw [← HonestTraceX.eval_mapC_castX, ← HonestTraceX.eval_mapC_castX]
    refine HonestTraceX.eval_okC okFs9 _ (by rw [HonestTraceX.okC_mapC]; exact hg) e1 e0 fun k i hk => ?_
    cases k <;> simp only [okFs9, Bool.false_eq_true] at hk
    exact htr i hk
  have hokS := List.all_eq_true.mp HonestTraceX9.slotsAct_ok9 S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hokS
  rw [hcong _ hokS.1.1.2]
  obtain ⟨s, hs4, hSs, hinv, hinvIm⟩ := slot_index9 hS'
  have hl1 : Compute.LogUp.limbVal b e1.trace (69 + 6 * s) =
      Quad.re _ (invV9 b δ H pd idOf W chalV pubVal j (HonestTraceX9.slotAt9 s)) := by
    rw [← limb_inv9 b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX9.trX9_pre b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (Or.inl (by have := k.isLt; omega))]
    rfl
  have hl2 : Compute.LogUp.limbVal b e1.trace (72 + 6 * s) =
      Quad.im _ (invV9 b δ H pd idOf W chalV pubVal j (HonestTraceX9.slotAt9 s)) := by
    rw [← limb_invIm9 b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX9.trX9_pre b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (Or.inl (by have := k.isLt; omega))]
    rfl
  have hinvQ : TeleCQX.invQX δ (Compute.TowerD.gatherEnv b e1) S =
      HonestSlotX.aVal b δ (castSlotX S) e0 * (HonestSlotX.dVal b δ (castSlotX S) e0)⁻¹ := by
    have h1 : S.inv = 69 + 6 * s := hinv
    have h2 : S.invIm = 72 + 6 * s := hinvIm
    show Quad.mk _ (Compute.LogUp.limbVal b e1.trace S.inv) (Compute.LogUp.limbVal b e1.trace S.invIm) = _
    rw [h1, h2, hl1, hl2, Quad.mk_re_im, invV9, ← hSs]
  rw [hinvQ, TeleCQX.evalQX_actB, ComplJ8CompPole.aVal_expand, ComplJ8CompPole.dVal_expand]
  have hpw0 := TeleX9.act_pairwise9 hOH hS
  have hpw : S.ents.Pairwise fun x y =>
      algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0) * algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX y.act e0) = 0 :=
    hpw0.imp fun h => by rw [← map_mul, h, map_zero]
  have hrcd : ∀ x : EntX ℚ, (castEntX (F := ZMod p) x).rcd = x.rcd := fun _ => rfl
  have hact : ∀ x : EntX ℚ, (castEntX (F := ZMod p) x).act.eval e0 = ChipHX.evalQX x.act e0 :=
    fun x => TeleCQX.castEntX_act x e0
  simp only [castSlotX, List.map_map, Function.comp_def, hrcd, hact]
  have hsum : ∀ l : List (EntX ℚ), algebraMap (ZMod p) 𝕂′ (l.map fun x => ChipHX.evalQX x.act e0).sum =
      (l.map fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0)).sum := fun l => by
    rw [map_list_sum, List.map_map]; rfl
  rw [map_add, hsum, hsum]
  cases hp : S.pair with
  | none =>
    simp only [map_zero, add_zero]
    have := ComplJ8OfBalG.onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
      (fun x => TeleCQX.DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.s)) 0 0 0 hpw
      (fun h => absurd rfl h)
    simpa using this
  | some q =>
    obtain ⟨fl, a, c, bb⟩ := q
    have hf : algebraMap (ZMod p) 𝕂′ (e0.trace fl) ≠ 0 → ∀ x ∈ S.ents,
        algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0) = 0 := by
      intro hne x hx
      have hfl : e0.trace fl ≠ 0 := fun h => hne (by rw [h, map_zero])
      have h0 := ComplJ9AOfComp.hex9 H pd idOf (castSlotX S) hS' e0 (rowAt9 W (j + 1)) (fl1 (j + 1))
        (llW W (j + 1)) hT hl10 fl a c bb hp hfl (castEntX x) (List.mem_map_of_mem hx)
      rw [← hact, h0, map_zero]
    by_cases hb : bb = Bal.s
    · simp only [hb, if_true]
      have hfb : e0.trace fl = 0 ∨ e0.trace fl = 1 := by
        simp only [slotsX9, List.mem_cons, List.not_mem_nil, or_false] at hS
        rcases hS with rfl | rfl | rfl | rfl
        · simp [slot0X9, extSlot, ChipHX.slot0X] at hp
        · simp [slot1X9, extSlot, ChipHX.slot1X] at hp
        · simp [slot2X9, extSlot, ChipHX.slot2X] at hp
          obtain ⟨-, -, -, rfl⟩ := hp
          simp at hb
        · simp only [slot3X9, extSlot, ChipHX.slot3X, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, -⟩ := hp
          rw [hT, show ChipHX.pr2X = 64 from rfl]
          exact col64_bool H pd idOf _ _ _
      have hfb' : algebraMap (ZMod p) 𝕂′ (e0.trace fl) = 0 ∨ algebraMap (ZMod p) 𝕂′ (e0.trace fl) = 1 := by
        rcases hfb with h | h <;> simp [h]
      have hpf : TeleCQX.pairFX e0 S = e0.trace fl := by simp [TeleCQX.pairFX, hp]
      rw [hpf]
      refine ComplJ8OfBalG.onehot_slot_pair S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
        (fun x => TeleCQX.DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.s))
        (algebraMap (ZMod p) 𝕂′ (e0.trace fl)) _ _ hpw hf hfb' fun h1 => ?_
      have h1' : e0.trace fl = 1 := by
        rcases hfb with h | h
        · rw [h, map_zero] at h1; exact absurd h1 zero_ne_one
        · exact h
      exact hpair S hS fl a c bb hp h1'
    · simp only [hb, if_false, map_zero, add_zero]
      exact ComplJ8OfBalG.onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
        (fun x => TeleCQX.DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.s))
        (algebraMap (ZMod p) 𝕂′ (e0.trace fl)) _ _ hpw hf

/-- **A twin accumulator pair is the sum of the rows' `.s` balance terms** (`accTA 4/5`). -/
theorem rhoS_rows9 (N : ℕ) :
    Quad.mk (algebraMap (ZMod p) K δ) (HonestTraceX9.accV9 b δ H pd idOf W chalV pubVal 4 N)
        (HonestTraceX9.accV9 b δ H pd idOf W chalV pubVal 5 N) =
      ∑ j ∈ Finset.range N, termQX9 δ b (env1 b δ H pd idOf W chalV pubVal j) .s :=
  ComplJ9ABalPC.acc_rows9 δ b H pd idOf W chalV pubVal N 4 .s rfl rfl

end TermS9

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC.sSum9_expand
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC.col64_bool
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC.termQX9_s
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC.rhoS_rows9
