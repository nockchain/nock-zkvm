/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalC.lean

* (1a) `acc_rows9`: the twin of `ComplJ8OfBalG.acc_rows`; the `accV9` totals are the sum of the rows' `𝕂′`
    balance terms `termQX9`.
  * (1b) `xSum9`, `termQX9_x`: the twin of `ComplJ8OfBalG.xSum` / `termQX_x`; a twin row's `.x` balance term is the
    reciprocal sum of its active `.x` entries (at the stage-1 environment `env0`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalG1
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.TeleX9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfComp
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AReadsAt
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalC

open Nock Nock.Noun Nock.Walk Nock.Reified Nock.Framework Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
  (slotsX9 statesX9 OneHotAt9 slot0X9 slot1X9 slot2X9 slot3X9 extSlot)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX castEntX DX invQX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)

noncomputable section

section Rows
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree LX9))
  (chalV pubVal : ℕ → ZMod p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-! ## (1a) the accumulator pair is the sum of the rows' balance terms -/

/-- The honest accumulator term over the cast twin slots is the `ℚ`-template term. -/
theorem termVal_slotsF9 (bl : Bal) (im : Bool) (eF : Env (ZMod p)) :
    Compute.LogUp.termVal b (HonestTraceX9.slotsF9 bl im) eF = TeleCQX.termValX b (TeleX9.slotsB9 bl im) eF := by
  simp only [Compute.LogUp.termVal, TeleCQX.termValX, HonestTraceX9.slotsF9, HonestTraceX9.slotsQ9,
    TeleX9.slotsB9, List.map_map, Function.comp_def, castSlot, HonestTraceX.eval_mapC_castX]

/-- **A twin compute balance's accumulator pair is the sum of the rows' `𝕂′` balance terms.** -/
theorem acc_rows9 (bl : Bal) (a : ℕ)
    (hre : HonestTraceX.accSpec a = (bl, false)) (him : HonestTraceX.accSpec (a + 1) = (bl, true)) :
    Quad.mk (algebraMap (ZMod p) K δ) (HonestTraceX9.accV9 b δ H pd idOf W chalV pubVal a W.length)
        (HonestTraceX9.accV9 b δ H pd idOf W chalV pubVal (a + 1) W.length) =
      ∑ j ∈ Finset.range W.length,
        TeleX9.termQX9 δ b (HonestTraceX9.env1 b δ H pd idOf W chalV pubVal j) bl := by
  simp only [HonestTraceX9.accV9, hre, him]
  rw [← TeleCQX.mk_fsumX]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TeleX9.termQX9_eq, termVal_slotsF9, termVal_slotsF9]

/-! ## (1b) the row's `.x` term -/

/-- The `.x` reciprocal sum of a twin compute row (at the stage-1 environment `env0`). -/
def xSum9 (j : ℕ) : 𝕂′ :=
  ((slotsX9 (F := ℚ)).map fun S => ((S.ents.filter fun x => decide (x.bal = Bal.x)).map fun x =>
    algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act (HonestTraceX9.env0 H pd idOf W chalV pubVal j)) *
      (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX9.env0 H pd idOf W chalV pubVal j))
        (HonestTraceX9.env0 H pd idOf W chalV pubVal j) x.rcd)⁻¹).sum).sum

/-- The honest row at the stage-1 environment is one-hot over the twin states. -/
theorem env0_onehot (j : ℕ) :
    OneHotAt9 (HonestTraceX9.env0 H pd idOf W chalV pubVal j)
      (ComplJ9AReadsAt.sIdx9 (HonestWalkX9.rowAt9 W (j + 1))) := by
  intro i hi
  exact ComplJ9AReadsAt.colX9_onehot H pd idOf _ _ _ i hi

theorem acts_pairwise9 (j : ℕ) (S : SlotX ℚ) (hS : S ∈ (slotsX9 : List (SlotX ℚ))) :
    S.ents.Pairwise fun x y =>
      algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act (HonestTraceX9.env0 H pd idOf W chalV pubVal j)) *
        algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX y.act (HonestTraceX9.env0 H pd idOf W chalV pubVal j)) = 0 := by
  have h := TeleX9.act_pairwise9 (env := HonestTraceX9.env0 H pd idOf W chalV pubVal j)
    (env0_onehot H pd idOf W chalV pubVal j) hS
  refine List.Pairwise.imp (fun hxy => ?_) h
  rw [← map_mul, hxy, map_zero]

/-- **A twin compute row's `.x` balance term is the reciprocal sum of its active export records.**
`hl` is the row fact `s10B → op-10` (`ComplJ9AOfComp.s10B_rows`). -/
theorem termQX9_x (j : ℕ)
    (hl : (HonestWalkX9.rowAt9 W (j + 1)).chip = .s10B → (HonestWalkX9.rowAt9 W (j + 1)).rn.st = .s10) :
    TeleX9.termQX9 δ b (HonestTraceX9.env1 b δ H pd idOf W chalV pubVal j) .x =
      xSum9 δ b H pd idOf W chalV pubVal j := by
  set e0 := HonestTraceX9.env0 H pd idOf W chalV pubVal j with he0
  set e1 := HonestTraceX9.env1 b δ H pd idOf W chalV pubVal j with he1
  unfold TeleX9.termQX9 xSum9
  congr 1
  refine List.map_congr_left fun S hS => ?_
  have hS' : castSlotX (F := ZMod p) S ∈ slotsX9 (F := ZMod p) := by
    rw [← TeleX9.slotsX9_cast]; exact List.mem_map_of_mem hS
  -- the activity reads the base columns
  have htr : ∀ c, HonestTraceX9.r0 c = true → e1.trace c = e0.trace c := fun c hc => by
    rw [HonestTraceX9.r0_iff] at hc
    simp only [he1, he0, HonestTraceX9.env1, HonestTraceX9.env0, HonestTraceX9.preT9]
    rcases hc with hc | hc
    · rw [if_pos hc]
    · rw [if_neg (by omega), if_neg (by omega), if_pos hc]
  have hcong : ∀ g : CoeffExpr ℚ, HonestTraceX.okC HonestTraceX9.okFs9 g = true →
      ChipHX.evalQX g e1 = ChipHX.evalQX g e0 := by
    intro g hg
    rw [← HonestTraceX.eval_mapC_castX, ← HonestTraceX.eval_mapC_castX]
    refine HonestTraceX.eval_okC HonestTraceX9.okFs9 _ (by rw [HonestTraceX.okC_mapC]; exact hg) e1 e0
      fun k i hk => ?_
    cases k <;> simp [HonestTraceX9.okFs9] at hk
    exact htr i hk
  have hokS := List.all_eq_true.mp HonestTraceX9.slotsAct_ok9 S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hokS
  rw [hcong _ hokS.1.1.1.1]
  obtain ⟨s, hs4, hSs, hinv, hinvIm⟩ := HonestTraceX9.slot_index9 hS'
  have hl1 : Compute.LogUp.limbVal b e1.trace (69 + 6 * s) =
      Quad.re _ (HonestTraceX9.invV9 b δ H pd idOf W chalV pubVal j (HonestTraceX9.slotAt9 s)) := by
    rw [← HonestTraceX9.limb_inv9 b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0)
      j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX9.trX9_pre b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (Or.inl (by have := k.isLt; omega))]
    rfl
  have hl2 : Compute.LogUp.limbVal b e1.trace (72 + 6 * s) =
      Quad.im _ (HonestTraceX9.invV9 b δ H pd idOf W chalV pubVal j (HonestTraceX9.slotAt9 s)) := by
    rw [← HonestTraceX9.limb_invIm9 b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0)
      j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX9.trX9_pre b δ H pd idOf W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (Or.inl (by have := k.isLt; omega))]
    rfl
  have hinvQ : invQX δ (Compute.TowerD.gatherEnv b e1) S =
      HonestSlotX.aVal b δ (castSlotX S) e0 * (HonestSlotX.dVal b δ (castSlotX S) e0)⁻¹ := by
    have h1 : S.inv = 69 + 6 * s := hinv
    have h2 : S.invIm = 72 + 6 * s := hinvIm
    show Quad.mk _ (Compute.LogUp.limbVal b e1.trace S.inv) (Compute.LogUp.limbVal b e1.trace S.invIm) = _
    rw [h1, h2, hl1, hl2, Quad.mk_re_im, HonestTraceX9.invV9, ← hSs]
  rw [hinvQ, TeleCQX.evalQX_actB, ComplJ8CompPole.aVal_expand, ComplJ8CompPole.dVal_expand]
  have hpx : ∀ q, S.pair = some q → q.2.2.2 ≠ Bal.x := by
    intro q hq
    simp only [slotsX9, List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl | rfl <;>
      simp [slot0X9, slot1X9, slot2X9, slot3X9, extSlot, ChipHX.slot0X, ChipHX.slot1X, ChipHX.slot2X,
        ChipHX.slot3X] at hq <;>
      rw [← hq] <;> decide
  have hpw := acts_pairwise9 (K := K) δ H pd idOf W chalV pubVal j S hS
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
      (fun x => DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.x)) 0 0 0 hpw
      (fun h => absurd rfl h)
    simpa using this
  | some q =>
    obtain ⟨fl, a, c, bb⟩ := q
    have hb := hpx _ hp
    simp only [hb, if_false, map_zero, add_zero]
    refine ComplJ8OfBalG.onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
      (fun x => DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.x))
      (algebraMap (ZMod p) 𝕂′ (e0.trace fl)) _ _ hpw ?_
    intro hne x hx
    have hfl : e0.trace fl ≠ 0 := fun h => hne (by rw [h, map_zero])
    have h0 := ComplJ9AOfComp.hex9 H pd idOf (castSlotX S) hS' e0 (HonestWalkX9.rowAt9 W (j + 1))
      (HonestWalkX9.fl1 (j + 1)) (HonestWalkX9.llW W (j + 1)) rfl hl
      fl a c bb hp hfl (castEntX x) (List.mem_map_of_mem hx)
    show algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0) = 0
    rw [← hact, h0, map_zero]

end Rows

#print axioms acc_rows9
#print axioms termQX9_x
