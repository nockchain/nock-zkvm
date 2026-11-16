/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AComp.lean

Route (no per-gate bookkeeping beyond four hand cases):
  * `viaPerm permX9` of the twin row environment agrees with the J-8 row environment on every column
    `< 137` (`trace9_eq`), and the J-8 environment is `0` on every column `≥ 123` (`trace8_zero`);
  * every twin gate reads only columns `< 137`, so each twin gate at the twin row = the twin gate at
    the J-8 row (`eval_okC` / `eval_okM` at the gathered `𝕂` environment);
  * at the J-8 row (new columns `0`): base gates — kept J-8 gate, or a product with a factor that is a
    new column, or one of the four changed
    gates (reduce to their J-8 originals), or an accumulator gate (`termCoord_twin`); slot pairs —
    `extSlot` adds entries active only on new states (`slotGateQX_extSlot`); walk gates — the twin's
    walk sums over the three new states vanish (`ccLX9_eval`, `cmLX9_eval`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ChipHX9RAP
import Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTraceX
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLookups

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AComp

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.Framework.Reify
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.HonestTraceX (okC okM envAt eval_okC eval_okM okC_mapC okM_mapM
  eval_mapC_castX)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8 (computeChipVCLHX_sat_iff)

noncomputable section

/-! ## 1. The embedding -/

/-- **Twin RAP column order** (`ChipHX9RAP` header: RAP cols `0..68` = J-8 cols `0..68`, RAP `69..82` = the
new twin cols `123..136` (zero), RAP `83..136` = J-8 cols `69..122`). -/
def emb9 {F : Type} [Field F] (P : Fin 123 → F[X]) : Fin 137 → F[X] :=
  fun j => if h : (j : ℕ) < 69 then P ⟨j, by omega⟩ else if h2 : (j : ℕ) < 83 then 0
    else P ⟨(j : ℕ) - 14, by omega⟩

theorem permX9_lt137 (j : Fin 123) : permX9 j < 137 := by
  have := j.isLt; simp only [permX9]; split_ifs <;> omega

/-- `emb9` at a RAP column `c = permX9 j` reads the old J-8 column `j`. -/
theorem emb9_at {F : Type} [Field F] (P : Fin 123 → F[X]) (c : Fin 137) (j : Fin 123)
    (h : (c : ℕ) = permX9 j) : emb9 P c = P j := by
  have hj := j.isLt
  simp only [permX9] at h
  unfold emb9
  split_ifs with h1 h2
  · exact congrArg P (Fin.ext (by show (c : ℕ) = (j : ℕ); split_ifs at h <;> omega))
  · exfalso; split_ifs at h <;> omega
  · exact congrArg P (Fin.ext (by show (c : ℕ) - 14 = (j : ℕ); split_ifs at h <;> omega))

/-- The old J-8 column `j` sits at RAP column `permX9 j`, and `emb9` reads it back. -/
theorem emb9_oldCol {F : Type} [Field F] (P : Fin 123 → F[X]) (j : Fin 123) :
    emb9 P ⟨permX9 j, permX9_lt137 j⟩ = P j :=
  emb9_at P _ j rfl

/-- The read-back as a function: `emb9 P` at the old columns is `P`. -/
theorem emb9_toJ8 {F : Type} [Field F] (P : Fin 123 → F[X]) :
    (fun j : Fin 123 => emb9 P ⟨permX9 j, permX9_lt137 j⟩) = P :=
  funext (emb9_oldCol P)

/-- The fourteen new RAP columns `69..82` (twin columns `123..136`) are zero. -/
theorem emb9_new {F : Type} [Field F] (P : Fin 123 → F[X]) (j : Fin 137) (h1 : 69 ≤ (j : ℕ))
    (h2 : (j : ℕ) < 83) : emb9 P j = 0 := by
  simp only [emb9]; rw [dif_neg (by omega), dif_pos h2]

/-! ## 2. The two row environments -/

section Envs
variable {F : Type} [Field F]

/-- Twin row environment (read through the permutation) = J-8 row environment below `137`. -/
theorem trace9_eq (P : Fin 123 → F[X]) (ω x : F) (chalV pubVal : ℕ → F) (c : ℕ) (hc : c < 137) :
    (Env.viaPerm permX9 (envOfTrace (emb9 P) ω x chalV pubVal)).trace c =
        (envOfTrace P ω x chalV pubVal).trace c ∧
      (Env.viaPerm permX9 (envOfTrace (emb9 P) ω x chalV pubVal)).traceNext c =
        (envOfTrace P ω x chalV pubVal).traceNext c := by
  by_cases h2 : c < 123
  · have hl : permX9 c < 137 := permX9_lt137 ⟨c, h2⟩
    have he : emb9 P ⟨permX9 c, hl⟩ = P ⟨c, h2⟩ := emb9_at P _ _ rfl
    refine ⟨?_, ?_⟩ <;> simp only [Env.viaPerm, envOfTrace] <;> rw [dif_pos hl, dif_pos h2, he]
  · have hp : permX9 c = c - 54 := by simp only [permX9]; split_ifs <;> omega
    have hl : permX9 c < 137 := by omega
    have he : emb9 P ⟨permX9 c, hl⟩ = 0 :=
      emb9_new P _ (by show 69 ≤ permX9 c; omega) (by show permX9 c < 83; omega)
    refine ⟨?_, ?_⟩ <;> simp only [Env.viaPerm, envOfTrace] <;>
      rw [dif_pos hl, dif_neg h2, he, Polynomial.eval_zero]

/-- The J-8 row environment is zero on every column `≥ 123`. -/
theorem trace8_zero (P : Fin 123 → F[X]) (ω x : F) (chalV pubVal : ℕ → F) (c : ℕ) (hc : 123 ≤ c) :
    (envOfTrace P ω x chalV pubVal).trace c = 0 ∧ (envOfTrace P ω x chalV pubVal).traceNext c = 0 := by
  simp only [envOfTrace]
  rw [dif_neg (by omega), dif_neg (by omega)]
  exact ⟨rfl, rfl⟩

end Envs

/-! ## 3. Read sets: every twin gate reads columns `< 137` only -/

/-- Base reads: trace columns `< 137` (current and next); coins and publics. -/
def okF9 : VarKind → ℕ → Bool
  | .traceCur, i => decide (i < 137)
  | .traceNext, i => decide (i < 137)
  | _, _ => true

/-- `𝕂` reads: a `𝕂` column at `i` occupies `i, i+1, i+2`. -/
def okK9 : VarKind → ℕ → Bool
  | .traceCur, i => decide (i + 2 < 137)
  | .traceNext, i => decide (i + 2 < 137)
  | _, _ => true

theorem baseGatesHX9_ok137 : (baseGatesHX9.all (okC okF9)) = true := by decide +kernel

theorem walkGatesX9_ok137 : ((walkGatesX9 (F := ℚ)).all (okM okK9 okF9)) = true := by decide +kernel

theorem slotPairsX9_ok137 {F : Type} [Field F] (δ : F) :
    ((slotPairsX9 F δ).all fun q => okM okK9 okF9 q.1 && okM okK9 okF9 q.2) = true := by
  rfl

section Agree
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Two base environments agreeing below `137` (and on coins / publics) agree on every `okF9` read. -/
theorem agreeF {e1 e2 : Env F} (hag : ∀ c < 137, e1.trace c = e2.trace c ∧ e1.traceNext c = e2.traceNext c)
    (hch : e1.chal = e2.chal) (hpub : e1.pub = e2.pub) :
    ∀ k i, okF9 k i = true → envAt e1 k i = envAt e2 k i := by
  intro k i hk
  cases k <;> simp only [okF9, decide_eq_true_eq] at hk <;> simp only [envAt]
  · exact (hag i hk).1
  · exact (hag i hk).2
  · rw [hch]
  · rw [hpub]

/-- … and their gathered `𝕂` environments agree on every `okK9` read. -/
theorem agreeK (b : Basis (Fin 3) F K) {e1 e2 : Env F}
    (hag : ∀ c < 137, e1.trace c = e2.trace c ∧ e1.traceNext c = e2.traceNext c)
    (hch : e1.chal = e2.chal) (hpub : e1.pub = e2.pub) :
    ∀ k i, okK9 k i = true → envAt (Compute.TowerD.gatherEnv b e1) k i = envAt (Compute.TowerD.gatherEnv b e2) k i := by
  intro k i hk
  cases k <;> simp only [okK9, decide_eq_true_eq] at hk <;> simp only [envAt]
  · show Compute.LogUp.limbVal b e1.trace i = Compute.LogUp.limbVal b e2.trace i
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hag _ (by have := k.isLt; omega)).1]
  · show Compute.LogUp.limbVal b e1.traceNext i = Compute.LogUp.limbVal b e2.traceNext i
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hag _ (by have := k.isLt; omega)).2]
  · show Compute.LogUp.limbVal b e1.chal i = Compute.LogUp.limbVal b e2.chal i
    rw [hch]
  · show Compute.LogUp.limbVal b e1.pub i = Compute.LogUp.limbVal b e2.pub i
    rw [hpub]

end Agree

/-! ## 4. Base gates at a row whose new columns are zero -/

/-- A syntactic "this expression is `0` when every column `≥ 123` is `0`". -/
def zeroAt : CoeffExpr ℚ → Bool
  | .const c => decide (c = 0)
  | .var .traceCur i => decide (123 ≤ i)
  | .var .traceNext i => decide (123 ≤ i)
  | .var _ _ => false
  | .add a b => zeroAt a && zeroAt b
  | .sub a b => zeroAt a && zeroAt b
  | .mul a b => zeroAt a || zeroAt b
  | .neg a => zeroAt a
  | .pow a n => decide (0 < n) && zeroAt a

section Base
variable {F : Type} [Field F]

theorem evalQX_zeroAt {env : Env F} (hz : ∀ c, 123 ≤ c → env.trace c = 0 ∧ env.traceNext c = 0) :
    ∀ g : CoeffExpr ℚ, zeroAt g = true → evalQX g env = 0
  | .const c, h => by simp only [zeroAt, decide_eq_true_eq] at h; simp [evalQX, h]
  | .var .traceCur i, h => by simp only [zeroAt, decide_eq_true_eq] at h; exact (hz i h).1
  | .var .traceNext i, h => by simp only [zeroAt, decide_eq_true_eq] at h; exact (hz i h).2
  | .var .challenge _, h => by simp [zeroAt] at h
  | .var .publicVal _, h => by simp [zeroAt] at h
  | .add a b, h => by
      simp only [zeroAt, Bool.and_eq_true] at h
      simp only [evalQX, evalQX_zeroAt hz a h.1, evalQX_zeroAt hz b h.2, add_zero]
  | .sub a b, h => by
      simp only [zeroAt, Bool.and_eq_true] at h
      simp only [evalQX, evalQX_zeroAt hz a h.1, evalQX_zeroAt hz b h.2, sub_zero]
  | .mul a b, h => by
      simp only [zeroAt, Bool.or_eq_true] at h
      rcases h with h | h
      · simp only [evalQX, evalQX_zeroAt hz a h, zero_mul]
      · simp only [evalQX, evalQX_zeroAt hz b h, mul_zero]
  | .neg a, h => by
      simp only [zeroAt] at h
      simp only [evalQX, evalQX_zeroAt hz a h, neg_zero]
  | .pow a n, h => by
      simp only [zeroAt, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [evalQX, evalQX_zeroAt hz a h.2]
      exact zero_pow (by omega)


/-- Every twin arithmetic gate is a J-8 arithmetic gate, vanishes at columns `≥ 123`, or is one of `oneHotSumX9, kindRelaxX9, svXFX9, prGateX9`. -/
theorem arith9_class :
    (arithGatesX9.all fun g => decide (g ∈ (arithGatesX (F := ℚ))) || zeroAt g ||
      decide (g ∈ ([oneHotSumX9, kindRelaxX9, svXFX9, prGateX9] : List (CoeffExpr ℚ)))) = true := by
  decide +kernel


/-- Every twin equality gate is a J-8 equality gate or vanishes at columns `≥ 123`. -/
theorem eq9_class :
    ((eqGatesX9 (F := ℚ)).all fun g => decide (g ∈ (eqGatesX (F := ℚ))) || zeroAt g.gate) = true := by
  decide +kernel

/-- **The twin's base gates hold at a J-8 row whose columns `≥ 123` are zero.** -/
theorem base9_of_base8 {env : Env F} (hB : BaseHoldsX env)
    (hz : ∀ c, 123 ≤ c → env.trace c = 0 ∧ env.traceNext c = 0) : BaseHoldsX9 env := by
  have hN : NewOff env := ⟨(hz _ (by decide)).1, (hz _ (by decide)).1, (hz _ (by decide)).1⟩
  intro g hg
  simp only [baseGatesHX9, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · have hc := List.all_eq_true.mp arith9_class g hg
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with (hc | hc) | hc
    · exact arith_of_base hB hc
    · exact evalQX_zeroAt hz g hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · have h := arith_of_base hB (g := .sub (selS (List.range nStates)) (.const 1)) (by decide +kernel)
        simp only [oneHotSumX9, evalQX, evalQX_selS_zero newStates hN.zero, add_zero]
        simp only [evalQX] at h
        exact h
      · have h := arith_of_base hB (g := .mul (kcE xF) (kbE xF)) (by decide +kernel)
        simp only [kindRelaxX9, oneMinus, cc, evalQX, hN.2.2, Rat.cast_one, sub_zero, one_mul]
        simp only [evalQX] at h
        exact h
      · have h := arith_of_base hB (g := svXF8) (by decide +kernel)
        simp only [svXFX9, oneMinus, prodL, List.foldr, cc, evalQX, hN.2.2, Rat.cast_one, sub_zero,
          one_mul, zero_mul, add_zero]
        exact h
      · have h := arith_of_base hB (g := prGateX) (by decide +kernel)
        simp only [prGateX9, cc, evalQX, hN.2.2, zero_mul, sub_zero]
        exact h
  · have T := fun (b : Bal) (im : Bool) (k : ℕ) => (termCoord_twin (env := env) hN b im k).symm
    have mem : ∀ g' ∈ (accGatesHX : List (CoeffExpr ℚ)), evalQX g' env = 0 := fun g' h' =>
      hB g' (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h'))))
    simp only [accGatesHX9, List.mem_append] at hg
    rcases hg with ((((h | h) | h) | h) | h) | h
    · obtain ⟨g', h', e⟩ := accGatesX_twin (T .x false) h
      rw [← e]; exact mem g' (by simp only [accGatesHX, List.mem_append]; tauto)
    · obtain ⟨g', h', e⟩ := accGatesX_twin (T .x true) h
      rw [← e]; exact mem g' (by simp only [accGatesHX, List.mem_append]; tauto)
    · obtain ⟨g', h', e⟩ := accGatesX_twin (T .p false) h
      rw [← e]; exact mem g' (by simp only [accGatesHX, List.mem_append]; tauto)
    · obtain ⟨g', h', e⟩ := accGatesX_twin (T .p true) h
      rw [← e]; exact mem g' (by simp only [accGatesHX, List.mem_append]; tauto)
    · obtain ⟨g', h', e⟩ := accGatesX_twin (T .s false) h
      rw [← e]; exact mem g' (by simp only [accGatesHX, List.mem_append]; tauto)
    · obtain ⟨g', h', e⟩ := accGatesX_twin (T .s true) h
      rw [← e]; exact mem g' (by simp only [accGatesHX, List.mem_append]; tauto)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
    have hc := List.all_eq_true.mp eq9_class e he
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · exact eq_of_base hB hc
    · exact evalQX_zeroAt hz _ hc

end Base

/-! ## 5. Slot pairs: the extended slots evaluate as J-8's when the new entries are off -/

section Slot
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δ : F) (eK : Env K) (eF : Env F)

theorem sumQ_fst (l : List (Q F)) :
    (sumQ F l).1.eval eK eF = (l.map fun q => q.1.eval eK eF).sum := by
  induction l with
  | nil => simp [sumQ, qconst, MixedExpr.eval]
  | cons a l ih =>
      show (qadd F a (sumQ F l)).1.eval eK eF = _
      simp only [qadd, MixedExpr.eval, ih, List.map_cons, List.sum_cons]

theorem sumQ_snd (l : List (Q F)) :
    (sumQ F l).2.eval eK eF = (l.map fun q => q.2.eval eK eF).sum := by
  induction l with
  | nil => simp [sumQ, qconst, MixedExpr.eval]
  | cons a l ih =>
      show (qadd F a (sumQ F l)).2.eval eK eF = _
      simp only [qadd, MixedExpr.eval, ih, List.map_cons, List.sum_cons]

/-- The outer shape of a slot gate: `V·(s + PT) − (lift l + PT2)`. -/
theorem slot_congr (V s s' PT PT2 : Q F) (l l' : CoeffExpr F)
    (h1 : s.1.eval eK eF = s'.1.eval eK eF) (h2 : s.2.eval eK eF = s'.2.eval eK eF)
    (hl : l.eval eF = l'.eval eF) :
    (qsub F (qmul F δ V (qadd F s PT)) (qadd F (qlift F l) PT2)).1.eval eK eF =
        (qsub F (qmul F δ V (qadd F s' PT)) (qadd F (qlift F l') PT2)).1.eval eK eF ∧
      (qsub F (qmul F δ V (qadd F s PT)) (qadd F (qlift F l) PT2)).2.eval eK eF =
        (qsub F (qmul F δ V (qadd F s' PT)) (qadd F (qlift F l') PT2)).2.eval eK eF := by
  constructor <;> simp only [qsub, qmul, qadd, qlift, MixedExpr.eval, h1, h2, hl]

/-- **An extended slot's gate pair evaluates as the J-8 slot's** when the appended entries are off. -/
theorem slotGateQX_extSlot (S : SlotX F) (es : List (EntX F)) (ps : List ℕ)
    (hes : ∀ x ∈ es, x.act.eval eF = 0) :
    (slotGateQX F δ (extSlot S es ps)).1.eval eK eF = (slotGateQX F δ S).1.eval eK eF ∧
      (slotGateQX F δ (extSlot S es ps)).2.eval eK eF = (slotGateQX F δ S).2.eval eK eF := by
  have z1 : ((es.map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd)).map
      fun q => q.1.eval eK eF).sum = 0 :=
    List.sum_eq_zero fun y hy => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
      simp [qmul, qlift, MixedExpr.eval, hes x hx]
  have z2 : ((es.map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd)).map
      fun q => q.2.eval eK eF).sum = 0 :=
    List.sum_eq_zero fun y hy => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
      simp [qmul, qlift, MixedExpr.eval, hes x hx]
  have A1 : (sumQ F ((S.ents ++ es).map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd))).1.eval eK eF =
      (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd))).1.eval eK eF := by
    rw [sumQ_fst, sumQ_fst, List.map_append, List.map_append, List.sum_append, z1, add_zero]
  have A2 : (sumQ F ((S.ents ++ es).map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd))).2.eval eK eF =
      (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQX F δ x.rcd))).2.eval eK eF := by
    rw [sumQ_snd, sumQ_snd, List.map_append, List.map_append, List.sum_append, z2, add_zero]
  have B : (CoeffExpr.sumList (S.ents ++ es) EntX.act).eval eF = (CoeffExpr.sumList S.ents EntX.act).eval eF := by
    rw [CoeffExpr.eval_sumList, CoeffExpr.eval_sumList, List.map_append, List.sum_append,
      List.sum_eq_zero (l := es.map _) (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact hes x hx), add_zero]
  exact slot_congr δ eK eF _ _ _ _ _ _ _ A1 A2 B

/-- An entry whose states are all `≥ 123` is off at a row whose columns `≥ 123` are zero. -/
theorem act_off (hz : ∀ c, 123 ≤ c → eF.trace c = 0 ∧ eF.traceNext c = 0) (x : EntX F)
    (hx : (x.states.all fun s => decide (123 ≤ s)) = true) : x.act.eval eF = 0 := by
  simp only [EntX.act, CoeffExpr.eval, selS, CoeffExpr.eval_sumList]
  rw [List.sum_eq_zero, zero_mul]
  intro y hy
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
  have := List.all_eq_true.mp hx s hs
  simp only [decide_eq_true_eq] at this
  exact (hz s this).1

theorem ents_new_ok :
    ((ents0New (F := F) ++ ents1New ++ ents2New ++ ents3New).all fun x =>
      x.states.all fun s => decide (123 ≤ s)) = true := by
  rfl

/-- **Every twin slot pair equals its J-8 slot pair** at a row whose columns `≥ 123` are zero. -/
theorem slotPairs9_eval (hz : ∀ c, 123 ≤ c → eF.trace c = 0 ∧ eF.traceNext c = 0) :
    ∀ q ∈ slotPairsX9 F δ, ∃ q8 ∈ slotPairsX F δ,
      q.1.eval eK eF = q8.1.eval eK eF ∧ q.2.eval eK eF = q8.2.eval eK eF := by
  have hok := ents_new_ok (F := F)
  have hoff : ∀ es : List (EntX F), (∀ x ∈ es, x ∈ ents0New (F := F) ++ ents1New ++ ents2New ++ ents3New) →
      ∀ x ∈ es, x.act.eval eF = 0 := fun es hsub x hx =>
    act_off eF hz x (List.all_eq_true.mp hok x (hsub x hx))
  intro q hq
  simp only [slotPairsX9, slotsX9, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_map_of_mem (by simp [ChipHX.slotsX] : slot0X ∈ (ChipHX.slotsX : List (SlotX F))),
      slotGateQX_extSlot δ eK eF slot0X ents0New []
      (hoff _ (fun x hx => by simp [hx]))⟩
  · exact ⟨_, List.mem_map_of_mem (by simp [ChipHX.slotsX] : slot1X ∈ (ChipHX.slotsX : List (SlotX F))),
      slotGateQX_extSlot δ eK eF slot1X ents1New []
      (hoff _ (fun x hx => by simp [hx]))⟩
  · exact ⟨_, List.mem_map_of_mem (by simp [ChipHX.slotsX] : slot2X ∈ (ChipHX.slotsX : List (SlotX F))),
      slotGateQX_extSlot δ eK eF slot2X ents2New [sS10S]
      (hoff _ (fun x hx => by simp [hx]))⟩
  · exact ⟨_, List.mem_map_of_mem (by simp [ChipHX.slotsX] : slot3X ∈ (ChipHX.slotsX : List (SlotX F))),
      slotGateQX_extSlot δ eK eF slot3X ents3New []
      (hoff _ (fun x hx => by simp [hx]))⟩

end Slot

/-! ## 6. Walk gates: the sums over the three new states vanish -/

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] (eK : Env K) (eF : Env F)

theorem childSumX9_old (kind : VarKind) (st : ℕ) (hst : st ∈ List.range nStates) :
    (childSumX9 kind st : MixedExpr ℚ) = childSumX kind st := by
  simp only [childSumX9, childSumX, fanoutX9_new.2 st hst]

theorem ccLX9_eval (kind : VarKind) (hz : ∀ st ∈ newStates, evalQ (kv kind st : CoeffExpr ℚ) eF = 0) :
    evalMQ (ccLX9 kind : MixedExpr ℚ) eK eF = evalMQ (ccLX kind : MixedExpr ℚ) eK eF := by
  simp only [ccLX9, ccLX, statesX9, allStatesX]
  rw [evalMQ_sumM, evalMQ_sumM, List.map_append, List.map_append, List.sum_append]
  have h0 : ((newStates.map fun st => (MixedExpr.Scale (kv kind st) (childSumX9 kind st) : MixedExpr ℚ)).map
      fun g => evalMQ g eK eF).sum = 0 :=
    List.sum_eq_zero fun y hy => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
      obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hg
      simp only [evalMQ, hz st hst, map_zero, zero_mul]
  rw [h0, add_zero]
  congr 1

theorem cmLX9_eval (kind : VarKind) (hz : ∀ st ∈ newStates, evalQ (kv kind st : CoeffExpr ℚ) eF = 0) :
    evalMQ (cmLX9 kind : MixedExpr ℚ) eK eF = evalMQ (cmLX kind : MixedExpr ℚ) eK eF := by
  simp only [cmLX9, cmLX, statesX9, allStatesX]
  rw [evalMQ_sumM, evalMQ_sumM, List.map_append, List.map_append, List.sum_append]
  have h0 : ((newStates.map fun st => (MixedExpr.Scale (kv kind st)
      (.Pow (.Var .challenge chalAlphaW) (childrenX9 st).length) : MixedExpr ℚ)).map
      fun g => evalMQ g eK eF).sum = 0 :=
    List.sum_eq_zero fun y hy => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
      obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hg
      simp only [evalMQ, hz st hst, map_zero, zero_mul]
  rw [h0, add_zero]
  congr 1

/-- **The twin walk gates evaluate as J-8's** at a row whose columns `≥ 123` are zero. -/
theorem walkGates9_eval (hz : ∀ c, 123 ≤ c → eF.trace c = 0 ∧ eF.traceNext c = 0) :
    ((walkGatesX9 (F := ℚ)).map fun t => evalMQ t eK eF) =
      (walkGatesX (F := ℚ)).map fun t => evalMQ t eK eF := by
  have hnew : ∀ st ∈ newStates, 123 ≤ st := by decide
  have hc : ∀ st ∈ newStates, evalQ (kv .traceCur st : CoeffExpr ℚ) eF = 0 := fun st hst =>
    (hz st (hnew st hst)).1
  have hn : ∀ st ∈ newStates, evalQ (kv .traceNext st : CoeffExpr ℚ) eF = 0 := fun st hst =>
    (hz st (hnew st hst)).2
  simp only [walkGatesX9, walkGatesX, List.map_cons, List.map_nil, evalMQ,
    ccLX9_eval eK eF .traceCur hc, ccLX9_eval eK eF .traceNext hn,
    cmLX9_eval eK eF .traceCur hc, cmLX9_eval eK eF .traceNext hn]

end Walk

/-! ## 7. The transport at one row -/

section Row
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **Row transport.**  If the J-8 gates vanish at `E8`, `E8` is zero on columns `≥ 123`, and `E9` agrees with
`E8` below `137` (and on coins / publics), then every twin gate vanishes at `E9`. -/
theorem twin_gates_of_J8 (b : Basis (Fin 3) F K) (δ : F) {E8 E9 : Env F}
    (hJ : ∀ g ∈ gatesHX b δ, g.eval E8 = 0)
    (hz : ∀ c, 123 ≤ c → E8.trace c = 0 ∧ E8.traceNext c = 0)
    (hag : ∀ c < 137, E9.trace c = E8.trace c ∧ E9.traceNext c = E8.traceNext c)
    (hch : E9.chal = E8.chal) (hpub : E9.pub = E8.pub) :
    ∀ g ∈ gatesHX9 b δ, g.eval E9 = 0 := by
  have aF := agreeF hag hch hpub
  have aK := agreeK b hag hch hpub
  have hB : BaseHoldsX E8 := fun t ht => by
    have h0 := hJ (mapC (fun q : ℚ => (q : F)) t)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ht)))
    rwa [eval_mapC_castX] at h0
  have hB9 := base9_of_base8 hB hz
  have cE8 := isCoordEnv_gather b E8
  have cE9 := isCoordEnv_gather b E9
  intro g hg
  simp only [gatesHX9, List.mem_append, List.mem_flatMap, List.mem_ofFn] at hg
  rcases hg with (hg | ⟨q, hq, hg⟩) | ⟨m, hm, k, rfl⟩
  · -- base
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    have hok : okC okF9 t = true := List.all_eq_true.mp baseGatesHX9_ok137 t ht
    rw [eval_okC okF9 _ (by rw [okC_mapC]; exact hok) E9 E8 aF, eval_mapC_castX]
    exact hB9 t ht
  · -- slot pairs
    have hok := List.all_eq_true.mp (slotPairsX9_ok137 δ) q hq
    simp only [Bool.and_eq_true] at hok
    obtain ⟨q8, hq8, e1, e2⟩ := slotPairs9_eval δ (Compute.TowerD.gatherEnv b E8) E8 hz q hq
    have hJ8 : ∀ g ∈ qGates b q8, g.eval E8 = 0 := fun g hg =>
      hJ g (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q8, hq8, hg⟩)))
    simp only [qGates, List.mem_append, List.mem_ofFn] at hg hJ8
    rcases hg with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [← mixedCompile_eval b col0Id cE9,
        eval_okM okK9 okF9 _ hok.1 (Compute.TowerD.gatherEnv b E9) (Compute.TowerD.gatherEnv b E8) E9 E8 aK aF, e1,
        mixedCompile_eval b col0Id cE8]
      exact hJ8 _ (Or.inl ⟨k, rfl⟩)
    · rw [← mixedCompile_eval b col0Id cE9,
        eval_okM okK9 okF9 _ hok.2 (Compute.TowerD.gatherEnv b E9) (Compute.TowerD.gatherEnv b E8) E9 E8 aK aF, e2,
        mixedCompile_eval b col0Id cE8]
      exact hJ8 _ (Or.inr ⟨k, rfl⟩)
  · -- walk
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    have hok : okM okK9 okF9 t = true := List.all_eq_true.mp walkGatesX9_ok137 t ht
    have hmem : evalMQ t (Compute.TowerD.gatherEnv b E8) E8 ∈ (walkGatesX (F := ℚ)).map
        fun t => evalMQ t (Compute.TowerD.gatherEnv b E8) E8 := by
      rw [← walkGates9_eval (Compute.TowerD.gatherEnv b E8) E8 hz]
      exact List.mem_map_of_mem ht
    obtain ⟨t8, ht8, e8⟩ := List.mem_map.mp hmem
    have hJ8 : ∀ k, (mixedCompile b col0Id (mapM (fun q : ℚ => (q : F)) t8) k).eval E8 = 0 := fun k =>
      hJ _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨_, List.mem_map_of_mem ht8, List.mem_ofFn.mpr ⟨k, rfl⟩⟩))
    rw [← mixedCompile_eval b col0Id cE9,
      eval_okM okK9 okF9 _ (by rw [okM_mapM]; exact hok) (Compute.TowerD.gatherEnv b E9) (Compute.TowerD.gatherEnv b E8) E9 E8 aK aF,
      eval_mapM_cast, ← e8, ← eval_mapM_cast, mixedCompile_eval b col0Id cE8]
    exact hJ8 k

end Row

/-! ## 8. The chip transport -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The honest compute fill of the J-9 A twin**: a J-8 compute trace satisfying `computeChipVCLHX`, extended
by zeros on the fourteen new columns (and laid out in the twin's RAP column order), satisfies
`computeChipVCLHX9`. -/
theorem sat9_of_sat8 [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ChipHX.computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (ChipHX.computeChipVCLHX hn nodes b δ chalV pubVal orbit) P) :
    RAP.SatisfiesWithPreprocessing (ChipHX9.computeChipVCLHX9 hn nodes b δ chalV pubVal orbit)
      (emb9 P) := by
  have hsat := (computeChipVCLHX_sat_iff hn nodes b δ chalV pubVal orbit P).mp hP
  refine ⟨?_, ?_⟩
  · intro i x hx
    have hall : ∀ g ∈ gatesHX9 b δ,
        g.eval (Env.viaPerm permX9 (envOfTrace (emb9 P) orbit.ω x chalV pubVal)) = 0 :=
      twin_gates_of_J8 b δ (hsat.2 x hx) (trace8_zero P orbit.ω x chalV pubVal)
        (trace9_eq P orbit.ω x chalV pubVal) rfl rfl
    have h1 := Nock.Framework.Reify.compose_eval
      (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap (emb9 P) i x
    have h2 : (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.C i =
        coeffToMv chalV pubVal ((gatesHX9P b δ).get i) := rfl
    rw [h1, h2]
    exact (eval_coeffToMv (w := 137) (emb9 P) orbit.ω x chalV pubVal ((gatesHX9P b δ).get i)).trans
      ((gatesHX9P_eval b δ _).mpr hall _ (List.get_mem _ _))
  · have h0 : P ⟨17, by show 17 < 123; omega⟩ = firstRowMask nodes := hsat.1 ⟨0, by show 0 < 2; omega⟩
    have h1 : P ⟨18, by show 18 < 123; omega⟩ = lastRowMask hn nodes := hsat.1 ⟨1, by show 1 < 2; omega⟩
    intro j
    rcases j with ⟨j, hj⟩
    have hj2 : j < 2 := hj
    interval_cases j
    · show emb9 P ⟨17, by decide⟩ = firstRowMask nodes
      simp only [emb9, dif_pos (show (17 : ℕ) < 69 by decide)]
      exact h0
    · show emb9 P ⟨18, by decide⟩ = lastRowMask hn nodes
      simp only [emb9, dif_pos (show (18 : ℕ) < 69 by decide)]
      exact h1

end Chip

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AComp

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AComp
#print axioms emb9_oldCol
#print axioms emb9_toJ8
#print axioms emb9_new
#print axioms trace9_eq
#print axioms baseGatesHX9_ok137
#print axioms walkGatesX9_ok137
#print axioms slotPairsX9_ok137
#print axioms arith9_class
#print axioms eq9_class
#print axioms base9_of_base8
#print axioms slotGateQX_extSlot
#print axioms slotPairs9_eval
#print axioms walkGates9_eval
#print axioms twin_gates_of_J8
#print axioms sat9_of_sat8
end Axioms
