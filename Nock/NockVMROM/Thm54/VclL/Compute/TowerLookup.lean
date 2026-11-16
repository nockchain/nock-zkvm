import Nock.NockVMROM.Thm54.VclL.Compute.TowerKept
import Nock.NockVMROM.Thm54.VclL.Compute.ChipQ7S

/-!
# Route (d), phase 2 : the lookups, accumulators and ax gate at `𝕂′`, the tower gate list

TARGET layout throughout (these gates are added after the reindex).  Appended columns, past the
Im block `232.. 393`: lookup-inverse Im triples `394 / 397 / 400`, accumulator Im triples `403`
(export) / `406` (path); the `ρ′` Im publics `51..53` (export) / `54..56` (path) (CORRECTED by TWD-4: `49..54` collided with the walk-seed Im public triple `48..50` of `fullImMap.extPub 1`).  Width `409`.

* `slot0Q / slot1Q / slot2Q`: `inv′ · den′ − act` as `(Re, Im)` pairs over `𝕂′` (`qmul`), the
  records entered through `entryQ` (a `𝕂`-role limb with the Im role from `fullImMap`, an `𝔽`
  column lifted), the coins `γ′ = (limbs 21, 42)`, `ρ′ = (24, 45)`;
* `accGatesT`: the accumulator gate is `𝔽`-linear in the inverse (`act ∈ 𝔽`), so the `𝕂′` gate is the
  EXISTING `accGates 3` on the Re limbs plus the same gate on the Im limbs;
* `axImGates`: `leaf.Im = 0` on the atom-test rows (the `𝔽`-valued axis);
* `vclGatesQ7T`: the tower gate list.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The appended columns -/

def invImBase (j : Fin 3) : ℕ := 394 + 3 * (j : ℕ)
def accImExport : ℕ := 403
def accImPath : ℕ := 406
def rhoExportImPub : ℕ := 51
def rhoPathImPub : ℕ := 54
def z1Col : ℕ := 409

/-- The tower chip's width: `232 + 162 (fullImMap) + 9 (inverse Im) + 6 (accumulator Im) + 1 (z1)`. -/
def vclWidthT : ℕ := 410

theorem vclWidthT_eq : vclWidthT = 232 + 162 + 9 + 6 + 1 := rfl

/-- The appended lookup / accumulator Im blocks are disjoint, past the Im block, and the `ρ′` Im
publics avoid the existing publics `42..47` and the walk-seed Im triple `48..50`. -/
theorem appended_disjoint :
    394 ≤ invImBase 0 ∧ invImBase 0 + 3 = invImBase 1 ∧ invImBase 1 + 3 = invImBase 2 ∧
      invImBase 2 + 3 = accImExport ∧ accImExport + 3 = accImPath ∧ accImPath + 3 = z1Col ∧
      z1Col + 1 = vclWidthT ∧
      50 < rhoExportImPub ∧ rhoExportImPub + 3 = rhoPathImPub := by
  decide

/-! ## 2. Records and denominators over `𝕂′` -/

section Lookup
variable (F : Type) [Field F]

/-- The Im role column of a record limb (`13 + 3·role`), from the route (d) map. -/
def imColOfLimb (l : ℕ) : Option ℕ :=
  if h : 13 ≤ l ∧ (l - 13) / 3 < 63 then fullImMap.ext ⟨(l - 13) / 3, h.2⟩ else none

/-- A record entry as a `𝕂′` pair. -/
def entryQ : Entry → Q F
  | .k l => qvar F .traceCur l (imColOfLimb l)
  | .f c => qlift F (.var .traceCur c)

def recQ {m : ℕ} (r : Fin m → Entry) : Fin m → Q F := fun c => entryQ F (r c)

/-- The `𝕂′` IO coins: `γ′ = (limbs 21, 42)`, `ρ′ = (limbs 24, 45)`. -/
def qγ : Q F := qvar F .challenge 21 (some 42)
def qρ : Q F := qvar F .challenge 24 (some 45)

/-- `ρ′ + Σ_{c<m} γ′^c · rec_c` over `𝕂′`. -/
def denQ (δ : F) : (m : ℕ) → (Fin m → Q F) → Q F
  | 0, _ => qρ F
  | m + 1, rr =>
      qadd F (denQ δ m fun c => rr c.castSucc) (qmul F δ (qpow F δ (qγ F) m) (rr (Fin.last m)))

/-- Slot `0`'s record with the side `1`: the formula cell, `11` entries. -/
def recQ0 : Fin 11 → Q F := fun c =>
  if h : (c : ℕ) < 10 then entryQ F (formulaRec ⟨c, h⟩) else qconst F 1

/-- A `𝕂′` inverse pair at Re limbs `re` and Im limbs `im`. -/
def invQ (re im : ℕ) : Q F := qcol F re im

/-- Slot `0`: `inv₀′ · den₀′ − 1`. -/
def slot0Q (δ : F) : Q F :=
  qsub F (qmul F δ (invQ F inv0Base (invImBase 0)) (denQ F δ 11 (recQ0 F))) (qconst F 1)

/-- `1 − z1` (base field). -/
def notZ1 : CoeffExpr F := .sub (.const 1) (.var .traceCur z1Col)

/-- The path activities : `s0·(1 − z1)` / `s9·(1 − z1)`. -/
def actP0 : CoeffExpr F := .mul (selVar 0) (notZ1 F)
def actP9 : CoeffExpr F := .mul (selVar 9) (notZ1 F)

/-- Slot `1`: `inv₁′ · (s0·(1−z1) · den_path + Σ s_x · den_export) − (s0·(1−z1) + Σ s_x)`. -/
def slot1Q (δ : F) : Q F :=
  qsub F (qmul F δ (invQ F (lookupInvBase 0) (invImBase 1))
    (qadd F (qmul F δ (qlift F (actP0 F)) (denQ F δ 8 (recQ F op0PathRec)))
      (qmul F δ (qlift F (selSum slot1ExportSels)) (denQ F δ 10 (recQ F tailRec)))))
    (qadd F (qlift F (actP0 F)) (qlift F (selSum slot1ExportSels)))

/-- Slot `2`: `s6` export / `s9·(1−z1)` core path. -/
def slot2Q (δ : F) : Q F :=
  qsub F (qmul F δ (invQ F (lookupInvBase 1) (invImBase 2))
    (qadd F (qmul F δ (qlift F (selVar 6)) (denQ F δ 10 (recQ F ttRec)))
      (qmul F δ (qlift F (actP9 F)) (denQ F δ 8 (recQ F op9PathRec)))))
    (qadd F (qlift F (selVar 6)) (qlift F (actP9 F)))

/-- **The `z1` gate on a fingerprint entry pair** (`𝕂′`): `z1 · sel · (child_c − root_c)`. -/
def z1EqQ (δ : F) (sel : ℕ) (r : Fin 8 → Entry) (c : Fin 3) : Q F :=
  qmul F δ (qlift F (.mul (.var .traceCur z1Col) (selVar sel)))
    (qsub F (entryQ F (r ⟨3 + (c : ℕ), by omega⟩)) (entryQ F (r ⟨(c : ℕ), by omega⟩)))

end Lookup

section Compiled
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The compiled pair: Re coordinates then Im coordinates. -/
def qGates (b : Basis (Fin 3) F K) (q : Q F) : List (CoeffExpr F) :=
  List.ofFn (mixedCompile b col0Id q.1) ++ List.ofFn (mixedCompile b col0Id q.2)

theorem qGates_length (b : Basis (Fin 3) F K) (q : Q F) : (qGates b q).length = 6 := by
  simp [qGates]

/-- **The lookup gates at `𝕂′`**: `6` per slot (was `3`). -/
def lookupGatesT (b : Basis (Fin 3) F K) (δ : F) : List (CoeffExpr F) :=
  qGates b (slot0Q F δ) ++ qGates b (slot1Q F δ) ++ qGates b (slot2Q F δ)

theorem lookupGatesT_length (b : Basis (Fin 3) F K) (δ : F) : (lookupGatesT b δ).length = 18 := by
  simp [lookupGatesT, qGates_length]

/-- **Gate transport**: the compiled pair vanishes iff the `𝕂′` pair equation holds. -/
theorem qGates_iff [FiniteDimensional F K] (b : Basis (Fin 3) F K) {eK : Env K} {eF : Env F}
    (h : IsCoordEnv b col0Id eK eF) (q : Q F) :
    (∀ g ∈ qGates b q, g.eval eF = 0) ↔ Q.IsZero q eK eF := by
  rw [gate_zero_iff_compiled b col0Id h q]
  simp only [qGates, List.mem_append, List.mem_ofFn]
  constructor
  · intro hg
    exact ⟨fun k => hg _ (Or.inl ⟨k, rfl⟩), fun k => hg _ (Or.inr ⟨k, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ g (⟨k, rfl⟩ | ⟨k, rfl⟩)
    exacts [h1 k, h2 k]

variable (δ : F)

theorem qpow_val' {K : Type} [Field K] [Algebra F K] (eK : Env K) (eF : Env F) (a : Q F) (n : ℕ) :
    Q.val δ (qpow F δ a n) eK eF = Q.val δ a eK eF ^ n := by
  induction n with
  | zero => simp [qpow, Q.val, MixedExpr.eval, Quad.mk]
  | succ n ih => rw [qpow, qmul_val, ih]; exact (pow_succ' _ _).symm

theorem denQ_val {K : Type} [Field K] [Algebra F K] (eK : Env K) (eF : Env F) :
    ∀ (m : ℕ) (rr : Fin m → Q F), Q.val δ (denQ F δ m rr) eK eF =
      Q.val δ (qρ F) eK eF + ∑ c : Fin m, Q.val δ (qγ F) eK eF ^ (c : ℕ) * Q.val δ (rr c) eK eF
  | 0, _ => by simp [denQ]
  | m + 1, rr => by
      rw [denQ, qadd_val, denQ_val eK eF m, qmul_val, qpow_val', Fin.sum_univ_castSucc]
      simp [add_assoc]

end Compiled

/-! ## 3. The accumulators and the ax gate -/

section Acc
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The accumulator slots read at the Im inverse limbs. -/
def accSlotsXIm : List (Slot F) :=
  [⟨.const 1, invImBase 0⟩, ⟨selSum slot1ExportSels, invImBase 1⟩, ⟨selVar 6, invImBase 2⟩]

def accSlotsPIm : List (Slot F) := [⟨selVar 0, invImBase 1⟩, ⟨selVar 9, invImBase 2⟩]

/-- **The tower-local path slots** : the activities `s0·(1−z1)` / `s9·(1−z1)` (the shared
`accSlotsP` of `AccVCL` is untouched; `ChipQ7` still reads it). -/
def accSlotsPT : List (Slot F) := [⟨actP0 F, lookupInvBase 0⟩, ⟨actP9 F, lookupInvBase 1⟩]
def accSlotsPImT : List (Slot F) := [⟨actP0 F, invImBase 1⟩, ⟨actP9 F, invImBase 2⟩]

/-- **The accumulators at `𝕂′`**: `act ∈ 𝔽` scales the inverse, so the `𝕂′` accumulator gate is the
existing `accGates 3` on the Re limbs and the same gate on the Im limbs. -/
def accGatesT : List (CoeffExpr F) :=
  accGates 3 accSlotsX accExportBase rhoExportPub ++ accGates 3 accSlotsXIm accImExport rhoExportImPub ++
    accGates 3 accSlotsPT accPathBase rhoPathPub ++ accGates 3 accSlotsPImT accImPath rhoPathImPub

theorem accGatesT_length : (accGatesT (F := F)).length = 36 := by
  simp [accGatesT, accGates_length]

/-- Accumulator gates with activity degree `≤ 2` have degree `≤ 4` (`accGates_degree` assumes `≤ 1`). -/
theorem accGates_degree2 (slots : List (Slot F)) (hs : ∀ s ∈ slots, s.act.degree ≤ 2) (a p : ℕ) :
    ∀ g ∈ accGates 3 slots a p, g.degree ≤ 4 := by
  intro g hg
  simp only [accGates, List.mem_append, List.mem_map, List.mem_range] at hg
  have ht : ∀ k, (termCoord slots k).degree ≤ 3 := fun k =>
    CoeffExpr.degree_sumList_le _ _ _ fun s hm => by
      simp only [CoeffExpr.degree]; have := hs s hm; omega
  rcases hg with (⟨k, -, rfl⟩ | ⟨k, -, rfl⟩) | ⟨k, -, rfl⟩
  · simp [accInitGate, CoeffExpr.degree]
  · simp only [accStepGate, CoeffExpr.degree]; have := ht k; omega
  · simp only [accTermGate, CoeffExpr.degree]; have := ht k; omega

theorem actP_degree : (actP0 F).degree ≤ 2 ∧ (actP9 F).degree ≤ 2 := by
  constructor <;> simp [actP0, actP9, notZ1, selVar, CoeffExpr.degree]

/-- **`accGatesT_degree`, restated **: path activity degree `≤ 2` ⇒ gate degree `≤ 4`. -/
theorem accGatesT_degree : ∀ g ∈ accGatesT (F := F), g.degree ≤ 4 := by
  intro g hg
  have hX : ∀ s ∈ accSlotsXIm (F := F), s.act.degree ≤ 1 := by
    intro s hs
    simp only [accSlotsXIm, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · simp [CoeffExpr.degree]
    · exact selSum_degree _
    · simp [selVar, CoeffExpr.degree]
  have hP : ∀ s ∈ accSlotsPT (F := F), s.act.degree ≤ 2 := by
    intro s hs
    simp only [accSlotsPT, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    exacts [(actP_degree (F := F)).1, (actP_degree (F := F)).2]
  have hPI : ∀ s ∈ accSlotsPImT (F := F), s.act.degree ≤ 2 := by
    intro s hs
    simp only [accSlotsPImT, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    exacts [(actP_degree (F := F)).1, (actP_degree (F := F)).2]
  simp only [accGatesT, List.mem_append] at hg
  rcases hg with ((h | h) | h) | h
  · exact (accGates_degree 3 _ exportSlots_act_degree _ _ g h).trans (by omega)
  · exact (accGates_degree 3 _ hX _ _ g h).trans (by omega)
  · exact accGates_degree2 _ hP _ _ g h
  · exact accGates_degree2 _ hPI _ _ g h

/-- `leaf.Im = 0` on the atom-test rows: `s0 · Im(f_t.leaf) + s9 · Im(f_th.leaf)`. -/
def axImGateCoord (k : Fin 3) : CoeffExpr F :=
  .add (.mul (.var .traceCur 0) (.var .traceCur ((fullImMap.ext 41).getD 0 + (k : ℕ))))
    (.mul (.var .traceCur 9) (.var .traceCur ((fullImMap.ext 44).getD 0 + (k : ℕ))))

def axImGates : List (CoeffExpr F) := List.ofFn axImGateCoord

theorem axImGates_length : (axImGates (F := F)).length = 3 := by simp [axImGates]

theorem axImGates_degree : ∀ g ∈ axImGates (F := F), g.degree ≤ 2 := by
  intro g hg
  simp only [axImGates, List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  simp [axImGateCoord, CoeffExpr.degree]

/-- Receipt: the leaf roles `41` / `44` carry Im columns and their limb windows are `ft/fth` leaves. -/
theorem axIm_cols : (fullImMap.ext 41).isSome = true ∧ (fullImMap.ext 44).isSome = true ∧
    13 + 3 * 41 = 136 ∧ 13 + 3 * 44 = 145 := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;> decide +kernel

end Acc

/-! ## 3b. The `z1` gates -/

section Z1
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `z1 · (z1 − 1)`. -/
def z1BoolGate : CoeffExpr F := .mul (.var .traceCur z1Col) (.sub (.var .traceCur z1Col) (.const 1))
/-- `z1 · (ax − 1)`. -/
def z1AxGate : CoeffExpr F := .mul (.var .traceCur z1Col) (.sub (.var .traceCur axCol) (.const 1))

/-- **The `z1` gates**: `bool z1`, `z1·(ax − 1)`, and over `𝕂′` the OP0 identity `z1·s0·(e − s)` and
the OP9 axis-1 identity `z1·s9·(sf2_f − sf1_e)` (`op9PathRec`'s child / root, `V_comp`'s OP9 clause
`mem_root_3 = sf1_e`, `mem_child_3 = sf2_f`), `6` coordinates per fingerprint entry. -/
def z1Gates (b : Basis (Fin 3) F K) (δ : F) : List (CoeffExpr F) :=
  [z1BoolGate, z1AxGate] ++
    (List.finRange 3).flatMap (fun c => qGates b (z1EqQ F δ 0 op0PathRec c)) ++
    (List.finRange 3).flatMap (fun c => qGates b (z1EqQ F δ 9 op9PathRec c))

theorem z1Gates_length (b : Basis (Fin 3) F K) (δ : F) : (z1Gates b δ).length = 38 := by
  simp [z1Gates, qGates_length, List.length_flatMap]

end Z1

/-! ## 4. The tower gate list -/

section Gates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The gates of the tower compute chip** (`vclGatesQ7S` with the tower kept groups, the 𝕂′ lookup
gates, the accumulator Im halves and the ax Im gate). -/
def vclGatesQ7T (n e : ℕ) (b : Basis (Fin 3) F K) (δ : F) : List (CoeffExpr F) :=
  ((towerKeptGates n e b δ).map reindexE ++ serialGates) ++ (axGates b ++ axImGates) ++
    lookupGatesT b δ ++ accGatesT ++ z1Gates b δ

end Gates

/-! ## 5. Lengths and degree -/

section LookupDeg
variable (F : Type) [Field F]

theorem qdeg_entryQ (e : Entry) : qdeg F (entryQ F e) ≤ 1 := by
  cases e with
  | k l => rw [entryQ, qdeg_qvar]; simp [MixedExpr.degree]
  | f c => simp [entryQ, qlift, qdeg, MixedExpr.degree, CoeffExpr.degree]

theorem qdeg_qγ : qdeg F (qγ F) = 0 := by rw [qγ, qdeg_qvar]; simp [MixedExpr.degree]
theorem qdeg_qρ : qdeg F (qρ F) = 0 := by rw [qρ, qdeg_qvar]; simp [MixedExpr.degree]

theorem qdeg_denQ (δ : F) : ∀ (m : ℕ) (rr : Fin m → Q F), (∀ c, qdeg F (rr c) ≤ 1) →
    qdeg F (denQ F δ m rr) ≤ 1
  | 0, _, _ => by simp [denQ, qdeg_qρ]
  | m + 1, rr, h => by
      refine (qdeg_qadd F _ _).trans (max_le (qdeg_denQ δ m _ fun c => h _) ?_)
      refine (qdeg_qmul F δ _ _).trans ?_
      have := (qdeg_qpow F δ (qγ F) m)
      rw [qdeg_qγ] at this
      have h2 := h (Fin.last m)
      simp at this
      omega

theorem qdeg_qlift_sel (l : List ℕ) : qdeg F (qlift F (selSum l)) ≤ 1 := by
  have := selSum_degree (F := F) l
  simp only [qlift, qdeg, MixedExpr.degree]; omega

theorem qdeg_qlift_le (c : CoeffExpr F) : qdeg F (qlift F c) ≤ c.degree := by
  simp only [qlift, qdeg, MixedExpr.degree]; omega

theorem qdeg_actP : qdeg F (qlift F (actP0 F)) ≤ 2 ∧ qdeg F (qlift F (actP9 F)) ≤ 2 :=
  ⟨(qdeg_qlift_le F _).trans (actP_degree (F := F)).1, (qdeg_qlift_le F _).trans (actP_degree (F := F)).2⟩

/-- **`qdeg_slots`, restated **: the slot activities `s0·(1−z1)` / `s9·(1−z1)` have degree
`2`, so `inv(1)·act(2)·den(1)` is `4` — the margin is zero. -/
theorem qdeg_slots (δ : F) : qdeg F (slot0Q F δ) ≤ 4 ∧ qdeg F (slot1Q F δ) ≤ 4 ∧
    qdeg F (slot2Q F δ) ≤ 4 := by
  have hr : ∀ {m : ℕ} (r : Fin m → Entry), ∀ c, qdeg F (recQ F r c) ≤ 1 := fun r c =>
    qdeg_entryQ F (r c)
  have hd : ∀ {m : ℕ} (r : Fin m → Entry), qdeg F (denQ F δ m (recQ F r)) ≤ 1 := fun r =>
    qdeg_denQ F δ _ _ (hr r)
  have hinv : ∀ a b, qdeg F (invQ F a b) ≤ 1 := fun a b => by
    simp [invQ, qcol, qdeg, MixedExpr.degree]
  have hs : ∀ l, qdeg F (qlift F (selSum (F := F) l)) ≤ 1 := qdeg_qlift_sel F
  have h0 : qdeg F (recQ0 F |> fun f => f 0) ≤ 1 := by
    simp only [recQ0]; split_ifs
    · exact qdeg_entryQ F _
    · simp [qconst, qdeg, MixedExpr.degree]
  have hd0 : qdeg F (denQ F δ 11 (recQ0 F)) ≤ 1 := by
    refine qdeg_denQ F δ _ _ fun c => ?_
    simp only [recQ0]; split_ifs
    · exact qdeg_entryQ F _
    · simp [qconst, qdeg, MixedExpr.degree]
  have hm : ∀ a b : Q F, qdeg F a ≤ 1 → qdeg F b ≤ 1 → qdeg F (qmul F δ a b) ≤ 2 :=
    fun a b ha hb => (qdeg_qmul F δ a b).trans (by omega)
  have hm3 : ∀ a b : Q F, qdeg F a ≤ 2 → qdeg F b ≤ 1 → qdeg F (qmul F δ a b) ≤ 3 :=
    fun a b ha hb => (qdeg_qmul F δ a b).trans (by omega)
  obtain ⟨ha0, ha9⟩ := qdeg_actP F
  have h6 : qdeg F (qlift F (selVar 6 : CoeffExpr F)) ≤ 1 := by
    simp [qlift, qdeg, MixedExpr.degree, selVar, CoeffExpr.degree]
  refine ⟨?_, ?_, ?_⟩
  · refine (qdeg_qsub F _ _).trans (max_le ((hm _ _ (hinv _ _) hd0).trans (by omega)) ?_)
    simp [qconst, qdeg, MixedExpr.degree]
  · refine (qdeg_qsub F _ _).trans (max_le ?_ ?_)
    · refine (qdeg_qmul F δ _ _).trans ?_
      have h1 := hinv (lookupInvBase 0) (invImBase 1)
      have h2 : qdeg F (qadd F (qmul F δ (qlift F (actP0 F)) (denQ F δ 8 (recQ F op0PathRec)))
          (qmul F δ (qlift F (selSum slot1ExportSels)) (denQ F δ 10 (recQ F tailRec)))) ≤ 3 :=
        (qdeg_qadd F _ _).trans (max_le (hm3 _ _ ha0 (hd _)) ((hm _ _ (hs _) (hd _)).trans (by omega)))
      omega
    · exact (qdeg_qadd F _ _).trans (max_le (ha0.trans (by omega)) ((hs _).trans (by omega)))
  · refine (qdeg_qsub F _ _).trans (max_le ?_ ?_)
    · refine (qdeg_qmul F δ _ _).trans ?_
      have h1 := hinv (lookupInvBase 1) (invImBase 2)
      have h2 : qdeg F (qadd F (qmul F δ (qlift F (selVar 6)) (denQ F δ 10 (recQ F ttRec)))
          (qmul F δ (qlift F (actP9 F)) (denQ F δ 8 (recQ F op9PathRec)))) ≤ 3 :=
        (qdeg_qadd F _ _).trans (max_le ((hm _ _ h6 (hd _)).trans (by omega)) (hm3 _ _ ha9 (hd _)))
      omega
    · exact (qdeg_qadd F _ _).trans (max_le (h6.trans (by omega)) (ha9.trans (by omega)))

/-- The `z1` identity gates have `qdeg ≤ 3`. -/
theorem qdeg_z1EqQ (δ : F) (sel : ℕ) (r : Fin 8 → Entry) (c : Fin 3) : qdeg F (z1EqQ F δ sel r c) ≤ 3 := by
  refine (qdeg_qmul F δ _ _).trans ?_
  have h1 : qdeg F (qlift F (.mul (.var .traceCur z1Col) (selVar sel) : CoeffExpr F)) ≤ 2 :=
    (qdeg_qlift_le F _).trans (by simp [selVar, CoeffExpr.degree])
  have h2 := (qdeg_qsub F (entryQ F (r ⟨3 + (c : ℕ), by omega⟩)) (entryQ F (r ⟨(c : ℕ), by omega⟩))).trans
    (max_le (qdeg_entryQ F _) (qdeg_entryQ F _))
  omega

end LookupDeg

section Count2
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem lookupGatesT_degree (b : Basis (Fin 3) F K) (δ : F) :
    ∀ g ∈ lookupGatesT b δ, g.degree ≤ 4 := by
  obtain ⟨h0, h1, h2⟩ := qdeg_slots F δ
  have key : ∀ q : Q F, qdeg F q ≤ 4 → ∀ g ∈ qGates b q, g.degree ≤ 4 := by
    intro q hq g hg
    simp only [qGates, List.mem_append, List.mem_ofFn] at hg
    rcases hg with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ((gate_compiled_degree_le b col0Id q k).1).trans hq
    · exact ((gate_compiled_degree_le b col0Id q k).2).trans hq
  intro g hg
  simp only [lookupGatesT, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  exacts [key _ h0 g hg, key _ h1 g hg, key _ h2 g hg]

/-- **The `z1` gates have degree `≤ 3`.** -/
theorem z1Gates_degree (b : Basis (Fin 3) F K) (δ : F) : ∀ g ∈ z1Gates b δ, g.degree ≤ 3 := by
  have key : ∀ sel r c, ∀ g ∈ qGates b (z1EqQ F δ sel r c), g.degree ≤ 3 := by
    intro sel r c g hg
    simp only [qGates, List.mem_append, List.mem_ofFn] at hg
    rcases hg with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ((gate_compiled_degree_le b col0Id _ k).1).trans (qdeg_z1EqQ F δ sel r c)
    · exact ((gate_compiled_degree_le b col0Id _ k).2).trans (qdeg_z1EqQ F δ sel r c)
  intro g hg
  simp only [z1Gates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hg
  rcases hg with ((rfl | rfl) | ⟨c, -, hg⟩) | ⟨c, -, hg⟩
  · simp [z1BoolGate, CoeffExpr.degree]
  · simp [z1AxGate, CoeffExpr.degree]
  · exact key _ _ _ g hg
  · exact key _ _ _ g hg

end Count2

section Count
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem coreIm_count : (coreImIds towerM).length = 70 := by decide +kernel
theorem wIm_counts :
    (((List.finRange 3).map auxTarget).filter (hasImW towerM)).length = 1 ∧
    (endpoint2Q7.filter (hasImW towerM)).length = 1 ∧
    (endpoint4_309.filter (hasImW towerM)).length = 1 := by decide +kernel

theorem flatMap_ofFn3_length {α : Type} (l : List α) (f : α → Fin 3 → CoeffExpr F) :
    (l.flatMap fun a => List.ofFn (f a)).length = 3 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]; ring

theorem towerKeptGates_length (n e : ℕ) (b : Basis (Fin 3) F K) (δ : F) :
    (towerKeptGates n e b δ).length = 289 + 3 * 70 + 9 := by
  have h289 := keptGatesQ7_length (F := F) n b
  simp only [keptGatesQ7, List.length_append] at h289
  have hcr : (correctedCoreVCLQ7 b).length = 3 * keptCoreIdsQ7.length :=
    flatMap_ofFn3_length keptCoreIdsQ7 (fun i k => correctedCoreCoord309 b i k)
  have hre : (towerCoreRe b δ e).length = 3 * keptCoreIdsQ7.length :=
    flatMap_ofFn3_length keptCoreIdsQ7 (fun i k => coreRe b δ e towerM i k)
  have him : (towerCoreIm b δ e).length = 3 * (coreImIds towerM).length :=
    flatMap_ofFn3_length (coreImIds towerM) (fun i k => coreIm b δ e towerM i k)
  have hw : ∀ ts : List WTyped, (wImList b δ e ts).length = 3 * (ts.filter (hasImW towerM)).length :=
    fun ts => flatMap_ofFn3_length (ts.filter (hasImW towerM)) (fun g k => wIm b δ e g k)
  obtain ⟨c1, c2, c3⟩ := wIm_counts
  rw [coreIm_count] at him
  simp only [towerKeptGates, List.length_append, hre, him, hw, c1, c2, c3]
  omega

theorem vclGatesQ7T_length (n e : ℕ) (b : Basis (Fin 3) F K) (δ : F) :
    (vclGatesQ7T n e b δ).length = 608 := by
  simp only [vclGatesQ7T, List.length_append, towerKeptGates_length, lookupGatesT_length,
    accGatesT_length, axGates_length, axImGates_length, serialGates, List.length_cons,
    List.length_nil, List.length_map, towerKeptGates_length, z1Gates_length]

theorem keptDeg (n : ℕ) (b : Basis (Fin 3) F K) :
    ∀ g ∈ keptGatesQ7 n b, g.degree ≤ 4 := by
  intro g hg
  have := vclGatesQ7_degree n b 21 24 (reindexE g) (by
    simp only [vclGatesQ7, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨g, hg, rfl⟩)))))
  rwa [degree_reindexE] at this

theorem auxTarget_degree : ∀ j, (auxTarget j).degree ≤ 4 := by decide +kernel

theorem wIm_degree (b : Basis (Fin 3) F K) (δ : F) (e : ℕ) (g : WTyped) (hg : g.degree ≤ 4)
    (k : Fin 3) : (wIm b δ e g k).degree ≤ 4 :=
  ((gate_compiled_degree_le b col0Id (toQW F towerM e δ g) k).2).trans
    ((toQW_qdeg_le F towerM e δ g).trans hg)

theorem towerKeptGates_degree (n e : ℕ) (b : Basis (Fin 3) F K) (δ : F) :
    ∀ g ∈ towerKeptGates n e b δ, g.degree ≤ 4 := by
  have hex : ∀ i : CorrectedCoreExtGateId, correctedFinalExtGate i ∈
      correctedLoweredExt ++ correctedEndpoint2 ++ correctedEndpoint4 := fun i => by
    simp only [List.mem_append]
    exact Or.inl (Or.inl (List.get_mem _ _))
  have hw2 : ∀ g ∈ endpoint2Q7, g.degree ≤ 4 := fun g hg =>
    (endpoint2_309_degree g (endpoint2Q7_sub g hg)).trans (by norm_num)
  intro g hg
  simp only [towerKeptGates, List.mem_append] at hg
  rcases hg with ((((((((hb | hr) | hi) | ha) | hai) | h2) | h2i) | h4) | h4i) | heq
  · exact keptDeg n b g (by simp [keptGatesQ7, hb])
  · simp only [towerCoreRe, List.mem_flatMap, List.mem_ofFn] at hr
    obtain ⟨i, hi, ⟨k, rfl⟩⟩ := hr
    unfold coreRe
    split_ifs
    · refine keptDeg n b _ ?_
      simp only [keptGatesQ7, List.mem_append, correctedCoreVCLQ7, List.mem_flatten, List.mem_map]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        ⟨_, ⟨i, hi, rfl⟩, List.mem_ofFn.mpr ⟨k, rfl⟩⟩))))
    · exact ((towerTwin_degree_le_four F b towerM e δ).1 _ (hex i) k).1
  · simp only [towerCoreIm, List.mem_flatMap, List.mem_ofFn] at hi
    obtain ⟨i, hi, ⟨k, rfl⟩⟩ := hi
    unfold coreIm
    split_ifs
    · simp [OptimizedComputeFinal.notLastCoeff, OptimizedComputeBaseGates.isLastVar,
        OptimizedComputeBaseGates.bv, CoeffExpr.degree]
    · exact ((towerTwin_degree_le_four F b towerM e δ).1 _ (hex i) k).2
  · exact keptDeg n b g (by simp [keptGatesQ7, ha])
  · simp only [wImList, List.mem_flatMap, List.mem_filter, List.mem_ofFn] at hai
    obtain ⟨t, ⟨ht, _⟩, ⟨k, rfl⟩⟩ := hai
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht
    exact wIm_degree b δ e _ (auxTarget_degree j) k
  · exact keptDeg n b g (by simp [keptGatesQ7, h2])
  · simp only [wImList, List.mem_flatMap, List.mem_filter, List.mem_ofFn] at h2i
    obtain ⟨t, ⟨ht, _⟩, ⟨k, rfl⟩⟩ := h2i
    exact wIm_degree b δ e _ (hw2 t ht) k
  · exact keptDeg n b g (by simp [keptGatesQ7, h4])
  · simp only [wImList, List.mem_flatMap, List.mem_filter, List.mem_ofFn] at h4i
    obtain ⟨t, ⟨ht, _⟩, ⟨k, rfl⟩⟩ := h4i
    exact wIm_degree b δ e _ (endpoint4_309_degree t ht) k
  · exact keptDeg n b g (by simp [keptGatesQ7, heq])

theorem vclGatesQ7T_degree (n e : ℕ) (b : Basis (Fin 3) F K) (δ : F) :
    ∀ g ∈ vclGatesQ7T n e b δ, g.degree ≤ 4 := by
  intro g hg
  simp only [vclGatesQ7T, List.mem_append, List.mem_map] at hg
  rcases hg with ((((⟨g', hg', rfl⟩ | hs) | hax) | hl) | hx) | hz
  · rw [degree_reindexE]; exact towerKeptGates_degree n e b δ g' hg'
  · exact (serialGates_degree g hs).trans (by norm_num)
  · rcases hax with hax | hax
    · exact (axGates_degree b g hax).trans (by norm_num)
    · exact (axImGates_degree g hax).trans (by norm_num)
  · exact lookupGatesT_degree b δ g hl
  · exact accGatesT_degree g hx
  · exact (z1Gates_degree b δ g hz).trans (by norm_num)

end Count

/-! ## 6. -/

section Coins
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The `𝕂′` coin `z′ = (χ 2, χ 3)`. -/
def zQuad (χ : Coins frameVCL K) : Quad (algebraMap F K δ) :=
  Quad.mk _ (χ ⟨2, by decide⟩) (χ ⟨3, by decide⟩)

/-- **`chalKQ7T`**: `chalKQ7` with the tower slots: `5 ↦ Re (z′⁻¹)`, `12 ↦ χ 3` (`z₂`),
`13 ↦ Im (z′⁻¹)`, `14 ↦ χ 6` (`γ₁`), `15 ↦ χ 7` (`ρ₁`). -/
def chalKQ7T (χ : Coins frameVCL K) (q : ℕ) : K :=
  if q = 5 then Quad.re _ (zQuad δ χ)⁻¹
  else if q = 12 then χ ⟨3, by decide⟩
  else if q = 13 then Quad.im _ (zQuad δ χ)⁻¹
  else if q = 14 then χ ⟨6, by decide⟩
  else if q = 15 then χ ⟨7, by decide⟩
  else chalKQ7 χ q

/-- **`chalVQ7T`**: the raw challenge vector at the tower (limbs `3q.. 3q+2`, `q < 16`). -/
def chalVQ7T (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) : ℕ → F :=
  fun j => if j < 48 then coord b (chalKQ7T δ χ (j / 3)) ⟨j % 3, Nat.mod_lt j (by decide)⟩ else 0

theorem chalVQ7T_old (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) (j : ℕ)
    (hj : j < 36) (h5 : j / 3 ≠ 5) : chalVQ7T δ b χ j = chalVQ7 b χ j := by
  have h12 : j / 3 < 12 := by omega
  have hj48 : j < 48 := by omega
  simp only [chalVQ7T, chalVQ7, hj, hj48, if_true, chalKQ7T, h5]
  have : j / 3 ≠ 12 ∧ j / 3 ≠ 13 ∧ j / 3 ≠ 14 ∧ j / 3 ≠ 15 := by omega
  simp [this.1, this.2.1, this.2.2.1, this.2.2.2]

/-- The tower coin slots read the pair coins. -/
theorem chalKQ7T_tower (χ : Coins frameVCL K) :
    chalKQ7T δ χ 12 = χ ⟨3, by decide⟩ ∧ chalKQ7T δ χ 14 = χ ⟨6, by decide⟩ ∧
      chalKQ7T δ χ 15 = χ ⟨7, by decide⟩ ∧
      Quad.mk _ (chalKQ7T δ χ 5) (chalKQ7T δ χ 13) = (zQuad δ χ)⁻¹ := by
  refine ⟨by simp [chalKQ7T], by simp [chalKQ7T], by simp [chalKQ7T], ?_⟩
  simp [chalKQ7T, Quad.mk_re_im]

end Coins

/-! ## 7. The tower chip (item 5) -/

section Chip
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
  Nock.Framework.Reify

/-- **The tower RAP**: `vclRAPQ7S` with the tower gate list and width `409`
(`wRAP = ![208, 201]`: round `0` unchanged, every appended column in the second round —
UNCONFIRMED round placement of the Im / inverse-Im / accumulator-Im columns). -/
def vclRAPQ7T {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n e : ℕ} (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![vclRound0, 202]
    w := vclWidthT
    w_eq := by simp [Fin.sum_univ_two, vclRound0, vclWidthT]
    h := h
    d := 4
    s := (vclGatesQ7T n e b δ).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalV pubVal ((vclGatesQ7T n e b δ).get i)
    C_vars := fun _i => coeffToMv_vars chalV pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalV pubVal _).trans
      (vclGatesQ7T_degree n e b δ _ (List.get_mem _ _))
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- **`computeChipVCLQ7T`**: the compute chip at the tower. -/
def computeChipVCLQ7T
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPQ7T (n := n) (e := MemoryTable.pwScaleExp K) b δ chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := Nat.two_pos
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          have := j.isLt
          change 11 + (j : ℕ) < vclRound0
          simp only [vclRound0]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

theorem vclRAPQ7T_w
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n e : ℕ} (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (vclRAPQ7T (n := n) (e := e) b δ chalV pubVal orbit H).w = 410 := rfl

theorem vclRAPQ7T_s
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n e : ℕ} (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (vclRAPQ7T (n := n) (e := e) b δ chalV pubVal orbit H).s = 608 := by
  have h := vclGatesQ7T_length n e b δ
  simp only [vclRAPQ7T]
  exact h

theorem vclRAPQ7T_d
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n e : ℕ} (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (vclRAPQ7T (n := n) (e := e) b δ chalV pubVal orbit H).d = 4 ∧
    (vclRAPQ7T (n := n) (e := e) b δ chalV pubVal orbit H).k = 2 ∧
    (vclRAPQ7T (n := n) (e := e) b δ chalV pubVal orbit H).e = 3 := ⟨rfl, rfl, rfl⟩

end Chip

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
