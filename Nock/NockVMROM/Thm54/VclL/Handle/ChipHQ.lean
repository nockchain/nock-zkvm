/-
  Nock/NockVMROM/Thm54/VclL/Handle/ChipHQ.lean

  A NEW chip beside
  `computeChipVCLH`; no existing module is edited.

  | cols | group |
  |---|---|
  | `70 / 73 / 76` | Im of the slot inverses `inv0 / inv1 / inv2` (`𝕂`, 3 limbs each) |
  | `79 / 82`      | Im of the accumulators `accX / accP` |

  **Coins** (compute challenge limbs): `0..2` Re `γH`, `3..5` Re `ρH`, `6..8` `αW`, `9..11` `γW`
  (unchanged), `12..14` Im `γH`, `15..17` Im `ρH`.  **Publics**: `0..20` as `computeChipVCLH`
  (`15..17 / 18..20` = Re `ρ₃ / ρ₄`), `21..23 / 24..26` = Im `ρ₃ / ρ₄`.

  **Gates**: the base gates of `computeChipVCLH` with `accGatesH` extended by the Im accumulators
  (`accGates 3` on the Im inverse limbs: `act ∈ 𝔽` scales the inverse, so the `𝕂′` accumulator is
  the existing gate on each half), the three slot gates as `𝕂′` pairs (`qGates`, 6 coordinate gates
  each) with `den′ = ρH + Σ_k γH^k · lift(col_k)` over `𝕂′`, and the nine walk gates unchanged.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipH

namespace Nock.NockVMROM.Thm54
namespace VclL.Handle
namespace ChipHQ

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.Framework

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. Layout -/

def invIm0 : ℕ := 70
def invIm1 : ℕ := 73
def invIm2 : ℕ := 76
def accXIm : ℕ := 79
def accPIm : ℕ := 82

/-- **The `𝕂′` handle chip's width.** -/
def widthHQ : ℕ := 85

/-- Width breakdown: `computeChipVCLH`'s `70` plus the Im triples of the 3 inverses and 2 accumulators. -/
theorem widthHQ_eq : widthHQ = widthH + 3 * 3 + 2 * 3 := rfl

theorem layoutQ_tiles :
    widthH = invIm0 ∧ invIm0 + 3 = invIm1 ∧ invIm1 + 3 = invIm2 ∧ invIm2 + 3 = accXIm ∧
      accXIm + 3 = accPIm ∧ accPIm + 3 = widthHQ := by decide

/-- The Im column of a slot inverse (`43 ↦ 70`, `46 ↦ 73`, `49 ↦ 76`). -/
def imOf (re : ℕ) : ℕ := if re = inv0 then invIm0 else if re = inv1 then invIm1 else invIm2

def chalGammaIm : ℕ := 12
def chalRhoIm : ℕ := 15
def pubRhoXIm : ℕ := 21
def pubRhoPIm : ℕ := 24

/-! ## 2. The `𝕂′` lookup -/

section Q
variable (F : Type) [Field F]

/-- The `𝕂′` handle coins `γH = (0, 12)`, `ρH = (3, 15)` (Re / Im first limbs). -/
def qγH : Q F := qvar F .challenge chalGammaL (some chalGammaIm)
def qρH : Q F := qvar F .challenge chalRhoL (some chalRhoIm)

/-- `Σ_k γH^k · lift(col_k)` over `𝕂′` (the only form in which a `𝕂′` gate reads a handle value). -/
def rlcKeyQ (δ : F) : ℕ → List ℕ → Q F
  | _, [] => qconst F 0
  | n, i :: r => qadd F (qmul F δ (qpow F δ (qγH F) n) (qlift F (cc i))) (rlcKeyQ δ (n + 1) r)

/-- The `𝕂′` denominator of a record. -/
def denQH (δ : F) (r : List ℕ) : Q F := qadd F (qρH F) (rlcKeyQ F δ 0 r)

def sumQ (l : List (Q F)) : Q F := l.foldr (qadd F) (qconst F 0)

/-- **The slot gate over `𝕂′`**: `inv′ · (Σ act·den′ [+ pr·den′ₐ·den′_b]) − (Σ act [+ pr·(den′ₐ + den′_b)])`. -/
def slotGateQ (δ : F) (S : SlotSpec F) : Q F :=
  qsub F (qmul F δ (qvar F .traceCur S.inv (some (imOf S.inv)))
      (qadd F (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQH F δ x.rcd)))
        (match S.pair with
         | some (fl, a, b) => qmul F δ (qlift F (cc fl)) (qmul F δ (denQH F δ a) (denQH F δ b))
         | none => qconst F 0)))
    (qadd F (qlift F (CoeffExpr.sumList S.ents Ent.act))
      (match S.pair with
       | some (fl, a, b) => qmul F δ (qlift F (cc fl)) (qadd F (denQH F δ a) (denQH F δ b))
       | none => qconst F 0))

end Q

/-! ## 3. The accumulators: Re (as `computeChipVCLH`) and Im -/

section Acc
variable {F : Type} [Field F]

/-- **The `𝕂′` accumulators**: `accGatesH` on the Re limbs, the same gates on the Im limbs. -/
def accGatesHQ : List (CoeffExpr F) :=
  accGatesH ++
    accGates 3 (slots.map fun S => ⟨S.actX, imOf S.inv⟩) accXIm pubRhoXIm ++
    accGates 3 (slots.map fun S => ⟨S.actP, imOf S.inv⟩) accPIm pubRhoPIm

/-- Base gates (generic builder): `computeChipVCLH`'s with the Im accumulators. -/
def baseGatesHQ : List (CoeffExpr F) := arithGates ++ accGatesHQ ++ eqGates.map EqG.gate

end Acc

/-! ## 4. The gate list and the chip -/

section Assemble
variable {F K : Type} [Field F] [Field K] [Algebra F K]

def baseGatesFQ : List (CoeffExpr F) := (baseGatesHQ (F := ℚ)).map (mapC (fun q : ℚ => (q : F)))

def walkGatesF : List (MixedExpr F) := (walkGates (F := ℚ)).map (mapM (fun q : ℚ => (q : F)))

/-- The three `𝕂′` slot pairs. -/
def slotPairs (δ : F) : List (Q F) := (slots (F := F)).map (slotGateQ F δ)

/-- **The gates of `computeChipVCLHQ`**: base, the `𝕂′` slot pairs (`6` coordinate gates each), the
compiled walk gates. -/
def gatesHQ (b : Basis (Fin 3) F K) (δ : F) : List (CoeffExpr F) :=
  baseGatesFQ ++ (slotPairs δ).flatMap (qGates b) ++
    (walkGatesF (F := F)).flatMap fun g => List.ofFn (mixedCompile b col0Id g)

end Assemble

/-! ## 5. Degree -/

section Degree
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem baseTemplateQ_degree :
    ((baseGatesHQ (F := ℚ)).all fun g => decide (g.degree ≤ 4)) = true := by decide +kernel

theorem walkTemplate_degree :
    ((walkGates (F := ℚ)).all fun g => decide (g.degree ≤ 4)) = true := by decide +kernel

theorem baseGatesFQ_degree : ∀ g ∈ (baseGatesFQ : List (CoeffExpr F)), g.degree ≤ 4 := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [degree_mapC]
  simpa using List.all_eq_true.mp baseTemplateQ_degree t ht

theorem walkGatesF_degree : ∀ g ∈ (walkGatesF : List (MixedExpr F)), g.degree ≤ 4 := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
  rw [degree_mapM]
  simpa using List.all_eq_true.mp walkTemplate_degree t ht

theorem qdeg_qconst0 (c : ℤ) : qdeg F (qconst F c) = 0 := by
  simp [qconst, qdeg, MixedExpr.degree]

theorem qdeg_qγH : qdeg F (qγH F) = 0 := by rw [qγH, qdeg_qvar]; simp [MixedExpr.degree]
theorem qdeg_qρH : qdeg F (qρH F) = 0 := by rw [qρH, qdeg_qvar]; simp [MixedExpr.degree]

theorem qdeg_rlcKeyQ (δ : F) : ∀ (r : List ℕ) (n : ℕ), qdeg F (rlcKeyQ F δ n r) ≤ 1
  | [], n => by rw [rlcKeyQ, qdeg_qconst0]; omega
  | i :: r, n => by
      rw [rlcKeyQ]
      refine (qdeg_qadd F _ _).trans (max_le ?_ (qdeg_rlcKeyQ δ r (n + 1)))
      refine (qdeg_qmul F δ _ _).trans ?_
      have h1 := (qdeg_qpow F δ (qγH F) n).trans (by rw [qdeg_qγH]; omega : n * qdeg F (qγH F) ≤ 0)
      have h2 := (qdeg_qlift_le F (cc i)).trans (by simp [cc, CoeffExpr.degree] : (cc i : CoeffExpr F).degree ≤ 1)
      omega

theorem qdeg_denQH (δ : F) (r : List ℕ) : qdeg F (denQH F δ r) ≤ 1 :=
  (qdeg_qadd F _ _).trans (max_le (by rw [qdeg_qρH]; omega) (qdeg_rlcKeyQ δ r 0))

theorem qdeg_sumQ (l : List (Q F)) (k : ℕ) (h : ∀ q ∈ l, qdeg F q ≤ k) : qdeg F (sumQ F l) ≤ k := by
  induction l with
  | nil => simp [sumQ, qdeg_qconst0]
  | cons a t ih =>
    simp only [sumQ, List.foldr_cons] at ih ⊢
    exact (qdeg_qadd F _ _).trans (max_le (h a (by simp)) (ih fun q hq => h q (by simp [hq])))

/-- A slot pair has degree `≤ 4` when its activities have degree `≤ 2` (`inv·act·den`, `inv·pr·dₐ·d_b`). -/
theorem slotGateQ_deg (δ : F) (S : SlotSpec F) (hact : ∀ x ∈ S.ents, x.act.degree ≤ 2)
    (hpair : ∀ fl a b, S.pair = some (fl, a, b) → (cc fl : CoeffExpr F).degree ≤ 1) :
    qdeg F (slotGateQ F δ S) ≤ 4 := by
  have hinv : qdeg F (qvar F .traceCur S.inv (some (imOf S.inv))) ≤ 1 := by
    rw [qdeg_qvar]; simp [MixedExpr.degree]
  have hs : qdeg F (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQH F δ x.rcd))) ≤ 3 := by
    refine qdeg_sumQ _ 3 fun q hq => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    have := (qdeg_qlift_le F x.act).trans (hact x hx)
    have := qdeg_denQH δ x.rcd
    exact (qdeg_qmul F δ _ _).trans (by omega)
  have hsum : qdeg F (qlift F (CoeffExpr.sumList S.ents Ent.act)) ≤ 2 :=
    (qdeg_qlift_le F _).trans (CoeffExpr.degree_sumList_le _ _ _ hact)
  have hp1 : qdeg F (match S.pair with
      | some (fl, a, b) => qmul F δ (qlift F (cc fl)) (qmul F δ (denQH F δ a) (denQH F δ b))
      | none => qconst F 0) ≤ 3 := by
    rcases hp : S.pair with _ | ⟨fl, a, b⟩
    · simp [qdeg_qconst0]
    · have hf := (qdeg_qlift_le F (cc fl)).trans (hpair fl a b hp)
      have ha := qdeg_denQH δ a; have hb := qdeg_denQH δ b
      refine (qdeg_qmul F δ _ _).trans ?_
      have := qdeg_qmul F δ (denQH F δ a) (denQH F δ b)
      omega
  unfold slotGateQ
  refine (qdeg_qsub F _ _).trans (max_le ?_ ?_)
  · refine (qdeg_qmul F δ _ _).trans ?_
    have := (qdeg_qadd F (sumQ F (S.ents.map fun x => qmul F δ (qlift F x.act) (denQH F δ x.rcd))) _).trans
      (max_le hs hp1)
    omega
  · refine (qdeg_qadd F _ _).trans (max_le (hsum.trans (by omega)) ?_)
    rcases hp : S.pair with _ | ⟨fl, a, b⟩
    · simp [qdeg_qconst0]
    · have hf := (qdeg_qlift_le F (cc fl)).trans (hpair fl a b hp)
      have ha := qdeg_denQH δ a; have hb := qdeg_denQH δ b
      refine (qdeg_qmul F δ _ _).trans ?_
      have := qdeg_qadd F (denQH F δ a) (denQH F δ b)
      omega

theorem slots_act_deg : ∀ S ∈ (slots : List (SlotSpec F)), ∀ x ∈ S.ents, x.act.degree ≤ 2 := by
  intro S hS x hx
  simp only [slots, slot0, slot1, slot2, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    simp [Ent.act, selS, CoeffExpr.degree, notC, cc, CoeffExpr.degree_sumList_le,
      ChipH.allStates, l2States]

/-- Every slot pair has degree `≤ 4`. -/
theorem slotPairs_degree (δ : F) : ∀ q ∈ slotPairs δ, qdeg F q ≤ 4 := by
  intro q hq
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hq
  exact slotGateQ_deg δ S (slots_act_deg S hS) (fun fl a b _ => by simp [cc, CoeffExpr.degree])

/-- **Degree `≤ 4` for every gate of the chip.** -/
theorem gatesHQ_degree (b : Basis (Fin 3) F K) (δ : F) : ∀ g ∈ gatesHQ b δ, g.degree ≤ 4 := by
  intro g hg
  simp only [gatesHQ, List.mem_append, List.mem_flatMap, List.mem_ofFn] at hg
  rcases hg with (hg | ⟨q, hq, hg⟩) | ⟨m, hm, k, rfl⟩
  · exact baseGatesFQ_degree g hg
  · have hd := slotPairs_degree δ q hq
    simp only [qGates, List.mem_append, List.mem_ofFn] at hg
    rcases hg with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact (mixedCompile_degree_le b _ q.1 k).trans (le_trans (le_max_left _ _) hd)
    · exact (mixedCompile_degree_le b _ q.2 k).trans (le_trans (le_max_right _ _) hd)
  · exact (mixedCompile_degree_le b _ m k).trans (walkGatesF_degree m hm)

end Degree

/-! ## 6. -/

section Instrument
variable {F : Type} [Field F]

/-- A coefficient that reads no trace column (coins and constants only). -/
def coinOnly : MixedExpr F → Bool
  | .Var .challenge _ => true
  | .Const _ => true
  | .Scale (.const _) u => coinOnly u
  | .Add x y => coinOnly x && coinOnly y
  | .Sub x y => coinOnly x && coinOnly y
  | .Mul x y => coinOnly x && coinOnly y
  | .Neg x => coinOnly x
  | .Pow x _ => coinOnly x
  | _ => false

def keyOKQe : MixedExpr F → Bool
  | .Mul x (.Lift (.var _ _)) => coinOnly x
  | .Var _ _ => true
  | .Lift g => serialFreeB g
  | .Scale g u => serialFreeB g && keyOKQe u
  | .Const _ => true
  | .Add x y => keyOKQe x && keyOKQe y
  | .Sub x y => keyOKQe x && keyOKQe y
  | .Mul x y => keyOKQe x && keyOKQe y
  | .Neg x => keyOKQe x
  | .Pow x _ => keyOKQe x

def keyOKQ (q : Q F) : Bool := keyOKQe q.1 && keyOKQe q.2

theorem slotPairs_keyOK : (slotPairs (F := ℚ) 7).all keyOKQ = true := by decide +kernel

/-- The base gates added by the twin (Im accumulators) are serial-free. -/
theorem accGatesHQ_serialFree : ((accGatesHQ (F := ℚ)).all serialFreeB) = true := by decide +kernel

/-- **Positive control**: the instrument flags a pair that multiplies a denominator by a serial. -/
theorem keyOKQ_flags : keyOKQ (qmul ℚ 7 (denQH ℚ 7 [hS.v]) (qlift ℚ (cc hS.v))) = false := by
  decide +kernel

end Instrument

/-! ## 7. The chip -/

section Chip
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **The `𝕂′` handle compute RAP** (`wRAP = ![43, 42]`: B0 columns, then the coin-dependent block). -/
def vclRAPHQ [FiniteDimensional F K] {h : ℕ} (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![round0W, 42]
    w := widthHQ
    w_eq := by simp [Fin.sum_univ_two, round0W, widthHQ]
    h := h
    d := 4
    s := (gatesHQ b δ).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalV pubVal ((gatesHQ b δ).get i)
    C_vars := fun _i => coeffToMv_vars chalV pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalV pubVal _).trans
      (gatesHQ_degree b δ _ (List.get_mem _ _))
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

/-- **`computeChipVCLHQ`**: the `𝕂′` handle compute chip (preprocessing `isFirst` / `isLast` at
`11` / `12`, as `computeChipVCLH`). -/
def computeChipVCLHQ [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPHQ b δ chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := Nat.two_pos
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          have := j.isLt
          change 11 + (j : ℕ) < round0W
          simp only [round0W]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

theorem computeChipVCLHQ_width [FiniteDimensional F K] {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).rap.w = 85 := rfl

end Chip

end

end ChipHQ
end VclL.Handle
end Nock.NockVMROM.Thm54
