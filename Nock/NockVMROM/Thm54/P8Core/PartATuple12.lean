/-
  Nock/NockVMROM/Thm54/P8Core/PartATuple12.lean

  * `MemoryChallengeTuple12` = `MemoryChallengeTuple` plus the memory WALK coin `walkAlpha` (`αW`).
  * `forget12` drops `αW` (the cylinder projection onto the landed eleven-coin tuple);
    `tuple12Equiv : Tuple12 ≃ Tuple × 𝕂`; `landedVec12` / `tuple12VecEquiv` (the landed order with
    `αW` at index `11`, `RepartitionedStaging.repartitionedChronology`'s order).
  * `memoryKOfTuple12`: realization (i), as signed.  `memoryChalValOfTuple12`'s bound is `j < 36` (was `j < 33`).
  * `memoryPublicOfTuple12`: the memory walk `initial_count = αW ^ kMem`.
  * `walkView11`: the eleven-coin tuple whose `alphaM` slot carries `αW`.  It is used ONLY to
    transport the MEMORY chip (`memoryChalValOfTuple12_swap`, `memoryPublicOfTuple12_eq_view`): the
    memory chip reads no timestamp coin.
-/
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.FormRAxisEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.PartA12

open Nock Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.CoordinateBasis
open Module

noncomputable section

/-! ## 1. The memory block and the tuple -/

/-- **The twelve-coin memory block**: the internal pole, the Form R `λ`, and the memory WALK coin
`walkAlpha`. -/
@[ext]
structure MemoryChallengeTuple12 (K : Type*) where
  interPole : K
  lambda : K
  /-- The memory walk coin `αW` (W-a).  Read by the six memory walk gates at memory slot `9`. -/
  walkAlpha : K
deriving DecidableEq, Fintype

theorem memoryChallengeTuple12_card (K : Type*) [Fintype K] :
    Fintype.card (MemoryChallengeTuple12 K) = Fintype.card K ^ 3 := by
  let e : MemoryChallengeTuple12 K ≃ (K × K × K) :=
    { toFun := fun c => (c.interPole, c.lambda, c.walkAlpha)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := by intro c; cases c; rfl
      right_inv := by intro p; rfl }
  rw [Fintype.card_congr e]
  simp [pow_three]

/-- **The twelve-coin production tuple** (`|𝕂|¹²`): the landed tuple with the memory block
`MemoryChallengeTuple12`.  The JointCoins block `c.1` is unchanged: `alphaM c.1` is the timestamp
base only (W-a). -/
abbrev OptimizedProductionChallengeTuple12 (K F : Type) [Fintype K] [Fintype F] :=
  JointCoins K ×
    ((K × K) ×
      (FinalComputeChallengeTuple K × MemoryChallengeTuple12 K))

variable {K F : Type} [Fintype K] [Fintype F]

/-- **`|𝕂|¹²`.** -/
theorem card_optimizedProductionChallengeTuple12 (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedProductionChallengeTuple12 K F) = Fintype.card K ^ 12 := by
  simp only [Fintype.card_prod, card_finalComputeChallengeTuple, memoryChallengeTuple12_card]
  ring

/-- The walk coin of a twelve-coin tuple. -/
abbrev walkAlphaOf (c : OptimizedProductionChallengeTuple12 K F) : K := c.2.2.2.walkAlpha

/-- **The cylinder projection**: drop `αW`. -/
def forget12 (c : OptimizedProductionChallengeTuple12 K F) : OptimizedProductionChallengeTuple K F :=
  (c.1, (c.2.1, (c.2.2.1, ⟨c.2.2.2.interPole, c.2.2.2.lambda⟩)))

/-- Extend a landed tuple by a walk coin. -/
def extend12 (c : OptimizedProductionChallengeTuple K F) (αW : K) :
    OptimizedProductionChallengeTuple12 K F :=
  (c.1, (c.2.1, (c.2.2.1, ⟨c.2.2.2.interPole, c.2.2.2.lambda, αW⟩)))

@[simp] theorem forget12_extend12 (c : OptimizedProductionChallengeTuple K F) (αW : K) :
    forget12 (extend12 c αW) = c := rfl

@[simp] theorem walkAlphaOf_extend12 (c : OptimizedProductionChallengeTuple K F) (αW : K) :
    walkAlphaOf (extend12 c αW) = αW := rfl

theorem extend12_forget12 (c : OptimizedProductionChallengeTuple12 K F) :
    extend12 (forget12 c) (walkAlphaOf c) = c := rfl

/-- `Tuple12 ≃ Tuple × 𝕂` (the free twelfth coordinate). -/
def tuple12Equiv : OptimizedProductionChallengeTuple12 K F ≃ OptimizedProductionChallengeTuple K F × K where
  toFun c := (forget12 c, walkAlphaOf c)
  invFun p := extend12 p.1 p.2
  left_inv c := rfl
  right_inv p := rfl

theorem forget12_joint (c : OptimizedProductionChallengeTuple12 K F) : (forget12 c).1 = c.1 := rfl

/-- The timestamp coin is untouched by `forget12` (W-a: `alphaM` is the timestamp base). -/
theorem alphaM_forget12 (c : OptimizedProductionChallengeTuple12 K F) :
    alphaM (forget12 c).1 = alphaM c.1 := rfl

/-! ## 2. The landed vector, with `αW` at index `11` -/

/-- The twelve coordinates in `repartitionedChronology`'s order:
`(αC, γ, αM, z | IOγ, IOpole | a, b, c | interPole, λ | αW)`. -/
def landedVec12 (c : OptimizedProductionChallengeTuple12 K F) : Fin 12 → K :=
  ![alphaC c.1, gamma c.1, alphaM c.1, nprSeed c.1, c.2.1.1, c.2.1.2,
    c.2.2.1.eqA, c.2.2.1.eqB, c.2.2.1.eqC, c.2.2.2.interPole, c.2.2.2.lambda,
    c.2.2.2.walkAlpha]

/-- Inverse of `landedVec12`. -/
def tuple12OfVec (x : Fin 12 → K) : OptimizedProductionChallengeTuple12 K F :=
  (((x 0, x 1), (x 2, x 3)), ((x 4, x 5), (⟨x 6, x 7, x 8⟩, ⟨x 9, x 10, x 11⟩)))

/-- The twelve-coin tuple is the coin vector `Fin 12 → 𝕂`. -/
def tuple12VecEquiv : OptimizedProductionChallengeTuple12 K F ≃ (Fin 12 → K) where
  toFun := landedVec12
  invFun := tuple12OfVec
  left_inv c := by
    rcases c with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨⟨a5, a6⟩, ⟨⟨a7, a8, a9⟩, ⟨a10, a11, a12⟩⟩⟩⟩
    rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- The first eleven coordinates are the landed eleven-coin vector of `forget12`. -/
theorem landedVec12_castSucc (c : OptimizedProductionChallengeTuple12 K F) (j : Fin 11) :
    landedVec12 c (Fin.castSucc j) = FormRAxisEvent.landedVec (forget12 c) j := by
  fin_cases j <;> rfl

theorem landedVec12_walk (c : OptimizedProductionChallengeTuple12 K F) :
    landedVec12 c 11 = walkAlphaOf c := rfl

/-! ## 3. The memory-chip view and the slot maps (realization (i)) -/

/-- **The memory-chip view** (memory chip ONLY; see the module docstring and C2): the eleven-coin
tuple whose `alphaM` coordinate carries `αW`.  Every other coordinate is `forget12`'s. -/
def walkView11 (c : OptimizedProductionChallengeTuple12 K F) : OptimizedProductionChallengeTuple K F :=
  (((alphaC c.1, gamma c.1), (c.2.2.2.walkAlpha, nprSeed c.1)), (forget12 c).2)

/-- The JointCoins block that summands `7` and `10` (the memory walk events) are lifted on:
`(αC, γ, αW, z)` (`liftWalkWFailure`, `PartAEvents12`). -/
def walkJoint (c : OptimizedProductionChallengeTuple12 K F) : JointCoins K := (walkView11 c).1

theorem alphaM_walkJoint (c : OptimizedProductionChallengeTuple12 K F) :
    alphaM (walkJoint c) = walkAlphaOf c := rfl

theorem gamma_walkJoint (c : OptimizedProductionChallengeTuple12 K F) :
    gamma (walkJoint c) = gamma c.1 := rfl

variable [Field F] [Field K] [Algebra F K] [DecidableEq K] [FiniteDimensional F K]

/-- **Memory `𝕂` coin at index `q` of a twelve-coin tuple (realization (i)).** -/
def memoryKOfTuple12 (c : OptimizedProductionChallengeTuple12 K F) : ℕ → K
  | 0 => nprSeed c.1
  | 2 => c.2.1.1
  | 4 => c.2.1.1
  | 5 => c.2.1.2
  | 6 => c.2.2.2.interPole
  | 7 => gamma c.1
  | 8 => c.2.2.2.lambda
  | 9 => c.2.2.2.walkAlpha
  | _ => 0

theorem memoryKOfTuple12_walkAlpha (c : OptimizedProductionChallengeTuple12 K F) :
    memoryKOfTuple12 c 9 = walkAlphaOf c := rfl

theorem memoryKOfTuple12_slot3 (c : OptimizedProductionChallengeTuple12 K F) :
    memoryKOfTuple12 c 3 = 0 := rfl

theorem memoryKOfTuple12_walkGamma (c : OptimizedProductionChallengeTuple12 K F) :
    memoryKOfTuple12 c 7 = gamma c.1 := rfl

/-- Off slots `3` and `9`, the twelve-coin slot map is the landed map at the memory view. -/
theorem memoryKOfTuple12_eq_view (c : OptimizedProductionChallengeTuple12 K F) (q : ℕ)
    (hq : q < 9) (hq3 : q ≠ 3) :
    memoryKOfTuple12 c q = DeployedChipFamily.memoryKOfTuple (walkView11 c) q := by
  interval_cases q <;> first | rfl | exact absurd rfl hq3

/-- Slot `3` of the memory view is `αW`. -/
theorem memoryKOfTuple_view3 (c : OptimizedProductionChallengeTuple12 K F) :
    DeployedChipFamily.memoryKOfTuple (walkView11 c) 3 = walkAlphaOf c := rfl

/-- **Raw `𝔽` challenge vector of the twelve-coin memory chip.**  Slots `6+3·q+k` carry
`coord b (memoryKOfTuple12 c q) k` for `q < 10` — the bound is `j < 36` (was `j < 33`). -/
def memoryChalValOfTuple12 (b : Basis (Fin 3) F K)
    (c : OptimizedProductionChallengeTuple12 K F) : ℕ → F :=
  fun j =>
    if h : 6 ≤ j ∧ j < 36 then
      coord b (memoryKOfTuple12 c ((j - 6) / 3))
        ⟨(j - 6) % 3, Nat.mod_lt _ (by decide)⟩
    else 0

theorem memoryChalValOfTuple12_slot
    (b : Basis (Fin 3) F K) (c : OptimizedProductionChallengeTuple12 K F)
    (q : Fin 10) (k : Fin 3) :
    memoryChalValOfTuple12 b c (6 + 3 * (q : ℕ) + (k : ℕ)) =
      coord b (memoryKOfTuple12 c q) k := by
  have h : 6 ≤ 6 + 3 * (q : ℕ) + (k : ℕ) ∧ 6 + 3 * (q : ℕ) + (k : ℕ) < 36 := by
    have := q.isLt; have := k.isLt; omega
  have hdiv : (6 + 3 * (q : ℕ) + (k : ℕ) - 6) / 3 = (q : ℕ) := by omega
  have hmod : (6 + 3 * (q : ℕ) + (k : ℕ) - 6) % 3 = (k : ℕ) := by omega
  unfold memoryChalValOfTuple12
  rw [dif_pos h, hdiv]
  apply congrArg
  exact Fin.ext hmod

/-- **The raw slot swap** `15..17 ↔ 33..35` (memory `𝕂` slots `3 ↔ 9`). -/
def walkRawSwap (j : ℕ) : ℕ :=
  if 15 ≤ j ∧ j < 18 then j + 18 else if 33 ≤ j ∧ j < 36 then j - 18 else j

/-- The `𝕂`-slot swap `3 ↔ 9`. -/
def walkSlotSwap (i : ℕ) : ℕ := if i = 3 then 9 else if i = 9 then 3 else i

/-- The raw swap is the coordinate expansion of the slot swap (`memoryCol0 = 6 + 3·idx`). -/
theorem walkRawSwap_coord (idx k : ℕ) (hk : k < 3) :
    walkRawSwap (6 + 3 * idx + k) = 6 + 3 * walkSlotSwap idx + k := by
  unfold walkRawSwap walkSlotSwap
  split_ifs <;> omega

omit [DecidableEq K] in
theorem coord_zero (b : Basis (Fin 3) F K) (k : Fin 3) : coord b (0 : K) k = 0 := by
  simp [coord]

/-- **The chalVal transport.**  The twelve-coin memory chalVal read through the slot swap IS the
landed memory chalVal at the memory view: the walk slot `9` lands on the landed walk slot `3`, the
retired slot `3` on the dead raw block `33..35`, every other slot on itself. -/
theorem memoryChalValOfTuple12_swap (b : Basis (Fin 3) F K)
    (c : OptimizedProductionChallengeTuple12 K F) :
    memoryChalValOfTuple12 b c ∘ walkRawSwap =
      DeployedChipFamily.memoryChalValOfTuple b (walkView11 c) := by
  funext j
  simp only [Function.comp_apply]
  unfold walkRawSwap memoryChalValOfTuple12 DeployedChipFamily.memoryChalValOfTuple
  by_cases h1 : 15 ≤ j ∧ j < 18
  · rw [if_pos h1, dif_pos (by omega), dif_pos (by omega)]
    have e1 : memoryKOfTuple12 c ((j + 18 - 6) / 3) =
        DeployedChipFamily.memoryKOfTuple (walkView11 c) ((j - 6) / 3) := by
      rw [show (j + 18 - 6) / 3 = 9 by omega, show (j - 6) / 3 = 3 by omega]; rfl
    exact congrArg₂ (fun x k => coord b x k) e1 (Fin.ext (by simp only; omega))
  · rw [if_neg h1]
    by_cases h2 : 33 ≤ j ∧ j < 36
    · rw [if_pos h2, dif_pos (by omega), dif_neg (by omega)]
      rw [show (j - 18 - 6) / 3 = 3 by omega, memoryKOfTuple12_slot3, coord_zero]
    · rw [if_neg h2]
      by_cases h3 : 6 ≤ j ∧ j < 33
      · rw [dif_pos (by omega), dif_pos h3]
        have hq : (j - 6) / 3 < 9 := by omega
        have hq3 : (j - 6) / 3 ≠ 3 := by omega
        rw [memoryKOfTuple12_eq_view c _ hq hq3]
      · rw [dif_neg (by omega), dif_neg h3]

/-- **Twelve-coin memory publics**: slots `6..8` are the memory walk's `initial_count = αW ^ kMem`; every other slot is the package map -/
def memoryPublicOfTuple12 (b : Basis (Fin 3) F K) (_claim : P8PublicClaim) (kMem : ℕ)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple12 K F) : ℕ → F :=
  fun j =>
    if h : 6 ≤ j ∧ j < 9 then
      coord b (c.2.2.2.walkAlpha ^ kMem) ⟨j - 6, by omega⟩
    else
      pkgPub j

/-- The twelve-coin memory publics are the landed publics at the memory view (`rfl`). -/
theorem memoryPublicOfTuple12_eq_view (b : Basis (Fin 3) F K) (claim : P8PublicClaim) (kMem : ℕ)
    (pkgPub : ℕ → F) (c : OptimizedProductionChallengeTuple12 K F) :
    memoryPublicOfTuple12 b claim kMem pkgPub c =
      DeployedChipFamily.memoryPublicOfTuple b claim kMem pkgPub (walkView11 c) := rfl

end

end Nock.NockVMROM.Thm54.PartA12
