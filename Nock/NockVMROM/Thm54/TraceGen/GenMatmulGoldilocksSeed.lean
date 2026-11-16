/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulGoldilocksSeed.lean

  **SeedGood / hbad / hout at `φ(7^(2^32−1))`.**

  Dyck is computed in `ZMod p` and transported by `encC_dyck_algebraMap`.
  No `decide` at `GaloisField`.  `hout` is the order argument
  (`sizeWindowFailureSeeds_subset_lowOrderRootSeeds`):
  `orderOf seedZ = 2^32 > 568` and `> 2048`.

  Ruled out (not implemented): SubISA OP7/OP9; `decide` at an
  extension field; `hconf` as a sixth binder of `nockCompiles`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSeed
import Nock.NockVMROM.Thm54.TraceGen.GenSeedGoodInstance
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensusWindow
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.GoldilocksOrbit
open Nock.NockVMROM.Thm54.SizeWindowCounting
open ComputeTable
open Polynomial

/-! ## Order kernels used by small Dyck facts (base field, then transport) -/

theorem goldilocksSeedBase_pow_two_ne_neg_one :
    goldilocksSeedBase ^ 2 ≠ (-1 : F) := by
  intro h
  have h4 : goldilocksSeedBase ^ 4 = 1 := by
    calc
      goldilocksSeedBase ^ 4 = (goldilocksSeedBase ^ 2) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [h]
      _ = 1 := by ring
  have hdvd : orderOf goldilocksSeedBase ∣ 4 :=
    orderOf_dvd_of_pow_eq_one h4
  have hord := goldilocksSeedBase_order
  have : 2 ^ 32 ∣ 4 := by simpa [hord] using hdvd
  exact (by decide : ¬ 2 ^ 32 ∣ 4) this

theorem one_add_seedBase_sq_ne : (1 + goldilocksSeedBase ^ 2 : F) ≠ 0 := by
  intro h
  exact goldilocksSeedBase_pow_two_ne_neg_one (eq_neg_of_add_eq_zero_right h)

theorem one_add_seedZ_sq_ne : (1 + seedZ ^ 2 : K) ≠ 0 := by
  intro h
  have hF : (1 + goldilocksSeedBase ^ 2 : F) = 0 :=
    φ_injective (by simpa [seedZ, map_add, map_one, map_pow] using h)
  exact one_add_seedBase_sq_ne hF

theorem op4_op0_dyck (ax : ℕ) :
    (encC seedZ (op4 (op0 ax))).dyck ≠ 0 := by
  rw [op4, op0]
  have h := encC_cell_atom_dyck seedZ seedZ_ne_zero 4
    (.cell (.atom 0) (.atom ax))
  rw [h, encC_cell_atom_atom_dyck seedZ seedZ_ne_zero 0 ax]
  exact mul_ne_zero seedZ_ne_zero (by simpa [pow_two] using one_add_seedZ_sq_ne)

theorem op0_dyck (ax : ℕ) : (encC seedZ (op0 ax)).dyck ≠ 0 :=
  encC_cell_atom_atom_dyck_ne seedZ seedZ_ne_zero 0 ax

theorem op0_2_dyck : (encC seedZ (op0 2)).dyck ≠ 0 :=
  op0_dyck 2

theorem op1_0_dyck : (encC seedZ (op1 0)).dyck ≠ 0 :=
  encC_cell_atom_atom_dyck_ne seedZ seedZ_ne_zero 1 0

theorem encC_zero_ne_one :
    encC seedZ (.atom 0) ≠ encC seedZ (.atom 1) :=
  encC_atom_ne seedZ 0 1 (by simp [Nat.cast_zero, Nat.cast_one])

theorem cell_op1_0_dyck :
    (encC seedZ (.cell (.atom 1) (.atom 0))).dyck ≠ 0 := by
  simpa [op1] using op1_0_dyck

theorem cell_op0_dyck (ax : ℕ) :
    (encC seedZ (.cell (.atom 0) (.atom ax))).dyck ≠ 0 := by
  simpa [op0] using op0_dyck ax

/-! ## Reduce `7^(2^32−1)` in `𝔽_p` (32 square-and-muls, then `decide`)

`decide` cannot unfold `7 ^ (2^32−1)` through the linear monoid `pow`.
MSB-first square-and-mul on the 32 ones of `2^32−1` is kernel-small. -/

theorem foldl_sqmul_seven (a : F) (k : ℕ) :
    (List.replicate k ()).foldl (fun acc _ => acc * acc * (7 : F)) a =
      a ^ (2 ^ k) * (7 : F) ^ (2 ^ k - 1) := by
  induction k generalizing a with
  | zero =>
      simp [pow_zero, pow_one]
  | succ k ih =>
      rw [List.replicate_succ, List.foldl_cons, ih]
      have h1 : (a * a * 7) ^ (2 ^ k) = a ^ (2 ^ (k + 1)) * (7 : F) ^ (2 ^ k) := by
        have ha : a * a = a ^ 2 := (pow_two a).symm
        rw [ha, mul_pow, ← pow_mul]
        have hexp : 2 * 2 ^ k = 2 ^ (k + 1) := by omega
        rw [hexp]
      have h2 : (7 : F) ^ (2 ^ k) * 7 ^ (2 ^ k - 1) = 7 ^ (2 ^ (k + 1) - 1) := by
        rw [← pow_add]
        congr 1
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
      rw [h1, mul_assoc, h2]

theorem goldilocksSeedBase_eq_fold :
    goldilocksSeedBase =
      (List.replicate 32 ()).foldl (fun acc _ => acc * acc * (7 : F)) 1 := by
  unfold goldilocksSeedBase
  have h := foldl_sqmul_seven (1 : F) 32
  rw [h, one_pow, one_mul]

/-- Concrete residue `7^(2^32−1) mod p`.  Arithmetic stays in `ZMod p`. -/
theorem goldilocksSeedBase_val :
    goldilocksSeedBase = (1753635133440165772 : F) := by
  rw [goldilocksSeedBase_eq_fold]
  decide

/-! ## `AllCellDyckNe` at the reduced residue, then transport.

`decide` runs in `ZMod p`, never in `GaloisField`. -/

set_option maxRecDepth 200000

theorem addFromMac_allCellDyckNe_base :
    AllCellDyckNe goldilocksSeedBase addFromMac := by
  rw [goldilocksSeedBase_val]
  decide

theorem quote_mmBattery_allCellDyckNe_base :
    AllCellDyckNe goldilocksSeedBase (quote mmBattery) := by
  rw [goldilocksSeedBase_val]
  decide

theorem mmC00_allCellDyckNe_base :
    AllCellDyckNe goldilocksSeedBase mmC00 := by
  rw [goldilocksSeedBase_val]
  decide

theorem mmC01_allCellDyckNe_base :
    AllCellDyckNe goldilocksSeedBase mmC01 := by
  rw [goldilocksSeedBase_val]
  decide

theorem mmC10_allCellDyckNe_base :
    AllCellDyckNe goldilocksSeedBase mmC10 := by
  rw [goldilocksSeedBase_val]
  decide

theorem mmC11_allCellDyckNe_base :
    AllCellDyckNe goldilocksSeedBase mmC11 := by
  rw [goldilocksSeedBase_val]
  decide

theorem mmFormula_allCellDyckNe_base :
    AllCellDyckNe goldilocksSeedBase mmFormula := by
  rw [goldilocksSeedBase_val]
  decide

theorem addFromMac_allCellDyckNe : AllCellDyckNe seedZ addFromMac :=
  allCellDyckNe_algebraMap φ_injective addFromMac_allCellDyckNe_base

theorem quote_mmBattery_allCellDyckNe :
    AllCellDyckNe seedZ (quote mmBattery) :=
  allCellDyckNe_algebraMap φ_injective quote_mmBattery_allCellDyckNe_base

theorem mmC00_allCellDyckNe : AllCellDyckNe seedZ mmC00 :=
  allCellDyckNe_algebraMap φ_injective mmC00_allCellDyckNe_base

theorem mmC01_allCellDyckNe : AllCellDyckNe seedZ mmC01 :=
  allCellDyckNe_algebraMap φ_injective mmC01_allCellDyckNe_base

theorem mmC10_allCellDyckNe : AllCellDyckNe seedZ mmC10 :=
  allCellDyckNe_algebraMap φ_injective mmC10_allCellDyckNe_base

theorem mmC11_allCellDyckNe : AllCellDyckNe seedZ mmC11 :=
  allCellDyckNe_algebraMap φ_injective mmC11_allCellDyckNe_base

theorem mmFormula_allCellDyckNe : AllCellDyckNe seedZ mmFormula :=
  allCellDyckNe_algebraMap φ_injective mmFormula_allCellDyckNe_base

theorem addFromMac_dyck : (encC seedZ addFromMac).dyck ≠ 0 :=
  addFromMac_allCellDyckNe.1

theorem quote_mmBattery_dyck : (encC seedZ (quote mmBattery)).dyck ≠ 0 :=
  quote_mmBattery_allCellDyckNe.1

theorem mmC00_dyck : (encC seedZ mmC00).dyck ≠ 0 := mmC00_allCellDyckNe.1
theorem mmC01_dyck : (encC seedZ mmC01).dyck ≠ 0 := mmC01_allCellDyckNe.1
theorem mmC10_dyck : (encC seedZ mmC10).dyck ≠ 0 := mmC10_allCellDyckNe.1
theorem mmC11_dyck : (encC seedZ mmC11).dyck ≠ 0 := mmC11_allCellDyckNe.1

theorem mmFormula_left_dyck :
    (encC seedZ (.cell mmC00 mmC01)).dyck ≠ 0 :=
  (allCellDyckNe_left mmFormula_allCellDyckNe).1

theorem mmFormula_right_dyck :
    (encC seedZ (.cell mmC10 mmC11)).dyck ≠ 0 :=
  (allCellDyckNe_right mmFormula_allCellDyckNe).1

theorem seedOK_addArm_one_seed (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      .ok (t, .atom (acc + 1))) :
    SeedOK seedZ t :=
  seedOK_addArm_one seedZ n acc h
    (op4_op0_dyck 6) (op4_op0_dyck 14) op0_2_dyck encC_zero_ne_one

theorem seedOK_macArm_one_m0_seed (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = .ok (t, .atom acc)) :
    SeedOK seedZ t :=
  seedOK_macArm_one_m0 seedZ n acc h
    (op0_dyck 5) (op0_dyck 6) op1_0_dyck (op4_op0_dyck 14)
    op0_2_dyck encC_zero_ne_one addFromMac_dyck (op0_dyck 30)

theorem seedOK_macArm_one_m1_seed (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      .ok (t, .atom (acc + 1))) :
    SeedOK seedZ t :=
  seedOK_macArm_one_m1 seedZ n acc h
    (op0_dyck 5) (op0_dyck 6) op1_0_dyck (op4_op0_dyck 6) (op4_op0_dyck 14)
    op0_2_dyck encC_zero_ne_one addFromMac_dyck (op0_dyck 30)

theorem mac2_inner_all {accF nF mF nF' mF' : Noun}
    (h : AllCellDyckNe seedZ (mac2 accF nF mF nF' mF')) :
    AllCellDyckNe seedZ (invokeMac accF nF mF) := by
  have hcell : AllCellDyckNe seedZ
      (.cell (.atom 7)
        (.cell (.cell (quote mmBattery)
          (.cell (invokeMac accF nF mF)
            (.cell (op1 0) (.cell nF' mF'))))
          (invokeAxis 4))) := by
    simpa [mac2, invokeMac, slam, op7, quote, op1] using h
  exact allCellDyckNe_left (allCellDyckNe_right (allCellDyckNe_left
    (allCellDyckNe_right hcell)))

theorem invokeMac_dyck (accF nF mF : Noun)
    (h : AllCellDyckNe seedZ (invokeMac accF nF mF)) :
    (encC seedZ (invokeMac accF nF mF)).dyck ≠ 0 := by
  simpa [invokeMac, slam, op7] using
    allCellDyckNe_cell (by simpa [invokeMac, slam, op7] using h)

theorem mmC00_inner_dyck :
    (encC seedZ (invokeMac (op1 0) (op0 8) (op0 12))).dyck ≠ 0 :=
  invokeMac_dyck _ _ _ (mac2_inner_all (by simpa [mmC00] using mmC00_allCellDyckNe))
theorem mmC01_inner_dyck :
    (encC seedZ (invokeMac (op1 0) (op0 8) (op0 13))).dyck ≠ 0 :=
  invokeMac_dyck _ _ _ (mac2_inner_all (by simpa [mmC01] using mmC01_allCellDyckNe))
theorem mmC10_inner_dyck :
    (encC seedZ (invokeMac (op1 0) (op0 10) (op0 12))).dyck ≠ 0 :=
  invokeMac_dyck _ _ _ (mac2_inner_all (by simpa [mmC10] using mmC10_allCellDyckNe))
theorem mmC11_inner_dyck :
    (encC seedZ (invokeMac (op1 0) (op0 10) (op0 13))).dyck ≠ 0 :=
  invokeMac_dyck _ _ _ (mac2_inner_all (by simpa [mmC11] using mmC11_allCellDyckNe))

theorem seedOK_mmC00 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC00 =
      .ok (t, .atom 2)) :
    SeedOK seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA⟩ := gen_macArm_one_m1 (K := K) (n + 20) 0
  have ihInnerArm := seedOK_macArm_one_m1_seed (n + 20) 0 innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 12) ha0 a00 b00 innerA
  have ihInner := seedOK_gen_invokeMac (z := seedZ) ha0 a00 b00 innerA hinner
    (seedOK_gen_op1 (z := seedZ) ha0)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot8 a00)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot12 b00)
    ihInnerArm cell_op1_0_dyck (cell_op0_dyck 8) op1_0_dyck quote_mmBattery_dyck
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 1
  have ihOuterArm := seedOK_macArm_one_m1_seed (n + 23) 1 outerA
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 14)
    hinner' a01 b10 outerA
  have hh := h
  simp only [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact seedOK_gen_invokeMac (z := seedZ) hinner' a01 b10 outerA houter
    ihInner
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot9 a01)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot14 b10)
    ihOuterArm
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using mmC00_inner_dyck)
    (cell_op0_dyck 9) op1_0_dyck quote_mmBattery_dyck

theorem seedOK_mmC01 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC01 =
      .ok (t, .atom 1)) :
    SeedOK seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA⟩ := gen_macArm_one_m0 (K := K) (n + 29) 0
  have ihInnerArm := seedOK_macArm_one_m0_seed (n + 29) 0 innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 13) ha0 a00 b01 innerA
  have ihInner := seedOK_gen_invokeMac (z := seedZ) ha0 a00 b01 innerA hinner
    (seedOK_gen_op1 (z := seedZ) ha0)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot8 a00)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot13 b01)
    ihInnerArm cell_op1_0_dyck (cell_op0_dyck 8) op1_0_dyck quote_mmBattery_dyck
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := seedOK_macArm_one_m1_seed (n + 23) 0 outerA
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 15)
    hinner' a01 b11 outerA
  have hh := h
  simp only [mmC01, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact seedOK_gen_invokeMac (z := seedZ) hinner' a01 b11 outerA houter
    ihInner
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot9 a01)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot15 b11)
    ihOuterArm
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using mmC01_inner_dyck)
    (cell_op0_dyck 9) op1_0_dyck quote_mmBattery_dyck

theorem seedOK_mmC10 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC10 =
      .ok (t, .atom 1)) :
    SeedOK seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA⟩ := gen_macArm_zero (K := K) (n + 45) (.atom 0) (.atom 1)
  have ihInnerArm := seedOK_macArm_zero seedZ (n + 45) (.atom 0) (.atom 1) innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 12) ha0 a10 b00 innerA
  have ihInner := seedOK_gen_invokeMac (z := seedZ) ha0 a10 b00 innerA hinner
    (seedOK_gen_op1 (z := seedZ) ha0)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot10 a10)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot12 b00)
    ihInnerArm cell_op1_0_dyck (cell_op0_dyck 10) op1_0_dyck quote_mmBattery_dyck
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := seedOK_macArm_one_m1_seed (n + 23) 0 outerA
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 14)
    hinner' a11 b10 outerA
  have hh := h
  simp only [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact seedOK_gen_invokeMac (z := seedZ) hinner' a11 b10 outerA houter
    ihInner
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot11 a11)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot14 b10)
    ihOuterArm
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using mmC10_inner_dyck)
    (cell_op0_dyck 11) op1_0_dyck quote_mmBattery_dyck

theorem seedOK_mmC11 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC11 =
      .ok (t, .atom 1)) :
    SeedOK seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA⟩ := gen_macArm_zero (K := K) (n + 45) (.atom 0) (.atom 0)
  have ihInnerArm := seedOK_macArm_zero seedZ (n + 45) (.atom 0) (.atom 0) innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 13) ha0 a10 b01 innerA
  have ihInner := seedOK_gen_invokeMac (z := seedZ) ha0 a10 b01 innerA hinner
    (seedOK_gen_op1 (z := seedZ) ha0)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot10 a10)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot13 b01)
    ihInnerArm cell_op1_0_dyck (cell_op0_dyck 10) op1_0_dyck quote_mmBattery_dyck
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := seedOK_macArm_one_m1_seed (n + 23) 0 outerA
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 15)
    hinner' a11 b11 outerA
  have hh := h
  simp only [mmC11, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact seedOK_gen_invokeMac (z := seedZ) hinner' a11 b11 outerA houter
    ihInner
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot11 a11)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot15 b11)
    ihOuterArm
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using mmC11_inner_dyck)
    (cell_op0_dyck 11) op1_0_dyck quote_mmBattery_dyck

theorem seedOK_mm {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) 64 mmSubject mmFormula = .ok (t, mmC)) :
    SeedOK seedZ t := by
  obtain ⟨t00, h00⟩ := gen_mmC00 (K := K) 6
  obtain ⟨t01, h01⟩ := gen_mmC01 (K := K) 6
  obtain ⟨t10, h10⟩ := gen_mmC10 (K := K) 6
  obtain ⟨t11, h11⟩ := gen_mmC11 (K := K) 6
  have ih00 := seedOK_mmC00 6 h00
  have ih01 := seedOK_mmC01 6 h01
  have ih10 := seedOK_mmC10 6 h10
  have ih11 := seedOK_mmC11 6 h11
  have h00c := h00
  simp only [mmC00, mac2, invokeMac, slam, op7, quote, op1] at h00c
  have h01c := h01
  simp only [mmC01, mac2, invokeMac, slam, op7, quote, op1] at h01c
  have h10c := h10
  simp only [mmC10, mac2, invokeMac, slam, op7, quote, op1] at h10c
  have h11c := h11
  simp only [mmC11, mac2, invokeMac, slam, op7, quote, op1] at h11c
  have hL := gen_cons (K := K) 62 h00c h01c
  have hR := gen_cons (K := K) 62 h10c h11c
  have hop := gen_cons (K := K) 63 hL hR
  have hh := h
  simp only [mmFormula, mmC00, mmC01, mmC10, mmC11, mac2, invokeMac, slam, op7,
    quote, op1, op0] at hh
  have huniq := gen_ok_unique hh hop
  rw [huniq.1]
  exact seedOK_gen_cons (z := seedZ) hL hR hop
    (seedOK_gen_cons (z := seedZ) h00c h01c hL ih00 ih01
      (by simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] using mmC00_dyck))
    (seedOK_gen_cons (z := seedZ) h10c h11c hR ih10 ih11
      (by simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] using mmC10_dyck))
    (by simpa [mmC00, mmC01, mac2, invokeMac, slam, op7, quote, op1, op0]
      using mmFormula_left_dyck)

theorem mmTree_seedOK : SeedOK seedZ (mmTree (K := K)) :=
  seedOK_mm (mmTree_gen (K := K))

theorem mmTree_seedGood : SeedGood seedZ (mmTree (K := K)) :=
  seedGood_of_seedOK mmTree_seedOK

/-! ## `hout` — seed order above `Λ`

`sizeWindowFailureSeeds ⊆ lowOrderRootSeeds Λ`, and every element of
the latter has `orderOf ≤ Λ`.  `orderOf seedZ = 2^32`. -/

variable [Fintype K] [DecidableEq K]

set_option linter.unusedSectionVars false

theorem not_mem_lowOrderRootSeeds_of_order {z : K} {Λ : ℕ}
    (hord : Λ < orderOf z) :
    z ∉ lowOrderRootSeeds (K := K) Λ := by
  intro h
  rw [lowOrderRootSeeds, Finset.mem_biUnion] at h
  obtain ⟨d, hd, hroot⟩ := h
  have hd' := Finset.mem_Icc.mp hd
  have hpos : 0 < d := hd'.1
  rw [mem_nthRootsFinset hpos] at hroot
  have : orderOf z ∣ d := orderOf_dvd_of_pow_eq_one hroot
  have hle : orderOf z ≤ d := Nat.le_of_dvd hpos this
  exact (not_le_of_gt hord) (hle.trans hd'.2)

theorem mm_sizeWindowBound :
    SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (mmTree (K := K))))
        (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (mmTree (K := K))))
      568 :=
  genComputeSkeleton_sizeWindowBound_gen (by decide : 1 ≤ 568)
    (mmTree_gen (K := K)) mm_traceConfined _

theorem seedZ_not_lowOrder (Λ : ℕ) (hΛ : Λ < 2 ^ 32) :
    seedZ ∉ lowOrderRootSeeds (K := K) Λ :=
  not_mem_lowOrderRootSeeds_of_order (seedZ_order_gt Λ hΛ)

/-- `hout` at the program-text window.  No new failure-event summand. -/
theorem mm_hout :
    seedZ ∉ sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder (mmTree (K := K))))
        (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (mmTree (K := K)))) := by
  intro h
  exact seedZ_not_lowOrder 568 (by decide : 568 < 2 ^ 32)
    (sizeWindowFailureSeeds_subset_lowOrderRootSeeds _ 568 mm_sizeWindowBound h)

theorem mm_hout_2048 :
    seedZ ∉ sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder (mmTree (K := K))))
        (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (mmTree (K := K)))) :=
  mm_hout

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks

#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.mm_hout
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.mmTree_seedGood
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.goldilocksSeedBase_val
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.one_add_seedZ_sq_ne
