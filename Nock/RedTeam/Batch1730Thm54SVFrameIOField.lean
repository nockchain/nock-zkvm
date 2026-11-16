/-
  Nock/RedTeam/Batch1730Thm54SVFrameIOField.lean

  Production: `P8Core/SVFrame/{WeightedIO (new), MemSoundnessFamily, JointSummands,
  StandaloneGeneric, FibreBound}.lean`.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1730

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.FiniteIO
open Polynomial

/-! ## §A  The IO field -/

/-- `frameVCL` has eleven coins, sampled after `![1,1,0,0,1,1,1,1,0,0,0]`. -/
theorem frameVCL_shape :
    frameVCL.n = 11 ∧ ∀ i : Fin frameVCL.n,
      frameVCL.sampledAfter i = ![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0] i :=
  ⟨rfl, fun _ => rfl⟩

/-- The VCL-L seed coins `z₁, z₂` (slots `2`, `3`) are round 0, and disjoint from the IO coins. -/
theorem frameVCL_seed_round0_disjoint {K Kio : Type} (mk : K → K → Kio)
    (hmk : ∀ a b c d, mk a b = mk c d → a = c ∧ b = d) :
    (∀ i ∈ ({⟨2, by decide⟩, ⟨3, by decide⟩} : Finset (Fin frameVCL.n)),
        frameVCL.sampledAfter i = 0) ∧
      Disjoint ({⟨2, by decide⟩, ⟨3, by decide⟩} : Finset (Fin frameVCL.n)) (ioSpecVCL mk hmk).dep := by
  refine ⟨by decide, ?_⟩
  show Disjoint ({⟨2, by decide⟩, ⟨3, by decide⟩} : Finset (Fin frameVCL.n))
    {ioγVCL.1, ioγVCL.2, ioρVCL.1, ioρVCL.2}
  decide

theorem ioSpec12_dep (K : Type) :
    (ioSpec12 K).dep = {⟨4, by decide⟩, ⟨5, by decide⟩} ∧ (ioSpec12 K).dep.card = 2 :=
  ⟨rfl, by
    show ({⟨4, by decide⟩, ⟨5, by decide⟩} : Finset (Fin frame12.n)).card = 2
    decide⟩

/-- `ioSpecVCL` reads its four coins through `mk` (an illustrative `𝕂 × 𝕂` coordinate map). -/
example : (ioSpecVCL (K := ZMod 5) (Kio := ZMod 5 × ZMod 5) Prod.mk
    (fun a b c d h => by simpa using h)).ioCoins (fun i => (i : ZMod 5)) = ⟨(4, 6), (5, 7)⟩ := rfl

#print axioms Nock.NockVMROM.Thm54.SVFrame.ioSpecVCL_dep_card
#print axioms Nock.NockVMROM.Thm54.SVFrame.ioSpecVCL_round
#print axioms Nock.NockVMROM.Thm54.SVFrame.ioCoins12
#print axioms Nock.NockVMROM.Thm54.SVFrame.ioSummand_mem
#print axioms Nock.NockVMROM.Thm54.SVFrame.ioSummand_mass_ext
#print axioms Nock.NockVMROM.Thm54.SVFrame.ioEventAt_card_le
#print axioms Nock.NockVMROM.Thm54.FiniteIO.ioFUB_sq
#print axioms Nock.NockVMROM.Thm54.FiniteIO.ioFUB_mul
#print axioms frameVCL_shape
#print axioms frameVCL_seed_round0_disjoint
#print axioms ioSpec12_dep
#check @Nock.NockVMROM.Thm54.SVFrame.IOCoinSpec
#check @Nock.NockVMROM.Thm54.SVFrame.ioSummand_mass_ext

/-! ## §B  The weighted LogUp -/

#print axioms Nock.NockVMROM.Thm54.FiniteIO.IOFailureEventW_card_le
#print axioms Nock.NockVMROM.Thm54.FiniteIO.IOLogDerivEventW_card_le
#print axioms Nock.NockVMROM.Thm54.FiniteIO.finiteIO_lookup_sound_weighted
#print axioms Nock.NockVMROM.Thm54.SVFrame.serves_of_weighted_lookup
#print axioms Nock.NockVMROM.Thm54.FiniteIO.partial_fraction_unique
#print axioms Nock.NockVMROM.Thm54.FiniteIO.nearP_count_ne
#check @Nock.NockVMROM.Thm54.FiniteIO.finiteIO_lookup_sound_weighted
#check @Nock.NockVMROM.Thm54.SVFrame.IOFacts
#check @Nock.NockVMROM.Thm54.SVFrame.MemSoundnessFamily.serves

/-! ## §C  Negative control: the consumer count is load-bearing -/

section NC

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The one consumed record, width 1. -/
def rNC : Fin 1 → ZMod 2 := fun _ => 0

/-- Coins `γ = 0`, `ρ = 1`. -/
def coinsNC : IOCoins (ZMod 2) := ⟨0, 1⟩

theorem ioQPW_NC : ioQPW [rNC, rNC] ([] : List ((Fin 1 → ZMod 2) × ZMod 2)) 0 = 0 := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have : ((2 : ℕ) : (ZMod 2)[X]) = 0 := by
      rw [← Polynomial.C_eq_natCast, show ((2 : ℕ) : ZMod 2) = 0 from rfl, Polynomial.C_0]
    exact_mod_cast this
  have hB : denomP (provVals ([] : List ((Fin 1 → ZMod 2) × ZMod 2)) (0 : ZMod 2)) = 1 :=
    Finset.prod_eq_one (fun i _ => Fin.elim0 i)
  have hW : numerPW (provVals ([] : List ((Fin 1 → ZMod 2) × ZMod 2)) (0 : ZMod 2))
      (provWts ([] : List ((Fin 1 → ZMod 2) × ZMod 2))) = 0 :=
    Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
  rw [ioQPW, hB, hW, mul_one, zero_mul, sub_zero]
  show (∑ i : Fin 2, ∏ i' ∈ Finset.univ.erase i, (X + C (consVals [rNC, rNC] (0 : ZMod 2) i'))) = 0
  have hv : ∀ i : Fin 2, consVals [rNC, rNC] (0 : ZMod 2) i = 0 := by
    intro i; fin_cases i <;> simp [consVals, Walk.rlc, rNC]
  simp only [hv, map_zero, add_zero]
  rw [Fin.sum_univ_two]
  simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  rw [← two_mul, h2, zero_mul]

/-- **The NC.**  Every hypothesis of `finiteIO_lookup_sound_weighted` except the consumer count holds
(`#consumers = 2 = p`), and the consumed record is NOT provided: the count bound cannot be dropped. -/
theorem lookup_needs_count_bound :
    (∀ r ∈ [rNC, rNC], compress coinsNC r ≠ 0) ∧
    (([rNC, rNC].map fun r => (compress coinsNC r)⁻¹).sum =
      (([] : List ((Fin 1 → ZMod 2) × ZMod 2)).map fun q => q.2 * (compress coinsNC q.1)⁻¹).sum) ∧
    coinsNC.gamma ∉ IORLCCollisionEvent (recordsW [rNC, rNC] ([] : List ((Fin 1 → ZMod 2) × ZMod 2))) ∧
    coinsNC.pole ∉ IOLogDerivEventW [rNC, rNC] ([] : List ((Fin 1 → ZMod 2) × ZMod 2)) coinsNC.gamma ∧
    [rNC, rNC].length = 2 ∧
    rNC ∉ ([] : List ((Fin 1 → ZMod 2) × ZMod 2)).map Prod.fst := by
  have hc : compress coinsNC rNC = 1 := by
    simp [compress, coinsNC, Walk.rlc, rNC]
  refine ⟨?_, ?_, ?_, ?_, rfl, by simp⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hr
    rw [hr, hc]; exact one_ne_zero
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hc, inv_one]
    decide
  · intro h
    simp only [IORLCCollisionEvent, recordsW, Finset.mem_filter, Finset.mem_univ, true_and,
      List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, or_self] at h
    obtain ⟨u, hu, v, hv, hne, -⟩ := h
    exact hne (hu.trans hv.symm)
  · intro h
    simp only [IOLogDerivEventW, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h.1 (by simpa [coinsNC] using ioQPW_NC)

end NC

#print axioms ioQPW_NC
#print axioms lookup_needs_count_bound

/-! ## §D  The statement at the amended frame -/

#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_generic
#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_generic_at
#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_fixed
#print axioms Nock.NockVMROM.Thm54.SVFrame.ctxW_of_accepts
#print axioms Nock.NockVMROM.Thm54.SVFrame.holdsF_of_accepts
#check @Nock.NockVMROM.Thm54.SVFrame.standalone_generic
#check @Nock.NockVMROM.Thm54.SVFrame.ExtraPremises

end Nock.RedTeam.Batch1730
