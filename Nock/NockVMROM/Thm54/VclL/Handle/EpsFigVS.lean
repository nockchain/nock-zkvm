/-
  Nock/NockVMROM/Thm54/VclL/Handle/EpsFigVS.lean

  **The claim-leaf bound, `boundVCLH''` in closed form and its figures at VS.**
  Additive.

  * `numH`, `boundVCLH''_eq`, `numH_corner`: the numerator over `|𝕂|⁴` and its monotone corner.
  * `standaloneVS_soundness_le`: probability of the bad event `≤ boundVCLH''` (from `standaloneVS_sound'`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.EpsVS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS

open Nock Nock.Walk Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS Nock.NockVMROM.Thm54.VclL.Handle.ServedVS
open Nock.NockVMROM.Thm54.VclL.Handle.ServedPVS Nock.NockVMROM.Thm54.VclL.Handle.WalkGenVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
open Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkChainSumVS Nock.NockVMROM.Thm54.VclL.Handle.CWalkChipVS
open Nock.NockVMROM.Thm54.VclL.Handle.SoundVS
open Nock.NockVMROM.Thm54.FiniteIO
open scoped Polynomial

open Nock.NockVMROM.Thm54.VclL.Handle.EpsVS Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF)

noncomputable section

/-! ## 1. The claim-leaf bound -/

theorem claimFuel_le_of_leafBoundF (q N : ℕ) (hN : 0 < N) (c : P8PublicClaim) :
    claimFuel c ≤ max fuelChip (leafBoundF q N c) := by
  have h0 : callLeaves q (c.subject, c.formula) ≤ leafBoundF q N c := by
    have hmem : (c.subject, c.formula) ∈ (Finset.range N).biUnion (callsAt q c.subject c.formula) :=
      Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr hN, by simp [callsAt]⟩
    exact (Finset.le_sup (f := callLeaves q) hmem).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hs : c.subject.leaves ≤ leafBoundF q N c := (le_max_left _ _).trans h0
  have hf : c.formula.leaves ≤ leafBoundF q N c :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans h0
  have he := result_le_leafBoundF q N c
  unfold claimFuel
  simp only [max_le_iff]
  exact ⟨le_max_left _ _, le_max_of_le_right hs, le_max_of_le_right hf, le_max_of_le_right he⟩

theorem claimFuel_eq_fuelChip (q N : ℕ) (hN : 0 < N) (c : P8PublicClaim)
    (h : leafBoundF q N c ≤ 2 ^ 110) : claimFuel c = fuelChip :=
  le_antisymm ((claimFuel_le_of_leafBoundF q N hN c).trans (max_le le_rfl (by unfold fuelChip; exact h)))
    (fuelChip_le_claimFuel c)

/-! ## 2. The closed form -/

/-- The numerator over `|𝕂|⁴` (at `|𝕂′| = |𝕂|²`). -/
def numH (c N D W Λ : ℕ) : ℕ :=
  c ^ 3 * (8 * N + 2 + 15 * W) +
  c ^ 2 * (D * (2 * fuelChip - 1) + 1 + pairCount (D + 3) * (2 * Λ - 1) +
    ioFailureUnionBound 5 (3 * N + W) D c + ioFailureUnionBound 5 (2 * N) (2 * W) c) +
  (ioFailureUnionBound 5 (3 + 2 * D) D (c ^ 2) + ioFailureUnionBound 11 W (2 * D) (c ^ 2))

theorem boundVCLH''_eq (c N D W Λ : ℕ) (hc : 0 < c) :
    boundVCLH'' c (c ^ 2) N D W Λ = (numH c N D W Λ : ℚ) / (c : ℚ) ^ 4 := by
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold boundVCLH'' numH
  push_cast
  field_simp
  ring

theorem ioFUB_mono (m c : ℕ) {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    ioFailureUnionBound m a b c ≤ ioFailureUnionBound m a' b' c := by
  unfold ioFailureUnionBound
  gcongr

theorem numH_corner {c N D W N₀ D₀ W₀ : ℕ} (Λ : ℕ) (hN : N ≤ N₀) (hD : D ≤ D₀) (hW : W ≤ W₀) :
    numH c N D W Λ ≤ numH c N₀ D₀ W₀ Λ := by
  have h1 := ioFUB_mono 5 c (a := 3 * N + W) (a' := 3 * N₀ + W₀) (b := D) (b' := D₀) (by omega) hD
  have h2 := ioFUB_mono 5 c (a := 2 * N) (a' := 2 * N₀) (b := 2 * W) (b' := 2 * W₀) (by omega) (by omega)
  have h3 := ioFUB_mono 5 (c ^ 2) (a := 3 + 2 * D) (a' := 3 + 2 * D₀) (b := D) (b' := D₀) (by omega) hD
  have h4 := ioFUB_mono 11 (c ^ 2) (a := W) (a' := W₀) (b := 2 * D) (b' := 2 * D₀) hW (by omega)
  have h5 : pairCount (D + 3) ≤ pairCount (D₀ + 3) := pairCount_mono (by omega)
  unfold numH
  gcongr

/-! ## 3. Soundness with its `ε` -/

section Sound
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)

open Classical in
/-- **Soundness at VS with its `ε`**: probability of the bad event `≤ boundVCLH''`. -/
theorem standaloneVS_soundness_le (hp : 2 ^ 63 < ringChar F) :
    letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
    letI : Algebra (ZMod (ringChar F)) K := zmodAlg
    ∀ (V : VerifierData F K hC (shapeVS hT hP))
      (_ : V.Checks (fun a => (compCoreVS δF hT hP hC (sumCVS hT hP hC)).reqBound V a +
        (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)).internalBound V a)
        (ringChar (Quad (algebraMap F K δF))))
      (msg : MessagesG (compCoreVS δF hT hP hC (sumCVS hT hP hC))
        (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)))
      (_ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) msg.traces),
    ((Finset.univ.filter fun χ : Coins frameVS K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVS K) ≤
      boundVCLH'' (Fintype.card K) (Fintype.card (Quad (algebraMap F K δF))) V.N
        (V.memRows (tCS hT hP)) (V.memRows (tWS hT hP)) (claimFuel V.claim) := by
  letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
  letI : Algebra (ZMod (ringChar F)) K := zmodAlg
  intro V hV msg hst
  exact ((standaloneVS_sound' δF hT hP kr hC hp).soundness V hV msg hst).trans
    (epsilonVS_le δF hT hP kr hC V msg)

end Sound

/-! ## 4. The figures -/

theorem boundVCLH''_lt_of_num {N D W b : ℕ} (h : numH cK N D W fuelChip * 2 ^ b < cK ^ 4) :
    boundVCLH'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ b := by
  rw [boundVCLH''_eq _ _ _ _ _ cK_pos]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ hc (by positivity), one_mul]
  exact_mod_cast h

theorem not_boundVCLH''_le_of_num {N D W b : ℕ} (h : cK ^ 4 < numH cK N D W fuelChip * 2 ^ b) :
    ¬ boundVCLH'' cK (cK ^ 2) N D W fuelChip ≤ 1 / (2 : ℚ) ^ b := by
  rw [boundVCLH''_eq _ _ _ _ _ cK_pos, not_le]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ (by positivity) hc, one_mul]
  exact_mod_cast h

/-- The kernel numerals (generic `c` with `c = p³`, so the kernel never sees `cK`). -/
theorem num_31 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numH c (2 ^ 31) (2 ^ 31) (2 ^ 31) fuelChip * 2 ^ 122 < c ^ 4 := by
  subst hc; unfold numH fuelChip; decide +kernel

theorem num_32 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numH c (2 ^ 32) (2 ^ 32) (2 ^ 32) fuelChip * 2 ^ 120 < c ^ 4 := by
  subst hc; unfold numH fuelChip; decide +kernel

theorem num_k (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numH c (2 ^ 21) (2 ^ 20) (2 ^ 21) fuelChip * 2 ^ 142 < c ^ 4 := by
  subst hc; unfold numH fuelChip; decide +kernel

theorem num_31_not (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numH c (2 ^ 31) (2 ^ 31) (2 ^ 31) fuelChip * 2 ^ 123 := by
  subst hc; unfold numH fuelChip; decide +kernel

theorem num_32_not (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numH c (2 ^ 32) (2 ^ 32) (2 ^ 32) fuelChip * 2 ^ 121 := by
  subst hc; unfold numH fuelChip; decide +kernel

theorem num_k_not (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numH c (2 ^ 21) (2 ^ 20) (2 ^ 21) fuelChip * 2 ^ 143 := by
  subst hc; unfold numH fuelChip; decide +kernel

theorem figVCLH''_two_pow_31 (N D W : ℕ) (hN : N ≤ 2 ^ 31) (hD : D ≤ 2 ^ 31) (hW : W ≤ 2 ^ 31) :
    boundVCLH'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ 122 :=
  boundVCLH''_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numH_corner fuelChip hN hD hW))
    (num_31 cK cK_eq))

theorem figVCLH''_two_pow_32 (N D W : ℕ) (hN : N ≤ 2 ^ 32) (hD : D ≤ 2 ^ 32) (hW : W ≤ 2 ^ 32) :
    boundVCLH'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ 120 :=
  boundVCLH''_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numH_corner fuelChip hN hD hW))
    (num_32 cK cK_eq))

theorem figVCLH''_kernel (N D W : ℕ) (hN : N ≤ 2 ^ 21) (hD : D ≤ 2 ^ 20) (hW : W ≤ 2 ^ 21) :
    boundVCLH'' cK (cK ^ 2) N D W fuelChip < 1 / (2 : ℚ) ^ 142 :=
  boundVCLH''_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numH_corner fuelChip hN hD hW))
    (num_k cK cK_eq))

/-- Tightness (figures, not floors). -/
theorem figVCLH''_not_123 :
    ¬ boundVCLH'' cK (cK ^ 2) (2 ^ 31) (2 ^ 31) (2 ^ 31) fuelChip ≤ 1 / (2 : ℚ) ^ 123 :=
  not_boundVCLH''_le_of_num (num_31_not cK cK_eq)

theorem figVCLH''_not_121_at_32 :
    ¬ boundVCLH'' cK (cK ^ 2) (2 ^ 32) (2 ^ 32) (2 ^ 32) fuelChip ≤ 1 / (2 : ℚ) ^ 121 :=
  not_boundVCLH''_le_of_num (num_32_not cK cK_eq)

theorem figVCLH''_not_143_kernel :
    ¬ boundVCLH'' cK (cK ^ 2) (2 ^ 21) (2 ^ 20) (2 ^ 21) fuelChip ≤ 1 / (2 : ℚ) ^ 143 :=
  not_boundVCLH''_le_of_num (num_k_not cK cK_eq)

theorem hx_alone_not_155 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 2 < ioFailureUnionBound 5 (3 * 2 ^ 31 + 2 ^ 31) (2 ^ 31) c * 2 ^ 155 := by
  subst hc; unfold ioFailureUnionBound; decide +kernel

theorem hx_alone_not_154_at_32 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 2 < ioFailureUnionBound 5 (3 * 2 ^ 32 + 2 ^ 32) (2 ^ 32) c * 2 ^ 154 := by
  subst hc; unfold ioFailureUnionBound; decide +kernel

theorem hx_alone_not_164_kernel (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 2 < ioFailureUnionBound 5 (3 * 2 ^ 21 + 2 ^ 21) (2 ^ 20) c * 2 ^ 164 := by
  subst hc; unfold ioFailureUnionBound; decide +kernel

/-- Every other summand fits 155 at the `2^31` corner (the numerator without the two handle IO
summands, over `|𝕂|⁴`). -/
theorem others_fit_155 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    (numH c (2 ^ 31) (2 ^ 31) (2 ^ 31) fuelChip -
      c ^ 2 * (ioFailureUnionBound 5 (3 * 2 ^ 31 + 2 ^ 31) (2 ^ 31) c +
        ioFailureUnionBound 5 (2 * 2 ^ 31) (2 * 2 ^ 31) c)) * 2 ^ 155 < c ^ 4 := by
  subst hc; unfold numH fuelChip ioFailureUnionBound; decide +kernel

/-! ## 5. The soundness figures -/

section Figs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)

open Classical in
theorem standaloneVS_122 (hp : 2 ^ 63 < ringChar F) :
    letI : Fact (ringChar F).Prime := ⟨prime_of_big hp⟩
    letI : Algebra (ZMod (ringChar F)) K := zmodAlg
    ∀ (V : VerifierData F K hC (shapeVS hT hP))
      (_ : V.Checks (fun a => (compCoreVS δF hT hP hC (sumCVS hT hP hC)).reqBound V a +
        (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)).internalBound V a)
        (ringChar (Quad (algebraMap F K δF))))
      (msg : MessagesG (compCoreVS δF hT hP hC (sumCVS hT hP hC))
        (memCoreVS δF hT hP kr hC (sumMVS δF hT hP kr hC)))
      (_ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) msg.traces)
      (_ : Fintype.card K = cK)
      (_ : V.N ≤ 2 ^ 31) (_ : V.memRows (tCS hT hP) ≤ 2 ^ 31) (_ : V.memRows (tWS hT hP) ≤ 2 ^ 31)
      (_ : leafBoundF (ringChar F) V.N V.claim ≤ 2 ^ 110),
    ((Finset.univ.filter fun χ : Coins frameVS K => AcceptsG V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins frameVS K) < 1 / (2 : ℚ) ^ 122 := by
  intro V hV msg hst hcK hN hD hW hΛ
  refine lt_of_le_of_lt (standaloneVS_soundness_le δF hT hP kr hC hp V hV msg hst) ?_
  rw [hcK, quad_card, hcK, claimFuel_eq_fuelChip _ _ V.hN _ hΛ]
  exact figVCLH''_two_pow_31 _ _ _ hN hD hW

end Figs

end

end Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
