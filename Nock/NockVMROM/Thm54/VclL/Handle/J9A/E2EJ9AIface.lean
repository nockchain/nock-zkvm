/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/E2EJ9AIface.lean

  **J-9 A e2e interface N1-N3**. -/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ProbJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5 (R0d L0d)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV (layLe_ofG)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7 c11 c12 c15 c16 c2 c3 liftJ8 embJ8 yDep sumJ8 orderJ8 ioSummandJ8 atomDyckJ8 atomCensusJ8 zeroYJ8 bivJ8 specV specH specZY)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (sumJ8C allJ8C DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (sum40 Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (allJ8X atomFpxJ8 withFpxV DataJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (PubJ9A MsgJ9A' TrJ9A StJ9A RowsJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AcceptsJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface (OneRoundCD OneRoundJ8 oneRoundJ8_of_cd oneRoundCD_lift
  cd_spec1314 cd_specVQ cd_specHQ cd_spec01 cj_specV cj_specH_y cj_specH cj_specZY cj_spec01 cj_y)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ9A (XA9Z soundA_absent soundA_present hA3A hcapA hgA)
open Nock.NockVMROM.Thm54.VclL.Handle.Out40J9A (XA9 cw9A)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A (sum40A withLiftCA CW9)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ9A} {g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem twinFact : Fact (ringChar (ZMod p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
@[reducible] def twinAlg : Algebra (ZMod (ringChar (ZMod p))) K :=
  @Eq.rec ℕ p (fun q _ => Algebra (ZMod q) K) ‹Algebra (ZMod p) K› _ (ZMod.ringChar_zmod_n p).symm
attribute [local instance] twinFact twinAlg

open Classical in
/-- **The J-9 A summand list**: `allJ8X` of the absent data (`XA9Z`, as `probJ9A_absent`) if `Pb.krootsV = 0`, else of
the present data (`XA9`, as `probJ9A_present`). -/
noncomputable def listJ9A (Pb : PubJ9A p) (c : P8PublicClaim) (r : RowsJ9A) (g : ℕ)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9 : (censusG Pb.toPubJ8 c).length + 6 ≤ 2 ^ 31) :
    List (BadSummand frameJ8 K (TrJ9A (ZMod p)) StJ9A) :=
  if Pb.krootsV = 0 then
    allJ8X
      (XA9Z δ b (g := g + r.N + r.AX) (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
        (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb c [] (by simp)
        (layLe_ofG (r := RR49A.rowsB r) Pb.toPubJ8 hLC hLM hLW hLA hLV) rfl hnM hreg9 Pb.axOn Pb.spOn hLC)
  else
    allJ8X
      (XA9 δ b (g := g + r.N + r.AX) (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
        (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb c [] (by simp)
        (layLe_ofG (r := RR49A.rowsB r) Pb.toPubJ8 hLC hLM hLW hLA hLV) rfl hnM hreg9 Pb.axOn Pb.spOn hLC)

open Classical in
/-- **N2**: `ε` of the list `< 2^-155`. -/
theorem epsilonOf_listJ9A (Pb : PubJ9A p) (c : P8PublicClaim) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9 : (censusG Pb.toPubJ8 c).length + 6 ≤ 2 ^ 31) :
    epsilonOf (listJ9A δ b Pb c r g hLC hLM hLW hLA hLV hnM hreg9) < 1 / (2 : ℚ) ^ 155 := by
  unfold listJ9A
  split_ifs
  · exact RR49A.epsJ8X_lt_155_optB _ hcK (RR49A.rowsB_le hr hAX hSP) (le_refl _) (ProbJ9A.hgA hr hAX hg)
  · exact RR49A.epsJ8X_lt_155_optB _ hcK (RR49A.rowsB_le hr hAX hSP) (le_refl _) (ProbJ9A.hgA hr hAX hg)

open Classical in
/-- **N1**: pointwise soundness of `AcceptsJ9A` outside the summands of `listJ9A`. -/
theorem soundJ9A_pointwise [CharP K p] [CharP 𝕂′ p] (Pb : PubJ9A p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (hpG : p = Nock.Atoms.p)
    (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9 : (censusG Pb.toPubJ8 c).length + 6 ≤ 2 ^ 31)
    (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p))
    (hM : AcceptsJ9A δ b Pb Rg c χ M tr r g)
    (hout : ∀ s ∈ listJ9A δ b Pb c r g hLC hLM hLW hLA hLV hnM hreg9, ¬ s.mem tr χ) :
    Nock.Jet.HoldsN c := by
  unfold listJ9A at hout
  by_cases h0 : Pb.krootsV = 0
  · rw [if_pos h0] at hout
    exact soundA_absent δ b hRg hM h0 _ _ [] (by simp) _ rfl hnM hreg9 hLC hout hpG hqM hk hmax
      (hA3A hr hpG) (hcapA hr hAX hg hpG)
  · rw [if_neg h0] at hout
    have hpos : 1 ≤ Pb.krootsV := Nat.pos_of_ne_zero h0
    have hΛ : fuelChip ≤ (RR49A.rowsB r).Λ := by
      show fuelChip ≤ r.Λ
      rw [hr.2.2.2.1]; exact le_refl _
    exact soundA_present δ b hRg hM hpos _ _ [] (by simp) _ rfl hnM hreg9 hLC hout hpG hqM hk hmax
      (hA3A hr hpG) hΛ (hcapA hr hAX hg hpG)

/-! ## N3. One round per summand -/

section OneRound
variable {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop}

open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (specVQ specHQ spec01 spec1314 v2 v3 v4 v5 v6 v7 v11 v12 v13 v14 v0 v1)

open Classical in
/-- The ten summands of `sum40A L C` are one-round (lifted to `frameJ8`). -/
theorem oneRound_sum40A {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K] {r' : RowsJ8}
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r') (C : CW9 (K := K) Tr St r') (hπ) :
    ∀ s ∈ sum40A L C, OneRoundJ8 (liftJ8 s (id : Tr → Tr) hπ : BadSummand frameJ8 K Tr St) := by
  intro s hs
  apply oneRoundCD_lift
  simp only [sum40A, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cd_spec1314 (K := K)
  · exact (by decide : OneRoundCD frameVSQ ({Lift40J8.v13} : Finset (Fin frameVSQ.n)) ∅)
  · exact (by decide : OneRoundCD frameVSQ ({Lift40J8.v2, Lift40J8.v3} : Finset (Fin frameVSQ.n)) ∅)
  · exact cd_spec01 (K := K)
  · exact cd_specVQ (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _)
  · exact (by decide : OneRoundCD frameVSQ ({Lift40J8.v2, Lift40J8.v3} : Finset (Fin frameVSQ.n)) ∅)
  · exact (by decide : OneRoundCD frameVSQ ({Lift40J8.v2, Lift40J8.v3} : Finset (Fin frameVSQ.n)) ∅)
  · exact cd_specVQ (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _)
  · exact cd_specHQ (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _)
  · exact cd_specHQ (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _)

open Classical in
/-- **N3 generic**: every summand of `allJ8X X` is one-round, given the 40th's class is. -/
theorem oneRound_allJ8X_gen {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K] {P g' : ℕ} {r' : RowsJ8}
    (X : DataJ8X (q := q) (algebraMap (ZMod p) K δ) Tr St r' P g')
    (h40 : ∀ s ∈ sumJ8C X.C .fortieth, OneRoundJ8 s) :
    ∀ s ∈ allJ8X X, OneRoundJ8 s := by
  intro s hs
  rw [allJ8X, List.mem_append] at hs
  rcases hs with hs | hs
  · rw [allJ8C, List.mem_flatMap] at hs
    obtain ⟨m, -, hs⟩ := hs
    cases m
    · exact h40 s hs
    · replace hs := List.mem_singleton.1 hs; subst hs
      exact oneRoundJ8_of_cd (cj_specV (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _))
    · replace hs := List.mem_singleton.1 hs; subst hs
      exact oneRoundJ8_of_cd (cj_specV (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _))
    · replace hs := List.mem_singleton.1 hs; subst hs
      exact oneRoundJ8_of_cd (cj_specH_y (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _))
    · replace hs := List.mem_singleton.1 hs; subst hs
      exact oneRoundJ8_of_cd (cj_specH (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _))
    · replace hs := List.mem_singleton.1 hs; subst hs
      exact oneRoundJ8_of_cd (cj_specH (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _))
    · simp only [sumJ8C, sumJ8, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl <;> exact oneRoundJ8_of_cd cj_y
    · replace hs := List.mem_singleton.1 hs; subst hs
      exact oneRoundJ8_of_cd (cj_spec01 (K := K))
    · replace hs := List.mem_singleton.1 hs; subst hs
      exact oneRoundJ8_of_cd (cj_specZY (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _))
  · replace hs := List.mem_singleton.1 hs; subst hs
    exact oneRoundJ8_of_cd (cj_specV (K := K) (Kio := 𝕂′) (mk := Quad.mk (algebraMap (ZMod p) K δ)) (hmk := Chips.quadMk_inj _))

open Classical in
/-- The 40th's class of a `withLiftCA` datum is one-round. -/
theorem oneRound_fortieth_withLiftCA {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K] {P g' : ℕ} {r' : RowsJ8}
    (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r' P g')
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r') (C : CW9 (K := K) Tr St r') :
    ∀ s ∈ sumJ8C (withLiftCA R L C) .fortieth, OneRoundJ8 s := by
  intro s hs
  simp only [sumJ8C, sumJ8, withLiftCA, Lift40J9A.withLiftA, List.mem_map] at hs
  obtain ⟨s', hs', rfl⟩ := hs
  exact oneRound_sum40A δ L C _ s' hs'

end OneRound

open Classical in
/-- **N3 at `listJ9A`**: every summand is one-round (`OneRoundCD frameJ8 s.coins s.dep`), in both branches. -/
theorem oneRound_listJ9A (Pb : PubJ9A p) (c : P8PublicClaim) (r : RowsJ9A) (g : ℕ)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9 : (censusG Pb.toPubJ8 c).length + 6 ≤ 2 ^ 31) :
    ∀ s ∈ listJ9A δ b Pb c r g hLC hLM hLW hLA hLV hnM hreg9, OneRoundCD frameJ8 s.coins s.dep := by
  intro s hs
  have key : OneRoundJ8 s := by
    unfold listJ9A at hs
    split_ifs at hs
    · exact oneRound_allJ8X_gen δ _ (oneRound_fortieth_withLiftCA δ _ _ _) s hs
    · exact oneRound_allJ8X_gen δ _ (oneRound_fortieth_withLiftCA δ _ _ _) s hs
  exact ⟨key.ne, key.same, key.dep_le⟩

end Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface
#print axioms listJ9A
#print axioms epsilonOf_listJ9A
#print axioms soundJ9A_pointwise
#print axioms oneRound_listJ9A
end Axioms
