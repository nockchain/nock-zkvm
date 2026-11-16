/-
  **The J-9 AL end-to-end interface**, the twin of
  `J9A/E2EJ9AIface` at the J-9 AL types (`PubJ9AL / MsgJ9AL' / TrJ9AL / RowsJ9AL`): `listJ9AL` (`allJ9AL` of the
  data used by `probJ9AL_absent` (`XA9ZP`) / `probJ9AL_present` (`XA9P`)), `epsilonOf_listJ9AL` (`< 2^-155`),
  `soundJ9AL_pointwise` (the `hsound` lambdas of `probJ9AL_absent` / `_present`), `oneRound_listJ9AL`
  (`OneRoundCD frameJ8` per summand).  Binders: `probJ9AL_final_clean`'s.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ProbJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.E2EJ9AIface

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface

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
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (TrJ9A StJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (PubJ9AL MsgJ9AL' TrJ9AL StJ9AL RowsJ9AL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL (AcceptsJ9AL censusP)
open Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface (OneRoundCD OneRoundJ8 oneRoundJ8_of_cd oneRoundCD_lift
  cd_spec1314 cd_specVQ cd_specHQ cd_spec01 cj_specV cj_specH_y cj_specH cj_specZY cj_spec01 cj_y)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ9A (hA3A hgA)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ9AL (soundAL_absent soundAL_present hcapAL)
open Nock.NockVMROM.Thm54.VclL.Handle.CensusAL (XA9P XA9ZP)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A (sum40A withLiftCA CW9)
open Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9AIface (twinFact twinAlg oneRound_sum40A oneRound_allJ8X_gen)


variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ9AL} {g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

attribute [local instance] twinFact twinAlg

open Classical in
/-- **The J-9 AL summand list**: `allJ9AL` of the absent data (`XA9ZP`, as `probJ9AL_absent`) if `Pb.krootsV = 0`,
else of the present data (`XA9P`, as `probJ9AL_present`). -/
noncomputable def listJ9AL (Pb : PubJ9AL p) (c : P8PublicClaim) (r : RowsJ9AL) (g : ℕ)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9P : (censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31) :
    List (BadSummand frameJ8 K (TrJ9AL (ZMod p)) StJ9AL) :=
  if Pb.krootsV = 0 then
    RR49AL.allJ9AL (r := r) δ b
      (XA9ZP δ b (g := g + r.N + r.AX) (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
        (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb c [] (by simp)
        (layLe_ofG (r := RR49A.rowsB r.toRowsJ9A) Pb.toPubJ8 hLC hLM hLW hLA hLV) rfl hnM hreg9P hLC) Pb c g
  else
    RR49AL.allJ9AL (r := r) δ b
      (XA9P δ b (g := g + r.N + r.AX) (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
        (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb c [] (by simp)
        (layLe_ofG (r := RR49A.rowsB r.toRowsJ9A) Pb.toPubJ8 hLC hLM hLW hLA hLV) rfl hnM hreg9P hLC) Pb c g

open Classical in
/-- **The error of the list**: `epsilonOf (listJ9AL …) < 2^-155`, for `Fintype.card K = cK`, a row bundle within the census corner `cornerC` (`r.AX, r.SP, r.AL, g ≤ 2^31`) and the size hypotheses on `Pb`. -/
theorem epsilonOf_listJ9AL (Pb : PubJ9AL p) (c : P8PublicClaim) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31) (hAL : r.AL ≤ 2 ^ 31)
    (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9P : (censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31) :
    epsilonOf (listJ9AL δ b Pb c r g hLC hLM hLW hLA hLV hnM hreg9P) < 1 / (2 : ℚ) ^ 155 := by
  unfold listJ9AL
  split_ifs
  · rw [RR49AL.epsilon_allJ9AL, quad_card, hcK]
    exact RR49AL.figJ9AL_155 hr hAX hSP hAL (le_refl _) hg
  · rw [RR49AL.epsilon_allJ9AL, quad_card, hcK]
    exact RR49AL.figJ9AL_155 hr hAX hSP hAL (le_refl _) hg

open Classical in
/-- **Pointwise soundness**: if `AcceptsJ9AL` holds for the transcript `tr` and message `M` at the coins `χ`, and `χ` lies in no summand of `listJ9AL` (`hout`), then the public claim holds (`Nock.Jet.HoldsN c`); for a faithful registry, `p = Nock.Atoms.p` and the row-size hypotheses. -/
theorem soundJ9AL_pointwise [CharP K p] [CharP 𝕂′ p] (Pb : PubJ9AL p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (hpG : p = Nock.Atoms.p)
    (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31) (hAL : r.AL ≤ 2 ^ 31)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9P : (censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31)
    (χ : Coins frameJ8 K) (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p))
    (hM : AcceptsJ9AL δ b Pb Rg c χ M tr r g)
    (hout : ∀ s ∈ listJ9AL δ b Pb c r g hLC hLM hLW hLA hLV hnM hreg9P, ¬ s.mem tr χ) :
    Nock.Jet.HoldsN c := by
  unfold listJ9AL at hout
  by_cases h0 : Pb.krootsV = 0
  · rw [if_pos h0] at hout
    exact soundAL_absent δ b hRg hM h0 _ _ [] (by simp) _ rfl hnM hreg9P hLC hout hpG hqM hk hmax
      (hA3A (r := r.toRowsJ9A) hr hpG) (hcapAL hr hAX hAL hg hpG)
  · rw [if_neg h0] at hout
    have hpos : 1 ≤ Pb.krootsV := Nat.pos_of_ne_zero h0
    have hΛ : fuelChip ≤ (RR49A.rowsB r.toRowsJ9A).Λ := by
      show fuelChip ≤ r.Λ
      rw [hr.2.2.2.1]; exact le_refl _
    exact soundAL_present δ b hRg hM hpos _ _ [] (by simp) _ rfl hnM hreg9P hLC hout hpG hqM hk hmax
      (hA3A (r := r.toRowsJ9A) hr hpG) hΛ (hcapAL hr hAX hAL hg hpG)

/-! ## One round per summand -/

section OneRound
variable {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop}

open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (specVQ specHQ spec01 spec1314 v2 v3 v4 v5 v6 v7 v11 v12 v13 v14 v0 v1)

open Classical in
/-- The ten summands of `sum40A L C` are one-round at `frameVSQ` (before lifting). -/
theorem cd_sum40A {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K] {r' : RowsJ8}
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r') (C : CW9 (K := K) Tr St r') :
    ∀ s ∈ sum40A L C, OneRoundCD frameVSQ s.coins s.dep := by
  intro s hs
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

end OneRound

open Classical in
/-- **One round, generic**: every summand of `allJ9AL X` is one-round (`OneRoundJ8`), given that every summand of the 40th summand's list `X.C.D.l40` is one-round at `frameVSQ`. -/
theorem oneRound_allJ9AL {P g₀ : ℕ}
    (X : DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A
      (RR49A.rowsB r.toRowsJ9A) P g₀) (Pb : PubJ9AL p) (c : P8PublicClaim) (g' : ℕ)
    (h40 : ∀ s ∈ X.C.D.l40, OneRoundCD frameVSQ s.coins s.dep) :
    ∀ s ∈ RR49AL.allJ9AL δ b X Pb c g', OneRoundJ8 s := by
  intro s hs
  rw [RR49AL.allJ9AL, List.mem_append] at hs
  rcases hs with hs | hs
  · refine oneRound_allJ8X_gen δ _ (fun s hs => ?_) s hs
    simp only [sumJ8C, sumJ8, RR49AL.XAL, List.mem_map] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    exact oneRoundCD_lift s' (h40 s' hs')
  · replace hs := List.mem_singleton.1 hs; subst hs
    refine oneRoundJ8_of_cd ?_
    rw [RR49AL.arithAL, AluSZEvent.arithSZ_coins, AluSZEvent.arithSZ_dep]
    decide

open Classical in
/-- **One round at `listJ9AL`**: every summand of `listJ9AL` is one-round (`OneRoundCD frameJ8 s.coins s.dep`), in both branches. -/
theorem oneRound_listJ9AL (Pb : PubJ9AL p) (c : P8PublicClaim) (r : RowsJ9AL) (g : ℕ)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9P : (censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31) :
    ∀ s ∈ listJ9AL δ b Pb c r g hLC hLM hLW hLA hLV hnM hreg9P, OneRoundCD frameJ8 s.coins s.dep := by
  intro s hs
  have key : OneRoundJ8 s := by
    unfold listJ9AL at hs
    split_ifs at hs
    · exact oneRound_allJ9AL (r := r) δ b _ Pb c g (cd_sum40A δ _ _) s hs
    · exact oneRound_allJ9AL (r := r) δ b _ Pb c g (cd_sum40A δ _ _) s hs
  exact ⟨key.ne, key.same, key.dep_le⟩

end Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.E2EJ9ALIface
#print axioms listJ9AL
#print axioms epsilonOf_listJ9AL
#print axioms soundJ9AL_pointwise
#print axioms oneRound_listJ9AL
end Axioms
