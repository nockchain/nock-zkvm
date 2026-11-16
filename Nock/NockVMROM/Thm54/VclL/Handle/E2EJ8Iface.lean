/-
  Nock/NockVMROM/Thm54/VclL/Handle/E2EJ8Iface.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface

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
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4 (RR4 LL4)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5 (R0d L0d)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV (hsoundJ8XUG linkXUG_of_R5)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A (hsoundJ8XUA linkXUA_of_R5)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (RR4A)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (wdV_view)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV (layLe_ofG)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7 c11 c12 c15 c16 c2 c3 liftJ8 embJ8 yDep sumJ8 orderJ8 ioSummandJ8 atomDyckJ8 atomCensusJ8 zeroYJ8 bivJ8 specV specH specZY)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (sumJ8C allJ8C DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (sum40 Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (allJ8X atomFpxJ8 withFpxV)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {g P : ℕ}

/-- The twin `ringChar` instances of `CleanJ8.probJ8V_final_clean`'s proof, as local instances. -/
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem twinFact : Fact (ringChar (ZMod p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
@[reducible] def twinAlg : Algebra (ZMod (ringChar (ZMod p))) K :=
  @Eq.rec ℕ p (fun q _ => Algebra (ZMod q) K) ‹Algebra (ZMod p) K› _ (ZMod.ringChar_zmod_n p).symm
attribute [local instance] twinFact twinAlg


open Classical in
/-- **The J-8 summand list at `probJ8V_final_clean`'s binders**: `allJ8X` of the absent data
(`LinkJ8A.probJ8V_absent`: `RR4A`) if `Pb.krootsV = 0`, else of the present data (`LinkJ8NV.probJ8NV_final`: `RR4`).
The layout / census binders enter as in those proofs (they are the proof arguments of `RR4` / `RR4A`). -/
noncomputable def listJ8V (Pb : PubJ8 p) (c : P8PublicClaim) (r : RowsJ8) (g : ℕ)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    List (BadSummand frameJ8 K (TrJ8 (ZMod p)) StJ8) :=
  if Pb.krootsV = 0 then
    AtomFpxJ8.allJ8X
      (AtomFpxJ8.withFpxV δ b
        (withLiftC (RR4A δ b (g := g + r.N) (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
            Pb c [] (by simp) (layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM hreg)
          (LL4 δ b (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb [] (by simp)
            (layLe_ofG Pb hLC hLM hLW hLA hLV)))
        Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA)
  else
    AtomFpxJ8.allJ8X
      (AtomFpxJ8.withFpxV δ b
        (withLiftC (RR4 δ b (g := g + r.N) (R0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (P := 2 ^ 66))
            Pb c [] (by simp) (layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM hreg)
          (LL4 δ b (L0d (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ)) Pb [] (by simp)
            (layLe_ofG Pb hLC hLM hLW hLA hLV)))
        Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA)

open Classical in
/-- **N2**: `ε` of the list `< 2^-155`. -/
theorem epsilonOf_listJ8V (Pb : PubJ8 p) (c : P8PublicClaim) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r EncInjJ8.cornerC) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    epsilonOf (listJ8V δ b Pb c r g hLC hLM hLW hLA hLV hnM hreg) < 1 / (2 : ℚ) ^ 155 := by
  unfold listJ8V
  split_ifs
  · exact RepriceJ8.epsJ8X_lt_155_census32 _ hcK hr (le_refl _) (RepriceJ8.g32_of_corner hr hg)
  · exact RepriceJ8.epsJ8X_lt_155_census32 _ hcK hr (le_refl _) (RepriceJ8.g32_of_corner hr hg)

open Classical in
/-- **N1**: pointwise soundness of `AcceptsJ8V` outside the summands of `listJ8V`. -/
theorem soundJ8V_pointwise [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (hpG : p = Nock.Atoms.p)
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (hM : AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hout : ∀ s ∈ listJ8V δ b Pb c r g hLC hLM hLW hLA hLV hnM hreg, ¬ s.mem tr χ) :
    Nock.Jet.HoldsN c := by
  unfold listJ8V at hout
  by_cases h0 : Pb.krootsV = 0
  · rw [if_pos h0] at hout
    exact hsoundJ8XUA δ b Pb hRg c χ M tr _ _ hpG hqM hk hM h0 hout
      (linkXUA_of_R5 δ b Pb c χ M tr _ _ [] (by simp) (layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM hreg hpG hr
        hg hmax hM h0 hout)
  · rw [if_neg h0] at hout
    have hM' := AcceptsJ8V.toNV_of_pos hM (Nat.pos_of_ne_zero h0)
    exact hsoundJ8XUG δ b Pb hRg c χ M tr _ _ hpG hqM hk hM' hout hM'.hbudV.2.2.2 hM'.hbudV.2.2.1
      (wdV_view δ b Pb tr _ _)
      (linkXUG_of_R5 δ b Pb c χ M tr _ _ [] (by simp) (layLe_ofG Pb hLC hLM hLW hLA hLV) rfl hnM hreg hpG hr
        hg hmax hM' hout)


/-! ## N3. One round per summand -/

/-- The `OneRound` shape on bare coin sets (decidable). -/
def OneRoundCD (Φ : CoinFrame) (C D : Finset (Fin Φ.n)) : Prop :=
  C.Nonempty ∧ (∀ i ∈ C, ∀ i' ∈ C, Φ.sampledAfter i = Φ.sampledAfter i') ∧
    ∀ i ∈ D, ∀ i' ∈ C, Φ.sampledAfter i ≤ Φ.sampledAfter i'

instance (Φ : CoinFrame) (C D : Finset (Fin Φ.n)) : Decidable (OneRoundCD Φ C D) := by
  unfold OneRoundCD; infer_instance

/-- **`OneRound`** at `Φ = frameJ8`, with `Staged := St`
abstract: the summand prices a nonempty set of coins, all sampled in one round, and reads only coins sampled no
later. -/
structure OneRoundJ8 {K : Type} [Field K] [Fintype K] [DecidableEq K] {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop}
    (s : BadSummand frameJ8 K Tr St) : Prop where
  ne : s.coins.Nonempty
  same : ∀ i ∈ s.coins, ∀ i' ∈ s.coins, frameJ8.sampledAfter i = frameJ8.sampledAfter i'
  dep_le : ∀ i ∈ s.dep, ∀ i' ∈ s.coins, frameJ8.sampledAfter i ≤ frameJ8.sampledAfter i'

section OneRound
variable {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop}

theorem oneRoundJ8_of_cd {s : BadSummand frameJ8 K Tr St} (h : OneRoundCD frameJ8 s.coins s.dep) :
    OneRoundJ8 s := ⟨h.1, h.2.1, h.2.2⟩

theorem emb_sampled (i : Fin frameVSQ.n) : frameJ8.sampledAfter (embJ8 i) = frameVSQ.sampledAfter i :=
  (toVSQ_sampled i).symm

theorem oneRoundCD_lift {Tr' : Type} {St' : (Coins frameVSQ K → Tr') → Prop} (s : BadSummand frameVSQ K Tr' St')
    (h : OneRoundCD frameVSQ s.coins s.dep) {π : Tr → Tr'} {hπ} :
    OneRoundJ8 (liftJ8 s π hπ : BadSummand frameJ8 K Tr St) := by
  refine oneRoundJ8_of_cd ⟨?_, ?_, ?_⟩
  · exact (h.1.map : (s.coins.map embJ8).Nonempty)
  · intro i hi i' hi'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.1 hi'
    rw [emb_sampled, emb_sampled]; exact h.2.1 a ha a' ha'
  · intro i hi i' hi'
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.1 hi'
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hi
      rw [emb_sampled, emb_sampled]; exact h.2.2 a ha a' ha'
    · -- the limb coins are sampled in round 0
      have hy : ∀ j ∈ yDep, frameJ8.sampledAfter j = 0 := by decide
      have := hy i hi
      omega

section Cd
variable {Kio : Type} [Field Kio] {mk : K → K → Kio} {hmk : ∀ a b c d, mk a b = mk c d → a = c ∧ b = d}
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (specVQ specHQ spec01 spec1314 v2 v3 v4 v5 v6 v7 v11 v12 v13 v14 v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (specV specH specZY)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (spec01J8 c0 c1)

theorem cd_specVQ : OneRoundCD frameVSQ (specVQ mk hmk).dep (coinsBelow frameVSQ 1) := by
  show OneRoundCD frameVSQ ({v4, v6, v5, v7} : Finset (Fin frameVSQ.n)) _; decide
theorem cd_specHQ : OneRoundCD frameVSQ (specHQ mk hmk).dep ∅ := by
  show OneRoundCD frameVSQ (({v11, cGamHi, v12, cRhoHi}) : Finset (Fin frameVSQ.n)) _; decide
theorem cd_spec01 : OneRoundCD frameVSQ (spec01 (K := K)).dep (coinsBelow frameVSQ 1) := by
  show OneRoundCD frameVSQ ({v0, v1} : Finset (Fin frameVSQ.n)) _; decide
theorem cd_spec1314 : OneRoundCD frameVSQ (spec1314 (K := K)).dep ∅ := by
  show OneRoundCD frameVSQ ({v13, v14} : Finset (Fin frameVSQ.n)) _; decide

end Cd

open Classical in
theorem oneRound_sum40 {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K] {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop}
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (hπ) :
    ∀ s ∈ sum40 L, OneRoundJ8 (liftJ8 s (id : Tr → Tr) hπ : BadSummand frameJ8 K Tr St) := by
  intro s hs
  apply oneRoundCD_lift
  simp only [sum40, List.mem_cons, List.not_mem_nil, or_false] at hs
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

section CdJ
variable {Kio : Type} [Field Kio] {mk : K → K → Kio} {hmk : ∀ a b c d, mk a b = mk c d → a = c ∧ b = d}
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (spec01J8 c0 c1)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (specV specH specZY)

theorem cj_specV : OneRoundCD frameJ8 (specV mk hmk).dep (coinsBelow frameJ8 1) := by
  show OneRoundCD frameJ8 ({c4, c6, c5, c7} : Finset (Fin frameJ8.n)) _; decide
theorem cj_specH_y : OneRoundCD frameJ8 (specH mk hmk).dep yDep := by
  show OneRoundCD frameJ8 ({c11, c15, c12, c16} : Finset (Fin frameJ8.n)) _; decide
theorem cj_specH : OneRoundCD frameJ8 (specH mk hmk).dep ∅ := by
  show OneRoundCD frameJ8 ({c11, c15, c12, c16} : Finset (Fin frameJ8.n)) _; decide
theorem cj_specZY : OneRoundCD frameJ8 (specZY mk hmk).dep ∅ := by
  show OneRoundCD frameJ8 ({WeightsJ8.c2, WeightsJ8.c3, cY1, cY2} : Finset (Fin frameJ8.n)) _; decide
theorem cj_spec01 : OneRoundCD frameJ8 (spec01J8 (K := K)).dep (coinsBelow frameJ8 1) := by
  show OneRoundCD frameJ8 ({EncZYJ8.c0, EncZYJ8.c1} : Finset (Fin frameJ8.n)) _; decide
theorem cj_y : OneRoundCD frameJ8 ({cY1, cY2} : Finset (Fin frameJ8.n)) ∅ := by decide

end CdJ

end OneRound

open Classical in
/-- **N3**: every summand of the J-8 list (at the data of `listJ8V`, for any readouts `R`, `L`) is one-round. -/
theorem oneRound_allJ8X
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r) (kroots : ℕ)
    {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p) (orbitV : StrictOrbitDomain (ZMod p) 3 hV)
    {hA nA : ℕ} (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA) :
    ∀ s ∈ allJ8X (withFpxV δ b (withLiftC R L) kroots hnV nodesV orbitV nodesA orbitA), OneRoundJ8 s := by
  intro s hs
  rw [allJ8X, List.mem_append] at hs
  rcases hs with hs | hs
  · rw [allJ8C, List.mem_flatMap] at hs
    obtain ⟨m, -, hs⟩ := hs
    replace hs : s ∈ sumJ8C (withLiftC R L) m := hs
    cases m
    · have : sumJ8C (withLiftC R L) .fortieth = (sum40 L).map fun s => liftJ8 s id (Lift40J8.hπ40_id StJ8) := rfl
      rw [this] at hs
      obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
      exact oneRound_sum40 δ L _ s' hs'
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
/-- **N3 at `listJ8V`**: every summand is one-round (`OneRoundJ8`), in both branches. -/
theorem oneRound_listJ8V (Pb : PubJ8 p) (c : P8PublicClaim) (r : RowsJ8) (g : ℕ)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    ∀ s ∈ listJ8V δ b Pb c r g hLC hLM hLW hLA hLV hnM hreg, OneRoundJ8 s := by
  unfold listJ8V
  split_ifs
  · exact oneRound_allJ8X δ b _ _ _ _ _ _ _ _
  · exact oneRound_allJ8X δ b _ _ _ _ _ _ _ _

end Nock.NockVMROM.Thm54.VclL.Handle.E2EJ8Iface
