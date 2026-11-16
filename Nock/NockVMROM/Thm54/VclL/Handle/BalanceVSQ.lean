/-
  Nock/NockVMROM/Thm54/VclL/Handle/BalanceVSQ.lean

  Additive: preparation. -/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
import Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ
import Nock.NockVMROM.Thm54.VclL.Handle.SummandsHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.MixedCoordinateCompiler

noncomputable section

section Bridges
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- **The compute twin's `𝕂′` coins at `chalVHQ` are `(γH′, ρH′)`.** -/
theorem coinsCV_VSQ (χ : Coins frameVSQ K) :
    TeleCQ.coinsCV b δF (chalVHQ b χ) = (⟨gamHQ δF χ, rhoHQ δF χ⟩ : IOCoins 𝕂′) := by
  unfold TeleCQ.coinsCV gamHQ rhoHQ
  congr 1 <;> congr 1 <;>
  · refine limbVal_eq_of_coords b _ _ _ fun k => ?_
    fin_cases k <;> simp [chalVHQ, coinHQ, coinH, toVS, chalGammaL, chalGammaIm, chalRhoL, chalRhoIm,
      cGamH, cRhoH, cGamHi, cRhoHi]

/-- The compute export / path terminals at `pubVHQ`. -/
theorem pubX_VSQ (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (χ : Coins frameVSQ K) :
    Quad.mk _ (limbVal b (pubVHQ δF b c m ρ χ) pubRhoX) (limbVal b (pubVHQ δF b c m ρ χ) pubRhoXIm) = ρ 3 := by
  have h1 : limbVal b (pubVHQ δF b c m ρ χ) pubRhoX = Quad.re _ (ρ 3) := by
    refine limbVal_eq_of_coords b _ _ _ fun k => ?_
    fin_cases k <;> simp [pubVHQ, pubVH, pubRhoX]
  have h2 : limbVal b (pubVHQ δF b c m ρ χ) pubRhoXIm = Quad.im _ (ρ 3) := by
    refine limbVal_eq_of_coords b _ _ _ fun k => ?_
    fin_cases k <;> simp [pubVHQ, pubRhoXIm]
  rw [h1, h2, Quad.mk_re_im]

theorem pubP_VSQ (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (χ : Coins frameVSQ K) :
    Quad.mk _ (limbVal b (pubVHQ δF b c m ρ χ) pubRhoP) (limbVal b (pubVHQ δF b c m ρ χ) pubRhoPIm) = ρ 4 := by
  have h1 : limbVal b (pubVHQ δF b c m ρ χ) pubRhoP = Quad.re _ (ρ 4) := by
    refine limbVal_eq_of_coords b _ _ _ fun k => ?_
    fin_cases k <;> simp [pubVHQ, pubVH, pubRhoP]
  have h2 : limbVal b (pubVHQ δF b c m ρ χ) pubRhoPIm = Quad.im _ (ρ 4) := by
    refine limbVal_eq_of_coords b _ _ _ fun k => ?_
    fin_cases k <;> simp [pubVHQ, pubRhoPIm]
  rw [h1, h2, Quad.mk_re_im]

/-- The memory twins' `𝕂′` coins at `chalsVSQ` are `(γH′, ρH′)`. -/
theorem chalsVSQ_coins (χ : Coins frameVSQ K) :
    (⟨Quad.mk _ (chalsVSQ δF χ 33) (chalsVSQ δF χ 35), Quad.mk _ (chalsVSQ δF χ 34) (chalsVSQ δF χ 36)⟩ :
      IOCoins 𝕂′) = ⟨gamHQ δF χ, rhoHQ δF χ⟩ := by
  have h33 : chalsVSQ δF χ 33 = χ ⟨11, by decide⟩ := by
    simp only [chalsVSQ, if_neg (show (33 : ℕ) ≠ 35 by decide), if_neg (show (33 : ℕ) ≠ 36 by decide)]
    exact chalsVS_hGam δF (toVS χ)
  have h34 : chalsVSQ δF χ 34 = χ ⟨12, by decide⟩ := by
    simp only [chalsVSQ, if_neg (show (34 : ℕ) ≠ 35 by decide), if_neg (show (34 : ℕ) ≠ 36 by decide)]
    exact chalsVS_hRho δF (toVS χ)
  have h35 : chalsVSQ δF χ 35 = χ cGamHi := by simp [chalsVSQ]
  have h36 : chalsVSQ δF χ 36 = χ cRhoHi := by simp [chalsVSQ]
  rw [h33, h34, h35, h36]; rfl

theorem pubsCHQ_term (ρ : Fin 5 → 𝕂′) (y yH : 𝕂′) :
    Quad.mk _ (pubsCHQ δF ρ y yH CellHQ.pubHQ) (pubsCHQ δF ρ y yH (CellHQ.pubHQ + 1)) = ρ 3 + yH := by
  simp [pubsCHQ, CellHQ.pubHQ, Quad.mk_re_im]

theorem pubsWHQ_termX (ρ : Fin 5 → 𝕂′) (y yH : 𝕂′) :
    Quad.mk _ (pubsWHQ δF ρ y yH WalkHQ.pubXQ) (pubsWHQ δF ρ y yH (WalkHQ.pubXQ + 1)) = yH := by
  simp [pubsWHQ, WalkHQ.pubXQ, Quad.mk_re_im]

theorem pubsWHQ_termP (ρ : Fin 5 → 𝕂′) (y yH : 𝕂′) :
    Quad.mk _ (pubsWHQ δF ρ y yH WalkHQ.pubPQ) (pubsWHQ δF ρ y yH (WalkHQ.pubPQ + 1)) = ρ 4 := by
  simp [pubsWHQ, WalkHQ.pubPQ, Quad.mk_re_im]

end Bridges

/-! ## The memory sides of the `𝕂′` balance, in list form -/

section MemLists
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ}
  (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The `𝕂′` coins at the memory leaves. -/
abbrev mcoins : IOCoins 𝕂′ := ⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩

theorem cell_provs_denQ (Q : Fin (cellChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ q ∈ ServeH.cellProvs b nodes orbit chals pubs Q,
      compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) q.1) ≠ 0 := by
  intro q hq
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
  rw [← TeleHQ.cDenQ_eq]
  exact (TeleHQ.cellHQ_inv δF b hn nodes orbit chals pubs Q hsat i).1

/-- **The cell providers' weighted `𝕂′` sum is the terminal `(pub₄, pub₅)`.** -/
theorem cell_provs_sumQ (Q : Fin (cellChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (cellChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((ServeH.cellProvs b nodes orbit chals pubs Q).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) := by
  rw [← TeleHQ.cellHQ_telescope δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  simp only [ServeH.cellProvs, List.map_map, Function.comp_def]
  rw [Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TeleHQ.cTermQ, (TeleHQ.cellHQ_inv δF b hn nodes orbit chals pubs Q hsat i).2, TeleHQ.cDenQ_eq]

theorem walk_reqs_denQ (Q : Fin (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ r ∈ ServeH.walkXReqs b nodes orbit chals pubs Q,
      compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) r) ≠ 0 := by
  intro r hr
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hr
  rw [← TeleHQ.wDenQ_eq δF kroots b hn nodes orbit chals pubs Q _ rfl]
  exact (TeleHQ.walkHQ_inv δF kroots b hn nodes orbit chals pubs Q hsat j).1.1

/-- **The walk's consumed export keys sum to its terminal `(pub₄, pub₅)`.** -/
theorem walk_reqs_sumQ (Q : Fin (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (walkChipHQ δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipHQ δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((ServeH.walkXReqs b nodes orbit chals pubs Q).map fun r =>
        (compress (mcoins δF chals) (BalanceQ.liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (pubs WalkHQ.pubXQ) (pubs (WalkHQ.pubXQ + 1)) := by
  rw [← TeleHQ.walkHQ_telescopeX δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  simp only [ServeH.walkXReqs, List.map_map, Function.comp_def]
  rw [Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(TeleHQ.walkHQ_inv δF kroots b hn nodes orbit chals pubs Q hsat j).1.2,
    TeleHQ.wDenQ_eq δF kroots b hn nodes orbit chals pubs Q _ rfl]

end MemLists

/-! ## The `𝕂′` export balance at an accepted VSQ coin -/

section Frame
open SVFrameG
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVSQ hT hP) → ClaimMsgVS → SummandsVSQ (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVSQ hT hP) → Unit → SummandsVSQ (F := F) (K := K) hT hP hC}

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The VSQ compute consumed export keys (actual coin / public vectors). -/
abbrev cXQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K) :
    List (Fin 5 → K) :=
  TeleC.compXReqs V.computeNodes (chalVHQ V.basis χ) (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ)
    V.orbitC (msg.Qc χ)

abbrev cPQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K) :
    List (Fin 5 → K) :=
  TeleC.compPReqs V.computeNodes (chalVHQ V.basis χ) (pubVHQ δF V.basis V.claim msg.msg0C (msg.requests χ) χ)
    V.orbitC (msg.Qc χ)

abbrev wXQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K) :
    List (Fin 5 → K) :=
  ServeH.walkXReqs V.basis (V.memNodes (tWQ hT hP)) (V.orbitM (tWQ hT hP)) (chalsVSQ δF χ)
    (pubsWHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (msg.Qm χ (tWQ hT hP))

abbrev tXQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K) :
    List ((Fin 5 → K) × K) :=
  ServeH.cellProvs V.basis (V.memNodes (tCQ hT hP)) (V.orbitM (tCQ hT hP)) (chalsVSQ δF χ)
    (pubsCHQ δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (msg.Qm χ (tCQ hT hP))

/-- **The `𝕂′` export LogUp identity at an accepted VSQ coin** (compute export + walk-consumed keys
against the cell twin's weighted provides), at `(γH′, ρH′)`; the compute path denominators are assumed
nonzero (they are, outside the `𝕂′` path event). -/
theorem export_sumQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (hV : V.Checks (fun a => reqBoundVSQ hT hP hC V a + internalBoundVSQ hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVSQ δF hT hP hC sumC) (memCoreVSQ δF hT hP kr hC sumM)) (χ : Coins frameVSQ K)
    (h : AcceptsG V msg χ)
    (hden : ∀ r ∈ cPQ δF hT hP kr hC V msg χ,
      compress (⟨gamHQ δF χ, rhoHQ δF χ⟩ : IOCoins 𝕂′) (BalanceQ.liftRec (L := 𝕂′) r) ≠ 0) :
    ((cXQ δF hT hP kr hC V msg χ ++ wXQ δF hT hP kr hC V msg χ).map fun r =>
        (compress (⟨gamHQ δF χ, rhoHQ δF χ⟩ : IOCoins 𝕂′) (BalanceQ.liftRec (L := 𝕂′) r))⁻¹).sum =
      ((tXQ δF hT hP kr hC V msg χ).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (⟨gamHQ δF χ, rhoHQ δF χ⟩ : IOCoins 𝕂′) (BalanceQ.liftRec (L := 𝕂′) q.1))⁻¹).sum := by
  obtain ⟨hg, hsat⟩ := compute_factsQ δF hT hP kr hC V msg χ h
  obtain ⟨-, hwT, hsatT⟩ := cell_factsQ δF hT hP kr hC V msg χ h
  obtain ⟨-, hwW, hsatW⟩ := walk_factsQ δF hT hP kr hC V msg χ h
  have hc : 11 < ringChar F := lt_trans (by norm_num) hg.2.2.1
  have hadj : ∀ (i : Fin V.N) (hi : (i : ℕ) + 1 < V.N),
      V.computeNodes ⟨(i : ℕ) + 1, hi⟩ = V.computeNodes i * V.orbitC.ω := fun i hi => by
    rw [hg.1 i hi, mul_comm]
  have hC := TeleCQ.compXQ_sum V.hN V.computeNodes V.basis δF _ _ V.orbitC _ hsat hg.2.1 hadj hc
    (by rw [coinsCV_VSQ]; exact hden)
  erw [coinsCV_VSQ, pubX_VSQ] at hC
  have hTe := cell_provs_sumQ δF V.basis (V.hM _) (V.memNodes _) (V.orbitM _) _ _ _ hsatT.1 hsatT.2
    (hV.memNodes_injective _) (hV.hadjM _)
  rw [mcoins, chalsVSQ_coins, pubsCHQ_term] at hTe
  have hWe := walk_reqs_sumQ δF kr V.basis (V.hM _) (V.memNodes _) (V.orbitM _) _ _ _ hsatW.1 hsatW.2
    (hV.memNodes_injective _) (hV.hadjM _)
  rw [mcoins, chalsVSQ_coins, pubsWHQ_termX] at hWe
  rw [List.map_append, List.sum_append]
  exact (congrArg₂ (· + ·) hC hWe).trans hTe.symm

end Frame

end

end Nock.NockVMROM.Thm54.VclL.Handle.BalanceVSQ
