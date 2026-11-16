/-
  Nock/NockVMROM/Thm54/VclL/Handle/CensusVS.lean

  Additive.

  * `seedSpecVS`: the fingerprint seed `z′ = χ₂ + χ₃√δ` (coins `{2, 3}`, sampled after round 0).
  * `zeroVS`: the zero-seed summand (`zeroSummand`, weight `1`).
  * `rowsVS`: the round-0 rows of the (restricted) cell twin, read from its B0 columns `< 129` only;
    `rowsVS_at`: at any accepted message they are the decoded cell table's `.b0` rows.
  * **`censusVS`**: `tableCensusSummand` at coins `{2, 3}`, `dep = ∅`, rows `rowsVS`, skeleton the claim
    nouns `[s, f, e]`, fuel `claimFuel` (`max fuelChip (claim leaves)`), weight
    `pairCount (T + 3) · (2·claimFuel − 1)`.
  * `census_sub`: outside the claim census at `Λ ≥ fuelChip`, also outside the plain table census
    `tableBadSeeds fuelChip rows []` (what T1 / T3 read).
  * **`claim_handles_VS'`**: `claim_handles_VS` with the seed and census exclusions priced
    (outside `valSummand`, `zeroVS`, `censusVS`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CensusVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The seed and the census inclusion -/

def s2 : Fin frameVS.n := ⟨2, by decide⟩
def s3 : Fin frameVS.n := ⟨3, by decide⟩

/-- **The VS fingerprint seed** `z′ = χ₂ + χ₃√δ` (coins `2, 3`, sampled after round 0). -/
def seedSpecVS {K : Type} [Field K] (δ : K) [Fact (¬ IsSquare δ)] : SeedSpec frameVS K (Quad δ) where
  seed χ := Quad.mk δ (χ s2) (χ s3)
  dep := ({s2, s3} : Finset (Fin frameVS.n))
  readsOn χ χ' h := by
    show Quad.mk δ _ _ = Quad.mk δ _ _
    rw [h s2 (Finset.mem_insert_self _ _), h s3 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
  round0 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> decide
  inj χ χ' h := by
    obtain ⟨h1, h2⟩ := (Quad.mk_eq_mk_iff δ _ _ _ _).mp h
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact h1
    · exact h2

theorem allPairs_append_mem : ∀ (l m : List Noun) {p : Noun × Noun}, p ∈ allPairs l → p ∈ allPairs (l ++ m)
  | [], _, _, h => by simp [allPairs] at h
  | a :: l, m, p, h => by
    simp only [List.cons_append, allPairs, List.mem_append, List.mem_map] at h ⊢
    rcases h with ⟨x, hx, rfl⟩ | h
    · exact Or.inl ⟨x, Or.inl hx, rfl⟩
    · exact Or.inr (allPairs_append_mem l m h)

section Sub
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp]

/-- **The claim census contains the table census**: outside `tableBadSeeds Λ rows skel` (`Λ ≥ fuelChip`),
also outside `tableBadSeeds fuelChip rows []`. -/
theorem census_sub {Λ : ℕ} (hΛ : fuelChip ≤ Λ) (rows : List (CellRowB0 q)) (skel : List Noun) {z : Kfp}
    (h : z ∉ tableBadSeeds Λ rows skel) : z ∉ tableBadSeeds fuelChip rows [] := by
  intro hm
  apply h
  unfold tableBadSeeds at hm ⊢
  rw [PreSeedCensus.mem_pairBadSeeds_iff] at hm ⊢
  obtain ⟨p, hp, h1, h2, h3⟩ := hm
  refine ⟨p, ?_, h1.trans hΛ, h2.trans hΛ, h3⟩
  unfold censusNouns at hp ⊢
  rw [List.append_nil] at hp
  exact allPairs_append_mem _ _ hp

end Sub

/-! ## 2. The round-0 rows and the two summands -/

section Summands

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP hC : ℕ)

theorem env_trace_129 {w w' h : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hw : 129 ≤ w) (hw' : 129 ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < 129), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩)
    (orbit : StrictOrbitDomain F 3 h) (x : F) (cv pv cv' pv' : ℕ → F) :
    ∀ j < 129, (Reify.envOfTrace Q orbit.ω x cv pv).trace j = (Reify.envOfTrace Q' orbit.ω x cv' pv').trace j := by
  intro j hj
  simp only [Reify.envOfTrace, dif_pos (show j < w by omega), dif_pos (show j < w' by omega)]
  rw [hQ j hj]

/-- **The cell twin's round-0 rows** (B0 columns `< 129` of the restricted trace). -/
def rowsVS (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) : List (CellRowB0 (ringChar F)) :=
  List.ofFn fun i : Fin (V.memRows (tCS hT hP)) =>
    cellB0Of (cellEnvF V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (fun _ => (0 : K))
      (fun _ => (0 : K)) (qrC (tr.2 (tCS hT hP))) i)

theorem rowsVS_length (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    (rowsVS hT hP hC V tr).length = V.memRows (tCS hT hP) := by
  simp [rowsVS]

theorem rowsVS_const (V : VerifierData F K hC (shapeVS hT hP)) (Q : Coins frameVS K → TrVS F hT hP hC)
    (hQ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) Q) (χ χ' : Coins frameVS K) :
    rowsVS hT hP hC V (Q χ) = rowsVS hT hP hC V (Q χ') := by
  unfold rowsVS
  congr 1
  funext i
  apply cellB0Of_congr
  refine env_trace_129 _ _ (by norm_num) (by norm_num) (fun j hj => ?_) _ _ _ _ _ _
  show (Q χ).2 (tCS hT hP) ⟨shiftCol 129 130 j, ValIOVS.shift_lt ⟨j, by omega⟩⟩ =
    (Q χ').2 (tCS hT hP) ⟨shiftCol 129 130 j, ValIOVS.shift_lt ⟨j, by omega⟩⟩
  refine hQ.2 (tCS hT hP) _ χ χ' fun i hi => absurd hi ?_
  have : ((shapeVS hT hP).table (tCS hT hP)).colRound ⟨shiftCol 129 130 j, ValIOVS.shift_lt ⟨j, by omega⟩⟩ = 0 := by
    change colRoundCH ⟨shiftCol 129 130 j, ValIOVS.shift_lt ⟨j, by omega⟩⟩ = 0
    simp only [colRoundCH, shiftCol]
    split_ifs <;> omega
  omega

/-- **The zero-seed summand at VS** (coins `{2, 3}`, weight `1`). -/
def zeroVS : BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) :=
  zeroSummand (F := F) (C := tableVS hC) (S := shapeVS hT hP) (Z := seedSpecVS (algebraMap F K δF))

theorem mem_zeroVS (tr : TrVS F hT hP hC) (χ : Coins frameVS K) :
    (zeroVS δF hT hP hC).mem tr χ ↔ zVS δF χ = 0 := by
  unfold zeroVS zeroSummand
  rw [seedSummand_mem]
  simp only [Finset.mem_singleton]
  rfl

def censusVS (V : VerifierData F K hC (shapeVS hT hP)) :
    BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) :=
  tableCensusSummand (algebraMap F K δF) frameVS s2 s3 (TracesStaged frameVS (tableVS hC) (shapeVS hT hP))
    (rowsVS hT hP hC V) (fun _ => claimList V.claim) (V.memRows (tCS hT hP)) 3 (claimFuel V.claim)
    (fun tr => le_of_eq (rowsVS_length hT hP hC V tr)) (fun _ => by simp [claimList])
    (fun Q hQ χ χ' => ⟨rowsVS_const hT hP hC V Q hQ χ χ', rfl⟩)

theorem mem_censusVS (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) (χ : Coins frameVS K) :
    (censusVS δF hT hP hC V).mem tr χ ↔
      zVS δF χ ∈ tableBadSeeds (Kfp := Quad (algebraMap F K δF)) (claimFuel V.claim) (rowsVS hT hP hC V tr)
        (claimList V.claim) := by
  have := tableCensusSummand_mem_iff (algebraMap F K δF) frameVS s2 s3
    (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) (rowsVS hT hP hC V) (fun _ => claimList V.claim)
    (V.memRows (tCS hT hP)) 3 (claimFuel V.claim) (fun tr => le_of_eq (rowsVS_length hT hP hC V tr))
    (fun _ => by simp [claimList]) (fun Q hQ χ χ' => ⟨rowsVS_const hT hP hC V Q hQ χ χ', rfl⟩) tr χ
  unfold censusVS
  convert this
  rfl

theorem censusVS_shape (V : VerifierData F K hC (shapeVS hT hP)) :
    (censusVS δF hT hP hC V).coins.card = 2 ∧ (censusVS δF hT hP hC V).dep = ∅ ∧
      (censusVS δF hT hP hC V).weight = pairCount (V.memRows (tCS hT hP) + 3) * (2 * claimFuel V.claim - 1) :=
  ⟨tableCensusSummand_coins_card _ _ _ _ (by decide) _ _ _ _ _ _ _ _ _, rfl, rfl⟩

end Summands

/-! ## 3. At VS -/

section VS

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

/-- At any coin the coin-free rows are the decoded cell table's round-0 rows. -/
theorem rowsVS_at (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    rowsVS hT hP hC V (msg.traces χ) = (tVS δF hT hP kr hC V msg χ).map (·.b0) := by
  unfold rowsVS tVS cellTableOf
  rw [List.map_ofFn]
  congr 1

/-- **Outside the zero and census summands**: the seed is nonzero and outside both censuses. -/
theorem census_good (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h0 : ¬ (zeroVS δF hT hP hC).mem (msg.traces χ) χ)
    (hc : ¬ (censusVS δF hT hP hC V).mem (msg.traces χ) χ) :
    zVS δF χ ≠ 0 ∧
      zVS δF χ ∉ tableBadSeeds (Kfp := Quad (algebraMap F K δF)) (claimFuel V.claim)
        ((tVS δF hT hP kr hC V msg χ).map (·.b0)) (claimList V.claim) ∧
      zVS δF χ ∉ tableBadSeeds (Kfp := Quad (algebraMap F K δF)) fuelChip
        ((tVS δF hT hP kr hC V msg χ).map (·.b0)) [] := by
  rw [mem_zeroVS] at h0
  rw [mem_censusVS, rowsVS_at] at hc
  exact ⟨h0, hc, census_sub (fuelChip_le_claimFuel V.claim) _ _ hc⟩

theorem claim_handles_VS' (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hval : ¬ (valSummand δF hT hP hC V msg.msg0C).mem (msg.traces χ) χ)
    (h0 : ¬ (zeroVS δF hT hP hC).mem (msg.traces χ) χ)
    (hc : ¬ (censusVS δF hT hP hC V).mem (msg.traces χ) χ) :
    ∀ k : Fin 3, denH ((tVS δF hT hP kr hC V msg χ).map (·.b0))
      (claimHandle (claimNoun V.claim k) (natOf ((msg.msg0C k).1 : F))) = some (claimNoun V.claim k) := by
  obtain ⟨hz, hT2, -⟩ := census_good δF hT hP kr hC V msg χ h0 hc
  exact claim_handles_VS δF hT hP kr hC V hV msg χ h hval hz hT2

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
