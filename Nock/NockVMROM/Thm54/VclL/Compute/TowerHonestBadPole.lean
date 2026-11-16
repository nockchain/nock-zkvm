import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestBad
import Nock.NockVMROM.Thm54.VclL.Compute.TowerLookupHonest
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemHonest

/-!
# The honest pole summands of the VCL compute family, item (d)

Five pole summands over the IO coins `{4,5,6,7}` (`ioSpecVCLQuad`), one per record kind of C3's gates:
`recQ0` (slot 0, all rows), `op0PathRec` (state 0), `tailRec` (`slot1ExportSels`), `ttRec` (state 6),
`op9PathRec` (state 9).  The record lists are read OFF THE COMMITTED COMPUTE TRACE `tr.1` (the raw VCL
row environment at the orbit nodes), never off the coins; they read only columns of round `<= 1`
(`entryR1`, `decide`), so along a staged strategy they depend only on the coins sampled after block 0,
`depB1 = {2,3,8,9,10}`, which are disjoint from the IO coins (round-respect, proved: `readsOn`).
Weight `N · |𝕂|²` each (`N` records, `|𝕂′| = |𝕂|²`), coins `4`, so `N / |𝕂|²` each.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

noncomputable section

/-! ## 1. Records read round `<= 1` columns only -/

/-- The coin round of VCL column `c` at `tableVCLT`. -/
def rnd (c : ℕ) : ℕ := if c < 232 then colRoundVCLE c else if c < 388 then 1 else if c = z1Col then 1 else 2

theorem tableVCLT_colRound_rnd (hC : ℕ) (j : Fin (tableVCLT hC).width) :
    (tableVCLT hC).colRound j = rnd j.1 := rfl

/-- An entry reads (its Re limbs and its Im twin) only columns of round `<= 1`. -/
def entryR1 : Entry → Bool
  | .k l => (List.range 3).all (fun j => decide (rnd (l + j) ≤ 1)) &&
      ((imColOfLimb l).elim true fun c => (List.range 3).all fun j => decide (rnd (c + j) ≤ 1))
  | .f c => decide (rnd c ≤ 1)

theorem formulaRec_R1 : ∀ i, entryR1 (formulaRec i) = true := by decide +kernel
theorem tailRec_R1 : ∀ i, entryR1 (tailRec i) = true := by decide +kernel
theorem ttRec_R1 : ∀ i, entryR1 (ttRec i) = true := by decide +kernel
theorem op0PathRec_R1 : ∀ i, entryR1 (op0PathRec i) = true := by decide +kernel
theorem op9PathRec_R1 : ∀ i, entryR1 (op9PathRec i) = true := by decide +kernel

section Agree
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

theorem entryQ_val_agree (E E' : Env F) (e : Entry) (he : entryR1 e = true)
    (hE : ∀ c, rnd c ≤ 1 → E.trace c = E'.trace c) :
    Q.val δ (entryQ F e) (gatherEnv b E) E = Q.val δ (entryQ F e) (gatherEnv b E') E' := by
  cases e with
  | k l =>
    simp only [entryR1, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at he
    obtain ⟨he1, he2⟩ := he
    show Q.val δ (qvar F VarKind.traceCur l (imColOfLimb l)) _ E = Q.val δ (qvar F VarKind.traceCur l (imColOfLimb l)) _ E'
    rw [qvar_val, qvar_val]
    have h1 : kread (gatherEnv b E) VarKind.traceCur l = kread (gatherEnv b E') VarKind.traceCur l := by
      simp only [kread, gatherEnv, LogUp.limbVal]
      exact Finset.sum_congr rfl fun j _ => by rw [hE (l + j) (he1 j j.isLt)]
    have h2 : imVal (kread (gatherEnv b E) VarKind.traceCur) (imColOfLimb l) =
        imVal (kread (gatherEnv b E') VarKind.traceCur) (imColOfLimb l) := by
      cases hc : imColOfLimb l with
      | none => rfl
      | some c =>
        rw [hc] at he2
        simp only [Option.elim, List.all_eq_true, List.mem_range, decide_eq_true_eq] at he2
        simp only [imVal, kread, gatherEnv, LogUp.limbVal]
        exact Finset.sum_congr rfl fun j _ => by rw [hE (c + j) (he2 j j.isLt)]
    rw [h1, h2]
  | f c =>
    simp only [entryR1, decide_eq_true_eq] at he
    show Q.val δ (qlift F (.var .traceCur c)) _ E = Q.val δ (qlift F (.var .traceCur c)) _ E'
    simp [qlift, Q.val, MixedExpr.eval, CoeffExpr.eval, hE c he]

theorem recQ0_val_agree (E E' : Env F) (hE : ∀ c, rnd c ≤ 1 → E.trace c = E'.trace c) (c : Fin 11) :
    Q.val δ (recQ0 F c) (gatherEnv b E) E = Q.val δ (recQ0 F c) (gatherEnv b E') E' := by
  unfold recQ0
  split
  · exact entryQ_val_agree δ b E E' _ (formulaRec_R1 _) hE
  · simp [qconst, Q.val, MixedExpr.eval]

theorem recValQ_agree (E E' : Env F) (hE : ∀ c, rnd c ≤ 1 → E.trace c = E'.trace c) {m : ℕ}
    (r : Fin m → Entry) (hr : ∀ i, entryR1 (r i) = true) :
    recValQ δ (gatherEnv b E) E r = recValQ δ (gatherEnv b E') E' r :=
  funext fun i => entryQ_val_agree δ b E E' _ (hr i) hE

end Agree

/-! ## 2. The record lists, read off the committed trace -/

section Lists
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

/-- The raw VCL row environment of the committed trace at compute node `i` (records read no challenge / public). -/
def rowEnvT (V : VerifierData F K hC S) (Q : Fin (tableVCLT hC).width → F[X]) (i : Fin V.N) : Env F :=
  Reify.envOfTrace Q V.orbitC.ω (V.computeNodes i) (fun _ => 0) (fun _ => 0)

theorem rowEnvT_agree (V : VerifierData F K hC S) {Q Q' : Fin (tableVCLT hC).width → F[X]} (h : AgreeT Q Q')
    (i : Fin V.N) : ∀ c, rnd c ≤ 1 → (rowEnvT V Q i).trace c = (rowEnvT V Q' i).trace c := by
  intro c hc
  simp only [rowEnvT, Reify.envOfTrace]
  split_ifs with hw
  · rw [h ⟨c, hw⟩ (by rw [tableVCLT_colRound_rnd]; exact hc)]
  · rfl

/-- The records of kind `f` at the rows selected by `p`. -/
def recList {m : ℕ} (V : VerifierData F K hC S) (p : Fin V.N → Bool)
    (f : Env F → Fin m → Quad (algebraMap F K δ)) (Q : Fin (tableVCLT hC).width → F[X]) :
    List (Fin m → Quad (algebraMap F K δ)) :=
  ((List.finRange V.N).filter p).map fun i => f (rowEnvT V Q i)

theorem recList_agree {m : ℕ} (V : VerifierData F K hC S) (p : Fin V.N → Bool)
    (f : Env F → Fin m → Quad (algebraMap F K δ))
    (hf : ∀ E E' : Env F, (∀ c, rnd c ≤ 1 → E.trace c = E'.trace c) → f E = f E')
    {Q Q' : Fin (tableVCLT hC).width → F[X]} (h : AgreeT Q Q') :
    recList δ V p f Q = recList δ V p f Q' := by
  unfold recList
  exact List.map_congr_left fun i _ => hf _ _ (rowEnvT_agree V h i)

theorem recList_length_le {m : ℕ} (V : VerifierData F K hC S) (p : Fin V.N → Bool)
    (f : Env F → Fin m → Quad (algebraMap F K δ)) (Q : Fin (tableVCLT hC).width → F[X]) :
    (recList δ V p f Q).length ≤ V.N := by
  unfold recList
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem mem_recList {m : ℕ} (V : VerifierData F K hC S) (p : Fin V.N → Bool)
    (f : Env F → Fin m → Quad (algebraMap F K δ)) (Q : Fin (tableVCLT hC).width → F[X]) (i : Fin V.N)
    (hi : p i = true) : f (rowEnvT V Q i) ∈ recList δ V p f Q := by
  unfold recList
  exact List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_finRange i, hi⟩, rfl⟩

/-- The five record readers. -/
def fRec0 : Env F → Fin 11 → Quad (algebraMap F K δ) :=
  fun E c => Q.val δ (recQ0 F c) (gatherEnv b E) E
def fRecOf {m : ℕ} (r : Fin m → Entry) : Env F → Fin m → Quad (algebraMap F K δ) :=
  fun E => recValQ δ (gatherEnv b E) E r

end Lists

/-! ## 3. A pole summand whose record list is read off the committed trace -/

section PoleTr
variable {Φ : CoinFrame} {K Kio : Type} [Field K] [Fintype K] [DecidableEq K] [Field Kio] [Fintype Kio]
  [DecidableEq Kio] {Tr : Type} {Staged : (Coins Φ K → Tr) → Prop}

open Classical in
/-- **A pole summand over a trace-read record list**: the IO coins hit a pole of one of the records
`recs tr χ`; along a staged strategy the list reads only the coins `dep` (disjoint from the IO coins). -/
def poleSummandTr (I : IOCoinSpec Φ K Kio) (dep : Finset (Fin Φ.n)) (hd : Disjoint I.dep dep) {m : ℕ}
    (len : ℕ) (recs : Tr → Coins Φ K → List (Fin m → Kio)) (hlen : ∀ tr χ, (recs tr χ).length ≤ len)
    (hreads : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ dep (fun χ => recs (Q χ) χ)) :
    BadSummand Φ K Tr Staged where
  coins := I.dep
  dep := dep
  disj := hd
  badSet tr χ := Finset.univ.filter fun v : I.dep → K => I.pair (extIO I v) ∈ poleBad (recs tr χ)
  weight := len * Fintype.card Kio
  card_le tr χ := by
    refine le_trans (Finset.card_le_card_of_injOn (fun v => I.pair (extIO I v)) ?_ ?_)
      ((poleBad_card_le (recs tr χ)).trans (Nat.mul_le_mul_right _ (hlen tr χ)))
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
      exact hv
    · intro v _ v' _ h; exact extIO_inj I h
  readsOn Q hQ χ χ' hdep := by
    show (Finset.univ.filter fun v : I.dep → K => I.pair (extIO I v) ∈ poleBad (recs (Q χ) χ)) =
      Finset.univ.filter fun v : I.dep → K => I.pair (extIO I v) ∈ poleBad (recs (Q χ') χ')
    have e : recs (Q χ) χ = recs (Q χ') χ' := hreads Q hQ χ χ' hdep
    rw [e]

theorem poleSummandTr_mem (I : IOCoinSpec Φ K Kio) (dep : Finset (Fin Φ.n)) (hd : Disjoint I.dep dep)
    {m : ℕ} (len : ℕ) (recs : Tr → Coins Φ K → List (Fin m → Kio)) (hlen : ∀ tr χ, (recs tr χ).length ≤ len)
    (hreads : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ dep (fun χ => recs (Q χ) χ))
    (tr : Tr) (χ : Coins Φ K) :
    (poleSummandTr I dep hd len recs hlen hreads (Staged := Staged)).mem tr χ ↔
      I.pair χ ∈ poleBad (recs tr χ) := by
  classical
  unfold BadSummand.mem
  show (fun i : I.dep => χ i) ∈
      (Finset.univ.filter fun v : I.dep → K => I.pair (extIO I v) ∈ poleBad (recs tr χ)) ↔ _
  rw [Finset.mem_filter, pair_extIO]
  simp

/-- **Decode**: outside the summand, no record of the list has a zero denominator at the IO coins. -/
theorem poleSummandTr_ne (I : IOCoinSpec Φ K Kio) (dep : Finset (Fin Φ.n)) (hd : Disjoint I.dep dep)
    {m : ℕ} (len : ℕ) (recs : Tr → Coins Φ K → List (Fin m → Kio)) (hlen : ∀ tr χ, (recs tr χ).length ≤ len)
    (hreads : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ dep (fun χ => recs (Q χ) χ))
    (tr : Tr) (χ : Coins Φ K)
    (hno : ¬ (poleSummandTr I dep hd len recs hlen hreads (Staged := Staged)).mem tr χ) :
    ∀ v ∈ recs tr χ, FiniteIO.compress (I.ioCoins χ) v ≠ 0 := by
  classical
  rw [poleSummandTr_mem] at hno
  intro v hv h0
  apply hno
  simp only [poleBad, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨v, hv, h0⟩

end PoleTr

/-! ## 4. The five summands at the tower -/

section Summands
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

theorem disj_io_depB1 : Disjoint (ioSpecVCLQuad (algebraMap F K δ)).dep depB1 := by
  show Disjoint ({ioγVCL.1, ioγVCL.2, ioρVCL.1, ioρVCL.2} : Finset (Fin frameVCL.n)) depB1
  unfold depB1 ioγVCL ioρVCL
  decide

/-- **The pole summand of one record kind**: `f` the reader, `p` the row selector, over the committed compute
trace of `tr`. -/
def sumPoleT {m : ℕ} (V : VerifierData F K hC S) (p : Fin V.N → Bool)
    (f : Env F → Fin m → Quad (algebraMap F K δ))
    (hf : ∀ E E' : Env F, (∀ c, rnd c ≤ 1 → E.trace c = E'.trace c) → f E = f E') : TSummand F K hC S :=
  poleSummandTr (ioSpecVCLQuad (algebraMap F K δ)) depB1 (disj_io_depB1 δ) V.N
    (fun tr _ => recList δ V p f tr.1) (fun tr _ => recList_length_le δ V p f tr.1)
    (fun Q hQ χ χ' h => recList_agree δ V p f hf (agree_of_depB1_T hQ h))

/-- Weight of each pole summand: `N · |𝕂′| = N · |𝕂|²`. -/
theorem sumPoleT_weight {m : ℕ} (V : VerifierData F K hC S) (p : Fin V.N → Bool)
    (f : Env F → Fin m → Quad (algebraMap F K δ)) (hf) :
    (sumPoleT δ V p f hf).weight = V.N * (Fintype.card K * Fintype.card K) := by
  show V.N * Fintype.card (Quad (algebraMap F K δ)) = _
  rw [quad_card, sq]

theorem sumPoleT_coins {m : ℕ} (V : VerifierData F K hC S) (p : Fin V.N → Bool)
    (f : Env F → Fin m → Quad (algebraMap F K δ)) (hf) : (sumPoleT δ V p f hf).coins.card = 4 :=
  ioSpecVCL_dep_card (Quad.mk (algebraMap F K δ)) (quadMk_inj (algebraMap F K δ))

variable (V : VerifierData F K hC S) (st : Fin V.N → ℕ)

theorem hf0 : ∀ E E' : Env F, (∀ c, rnd c ≤ 1 → E.trace c = E'.trace c) →
    fRec0 δ V.basis E = fRec0 δ V.basis E' :=
  fun E E' h => funext fun c => recQ0_val_agree δ V.basis E E' h c

theorem hfOf {m : ℕ} (r : Fin m → Entry) (hr : ∀ i, entryR1 (r i) = true) :
    ∀ E E' : Env F, (∀ c, rnd c ≤ 1 → E.trace c = E'.trace c) →
      fRecOf δ V.basis r E = fRecOf δ V.basis r E' :=
  fun E E' h => recValQ_agree δ V.basis E E' h r hr

def sumPole0 : TSummand F K hC S := sumPoleT δ V (fun _ => true) (fRec0 δ V.basis) (hf0 δ V)
def sumPole1 : TSummand F K hC S :=
  sumPoleT δ V (fun i => decide (st i = 0)) (fRecOf δ V.basis op0PathRec) (hfOf δ V _ op0PathRec_R1)
def sumPole2 : TSummand F K hC S :=
  sumPoleT δ V (fun i => decide (st i ∈ slot1ExportSels)) (fRecOf δ V.basis tailRec) (hfOf δ V _ tailRec_R1)
def sumPole3 : TSummand F K hC S :=
  sumPoleT δ V (fun i => decide (st i = 6)) (fRecOf δ V.basis ttRec) (hfOf δ V _ ttRec_R1)
def sumPole4 : TSummand F K hC S :=
  sumPoleT δ V (fun i => decide (st i = 9)) (fRecOf δ V.basis op9PathRec) (hfOf δ V _ op9PathRec_R1)

/-- **The pole summands**. -/
def sumPolesT : List (TSummand F K hC S) :=
  [sumPole0 δ V, sumPole1 δ V st, sumPole2 δ V st, sumPole3 δ V st, sumPole4 δ V st]

/-- Common form of the five decodes: at the raw row environment `E` of the committed trace (any challenge / public
maps, challenges the tower ones), the compressed record at `coinsQ` is nonzero. -/
theorem compress_rec_ne {m : ℕ} (p : Fin V.N → Bool) (f : Env F → Fin m → Quad (algebraMap F K δ)) (hf)
    (tr : Traces F (tableVCLT hC) S) (χ : Coins frameVCL K)
    (hno : ¬ (sumPoleT δ V p f hf).mem tr χ) (i : Fin V.N) (hi : p i = true)
    (cv pv : ℕ → F)
    (hch : (Reify.envOfTrace tr.1 V.orbitC.ω (V.computeNodes i) cv pv).chal = chalVQ7T δ V.basis χ)
    (g : Env F → Fin m → Quad (algebraMap F K δ))
    (hg : g (Reify.envOfTrace tr.1 V.orbitC.ω (V.computeNodes i) cv pv) = f (rowEnvT V tr.1 i)) :
    FiniteIO.compress (coinsQ δ (gatherEnv V.basis (Reify.envOfTrace tr.1 V.orbitC.ω (V.computeNodes i) cv pv))
      (Reify.envOfTrace tr.1 V.orbitC.ω (V.computeNodes i) cv pv))
      (g (Reify.envOfTrace tr.1 V.orbitC.ω (V.computeNodes i) cv pv)) ≠ 0 := by
  rw [coinsQ_chalVQ7T δ V.basis χ _ hch, hg]
  exact poleSummandTr_ne _ _ _ _ _ _ _ tr χ hno _ (mem_recList δ V p f tr.1 i hi)

end Summands

/-! ## 5. The list `honestBadCF` and its decode -/

section All
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **`honestBadCF`**: SeedGood, rlc5, the `χ0` order, and the five pole summands of the honest tower strategy. -/
def honestBadCF (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (wS : ℕ) (hwS : (badSeedsT δ t).card ≤ wS)
    (wR : ℕ) (hwR : (bfsForest [airReorder t]).length * (Fintype.card K * Fintype.card K) ≤ wR)
    (h : ℕ) (hh : 1 ≤ h) (V : VerifierData F K hC S) (st : Fin V.N → ℕ) : List (TSummand F K hC S) :=
  [sumSeedGoodT δ t wS hwS, sumRlc5T δ t wR hwR, sumOrdT h hh] ++ sumPolesT δ V st

/-- **The total weight, as a formula**:
`ε = wS/|𝕂|² + wR/|𝕂|³ + h²/|𝕂| + 5·N·|𝕂|²/|𝕂|⁴`, with `wS = 1 + R·3(2Λ−1)`, `wR = nR·|𝕂|²`
(so `= 1/|𝕂|² + 3R(2Λ−1)/|𝕂|² + nR/|𝕂| + h²/|𝕂| + 5N/|𝕂|²`). -/
theorem epsilon_honestBadCF (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (wS : ℕ)
    (hwS : (badSeedsT δ t).card ≤ wS) (wR : ℕ)
    (hwR : (bfsForest [airReorder t]).length * (Fintype.card K * Fintype.card K) ≤ wR)
    (h : ℕ) (hh : 1 ≤ h) (V : VerifierData F K hC S) (st : Fin V.N → ℕ) :
    epsilonOf (honestBadCF (hC := hC) (S := S) δ t wS hwS wR hwR h hh V st) =
      (wS : ℚ) / (Fintype.card K : ℚ) ^ 2 + (wR : ℚ) / (Fintype.card K : ℚ) ^ 3 +
        ((h * h : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 1 +
        5 * ((V.N * (Fintype.card K * Fintype.card K) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 4 := by
  have c1 : (sumSeedGoodT (hC := hC) (S := S) δ t wS hwS).coins.card = 2 := by
    show ({⟨2, by decide⟩, ⟨3, by decide⟩} : Finset (Fin frameVCL.n)).card = 2
    decide
  have c2 : (sumRlc5T (hC := hC) (S := S) δ t wR hwR).coins.card = 3 := by
    show ({⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩} : Finset (Fin frameVCL.n)).card = 3
    decide
  have c3 : (sumOrdT (hC := hC) (S := S) (F := F) (K := K) h hh).coins.card = 1 := by
    show ({⟨0, by decide⟩} : Finset (Fin frameVCL.n)).card = 1
    simp
  unfold epsilonOf honestBadCF sumPolesT
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [c1, c2, c3]
  show _ = _
  simp only [sumPole0, sumPole1, sumPole2, sumPole3, sumPole4, sumPoleT_coins, sumPoleT_weight]
  show (wS : ℚ) / _ + ((wR : ℚ) / _ + (((h * h : ℕ) : ℚ) / _ + _)) = _
  push_cast
  ring

/-- **Decode of the whole list**: outside every summand, at the coin vector `χ` and committed traces `tr`,
the seed is good, `rlc5` holds at every generated row, `h ≤ orderOf (ι χ0)`, and every pole condition of
C3's honest gates holds at the raw row environment (challenges the tower ones). -/
theorem honestBadCF_decode (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (wS : ℕ)
    (hwS : (badSeedsT δ t).card ≤ wS) (wR : ℕ)
    (hwR : (bfsForest [airReorder t]).length * (Fintype.card K * Fintype.card K) ≤ wR)
    (h : ℕ) (hh : 1 ≤ h) (V : VerifierData F K hC S) (st : Fin V.N → ℕ)
    (tr : Traces F (tableVCLT hC) S) (χ : Coins frameVCL K)
    (hno : ∀ s ∈ honestBadCF (hC := hC) (S := S) δ t wS hwS wR hwR h hh V st, ¬ s.mem tr χ) :
    (zQuad δ χ ≠ 0 ∧ SeedGood (zQuad δ χ) t) ∧
    (∀ (αs : Quad (algebraMap F K δ)) {fuel : ℕ} {subject formula result : Noun}
      (hgen : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
      {i : ℕ} (hi : i ∈ List.range' 1 (bfsForest [airReorder t]).length),
      Nock.ComputeTable.Vcomp ⟨αs, zQuad δ χ, algebraMap K (Quad (algebraMap F K δ)) (χ ⟨8, by decide⟩),
          algebraMap K _ (χ ⟨9, by decide⟩), algebraMap K _ (χ ⟨10, by decide⟩)⟩
        (renderNode (zQuad δ χ) αs (bfsLabelAt (airReorder t) i)).row.2.2.1
        (renderNode (zQuad δ χ) αs (bfsLabelAt (airReorder t) i)).row.2.2.2 ∧
      Nock.ComputeTable.WF ⟨αs, zQuad δ χ, algebraMap K (Quad (algebraMap F K δ)) (χ ⟨8, by decide⟩),
          algebraMap K _ (χ ⟨9, by decide⟩), algebraMap K _ (χ ⟨10, by decide⟩)⟩
        (renderNode (zQuad δ χ) αs (bfsLabelAt (airReorder t) i)).row.2.2.1) ∧
    (∀ {K' : Type} [Field K'] [Algebra K K'], h ≤ orderOf (algebraMap K K' (χ ⟨0, by decide⟩))) ∧
    (∀ (i : Fin V.N) (cv pv : ℕ → F),
      (Reify.envOfTrace tr.1 V.orbitC.ω (V.computeNodes i) cv pv).chal = chalVQ7T δ V.basis χ →
      let E := Reify.envOfTrace tr.1 V.orbitC.ω (V.computeNodes i) cv pv
      den0Q δ (gatherEnv V.basis E) E ≠ 0 ∧
      (st i = 0 → FiniteIO.compress (coinsQ δ (gatherEnv V.basis E) E)
        (recValQ δ (gatherEnv V.basis E) E op0PathRec) ≠ 0) ∧
      (st i ∈ slot1ExportSels → FiniteIO.compress (coinsQ δ (gatherEnv V.basis E) E)
        (recValQ δ (gatherEnv V.basis E) E tailRec) ≠ 0) ∧
      (st i = 6 → FiniteIO.compress (coinsQ δ (gatherEnv V.basis E) E)
        (recValQ δ (gatherEnv V.basis E) E ttRec) ≠ 0) ∧
      (st i = 9 → FiniteIO.compress (coinsQ δ (gatherEnv V.basis E) E)
        (recValQ δ (gatherEnv V.basis E) E op9PathRec) ≠ 0)) := by
  have mS := hno (sumSeedGoodT (hC := hC) (S := S) δ t wS hwS) (by simp [honestBadCF])
  have mR := hno (sumRlc5T (hC := hC) (S := S) δ t wR hwR) (by simp [honestBadCF])
  have mO := hno (sumOrdT (hC := hC) (S := S) h hh) (by simp [honestBadCF])
  rw [sumSeedGoodT_mem] at mS
  rw [sumRlc5T_mem] at mR
  rw [sumOrdT_mem] at mO
  have hseed := seedGood_of_not_mem δ t χ mS
  refine ⟨hseed, ?_, ?_, ?_⟩
  · intro αs fuel subject formula result hgen i hi
    exact gen_vcomp_wf (zQuad δ χ) αs _ _ _ hseed.1 hgen hseed.2 hi (rlc5_of_not_mem δ t χ mR αs hi)
  · intro K' _ _
    exact hord_of_not_mem h _ mO
  · intro i cv pv hch E
    have hz : ∀ {m : ℕ} (r : Fin m → Entry) (hr : ∀ j, entryR1 (r j) = true),
        recValQ δ (gatherEnv V.basis E) E r = fRecOf δ V.basis r (rowEnvT V tr.1 i) := fun r hr =>
      hfOf δ V r hr _ _ (fun c _ => rfl)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := compress_rec_ne δ V (fun _ => true) (fRec0 δ V.basis) (hf0 δ V) tr χ
        (hno _ (by simp [honestBadCF, sumPolesT, sumPole0])) i rfl cv pv hch
        (fun E => fRec0 δ V.basis E) (hf0 δ V _ _ (fun c _ => rfl))
      exact this
    · intro hs
      exact compress_rec_ne δ V (fun i => decide (st i = 0)) (fRecOf δ V.basis op0PathRec)
        (hfOf δ V _ op0PathRec_R1) tr χ (hno _ (by simp [honestBadCF, sumPolesT, sumPole1])) i
        (by simpa using hs) cv pv hch (fRecOf δ V.basis op0PathRec) (hz _ op0PathRec_R1 ▸ rfl)
    · intro hs
      exact compress_rec_ne δ V (fun i => decide (st i ∈ slot1ExportSels)) (fRecOf δ V.basis tailRec)
        (hfOf δ V _ tailRec_R1) tr χ (hno _ (by simp [honestBadCF, sumPolesT, sumPole2])) i
        (by simpa using hs) cv pv hch (fRecOf δ V.basis tailRec) (hz _ tailRec_R1 ▸ rfl)
    · intro hs
      exact compress_rec_ne δ V (fun i => decide (st i = 6)) (fRecOf δ V.basis ttRec)
        (hfOf δ V _ ttRec_R1) tr χ (hno _ (by simp [honestBadCF, sumPolesT, sumPole3])) i
        (by simpa using hs) cv pv hch (fRecOf δ V.basis ttRec) (hz _ ttRec_R1 ▸ rfl)
    · intro hs
      exact compress_rec_ne δ V (fun i => decide (st i = 9)) (fRecOf δ V.basis op9PathRec)
        (hfOf δ V _ op9PathRec_R1) tr χ (hno _ (by simp [honestBadCF, sumPolesT, sumPole4])) i
        (by simpa using hs) cv pv hch (fRecOf δ V.basis op9PathRec) (hz _ op9PathRec_R1 ▸ rfl)

end All

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
