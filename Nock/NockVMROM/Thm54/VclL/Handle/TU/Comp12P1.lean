/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/Comp12P1.lean

 **Trace uniqueness on the P1 fragment: the compute rounds 1 and 2 from `comp_cols_eq`, at a coin outside the
 events.**

 * §1 the slot factor `N = Σ act·den (+ flag·den_a·den_b)` of `RoundsCompP1.slotNQ` in closed form (`slotNQ_val`),
 the right-hand side `M` (`slotMQ_val`) and the total activity (`actTot_val`); `slotN_ne`: at a one-hot row whose
 base gates and slot gate hold, an active slot has `N ≠ 0` as soon as its pair denominators are nonzero when the
 pair flag is set. (Without the pair flag `inv·N = M = Σ act ≠ 0`; with it every entry is inactive and
 `N = den_a·den_b`.)
 * §2 on an accepted `computeChipVCLHX` trace: the `hN` of `comp_cols_eq` from the nonzero pair denominators
 (`hN_of_den`), hence from nonzero compute request denominators (`hN_of_reqs`, through `DenXJ8.hden_of_reqs`).
 * §3 at the J-8 verifier: the compute request denominators are nonzero outside the three handle IO events
 (`hne_J8`); the `pubIC` limbs agree, and the `pubSeed` limbs agree when the claim serials of the cell claim nouns
 agree (`pubs_low_eq`); `comp_rows_eq`: two `AcceptsJ8V` traces with `canonC2`, equal round-0 compute columns,
 equal claim serials and nonzero compute request denominators on the first trace have equal compute columns.
 * §4 at the absent-atom-walk data of `LinkJ8A.probJ8V_absent` (`krootsV = 0`): outside `allJ8X` the compute request
 denominators are nonzero (`hne_absent`); **`trace_unique_good''`**: `trace_unique_good'` with `hcomp12`
 discharged, its remaining hypotheses the fields of `OpenP1`.

 `Comp12P1` itself (quantified over every pair of accepted traces, with no coin condition) is not derived: a row whose
 pair flag is set and whose two pair denominators both vanish satisfies its slot gate at every inverse, so the
 per-trace event is needed (`comp_rows_eq` takes it as `hne`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCompP1
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc notC selS pubIC pubSeed mapC)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (sumQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (rEF envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf compReqsX)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX reqsOf MsgJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe realize40)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X withFpxV)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 pubVJ8 chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3G (realizeG)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4 (LL4)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (RR4A toMsgJ8ZA acceptsJ8ZA_of_V budX_ofZA budP_ofZA budS_ofZA)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (rdX_realIO rdP_real40)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRoundsP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCompP1 (slotNQ slotMQ slotGate_eq comp_cols_eq)

/-! ## 1. The slot factor in closed form -/

section Slot
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- **The slot factor `N`**: `Σ act·den` over the entries plus `flag·den_a·den_b`. -/
theorem slotNQ_val (S : SlotX ℚ) (eK : Env K) (eF : Env F) :
    Q.val δ (slotNQ δ (castSlotX S)) eK eF =
      (S.ents.map fun x => algebraMap F 𝕂′ (evalQX x.act eF) * DX δ eK eF x.rcd).sum +
        algebraMap F 𝕂′ (pairFX eF S) * (pairDaX δ eK eF S * pairDbX δ eK eF S) := by
  have hents : Q.val δ (sumQ F ((castSlotX (F := F) S).ents.map fun x =>
      qmul F δ (qlift F x.act) (denQX F δ x.rcd))) eK eF =
      (S.ents.map fun x => algebraMap F 𝕂′ (evalQX x.act eF) * DX δ eK eF x.rcd).sum := by
    rw [ComputeSatHQ.sumQ_val]
    simp only [castSlotX, List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp, qmul_val, qlift_val, castEntX_act]
    rfl
  unfold slotNQ
  rw [qadd_val, hents]
  congr 1
  simp only [castSlotX]
  unfold pairFX pairDaX pairDbX
  cases hp : S.pair with
  | none => simp [qconst_val]
  | some q =>
    obtain ⟨fl, a, c, bl⟩ := q
    simp only [qmul_val, qlift_val, cc, CoeffExpr.eval, DX]

/-- **The slot right-hand side `M`**: `Σ act` plus `flag·(den_a + den_b)`. -/
theorem slotMQ_val (S : SlotX ℚ) (eK : Env K) (eF : Env F) :
    Q.val δ (slotMQ δ (castSlotX S)) eK eF =
      algebraMap F 𝕂′ ((S.ents.map fun x => evalQX x.act eF).sum) +
        algebraMap F 𝕂′ (pairFX eF S) * (pairDaX δ eK eF S + pairDbX δ eK eF S) := by
  have hlift : Q.val δ (qlift F (CoeffExpr.sumList (castSlotX (F := F) S).ents EntX.act)) eK eF =
      algebraMap F 𝕂′ ((S.ents.map fun x => evalQX x.act eF).sum) := by
    rw [qlift_val]; simp only [castSlotX]; rw [castEntX_sumAct]
  unfold slotMQ
  rw [qadd_val, hlift]
  congr 1
  simp only [castSlotX]
  unfold pairFX pairDaX pairDbX
  cases hp : S.pair with
  | none => simp [qconst_val]
  | some q =>
    obtain ⟨fl, a, c, bl⟩ := q
    simp only [qmul_val, qadd_val, qlift_val, cc, CoeffExpr.eval, DX]

/-- **The total activity** of a slot: `Σ act + flag`. -/
theorem actTot_val (S : SlotX ℚ) (eF : Env F) :
    (actTotX (castSlotX (F := F) S)).eval eF = (S.ents.map fun x => evalQX x.act eF).sum + pairFX eF S := by
  unfold actTotX
  simp only [CoeffExpr.eval]
  rw [show (castSlotX (F := F) S).ents = S.ents.map castEntX from rfl, castEntX_sumAct]
  congr 1
  simp only [castSlotX]
  unfold pairFX
  cases hp : S.pair with
  | none => simp [CoeffExpr.eval]
  | some q =>
    obtain ⟨fl, a, c, bl⟩ := q
    simp [cc, CoeffExpr.eval]

/-- **An active slot has a nonzero factor `N`** at a one-hot row whose base gates and slot gate hold, given nonzero
pair denominators when the pair flag is set. -/
theorem slotN_ne {eK : Env K} {eF : Env F} {j : ℕ} (hB : BaseHoldsX eF) (hOH : OneHotAt eF j)
    {S : SlotX ℚ} (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ)))
    (g : Q.val δ (slotGateQX F δ (castSlotX S)) eK eF = 0)
    (hden : pairFX eF S = 1 → pairDaX δ eK eF S ≠ 0 ∧ pairDbX δ eK eF S ≠ 0)
    (hA : (actTotX (castSlotX (F := F) S)).eval eF ≠ 0) :
    Q.val δ (slotNQ δ (castSlotX S)) eK eF ≠ 0 := by
  intro hN0
  rw [slotGate_eq, qsub_val, qmul_val, hN0, mul_zero, zero_sub, neg_eq_zero, slotMQ_val] at g
  rw [actTot_val] at hA
  rcases pairF_bool hB hOH hS with h0 | h1
  · rw [h0, map_zero, zero_mul, add_zero] at g
    rw [h0, add_zero] at hA
    exact hA ((map_eq_zero_iff _ (algebraMap F 𝕂′).injective).mp g)
  · have hz : ∀ x ∈ S.ents, evalQX x.act eF = 0 := fun x hx => by
      have := pairF_act hB hOH hS x hx
      rwa [h1, one_mul] at this
    rw [slotNQ_val, h1, map_one, one_mul] at hN0
    have hs : (S.ents.map fun x => algebraMap F 𝕂′ (evalQX x.act eF) * DX δ eK eF x.rcd).sum = 0 := by
      rw [List.map_congr_left (fun x hx => by rw [hz x hx, map_zero, zero_mul])]
      simp
    rw [hs, zero_add] at hN0
    exact mul_ne_zero (hden h1).1 (hden h1).2 hN0

end Slot

/-! ## 2. `hN` on an accepted compute trace -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
  (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- **`hN` from nonzero pair denominators**: on an accepted `computeChipVCLHX` trace (`17 < char`), every active slot
of every row has a nonzero factor `N`, given the pair denominators of `compute_balanceX`'s `hden`. -/
theorem hN_of_den (hc : nStates < ringChar F)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P)
    (hden : ∀ r < n, ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)),
      pairFX (envsN hn nodes chalV pubVal orbit P r) S = 1 →
        pairDaX δ (gatherEnv b (envsN hn nodes chalV pubVal orbit P r)) (envsN hn nodes chalV pubVal orbit P r) S ≠ 0 ∧
        pairDbX δ (gatherEnv b (envsN hn nodes chalV pubVal orbit P r)) (envsN hn nodes chalV pubVal orbit P r) S ≠ 0) :
    ∀ (i : Fin n), ∀ S ∈ (ChipHX.slotsX : List (SlotX F)),
      (actTotX S).eval (rEF nodes chalV pubVal orbit P i) ≠ 0 →
        Q.val δ (slotNQ δ S) (gatherEnv b (rEF nodes chalV pubVal orbit P i)) (rEF nodes chalV pubVal orbit P i) ≠ 0 := by
  intro i S hS
  rw [← slotsX_cast] at hS
  obtain ⟨S0, hS0, rfl⟩ := List.mem_map.mp hS
  have hB := baseX_of_sat hn nodes b δ chalV pubVal orbit P hsat (nodes i) (mem_rowNodeSet nodes i)
  have hd := hden i i.isLt S0 hS0
  have he : envsN hn nodes chalV pubVal orbit P i = rEF nodes chalV pubVal orbit P i := by
    simp only [envsN, dif_pos i.isLt]
  rw [he] at hd
  exact slotN_ne δ hB (stX_spec hB hc) hS0
    (slotX_of_sat hn nodes b δ chalV pubVal orbit P hsat (nodes i) (mem_rowNodeSet nodes i) S0 hS0) hd

/-- **`hN` from nonzero compute request denominators** (`DenXJ8.hden_of_reqs`). -/
theorem hN_of_reqs [Fintype K] (hc : nStates < ringChar F)
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P)
    (hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := hn) (nodes := nodes) (chalV := chalV) (pubVal := pubVal)
      (orbit := orbit) (P := P) bl, compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r) ≠ 0) :
    ∀ (i : Fin n), ∀ S ∈ (ChipHX.slotsX : List (SlotX F)),
      (actTotX S).eval (rEF nodes chalV pubVal orbit P i) ≠ 0 →
        Q.val δ (slotNQ δ S) (gatherEnv b (rEF nodes chalV pubVal orbit P i)) (rEF nodes chalV pubVal orbit P i) ≠ 0 :=
  hN_of_den hn nodes b δ chalV pubVal orbit P hc hsat (DenXJ8.hden_of_reqs hne)

end Chip

/-! ## 3. At the J-8 verifier -/

section J8
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The compute request denominators are nonzero outside the three handle IO events** (cell export `x`, walk path
`p`, service `s`) at the compute coins, at any provider lists. -/
theorem hne_J8 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    {px : List ((Fin (mOf .x) → 𝕂′) × 𝕂′)} {pp : List ((Fin (mOf .p) → 𝕂′) × 𝕂′)}
    {ps : List ((Fin (mOf .s) → 𝕂′) × 𝕂′)}
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) px)
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) pp)
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) ps) :
    ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
      (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
      (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r) ≠ 0 := by
  intro bl r hr
  cases bl with
  | s => exact TeleC.den_ne_of_out _ _ _ _ hs _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  | x => exact TeleC.den_ne_of_out _ _ _ _ hx _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  | p => exact TeleC.den_ne_of_out _ _ _ _ hpp _ (List.mem_map_of_mem (List.mem_append_left _ hr))

/-- The claim handles agree when the claim serials of the cell claim nouns agree. -/
theorem claimH_eq (c : P8PublicClaim) {m m' : ClaimMsgVS}
    (hm : ∀ k, isCellN (claimNoun c k) = true → (m k).1 = (m' k).1) (k : Fin 3) : claimH c m k = claimH c m' k := by
  unfold claimH claimHandle
  cases hc : claimNoun c k with
  | atom v => rfl
  | cell a a' => rw [hm k (by rw [hc]; rfl)]

/-- **The compute publics `0 .. 11` agree** (the claim label, `pubIC = αW`, `pubSeed`) when the claim serials of the
cell claim nouns agree: they are functions of the claim, those serials and the coin. -/
theorem pubs_low_eq (c : P8PublicClaim) (χ : Coins frameJ8 K) {M M' : MsgJ8' p K δ}
    (hm : ∀ k, isCellN (claimNoun c k) = true → (M.m k).1 = (M'.m k).1) :
    ∀ j < 12, pubVJ8 δ b c M.m M.ρ M.ρS χ j = pubVJ8 δ b c M'.m M'.ρ M'.ρS χ j := by
  intro j hj
  have hlab : labelF (F := ZMod p) c M.m = labelF c M'.m := by
    simp only [labelF, claimH_eq c hm 0, claimH_eq c hm 1, claimH_eq c hm 2]
  have h27 : j < 27 := by omega
  have h21 : j < 21 := by omega
  simp only [pubVJ8, pubVHQ, if_pos h27, if_pos h21]
  unfold pubVH seedVS
  rw [hlab]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- **The compute columns are determined by round 0** (pointwise `Comp12P1`): two `AcceptsJ8V` traces at one layout,
claim and coin, both with `canonC2`, equal round-0 compute columns and equal claim serials, and nonzero compute request
denominators on the first trace, have equal compute columns at every row. -/
theorem comp_rows_eq {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h' : AcceptsJ8V δ b Pb Rg c χ M' tr' r g)
    (hC2 : (canonC2 b Pb).Satisfies (sideC2Q tr)) (hC2' : (canonC2 b Pb).Satisfies (sideC2Q tr'))
    (hp : 17 < p)
    (hne : ∀ bl, ∀ x ∈ compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
      (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
      (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x) ≠ 0)
    (hm : ∀ k, isCellN (claimNoun c k) = true → (M.m k).1 = (M'.m k).1)
    (h0 : ∀ j : Fin 123, (j : ℕ) < 69 → ∀ i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i)) :
    ∀ j i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i) := by
  have hc : nStates < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hN := hN_of_reqs Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
    (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) hc h.hsatX hne
  have hpub := pubs_low_eq δ b c χ hm
  have hr0 : ∀ (i : Fin Pb.n) (j : ℕ), j < 69 →
      (rEF Pb.nodes (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
        (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) i).trace j =
      (rEF Pb.nodes (chalVJ8 b χ) (pubVJ8 δ b c M'.m M'.ρ M'.ρS χ) Pb.orbit
        (qX δ b Pb tr' (chalVJ8 b χ) (pubVJ8 δ b c M'.m M'.ρ M'.ρS χ)) i).trace j := by
    intro i j hj
    rw [envOfTrace_trace (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) _ _ _ _
        (show j < 123 by omega),
      envOfTrace_trace (qX δ b Pb tr' (chalVJ8 b χ) (pubVJ8 δ b c M'.m M'.ρ M'.ρS χ)) _ _ _ _
        (show j < 123 by omega)]
    exact h0 ⟨j, by omega⟩ hj i
  have key := comp_cols_eq Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)
    (pubVJ8 δ b c M'.m M'.ρ M'.ρS χ) Pb.orbit
    (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
    (qX δ b Pb tr' (chalVJ8 b χ) (pubVJ8 δ b c M'.m M'.ρ M'.ρS χ))
    h.hsatX h'.hsatX h.hsatX.2 h'.hsatX.2 h.hinjX h.hadjX
    (sideC2Q tr) hC2 (fun j hj => rfl) (sideC2Q tr') hC2' (fun j hj => rfl) hr0
    (fun k hk => hpub _ (by simp only [pubIC]; omega)) (fun k hk => hpub _ (by simp only [pubSeed]; omega)) hN
  intro j i
  have := key i j j.isLt
  rwa [envOfTrace_trace (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) _ _ _ _ j.isLt,
    envOfTrace_trace (qX δ b Pb tr' (chalVJ8 b χ) (pubVJ8 δ b c M'.m M'.ρ M'.ρS χ)) _ _ _ _ j.isLt] at this

end J8

/-! ## 4. At the absent-atom-walk data: the events and the uniqueness core -/

section Absent
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The event data of `LinkJ8A.probJ8V_absent` (`krootsV = 0`), at any `R0`, `L0` and layout. -/
abbrev dataA (Pb : PubJ8 p) (c : P8PublicClaim)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P (g + r.N) :=
  withFpxV δ b (withLiftC (RR4A δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) (LL4 δ b L0 Pb skel hs hL))
    Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA

/-- **Outside `allJ8X` at the absent data, the compute request denominators are nonzero**: the readouts of the three
handle IO events at the trace (`rdX_realIO`, `rdP_real40`, `rdS_A`) at their budgets (`budX/P/S_ofZA`). -/
theorem hne_absent (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hp17 : 17 < p) {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    (hacc3 : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h0 : Pb.krootsV = 0)
    (hout : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr χ) :
    ∀ bl, ∀ x ∈ compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
      (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
      (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x) ≠ 0 := by
  have hacc := acceptsJ8ZA_of_V hacc3 h0
  have hB := hacc3.hbud
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hout
  have rX := rdX_realIO δ b (realizeG δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg) Pb c χ
    (toMsgJ8ZA δ b Pb c χ M tr) tr
  have rS := AbsentVJ8.rdS_A δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg χ (toMsgJ8ZA δ b Pb c χ M tr) tr
  have rP := rdP_real40 δ b (realize40 δ b L0 (layPb Pb skel hs) hL) Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr
  have bX := budX_ofZA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr hacc hp17 hB
  have bP := budP_ofZA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr hacc hp17 hB
  have bS := budS_ofZA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr hacc hp17 hB
  have hx := ListJ8C.hout_x_of_outsideC _ b hoC _ _ rX.1 rX.2 bX.1 bX.2
  have hpp := ListJ8C.hout_p_of_outside40C _ _ b hoC _ _ rP.1 rP.2 bP.1 bP.2
  have hss := ListJ8C.hout_s_of_outsideC _ b hoC _ _ rS.1 rS.2 bS.1 bS.2
  exact hne_J8 δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr hx hpp hss

/-- **`trace_unique_good''`: the uniqueness core with the compute rounds discharged.** Two tuples accepted by
`AcceptsCanon2` at one claim `c`, layout `Pb` with no atom walk (`krootsV = 0`), registry and coin `χ`, with `χ` outside
every event of `allJ8X` at the absent data (`dataA`, the data of `LinkJ8A.probJ8V_absent`) at the first trace, are
equal, given the open facts `O`. -/
theorem trace_unique_good'' {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim}
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (h0 : Pb.krootsV = 0)
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hg : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr χ)
    (O : OpenP1 δ b Pb c χ M M' tr tr' ax ax') :
    (tr, ax, M) = (tr', ax', M') := by
  obtain ⟨⟨hA, hC⟩, hC2⟩ := h
  obtain ⟨⟨hA', hC'⟩, hC2'⟩ := h'
  have hp17 : 17 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  -- step 0: the layout constants
  have hJ0 : Pb.nJ = 0 := by rw [hC.hPb]; exact (canonPb_consts hpG sz c).1
  -- the compute rounds 1, 2 (the handle IO events give the slot factors)
  have hcomp := comp_rows_eq δ b hA hA' hC2 hC2' hp17
    (hne_absent δ b Pb c R0 L0 skel hs hL hP hnM hreg hp17 hA h0 hg) O.claim O.r0C
  -- steps 8, 9: the atom, cell and walk tables and their publics
  obtain ⟨hAr, pA⟩ := atom_rows_eq δ b hA hA' hC.hApad hC'.hApad (yA_of_outside δ hg)
  obtain ⟨hM, pC⟩ := cell_rows_eq' δ b hA hA' (two63_lt_ringChar hpG) (zC_of_outside δ rfl hg)
    O.servedC O.servedC' O.r0M
  obtain ⟨hW, pW⟩ := walk_rows_eq' δ b hA hA' (walk_round0_poly hA.hinjW hC.hdeg hC'.hdeg O.r0W) O.r1W
  have hrows : RowsEqP1 Pb tr tr' := ⟨hcomp, hM, hW, hAr⟩
  -- step 11: the degree lift
  have htr : tr = tr' := tr_eq_of_rows hC.hdeg hC'.hdeg hJ0 hC.hV0 hC'.hV0 hA.hinjX hA.hinjC hA.hinjW hA.hinjA hrows
  have hax : ax = ax' := aux_eq_of_rows hC.hdeg hC'.hdeg hA.hinjC hA.hinjW O.auxM O.auxW
  subst htr hax
  -- step 10: the message
  have hMe := RoundsP1.msg_eq δ b hA hA' hC.hmsg hC'.hmsg O.claim pC pW pA
  rw [hMe]

end Absent

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1.slotN_ne
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1.hN_of_den
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1.hN_of_reqs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1.hne_J8
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1.pubs_low_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1.comp_rows_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1.hne_absent
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1.trace_unique_good''
