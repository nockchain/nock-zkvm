import Nock.NockVMROM.Thm54.VclL.Compute.AccChip
import Nock.NockVMROM.Thm54.P8Core.SVFrame.MemSoundnessFamily

/-!
# V4T : the chip enforces the verifier's row checks — `reqFacts` with no `Checks`

.  `CompSoundnessFamily.reqFacts`
receives no `VerifierData.Checks`, so the compute chip of a verifier datum itself checks the row
facts its LogUp argument needs and is UNSATISFIABLE otherwise:

* `GoodV V` — `V.AdjacentC` (R-LC8: row `i+1`'s node is `ω ·` row `i`'s), injective compute nodes,
  and the characteristic condition `hchar` on the extension field (all decidable from `V` and the
  field; `GoodV.decidable`);
* `computeChipVCLF ok` — `computeChipVCLE` plus the gate `const 1` when `ok = false`
  (`sat_ok`: an accepted trace has `ok = true`);
* **`chipOfV V γc ρc chalV pubVal := computeChipVCLF (decide (GoodV V)) …`** at `V.computeNodes`,
  `V.basis`, `V.orbitC`; width `232` for every `V` (`chipOfV_width`);
* **`acceptedRows_of_chipOfV`** — acceptance alone gives the accepted row family, hence
  `exportReqFacts` / `pathReqFacts` with no premise on `V` (`chipOfV_exportReqFacts`,
  `chipOfV_pathReqFacts`).  `R-LC8`'s `AdjacentC` is exactly the adjacency `acceptedRows_of_sat`
  consumes (no shape mismatch).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Module
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open scoped Polynomial

set_option maxRecDepth 300000

noncomputable section

/-! ## 1. The gated chip -/

section gates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The rejecting gate (`1 = 0`) when the verifier checks fail. -/
def okGates (ok : Bool) : List (CoeffExpr F) := if ok then [] else [.const 1]

def vclGatesF (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) (ok : Bool) : List (CoeffExpr F) :=
  vclGatesE n b γc ρc ++ okGates ok

theorem vclGatesF_degree (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) (ok : Bool) :
    ∀ g ∈ vclGatesF n b γc ρc ok, g.degree ≤ 4 := by
  intro g hg
  simp only [vclGatesF, List.mem_append] at hg
  rcases hg with h | h
  · exact vclGatesE_degree n b γc ρc g h
  · cases ok <;> simp [okGates] at h; subst h; simp [CoeffExpr.degree]

end gates

def vclRAPF {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (γc ρc : ℕ) (ok : Bool) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![vclRound0, 24]
    w := vclWidthE
    w_eq := by simp [Fin.sum_univ_two, vclRound0, vclWidthE]
    h := h
    d := 4
    s := (vclGatesF n b γc ρc ok).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalV pubVal ((vclGatesF n b γc ρc ok).get i)
    C_vars := fun _i => coeffToMv_vars chalV pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalV pubVal _).trans
      (vclGatesF_degree n b γc ρc ok _ (List.get_mem _ _))
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- **`computeChipVCLF ok`**: `computeChipVCLE`, rejecting every trace when `ok = false`. -/
def computeChipVCLF
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (ok : Bool) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPF (n := n) b γc ρc ok chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [vclRAPF]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          have := j.isLt
          change 11 + (j : ℕ) < vclRound0
          simp only [vclRound0]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

set_option maxHeartbeats 3200000 in
theorem computeChipVCLF_sat_iff
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (ok : Bool) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLF hn nodes b γc ρc ok chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLF hn nodes b γc ρc ok chalV pubVal orbit) P ↔
      (computeChipVCLF hn nodes b γc ρc ok chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ vclGatesF n b γc ρc ok,
          g.eval (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLF hn nodes b γc ρc ok chalV pubVal orbit).rap.s) (x : F),
      ((computeChipVCLF hn nodes b γc ρc ok chalV pubVal orbit).rap.compose P i).eval x =
        ((vclGatesF n b γc ρc ok).get i).eval (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalV pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, fun x hx g hg => ?_⟩
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

/-- **A rejecting chip accepts nothing**: acceptance forces `ok = true`. -/
theorem sat_ok
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (ok : Bool) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLF hn nodes b γc ρc ok chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLF hn nodes b γc ρc ok chalV pubVal orbit) P) :
    ok = true := by
  cases ok
  · exfalso
    have hs := (computeChipVCLF_sat_iff hn nodes b γc ρc false chalV pubVal orbit P).1 hP
    have hx : nodes ⟨0, hn⟩ ∈ rowNodeSet nodes := by simp [rowNodeSet]
    have := hs.2 _ hx (.const 1) (by simp [vclGatesF, okGates])
    simp [CoeffExpr.eval] at this
  · rfl

/-! ## 2. The verifier-checked chip of a datum -/

section datum
variable {F K Kio : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [DecidableEq K] {hC : ℕ} {S : MemShape}

/-- **The row checks the chip enforces**: row adjacency on the orbit (R-LC8's `AdjacentC`),
injective compute nodes, and the characteristic condition on `K`. -/
def GoodV (V : VerifierData F K hC S) : Prop :=
  V.AdjacentC ∧ Function.Injective V.computeNodes ∧ ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1

instance GoodV.decidable (V : VerifierData F K hC S) : Decidable (GoodV V) := by
  unfold GoodV; infer_instance

/-- **The compute chip of a verifier datum** (pre-tower; coins / publics placed by the caller). -/
def chipOfV (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F) :
    FixedPreprocessingRAP F :=
  computeChipVCLF V.hN V.computeNodes V.basis γc ρc (decide (GoodV V)) chalV pubVal V.orbitC

theorem chipOfV_width (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F) :
    (chipOfV V γc ρc chalV pubVal).rap.w = 232 := rfl

theorem chipOfV_good (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (P : Fin 232 → F[X]) (hP : RAP.SatisfiesWithPreprocessing (chipOfV V γc ρc chalV pubVal) P) :
    GoodV V :=
  of_decide_eq_true (sat_ok V.hN V.computeNodes V.basis γc ρc _ chalV pubVal V.orbitC P hP)

variable [Fintype K] [CharP K (ringChar K)]

/-- **Acceptance alone gives the accepted row family** (no `Checks`). -/
theorem acceptedRows_of_chipOfV (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (P : Fin 232 → F[X]) (hP : RAP.SatisfiesWithPreprocessing (chipOfV V γc ρc chalV pubVal) P) :
    AcceptedRows V.basis γc ρc V.N V.N (rowEnvs (h := hC) V.computeNodes V.orbitC.ω P chalV pubVal)
      chalV pubVal := by
  obtain ⟨hadj, hinj, hchar⟩ := chipOfV_good V γc ρc chalV pubVal P hP
  have hs := (computeChipVCLF_sat_iff V.hN V.computeNodes V.basis γc ρc _ chalV pubVal V.orbitC P).1 hP
  have hn := V.hN
  have hmem : ∀ i (hi : i < V.N), V.computeNodes ⟨i, hi⟩ ∈ rowNodeSet V.computeNodes := fun i hi => by simp [rowNodeSet]
  have henv : ∀ i (hi : i < V.N), rowEnvs (h := hC) V.computeNodes V.orbitC.ω P chalV pubVal i =
      envOfTrace P V.orbitC.ω (V.computeNodes ⟨i, hi⟩) chalV pubVal := fun i hi => by simp [rowEnvs, hi]
  have hgates : ∀ i < V.N, ∀ g ∈ vclGatesE V.N V.basis γc ρc,
      g.eval (rowEnvs (h := hC) V.computeNodes V.orbitC.ω P chalV pubVal i) = 0 := by
    intro i hi g hg
    rw [henv i hi]
    exact hs.2 _ (hmem i hi) g (by simp only [vclGatesF, List.mem_append]; exact Or.inl hg)
  have h11 : (11 : ℕ) < 232 := by norm_num
  have h12 : (12 : ℕ) < 232 := by norm_num
  have m0 : P ⟨11, h11⟩ = firstRowMask V.computeNodes := hs.1 ⟨0, by change 0 < 2; norm_num⟩
  have m1 : P ⟨12, h12⟩ = lastRowMask hn V.computeNodes := hs.1 ⟨1, by change 1 < 2; norm_num⟩
  have htr11 : ∀ i (hi : i < V.N), (rowEnvs (h := hC) V.computeNodes V.orbitC.ω P chalV pubVal i).trace 11 =
      if i = 0 then 1 else 0 := by
    intro i hi
    rw [henv i hi]
    simp only [envOfTrace, dif_pos h11]
    rw [m0, Nock.Framework.firstRowMask_eval _ hinj]
  have htr12 : ∀ i (hi : i < V.N), (rowEnvs (h := hC) V.computeNodes V.orbitC.ω P chalV pubVal i).trace 12 =
      if i = V.N - 1 then 1 else 0 := by
    intro i hi
    rw [henv i hi]
    simp only [envOfTrace, dif_pos h12]
    rw [m1, Nock.Framework.lastRowMask_eval _ _ hinj]
    simp only [Fin.ext_iff]
  refine ⟨hn, hgates, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j
    rw [henv i (by omega), henv (i + 1) hi]
    have ha := hadj ⟨i, by omega⟩ hi
    simp only [envOfTrace]
    split_ifs with hj
    · rw [ha]
    · rfl
  · rw [htr11 0 hn, if_pos rfl]
  · intro i hi
    rw [htr12 i (by omega), if_neg (by omega)]
  · rw [htr12 (V.N - 1) (by omega), if_pos rfl]
  · intro i hi
    exact selAt_of_gates V.N V.basis γc ρc _ (hgates i hi) hchar
  · intro i; simp only [rowEnvs]; split_ifs <;> rfl
  · intro i; simp only [rowEnvs]; split_ifs <;> rfl

/-- **The export `reqFacts` of the verifier-checked chip** (no premise on `V`). -/
def chipOfV_exportReqFacts (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (P : Fin 232 → F[X]) (hP : RAP.SatisfiesWithPreprocessing (chipOfV V γc ρc chalV pubVal) P) :
    ReqIOFacts (FiniteIO.compress (m := 10) (coinsV V.basis chalV γc ρc))
      (limbVal V.basis pubVal rhoExportPub) :=
  exportReqFacts V.basis γc ρc V.N V.N _ chalV pubVal (acceptedRows_of_chipOfV V γc ρc chalV pubVal P hP)

/-- **The path `reqFacts` of the verifier-checked chip.** -/
def chipOfV_pathReqFacts (V : VerifierData F K hC S) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (P : Fin 232 → F[X]) (hP : RAP.SatisfiesWithPreprocessing (chipOfV V γc ρc chalV pubVal) P) :
    ReqIOFacts (FiniteIO.compress (m := 8) (coinsV V.basis chalV γc ρc))
      (limbVal V.basis pubVal rhoPathPub) :=
  pathReqFacts V.basis γc ρc V.N V.N _ chalV pubVal (acceptedRows_of_chipOfV V γc ρc chalV pubVal P hP)

/-- An honest datum passes the checks (the chip is not vacuous): `GoodV` holds whenever its three
conjuncts do (positive control, by definition). -/
theorem goodV_of (V : VerifierData F K hC S) (h1 : V.AdjacentC) (h2 : Function.Injective V.computeNodes)
    (h3 : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) : GoodV V := ⟨h1, h2, h3⟩

end datum

end

end VclL.Compute
end Nock.NockVMROM.Thm54
