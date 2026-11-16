/-
**vacuity witnesses for `nock_e2e_J9A_succinct`** (accept-vacuity rule).  No existing statement is edited.

Part A (Merkle budgets, inventory ): `hterm`/`hconfig` hold for EVERY skeleton list (`budgets_exist`, with `V = length * sum leafCount`), and for the
side tree list of any instance (`side_budgets_sat`, `Vf = k * 2^nD`, `Pf = 2 * 2^nD`), so `htermf`/`hconfigf` are inhabited at toy9R with `Vf <= 2^32`.
Part B (numbers): `SideNums (XI170 toy9R) .. (31/64) (31/64) (m * 2^nD/|KC|)` with `m = mSX`, `mSX + 1 <= 2^12`, and the side-VK budget
`T = 2 * (total - 1) <= 2^40`, composed into `nock_e2e_J9A_toy_numbers` (the numbers theorem at toy9R without `shapeOkF`, whose decide is not run).
-/
import NockvmE2E.J9A.E2ESuccinctNum
import NockvmE2E.J9A.E2EJ9AVSat
import NockvmE2E.Exec.SideBoundF

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9A.E2ESuccinctNonVac
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle
  NockvmE2E.Exec.SideInst NockvmE2E.Merkle.SideMerkle NockvmE2E.Exec.SideBoundF NockvmE2E.Exec.Cover
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.Exec.E2EResid (encK)
open NockvmE2E.Exec.Toy9R
open NockvmE2E.Deep
open NockvmE2E.J9A.E2EJ9AVSat (toy9R_k toy9R_hk toy9R_dom)
open MerkleTreeMultiExtractability

variable [SampleableType KC]

/-! ## Part A: Merkle budgets -/

theorem le_sum_of_mem' : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ≤ l.sum
  | [], _, h => nomatch h
  | x :: l, a, h => by
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_sum_of_mem' l a h; omega

theorem hconfig_gen (skels : List Skeleton) (B : ℕ) (hB : ∀ j : Fin skels.length, (skels.get j).leafCount ≤ B) :
    ∀ tag, (mconfig skels).nodeBudget tag ≤ 2 * B := by
  intro tag
  have := hB tag
  show 2 * (skels.get tag).leafCount - 1 ≤ 2 * B
  omega

theorem hterm_gen {YY Query : Type} (skels : List Skeleton) (B : ℕ) (hB : ∀ j : Fin skels.length, (skels.get j).leafCount ≤ B)
    (roots : List YY) (h : roots.length = skels.length) (ops : OpenAll YY skels)
    (logs : Fin skels.length → MerkleTreeExtractor.QueryLog Query YY) :
    claimsQueryCount (mkClaims skels roots h ops logs) ≤ skels.length * B := by
  have := claimsQueryCount_le_length_mul (mkClaims skels roots h ops logs) B (fun tag => by
    have := hB tag
    show (skels.get tag).leafCount - 1 ≤ B
    omega)
  simpa [mkClaims] using this

/-- `hterm` and `hconfig` are satisfiable for every skeleton list, at every `Y`, `Query` (so for the main `merkleSkels MC`). -/
theorem budgets_exist {YY Query : Type} (skels : List Skeleton) :
    ∃ V Pn : ℕ, (∀ (roots : List YY) (h : roots.length = skels.length) (ops : OpenAll YY skels)
        (logs : Fin skels.length → MerkleTreeExtractor.QueryLog Query YY),
        claimsQueryCount (mkClaims skels roots h ops logs) ≤ V) ∧
      ∀ tag, (mconfig skels).nodeBudget tag ≤ Pn := by
  have hB : ∀ j : Fin skels.length, (skels.get j).leafCount ≤ (skels.map Skeleton.leafCount).sum := fun j =>
    le_sum_of_mem' _ _ (List.mem_map_of_mem (List.get_mem skels j))
  exact ⟨_, _, fun roots h ops logs => hterm_gen skels _ hB roots h ops logs, hconfig_gen skels _ hB⟩

/-- every skeleton of the side Merkle list has `<= 2^nD` leaves -/
theorem side_leaf_le (XI : ExecInst) (hn : XI.nD ≤ 32)
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)] :
    ∀ s ∈ merkleSkels (bMask (S := KC) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 encK), s.leafCount ≤ 2 ^ XI.nD := by
  intro s hs
  rw [merkleSkels_bMask_eq] at hs
  simp only [List.mem_map] at hs
  obtain ⟨i, -, rfl⟩ := hs
  show (skelOf (friSpec (2 ^ (XI.nD - (i.1 + 1)))) (2 ^ (XI.nD - (i.1 + 1))) (2 ^ (XI.nD - (i.1 + 1)))).leafCount ≤ _
  rw [leafCount_skelOf _ (wf_friSpec _) _ _ (Nat.two_pow_pos _) le_rfl]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)

/-- `htermf` and `hconfigf` (side): inhabited at any instance with `k * 2^nD <= 2^32`, with `Vf <= 2^32`. -/
theorem side_budgets_sat (XI : ExecInst) (hn : XI.nD ≤ 32)
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (hV : XI.k * 2 ^ XI.nD ≤ 2 ^ 32) :
    ∃ Vf Pf : ℕ, Vf ≤ 2 ^ 32 ∧
      (∀ (roots : List DgJ8)
        (h : roots.length = (merkleSkels (bMask (S := KC) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 encK)).length)
        (op : OpenAll DgJ8 (merkleSkels (bMask (S := KC) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 encK)))
        (logs : Fin (merkleSkels (bMask (S := KC) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 encK)).length →
          MerkleTreeExtractor.QueryLog (NQuery (skelsSide XI)) DgJ8),
        claimsQueryCount (mkClaims (merkleSkels (bMask (S := KC) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 encK))
          roots h op logs) ≤ Vf) ∧
      ∀ tag, (mconfig (merkleSkels (bMask (S := KC) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 encK))).nodeBudget tag ≤ Pf := by
  have hB : ∀ j : Fin (merkleSkels (bMask (S := KC) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 encK)).length,
      ((merkleSkels (bMask (S := KC) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 encK)).get j).leafCount ≤ 2 ^ XI.nD :=
    fun j => side_leaf_le XI hn _ (List.get_mem _ j)
  have hlen := merkleSkels_bMask_length (S := KC) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (LX XI hn) DgJ8 encK
  refine ⟨XI.k * 2 ^ XI.nD, 2 * 2 ^ XI.nD, hV, fun roots h op logs => ?_, hconfig_gen _ _ hB⟩
  have := hterm_gen _ _ hB roots h op logs
  exact this.trans (Nat.le_of_eq (by rw [hlen]))

/-- `SampleableType KC`, by name -/
noncomputable def instKC_toy : SampleableType KC := SampleableType.ofFintype KC

omit [SampleableType KC] in
theorem toy9R_nD : (XI170 toy9R).nD = 13 := rfl
omit [SampleableType KC] in
theorem toy9R_nc : (XI170 toy9R).nc = 1355 := rfl
omit [SampleableType KC] in
theorem toy9R_r : (XI170 toy9R).r = 2 := rfl
omit [SampleableType KC] in
theorem toy9R_tabs : (XI170 toy9R).tabs.size = 7 := rfl

omit [SampleableType KC] in
theorem toy9R_nD32 : (XI170 toy9R).nD ≤ 32 := by rw [toy9R_nD]; norm_num

omit [SampleableType KC] in
/-- the challenge instance at toy9R's domain, by name -/
noncomputable def iCh_toy : ∀ j, SampleableType ((pSpec (XI170 toy9R).k
    (ω := smoothDomain (XI170 toy9R).nD toy9R_nD32) (fun _ : Fin ((XI170 toy9R).k + 1) => (1 : ℕ+)) (XI170 toy9R).l).Challenge j) :=
  fun j => by
    haveI := NockvmE2E.FriPort.friChal_finite (k := (XI170 toy9R).k) (ω := smoothDomain (XI170 toy9R).nD toy9R_nD32)
      (fun _ : Fin ((XI170 toy9R).k + 1) => (1 : ℕ+)) (XI170 toy9R).l j
    haveI := NockvmE2E.FriPort.friChal_nonempty (k := (XI170 toy9R).k) (ω := smoothDomain (XI170 toy9R).nD toy9R_nD32)
      (fun _ : Fin ((XI170 toy9R).k + 1) => (1 : ℕ+)) (XI170 toy9R).l j
    haveI := Fintype.ofFinite ((pSpec (XI170 toy9R).k (ω := smoothDomain (XI170 toy9R).nD toy9R_nD32)
      (fun _ : Fin ((XI170 toy9R).k + 1) => (1 : ℕ+)) (XI170 toy9R).l).Challenge j)
    exact SampleableType.ofFintype _

omit [SampleableType KC] in
/-- the Merkle-budget witness at toy9R: `Vf = 6 * 2^13 <= 2^32` -/
noncomputable def side_budgets_toy := @side_budgets_sat instKC_toy (XI170 toy9R) toy9R_nD32 iCh_toy
  (by rw [NockvmE2E.J9A.E2EJ9AVSat.toy9R_k, toy9R_nD]; norm_num)

/-! ## Part B: numbers -/

omit [SampleableType KC] in
theorem fixLen_le (XI : ExecInst) (c : FixCol) : fixLen XI c ≤ max XI.r 1 := by
  cases c <;> simp [fixLen]

omit [SampleableType KC] in
theorem fixCols_size_le (XI : ExecInst) : (fixCols XI).size ≤ XI.nc + 1 + XI.tabs.size := by
  unfold fixCols
  simp only [Array.size_append, Array.size_map, Array.size_singleton]
  have h1 : (Array.filter (fun c => XI.colKind[c]! == 1) (Array.range XI.nc)).size ≤ (Array.range XI.nc).size :=
    Array.size_filter_le
  have h2 : (Array.filter (fun t => decide (tabHN XI t < XI.hN)) (Array.range XI.tabs.size)).size ≤
      (Array.range XI.tabs.size).size := Array.size_filter_le
  simp only [Array.size_range] at h1 h2 ⊢
  omega

omit [SampleableType KC] in
theorem opList_length_le (XI : ExecInst) : (opList XI).length ≤ (XI.nc + 1 + XI.tabs.size) * max XI.r 1 := by
  unfold opList
  rw [List.length_flatMap]
  have h := List.sum_le_card_nsmul ((List.range (fixCols XI).size).map
    ((List.length : List (ℕ × ℕ) → ℕ) ∘ fun j => (List.range (fixLen XI (fixCols XI)[j]!)).map (j, ·))) (max XI.r 1) (by
      intro x hx
      simp only [List.mem_map, List.mem_range, Function.comp] at hx
      obtain ⟨j, -, rfl⟩ := hx
      simpa using fixLen_le XI (fixCols XI)[j]!)
  simp only [List.length_map, List.length_range, smul_eq_mul] at h
  exact h.trans (Nat.mul_le_mul_right _ (fixCols_size_le XI))

omit [SampleableType KC] in
theorem toy9R_dims: (XI170 toy9R).nc = 1355 ∧ (XI170 toy9R).r = 2 ∧ (XI170 toy9R).tabs.size = 7 :=
  ⟨toy9R_nc, toy9R_r, toy9R_tabs⟩

omit [SampleableType KC] in
theorem mSX_gen (XI : ExecInst) (hnc : XI.nc = 1355) (hr : XI.r = 2) (ht : XI.tabs.size = 7) :
    mSX XI + 1 ≤ 2 ^ 12 := by
  have h := opList_length_le XI
  rw [hnc, hr, ht] at h
  unfold mSX
  generalize (opList XI).length = L at h ⊢
  norm_num at h ⊢
  omega

omit [SampleableType KC] in
theorem mSX_toy : mSX (XI170 toy9R) + 1 ≤ 2 ^ 12 := mSX_gen _ toy9R_nc toy9R_r toy9R_tabs

omit [SampleableType KC] in
theorem vk_total_gen (XI : ExecInst) (hnc : XI.nc = 1355) (ht : XI.tabs.size = 7) (hD : XI.nD - 1 = 12) :
    2 * ((NockvmE2E.Exec.VKBind.vkSp XI).total - 1) ≤ 2 ^ 40 := by
  rw [NockvmE2E.Exec.VKBind.vkSp_total]
  have h := fixCols_size_le XI
  rw [hnc, ht] at h
  rw [hD]
  generalize (fixCols XI).size = S at h ⊢
  have : 2 * S * 2 ^ 12 ≤ 2 * 1363 * 2 ^ 12 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  omega

omit [SampleableType KC] in
theorem vk_total_toy : 2 * ((NockvmE2E.Exec.VKBind.vkSp (XI170 toy9R)).total - 1) ≤ 2 ^ 40 :=
  vk_total_gen _ toy9R_nc toy9R_tabs (by rw [toy9R_nD])

/-- `SideNums` at toy9R, `θ = δ = 31/64`, `ε = m 2^nD/|KC|` with `m = mSX` (the `ε` of `nock_e2e_J9A_numbers`) -/
theorem sideNums_toy :
    SideNums (XI170 toy9R) toy9R_nD32 (31 / 64 : ℝ) (31 / 64 : ℝ≥0)
      ((mSX (XI170 toy9R) * ((2 ^ (XI170 toy9R).nD : ℝ≥0) / Fintype.card KC) : ℝ≥0)) := by
  have hr : 64 * (2 ^ (∑ i : Fin ((XI170 toy9R).k + 1), (((fun _ : Fin ((XI170 toy9R).k + 1) => (1 : ℕ+)) i).1 : ℕ)) * ((1 : ℕ+) : ℕ)) ≤
      2 ^ (XI170 toy9R).nD := by
    rw [toy9R_k, toy9R_nD]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, PNat.one_coe, Nat.mul_one]
    have h1 : (1 : ℕ+).1 = 1 := rfl
    simp only [h1, PNat.val_ofNat, PNat.one_coe]
    norm_num
  have hfb : friBound (fun _ : Fin ((XI170 toy9R).k + 1) => (1 : ℕ+)) 1 = 2 ^ ((XI170 toy9R).k + 1) := by
    unfold friBound
    have h1 : (1 : ℕ+).1 = 1 := rfl
    simp [h1]
  refine ⟨toy9R_hk, toy9R_dom, ?_, ?_, ?_, ?_⟩
  · exact NockvmE2E.Succ.Numbers.caError_powers_numbers (F := KC) (ω := smoothDomain (XI170 toy9R).nD toy9R_nD32)
      (mSX (XI170 toy9R)) (N := 2 ^ (∑ i : Fin ((XI170 toy9R).k + 1), (((fun _ : Fin ((XI170 toy9R).k + 1) => (1 : ℕ+)) i).1 : ℕ)) *
        ((1 : ℕ+) : ℕ)) (by positivity) hr
  · rw [hfb]
  · rw [hfb, toy9R_k, toy9R_nD]; norm_num
  · rw [hfb, toy9R_k]
    refine NockvmE2E.Succ.Numbers.relUDR_rs_ge _ _ ?_
    rw [Fintype.card_fin, toy9R_nD]; norm_num

end NockvmE2E.J9A.E2ESuccinctNonVac

#print axioms NockvmE2E.J9A.E2ESuccinctNonVac.budgets_exist
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac.side_budgets_toy
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac.mSX_toy
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac.vk_total_toy
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac.sideNums_toy
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac.iCh_toy
#print axioms NockvmE2E.J9A.E2ESuccinctNonVac.instKC_toy
