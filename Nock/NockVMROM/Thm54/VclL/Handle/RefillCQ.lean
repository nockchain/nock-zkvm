/-
  Nock/NockVMROM/Thm54/VclL/Handle/RefillCQ.lean

  Additive.

  Given a trace `P` (85 columns) accepted by the `𝕂′` compute twin `computeChipVCLHQ` at challenge /
  public vectors `chalVQ / pubVQ`, and VS vectors `chalV / pubV` that agree with them on the walk coins
  (limbs `6..11`) and the publics `0..14`, `refillP` keeps every column of `P` outside the handle block
  `43..57` (as the SAME polynomial) and interpolates at the row nodes the `𝕂` fill at the coins
  `(limb 0, limb 3)` of `chalV`: the slot inverses `A / D` (`fillTrace`) and the exclusive prefix sums of the
  per-row consumed-record terms `Σ 1/compress`.  **`computeChipVCLH_of_HQ`**: if every consumed record of
  every row has a nonzero denominator at those coins and the terminals `pubRhoX / pubRhoP` of `pubV` are
  the two totals, the VS compute chip `computeChipVCLH` accepts `refillP` at `chalV / pubV`.

  * `rowSel_congr`: the row selector facts read only columns `< 43`;
  * `notBad_of_sel`: at a row with `RowSel` whose active records have nonzero denominators, no slot is bad
    (`D = 0 → A = 0`), so the inverse `A / D` satisfies the slot gate.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompSatH
import Nock.NockVMROM.Thm54.VclL.Handle.PoleFree

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RefillCQ

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.ComputeSatHQ
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

noncomputable section

/-! ## 1. Row facts -/

section Row
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

/-- The row selector facts read only the columns `< 43`. -/
theorem rowSel_congr {e1 e2 : Env F} {j0 : ℕ} (h : ∀ c < 43, e1.trace c = e2.trace c) (hs : RowSel e1 j0) :
    RowSel e2 j0 := by
  have h13 : z1C < 43 := by decide
  have h15 : betaC < 43 := by decide
  have h25 : hSf1.k < 43 := by decide
  have h18 : prC < 43 := by decide
  refine ⟨hs.lt, fun j hj => by rw [← h j (by omega)]; exact hs.sel j hj, by rw [← h _ h13]; exact hs.z1,
    by rw [← h _ h15]; exact hs.beta, by rw [← h _ h25]; exact hs.k1, ?_⟩
  rw [← h _ h18, ← h 5 (by omega), ← h _ h15, ← h _ h13]
  exact hs.pr

theorem slotD_eq (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) :
    slotD S eK eF = (S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (ChipH.den x.rcd) eK eF).sum +
      algebraMap F K (pairF S eF) * (pairDa S eK eF * pairDb S eK eF) := by
  unfold slotD
  cases hp : S.pair with
  | none => simp [pairF, pairDa, pairDb, hp]
  | some q => obtain ⟨fl, a, b⟩ := q; simp [pairF, pairDa, pairDb, hp, evalQ_cc]

theorem slotA_eq (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) :
    slotA S eK eF = algebraMap F K ((S.ents.map fun x => evalQ x.act eF).sum) +
      algebraMap F K (pairF S eF) * (pairDa S eK eF + pairDb S eK eF) := by
  unfold slotA
  cases hp : S.pair with
  | none => simp [pairF, pairDa, pairDb, hp]
  | some q => obtain ⟨fl, a, b⟩ := q; simp [pairF, pairDa, pairDb, hp, evalQ_cc]

/-- **No slot is bad** at a row with `RowSel` whose active records (and active read pair) have nonzero
denominators. -/
theorem notBad_of_sel {eF : Env F} {j0 : ℕ} (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) (eK : Env K)
    (hden : ∀ x ∈ S.ents, evalQ x.act eF = 1 → evalMQ (ChipH.den x.rcd) eK eF ≠ 0)
    (hpd : pairF S eF = 1 → pairDa S eK eF ≠ 0 ∧ pairDb S eK eF ≠ 0) :
    ¬ SlotBad S eK eF := by
  rintro ⟨hD, hA⟩
  rw [slotD_eq] at hD
  rw [slotA_eq] at hA
  have hb := fun x hx => act_bool hs S hS x hx
  rcases pairF_bool hs S hS with h0 | h1
  · rw [h0, map_zero, zero_mul, add_zero] at hD hA
    rw [sum_bool S.ents (fun x => evalQ x.act eF) _ hb] at hD
    rw [sum_bool_one S.ents (fun x => evalQ x.act eF) hb] at hA
    rcases TeleC.active_le_one S.ents (fun x => evalQ x.act eF) (act_pairwise hs S hS) with hE | ⟨x0, hx0, ha0, hE⟩
    · rw [hE] at hA; exact hA (by simp)
    · rw [hE] at hD
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hD
      exact hden x0 hx0 ha0 hD
  · have hz : ∀ x ∈ S.ents, evalQ x.act eF = 0 := fun x hx => by
      have := pairF_act hs S hS x hx; rwa [h1, one_mul] at this
    have hs0 : (S.ents.map fun x => evalQ x.act eF).sum = 0 :=
      List.sum_eq_zero fun y hy => by obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hz x hx
    have hs1 : (S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (ChipH.den x.rcd) eK eF).sum = 0 :=
      List.sum_eq_zero fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; rw [hz x hx, map_zero, zero_mul]
    rw [hs1, h1, map_one, one_mul, zero_add] at hD
    obtain ⟨ha, hb'⟩ := hpd h1
    exact mul_ne_zero ha hb' hD

/-- Active export / path records are consumed records of the row. -/
theorem act_mem_reqs {eF : Env F} (S : SlotSpec ℚ) (hS : S ∈ slots) (x : Ent ℚ) (hx : x ∈ S.ents)
    (ha : evalQ x.act eF = 1) :
    (entKey x.rcd eF : Fin 5 → K) ∈ rowXReqs eF ++ rowPReqs eF := by
  cases hp : x.path
  · refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨S, hS, List.mem_map.mpr ⟨x, ?_, rfl⟩⟩)
    simp [activeX, hx, hp, ha]
  · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨S, hS, List.mem_append_left _
      (List.mem_map.mpr ⟨x, ?_, rfl⟩)⟩)
    simp [activeP, hx, hp, ha]

/-- **No slot is bad** when every consumed record of the row has a nonzero denominator. -/
theorem notBad_of_reqs {eF : Env F} {j0 : ℕ} (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots) (eK : Env K)
    (hden : ∀ r ∈ (rowXReqs eF ++ rowPReqs eF : List (Fin 5 → K)), compress (coinsOf eK) r ≠ 0) :
    ¬ SlotBad S eK eF := by
  refine notBad_of_sel hs S hS eK (fun x hx ha => ?_) (fun h1 => ?_)
  · rw [evalMQ_den eK eF _ (slots_states S hS x hx).2.2]
    exact hden _ (act_mem_reqs S hS x hx ha)
  · unfold pairF at h1
    unfold pairDa pairDb
    cases hp : S.pair with
    | none => rw [hp] at h1; exact absurd h1 zero_ne_one
    | some q =>
      obtain ⟨fl, a, c⟩ := q
      rw [hp] at h1
      obtain ⟨-, ha, hc, -⟩ := slots_pair S hS fl a c hp
      simp only at h1 ⊢
      have hm : ∀ r ∈ (pairReqs S eF : List (Fin 5 → K)), compress (coinsOf eK) r ≠ 0 := fun r hr =>
        hden r (List.mem_append_right _ (pairReqs_sub S hS r hr))
      have hpr : (pairReqs S eF : List (Fin 5 → K)) = [entKey a eF, entKey c eF] := by
        unfold pairReqs; rw [hp]; simp only; rw [if_pos h1]
      rw [evalMQ_den eK eF _ ha, evalMQ_den eK eF _ hc]
      exact ⟨hm _ (by rw [hpr]; simp), hm _ (by rw [hpr]; simp)⟩

end Row

/-! ## 2. The re-filled trace -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (nodes : Fin n → F) (b : Basis (Fin 3) F K) (chalV pubV : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (P : Fin 85 → F[X])

/-- Row `j` of `P` read at the VS vectors (a default environment off the rows). -/
def baseN (j : ℕ) : Env F :=
  if hj : j < n then Reify.envOfTrace P orbit.ω (nodes ⟨j, hj⟩) chalV pubV
  else ⟨fun _ => 0, fun _ => 0, chalV, pubV⟩

/-- Row `j`'s export term at the `𝕂` coins of `chalV`: `Σ_{rowXReqs} 1/compress`. -/
def termXV (j : ℕ) : K :=
  ((rowXReqs (baseN nodes chalV pubV orbit P j)).map fun r => (compress (coinsC b chalV) r)⁻¹).sum

/-- Row `j`'s path term. -/
def termPV (j : ℕ) : K :=
  ((rowPReqs (baseN nodes chalV pubV orbit P j)).map fun r => (compress (coinsC b chalV) r)⁻¹).sum

/-- The handle-block fill of row `r`, column `c` (`43..51` the slot inverses `A / D`, `52..54` / `55..57`
the exclusive prefix sums of the export / path terms). -/
def fillC (r c : ℕ) : F :=
  if c < 52 then fillTrace b (baseN nodes chalV pubV orbit P r) c
  else if c < 55 then coordNA b (∑ j ∈ Finset.range r, termXV nodes b chalV pubV orbit P j) (c - 52)
  else coordNA b (∑ j ∈ Finset.range r, termPV nodes b chalV pubV orbit P j) (c - 55)

/-- **The re-filled VS compute trace**: `P`'s columns outside `43..57` (the same polynomials), the fill
interpolated at the row nodes on `43..57`. -/
def refillP : Fin 70 → F[X] := fun c =>
  if 43 ≤ (c : ℕ) ∧ (c : ℕ) < 58 then
    Lagrange.interpolate Finset.univ nodes (fun i : Fin n => fillC nodes b chalV pubV orbit P (i : ℕ) (c : ℕ))
  else P ⟨c, by omega⟩

theorem refillP_old (c : ℕ) (hc : c < 70) (hc' : ¬ (43 ≤ c ∧ c < 58)) :
    refillP nodes b chalV pubV orbit P ⟨c, hc⟩ = P ⟨c, by omega⟩ := by
  unfold refillP; rw [if_neg hc']

theorem refillP_new (c : ℕ) (hc : c < 70) (hc' : 43 ≤ c ∧ c < 58) :
    refillP nodes b chalV pubV orbit P ⟨c, hc⟩ =
      Lagrange.interpolate Finset.univ nodes (fun i : Fin n => fillC nodes b chalV pubV orbit P (i : ℕ) c) := by
  unfold refillP; rw [if_pos hc']

variable (cv pv : ℕ → F)

theorem refill_trace_old (i : Fin n) (c : ℕ) (hc : c < 70) (hc' : ¬ (43 ≤ c ∧ c < 58)) :
    (Reify.envOfTrace (refillP nodes b chalV pubV orbit P) orbit.ω (nodes i) chalV pubV).trace c =
      (Reify.envOfTrace P orbit.ω (nodes i) cv pv).trace c := by
  rw [envOfTrace_trace _ _ _ _ _ hc, envOfTrace_trace _ _ _ _ _ (show c < 85 by omega), refillP_old _ _ _ _ _ _ c hc hc']

theorem refill_next_old (i : Fin n) (c : ℕ) (hc : c < 70) (hc' : ¬ (43 ≤ c ∧ c < 58)) :
    (Reify.envOfTrace (refillP nodes b chalV pubV orbit P) orbit.ω (nodes i) chalV pubV).traceNext c =
      (Reify.envOfTrace P orbit.ω (nodes i) cv pv).traceNext c := by
  rw [envOfTrace_traceNext _ _ _ _ _ hc, envOfTrace_traceNext _ _ _ _ _ (show c < 85 by omega),
    refillP_old _ _ _ _ _ _ c hc hc']

theorem refill_trace_new (hinj : Function.Injective nodes) (i : Fin n) (c : ℕ) (hc' : 43 ≤ c ∧ c < 58) :
    (Reify.envOfTrace (refillP nodes b chalV pubV orbit P) orbit.ω (nodes i) chalV pubV).trace c =
      fillC nodes b chalV pubV orbit P (i : ℕ) c := by
  rw [envOfTrace_trace _ _ _ _ _ (show c < 70 by omega), refillP_new _ _ _ _ _ _ c (by omega) hc']
  exact Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

theorem refill_next_new (hinj : Function.Injective nodes) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (hadj : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) (c : ℕ) (hc' : 43 ≤ c ∧ c < 58) :
    (Reify.envOfTrace (refillP nodes b chalV pubV orbit P) orbit.ω (nodes i) chalV pubV).traceNext c =
      fillC nodes b chalV pubV orbit P ((i : ℕ) + 1) c := by
  rw [envOfTrace_traceNext _ _ _ _ _ (show c < 70 by omega), refillP_new _ _ _ _ _ _ c (by omega) hc',
    mul_comm, ← hadj]
  exact Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := nodes)
    (fun i : Fin n => fillC nodes b chalV pubV orbit P (i : ℕ) c) hinj.injOn (Finset.mem_univ (⟨(i : ℕ) + 1, hi⟩ : Fin n))

theorem baseN_lt (i : Fin n) :
    baseN nodes chalV pubV orbit P i = Reify.envOfTrace P orbit.ω (nodes i) chalV pubV := by
  simp [baseN, i.isLt]

theorem limbVal_congr3 (f g : ℕ → F) (base : ℕ) (hfg : ∀ k < 3, f (base + k) = g (base + k)) :
    limbVal b f base = limbVal b g base := by
  unfold limbVal
  exact Finset.sum_congr rfl fun k _ => by rw [hfg k k.isLt]

theorem fillC_accX (r : ℕ) (k : Fin 3) :
    fillC nodes b chalV pubV orbit P r (accX + k) =
      coord b (∑ j ∈ Finset.range r, termXV nodes b chalV pubV orbit P j) k := by
  have := k.isLt
  unfold fillC
  rw [if_neg (by simp only [accX]; omega), if_pos (by simp only [accX]; omega)]
  simp only [coordNA, accX, show 52 + (k : ℕ) - 52 = k by omega, dif_pos this]

theorem fillC_accP (r : ℕ) (k : Fin 3) :
    fillC nodes b chalV pubV orbit P r (accP + k) =
      coord b (∑ j ∈ Finset.range r, termPV nodes b chalV pubV orbit P j) k := by
  have := k.isLt
  unfold fillC
  rw [if_neg (by simp only [accP]; omega), if_neg (by simp only [accP]; omega)]
  simp only [coordNA, accP, show 55 + (k : ℕ) - 55 = k by omega, dif_pos this]

end Chip

/-! ## 3. Acceptance of the re-fill -/

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (chalVQ pubVQ chalV pubV : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (P : Fin 85 → F[X])

/-- **The VS compute chip accepts the `𝕂` re-fill of a `𝕂′`-accepted compute trace**, at VS vectors
agreeing with the `𝕂′` ones on the walk coins and the publics `< 15`, when every consumed record of every
row has a nonzero denominator at the `𝕂` coins and the two handle terminals are the totals. -/
theorem computeChipVCLH_of_HQ
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHQ hn nodes b δ chalVQ pubVQ orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hc : 11 < ringChar F)
    (hchal : ∀ j, 6 ≤ j → j < 12 → chalV j = chalVQ j)
    (hpub : ∀ j, j < 15 → pubV j = pubVQ j)
    (hden : ∀ i : Fin n, ∀ r ∈ (rowXReqs (baseN nodes chalV pubV orbit P i) ++
        rowPReqs (baseN nodes chalV pubV orbit P i) : List (Fin 5 → K)), compress (coinsC b chalV) r ≠ 0)
    (hpX : ∀ k : Fin 3, pubV (pubRhoX + k) =
      coord b (∑ j ∈ Finset.range n, termXV nodes b chalV pubV orbit P j) k)
    (hpP : ∀ k : Fin 3, pubV (pubRhoP + k) =
      coord b (∑ j ∈ Finset.range n, termPV nodes b chalV pubV orbit P j) k) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubV orbit)
      (refillP nodes b chalV pubV orbit P) := by
  obtain ⟨hfixQ, hallQ⟩ := (computeChipVCLHQ_sat_iff hn nodes b δ chalVQ pubVQ orbit P).mp hsat
  set R := refillP nodes b chalV pubV orbit P with hR
  let eV : Fin n → Env F := fun i => Reify.envOfTrace R orbit.ω (nodes i) chalV pubV
  let eQ : Fin n → Env F := fun i => Reify.envOfTrace P orbit.ω (nodes i) chalVQ pubVQ
  have hlow : ∀ i c, c < 43 → (eV i).trace c = (eQ i).trace c := fun i c hc' =>
    refill_trace_old nodes b chalV pubV orbit P chalVQ pubVQ i c (by omega) (by omega)
  have hlowN : ∀ i c, c < 43 → (eV i).traceNext c = (eQ i).traceNext c := fun i c hc' =>
    refill_next_old nodes b chalV pubV orbit P chalVQ pubVQ i c (by omega) (by omega)
  have hhigh : ∀ i c, 58 ≤ c → c < 70 → (eV i).trace c = (eQ i).trace c := fun i c h1 h2 =>
    refill_trace_old nodes b chalV pubV orbit P chalVQ pubVQ i c h2 (by omega)
  have hhighN : ∀ i c, 58 ≤ c → c < 70 → (eV i).traceNext c = (eQ i).traceNext c := fun i c h1 h2 =>
    refill_next_old nodes b chalV pubV orbit P chalVQ pubVQ i c h2 (by omega)
  have hbaseT : ∀ (i : Fin n) c, c < 43 → (baseN nodes chalV pubV orbit P i).trace c = (eV i).trace c := by
    intro i c hc'
    rw [hlow i c hc', baseN_lt]
    rfl
  -- row selectors
  have hsel : ∀ i : Fin n, ∃ j0, RowSel (eV i) j0 := by
    intro i
    obtain ⟨j0, hs⟩ := rowSel_of_base (fun t ht => TeleCQ.base_of_satQ hn nodes b δ chalVQ pubVQ orbit P hsat i t
      (TeleCQ.baseH_sub t ht)) hc
    exact ⟨j0, rowSel_congr (fun c hc' => (hlow i c hc').symm) hs⟩
  -- the consumed lists of the re-fill are those of `P`
  have hlists : ∀ i : Fin n, (rowXReqs (eV i) : List (Fin 5 → K)) = rowXReqs (baseN nodes chalV pubV orbit P i) ∧
      (rowPReqs (eV i) : List (Fin 5 → K)) = rowPReqs (baseN nodes chalV pubV orbit P i) := fun i =>
    IOVS.rowReqs_congr _ _ (fun c hc' => (hbaseT i c hc').symm)
  have hcoins : ∀ i : Fin n, coinsOf (Compute.TowerD.gatherEnv b (eV i)) = coinsC b chalV := fun i => rfl
  have hdenV : ∀ i : Fin n, ∀ r ∈ (rowXReqs (eV i) ++ rowPReqs (eV i) : List (Fin 5 → K)),
      compress (coinsOf (Compute.TowerD.gatherEnv b (eV i))) r ≠ 0 := by
    intro i r hr
    rw [hcoins, (hlists i).1, (hlists i).2] at *
    exact hden i r hr
  -- the slot fill
  have hfill : ∀ i : Fin n, HonestFill b (eV i) := by
    intro i
    obtain ⟨h1, h2, -, -, h5⟩ := honestFill_attainable b (baseN nodes chalV pubV orbit P i)
    refine honestFill_congr b _ _ (fun c hc' => ?_) (by rw [h2, baseN_lt]; rfl) h5
    by_cases hc43 : c < 43
    · rw [h1 c hc43, hbaseT i c hc43]
    · rw [refill_trace_new nodes b chalV pubV orbit P hinj i c ⟨by omega, by omega⟩]
      show fillTrace b _ c = _
      unfold fillC; rw [if_pos hc']
  have hslot : ∀ i : Fin n, ∀ S ∈ (slots : List (SlotSpec ℚ)),
      evalMQ (slotGate S) (Compute.TowerD.gatherEnv b (eV i)) (eV i) = 0 := by
    intro i S hS
    obtain ⟨j0, hs⟩ := hsel i
    exact slotGate_honest_of_not_bad S _ _
      (notBad_of_reqs hs S hS _ (hdenV i)) (hfill i S hS)
  -- the per-row terms
  have htX : ∀ i : Fin n, termVal b (slotsX (F := F)) (eV i) = termXV nodes b chalV pubV orbit P i := by
    intro i
    obtain ⟨j0, hs⟩ := hsel i
    rw [termX_row b hs (hslot i) (fun r hr => hdenV i r (List.mem_append_right _ hr)), hcoins, (hlists i).1]
    rfl
  have htP : ∀ i : Fin n, termVal b (slotsP (F := F)) (eV i) = termPV nodes b chalV pubV orbit P i := by
    intro i
    obtain ⟨j0, hs⟩ := hsel i
    rw [termP_row b hs (hslot i) (fun r hr => hdenV i r (List.mem_append_right _ hr)), hcoins, (hlists i).2]
    rfl
  -- the row environments as a sequence
  let envs : ℕ → Env F := fun j => if hj : j < n then eV ⟨j, hj⟩ else ⟨fun _ => 0, fun _ => 0, chalV, pubV⟩
  have henv : ∀ i : Fin n, envs i = eV i := fun i => by simp [envs, i.isLt]
  have h11 : ∀ i : Fin n, (envs i).trace 11 = if (i : ℕ) = 0 then 1 else 0 := by
    intro i
    rw [henv, hlow i 11 (by omega)]
    exact (TeleCQ.masksCQ hn nodes b δ chalVQ pubVQ orbit P hfixQ hinj i).1
  have h12 : ∀ i : Fin n, (envs i).trace 12 = if (i : ℕ) + 1 = n then 1 else 0 := by
    intro i
    rw [henv, hlow i 12 (by omega)]
    have m2 := (TeleCQ.masksCQ hn nodes b δ chalVQ pubVQ orbit P hfixQ hinj i).2
    change (eQ i).trace 12 = _ at m2
    rw [m2]
    by_cases hh : (i : ℕ) + 1 = n
    · rw [if_pos (by omega), if_pos hh]
    · rw [if_neg (by omega), if_neg hh]
  have hsX : ∀ r ≤ n, ∑ j ∈ Finset.range r, termVal b (slotsX (F := F)) (envs j) =
      ∑ j ∈ Finset.range r, termXV nodes b chalV pubV orbit P j := fun r hr =>
    Finset.sum_congr rfl fun j hj => by
      have hj' : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hr
      rw [show envs j = eV ⟨j, hj'⟩ from henv ⟨j, hj'⟩, htX ⟨j, hj'⟩]
  have hsP : ∀ r ≤ n, ∑ j ∈ Finset.range r, termVal b (slotsP (F := F)) (envs j) =
      ∑ j ∈ Finset.range r, termPV nodes b chalV pubV orbit P j := fun r hr =>
    Finset.sum_congr rfl fun j hj => by
      have hj' : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hr
      rw [show envs j = eV ⟨j, hj'⟩ from henv ⟨j, hj'⟩, htP ⟨j, hj'⟩]
  have hpubV : ∀ i : Fin n, (eV i).pub = pubV := fun i => rfl
  refine computeChipVCLH_sat_of_rows hn nodes b chalV pubV orbit R ?_ ?_ ?_
  · intro j
    fin_cases j
    · have h0 : P ⟨11, by omega⟩ = firstRowMask nodes := hfixQ ⟨0, by show 0 < 2; omega⟩
      exact (refillP_old nodes b chalV pubV orbit P 11 (by omega) (by omega)).trans h0
    · have h1 : P ⟨12, by omega⟩ = lastRowMask hn nodes := hfixQ ⟨1, by show 1 < 2; omega⟩
      exact (refillP_old nodes b chalV pubV orbit P 12 (by omega) (by omega)).trans h1
  · intro x hx t ht
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    change evalQ t (eV i) = 0
    have harith : ∀ t ∈ (arithGates : List (CoeffExpr ℚ)) ++ (eqGates : List (EqG ℚ)).map EqG.gate,
        t ∈ (baseGatesH : List (CoeffExpr ℚ)) → evalQ t (eV i) = 0 := by
      intro t hmem htB
      rw [evalQ_congr_rds t (eV i) (eQ i) (fun p hp => ?_)]
      · exact TeleCQ.base_of_satQ hn nodes b δ chalVQ pubVQ orbit P hsat i t (TeleCQ.baseH_sub t htB)
      have hp' := arith_reads t hmem p hp
      rcases p with ⟨k, c⟩
      cases k
      · simp only [bsOK, decide_eq_true_eq] at hp'
        exact hlow i c hp'
      · simp [bsOK] at hp'
      · simp [bsOK] at hp'
      · simp only [bsOK, decide_eq_true_eq] at hp'
        exact hpub c (by omega)
    simp only [baseGatesH, List.mem_append] at ht
    rcases ht with (ht | ht) | ht
    · exact harith t (List.mem_append_left _ ht) (by simp [baseGatesH, ht])
    · have hr := accGatesH_honest b n (i : ℕ) i.isLt envs
        (∑ j ∈ Finset.range n, termXV nodes b chalV pubV orbit P j)
        (∑ j ∈ Finset.range n, termPV nodes b chalV pubV orbit P j)
        (h11 i) (h12 i) (hsX n le_rfl) (hsP n le_rfl)
        (fun k => by
          rw [hsX _ i.isLt.le, henv, refill_trace_new nodes b chalV pubV orbit P hinj i _
            ⟨by simp only [accX]; omega, by have := k.isLt; simp only [accX]; omega⟩, fillC_accX])
        (fun hlt k => by
          rw [hsX _ (by omega), henv, refill_next_new nodes b chalV pubV orbit P hinj i hlt (hadj i hlt) _
            ⟨by simp only [accX]; omega, by have := k.isLt; simp only [accX]; omega⟩, fillC_accX])
        (fun k => by
          rw [hsP _ i.isLt.le, henv, refill_trace_new nodes b chalV pubV orbit P hinj i _
            ⟨by simp only [accP]; omega, by have := k.isLt; simp only [accP]; omega⟩, fillC_accP])
        (fun hlt k => by
          rw [hsP _ (by omega), henv, refill_next_new nodes b chalV pubV orbit P hinj i hlt (hadj i hlt) _
            ⟨by simp only [accP]; omega, by have := k.isLt; simp only [accP]; omega⟩, fillC_accP])
        (fun k => by rw [henv, hpubV]; exact hpX k)
        (fun k => by rw [henv, hpubV]; exact hpP k)
        (mapC (fun q : ℚ => (q : F)) t) (List.mem_map_of_mem ht)
      rwa [eval_mapC_cast, henv i] at hr
    · exact harith t (List.mem_append_right _ ht) (by simp [baseGatesH, ht])
  · intro x hx t ht
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    change evalMQ t (Compute.TowerD.gatherEnv b (eV i)) (eV i) = 0
    rcases List.mem_append.mp ht with hs | hw
    · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hs
      exact hslot i S hS
    · have hQw : evalMQ t (Compute.TowerD.gatherEnv b (eQ i)) (eQ i) = 0 := by
        have h0 : ∀ k, (mixedCompile b Compute.TowerD.col0Id (mapM (fun q : ℚ => (q : F)) t) k).eval (eQ i) = 0 :=
          fun k => hallQ (nodes i) (mem_rowNodeSet nodes i) _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem hw, List.mem_ofFn.mpr ⟨k, rfl⟩⟩))
        have := (mixedCompile_zero_iff b Compute.TowerD.col0Id (Compute.TowerD.isCoordEnv_gather b (eQ i)) _).mpr h0
        rwa [eval_mapM_cast] at this
      rw [← hQw]
      refine evalMQ_congr_rds t _ _ _ _ (fun p hp => ?_) (fun p hp => ?_)
      · have hp' := walk_readsK t hw p hp
        rcases p with ⟨k, c⟩
        cases k
        · simp only [wkOK, Bool.or_eq_true, beq_iff_eq, wLn, wCnt, wAcc, wInv] at hp'
          show limbVal b (eV i).trace c = limbVal b (eQ i).trace c
          refine limbVal_congr3 b _ _ c fun k hk => hhigh i _ (by omega) (by omega)
        · simp only [wkOK, Bool.or_eq_true, beq_iff_eq, wLn, wCnt, wAcc] at hp'
          show limbVal b (eV i).traceNext c = limbVal b (eQ i).traceNext c
          refine limbVal_congr3 b _ _ c fun k hk => hhighN i _ (by omega) (by omega)
        · simp only [wkOK, Bool.or_eq_true, beq_iff_eq, chalAlphaW, chalGammaW] at hp'
          show limbVal b chalV c = limbVal b chalVQ c
          refine limbVal_congr3 b _ _ c fun k hk => hchal _ (by omega) (by omega)
        · simp only [wkOK, Bool.or_eq_true, beq_iff_eq, pubIC, pubSeed, pubOut] at hp'
          show limbVal b pubV c = limbVal b pubVQ c
          refine limbVal_congr3 b _ _ c fun k hk => hpub _ (by omega)
      · have hp' := walk_readsF t hw p hp
        rcases p with ⟨k, c⟩
        cases k
        · simp only [wfOK, decide_eq_true_eq] at hp'
          exact hlow i c hp'
        · simp only [wfOK, decide_eq_true_eq] at hp'
          exact hlowN i c hp'
        · simp [wfOK] at hp'
        · simp [wfOK] at hp'

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.RefillCQ
