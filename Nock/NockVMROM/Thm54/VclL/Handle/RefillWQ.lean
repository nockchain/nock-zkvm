/-
  Nock/NockVMROM/Thm54/VclL/Handle/RefillWQ.lean

  Additive.

  Given a trace `Q` (166 columns) accepted by the `𝕂′` walk twin `walkChipHQ` at `chalsQ / pubsQ`,
  `refillW` keeps its columns `0..135` (the original walk chip's columns and the four handle columns
  `kL vL kR vR`, as the SAME polynomials) and interpolates on `136..150` the `𝕂` fill at the handle leaves
  `33 / 34` of `chals`: the three inverses `den⁻¹` (consumed export key, provided records `L / R`) and the
  inclusive prefix sums of `xInv` and of `mL · invL + mR · invR`.  **`walkChipH_of_HQ`**: when the vectors
  agree on the leaves `< 33` / publics `< 4`, every row's three denominators are nonzero at the `𝕂` coins and
  the terminals `pubs 4 / 5` are the totals, the VS walk twin `walkChipH` accepts `refillW` (with its
  preprocessing).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RefillMQ
import Nock.NockVMROM.Thm54.VclL.Handle.WalkTraceH
import Nock.NockVMROM.Thm54.VclL.Handle.RangeHQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RefillWQ

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial

noncomputable section

section Den
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- A length-4 key's denominator is `compress` of the key padded by `0`. -/
theorem denKey_eval4 (eK : Env K) (eF : Env F) (l : List (CoeffExpr F)) (hl : l.length = 4) :
    (CellH.denKey l).eval eK eF = compress ⟨eK.chal CellH.hGam, eK.chal CellH.hRho⟩ (ServeH.keyVec5 l eF) := by
  simp only [CellH.denKey, MixedExpr.eval, ServeH.rlcH_eval, hl, compress, Walk.rlc, ServeH.keyVec5, zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun c => eK.chal CellH.hGam ^ c *
    algebraMap F K ((l.getD c (.const 0)).eval eF)) 5]
  conv_rhs => rw [show (5 : ℕ) = 4 + 1 from rfl, Finset.sum_range_succ]
  have h4 : (l.getD 4 (.const 0)).eval eF = 0 := by
    rw [List.getD_eq_default _ _ (by omega)]; simp [CoeffExpr.eval]
  rw [h4, map_zero, mul_zero, add_zero]

end Den

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ}
  (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chalsQ pubsQ chals pubs : ℕ → K)
  (Q : Fin (walkChipHQ δF kroots b hn nodes orbit chalsQ pubsQ).rap.w → F[X])

/-- Row `i`'s base environment of `Q`. -/
abbrev rowW (i : Fin n) : Env F :=
  Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 25 chals) (slotVal b 25 pubs)

/-- Row `j`'s denominator of the key list `l` at the `𝕂` coins (`1` off the rows). -/
def dW (l : List (CoeffExpr F)) (j : ℕ) : K :=
  if hj : j < n then compress ⟨chals CellH.hGam, chals CellH.hRho⟩
    (ServeH.keyVec5 l (rowW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q ⟨j, hj⟩)) else 1

/-- Row `j`'s base column `c` (`0` off the rows). -/
def cW (c j : ℕ) : F :=
  if hj : j < n then (rowW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q ⟨j, hj⟩).trace c else 0

/-- The inclusive prefix sums. -/
def xaW (r : ℕ) : K :=
  ∑ j ∈ Finset.range (r + 1), (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.xKeyH j)⁻¹

def paW (r : ℕ) : K :=
  ∑ j ∈ Finset.range (r + 1),
    (algebraMap F K (cW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WChip.mL j) *
        (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recLH j)⁻¹ +
      algebraMap F K (cW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WChip.mR j) *
        (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recRH j)⁻¹)

/-- The fill of row `r`, column `c ∈ 136..150`. -/
def fillMW (r c : ℕ) : F :=
  if c < 139 then coordN b (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.xKeyH r)⁻¹ (c - 136)
  else if c < 142 then coordN b (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recLH r)⁻¹ (c - 139)
  else if c < 145 then coordN b (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recRH r)⁻¹ (c - 142)
  else if c < 148 then coordN b (xaW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q r) (c - 145)
  else coordN b (paW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q r) (c - 148)

/-- **The re-filled VS walk twin trace.** -/
def refillW : Fin (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w → F[X] := fun c =>
  if hc : (c : ℕ) < 136 then Q ⟨c, by rw [walkChipHQ_width]; omega⟩
  else Lagrange.interpolate Finset.univ nodes
    (fun i : Fin n => fillMW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q (i : ℕ) c)

variable (cv pv : ℕ → F)

theorem refillW_trace_old (i : Fin n) (c : ℕ) (hc : c < 136) :
    (Reify.envOfTrace (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i) cv pv).trace c =
      (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 25 chals) (slotVal b 25 pubs)).trace c := by
  have h1 : c < (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w := by rw [walkChipH_width]; omega
  have h2 : c < (walkChipHQ δF kroots b hn nodes orbit chalsQ pubsQ).rap.w := by rw [walkChipHQ_width]; omega
  rw [envOfTrace_trace _ _ _ _ _ h1, envOfTrace_trace _ _ _ _ _ h2]
  simp only [refillW, dif_pos hc]

theorem refillW_next_old (i : Fin n) (c : ℕ) (hc : c < 136) :
    (Reify.envOfTrace (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i) cv pv).traceNext c =
      (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 25 chals) (slotVal b 25 pubs)).traceNext c := by
  have h1 : c < (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w := by rw [walkChipH_width]; omega
  have h2 : c < (walkChipHQ δF kroots b hn nodes orbit chalsQ pubsQ).rap.w := by rw [walkChipHQ_width]; omega
  rw [envOfTrace_traceNext _ _ _ _ _ h1, envOfTrace_traceNext _ _ _ _ _ h2]
  simp only [refillW, dif_pos hc]

theorem refillW_trace_new (hinj : Function.Injective nodes) (i : Fin n) (c : ℕ) (hc : 136 ≤ c) (hc' : c < 151) :
    (Reify.envOfTrace (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i) cv pv).trace c =
      fillMW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q (i : ℕ) c := by
  have h1 : c < (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w := by rw [walkChipH_width]; omega
  rw [envOfTrace_trace _ _ _ _ _ h1]
  simp only [refillW, dif_neg (show ¬ c < 136 by omega)]
  exact Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

theorem refillW_next_new (hinj : Function.Injective nodes) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (hadj : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) (c : ℕ) (hc : 136 ≤ c) (hc' : c < 151) :
    (Reify.envOfTrace (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i) cv pv).traceNext c =
      fillMW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q ((i : ℕ) + 1) c := by
  have h1 : c < (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w := by rw [walkChipH_width]; omega
  rw [envOfTrace_traceNext _ _ _ _ _ h1]
  simp only [refillW, dif_neg (show ¬ c < 136 by omega)]
  rw [mul_comm, ← hadj]
  exact Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := nodes)
    (fun i : Fin n => fillMW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q (i : ℕ) c) hinj.injOn
    (Finset.mem_univ (⟨(i : ℕ) + 1, hi⟩ : Fin n))

theorem fillMW_x (r : ℕ) (k : Fin 3) :
    fillMW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q r (136 + k) =
      coord b (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.xKeyH r)⁻¹ k := by
  have := k.isLt
  unfold fillMW
  rw [if_pos (by omega), show 136 + (k : ℕ) - 136 = k by omega]
  exact coordN_eq b _ k

theorem fillMW_L (r : ℕ) (k : Fin 3) :
    fillMW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q r (139 + k) =
      coord b (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recLH r)⁻¹ k := by
  have := k.isLt
  unfold fillMW
  rw [if_neg (by omega), if_pos (by omega), show 139 + (k : ℕ) - 139 = k by omega]
  exact coordN_eq b _ k

theorem fillMW_R (r : ℕ) (k : Fin 3) :
    fillMW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q r (142 + k) =
      coord b (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recRH r)⁻¹ k := by
  have := k.isLt
  unfold fillMW
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 142 + (k : ℕ) - 142 = k by omega]
  exact coordN_eq b _ k

theorem fillMW_xa (r : ℕ) (k : Fin 3) :
    fillMW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q r (145 + k) =
      coord b (xaW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q r) k := by
  have := k.isLt
  unfold fillMW
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 145 + (k : ℕ) - 145 = k by omega]
  exact coordN_eq b _ k

theorem fillMW_pa (r : ℕ) (k : Fin 3) :
    fillMW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q r (148 + k) =
      coord b (paW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q r) k := by
  have := k.isLt
  unfold fillMW
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show 148 + (k : ℕ) - 148 = k by omega]
  exact coordN_eq b _ k

/-- **The VS walk twin accepts the `𝕂` re-fill of a `𝕂′`-walk-twin-accepted trace.** -/
theorem walkChipH_of_HQ
    (hsatQ : RAP.SatisfiesWithPreprocessing (walkChipHQ δF kroots b hn nodes orbit chalsQ pubsQ) Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hc : ∀ i < 33, chalsQ i = chals i) (hp : ∀ i < 4, pubsQ i = pubs i)
    (hpX : ∀ j < n, dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.xKeyH j ≠ 0)
    (hpL : ∀ j < n, dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recLH j ≠ 0)
    (hpR : ∀ j < n, dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recRH j ≠ 0)
    (hpubX : pubs WalkHC.pubX = ∑ j ∈ Finset.range n,
      (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.xKeyH j)⁻¹)
    (hpubP : pubs WalkHC.pubP = ∑ j ∈ Finset.range n,
      (algebraMap F K (cW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WChip.mL j) *
          (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recLH j)⁻¹ +
        algebraMap F K (cW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WChip.mR j) *
          (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recRH j)⁻¹)) :
    RAP.SatisfiesWithPreprocessing (walkChipH δF kroots b hn nodes orbit chals pubs)
      (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q) := by
  obtain ⟨hsat, hbind⟩ := hsatQ
  have hW132 : (walkTemplate δF kroots).width 3 = 132 := WalkTraceH.walkTemplate_width δF kroots
  refine ⟨?_, ?_⟩
  · have hres : restrictQ 21 25 (shift_lt (walkTemplate δF kroots) (walkTemplateH δF kroots) 21 25
        (walkTemplate_baseCols δF kroots) (walkTemplateH_baseCols δF kroots) (by omega)
        (by rw [walkTemplate_extCols, walkTemplateH_extCols]; omega))
          (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q) =
        restrictWalkQ δF kroots b hn nodes orbit chalsQ pubsQ Q := by
      funext j
      have hj := j.isLt
      have hlt : shiftCol 21 25 j < 136 := by
        have : (j : ℕ) < 132 := by omega
        unfold shiftCol; split_ifs <;> omega
      simp only [restrictQ, restrictWalkQ, refillW, dif_pos hlt]
      rfl
    have h0 := CpCongr.walkChip_cp_congr δF b hn nodes orbit chalsQ pubsQ chals pubs kroots hc hp _
      (walkChipHQ_restrict_sat δF kroots b hn nodes orbit chalsQ pubsQ Q hsat)
    have h0' : (expandChip (walkTemplate δF kroots) b (slotVal b 21 chals) (slotVal b 21 pubs) orbit
        (rowNodeSet nodes)).Satisfies (restrictQ 21 25 (shift_lt (walkTemplate δF kroots) (walkTemplateH δF kroots)
          21 25 (walkTemplate_baseCols δF kroots) (walkTemplateH_baseCols δF kroots) (by omega)
          (by rw [walkTemplate_extCols, walkTemplateH_extCols]; omega))
          (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q)) := by
      have key : ∀ (X : RAP F) (P1 P2 : Fin X.w → F[X]), P1 = P2 → X.Satisfies P2 → X.Satisfies P1 :=
        fun X P1 P2 h hs => h ▸ hs
      exact key _ _ _ hres h0
    have hlQ := (expandChip_satisfies_iff_language (walkTemplateHQ δF kroots) b _ _ orbit _ Q).mp hsat
    refine expandChip_extend b orbit (rowNodeSet nodes) chals pubs (walkTemplate δF kroots) (walkTemplateH δF kroots)
      21 25 (walkTemplate_baseCols δF kroots) (walkTemplateH_baseCols δF kroots) (by omega)
      (by rw [walkTemplate_extCols, walkTemplateH_extCols]; omega)
      (fun g hg => ⟨List.mem_append_left _ hg, walkBase_below kroots g hg⟩)
      (fun g hg => ⟨List.mem_append_left _ hg, by rw [walkTemplate_extCols]; exact walkMixed_below δF kroots g hg⟩)
      rfl rfl (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q) h0' ?_ ?_
    · intro x hx g hg hg0
      obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
      have hgB : g ∈ (WalkHC.baseH : List (CoeffExpr F)) := by
        have hg' : g ∈ WChip.baseGates kroots ++ WalkHC.baseH := hg
        rcases List.mem_append.mp hg' with h1 | h1
        · exact absurd h1 hg0
        · exact h1
      have hQg := (hlQ (nodes i) (mem_rowNodeSet nodes i)).1 g hg
      rw [← hQg]
      exact colsBelow_eval (RangeHQ.walkHC_baseH_below g hgB)
        (fun j hj => refillW_trace_old δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i j (by omega))
        (fun j hj => refillW_next_old δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i j (by omega))
    intro x hx g hg hg0
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hgm : g ∈ WalkHC.gates (F := F) := by
      have hg' : g ∈ WChip.mixedGates δF kroots ++ WalkHC.gates (F := F) := hg
      rcases List.mem_append.mp hg' with h1 | h1
      · exact absurd h1 hg0
      · exact h1
    have hcol0 : ∀ r k : ℕ, (walkTemplateH δF kroots).col0 3 .traceCur r + k = 25 + 3 * r + k := by
      intro r k; simp only [ChipTemplate.col0, walkTemplateH_baseCols]
    have hcolN : ∀ r k : ℕ, (walkTemplateH δF kroots).col0 3 .traceNext r + k = 25 + 3 * r + k := hcol0
    -- denominators at the row (from the base columns)
    have hdenL : ∀ (l : List (CoeffExpr F)), (∀ g ∈ l, colsBelow 25 g = true) →
        (l.length = 4 ∨ l.length = 5) →
        (CellH.denKey l).eval (gatherEnv b ((walkTemplateH δF kroots).col0 3)
          (Reify.envOfTrace (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i)
            (slotVal b 25 chals) (slotVal b 25 pubs)))
          (Reify.envOfTrace (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i)
            (slotVal b 25 chals) (slotVal b 25 pubs)) = dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q l i := by
      intro l hl hlen
      have e := WalkTraceH.denAt_congr δF kroots b chals l hl
        (Reify.envOfTrace (refillW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i)
          (slotVal b 25 chals) (slotVal b 25 pubs))
        (rowW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q i) rfl rfl
        (fun j hj => refillW_trace_old δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i j (by omega))
        (fun j hj => refillW_next_old δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i j (by omega))
      unfold WalkTraceH.denAt at e
      rw [e]
      have hgc : ∀ r, (gatherEnv b ((walkTemplateH δF kroots).col0 3)
          (rowW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q i)).chal r = chals r :=
        WalkTraceH.gather_chal δF kroots b chals _ rfl
      simp only [dW, dif_pos i.isLt]
      rcases hlen with h4 | h5
      · rw [denKey_eval4 _ _ _ h4, hgc, hgc]
      · rw [ServeH.denKey_eval _ _ _ h5, hgc, hgc]
    have hbx := WalkTraceH.keys_below (F := F) WalkHC.xKeyH (Or.inl rfl)
    have hbl := WalkTraceH.keys_below (F := F) WalkHC.recLH (Or.inr (Or.inl rfl))
    have hbr := WalkTraceH.keys_below (F := F) WalkHC.recRH (Or.inr (Or.inr rfl))
    refine walkH_gates_honest _ _ n i i.isLt
      (fun j => cW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WChip.mL j)
      (fun j => cW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WChip.mR j)
      (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.xKeyH)
      (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recLH)
      (dW δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q WalkHC.recRH)
      (hpX i i.isLt) (hpL i i.isLt) (hpR i i.isLt) ?_ ?_ ?_ ?_ ?_ ?_
      (hdenL _ hbx (Or.inr (by simp [WalkHC.xKeyH]))) (hdenL _ hbl (Or.inl (by simp [WalkHC.recLH])))
      (hdenL _ hbr (Or.inl (by simp [WalkHC.recRH]))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ g hgm
    · rw [refillW_trace_old δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i WChip.isF (by decide)]
      exact (TeleHQ.walkHQ_masks δF kroots b hn nodes orbit chalsQ pubsQ Q hbind hinj i).1
    · rw [refillW_trace_old δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i WChip.isL (by decide)]
      refine (TeleHQ.walkHQ_masks δF kroots b hn nodes orbit chalsQ pubsQ Q hbind hinj i).2.trans ?_
      by_cases hh : (i : ℕ) + 1 = n
      · rw [if_pos (by omega), if_pos hh]
      · rw [if_neg (by omega), if_neg hh]
    · rw [refillW_trace_old δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i WChip.mL (by decide)]
      simp only [cW, dif_pos i.isLt]
    · rw [refillW_trace_old δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i WChip.mR (by decide)]
      simp only [cW, dif_pos i.isLt]
    · intro hi
      rw [refillW_next_old δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i WChip.mL (by decide)]
      refine (TeleHQ.qwEF_next δF kroots b hn nodes orbit chalsQ pubsQ Q hadj i hi WChip.mL).trans ?_
      simp only [cW, dif_pos hi]
      rfl
    · intro hi
      rw [refillW_next_old δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i WChip.mR (by decide)]
      refine (TeleHQ.qwEF_next δF kroots b hn nodes orbit chalsQ pubsQ Q hadj i hi WChip.mR).trans ?_
      simp only [cW, dif_pos hi]
      rfl
    · refine gather_trace b _ _ WalkHC.hxInv _ fun k => ?_
      rw [hcol0, show 25 + 3 * WalkHC.hxInv + (k : ℕ) = 136 + k by simp [WalkHC.hxInv],
        refillW_trace_new δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i _ (by omega)
          (by have := k.isLt; omega), fillMW_x]
    · intro hi
      refine gather_traceNext b _ _ WalkHC.hxInv _ fun k => ?_
      rw [hcolN, show 25 + 3 * WalkHC.hxInv + (k : ℕ) = 136 + k by simp [WalkHC.hxInv],
        refillW_next_new δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i hi (hadj i hi) _
          (by omega) (by have := k.isLt; omega), fillMW_x]
    · refine gather_trace b _ _ WalkHC.hpInvL _ fun k => ?_
      rw [hcol0, show 25 + 3 * WalkHC.hpInvL + (k : ℕ) = 139 + k by simp [WalkHC.hpInvL],
        refillW_trace_new δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i _ (by omega)
          (by have := k.isLt; omega), fillMW_L]
    · refine gather_trace b _ _ WalkHC.hpInvR _ fun k => ?_
      rw [hcol0, show 25 + 3 * WalkHC.hpInvR + (k : ℕ) = 142 + k by simp [WalkHC.hpInvR],
        refillW_trace_new δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i _ (by omega)
          (by have := k.isLt; omega), fillMW_R]
    · intro hi
      refine gather_traceNext b _ _ WalkHC.hpInvL _ fun k => ?_
      rw [hcolN, show 25 + 3 * WalkHC.hpInvL + (k : ℕ) = 139 + k by simp [WalkHC.hpInvL],
        refillW_next_new δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i hi (hadj i hi) _
          (by omega) (by have := k.isLt; omega), fillMW_L]
    · intro hi
      refine gather_traceNext b _ _ WalkHC.hpInvR _ fun k => ?_
      rw [hcolN, show 25 + 3 * WalkHC.hpInvR + (k : ℕ) = 142 + k by simp [WalkHC.hpInvR],
        refillW_next_new δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i hi (hadj i hi) _
          (by omega) (by have := k.isLt; omega), fillMW_R]
    · refine gather_trace b _ _ WalkHC.hxAcc _ fun k => ?_
      rw [hcol0, show 25 + 3 * WalkHC.hxAcc + (k : ℕ) = 145 + k by simp [WalkHC.hxAcc],
        refillW_trace_new δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i _ (by omega)
          (by have := k.isLt; omega), fillMW_xa]
      rfl
    · intro hi
      refine gather_traceNext b _ _ WalkHC.hxAcc _ fun k => ?_
      rw [hcolN, show 25 + 3 * WalkHC.hxAcc + (k : ℕ) = 145 + k by simp [WalkHC.hxAcc],
        refillW_next_new δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i hi (hadj i hi) _
          (by omega) (by have := k.isLt; omega), fillMW_xa]
      rfl
    · refine gather_trace b _ _ WalkHC.hpAcc _ fun k => ?_
      rw [hcol0, show 25 + 3 * WalkHC.hpAcc + (k : ℕ) = 148 + k by simp [WalkHC.hpAcc],
        refillW_trace_new δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i _ (by omega)
          (by have := k.isLt; omega), fillMW_pa]
      rfl
    · intro hi
      refine gather_traceNext b _ _ WalkHC.hpAcc _ fun k => ?_
      rw [hcolN, show 25 + 3 * WalkHC.hpAcc + (k : ℕ) = 148 + k by simp [WalkHC.hpAcc],
        refillW_next_new δF kroots b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i hi (hadj i hi) _
          (by omega) (by have := k.isLt; omega), fillMW_pa]
      rfl
    · rw [TeleH.gather_pub_T b (walkTemplateH δF kroots) 25 (walkTemplateH_baseCols δF kroots) _ pubs rfl]
      exact hpubX
    · rw [TeleH.gather_pub_T b (walkTemplateH δF kroots) 25 (walkTemplateH_baseCols δF kroots) _ pubs rfl]
      exact hpubP
  · intro j
    fin_cases j
    · have h0 : Q ⟨0, by rw [walkChipHQ_width]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 3; omega⟩
      refine Eq.trans ?_ h0
      simp only [refillW, dif_pos (show (0 : ℕ) < 136 by omega)]
      rfl
    · have h1 : Q ⟨1, by rw [walkChipHQ_width]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 3; omega⟩
      refine Eq.trans ?_ h1
      simp only [refillW, dif_pos (show (1 : ℕ) < 136 by omega)]
      rfl
    · have h2 : Q ⟨2, by rw [walkChipHQ_width]; omega⟩ = rootRowMaskW nodes kroots := hbind ⟨2, by show 2 < 3; omega⟩
      refine Eq.trans ?_ h2
      simp only [refillW, dif_pos (show (2 : ℕ) < 136 by omega)]
      rfl

end Walk

end

end Nock.NockVMROM.Thm54.VclL.Handle.RefillWQ
