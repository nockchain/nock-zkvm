/-
  Nock/NockVMROM/Thm54/VclL/Handle/RefillMQ.lean

  Additive.

  Given a trace `Q` (238 columns) accepted by the `𝕂′` cell twin `cellChipHQ` at `chalsQ / pubsQ`,
  `refillC` keeps its columns `0..225` (the original cell chip's `225` columns and the multiplicity `mh`, as
  the SAME polynomials) and interpolates on `226..231` the `𝕂` fill at the handle leaves `33 / 34` of
  `chals`: the inverse `den⁻¹` and the inclusive prefix sum of `mh · den⁻¹`.
  **`cellChipH_of_HQ`**: when `chals` / `pubs` agree with `chalsQ` / `pubsQ` on the leaves `< 33` / publics
  `< 4` (all the original chip reads, `CpCongr`), every row's key has a nonzero denominator at the `𝕂`
  coins and the terminal `pubs 4` is the total, the VS cell twin `cellChipH` accepts `refillC` (with its
  preprocessing).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CpCongr
import Nock.NockVMROM.Thm54.VclL.Handle.CellTraceH
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
import Nock.NockVMROM.Thm54.VclL.Handle.IOVS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RefillMQ

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Module
open scoped Polynomial

noncomputable section

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chalsQ pubsQ chals pubs : ℕ → K)
  (Q : Fin (cellChipHQ δF b hn nodes orbit chalsQ pubsQ).rap.w → F[X])

/-- Row `i`'s base environment of `Q`. -/
abbrev rowC (i : Fin n) : Env F :=
  Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 130 chals) (slotVal b 130 pubs)

/-- Row `j`'s handle denominator at the `𝕂` coins of `chals` (`1` off the rows). -/
def dC (j : ℕ) : K :=
  if hj : j < n then compress ⟨chals CellH.hGam, chals CellH.hRho⟩
    (ServeH.keyVec5 CellH.keyH (rowC δF b hn nodes orbit chalsQ pubsQ chals pubs Q ⟨j, hj⟩)) else 1

/-- Row `j`'s multiplicity (`0` off the rows). -/
def mC (j : ℕ) : F :=
  if hj : j < n then (rowC δF b hn nodes orbit chalsQ pubsQ chals pubs Q ⟨j, hj⟩).trace CellH.mh else 0

/-- The inclusive prefix sum of `mh · den⁻¹`. -/
def aC (r : ℕ) : K :=
  ∑ j ∈ Finset.range (r + 1), algebraMap F K (mC δF b hn nodes orbit chalsQ pubsQ chals pubs Q j) *
    (dC δF b hn nodes orbit chalsQ pubsQ chals pubs Q j)⁻¹

/-- The fill of row `r`, column `c ∈ 226..231`. -/
def fillMC (r c : ℕ) : F :=
  if c < 229 then coordN b (dC δF b hn nodes orbit chalsQ pubsQ chals pubs Q r)⁻¹ (c - 226)
  else coordN b (aC δF b hn nodes orbit chalsQ pubsQ chals pubs Q r) (c - 229)

/-- **The re-filled VS cell twin trace.** -/
def refillC : Fin (cellChipH δF b hn nodes orbit chals pubs).rap.w → F[X] := fun c =>
  if hc : (c : ℕ) < 226 then Q ⟨c, by rw [cellChipHQ_width]; omega⟩
  else Lagrange.interpolate Finset.univ nodes
    (fun i : Fin n => fillMC δF b hn nodes orbit chalsQ pubsQ chals pubs Q (i : ℕ) c)

variable (cv pv : ℕ → F)

theorem refillC_trace_old (i : Fin n) (c : ℕ) (hc : c < 226) :
    (Reify.envOfTrace (refillC δF b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i) cv pv).trace c =
      (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 130 chals) (slotVal b 130 pubs)).trace c := by
  have h1 : c < (cellChipH δF b hn nodes orbit chals pubs).rap.w := by rw [cellChipH_width]; omega
  have h2 : c < (cellChipHQ δF b hn nodes orbit chalsQ pubsQ).rap.w := by rw [cellChipHQ_width]; omega
  rw [envOfTrace_trace _ _ _ _ _ h1, envOfTrace_trace _ _ _ _ _ h2]
  simp only [refillC, dif_pos hc]

theorem refillC_next_old (i : Fin n) (c : ℕ) (hc : c < 226) :
    (Reify.envOfTrace (refillC δF b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i) cv pv).traceNext c =
      (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 130 chals) (slotVal b 130 pubs)).traceNext c := by
  have h1 : c < (cellChipH δF b hn nodes orbit chals pubs).rap.w := by rw [cellChipH_width]; omega
  have h2 : c < (cellChipHQ δF b hn nodes orbit chalsQ pubsQ).rap.w := by rw [cellChipHQ_width]; omega
  rw [envOfTrace_traceNext _ _ _ _ _ h1, envOfTrace_traceNext _ _ _ _ _ h2]
  simp only [refillC, dif_pos hc]

theorem refillC_trace_new (hinj : Function.Injective nodes) (i : Fin n) (c : ℕ) (hc : 226 ≤ c) (hc' : c < 232) :
    (Reify.envOfTrace (refillC δF b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i) cv pv).trace c =
      fillMC δF b hn nodes orbit chalsQ pubsQ chals pubs Q (i : ℕ) c := by
  have h1 : c < (cellChipH δF b hn nodes orbit chals pubs).rap.w := by rw [cellChipH_width]; omega
  rw [envOfTrace_trace _ _ _ _ _ h1]
  simp only [refillC, dif_neg (show ¬ c < 226 by omega)]
  exact Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

theorem refillC_next_new (hinj : Function.Injective nodes) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (hadj : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) (c : ℕ) (hc : 226 ≤ c) (hc' : c < 232) :
    (Reify.envOfTrace (refillC δF b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i) cv pv).traceNext c =
      fillMC δF b hn nodes orbit chalsQ pubsQ chals pubs Q ((i : ℕ) + 1) c := by
  have h1 : c < (cellChipH δF b hn nodes orbit chals pubs).rap.w := by rw [cellChipH_width]; omega
  rw [envOfTrace_traceNext _ _ _ _ _ h1]
  simp only [refillC, dif_neg (show ¬ c < 226 by omega)]
  rw [mul_comm, ← hadj]
  exact Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := nodes)
    (fun i : Fin n => fillMC δF b hn nodes orbit chalsQ pubsQ chals pubs Q (i : ℕ) c) hinj.injOn
    (Finset.mem_univ (⟨(i : ℕ) + 1, hi⟩ : Fin n))

theorem fillMC_inv (r : ℕ) (k : Fin 3) :
    fillMC δF b hn nodes orbit chalsQ pubsQ chals pubs Q r (226 + k) =
      coord b (dC δF b hn nodes orbit chalsQ pubsQ chals pubs Q r)⁻¹ k := by
  have := k.isLt
  unfold fillMC
  rw [if_pos (by omega), show 226 + (k : ℕ) - 226 = k by omega]
  exact coordN_eq b _ k

theorem fillMC_acc (r : ℕ) (k : Fin 3) :
    fillMC δF b hn nodes orbit chalsQ pubsQ chals pubs Q r (229 + k) =
      coord b (aC δF b hn nodes orbit chalsQ pubsQ chals pubs Q r) k := by
  have := k.isLt
  unfold fillMC
  rw [if_neg (by omega), show 229 + (k : ℕ) - 229 = k by omega]
  exact coordN_eq b _ k

/-- **The VS cell twin accepts the `𝕂` re-fill of a `𝕂′`-cell-twin-accepted trace.** -/
theorem cellChipH_of_HQ
    (hsatQ : RAP.SatisfiesWithPreprocessing (cellChipHQ δF b hn nodes orbit chalsQ pubsQ) Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hc : ∀ i < 33, chalsQ i = chals i) (hp : ∀ i < 4, pubsQ i = pubs i)
    (hpole : ∀ j < n, dC δF b hn nodes orbit chalsQ pubsQ chals pubs Q j ≠ 0)
    (hpub : pubs CellH.pubH = ∑ j ∈ Finset.range n,
      algebraMap F K (mC δF b hn nodes orbit chalsQ pubsQ chals pubs Q j) *
        (dC δF b hn nodes orbit chalsQ pubsQ chals pubs Q j)⁻¹) :
    RAP.SatisfiesWithPreprocessing (cellChipH δF b hn nodes orbit chals pubs)
      (refillC δF b hn nodes orbit chalsQ pubsQ chals pubs Q) := by
  obtain ⟨hsat, hbind⟩ := hsatQ
  refine ⟨?_, ?_⟩
  · have hres : restrictQ 129 130 (shift_lt (cellTemplate δF) (cellTemplateH δF) 129 130 (cellTemplate_baseCols δF)
        (cellTemplateH_baseCols δF) (by omega) (by rw [cellTemplate_extCols, cellTemplateH_extCols]; omega))
          (refillC δF b hn nodes orbit chalsQ pubsQ chals pubs Q) =
        restrictCellQ δF b hn nodes orbit chalsQ pubsQ Q := by
      funext j
      have hj := j.isLt
      have hlt : shiftCol 129 130 j < 226 := by
        have : (j : ℕ) < 225 := by
          have h225 : (cellTemplate δF).width 3 = 225 := CellTraceH.cellTemplate_width δF
          omega
        unfold shiftCol; split_ifs <;> omega
      simp only [restrictQ, restrictCellQ, refillC, dif_pos hlt]
      rfl
    have h0 := CpCongr.cellChip_cp_congr δF b hn nodes orbit chalsQ pubsQ chals pubs hc hp _
      (cellChipHQ_restrict_sat δF b hn nodes orbit chalsQ pubsQ Q hsat)
    have h0' : (expandChip (cellTemplate δF) b (slotVal b 129 chals) (slotVal b 129 pubs) orbit
        (rowNodeSet nodes)).Satisfies (restrictQ 129 130 (shift_lt (cellTemplate δF) (cellTemplateH δF) 129 130
          (cellTemplate_baseCols δF) (cellTemplateH_baseCols δF) (by omega)
          (by rw [cellTemplate_extCols, cellTemplateH_extCols]; omega))
          (refillC δF b hn nodes orbit chalsQ pubsQ chals pubs Q)) := by
      have key : ∀ (X : RAP F) (P1 P2 : Fin X.w → F[X]), P1 = P2 → X.Satisfies P2 → X.Satisfies P1 :=
        fun X P1 P2 h hs => h ▸ hs
      exact key _ _ _ hres h0
    refine expandChip_extend b orbit (rowNodeSet nodes) chals pubs (cellTemplate δF) (cellTemplateH δF) 129 130
      (cellTemplate_baseCols δF) (cellTemplateH_baseCols δF) (by omega)
      (by rw [cellTemplate_extCols, cellTemplateH_extCols]; omega)
      (fun g hg => ⟨hg, cellBase_below g hg⟩)
      (fun g hg => ⟨List.mem_append_left _ hg, by rw [cellTemplate_extCols]; exact cellMixed_below δF g hg⟩)
      rfl rfl (refillC δF b hn nodes orbit chalsQ pubsQ chals pubs Q)
      h0' (fun x hx g hg hg0 => absurd hg hg0) ?_
    intro x hx g hg hg0
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
    have hgm : g ∈ CellH.gates (F := F) := by
      have hg' : g ∈ Cell.mixedGates δF ++ CellH.gates (F := F) := hg
      rcases List.mem_append.mp hg' with h1 | h1
      · exact absurd h1 hg0
      · exact h1
    have hcol0 : ∀ r k : ℕ, (cellTemplateH δF).col0 3 .traceCur r + k = 130 + 3 * r + k := by
      intro r k; simp only [ChipTemplate.col0, cellTemplateH_baseCols]
    have hcolN : ∀ r k : ℕ, (cellTemplateH δF).col0 3 .traceNext r + k = 130 + 3 * r + k := hcol0
    have hdi : dC δF b hn nodes orbit chalsQ pubsQ chals pubs Q i =
        compress ⟨chals CellH.hGam, chals CellH.hRho⟩
          (ServeH.keyVec5 CellH.keyH (rowC δF b hn nodes orbit chalsQ pubsQ chals pubs Q i)) := by
      simp only [dC, dif_pos i.isLt]
    have hden : (CellH.denKey (CellH.keyH (F := F))).eval
        (gatherEnv b ((cellTemplateH δF).col0 3) (rowC δF b hn nodes orbit chalsQ pubsQ chals pubs Q i))
        (rowC δF b hn nodes orbit chalsQ pubsQ chals pubs Q i) = dC δF b hn nodes orbit chalsQ pubsQ chals pubs Q i := by
      rw [ServeH.denKey_eval _ _ _ rfl, TeleH.gather_chal_T b (cellTemplateH δF) 130 (cellTemplateH_baseCols δF) _
        chals rfl, TeleH.gather_chal_T b (cellTemplateH δF) 130 (cellTemplateH_baseCols δF) _ chals rfl, hdi]
    refine cellH_gates_honest (gatherEnv b ((cellTemplateH δF).col0 3)
      (Reify.envOfTrace (refillC δF b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i)
        (slotVal b 130 chals) (slotVal b 130 pubs)))
      (Reify.envOfTrace (refillC δF b hn nodes orbit chalsQ pubsQ chals pubs Q) orbit.ω (nodes i)
        (slotVal b 130 chals) (slotVal b 130 pubs)) n i i.isLt
      (mC δF b hn nodes orbit chalsQ pubsQ chals pubs Q) (dC δF b hn nodes orbit chalsQ pubsQ chals pubs Q)
      (hpole i i.isLt) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ g hgm
    · rw [refillC_trace_old δF b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i Cell.isF (by decide)]
      exact (TeleHQ.cellHQ_masks δF b hn nodes orbit chalsQ pubsQ Q hbind hinj i).1
    · rw [refillC_trace_old δF b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i Cell.isL (by decide)]
      have m2 := (TeleHQ.cellHQ_masks δF b hn nodes orbit chalsQ pubsQ Q hbind hinj i).2
      refine m2.trans ?_
      by_cases hh : (i : ℕ) + 1 = n
      · rw [if_pos (by omega), if_pos hh]
      · rw [if_neg (by omega), if_neg hh]
    · rw [refillC_trace_old δF b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i CellH.mh (by decide)]
      simp only [mC, dif_pos i.isLt]
    · intro hi
      rw [refillC_next_old δF b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i CellH.mh (by decide)]
      refine (TeleHQ.qcEF_next δF b hn nodes orbit chalsQ pubsQ Q hadj i hi CellH.mh).trans ?_
      simp only [mC, dif_pos hi]
      rfl
    · refine Eq.trans ?_ hden
      refine CellTraceH.denKey_congr δF b chals _ _ rfl rfl (fun j hj => ?_) (fun j hj => ?_)
      · exact refillC_trace_old δF b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i j (by omega)
      · exact refillC_next_old δF b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ i j (by omega)
    · refine gather_trace b _ _ CellH.invH _ fun k => ?_
      rw [hcol0, show 130 + 3 * CellH.invH + (k : ℕ) = 226 + k by simp [CellH.invH],
        refillC_trace_new δF b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i _ (by omega)
          (by have := k.isLt; omega), fillMC_inv]
    · intro hi
      refine gather_traceNext b _ _ CellH.invH _ fun k => ?_
      rw [hcolN, show 130 + 3 * CellH.invH + (k : ℕ) = 226 + k by simp [CellH.invH],
        refillC_next_new δF b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i hi (hadj i hi) _ (by omega)
          (by have := k.isLt; omega), fillMC_inv]
    · refine gather_trace b _ _ CellH.accH _ fun k => ?_
      rw [hcol0, show 130 + 3 * CellH.accH + (k : ℕ) = 229 + k by simp [CellH.accH],
        refillC_trace_new δF b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i _ (by omega)
          (by have := k.isLt; omega), fillMC_acc]
      rfl
    · intro hi
      refine gather_traceNext b _ _ CellH.accH _ fun k => ?_
      rw [hcolN, show 130 + 3 * CellH.accH + (k : ℕ) = 229 + k by simp [CellH.accH],
        refillC_next_new δF b hn nodes orbit chalsQ pubsQ chals pubs Q _ _ hinj i hi (hadj i hi) _ (by omega)
          (by have := k.isLt; omega), fillMC_acc]
      rfl
    · rw [TeleH.gather_pub_T b (cellTemplateH δF) 130 (cellTemplateH_baseCols δF) _ pubs rfl]
      exact hpub
  · intro j
    fin_cases j
    · have h0 : Q ⟨0, by rw [cellChipHQ_width]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
      refine Eq.trans ?_ h0
      simp only [refillC, dif_pos (show (0 : ℕ) < 226 by omega)]
      rfl
    · have h1 : Q ⟨1, by rw [cellChipHQ_width]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
      refine Eq.trans ?_ h1
      simp only [refillC, dif_pos (show (1 : ℕ) < 226 by omega)]
      rfl

end Cell

end

end Nock.NockVMROM.Thm54.VclL.Handle.RefillMQ
