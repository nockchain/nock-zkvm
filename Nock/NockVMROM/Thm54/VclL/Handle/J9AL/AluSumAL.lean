/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluSumAL.lean

  **The list-sum forms of the three ALU telescopes.**

  `AluTeleAL` proves the three accumulator telescopes of `aluSZChipJ9` over `Fp` (the ALU is reached at
  `p = Nock.Atoms.p`, as `AluSZOps`).  This module turns each into the list-sum form of the coin-free lists of `RealIOJ9AL`
  at `p = Nock.Atoms.p` (S8's `hbalAL` reaches them by `subst hpG`):
  * `aluX_sumL`: `Σ_{keyX ∈ aluExportReqsOf} compress(κ, keyX)⁻¹ = (pubALx, pubALx+1)`;
  * `aluS_sumL`: `Σ_{aluRegReqsOf} compress⁻¹ − Σ_{aluRegProvsOf ++ aluJetProvsOf} w·compress⁻¹ = (pubALs, pubALs+1)`;
  * `aluV_sumL`: `Σ_{aluFpReqsOf} compress(⟨γV, ρV⟩, ·)⁻¹ = (pubALv, pubALv+1)` (`den(valKey)` through
    `Telescope.den_ev_compress`).
  The activities `sH` (`gKind`) and `aV = fst·(mR + mV)` (`gFlag`, `gSlot`, the six one-hot modes) are boolean, so a
  kept row has weight `1`; the dropped rows have activity `0` and contribute `0`.
  `κ = ((chals 33, chals 35), (chals 34, chals 36))`, the handle coins of the `𝕂′` key denominators (as the axis chip).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.RR49AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluTeleAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.AxisTeleJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSumAL

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZRead (qe_zero ag_zero mem_kind mem_slot mem_flag modes_sum
  mode_bool)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG CopyG Op)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZOps (aluEF aluEK alu_rowGates)
open Nock.NockVMROM.Thm54.VclL.Handle.AluTeleAL (fv qv alu_qe alu_teleX alu_teleV alu_teleS wSv)
open Nock.Atoms (Fp)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Module
open scoped Polynomial

noncomputable section

section Tele
variable {K : Type} [Field K] [Algebra Fp K] [FiniteDimensional Fp K] [Fintype K] (δ : Fp)
  [Fact (¬ IsSquare (algebraMap Fp K δ))] (b : Basis (Fin 3) Fp K)
  (Pb : PubJ9AL Nock.Atoms.p) (tr : TrJ9AL Fp) (chals pubs : ℕ → K)

local notation "𝕂′" => Quad (algebraMap Fp K δ)
local notation "CH" => aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL
local notation "QL" => qAL δ b Pb tr chals pubs
local notation "FV" => fv b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL
local notation "QV" => qv b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL
local notation "EF" => aluEF b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL
local notation "EK" => aluEK b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL

/-- The handle coins of the `𝕂′` key denominators. -/
abbrev κ : IOCoins 𝕂′ := ⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩

theorem eK_chal (i : Fin Pb.nL) (j : ℕ) : (EK i).chal j = chals j :=
  TeleH.gather_chal_T b (aluTemplateSZ δ) 94 (aluTemplateSZ_baseCols δ) _ chals rfl j

/-! ## The inverses and the booleans -/

/-- An activity-gated inverse `act·(inv·den − 1) = 0` with `act ≠ 0`: `inv = den⁻¹`. -/
theorem inv_of (hsat : (CH).rap.Satisfies QL) (i : Fin Pb.nL) {act : CoeffExpr Fp} {inv : ℕ}
    {d : QE Fp} (he : invG δ act inv d ∈ aluQ δ) (hact : act.eval (EF i) ≠ 0) :
    QV inv i = (d.ev δ (EK i) (EF i))⁻¹ := by
  have g := alu_qe b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat i he
  simp only [invG, ev_scale, ev_sub, ev_mul, ev_var, ev_one] at g
  rcases mul_eq_zero.mp g with h | h
  · exact absurd ((map_eq_zero_iff _ (algebraMap Fp K).injective).mp
      ((map_eq_zero_iff (algebraMap K 𝕂′) (algebraMap K 𝕂′).injective).mp h)) hact
  · exact eq_inv_of_mul_eq_one_left (sub_eq_zero.mp h)

/-- `sH` is boolean (`gKind`). -/
theorem sH_bool (hsat : (CH).rap.Satisfies QL) (i : Fin Pb.nL) : FV sH i = 0 ∨ FV sH i = 1 := by
  have g := ag_zero (alu_rowGates b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat i)
    (mem_kind (a := ar (boolE (cv sH))) (by simp [gKind]))
  simp only [AG.gate, ar, boolE, cv, CoeffExpr.eval] at g
  exact Chips.CertBound.bool_cases g

/-- **`aV = fst·(mR + mV)` is boolean** (`gFlag`; `fst = 1` forces `sL = 1` (`gSlot`), and the six boolean modes
sum to `sL`, so at most one of `mR`, `mV` is `1`). -/
theorem aV_bool (hsat : (CH).rap.Satisfies QL) (i : Fin Pb.nL) : FV aV i = 0 ∨ FV aV i = 1 := by
  have h := alu_rowGates b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat i
  set e := EF i with he
  have gA := ag_zero h (mem_flag (a := ar (.sub (cv aV) (.mul (cv fst) (sumC [mR, mV])))) (by simp [gFlag]))
  simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at gA
  have gF := ag_zero h (mem_slot (a := ar (boolE (cv fst))) (by simp [gSlot]))
  simp only [AG.gate, ar, boolE, cv, CoeffExpr.eval] at gF
  have gS := ag_zero h (mem_slot (a := ar (.mul (cv fst) (notE (cv sL)))) (by simp [gSlot]))
  simp only [AG.gate, ar, notE, cv, CoeffExpr.eval] at gS
  have hA : e.trace aV = e.trace fst * (e.trace mR + e.trace mV) := sub_eq_zero.mp gA
  rcases Chips.CertBound.bool_cases gF with h0 | h1
  · left; show e.trace aV = 0; rw [hA, h0, zero_mul]
  · have hsL : e.trace sL = 1 := by rw [h1, one_mul] at gS; exact (sub_eq_zero.mp gS).symm
    have hs := modes_sum h
    obtain ⟨cR, hR1, hR⟩ := mode_bool h (j := mR) (by simp [modeCols])
    obtain ⟨cS, hS1, hS⟩ := mode_bool h (j := mS) (by simp [modeCols])
    obtain ⟨cV, hV1, hV⟩ := mode_bool h (j := mV) (by simp [modeCols])
    obtain ⟨cW, hW1, hW⟩ := mode_bool h (j := mW) (by simp [modeCols])
    obtain ⟨c1, h11, h1'⟩ := mode_bool h (j := mQ1) (by simp [modeCols])
    obtain ⟨cM, hM1, hM⟩ := mode_bool h (j := mQM) (by simp [modeCols])
    rw [hsL, hR, hS, hV, hW, h1', hM] at hs
    have hp7 : 7 < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
    have hsum : cR + cS + cV + cW + c1 + cM = 1 := by
      have e1 : (((cR + cS + cV + cW + c1 + cM : ℕ)) : Fp) = ((1 : ℕ) : Fp) := by push_cast; exact hs.symm
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e1
      exact e1
    have hA' : e.trace aV = ((cR + cV : ℕ) : Fp) := by rw [hA, h1, hR, hV, one_mul]; push_cast; ring
    rcases Nat.lt_or_ge (cR + cV) 1 with hl | hl
    · left; show e.trace aV = 0; rw [hA', show cR + cV = 0 by omega]; simp
    · right; show e.trace aV = 1; rw [hA', show cR + cV = 1 by omega]; simp

/-! ## The list-sum forms -/

/-- The coin-free row environment and the chip-view row environment have the same base trace. -/
theorem trace_eq (i : Fin Pb.nL) : (alE0 (K := K) δ b Pb tr i).trace = (EF i).trace := rfl

/-- A key read off `RE` entries depends on the base trace only. -/
theorem keyVecL_RE (m : ℕ) (lr : List RE) {e e' : Env Fp} (ht : e.trace = e'.trace) :
    AxisChipJ9.keyVecL (K := K) m (lr.map (reE (F := Fp))) e =
      AxisChipJ9.keyVecL (K := K) m (lr.map (reE (F := Fp))) e' := by
  funext c
  simp only [AxisChipJ9.keyVecL]
  congr 1
  rcases Nat.lt_or_ge (c : ℕ) (lr.map (reE (F := Fp))).length with hc | hc
  · rw [List.getD_eq_getElem _ _ hc, List.getElem_map]
    obtain ⟨x, hx⟩ : ∃ x, lr[(c : ℕ)]'(by simpa using hc) = x := ⟨_, rfl⟩
    simp only [hx]
    cases x <;> simp [reE, CoeffExpr.eval, cv, ht]
  · rw [List.getD_eq_default _ _ hc]; rfl

/-- **The export list-sum**: the `hdr` export consumes sum to the export terminal. -/
theorem aluX_sumL (hsat : (CH).rap.Satisfies QL) (hbind : (CH).BindsPreprocessing QL)
    (hinj : Function.Injective Pb.nodesL)
    (hadj : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω) :
    ((aluExportReqsOf (K := K) δ b Pb tr).map fun r => (compress (κ δ chals) (liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (pubs pubALx) (pubs (pubALx + 1)) := by
  rw [← alu_teleX b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat hbind hinj hadj]
  unfold aluExportReqsOf
  rw [AxisTeleJ9.sum_map_flatMap, Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_eq δ b Pb tr chals pubs i]
  rcases sH_bool δ b Pb tr chals pubs hsat i with h0 | h1
  · have h0' : (EF i).trace sH = 0 := h0
    rw [if_pos h0']; simp [fv, h0']
  · have h1' : (EF i).trace sH = 1 := h1
    rw [if_neg (by rw [h1']; exact one_ne_zero)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, fv, h1', liftQ, map_one, one_mul]
    rw [inv_of δ b Pb tr chals pubs hsat i (act := cv sH) (inv := invX) (d := HQ.denKeyQ δ keyXE)
      (List.mem_append_right _ (by simp [logupQ])) (by simp only [CoeffExpr.eval, cv]; rw [h1']; exact one_ne_zero),
      AxisTeleJ9.denKeyQ_evL δ _ _ 5 keyXE (by simp [keyXE, keyXRE])]
    simp only [TeleHQ.coinsQ, eK_chal, κ]
    rw [show (keyXE : List (CoeffExpr Fp)) = keyXRE.map reE from rfl,
      keyVecL_RE (K := K) 5 keyXRE (trace_eq δ b Pb tr chals pubs i)]

/-- A key denominator at row `i`, as `compress` of the coin-free key. -/
theorem den_eq (lr : List RE) (hl : lr.length ≤ 8) (i : Fin Pb.nL) :
    (HQ.denKeyQ δ (lr.map (reE (F := Fp)))).ev δ (EK i) (EF i) =
      compress (κ δ chals) (liftRec (L := 𝕂′) (AxisChipJ9.keyVecL (K := K) 8 (lr.map (reE (F := Fp)))
        (alE0 (K := K) δ b Pb tr i))) := by
  rw [AxisTeleJ9.denKeyQ_evL δ _ _ 8 _ (by simpa using hl)]
  simp only [TeleHQ.coinsQ, eK_chal, κ]
  rw [keyVecL_RE (K := K) 8 lr (trace_eq δ b Pb tr chals pubs i)]

/-- **The per-row service identity** (abstract): the `hdr` consumes minus the `preg` and jet provides of one row
equal the telescope term `wS·(invR + invO) − sH·mJ·invJ`, when `sH`, `sP` are boolean. -/
theorem rowS_alg (f : (Fin 8 → K) → 𝕂′) (kR kO kJ : Fin 8 → K) {iR iO iJ : 𝕂′} {h s m mj : Fp}
    (hh : h = 0 ∨ h = 1) (hs : s = 0 ∨ s = 1)
    (hR : h + s ≠ 0 → iR = f kR) (hO : h + s ≠ 0 → iO = f kO) (hJ : h ≠ 0 → iJ = f kJ) :
    ((if h = 0 then [] else [kR, kO]).map f).sum -
      (((if s * m = 0 then [] else [(kR, algebraMap Fp K (s * m)), (kO, algebraMap Fp K (s * m))]).map
          fun q => algebraMap K 𝕂′ q.2 * f q.1).sum +
        ((if h * mj = 0 then [] else [(kJ, algebraMap Fp K (h * mj))]).map
          fun q => algebraMap K 𝕂′ q.2 * f q.1).sum) =
      liftQ δ (h - s * m) * iR + liftQ δ (h - s * m) * iO - liftQ δ (h * mj) * iJ := by
  have e1 : ∀ x : Fp, ((if x = 0 then [] else [(kR, algebraMap Fp K x), (kO, algebraMap Fp K x)]).map
      fun q => algebraMap K 𝕂′ q.2 * f q.1).sum = liftQ δ x * (f kR + f kO) := by
    intro x; split_ifs with hx
    · simp [hx, liftQ]
    · simp [liftQ]; ring
  have e2 : ∀ x : Fp, ((if x = 0 then [] else [(kJ, algebraMap Fp K x)]).map
      fun q => algebraMap K 𝕂′ q.2 * f q.1).sum = liftQ δ x * f kJ := by
    intro x; split_ifs with hx
    · simp [hx, liftQ]
    · simp [liftQ]
  have h2 : (1 : Fp) + 1 ≠ 0 := by
    intro h2
    have h' := congrArg ZMod.val h2
    rw [ZMod.val_zero, show (1 : Fp) + 1 = ((2 : ℕ) : Fp) by norm_num, ZMod.val_natCast] at h'
    norm_num [Nock.Atoms.p, Nock.Field.p] at h'
  rw [e1, e2]
  rcases hh with rfl | rfl <;> rcases hs with rfl | rfl
  · simp [liftQ]
  · rw [hR (by simp), hO (by simp)]; simp [liftQ]; try ring
  · rw [hR (by simp), hO (by simp), hJ one_ne_zero]; simp [liftQ]; try ring
  · rw [hR h2, hO h2, hJ one_ne_zero]; simp [liftQ]; try ring

/-- **The service list-sum**: the `hdr` consumes minus the `preg` and jet provides sum to the service terminal
(`sP`, the preg selector, is boolean: verifier preprocessing). -/
theorem aluS_sumL (hsat : (CH).rap.Satisfies QL) (hbind : (CH).BindsPreprocessing QL)
    (hinj : Function.Injective Pb.nodesL)
    (hadj : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω)
    (hsP : ∀ i : Fin Pb.nL, FV sP i = 0 ∨ FV sP i = 1) :
    ((aluRegReqsOf (K := K) δ b Pb tr).map fun r => (compress (κ δ chals) (liftRec (L := 𝕂′) r))⁻¹).sum -
      ((aluRegProvsOf (K := K) δ b Pb tr ++ aluJetProvsOf (K := K) δ b Pb tr).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (κ δ chals) (liftRec (L := 𝕂′) q.1))⁻¹).sum =
      Quad.mk _ (pubs pubALs) (pubs (pubALs + 1)) := by
  rw [← alu_teleS b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat hbind hinj hadj]
  unfold aluRegReqsOf aluRegProvsOf aluJetProvsOf
  rw [List.map_append, List.sum_append, AxisTeleJ9.sum_map_flatMap, AxisTeleJ9.sum_map_flatMap,
    AxisTeleJ9.sum_map_flatMap, Chips.ChipRAP.sum_finRange, Chips.ChipRAP.sum_finRange, Chips.ChipRAP.sum_finRange,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_eq δ b Pb tr chals pubs i]
  have hR := den_eq δ b Pb tr chals pubs keyRgRE (by simp [keyRgRE]) i
  have hO := den_eq δ b Pb tr chals pubs opRecRE (by simp [opRecRE]) i
  have hJ := den_eq δ b Pb tr chals pubs keyJetRE (by simp [keyJetRE]) i
  have hmR : invG δ (sumC [sH, sP]) invR (HQ.denKeyQ δ keyRgE) ∈ aluQ δ :=
    List.mem_append_right _ (by simp [logupQ])
  have hmO : invG δ (sumC [sH, sP]) invO (HQ.denKeyQ δ opRecE) ∈ aluQ δ :=
    List.mem_append_right _ (by simp [logupQ])
  have hmJ : invG δ (cv sH) invJ (HQ.denKeyQ δ keyJetE) ∈ aluQ δ :=
    List.mem_append_right _ (by simp [logupQ])
  have hsum : (sumC [sH, sP] : CoeffExpr Fp).eval (EF i) = (EF i).trace sH + (EF i).trace sP := by
    simp [sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv]
  refine rowS_alg δ _ _ _ _ (sH_bool δ b Pb tr chals pubs hsat i) (hsP i) ?_ ?_ ?_
  · intro hne
    rw [inv_of δ b Pb tr chals pubs hsat i hmR (by rw [hsum]; exact hne)]
    exact congrArg _ hR
  · intro hne
    rw [inv_of δ b Pb tr chals pubs hsat i hmO (by rw [hsum]; exact hne)]
    exact congrArg _ hO
  · intro hne
    rw [inv_of δ b Pb tr chals pubs hsat i hmJ (by simpa [CoeffExpr.eval, cv] using hne)]
    exact congrArg _ hJ

/-- **The validity list-sum**: the ALU's validity reads (`aV ≠ 0`, key `[z, 0, L, 0, sv]`) sum to the validity
terminal, at validity coins `(γ, ρ)` read off the ALU challenge vector (`ChalsOK … 5`). -/
theorem aluV_sumL (hsat : (CH).rap.Satisfies QL) (hbind : (CH).BindsPreprocessing QL)
    (hinj : Function.Injective Pb.nodesL)
    (hadj : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω)
    (γ ρ : 𝕂′) (hok : ChalsOK δ chals γ ρ 5) :
    ((aluFpReqsOf (K := K) δ b Pb tr chals).map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum =
      Quad.mk _ (pubs pubALv) (pubs (pubALv + 1)) := by
  rw [← alu_teleV b Pb.hnL Pb.nodesL Pb.orbitL chals pubs Pb.preL QL hsat hbind hinj hadj]
  unfold aluFpReqsOf
  rw [AxisTeleJ9.sum_map_flatMap, Chips.ChipRAP.sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : invG δ (cv aV) invV (den δ valKey) ∈ aluQ δ := List.mem_append_right _ (by simp [logupQ])
  have hkey : (fun c : Fin 5 => ((valKey (F := Fp)).getD c QE.zero).ev δ
      (alEK δ b Pb.nodesL Pb.orbitL chals (fun _ => (0 : K)) (qAL δ b Pb tr chals (fun _ => (0 : K))) i)
      (alEF b Pb.nodesL Pb.orbitL chals (fun _ => (0 : K)) (qAL δ b Pb tr chals (fun _ => (0 : K))) i)) =
      keyVec δ 5 valKey (EK i) (EF i) := by
    funext c; fin_cases c <;> rfl
  have htr : (alEF b Pb.nodesL Pb.orbitL chals (fun _ => (0 : K)) (qAL δ b Pb tr chals (fun _ => (0 : K))) i).trace =
      (EF i).trace := rfl
  rw [htr]
  rcases aV_bool δ b Pb tr chals pubs hsat i with h0 | h1
  · have h0' : (EF i).trace aV = 0 := h0
    rw [if_pos h0']; simp [fv, h0']
  · have h1' : (EF i).trace aV = 1 := h1
    rw [if_neg (by rw [h1']; exact one_ne_zero)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, fv, h1', liftQ, map_one, one_mul]
    rw [hkey, inv_of δ b Pb tr chals pubs hsat i hm (by simp only [CoeffExpr.eval, cv]; rw [h1']; exact one_ne_zero),
      den_ev_compress' δ valKey (m := 5) rfl (EK i) (EF i) γ ρ (by
        refine ⟨?_, fun j hj => ?_⟩
        · rw [eK_chal, eK_chal]; exact hok.1
        · rw [eK_chal, eK_chal]; exact hok.2 j hj)]

end Tele

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSumAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AluSumAL
#print axioms aV_bool
#print axioms aluX_sumL
#print axioms aluS_sumL
#print axioms aluV_sumL
end Axioms
