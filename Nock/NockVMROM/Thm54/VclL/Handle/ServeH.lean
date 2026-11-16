/-
  Nock/NockVMROM/Thm54/VclL/Handle/ServeH.lean

  * `rlcH_eval`, `denKey_eval`: a twin denominator `ρH + Σ_k γH^k · lift(key_k)` is
    `FiniteIO.compress ⟨γH, ρH⟩ (keyVec5 key)` (keys of length 5, entries lifted from `𝔽`).
  * `served_of_balance`: outside `IOFailureEventW reqs provs` at `(γ, ρ)`, with nonzero
    denominators, the weighted balance and `|reqs| < p`, every consumed record is provided
    (`finiteIO_lookup_sound_weighted`).  The pole event (any denominator vanishing) is part of
    `IOFailureEventW` (`IOPoleHitEvent`), so it is PRICED, not assumed: the inverse gates already
    force every row's denominator nonzero on an accepted trace (`cellH_inv`, `walkH_inv`).
  * `cellProvs` (the cell twin's `(keyH, mh)` records) and `cell_provs_sum`: their weighted sum is
    `pubs 4` (`cellH_export_telescope` + `cellH_inv` + `denKey_eval`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleH

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ServeH

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SVFrame
open scoped Polynomial

noncomputable section

section Den
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- A length-5 key read off a base environment, lifted to `𝕂`. -/
def keyVec5 (l : List (CoeffExpr F)) (eF : Env F) : Fin 5 → K :=
  fun c => algebraMap F K ((l.getD c (.const 0)).eval eF)

theorem rlcH_eval (eK : Env K) (eF : Env F) :
    ∀ (l : List (CoeffExpr F)) (m : ℕ), (CellH.rlcH m l).eval eK eF =
      ∑ c ∈ Finset.range l.length, eK.chal CellH.hGam ^ (m + c) *
        algebraMap F K ((l.getD c (.const 0)).eval eF)
  | [], m => by simp [CellH.rlcH, MixedExpr.eval]
  | g :: r, m => by
    rw [CellH.rlcH, MixedExpr.eval, rlcH_eval eK eF r (m + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [MixedExpr.eval, List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show m + 1 + c = m + (c + 1) by omega]

theorem denKey_eval (eK : Env K) (eF : Env F) (l : List (CoeffExpr F)) (hl : l.length = 5) :
    (CellH.denKey l).eval eK eF =
      compress ⟨eK.chal CellH.hGam, eK.chal CellH.hRho⟩ (keyVec5 l eF) := by
  simp only [CellH.denKey, MixedExpr.eval, rlcH_eval, hl, compress, Walk.rlc, keyVec5, zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun c => eK.chal CellH.hGam ^ c *
    algebraMap F K ((l.getD c (.const 0)).eval eF)) 5]

end Den

section Serve
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}

/-- **LogUp at the handle coins**: outside the weighted IO failure event, every consumed record is
provided.  The denominators' non-vanishing is supplied by the chips' inverse gates. -/
theorem served_of_balance {p : ℕ} [CharP K p] (reqs : List (Fin m → K)) (provs : List ((Fin m → K) × K))
    (γ ρ : K) (hdA : ∀ r ∈ reqs, compress ⟨γ, ρ⟩ r ≠ 0) (hdB : ∀ q ∈ provs, compress ⟨γ, ρ⟩ q.1 ≠ 0)
    (hsum : (reqs.map fun r => (compress ⟨γ, ρ⟩ r)⁻¹).sum =
      (provs.map fun q => q.2 * (compress ⟨γ, ρ⟩ q.1)⁻¹).sum)
    (hcount : reqs.length < p) (hout : (γ, ρ) ∉ IOFailureEventW reqs provs) :
    ∀ r ∈ reqs, r ∈ provs.map Prod.fst := by
  rw [mem_IOFailureEventW_iff] at hout
  push Not at hout
  exact finiteIO_lookup_sound_weighted reqs provs ⟨γ, ρ⟩ hdA hdB hsum hcount hout.1 hout.2.2

end Serve

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (cellChipH δF b hn nodes orbit chals pubs).rap.w → F[X])

/-- **The cell twin's handle-export providers**: `(keyH, mh)` per row. -/
def cellProvs {w : ℕ} (Q' : Fin w → F[X]) : List ((Fin 5 → K) × K) :=
  (List.finRange n).map fun i =>
    (keyVec5 CellH.keyH (cEF b nodes orbit chals pubs Q' i),
      algebraMap F K ((cEF b nodes orbit chals pubs Q' i).trace CellH.mh))

theorem cell_den_eq (i : Fin n) :
    cDenH δF b nodes orbit chals pubs Q i =
      compress ⟨chals CellH.hGam, chals CellH.hRho⟩ (keyVec5 CellH.keyH (cEF b nodes orbit chals pubs Q i)) := by
  show (CellH.denKey CellH.keyH : MixedExpr F).eval (cEK δF b nodes orbit chals pubs Q i)
    (cEF b nodes orbit chals pubs Q i) = _
  rw [denKey_eval _ _ _ rfl, cEK_chal, cEK_chal]

/-- Every cell provider's denominator is nonzero (the inverse gate). -/
theorem cell_provs_den (hsat : (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ q ∈ cellProvs b nodes orbit chals pubs Q, compress ⟨chals CellH.hGam, chals CellH.hRho⟩ q.1 ≠ 0 := by
  intro q hq
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
  rw [← cell_den_eq]
  exact (cellH_inv δF b hn nodes orbit chals pubs Q hsat i).1

/-- **The providers' weighted sum is the terminal `pubs 4`.** -/
theorem cell_provs_sum (hsat : (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChipH δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((cellProvs b nodes orbit chals pubs Q).map fun q =>
        q.2 * (compress ⟨chals CellH.hGam, chals CellH.hRho⟩ q.1)⁻¹).sum = pubs CellH.pubH := by
  rw [← cellH_export_telescope δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  simp only [cellProvs, List.map_map, Function.comp_def]
  rw [sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  show _ = algebraMap F K ((cEF b nodes orbit chals pubs Q i).trace CellH.mh) *
    (cEK δF b nodes orbit chals pubs Q i).trace CellH.invH
  rw [(cellH_inv δF b hn nodes orbit chals pubs Q hsat i).2, cell_den_eq]

end Cell

section Walk
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ)
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (walkChipH δF kroots b hn nodes orbit chals pubs).rap.w → F[X])

/-- **The walk twin's consumed handle-export keys** `(idx, kL, vL, kR, vR)`, one per row. -/
def walkXReqs {w : ℕ} (Q' : Fin w → F[X]) : List (Fin 5 → K) :=
  (List.finRange n).map fun j => keyVec5 WalkHC.xKeyH (wEF b nodes orbit chals pubs Q' j)

/-- **The walk twin's provided handle walk records** `(rootIdx, 2·pre + b, k_b, v_b)` with weights
`mL / mR` (the record list padded to length 5 by a zero entry). -/
def walkPProvs {w : ℕ} (Q' : Fin w → F[X]) : List ((Fin 5 → K) × K) :=
  (List.finRange n).flatMap fun j =>
    [(keyVec5 WalkHC.recLH (wEF b nodes orbit chals pubs Q' j),
        algebraMap F K ((wEF b nodes orbit chals pubs Q' j).trace WChip.mL)),
     (keyVec5 WalkHC.recRH (wEF b nodes orbit chals pubs Q' j),
        algebraMap F K ((wEF b nodes orbit chals pubs Q' j).trace WChip.mR))]

/-- A walk denominator of a length-4 record is `compress` of the record padded by `0`. -/
theorem walk_den_eq (l : List (CoeffExpr F)) (hl : l.length = 4) (j : Fin n) :
    wDen δF kroots b nodes orbit chals pubs Q l j =
      compress ⟨chals CellH.hGam, chals CellH.hRho⟩ (keyVec5 l (wEF b nodes orbit chals pubs Q j)) := by
  show (CellH.denKey l : MixedExpr F).eval (wEK δF kroots b nodes orbit chals pubs Q j)
    (wEF b nodes orbit chals pubs Q j) = _
  simp only [CellH.denKey, MixedExpr.eval, rlcH_eval, hl, compress, Walk.rlc, keyVec5, zero_add,
    wEK_chal]
  rw [Fin.sum_univ_eq_sum_range (fun c => chals CellH.hGam ^ c *
    algebraMap F K ((l.getD c (.const 0)).eval (wEF b nodes orbit chals pubs Q j))) 5]
  conv_rhs => rw [show (5 : ℕ) = 4 + 1 from rfl, Finset.sum_range_succ]
  have h4 : (l.getD 4 (.const 0)).eval (wEF b nodes orbit chals pubs Q j) = 0 := by
    rw [List.getD_eq_default _ _ (by omega)]; simp [CoeffExpr.eval]
  rw [h4, map_zero, mul_zero, add_zero]

theorem walk_xden_eq (j : Fin n) :
    wDen δF kroots b nodes orbit chals pubs Q WalkHC.xKeyH j =
      compress ⟨chals CellH.hGam, chals CellH.hRho⟩ (keyVec5 WalkHC.xKeyH (wEF b nodes orbit chals pubs Q j)) := by
  show (CellH.denKey WalkHC.xKeyH : MixedExpr F).eval (wEK δF kroots b nodes orbit chals pubs Q j)
    (wEF b nodes orbit chals pubs Q j) = _
  rw [denKey_eval _ _ _ rfl, wEK_chal, wEK_chal]

theorem walk_reqs_den (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ r ∈ walkXReqs b nodes orbit chals pubs Q, compress ⟨chals CellH.hGam, chals CellH.hRho⟩ r ≠ 0 := by
  intro r hr
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hr
  rw [← walk_xden_eq]
  exact (walkH_inv δF kroots b hn nodes orbit chals pubs Q hsat j).1.1

/-- **The walk's consumed keys sum to its terminal `pubs 4`.** -/
theorem walk_reqs_sum (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipH δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((walkXReqs b nodes orbit chals pubs Q).map fun r =>
        (compress ⟨chals CellH.hGam, chals CellH.hRho⟩ r)⁻¹).sum = pubs WalkHC.pubX := by
  rw [← walkH_export_telescope δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  simp only [walkXReqs, List.map_map, Function.comp_def]
  rw [sum_finRange]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(walkH_inv δF kroots b hn nodes orbit chals pubs Q hsat j).1.2, walk_xden_eq]

theorem walk_provs_den (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ q ∈ walkPProvs b nodes orbit chals pubs Q, compress ⟨chals CellH.hGam, chals CellH.hRho⟩ q.1 ≠ 0 := by
  intro q hq
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hq
  have hi := walkH_inv δF kroots b hn nodes orbit chals pubs Q hsat j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · rw [← walk_den_eq δF kroots b hn nodes orbit chals pubs Q _ rfl]; exact hi.2.1.1
  · rw [← walk_den_eq δF kroots b hn nodes orbit chals pubs Q _ rfl]; exact hi.2.2.1

/-- **The walk's provided handle walk records sum (weighted) to its terminal `pubs 5`.** -/
theorem walk_provs_sum (hsat : (walkChipH δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipH δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((walkPProvs b nodes orbit chals pubs Q).map fun q =>
        q.2 * (compress ⟨chals CellH.hGam, chals CellH.hRho⟩ q.1)⁻¹).sum = pubs WalkHC.pubP := by
  rw [← walkH_path_telescope δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj]
  simp only [walkPProvs, map_flatMap_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Function.comp_def]
  rw [sum_finRange]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi := walkH_inv δF kroots b hn nodes orbit chals pubs Q hsat j
  show _ = algebraMap F K _ * wK δF kroots b nodes orbit chals pubs Q WalkHC.hpInvL j +
    algebraMap F K _ * wK δF kroots b nodes orbit chals pubs Q WalkHC.hpInvR j
  rw [hi.2.1.2, hi.2.2.2, walk_den_eq δF kroots b hn nodes orbit chals pubs Q _ rfl,
    walk_den_eq δF kroots b hn nodes orbit chals pubs Q _ rfl]

end Walk

section Joint
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- **The three-party handle-export balance**: compute consumers `creqs` (terminal `sC`) and walk
consumers `wreqs` (terminal `sW`) against providers `provs` (terminal `sC + sW`, the cell twin's
`pubs 4 = Re ρ₃ + yH`).  Outside `IOFailureEventW` at `(γH, ρH)` every consumed key is provided. -/
theorem keys_served {p : ℕ} [CharP K p] {m : ℕ} (creqs wreqs : List (Fin m → K))
    (provs : List ((Fin m → K) × K)) (γ ρ sC sW : K)
    (hdC : ∀ r ∈ creqs, compress ⟨γ, ρ⟩ r ≠ 0) (hdW : ∀ r ∈ wreqs, compress ⟨γ, ρ⟩ r ≠ 0)
    (hdB : ∀ q ∈ provs, compress ⟨γ, ρ⟩ q.1 ≠ 0)
    (hC : (creqs.map fun r => (compress ⟨γ, ρ⟩ r)⁻¹).sum = sC)
    (hW : (wreqs.map fun r => (compress ⟨γ, ρ⟩ r)⁻¹).sum = sW)
    (hP : (provs.map fun q => q.2 * (compress ⟨γ, ρ⟩ q.1)⁻¹).sum = sC + sW)
    (hcount : (creqs ++ wreqs).length < p) (hout : (γ, ρ) ∉ IOFailureEventW (creqs ++ wreqs) provs) :
    ∀ r ∈ creqs ++ wreqs, r ∈ provs.map Prod.fst := by
  refine served_of_balance _ provs γ ρ ?_ hdB ?_ hcount hout
  · intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact hdC r h
    · exact hdW r h
  · rw [List.map_append, List.sum_append, hC, hW, hP]

end Joint

end

end Nock.NockVMROM.Thm54.VclL.Handle.ServeH
