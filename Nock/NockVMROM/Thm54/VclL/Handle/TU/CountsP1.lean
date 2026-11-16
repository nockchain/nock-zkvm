/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/CountsP1.lean

 **Multiplicities are exact consumer counts (trace uniqueness, P1 fragment).**

 * §1 the per-record balance (`fibre_counts`'s conclusion) with providers of pairwise distinct keys: each
 provider's weight is the exact number of consumers of its key; every consumed key has a unique provider.
 * §2 the cell table: `mv` (validity, `cVRec`), `mx`, `mx1` (export, `cXRec`), `mh` (handle export,
 `cellProvsW`).
 * §3 the walk: `mL`, `mR` (path records, `walkPProvs`), and the consumed handle-export key of a walk row is the
 unique cell row's `keyH` (so `vL`, `vR` are that row's handle values).
 The distinctness of the providers' keys is a HYPOTHESIS (`hdistinct`), proved separately from the cell order.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
import Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW
import Nock.NockVMROM.Thm54.VclL.Handle.ServeH
import Nock.NockVMROM.Thm54.VclL.Chips.MemFamilyVCL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW
open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)

/-! ## 1. Weights are counts -/

section Core
variable {L : Type*} [Field L] {α : Type*} [DecidableEq α]

/-- Distinct keys: the weight of a key is the weight of its provider. -/
theorem pw_of_nodup (provs : List (α × L)) (hnd : (provs.map Prod.fst).Nodup) {q : α × L} (hq : q ∈ provs) :
    pw provs q.1 = q.2 := by
  induction provs with
  | nil => simp at hq
  | cons a t ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have hz : ∀ r, r ∈ t.map Prod.fst → pw t r = 0 → True := fun _ _ _ => trivial
    unfold pw at ih ⊢
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with rfl | hqt
    · have : (t.map fun q' => if q'.1 = q.1 then q'.2 else 0).sum = 0 :=
        List.sum_eq_zero fun x hx => by
          obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hx
          have : q'.1 ≠ q.1 := fun h => hnd.1 (List.mem_map.mpr ⟨q', hq', h⟩)
          simp [this]
      simp [this]
    · have hne : a.1 ≠ q.1 := fun h => hnd.1 (h ▸ List.mem_map.mpr ⟨q, hqt, rfl⟩)
      simp [hne]
      exact ih hnd.2 hqt

/-- A key that is nobody's provider has weight `0`. -/
theorem pw_of_not_mem (provs : List (α × L)) (r : α) (h : r ∉ provs.map Prod.fst) : pw provs r = 0 := by
  unfold pw
  exact List.sum_eq_zero fun x hx => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    have : q.1 ≠ r := fun e => h (List.mem_map.mpr ⟨q, hq, e⟩)
    simp [this]

/-- **A provider's weight is the exact consumer count of its key** (per-record balance, distinct keys). -/
theorem weight_eq_count (reqs : List α) (provs : List (α × L))
    (hbal : ∀ r, (reqs.count r : L) = pw provs r) (hdistinct : (provs.map Prod.fst).Nodup)
    {q : α × L} (hq : q ∈ provs) : q.2 = (reqs.count q.1 : L) := by
  rw [hbal, pw_of_nodup provs hdistinct hq]

/-- **A consumed key has a provider** (the consumer count is a nonzero natural below the characteristic). -/
theorem consumed_provided {p : ℕ} [CharP L p] (reqs : List α) (provs : List (α × L))
    (hbal : ∀ r, (reqs.count r : L) = pw provs r) (hbud : reqs.length < p) {r : α} (hr : r ∈ reqs) :
    ∃ q ∈ provs, q.1 = r := by
  by_contra hno
  push Not at hno
  have h0 : pw provs r = 0 := pw_of_not_mem provs r fun hm => by
    obtain ⟨q, hq, e⟩ := List.mem_map.mp hm
    exact hno q hq e
  have hc : ((reqs.count r : ℕ) : L) = 0 := by rw [hbal, h0]
  have hdvd := (CharP.cast_eq_zero_iff L p _).mp hc
  have hpos : 0 < reqs.count r := List.count_pos_iff.mpr hr
  have hle : reqs.count r ≤ reqs.length := List.count_le_length
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

/-- **Unique providers: a consumed key has a UNIQUE provider** (distinct keys). -/
theorem consumed_unique_provider {p : ℕ} [CharP L p] (reqs : List α) (provs : List (α × L))
    (hbal : ∀ r, (reqs.count r : L) = pw provs r) (hdistinct : (provs.map Prod.fst).Nodup)
    (hbud : reqs.length < p) {r : α} (hr : r ∈ reqs) :
    ∃ q ∈ provs, q.1 = r ∧ ∀ q' ∈ provs, q'.1 = r → q' = q := by
  obtain ⟨q, hq, e⟩ := consumed_provided reqs provs hbal hbud hr
  exact ⟨q, hq, e, fun q' hq' e' => List.inj_on_of_nodup_map hdistinct hq' hq (e'.trans e.symm)⟩

end Core


/-! ## 2. The cell table -/

section Cell
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K) {h n : ℕ} (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) {w : ℕ} (Q : Fin w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- A natural number in `𝕂′` determines it in `F`. -/
theorem eq_natCast_of_alg {x : F} {m : ℕ} (h : algebraMap F 𝕂′ x = (m : 𝕂′)) : x = (m : F) := by
  apply (algebraMap F 𝕂′).injective
  rw [h, map_natCast]

/-- **`mv` is the exact number of consumers of the row's validity key.** -/
theorem mv_eq_count [DecidableEq 𝕂′] (reqs : List (Fin 5 → 𝕂′)) (provs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hbal : ∀ r, (reqs.count r : 𝕂′) = pw provs r) (hdistinct : (provs.map Prod.fst).Nodup)
    (hsub : ∀ q ∈ liftWts (cVRec δF b nodes orbit chals pubs Q), q ∈ provs) (i : Fin n) :
    (cellEnvF b nodes orbit chals pubs Q i).trace Cell.mv =
      (reqs.count (keyVec δF 5 Cell.vKeyP (cellEnvK δF b nodes orbit chals pubs Q i)
        (cellEnvF b nodes orbit chals pubs Q i)) : F) := by
  have hq := hsub (_, algebraMap F 𝕂′ ((cellEnvF b nodes orbit chals pubs Q i).trace Cell.mv))
    (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, rfl⟩)
  exact eq_natCast_of_alg δF (weight_eq_count reqs provs hbal hdistinct hq)

/-- **`mx` is the exact number of consumers of the row's side-`0` export key.** -/
theorem mx_eq_count [DecidableEq 𝕂′] (reqs : List (Fin 11 → 𝕂′)) (provs : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbal : ∀ r, (reqs.count r : 𝕂′) = pw provs r) (hdistinct : (provs.map Prod.fst).Nodup)
    (hsub : ∀ q ∈ liftWts (cXRec δF b nodes orbit chals pubs Q), q ∈ provs) (i : Fin n) :
    (cellEnvF b nodes orbit chals pubs Q i).trace Cell.mx =
      (reqs.count (keyVec δF 11 (Cell.xKeyS 0) (cellEnvK δF b nodes orbit chals pubs Q i)
        (cellEnvF b nodes orbit chals pubs Q i)) : F) := by
  have hm : (keyVec δF 11 (Cell.xKeyS 0) (cellEnvK δF b nodes orbit chals pubs Q i)
      (cellEnvF b nodes orbit chals pubs Q i), (cellEnvF b nodes orbit chals pubs Q i).trace Cell.mx) ∈
      cXRec δF b nodes orbit chals pubs Q := List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp⟩
  have hq := hsub _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
  exact eq_natCast_of_alg δF (weight_eq_count reqs provs hbal hdistinct hq)

/-- **`mx1` is the exact number of consumers of the row's side-`1` export key.** -/
theorem mx1_eq_count [DecidableEq 𝕂′] (reqs : List (Fin 11 → 𝕂′)) (provs : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbal : ∀ r, (reqs.count r : 𝕂′) = pw provs r) (hdistinct : (provs.map Prod.fst).Nodup)
    (hsub : ∀ q ∈ liftWts (cXRec δF b nodes orbit chals pubs Q), q ∈ provs) (i : Fin n) :
    (cellEnvF b nodes orbit chals pubs Q i).trace Cell.mx1 =
      (reqs.count (keyVec δF 11 (Cell.xKeyS 1) (cellEnvK δF b nodes orbit chals pubs Q i)
        (cellEnvF b nodes orbit chals pubs Q i)) : F) := by
  have hm : (keyVec δF 11 (Cell.xKeyS 1) (cellEnvK δF b nodes orbit chals pubs Q i)
      (cellEnvF b nodes orbit chals pubs Q i), (cellEnvF b nodes orbit chals pubs Q i).trace Cell.mx1) ∈
      cXRec δF b nodes orbit chals pubs Q := List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp⟩
  have hq := hsub _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
  exact eq_natCast_of_alg δF (weight_eq_count reqs provs hbal hdistinct hq)

end Cell


/-! ## 3. The handle export and the walk -/

section Handle
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [DecidableEq K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ}
  (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) {w : ℕ} (Q : Fin w → F[X])

theorem eq_natCast_of_algK {x : F} {m : ℕ} (h : algebraMap F K x = (m : K)) : x = (m : F) := by
  apply (algebraMap F K).injective
  rw [h, map_natCast]

/-- **`mh` is the exact number of consumers of the row's handle-export key.** -/
theorem mh_eq_count (reqs : List (Fin 5 → K)) (provs : List ((Fin 5 → K) × K))
    (hbal : ∀ r, (reqs.count r : K) = pw provs r) (hdistinct : (provs.map Prod.fst).Nodup)
    (hsub : ∀ q ∈ CellTwinKW.cellProvsW b nodes orbit chals pubs Q, q ∈ provs) (i : Fin n) :
    (hqkEF b nodes orbit chals pubs Q i).trace CellH.mh =
      (reqs.count (ServeH.keyVec5 (K := K) (keyHK (F := F)) (hqkEF b nodes orbit chals pubs Q i)) : F) := by
  have hq := hsub (ServeH.keyVec5 (K := K) (keyHK (F := F)) (hqkEF b nodes orbit chals pubs Q i),
    algebraMap F K ((hqkEF b nodes orbit chals pubs Q i).trace CellH.mh))
    (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  exact eq_natCast_of_algK (weight_eq_count reqs provs hbal hdistinct hq)

/-- **The walk's left path-record multiplicity `mL` is the exact number of consumers of the record.** -/
theorem mL_eq_count (reqs : List (Fin 5 → K)) (provs : List ((Fin 5 → K) × K))
    (hbal : ∀ r, (reqs.count r : K) = pw provs r) (hdistinct : (provs.map Prod.fst).Nodup)
    (hsub : ∀ q ∈ ServeH.walkPProvs b nodes orbit chals pubs Q, q ∈ provs) (j : Fin n) :
    (wEF b nodes orbit chals pubs Q j).trace WChip.mL =
      (reqs.count (ServeH.keyVec5 (K := K) WalkHC.recLH (wEF b nodes orbit chals pubs Q j)) : F) := by
  have hm : (ServeH.keyVec5 (K := K) WalkHC.recLH (wEF b nodes orbit chals pubs Q j),
      algebraMap F K ((wEF b nodes orbit chals pubs Q j).trace WChip.mL)) ∈
      ServeH.walkPProvs b nodes orbit chals pubs Q :=
    List.mem_flatMap.mpr ⟨j, List.mem_finRange j, by simp⟩
  exact eq_natCast_of_algK (weight_eq_count reqs provs hbal hdistinct (hsub _ hm))

/-- **`mR`, the right path-record multiplicity.** -/
theorem mR_eq_count (reqs : List (Fin 5 → K)) (provs : List ((Fin 5 → K) × K))
    (hbal : ∀ r, (reqs.count r : K) = pw provs r) (hdistinct : (provs.map Prod.fst).Nodup)
    (hsub : ∀ q ∈ ServeH.walkPProvs b nodes orbit chals pubs Q, q ∈ provs) (j : Fin n) :
    (wEF b nodes orbit chals pubs Q j).trace WChip.mR =
      (reqs.count (ServeH.keyVec5 (K := K) WalkHC.recRH (wEF b nodes orbit chals pubs Q j)) : F) := by
  have hm : (ServeH.keyVec5 (K := K) WalkHC.recRH (wEF b nodes orbit chals pubs Q j),
      algebraMap F K ((wEF b nodes orbit chals pubs Q j).trace WChip.mR)) ∈
      ServeH.walkPProvs b nodes orbit chals pubs Q :=
    List.mem_flatMap.mpr ⟨j, List.mem_finRange j, by simp⟩
  exact eq_natCast_of_algK (weight_eq_count reqs provs hbal hdistinct (hsub _ hm))

/-- **A consumed handle-export key `(idx, kL, vL, kR, vR)` of a walk row is the handle-export key of
EXACTLY ONE cell row** (the providers are the cell rows, distinct keys). -/
theorem walk_key_is_cell_key {p : ℕ} [CharP K p] (reqs : List (Fin 5 → K))
    (hbal : ∀ r, (reqs.count r : K) = pw (CellTwinKW.cellProvsW b nodes orbit chals pubs Q) r)
    (hdistinct : ((CellTwinKW.cellProvsW b nodes orbit chals pubs Q).map Prod.fst).Nodup)
    (hbud : reqs.length < p) {r : Fin 5 → K} (hr : r ∈ reqs) :
    ∃ i : Fin n, ServeH.keyVec5 (K := K) (keyHK (F := F)) (hqkEF b nodes orbit chals pubs Q i) = r ∧
      ∀ i' : Fin n, ServeH.keyVec5 (K := K) (keyHK (F := F)) (hqkEF b nodes orbit chals pubs Q i') = r → i' = i := by
  obtain ⟨q, hq, e, hu⟩ := consumed_unique_provider reqs _ hbal hdistinct hbud hr
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
  refine ⟨i, e, fun i' hi' => ?_⟩
  have hnd : ((List.finRange n).map fun i => ServeH.keyVec5 (K := K) (keyHK (F := F))
      (hqkEF b nodes orbit chals pubs Q i)).Nodup := by
    simpa [CellTwinKW.cellProvsW, List.map_map, Function.comp_def] using hdistinct
  exact List.inj_on_of_nodup_map hnd (List.mem_finRange i') (List.mem_finRange i) (hi'.trans e.symm)

/-- **Walk path values**: for the walk row `j` whose consumed key is in `reqs`, the key's `vL`, `vR` entries are the unique
cell row's handle-export values. -/
theorem walk_vL_vR {p : ℕ} [CharP K p] (reqs : List (Fin 5 → K))
    (hbal : ∀ r, (reqs.count r : K) = pw (CellTwinKW.cellProvsW b nodes orbit chals pubs Q) r)
    (hdistinct : ((CellTwinKW.cellProvsW b nodes orbit chals pubs Q).map Prod.fst).Nodup)
    (hbud : reqs.length < p) {w' : ℕ} (Q' : Fin w' → F[X]) (j : Fin n)
    (hr : ServeH.keyVec5 (K := K) WalkHC.xKeyH (wEF b nodes orbit chals pubs Q' j) ∈ reqs) :
    ∃ i : Fin n,
      algebraMap F K ((wEF b nodes orbit chals pubs Q' j).trace WalkHC.vL) =
        ServeH.keyVec5 (K := K) (keyHK (F := F)) (hqkEF b nodes orbit chals pubs Q i) 2 ∧
      algebraMap F K ((wEF b nodes orbit chals pubs Q' j).trace WalkHC.vR) =
        ServeH.keyVec5 (K := K) (keyHK (F := F)) (hqkEF b nodes orbit chals pubs Q i) 4 := by
  obtain ⟨i, e, -⟩ := walk_key_is_cell_key b nodes orbit chals pubs Q reqs hbal hdistinct hbud hr
  refine ⟨i, ?_, ?_⟩
  · have := congrFun e 2
    rw [this]
    simp [ServeH.keyVec5, WalkHC.xKeyH, cv, CoeffExpr.eval]
  · have := congrFun e 4
    rw [this]
    simp [ServeH.keyVec5, WalkHC.xKeyH, cv, CoeffExpr.eval]

end Handle

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1.weight_eq_count
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1.consumed_unique_provider
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1.mv_eq_count
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1.mx_eq_count
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1.mx1_eq_count
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1.mh_eq_count
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1.mL_eq_count
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1.mR_eq_count
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1.walk_key_is_cell_key
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1.walk_vL_vR
