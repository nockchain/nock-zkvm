/-
  Nock/NockVMROM/Thm54/VclL/Handle/TeleCQ.lean

  Additive.

  * `slots_castSpec`: the `F`-slots of `slotPairs` are the `ℚ` slot specs with their activities cast;
  * `denQH_val'`: a `𝕂′` record denominator is `compress` at the compute's `𝕂′` coins
    `(γH′, ρH′) = (limb 0 + limb 12·√δ, limb 3 + limb 15·√δ)` of the LIFTED `𝕂` key (`liftRec ∘ entKey`);
  * `slot_atQ` / `termXQ_row` / `termPQ_row`: the slot lemma at `𝕂′` (`slot_core` at `K := 𝕂′`);
  * `compute_telescopeQ`: the limb accumulators telescope on the twin (Re and Im separately);
  * **`compXQ_sum` / `compPQ_sum`**: `Σ_{compXReqs} compress′(lift r)⁻¹ = (Re, Im) limbs 15 / 21` and
    `Σ_{compPReqs} … = limbs 18 / 24` — the compute side of the `𝕂′` balance.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComputeSatHQ
import Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.TeleC
open Nock.NockVMROM.Thm54.VclL.Handle.ComputeSatHQ Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

noncomputable section

/-! ## 1. The slot specs at `ℚ` and at `F` -/

section Cast
variable {F : Type} [Field F]

def castEnt (x : Ent ℚ) : Ent F := ⟨x.states, mapC (fun q : ℚ => (q : F)) x.extra, x.rcd, x.path⟩
def castSpec (S : SlotSpec ℚ) : SlotSpec F := ⟨S.inv, S.ents.map castEnt, S.pair, S.pairStates⟩

theorem slots_castSpec : (slots (F := ℚ)).map castSpec = (slots (F := F)) := by
  simp [slots, slot0, slot1, slot2, castSpec, castEnt, mapC, notC, cc]

theorem castEnt_act (x : Ent ℚ) (eF : Env F) : (castEnt x).act.eval eF = evalQ x.act eF := by
  simp only [castEnt, Ent.act, CoeffExpr.eval, evalQ, eval_mapC_cast, selS, CoeffExpr.eval_sumList,
    evalQ_sumList, cc, evalQ_cc]

theorem castEnt_sumAct (l : List (Ent ℚ)) (eF : Env F) :
    (CoeffExpr.sumList (l.map castEnt) Ent.act).eval eF = (l.map fun x => evalQ x.act eF).sum := by
  rw [CoeffExpr.eval_sumList, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => castEnt_act x eF

end Cast

/-! ## 2. Values at the `𝕂′` coins -/

section Val
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (eK : Env K) (eF : Env F)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- The compute twin's `𝕂′` handle coins (`γH′`: Re limb `0`, Im limb `12`; `ρH′`: `3`, `15`). -/
def coinsCQ : IOCoins 𝕂′ :=
  ⟨Quad.mk _ (eK.chal chalGammaL) (eK.chal chalGammaIm), Quad.mk _ (eK.chal chalRhoL) (eK.chal chalRhoIm)⟩

theorem rlcKeyQ_val' : ∀ (r : List ℕ) (m : ℕ), Q.val δ (rlcKeyQ F δ m r) eK eF =
    ∑ c ∈ Finset.range r.length, (coinsCQ δ eK).gamma ^ (m + c) *
      algebraMap K 𝕂′ (algebraMap F K (eF.trace (r.getD c 0)))
  | [], m => by simp [rlcKeyQ, qconst_val]
  | i :: r, m => by
    rw [rlcKeyQ, qadd_val, qmul_val, qpow_val, rlcKeyQ_val' r (m + 1), qlift_val', List.length_cons,
      Finset.sum_range_succ']
    have hg : Q.val δ (qγH F) eK eF = (coinsCQ δ eK).gamma := by
      rw [qγH, qvar_val]; rfl
    rw [hg]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero, cc, CoeffExpr.eval]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show m + 1 + c = m + (c + 1) by omega]

/-- **A `𝕂′` compute denominator is `compress` of the lifted key at the `𝕂′` coins.** -/
theorem denQH_val' (r : List ℕ) (hr : r.length ≤ 5) :
    Q.val δ (denQH F δ r) eK eF = compress (coinsCQ δ eK) (liftRec (L := 𝕂′) (entKey (K := K) r eF)) := by
  rw [denQH, qadd_val, rlcKeyQ_val' δ eK eF r 0]
  have hr' : Q.val δ (qρH F) eK eF = (coinsCQ δ eK).pole := by
    rw [qρH, qvar_val]; rfl
  rw [hr']
  simp only [compress, Walk.rlc, zero_add]
  congr 1
  have hR : (∑ c : Fin 5, (coinsCQ δ eK).gamma ^ (c : ℕ) * liftRec (L := 𝕂′) (entKey (K := K) r eF) c) =
      ∑ c ∈ Finset.range 5, (coinsCQ δ eK).gamma ^ c * algebraMap K 𝕂′ (entKeyN (K := K) r eF c) := by
    rw [← Fin.sum_univ_eq_sum_range (fun c => (coinsCQ δ eK).gamma ^ c * algebraMap K 𝕂′ (entKeyN (K := K) r eF c)) 5]
    rfl
  rw [hR, ← Finset.sum_subset (Finset.range_subset_range.mpr hr)]
  · refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    simp [entKeyN, hc]
  · intro c _ hc
    rw [Finset.mem_range] at hc
    simp [entKeyN, hc]

/-- The `𝕂′` inverse of a slot (Re at `S.inv`, Im at `imOf S.inv`). -/
def invQ (S : SlotSpec ℚ) : 𝕂′ := Quad.mk _ (eK.trace S.inv) (eK.trace (imOf S.inv))

def pairDaQ (S : SlotSpec ℚ) : 𝕂′ :=
  match S.pair with
  | some (_, a, _) => Q.val δ (denQH F δ a) eK eF
  | none => 0

def pairDbQ (S : SlotSpec ℚ) : 𝕂′ :=
  match S.pair with
  | some (_, _, c) => Q.val δ (denQH F δ c) eK eF
  | none => 0

theorem aMF (x : F) : algebraMap F 𝕂′ x = algebraMap K 𝕂′ (algebraMap F K x) :=
  IsScalarTower.algebraMap_apply F K _ x

/-- **The `𝕂′` slot pair's value.** -/
theorem slotGateQ_val_spec (S : SlotSpec ℚ) :
    Q.val δ (slotGateQ F δ (castSpec S)) eK eF =
      invQ δ eK S * ((S.ents.map fun x => algebraMap F 𝕂′ (evalQ x.act eF) * Q.val δ (denQH F δ x.rcd) eK eF).sum +
          algebraMap F 𝕂′ (pairF S eF) * (pairDaQ δ eK eF S * pairDbQ δ eK eF S)) -
        (algebraMap F 𝕂′ ((S.ents.map fun x => evalQ x.act eF).sum) +
          algebraMap F 𝕂′ (pairF S eF) * (pairDaQ δ eK eF S + pairDbQ δ eK eF S)) := by
  have hents : Q.val δ (sumQ F ((castSpec (F := F) S).ents.map fun x => qmul F δ (qlift F x.act) (denQH F δ x.rcd))) eK eF =
      (S.ents.map fun x => algebraMap F 𝕂′ (evalQ x.act eF) * Q.val δ (denQH F δ x.rcd) eK eF).sum := by
    rw [sumQ_val]
    simp only [castSpec, List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp, qmul_val, qlift_val, castEnt_act]
    rfl
  have hinv : Q.val δ (qvar F .traceCur (castSpec (F := F) S).inv (some (imOf (castSpec (F := F) S).inv))) eK eF = invQ δ eK S := by
    rw [qvar_val]; rfl
  have hlift : Q.val δ (qlift F (CoeffExpr.sumList (castSpec (F := F) S).ents Ent.act)) eK eF =
      algebraMap F 𝕂′ ((S.ents.map fun x => evalQ x.act eF).sum) := by
    rw [qlift_val]; simp only [castSpec]; rw [castEnt_sumAct]
  unfold slotGateQ
  rw [qsub_val, qmul_val, qadd_val, qadd_val, hinv, hents, hlift]
  simp only [castSpec]
  unfold pairF pairDaQ pairDbQ
  cases hp : S.pair with
  | none => simp [qconst_val]
  | some q =>
    obtain ⟨fl, a, c⟩ := q
    simp only [qmul_val, qadd_val, qlift_val, cc, CoeffExpr.eval]

end Val

/-! ## 3. The slot lemma at `𝕂′` -/

section Slot
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] {eF : Env F} {j0 : ℕ}

local notation "𝕂′" => Quad (algebraMap F K δ)

variable (b : Basis (Fin 3) F K)

abbrev gK (eF : Env F) : Env K := Compute.TowerD.gatherEnv b eF

/-- **The slot lemma at `𝕂′`.** -/
theorem slot_atQ (hs : RowSel eF j0) (S : SlotSpec ℚ) (hS : S ∈ slots)
    (hg : Q.val δ (slotGateQ F δ (castSpec S)) (gK b eF) eF = 0)
    (hden : ∀ r ∈ rowPReqs (K := K) eF, compress (coinsCQ δ (gK b eF)) (liftRec (L := 𝕂′) r) ≠ 0)
    (P : Ent ℚ → Bool) :
    algebraMap F 𝕂′ (((S.ents.filter P).map fun x => evalQ x.act eF).sum) * invQ δ (gK b eF) S =
      ((((S.ents.filter P).filter fun x => evalQ x.act eF = 1)).map fun x =>
        (compress (coinsCQ δ (gK b eF)) (liftRec (L := 𝕂′) (entKey (K := K) x.rcd eF)))⁻¹).sum ∧
    algebraMap F 𝕂′ (pairF S eF) * invQ δ (gK b eF) S =
      ((pairReqs (K := K) S eF).map fun r => (compress (coinsCQ δ (gK b eF)) (liftRec (L := 𝕂′) r))⁻¹).sum := by
  set eK := gK b eF
  have hcore := slot_core S.ents (fun x => evalQ x.act eF) (fun x => Q.val δ (denQH F δ x.rcd) eK eF) P
    (invQ δ eK S) (pairF S eF) (pairDaQ δ eK eF S) (pairDbQ δ eK eF S)
    (fun x hx => act_bool hs S hS x hx) (act_pairwise hs S hS) (pairF_bool hs S hS)
    (fun x hx => pairF_act hs S hS x hx) (by rw [← slotGateQ_val_spec]; exact hg) ?_
  · refine ⟨?_, ?_⟩
    · rw [hcore.1]
      congr 1
      refine List.map_congr_left fun x hx => ?_
      have hxS : x ∈ S.ents := (List.mem_filter.mp (List.mem_filter.mp hx).1).1
      rw [denQH_val' δ eK eF _ (slots_states S hS x hxS).2.2]
    · rw [hcore.2]
      unfold pairReqs pairF pairDaQ pairDbQ
      cases hp : S.pair with
      | none => simp
      | some q =>
        obtain ⟨fl, a, c⟩ := q
        obtain ⟨-, ha, hc, -⟩ := slots_pair S hS fl a c hp
        simp only
        split_ifs with h1
        · simp [denQH_val' δ eK eF _ ha, denQH_val' δ eK eF _ hc]
        · simp
  · intro h1
    unfold pairDaQ pairDbQ
    unfold pairF at h1
    cases hp : S.pair with
    | none => rw [hp] at h1; exact absurd h1 zero_ne_one
    | some q =>
      obtain ⟨fl, a, c⟩ := q
      rw [hp] at h1
      obtain ⟨-, ha, hc, -⟩ := slots_pair S hS fl a c hp
      simp only at h1 ⊢
      have hin : ∀ r ∈ pairReqs (K := K) S eF, compress (coinsCQ δ eK) (liftRec (L := 𝕂′) r) ≠ 0 := fun r hr =>
        hden r (pairReqs_sub S hS r hr)
      unfold pairReqs at hin
      rw [hp] at hin
      simp only [h1, if_true, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hin
      rw [denQH_val' δ eK eF _ ha, denQH_val' δ eK eF _ hc]
      exact hin

/-- The `𝕂′` export term of a row: `Σ_S actX · inv′`. -/
def termXQ (eF : Env F) : 𝕂′ :=
  ((slots : List (SlotSpec ℚ)).map fun S => algebraMap F 𝕂′ (evalQ S.actX eF) * invQ δ (gK b eF) S).sum

def termPQ (eF : Env F) : 𝕂′ :=
  ((slots : List (SlotSpec ℚ)).map fun S => algebraMap F 𝕂′ (evalQ S.actP eF) * invQ δ (gK b eF) S).sum

theorem termXQ_row (hs : RowSel eF j0)
    (hg : ∀ S ∈ (slots : List (SlotSpec ℚ)), Q.val δ (slotGateQ F δ (castSpec S)) (gK b eF) eF = 0)
    (hden : ∀ r ∈ rowPReqs (K := K) eF, compress (coinsCQ δ (gK b eF)) (liftRec (L := 𝕂′) r) ≠ 0) :
    termXQ δ b eF = ((rowXReqs (K := K) eF).map fun r => (compress (coinsCQ δ (gK b eF)) (liftRec (L := 𝕂′) r))⁻¹).sum := by
  rw [termXQ, rowXReqs, map_flatMap_sum]
  congr 1
  refine List.map_congr_left fun S hS => ?_
  rw [evalQ_actX, (slot_atQ δ b hs S hS (hg S hS) hden (fun x => !x.path)).1, List.map_map]
  rfl

theorem termPQ_row (hs : RowSel eF j0)
    (hg : ∀ S ∈ (slots : List (SlotSpec ℚ)), Q.val δ (slotGateQ F δ (castSpec S)) (gK b eF) eF = 0)
    (hden : ∀ r ∈ rowPReqs (K := K) eF, compress (coinsCQ δ (gK b eF)) (liftRec (L := 𝕂′) r) ≠ 0) :
    termPQ δ b eF = ((rowPReqs (K := K) eF).map fun r => (compress (coinsCQ δ (gK b eF)) (liftRec (L := 𝕂′) r))⁻¹).sum := by
  rw [termPQ, rowPReqs, map_flatMap_sum]
  congr 1
  refine List.map_congr_left fun S hS => ?_
  have h := slot_atQ δ b hs S hS (hg S hS) hden (fun x => x.path)
  rw [evalQ_actP, map_add, add_mul, h.1, h.2, List.map_append, List.sum_append, List.map_map]
  rfl

end Slot

/-! ## 4. The compute twin's telescopes -/

section Chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))] (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
  (P : Fin (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δ)

theorem baseH_sub (t : CoeffExpr ℚ) (ht : t ∈ baseGatesH (F := ℚ)) : t ∈ baseGatesHQ (F := ℚ) := by
  simp only [baseGatesH, baseGatesHQ, accGatesHQ, List.mem_append] at ht ⊢
  rcases ht with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr h

theorem base_of_satQ (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHQ hn nodes b δ chalV pubVal orbit) P)
    (i : Fin n) (t : CoeffExpr ℚ) (ht : t ∈ baseGatesHQ (F := ℚ)) :
    evalQ t (rEF nodes chalV pubVal orbit P i) = 0 := by
  have h0 := ((computeChipVCLHQ_sat_iff hn nodes b δ chalV pubVal orbit P).mp hsat).2 _ (mem_rowNodeSet nodes i)
    (mapC (fun q : ℚ => (q : F)) t) (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ht)))
  rwa [eval_mapC_cast] at h0

theorem pair_of_satQ (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHQ hn nodes b δ chalV pubVal orbit) P)
    (i : Fin n) (S : SlotSpec ℚ) (hS : S ∈ (slots : List (SlotSpec ℚ))) :
    Q.val δ (slotGateQ F δ (castSpec S)) (gK b (rEF nodes chalV pubVal orbit P i)) (rEF nodes chalV pubVal orbit P i) = 0 := by
  have hall := ((computeChipVCLHQ_sat_iff hn nodes b δ chalV pubVal orbit P).mp hsat).2 _ (mem_rowNodeSet nodes i)
  have hS' : castSpec S ∈ (slots : List (SlotSpec F)) := by
    rw [← slots_castSpec]; exact List.mem_map_of_mem hS
  have hz : Q.IsZero (slotGateQ F δ (castSpec S)) (gK b (rEF nodes chalV pubVal orbit P i))
      (rEF nodes chalV pubVal orbit P i) :=
    (Compute.TowerD.qGates_iff b (Compute.TowerD.isCoordEnv_gather b _) _).mp fun g hg =>
      hall g (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨_, List.mem_map_of_mem hS', hg⟩)))
  exact (Q.isZero_iff δ _ _ _).mp hz

theorem masksCQ (hbind : (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).BindsPreprocessing P)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (rEF nodes chalV pubVal orbit P i).trace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (rEF nodes chalV pubVal orbit P i).trace 12 = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).rap.w = 85 := rfl
  have h0 : P ⟨11, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : P ⟨12, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  rw [envOfTrace_trace P _ _ _ _ (show 11 < _ by rw [hw]; omega),
    envOfTrace_trace P _ _ _ _ (show 12 < _ by rw [hw]; omega), h0, h1,
    firstRowMask_eval nodes hinj i, lastRowMask_eval hn nodes hinj i]
  refine ⟨rfl, ?_⟩
  by_cases hi : (i : ℕ) = n - 1
  · rw [if_pos (Fin.ext hi), if_pos hi]
  · rw [if_neg (fun h => hi (congrArg Fin.val h)), if_neg hi]

/-- **The generic limb telescope on the `𝕂′` compute twin.** -/
theorem compute_telescopeQ (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHQ hn nodes b δ chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (sl : List (Compute.LogUp.Slot ℚ)) (accBase pubBase : ℕ)
    (hsub : ∀ t ∈ Compute.LogUp.accGates 3 sl accBase pubBase, t ∈ baseGatesHQ (F := ℚ)) :
    ∑ i : Fin n, Compute.LogUp.termVal b (sl.map castSlot) (rEF nodes chalV pubVal orbit P i) =
      Compute.LogUp.limbVal b pubVal pubBase := by
  have hbind := ((computeChipVCLHQ_sat_iff hn nodes b δ chalV pubVal orbit P).mp hsat).1
  have hlt : ∀ k (hk : k < n), envsN hn nodes chalV pubVal orbit P k = rEF nodes chalV pubVal orbit P ⟨k, hk⟩ :=
    fun k hk => by simp [envsN, hk]
  have hg : ∀ i < n, ∀ g ∈ Compute.LogUp.accGates 3 (sl.map castSlot) accBase pubBase,
      g.eval (envsN hn nodes chalV pubVal orbit P i) = 0 := by
    intro i hi g hg
    rw [← accGates_map] at hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    rw [hlt i hi, eval_mapC_cast]
    exact base_of_satQ hn nodes b δ chalV pubVal orbit P hsat _ t (hsub t ht)
  have hsum := Compute.LogUp.acc_rows b (sl.map castSlot) accBase pubBase n hn
    (envsN hn nodes chalV pubVal orbit P) hg
    (fun i hi j => by
      rw [hlt i (by omega), hlt (i + 1) hi]
      exact traceNext_eq nodes orbit P _ _ hadj ⟨i, by omega⟩ hi j)
    (by rw [hlt 0 hn, (masksCQ hn nodes b δ chalV pubVal orbit P hbind hinj _).1]; rfl)
    (fun i hi => by
      rw [hlt i (by omega), (masksCQ hn nodes b δ chalV pubVal orbit P hbind hinj _).2]
      simp only; rw [if_neg (by omega)])
    (by rw [hlt (n - 1) (by omega), (masksCQ hn nodes b δ chalV pubVal orbit P hbind hinj _).2]; simp)
    (Compute.LogUp.limbVal b pubVal pubBase)
    (by rw [hlt (n - 1) (by omega)]; rfl)
  rw [← hsum, Finset.sum_range (fun i => Compute.LogUp.termVal b (sl.map castSlot)
    (envsN hn nodes chalV pubVal orbit P i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hlt i i.isLt]

/-- The Im export / path accumulator slot lists. -/
def slotsXIm : List (Compute.LogUp.Slot F) :=
  ((slots : List (SlotSpec ℚ)).map fun S => (⟨S.actX, imOf S.inv⟩ : Compute.LogUp.Slot ℚ)).map castSlot
def slotsPIm : List (Compute.LogUp.Slot F) :=
  ((slots : List (SlotSpec ℚ)).map fun S => (⟨S.actP, imOf S.inv⟩ : Compute.LogUp.Slot ℚ)).map castSlot

theorem mk_list_sum {ι : Type} (l : List ι) (f g : ι → K) :
    Quad.mk (algebraMap F K δ) (l.map f).sum (l.map g).sum = (l.map fun i => Quad.mk (algebraMap F K δ) (f i) (g i)).sum := by
  induction l with
  | nil => simp [Quad.mk_zero']
  | cons a t ih => simp only [List.map_cons, List.sum_cons]; rw [← ih, Quad.mk_add]

theorem mk_fsum {ι : Type} (s : Finset ι) (f g : ι → K) :
    ∑ i ∈ s, Quad.mk (algebraMap F K δ) (f i) (g i) = Quad.mk (algebraMap F K δ) (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Quad.mk_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, Quad.mk_add]

theorem termVal_slots' (sel : SlotSpec ℚ → CoeffExpr ℚ) (ib : SlotSpec ℚ → ℕ) (eF : Env F) :
    Compute.LogUp.termVal b (((slots : List (SlotSpec ℚ)).map fun S => (⟨sel S, ib S⟩ : Compute.LogUp.Slot ℚ)).map
        castSlot) eF =
      ((slots : List (SlotSpec ℚ)).map fun S =>
        algebraMap F K (evalQ (sel S) eF) * (Compute.TowerD.gatherEnv b eF).trace (ib S)).sum := by
  simp only [Compute.LogUp.termVal, List.map_map, Function.comp_def, castSlot, eval_mapC_cast,
    Algebra.smul_def]
  rfl

/-- A row's export term at `𝕂′` is the pair (Re limb term, Im limb term). -/
theorem termXQ_eq (eF : Env F) :
    termXQ δ b eF = Quad.mk _
      (Compute.LogUp.termVal b (((slots : List (SlotSpec ℚ)).map fun S =>
        (⟨S.actX, S.inv⟩ : Compute.LogUp.Slot ℚ)).map castSlot) eF)
      (Compute.LogUp.termVal b (((slots : List (SlotSpec ℚ)).map fun S =>
        (⟨S.actX, imOf S.inv⟩ : Compute.LogUp.Slot ℚ)).map castSlot) eF) := by
  rw [termVal_slots', termVal_slots', mk_list_sum, termXQ]
  congr 1
  refine List.map_congr_left fun S _ => ?_
  rw [invQ, aMF, Quad.mk_smul]

theorem termPQ_eq (eF : Env F) :
    termPQ δ b eF = Quad.mk _
      (Compute.LogUp.termVal b (((slots : List (SlotSpec ℚ)).map fun S =>
        (⟨S.actP, S.inv⟩ : Compute.LogUp.Slot ℚ)).map castSlot) eF)
      (Compute.LogUp.termVal b (((slots : List (SlotSpec ℚ)).map fun S =>
        (⟨S.actP, imOf S.inv⟩ : Compute.LogUp.Slot ℚ)).map castSlot) eF) := by
  rw [termVal_slots', termVal_slots', mk_list_sum, termPQ]
  congr 1
  refine List.map_congr_left fun S _ => ?_
  rw [invQ, aMF, Quad.mk_smul]

/-- The compute twin's `𝕂′` coins, read off the challenge vector. -/
def coinsCV : IOCoins 𝕂′ :=
  ⟨Quad.mk _ (limbVal b chalV chalGammaL) (limbVal b chalV chalGammaIm),
    Quad.mk _ (limbVal b chalV chalRhoL) (limbVal b chalV chalRhoIm)⟩

theorem coinsCQ_rEF (i : Fin n) : coinsCQ δ (gK b (rEF nodes chalV pubVal orbit P i)) = coinsCV b δ chalV := rfl

theorem accXIm_sub : ∀ t ∈ Compute.LogUp.accGates 3 ((slots : List (SlotSpec ℚ)).map fun S =>
    (⟨S.actX, imOf S.inv⟩ : Compute.LogUp.Slot ℚ)) accXIm pubRhoXIm, t ∈ baseGatesHQ (F := ℚ) := fun t ht => by
  simp only [baseGatesHQ, accGatesHQ, List.mem_append]; exact Or.inl (Or.inr (Or.inl (Or.inr ht)))

theorem accPIm_sub : ∀ t ∈ Compute.LogUp.accGates 3 ((slots : List (SlotSpec ℚ)).map fun S =>
    (⟨S.actP, imOf S.inv⟩ : Compute.LogUp.Slot ℚ)) accPIm pubRhoPIm, t ∈ baseGatesHQ (F := ℚ) := fun t ht => by
  simp only [baseGatesHQ, accGatesHQ, List.mem_append]; exact Or.inl (Or.inr (Or.inr ht))

/-- **The `𝕂′` compute export telescope**: `Σ_{compXReqs} compress′(lift r)⁻¹ = (limbs 15, limbs 21)`. -/
theorem compXQ_sum (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHQ hn nodes b δ chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hc : 11 < ringChar F)
    (hden : ∀ r ∈ compPReqs (K := K) nodes chalV pubVal orbit P, compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r) ≠ 0) :
    ((compXReqs (K := K) nodes chalV pubVal orbit P).map fun r => (compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (limbVal b pubVal pubRhoX) (limbVal b pubVal pubRhoXIm) := by
  rw [compXReqs, map_flatMap_sum, sum_finRange]
  have hrow : ∀ i : Fin n, ((rowXReqs (K := K) (rEF nodes chalV pubVal orbit P i)).map fun r =>
      (compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r))⁻¹).sum = termXQ δ b (rEF nodes chalV pubVal orbit P i) := by
    intro i
    obtain ⟨j0, hs⟩ := rowSel_of_base (fun t ht => base_of_satQ hn nodes b δ chalV pubVal orbit P hsat i t
      (baseH_sub t ht)) hc
    rw [termXQ_row δ b hs (fun S hS => pair_of_satQ hn nodes b δ chalV pubVal orbit P hsat i S hS)
      (fun r hr => hden r (List.mem_flatMap.mpr ⟨i, List.mem_finRange _, hr⟩)), coinsCQ_rEF]
  simp only [hrow, termXQ_eq]
  rw [mk_fsum, compute_telescopeQ hn nodes b δ chalV pubVal orbit P hsat hinj hadj _ accX pubRhoX
      (fun t ht => baseH_sub t (accX_sub t ht)),
    compute_telescopeQ hn nodes b δ chalV pubVal orbit P hsat hinj hadj _ accXIm pubRhoXIm accXIm_sub]

/-- **The `𝕂′` compute path telescope**: `Σ_{compPReqs} compress′(lift r)⁻¹ = (limbs 18, limbs 24)`. -/
theorem compPQ_sum (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLHQ hn nodes b δ chalV pubVal orbit) P)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hc : 11 < ringChar F)
    (hden : ∀ r ∈ compPReqs (K := K) nodes chalV pubVal orbit P, compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r) ≠ 0) :
    ((compPReqs (K := K) nodes chalV pubVal orbit P).map fun r => (compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r))⁻¹).sum =
      Quad.mk _ (limbVal b pubVal pubRhoP) (limbVal b pubVal pubRhoPIm) := by
  rw [compPReqs, map_flatMap_sum, sum_finRange]
  have hrow : ∀ i : Fin n, ((rowPReqs (K := K) (rEF nodes chalV pubVal orbit P i)).map fun r =>
      (compress (coinsCV b δ chalV) (liftRec (L := 𝕂′) r))⁻¹).sum = termPQ δ b (rEF nodes chalV pubVal orbit P i) := by
    intro i
    obtain ⟨j0, hs⟩ := rowSel_of_base (fun t ht => base_of_satQ hn nodes b δ chalV pubVal orbit P hsat i t
      (baseH_sub t ht)) hc
    rw [termPQ_row δ b hs (fun S hS => pair_of_satQ hn nodes b δ chalV pubVal orbit P hsat i S hS)
      (fun r hr => hden r (List.mem_flatMap.mpr ⟨i, List.mem_finRange _, hr⟩)), coinsCQ_rEF]
  simp only [hrow, termPQ_eq]
  rw [mk_fsum, compute_telescopeQ hn nodes b δ chalV pubVal orbit P hsat hinj hadj _ accP pubRhoP
      (fun t ht => baseH_sub t (accP_sub t ht)),
    compute_telescopeQ hn nodes b δ chalV pubVal orbit P hsat hinj hadj _ accPIm pubRhoPIm accPIm_sub]

end Chip

end

end Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ
