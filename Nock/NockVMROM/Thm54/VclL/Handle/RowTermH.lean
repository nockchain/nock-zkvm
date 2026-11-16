/-
  Nock/NockVMROM/Thm54/VclL/Handle/RowTermH.lean

  Additive; no existing module edited.

  At a row whose base columns are `colVal cells r fst lst` (`AtRow`), with `r` semantically valid, the
  three slots' contributions to the two accumulators are, slot by slot and opcode by opcode:
  * `slot_terms_row` (generic in the opcode): `act * inv` = sum of `1/den` over the active records
    (`SlotTermH.slot_term` at `P x := evalQ x.act = 1`); `active_le_one` (state disjointness; the OP5
    pair only on OP5), `extras_01`, `filter_export_eq` / `filter_path_eq` (activity = state and extra);
  * `export_terms_row` / `termValX_row`: the export accumulator's row term (`termVal` of `slotsX`) equals
    `Sigma 1/recDen ρ γ (entryRec cells x)` over `exportEntries r`;
  * `path_terms_row` / `termValP_row`: the path accumulator's row term (`slotsP`, including the OP5
    first-difference pair) equals `Sigma 1/recDenP ρ γ (entRecP cells x)` over `consEntries (hn r)`.
  Hypotheses (not discharged here): the honest slot inverses `inv = A / D`, non-zero active denominators
  (the priced pole event of `PoleFree`), the limb bridge, and the OP3 hosting.  The 11-opcode casework is
  closed by `interval_cases` + `simp`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.SlotTermH
import Nock.NockVMROM.Thm54.VclL.Handle.WalkGatesH
import Nock.NockVMROM.Thm54.VclL.Handle.DenRecH
import Nock.NockVMROM.Thm54.VclL.Handle.PathConsH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Walk Nock.Reified Module
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH

noncomputable section

section Row
variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable (cells : List Noun) (r : RowN) (fst lst : F) (eF : Env F)

/-- The honest env reads the base columns. -/
def AtRow : Prop := ∀ i, i ≤ 42 → eF.trace i = colVal cells r fst lst i

theorem selS_eval (hE : AtRow cells r fst lst eF) (l : List ℕ) (hl : l.Nodup) (hle : ∀ i ∈ l, i ≤ 10) :
    evalQ (selS (F := ℚ) l) eF = if r.op ∈ l then 1 else 0 := by
  unfold selS
  rw [evalQ_sumList]
  simp only [evalQ_cc]
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd := List.nodup_cons.mp hl
    have ih' := ih hnd.2 (fun i hi => hle i (List.mem_cons_of_mem _ hi))
    have h10 := hle a (List.mem_cons_self ..)
    have ha : eF.trace a = if r.op = a then 1 else 0 := by
      rw [hE a (by omega)]; simp [colVal, h10]
    simp only [List.map_cons, List.sum_cons, ha, ih']
    by_cases h : r.op = a
    · subst h; simp [hnd.1]
    · simp [h]

/-- The three slots' extras evaluate to 0 / 1 at an honest row. -/
theorem z1v_01 (r : RowN) : z1v (F := F) r = 0 ∨ z1v (F := F) r = 1 := by
  unfold z1v; split_ifs <;> simp

theorem prv_01 (r : RowN) : prv (F := F) r = 0 ∨ prv (F := F) r = 1 := by
  unfold prv; split_ifs <;> simp

theorem hdl_k_01 (c : List Noun) (n : Noun) : (hdl (F := F) c n).1 = 0 ∨ (hdl (F := F) c n).1 = 1 := by
  cases n <;> simp [hdl]

/-- The activity of an entry: the state selector times the extra. -/
theorem ent_act_eval (hE : AtRow cells r fst lst eF) (x : Ent ℚ) (hnd : x.states.Nodup)
    (hle : ∀ i ∈ x.states, i ≤ 10) :
    evalQ x.act eF = (if r.op ∈ x.states then 1 else 0) * evalQ x.extra eF := by
  simp only [Ent.act, evalQ, selS_eval cells r fst lst eF hE _ hnd hle]

theorem slots_nodup : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ x ∈ S.ents,
    x.states.Nodup ∧ ∀ i ∈ x.states, i ≤ 10 := by
  intro S hS x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl <;>
  · simp only [slot0, slot1, slot2, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only; refine ⟨?_, ?_⟩ <;> decide)


variable (eK : Env K)

open Classical in
/-- `D` and `A` of a slot (`slotGate_honest`). -/
def slotDR (S : SlotSpec ℚ) : K :=
  (S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (den x.rcd) eK eF).sum +
    (match S.pair with
     | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF * evalMQ (den b) eK eF)
     | none => 0)

def slotAR (S : SlotSpec ℚ) : K :=
  algebraMap F K ((S.ents.map fun x => evalQ x.act eF).sum) +
    (match S.pair with
     | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF + evalMQ (den b) eK eF)
     | none => 0)

theorem extra_eval (hE : AtRow cells r fst lst eF) :
    evalQ (notC (F := ℚ) z1C) eF = 1 - z1v r ∧
    evalQ (cc (F := ℚ) hSf1.k) eF = (hdl (F := F) cells (hn r).sf1).1 := by
  refine ⟨?_, ?_⟩
  · rw [evalQ_notC, hE z1C (by decide)]; simp [z1C, colVal]
  · rw [evalQ_cc, hE hSf1.k (by decide)]; simp [hSf1, hd, colVal]


theorem filter_length_mono {α : Type} (l : List α) (P Q : α → Bool) (h : ∀ x ∈ l, P x = true → Q x = true) :
    (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (List.mem_cons_self ..)
    by_cases hP : P a = true
    · have hQ := ha hP
      simp [List.filter_cons, hP, hQ, ih']
    · by_cases hQ : Q a = true
      · simp [List.filter_cons, hP, hQ]; omega
      · simp [List.filter_cons, hP, hQ, ih']

theorem states_le_one : ∀ o ≤ 10, ∀ S ∈ [slot0 (F := ℚ), slot1, slot2],
    (S.ents.filter fun x => decide (o ∈ x.states)).length ≤ 1 := by decide

theorem states_five : ((slot2 (F := ℚ)).ents.filter fun x => decide (5 ∈ x.states)).length = 0 := by decide

open Classical in
theorem active_le_one (hE : AtRow cells r fst lst eF) (hle : r.op ≤ 10) :
    ∀ S ∈ [slot0 (F := ℚ), slot1, slot2],
      (S.ents.filter fun x => decide (evalQ x.act eF = 1)).length +
        (if (∃ fl a b, S.pair = some (fl, a, b) ∧ evalQ (cc fl) eF = 1) then 1 else 0) ≤ 1 := by
  have hz := extra_eval cells r fst lst eF hE
  have hsel : ∀ x ∈ ((slot0 (F := ℚ)).ents ++ (slot1 (F := ℚ)).ents ++ (slot2 (F := ℚ)).ents),
      evalQ x.act eF = (if r.op ∈ x.states then 1 else 0) * evalQ x.extra eF := by
    intro x hx
    simp only [List.mem_append] at hx
    have := slots_nodup
    rcases hx with (hx | hx) | hx
    · exact ent_act_eval cells r fst lst eF hE x (this _ (by simp) x hx).1 (this _ (by simp) x hx).2
    · exact ent_act_eval cells r fst lst eF hE x (this _ (by simp) x hx).1 (this _ (by simp) x hx).2
    · exact ent_act_eval cells r fst lst eF hE x (this _ (by simp) x hx).1 (this _ (by simp) x hx).2
  intro S hS
  have hmono : (S.ents.filter fun x => decide (evalQ x.act eF = 1)).length ≤
      (S.ents.filter fun x => decide (r.op ∈ x.states)).length := by
    apply filter_length_mono
    intro x hx hP
    have hP' : evalQ x.act eF = 1 := by simpa using hP
    have hxm : x ∈ ((slot0 (F := ℚ)).ents ++ (slot1 (F := ℚ)).ents ++ (slot2 (F := ℚ)).ents) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl | rfl <;> simp [hx]
    rw [hsel x hxm] at hP'
    by_contra hn
    have : r.op ∉ x.states := by simpa using hn
    simp [this] at hP'
  have h1 := states_le_one r.op hle S hS
  by_cases hq : ∃ fl a b, S.pair = some (fl, a, b) ∧ evalQ (cc fl) eF = 1
  · simp only [hq, if_true]
    obtain ⟨fl, a, b, hp, hf⟩ := hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl
    · simp [slot0] at hp
    · simp [slot1] at hp
    · simp only [slot2, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, -, -⟩ := hp
      have h18 : eF.trace prC = prv r := by rw [hE prC (by decide)]; simp [prC, colVal]
      rw [evalQ_cc, h18] at hf
      have hop5 : r.op = 5 := by
        unfold prv at hf
        split_ifs at hf with h
        · exact h.1
        · simp at hf
      have := states_five
      rw [hop5] at hmono
      omega
  · simp only [hq, if_false]; omega


theorem extras_01 (hE : AtRow cells r fst lst eF) :
    ∀ x ∈ ((slot0 (F := ℚ)).ents ++ (slot1 (F := ℚ)).ents ++ (slot2 (F := ℚ)).ents),
      evalQ x.extra eF = 0 ∨ evalQ x.extra eF = 1 := by
  have hz := extra_eval cells r fst lst eF hE
  intro x hx
  simp only [slot0, slot1, slot2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> simp only [evalQ_cc, hz.1, hz.2]
  all_goals first
    | (right; simp [evalQ]; done)
    | (rcases z1v_01 (F := F) r with h | h <;> simp [h]; done)
    | (rcases hdl_k_01 (F := F) cells (hn r).sf1 with h | h <;> simp [h]; done)

open Classical in
/-- **The slot terms at an honest row** (generic in the opcode): each slot's `act * inv` equals the sum of
`1/den` over its active records. -/
theorem slot_terms_row (hE : AtRow cells r fst lst eF) (hle : r.op ≤ 10)
    (hinv : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], eK.trace S.inv = slotAR eF eK S * (slotDR eF eK S)⁻¹)
    (hpole : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ x ∈ S.ents, evalQ x.act eF = 1 →
      evalMQ (den x.rcd) eK eF ≠ 0)
    (hpoleP : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ fl a b, S.pair = some (fl, a, b) →
      evalQ (cc fl) eF = 1 → evalMQ (den a) eK eF ≠ 0 ∧ evalMQ (den b) eK eF ≠ 0) :
    ∀ S ∈ [slot0 (F := ℚ), slot1, slot2],
      algebraMap F K (evalQ S.actX eF) * eK.trace S.inv =
        ((S.ents.filter fun x => !x.path && decide (evalQ x.act eF = 1)).map
          fun x => (evalMQ (den x.rcd) eK eF)⁻¹).sum ∧
      algebraMap F K (evalQ S.actP eF) * eK.trace S.inv =
        ((S.ents.filter fun x => x.path && decide (evalQ x.act eF = 1)).map
          fun x => (evalMQ (den x.rcd) eK eF)⁻¹).sum +
          pairTerm S eK eF (∃ fl a b, S.pair = some (fl, a, b) ∧ evalQ (cc fl) eF = 1) := by
  intro S hS
  have hall : ∀ x ∈ S.ents, x ∈ ((slot0 (F := ℚ)).ents ++ (slot1 (F := ℚ)).ents ++ (slot2 (F := ℚ)).ents) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl <;> simp [hx]
  have hsel : ∀ x ∈ S.ents, evalQ x.act eF = (if r.op ∈ x.states then 1 else 0) * evalQ x.extra eF := by
    intro x hx
    have hh := slots_nodup S hS x hx
    exact ent_act_eval cells r fst lst eF hE x hh.1 hh.2
  have hact : ∀ x ∈ S.ents, evalQ x.act eF = if evalQ x.act eF = 1 then 1 else 0 := by
    intro x hx
    have h01 := extras_01 cells r fst lst eF hE x (hall x hx)
    rw [hsel x hx]
    by_cases hm : r.op ∈ x.states <;> rcases h01 with h | h <;> simp [hm, h]
  have hfl : ∀ fl a b, S.pair = some (fl, a, b) →
      evalQ (cc fl) eF = if (∃ fl a b, S.pair = some (fl, a, b) ∧ evalQ (cc fl) eF = 1) then 1 else 0 := by
    intro fl a b hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl
    · simp [slot0] at hp
    · simp [slot1] at hp
    · simp only [slot2, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, -, -⟩ := hp
      have h18 : eF.trace prC = prv r := by rw [hE prC (by decide)]; simp [prC, colVal]
      rw [evalQ_cc, h18]
      rcases prv_01 (F := F) r with h | h
      · rw [h]
        have : ¬ ∃ fl a b, (slot2 (F := ℚ)).pair = some (fl, a, b) ∧ evalQ (cc fl) eF = 1 := by
          rintro ⟨fl', a', b', hp', hf'⟩
          simp only [slot2, Option.some.injEq, Prod.mk.injEq] at hp'
          obtain ⟨rfl, -, -⟩ := hp'
          rw [evalQ_cc, h18, h] at hf'
          exact zero_ne_one hf'
        rw [if_neg this]
      · rw [h]
        have : ∃ fl a b, (slot2 (F := ℚ)).pair = some (fl, a, b) ∧ evalQ (cc fl) eF = 1 :=
          ⟨prC, _, _, rfl, by rw [evalQ_cc, h18, h]⟩
        rw [if_pos this]
  have hq : S.pair = none → ¬ (∃ fl a b, S.pair = some (fl, a, b) ∧ evalQ (cc fl) eF = 1) := by
    intro hp; rintro ⟨fl, a, b, hp', -⟩; rw [hp] at hp'; cases hp'
  exact slot_term S eK eF (fun x => evalQ x.act eF = 1) _ hact hfl hq
    (active_le_one cells r fst lst eF hE hle S hS) (hpole S hS)
    (fun fl a b hp hq' => hpoleP S hS fl a b hp (by
      obtain ⟨fl', a', b', hp', hf'⟩ := hq'
      rw [hp] at hp'
      simp only [Option.some.injEq, Prod.mk.injEq] at hp'
      obtain ⟨rfl, -, -⟩ := hp'
      exact hf')) _ _ rfl rfl (hinv S hS)


open Classical in
/-- The active export entries of a slot, with the activity unfolded to states and extras. -/
theorem filter_export_eq (hE : AtRow cells r fst lst eF) (S : SlotSpec ℚ)
    (hS : S ∈ [slot0 (F := ℚ), slot1, slot2]) (f : Ent ℚ → K) :
    ((S.ents.filter fun x => !x.path && decide (evalQ x.act eF = 1)).map f) =
      ((S.ents.filter fun x => !x.path && decide (r.op ∈ x.states ∧ evalQ x.extra eF = 1)).map f) := by
  have hall : ∀ x ∈ S.ents, x ∈ ((slot0 (F := ℚ)).ents ++ (slot1 (F := ℚ)).ents ++ (slot2 (F := ℚ)).ents) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl <;> simp [hx]
  congr 1
  refine List.filter_congr fun x hx => ?_
  have hh := slots_nodup S hS x hx
  have h01 := extras_01 cells r fst lst eF hE x (hall x hx)
  have := ent_act_eval cells r fst lst eF hE x hh.1 hh.2
  congr 1
  apply decide_eq_decide.mpr
  rw [this]
  by_cases hm : r.op ∈ x.states <;> rcases h01 with h | h <;> simp [hm, h]


theorem op_le_ten (hs : r.Sem) : r.op ≤ 10 := by
  unfold RowN.Sem at hs
  by_contra h
  split at hs <;> first | exact hs | omega

theorem hn_s' (r : RowN) : (hn r).s = r.s := by unfold hn; split_ifs <;> rfl
theorem hn_sf1' (r : RowN) : (hn r).sf1 = r.sf1 := by unfold hn; split_ifs <;> rfl
theorem hn_sf2' (r : RowN) : (hn r).sf2 = r.sf2 := by unfold hn; split_ifs <;> rfl
theorem hn_op_row (r : RowN) : (hn r).op = r.op := by unfold hn; split_ifs <;> rfl
theorem hn_m_ne (r : RowN) (h : r.op ≠ 5) : (hn r).m = r.m := by rw [hn_of_ne r h]
theorem hn_ftth_ne (r : RowN) (h : r.op ≠ 5) : (hn r).ftth = r.ftth := by rw [hn_of_ne r h]
theorem hn_fttt_ne (r : RowN) (h : r.op ≠ 5) : (hn r).fttt = r.fttt := by rw [hn_of_ne r h]

open Classical in
theorem export_terms_row (hs : r.Sem) (hE : AtRow cells r fst lst eF)
    (hhost : r.op = 3 → r.ftth = hdN r.sf1 ∧ r.fttt = tlN r.sf1)
    (hinv : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], eK.trace S.inv = slotAR eF eK S * (slotDR eF eK S)⁻¹)
    (hpole : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ x ∈ S.ents, evalQ x.act eF = 1 →
      evalMQ (den x.rcd) eK eF ≠ 0)
    (hpoleP : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ fl a b, S.pair = some (fl, a, b) →
      evalQ (cc fl) eF = 1 → evalMQ (den a) eK eF ≠ 0 ∧ evalMQ (den b) eK eF ≠ 0) :
    ([slot0 (F := ℚ), slot1, slot2].map fun S => algebraMap F K (evalQ S.actX eF) * eK.trace S.inv).sum =
      ((exportEntries r).map fun x =>
        (recDen (eK.chal chalRhoL) (eK.chal chalGammaL) (entryRec (F := F) cells x))⁻¹).sum := by
  have hle := op_le_ten r hs
  have hT := slot_terms_row cells r fst lst eF eK hE hle hinv hpole hpoleP
  have hRHS : ((exportEntries r).map fun x =>
        (recDen (eK.chal chalRhoL) (eK.chal chalGammaL) (entryRec (F := F) cells x))⁻¹) =
      ((exportEntries r).map fun x =>
        (recDen (eK.chal chalRhoL) (eK.chal chalGammaL)
          ((hdl (F := F) cells x.1).2, hdl (F := F) cells x.2.1, hdl (F := F) cells x.2.2))⁻¹) :=
    List.map_congr_left fun x hx => by
      rw [recDen_entry cells _ _ x (by rw [exportEntries_cell r hs x hx]; rfl)]
  rw [hRHS]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [(hT slot0 (by simp)).1, (hT slot1 (by simp)).1, (hT slot2 (by simp)).1]
  rw [filter_export_eq cells r fst lst eF hE slot0 (by simp), filter_export_eq cells r fst lst eF hE slot1 (by simp),
    filter_export_eq cells r fst lst eF hE slot2 (by simp)]
  have hz := extra_eval cells r fst lst eF hE
  have t19 := hE 19 (by norm_num)
  have t20 := hE 20 (by norm_num)
  have t21 := hE 21 (by norm_num)
  have t22 := hE 22 (by norm_num)
  have t23 := hE 23 (by norm_num)
  have t24 := hE 24 (by norm_num)
  have t25 := hE 25 (by norm_num)
  have t26 := hE 26 (by norm_num)
  have t27 := hE 27 (by norm_num)
  have t28 := hE 28 (by norm_num)
  have t29 := hE 29 (by norm_num)
  have t30 := hE 30 (by norm_num)
  have t31 := hE 31 (by norm_num)
  have t32 := hE 32 (by norm_num)
  have t33 := hE 33 (by norm_num)
  have t34 := hE 34 (by norm_num)
  have t35 := hE 35 (by norm_num)
  have t36 := hE 36 (by norm_num)
  have t37 := hE 37 (by norm_num)
  have t38 := hE 38 (by norm_num)
  have t39 := hE 39 (by norm_num)
  have t40 := hE 40 (by norm_num)
  have t41 := hE 41 (by norm_num)
  have t42 := hE 42 (by norm_num)
  have hH1 : r.op = 3 → r.ftth = hdN r.sf1 := fun h => (hhost h).1
  have hH2 : r.op = 3 → r.fttt = tlN r.sf1 := fun h => (hhost h).2
  obtain ⟨o, ho⟩ : ∃ o, r.op = o := ⟨_, rfl⟩
  rw [ho] at hle
  interval_cases o
  all_goals
    simp [slot0, slot1, slot2, exportEntries, ho, List.filter_cons, den_cellRec, ChipH.allStates, ChipH.l2States, ChipH.consCol, evalQ, hz.1, hz.2, ChipH.hS, ChipH.hF, ChipH.hE, ChipH.hSf1, ChipH.hSf2, ChipH.hFh, ChipH.hFt, ChipH.hFth, ChipH.hFtt, ChipH.hFtth, ChipH.hFttt, ChipH.hM, hd, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, hn_f, hn_e, hn_ft, hn_fh, hn_fth, hn_ftt, hn_m_ne, hn_ftth_ne, hn_fttt_ne, hn_s', hn_sf1', hn_sf2', hH1, hH2]
  have h25 : evalQ (cc 25) eF = (hdl (F := F) cells r.sf1).1 := by
    rw [evalQ_cc, t25]; simp [cv25, hn_sf1']
  by_cases hc : r.sf1.isCell = true
  · obtain ⟨a, b, hab⟩ : ∃ a b, r.sf1 = Noun.cell a b := by
      cases h : r.sf1 with
      | atom _ => rw [h] at hc; simp [Noun.isCell] at hc
      | cell a b => exact ⟨a, b, rfl⟩
    have h1 : evalQ (cc 25) eF = 1 := by rw [h25, hab]; simp [hdl]
    rw [if_pos h1, if_pos hc]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [den_cellRec]
    simp [t25, t26, t37, t38, t39, t40, cv25, cv26, cv37, cv38, cv39, cv40, hn_sf1', hH1 ho, hH2 ho, ho, hn_ftth_ne, hn_fttt_ne]
  · have h1 : ¬ evalQ (cc 25) eF = 1 := by
      rw [h25]; cases h : r.sf1 with
      | atom v => simp [hdl]
      | cell a b => rw [h] at hc; simp [Noun.isCell] at hc
    rw [if_neg h1, if_neg hc]; simp


theorem root_cell_of_slot {ax : ℕ} {n c : Noun} (h2 : 2 ≤ ax) (h : Noun.slot ax n = some c) : n.isCell = true := by
  cases n with
  | atom v => rw [TraceGen.slot_atom_of_ge_two h2] at h; cases h
  | cell _ _ => rfl

theorem fdN_ne_nil_cell (a b : Noun) (h : (fdN a b).1 ≠ []) : a.isCell = true ∧ b.isCell = true := by
  cases a <;> cases b <;> simp_all [fdN, Noun.isCell]

theorem entRecP_cell (cells : List Noun) (x : PEnt) (hc : x.1.isCell = true) :
    (entRecP (F := F) cells x) = ((hdl (F := F) cells x.1).2, (x.2.1 : F), hdl (F := F) cells x.2.2) := by
  obtain ⟨p, a, c⟩ := x
  cases p with
  | atom _ => simp [Noun.isCell] at hc
  | cell _ _ => simp [entRecP, hdl]

open Classical in
theorem filter_path_eq (hE : AtRow cells r fst lst eF) (S : SlotSpec ℚ)
    (hS : S ∈ [slot0 (F := ℚ), slot1, slot2]) (f : Ent ℚ → K) :
    ((S.ents.filter fun x => x.path && decide (evalQ x.act eF = 1)).map f) =
      ((S.ents.filter fun x => x.path && decide (r.op ∈ x.states ∧ evalQ x.extra eF = 1)).map f) := by
  have hall : ∀ x ∈ S.ents, x ∈ ((slot0 (F := ℚ)).ents ++ (slot1 (F := ℚ)).ents ++ (slot2 (F := ℚ)).ents) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl <;> simp [hx]
  congr 1
  refine List.filter_congr fun x hx => ?_
  have hh := slots_nodup S hS x hx
  have h01 := extras_01 cells r fst lst eF hE x (hall x hx)
  have := ent_act_eval cells r fst lst eF hE x hh.1 hh.2
  congr 1
  apply decide_eq_decide.mpr
  rw [this]
  by_cases hm : r.op ∈ x.states <;> rcases h01 with h | h <;> simp [hm, h]

open Classical in
theorem path_terms_row (hs : r.Sem) (hE : AtRow cells r fst lst eF)
    (hhost : r.op = 3 → r.ftth = hdN r.sf1 ∧ r.fttt = tlN r.sf1)
    (hinv : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], eK.trace S.inv = slotAR eF eK S * (slotDR eF eK S)⁻¹)
    (hpole : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ x ∈ S.ents, evalQ x.act eF = 1 →
      evalMQ (den x.rcd) eK eF ≠ 0)
    (hpoleP : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ fl a b, S.pair = some (fl, a, b) →
      evalQ (cc fl) eF = 1 → evalMQ (den a) eK eF ≠ 0 ∧ evalMQ (den b) eK eF ≠ 0) :
    ([slot0 (F := ℚ), slot1, slot2].map fun S => algebraMap F K (evalQ S.actP eF) * eK.trace S.inv).sum =
      ((consEntries (hn r)).map fun x =>
        (recDenP (eK.chal chalRhoL) (eK.chal chalGammaL) (entRecP (F := F) cells x))⁻¹).sum := by
  have hle := op_le_ten r hs
  have hT := slot_terms_row cells r fst lst eF eK hE hle hinv hpole hpoleP
  have hRHS : ((consEntries (hn r)).map fun x =>
        (recDenP (eK.chal chalRhoL) (eK.chal chalGammaL) (entRecP (F := F) cells x))⁻¹) =
      ((consEntries (hn r)).map fun x =>
        (recDenP (eK.chal chalRhoL) (eK.chal chalGammaL)
          ((hdl (F := F) cells x.1).2, (x.2.1 : F), hdl (F := F) cells x.2.2))⁻¹) :=
    List.map_congr_left fun x hx => by
      have h := row_cons_eq r hs x hx
      rw [entRecP_cell cells x (root_cell_of_slot h.1 h.2)]
  rw [hRHS]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [(hT slot0 (by simp)).2, (hT slot1 (by simp)).2, (hT slot2 (by simp)).2]
  rw [filter_path_eq cells r fst lst eF hE slot0 (by simp), filter_path_eq cells r fst lst eF hE slot1 (by simp),
    filter_path_eq cells r fst lst eF hE slot2 (by simp)]
  have hz := extra_eval cells r fst lst eF hE
  have t19 := hE 19 (by norm_num)
  have t20 := hE 20 (by norm_num)
  have t21 := hE 21 (by norm_num)
  have t22 := hE 22 (by norm_num)
  have t23 := hE 23 (by norm_num)
  have t24 := hE 24 (by norm_num)
  have t25 := hE 25 (by norm_num)
  have t26 := hE 26 (by norm_num)
  have t27 := hE 27 (by norm_num)
  have t28 := hE 28 (by norm_num)
  have t29 := hE 29 (by norm_num)
  have t30 := hE 30 (by norm_num)
  have t31 := hE 31 (by norm_num)
  have t32 := hE 32 (by norm_num)
  have t33 := hE 33 (by norm_num)
  have t34 := hE 34 (by norm_num)
  have t35 := hE 35 (by norm_num)
  have t36 := hE 36 (by norm_num)
  have t37 := hE 37 (by norm_num)
  have t38 := hE 38 (by norm_num)
  have t39 := hE 39 (by norm_num)
  have t40 := hE 40 (by norm_num)
  have t41 := hE 41 (by norm_num)
  have t42 := hE 42 (by norm_num)
  have hH1 : r.op = 3 → r.ftth = hdN r.sf1 := fun h => (hhost h).1
  have hft : r.op = 0 → ∃ ax, r.ft = .atom ax := by
    intro h; have := hs; simp only [RowN.Sem, h] at this
    obtain ⟨-, -, ax, h1, -⟩ := this; exact ⟨ax, h1⟩
  have hfth : r.op = 9 → ∃ ax, r.fth = .atom ax := by
    intro h; have := hs; simp only [RowN.Sem, h] at this
    obtain ⟨-, -, -, -, ax, h1, -⟩ := this; exact ⟨ax, h1⟩
  have hm5 : r.op = 5 → ∃ v, (hn r).m = .atom v := by
    intro h; exact ⟨axisOfPath (fdN r.sf1 r.sf2).1, by simp [hn, h]⟩
  obtain ⟨o, ho⟩ : ∃ o, r.op = o := ⟨_, rfl⟩
  rw [ho] at hle
  have h18 : evalQ (cc prC) eF = prv r := by rw [evalQ_cc, hE prC (by decide)]; simp [prC, colVal]
  interval_cases o
  all_goals
    simp [slot0, slot1, slot2, consEntries, pairTerm, ho, List.filter_cons, den_walkRec, ChipH.allStates, ChipH.l2States, ChipH.consCol, evalQ, hz.1, hz.2, ChipH.hS, ChipH.hF, ChipH.hE, ChipH.hSf1, ChipH.hSf2, ChipH.hFh, ChipH.hFt, ChipH.hFth, ChipH.hFtt, ChipH.hFtth, ChipH.hFttt, ChipH.hM, hd, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, hn_f, hn_e, hn_ft, hn_fh, hn_fth, hn_ftt, hn_m_ne, hn_ftth_ne, hn_fttt_ne, hn_s', hn_sf1', hn_sf2', z1v, prv, h18, hn_op_row]
  all_goals
    split_ifs <;>
    simp [den_walkRec, evalQ, hz.1, hz.2, hd, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, hn_f, hn_e, hn_ft, hn_fh, hn_fth, hn_ftt, hn_m_ne, hn_ftth_ne, hn_fttt_ne, hn_s', hn_sf1', hn_sf2', ho, ChipH.hS, ChipH.hF, ChipH.hE, ChipH.hSf1, ChipH.hSf2, ChipH.hFh, ChipH.hFt, ChipH.hFth, ChipH.hFtt, ChipH.hFtth, ChipH.hFttt, ChipH.hM]
  all_goals first
    | (obtain ⟨ax, hax⟩ := hft ho; simp [hax, hdl, atomVal, hn_ft]; done)
    | (obtain ⟨ax, hax⟩ := hfth ho; simp [hax, hdl, atomVal, hn_fth]; done)
    | (obtain ⟨v, hv⟩ := hm5 ho; simp [hv, hdl, atomVal]; done)


theorem termVal_eq_slots (b : Basis (Fin 3) F K) (acts : List (Slot ℚ)) (eK : Env K)
    (hlimb : ∀ s ∈ acts, limbVal b eF.trace s.invBase = eK.trace s.invBase) :
    termVal b (acts.map (castSlot (F := F))) eF =
      (acts.map fun s => algebraMap F K (evalQ s.act eF) * eK.trace s.invBase).sum := by
  unfold termVal
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  simp only [Function.comp, castSlot, eval_mapC_cast, Algebra.smul_def, hlimb s hs]


open Classical in
/-- **The export accumulator's per-row term is the sum of `1/den` over the row's consumed export records**
(`termVal` of the export slots at the honest row; slot-exclusivity, 0/1 activity, pole-freedom of the
active records and the honest slot inverses as hypotheses; the limb bridge `hlimb` ties the `K`-valued
inverse the mixed gates read to the limbs the accumulator reads). -/
theorem termValX_row (b : Basis (Fin 3) F K) (hs : r.Sem) (hE : AtRow cells r fst lst eF)
    (hhost : r.op = 3 → r.ftth = hdN r.sf1 ∧ r.fttt = tlN r.sf1)
    (hlimb : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], limbVal b eF.trace S.inv = eK.trace S.inv)
    (hinv : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], eK.trace S.inv = slotAR eF eK S * (slotDR eF eK S)⁻¹)
    (hpole : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ x ∈ S.ents, evalQ x.act eF = 1 →
      evalMQ (den x.rcd) eK eF ≠ 0)
    (hpoleP : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ fl a b, S.pair = some (fl, a, b) →
      evalQ (cc fl) eF = 1 → evalMQ (den a) eK eF ≠ 0 ∧ evalMQ (den b) eK eF ≠ 0) :
    termVal b (slotsX (F := F)) eF =
      ((exportEntries r).map fun x =>
        (recDen (eK.chal chalRhoL) (eK.chal chalGammaL) (entryRec (F := F) cells x))⁻¹).sum := by
  rw [← export_terms_row cells r fst lst eF eK hs hE hhost hinv hpole hpoleP]
  unfold slotsX
  rw [termVal_eq_slots eF b _ eK (by
    intro s hs'
    simp only [List.mem_map] at hs'
    obtain ⟨S, hS, rfl⟩ := hs'
    exact hlimb S (by simpa [ChipH.slots] using hS))]
  simp [ChipH.slots, List.map_map, Function.comp]

open Classical in
/-- **The path accumulator's per-row term is the sum of `1/den` over the row's consumed walk-handle
records** (OP0, OP9 and the OP5 first-difference pair; `consEntries`). -/
theorem termValP_row (b : Basis (Fin 3) F K) (hs : r.Sem) (hE : AtRow cells r fst lst eF)
    (hhost : r.op = 3 → r.ftth = hdN r.sf1 ∧ r.fttt = tlN r.sf1)
    (hlimb : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], limbVal b eF.trace S.inv = eK.trace S.inv)
    (hinv : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], eK.trace S.inv = slotAR eF eK S * (slotDR eF eK S)⁻¹)
    (hpole : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ x ∈ S.ents, evalQ x.act eF = 1 →
      evalMQ (den x.rcd) eK eF ≠ 0)
    (hpoleP : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ fl a b, S.pair = some (fl, a, b) →
      evalQ (cc fl) eF = 1 → evalMQ (den a) eK eF ≠ 0 ∧ evalMQ (den b) eK eF ≠ 0) :
    termVal b (slotsP (F := F)) eF =
      ((consEntries (hn r)).map fun x =>
        (recDenP (eK.chal chalRhoL) (eK.chal chalGammaL) (entRecP (F := F) cells x))⁻¹).sum := by
  rw [← path_terms_row cells r fst lst eF eK hs hE hhost hinv hpole hpoleP]
  unfold slotsP
  rw [termVal_eq_slots eF b _ eK (by
    intro s hs'
    simp only [List.mem_map] at hs'
    obtain ⟨S, hS, rfl⟩ := hs'
    exact hlimb S (by simpa [ChipH.slots] using hS))]
  simp [ChipH.slots, List.map_map, Function.comp]

end Row

end

end Nock.NockVMROM.Thm54.VclL.Handle
