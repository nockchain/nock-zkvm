/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestFillH.lean

  Additive.

  * `HonestFill`: the inverse limbs of each slot read `A / D` at the row (`gE b eF`, the limb reading of the
    base trace, so the limb bridge `hlimb` is `rfl`).
  * `polesOf` / `NotBadRow` / `poles_of_notBad`: the non-zero active denominators of `termVal*_row` are exactly
    "the pole coin hits no record of the row"; `poleRow_card`: that event has at most `|polesOf|` coins
    (a priced completeness summand, not a hypothesis).
  * `termValX_honest` / `termValP_honest`: at an honest row (`Sem`, `AtRow`, OP3 hosted, `HonestFill`,
    `NotBadRow`) the export / path accumulator terms are `Sigma 1/recDen` / `Sigma 1/recDenP` over the consumed
    records.
  * `accGatesH_honest_rows`: the 18 accumulator gates hold at the honest fill with the honest totals `rxTot` /
    `rpTot` as the publics; no `termVal` hypothesis remains.
  * `slot_pole_free`, `slotGates_honest_row`: the 3 slot gates hold at the honest fill (the pole-free condition
    `D != 0 or A = 0` is derived from at most one active record and non-zero denominators).
  NOT shown (UNCONFIRMED): that the fill `HonestFill` is attainable (the inverse limbs lie outside the columns
  `AtRow` and `den` read, so `A / D` does not depend on them; not proved here), and the `mixedCompile` lowering.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RowTermH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLookups
import Nock.NockVMROM.Thm54.VclL.Handle.TwinGatesH

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

section Fill
variable {F K : Type} [Field F] [Field K] [Algebra F K]

abbrev gE (b : Basis (Fin 3) F K) (eF : Env F) : Env K :=
  Nock.NockVMROM.Thm54.VclL.Compute.TowerD.gatherEnv b eF

/-- The honest bad event of one compute row, as a list: the `rlc` of every record the three slots can
consume (the `ents` and the OP5 pair).  `ρ` hits a denominator iff `ρ + x = 0` for some `x` here. -/
def polesOf (eK : Env K) (eF : Env F) : List K :=
  [slot0 (F := ℚ), slot1, slot2].flatMap fun S =>
    (S.ents.map fun x => rlcL (eK.chal chalGammaL) 0 (x.rcd.map fun i => algebraMap F K (eF.trace i))) ++
    (match S.pair with
     | some (_, a, b) =>
        [rlcL (eK.chal chalGammaL) 0 (a.map fun i => algebraMap F K (eF.trace i)),
         rlcL (eK.chal chalGammaL) 0 (b.map fun i => algebraMap F K (eF.trace i))]
     | none => [])

/-- **Not in the priced pole event**: the pole coin hits no record of the row. -/
def NotBadRow (eK : Env K) (eF : Env F) : Prop :=
  ∀ x ∈ polesOf eK eF, eK.chal chalRhoL + x ≠ 0

theorem poles_of_notBad (eK : Env K) (eF : Env F) (hnb : NotBadRow eK eF) :
    (∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ x ∈ S.ents, evalQ x.act eF = 1 →
      evalMQ (den x.rcd) eK eF ≠ 0) ∧
    (∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ fl a b, S.pair = some (fl, a, b) →
      evalQ (cc fl) eF = 1 → evalMQ (den a) eK eF ≠ 0 ∧ evalMQ (den b) eK eF ≠ 0) := by
  refine ⟨fun S hS x hx _ => ?_, fun S hS fl a b hp _ => ?_⟩
  · rw [den_eval]
    exact hnb _ (by
      simp only [polesOf, List.mem_flatMap, List.mem_append, List.mem_map]
      exact ⟨S, hS, Or.inl ⟨x, hx, rfl⟩⟩)
  · rw [den_eval, den_eval]
    refine ⟨hnb _ ?_, hnb _ ?_⟩ <;>
    · simp only [polesOf, List.mem_flatMap, List.mem_append, List.mem_map]
      refine ⟨S, hS, Or.inr ?_⟩
      simp [hp]

section Pricing
variable [Fintype K] [DecidableEq K]

/-- **The row's pole event has at most `|polesOf|` coins** (a completeness summand), and outside it the row
is `NotBadRow`. -/
theorem notBadRow_of_not_bad (eK : Env K) (eF : Env F)
    (hρ : eK.chal chalRhoL ∉ (Finset.univ.filter fun ρ : K => ∃ x ∈ polesOf eK eF, ρ + x = 0)) :
    NotBadRow eK eF := fun x hx => den_ne_zero_of_not_bad _ hx hρ

theorem poleRow_card (eK : Env K) (eF : Env F) :
    (Finset.univ.filter fun ρ : K => ∃ x ∈ polesOf eK eF, ρ + x = 0).card ≤ (polesOf eK eF).length :=
  den_bad_card _

end Pricing

/-- **The honest slot-inverse fill**: the inverse limbs of each slot read `A / D` at the row. -/
def HonestFill (b : Basis (Fin 3) F K) (eF : Env F) : Prop :=
  ∀ S ∈ [slot0 (F := ℚ), slot1, slot2],
    limbVal b eF.trace S.inv = slotAR eF (gE b eF) S * (slotDR eF (gE b eF) S)⁻¹

section Row
variable (cells : List Noun) (r : RowN) (fst lst : F) (eF : Env F) (b : Basis (Fin 3) F K)

open Classical in
/-- **The export accumulator's row term at the honest fill** is `Σ 1/recDen` over the row's export entries:
the limb bridge and the slot inverses are `HonestFill` (`gE` reads the limbs), the nonzero denominators are
`NotBadRow` (outside the priced pole event), OP3 is hosted. -/
theorem termValX_honest (hs : r.Sem) (hE : AtRow cells r fst lst eF)
    (hhost : r.op = 3 → r.ftth = hdN r.sf1 ∧ r.fttt = tlN r.sf1)
    (hfill : HonestFill b eF) (hnb : NotBadRow (gE b eF) eF) :
    termVal b (slotsX (F := F)) eF =
      ((exportEntries r).map fun x =>
        (recDen ((gE b eF).chal chalRhoL) ((gE b eF).chal chalGammaL) (entryRec (F := F) cells x))⁻¹).sum :=
  termValX_row cells r fst lst eF (gE b eF) b hs hE hhost (fun S _ => rfl) (fun S hS => hfill S hS)
    (poles_of_notBad _ _ hnb).1 (poles_of_notBad _ _ hnb).2

open Classical in
theorem termValP_honest (hs : r.Sem) (hE : AtRow cells r fst lst eF)
    (hhost : r.op = 3 → r.ftth = hdN r.sf1 ∧ r.fttt = tlN r.sf1)
    (hfill : HonestFill b eF) (hnb : NotBadRow (gE b eF) eF) :
    termVal b (slotsP (F := F)) eF =
      ((consEntries (hn r)).map fun x =>
        (recDenP ((gE b eF).chal chalRhoL) ((gE b eF).chal chalGammaL) (entRecP (F := F) cells x))⁻¹).sum :=
  termValP_row cells r fst lst eF (gE b eF) b hs hE hhost (fun S _ => rfl) (fun S hS => hfill S hS)
    (poles_of_notBad _ _ hnb).1 (poles_of_notBad _ _ hnb).2

end Row

end Fill

section SlotGates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

open Classical in
/-- **A slot's `D` is non-zero or its `A` is zero**, with at most one active record (or the pair) and
non-zero active denominators: the pole-free condition of `slotGate_honest`, derived. -/
theorem slot_pole_free (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) (P : Ent ℚ → Prop) [DecidablePred P]
    (q : Prop) [Decidable q]
    (hact : ∀ x ∈ S.ents, evalQ x.act eF = if P x then 1 else 0)
    (hfl : ∀ fl a b, S.pair = some (fl, a, b) → evalQ (cc fl) eF = if q then 1 else 0)
    (hq : S.pair = none → ¬ q)
    (hex : (S.ents.filter fun x => decide (P x)).length + (if q then 1 else 0) ≤ 1)
    (hpole : ∀ x ∈ S.ents, P x → evalMQ (den x.rcd) eK eF ≠ 0)
    (hpoleP : ∀ fl a b, S.pair = some (fl, a, b) → q →
      evalMQ (den a) eK eF ≠ 0 ∧ evalMQ (den b) eK eF ≠ 0)
    (D A : K)
    (hD : D = (S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (den x.rcd) eK eF).sum +
          (match S.pair with
           | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF * evalMQ (den b) eK eF)
           | none => 0))
    (hA : A = algebraMap F K ((S.ents.map fun x => evalQ x.act eF).sum) +
        (match S.pair with
         | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF + evalMQ (den b) eK eF)
         | none => 0)) :
    D ≠ 0 ∨ A = 0 := by
  have hDs : (S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (den x.rcd) eK eF).sum =
      ((S.ents.filter fun x => decide (P x)).map fun x => evalMQ (den x.rcd) eK eF).sum := by
    have := sum_filter_act (F := F) (K := K) eF S.ents P (fun _ => true) (fun x => evalMQ (den x.rcd) eK eF) hact
    simpa using this
  have hAs : (S.ents.map fun x => evalQ x.act eF).sum =
      (((S.ents.filter fun x => decide (P x)).length : ℕ) : F) := by
    have := sum_filter_act1 (F := F) eF S.ents P (fun _ => true) hact
    simpa using this
  have hLne : ∀ x ∈ S.ents.filter (fun x => decide (P x)), evalMQ (den x.rcd) eK eF ≠ 0 := by
    intro x hx
    simp only [List.mem_filter, decide_eq_true_eq] at hx
    exact hpole x hx.1 hx.2
  rw [hD, hA, hDs, hAs]
  generalize S.ents.filter (fun x => decide (P x)) = L at *
  by_cases hq' : q
  · have hL0 : L = [] := by
      have : L.length + 1 ≤ 1 := by simpa [hq'] using hex
      exact List.length_eq_zero_iff.mp (by omega)
    subst hL0
    rcases hp : S.pair with _ | ⟨fl, a, b⟩
    · exact absurd hq' (hq hp)
    · left
      obtain ⟨ha, hb⟩ := hpoleP fl a b hp hq'
      simp [hp, hfl fl a b hp, hq', mul_ne_zero ha hb]
  · have hlen : L.length ≤ 1 := by simpa [hq'] using hex
    rcases L with _ | ⟨x, L'⟩
    · right
      rcases hp : S.pair with _ | ⟨fl, a, b⟩
      · simp [hp]
      · simp [hp, hfl fl a b hp, hq']
    · have hL' : L' = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
      subst hL'
      left
      have := hLne x (by simp)
      rcases hp : S.pair with _ | ⟨fl, a, b⟩
      · simp [hp, this]
      · simp [hp, hfl fl a b hp, hq', this]

variable (cells : List Noun) (r : RowN) (fst lst : F) (eF : Env F) (b : Basis (Fin 3) F K)

open Classical in
/-- **The three slot gates hold at the honest fill** (`HonestFill`, outside the priced pole event, `r` valid). -/
theorem slotGates_honest_row (hs : r.Sem) (hE : AtRow cells r fst lst eF)
    (hfill : HonestFill b eF) (hnb : NotBadRow (gE b eF) eF) :
    ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], evalMQ (slotGate S) (gE b eF) eF = 0 := by
  have hle := op_le_ten r hs
  have hpole := (poles_of_notBad _ _ hnb).1
  have hpoleP := (poles_of_notBad _ _ hnb).2
  have hinv : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], (gE b eF).trace S.inv =
      slotAR eF (gE b eF) S * (slotDR eF (gE b eF) S)⁻¹ := fun S hS => hfill S hS
  let eK := gE b eF
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
  exact slotGate_honest S eK eF _ _ rfl rfl (hinv S hS)
    (slot_pole_free S eK eF (fun x => evalQ x.act eF = 1) _ hact hfl hq
      (active_le_one cells r fst lst eF hE hle S hS) (hpole S hS)
      (fun fl a b hp hq' => hpoleP S hS fl a b hp (by
        obtain ⟨fl', a', b', hp', hf'⟩ := hq'
        rw [hp] at hp'
        simp only [Option.some.injEq, Prod.mk.injEq] at hp'
        obtain ⟨rfl, -, -⟩ := hp'
        exact hf')) _ _ rfl rfl)

end SlotGates

section Wire
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The export total: `Σ_j Σ_{x ∈ exportEntries (rows j)} 1/recDen`. -/
def rxTot (b : Basis (Fin 3) F K) (cells : List Noun) (rows : ℕ → RowN) (envs : ℕ → Env F) (N : ℕ) : K :=
  ∑ j ∈ Finset.range N, ((exportEntries (rows j)).map fun x =>
    (recDen ((gE b (envs j)).chal chalRhoL) ((gE b (envs j)).chal chalGammaL)
      (entryRec (F := F) cells x))⁻¹).sum

open Classical in
/-- The path total: `Σ_j Σ_{x ∈ consEntries (rows j)} 1/recDenP`. -/
def rpTot (b : Basis (Fin 3) F K) (cells : List Noun) (rows : ℕ → RowN) (envs : ℕ → Env F) (N : ℕ) : K :=
  ∑ j ∈ Finset.range N, ((consEntries (hn (rows j))).map fun x =>
    (recDenP ((gE b (envs j)).chal chalRhoL) ((gE b (envs j)).chal chalGammaL)
      (entRecP (F := F) cells x))⁻¹).sum

open Classical in
/-- **The compute chip's 18 accumulator gates hold at the honest fill with the honest totals.**  Every row `j`
is honest (`Sem`, `AtRow`, OP3 hosted, `HonestFill`, outside the priced pole event), so its accumulator
terms are `Σ 1/den` over the consumed records (`termValX_honest` / `termValP_honest`), and the telescope
(`accGatesH_honest`) closes with the publics the totals `rxTot` / `rpTot`: no `termVal` hypothesis remains. -/
theorem accGatesH_honest_rows (b : Basis (Fin 3) F K) (N i : ℕ) (hi : i < N) (envs : ℕ → Env F)
    (cells : List Noun) (rows : ℕ → RowN) (fst lst : ℕ → F)
    (hrow : ∀ j < N, (rows j).Sem ∧ AtRow cells (rows j) (fst j) (lst j) (envs j) ∧
      ((rows j).op = 3 → (rows j).ftth = hdN (rows j).sf1 ∧ (rows j).fttt = tlN (rows j).sf1) ∧
      HonestFill b (envs j) ∧ NotBadRow (gE b (envs j)) (envs j))
    (h11 : (envs i).trace 11 = if i = 0 then 1 else 0)
    (h12 : (envs i).trace 12 = if i + 1 = N then 1 else 0)
    (haX : ∀ k : Fin 3, (envs i).trace (accX + k) =
      coord b (∑ j ∈ Finset.range i, termVal b (slotsX (F := F)) (envs j)) k)
    (haXn : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accX + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b (slotsX (F := F)) (envs j)) k)
    (haP : ∀ k : Fin 3, (envs i).trace (accP + k) =
      coord b (∑ j ∈ Finset.range i, termVal b (slotsP (F := F)) (envs j)) k)
    (haPn : i + 1 < N → ∀ k : Fin 3, (envs i).traceNext (accP + k) =
      coord b (∑ j ∈ Finset.range (i + 1), termVal b (slotsP (F := F)) (envs j)) k)
    (hpx : ∀ k : Fin 3, (envs i).pub (pubRhoX + k) = coord b (rxTot b cells rows envs N) k)
    (hpp : ∀ k : Fin 3, (envs i).pub (pubRhoP + k) = coord b (rpTot b cells rows envs N) k) :
    ∀ g ∈ (accGatesH : List (CoeffExpr ℚ)).map (mapC (fun q : ℚ => (q : F))),
      g.eval (envs i) = 0 :=
  accGatesH_honest b N i hi envs _ _ h11 h12
    (Finset.sum_congr rfl fun j hj => by
      obtain ⟨hs, hE, hh, hf, hn'⟩ := hrow j (Finset.mem_range.mp hj)
      exact termValX_honest cells (rows j) (fst j) (lst j) (envs j) b hs hE hh hf hn')
    (Finset.sum_congr rfl fun j hj => by
      obtain ⟨hs, hE, hh, hf, hn'⟩ := hrow j (Finset.mem_range.mp hj)
      exact termValP_honest cells (rows j) (fst j) (lst j) (envs j) b hs hE hh hf hn')
    haX haXn haP haPn hpx hpp

end Wire

end

end Nock.NockVMROM.Thm54.VclL.Handle
