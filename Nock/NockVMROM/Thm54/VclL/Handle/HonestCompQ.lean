/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestCompQ.lean

  Additive: a NEW module.

  With the handle coins `(γH′, ρH′) ∈ 𝕂′` (nonzero Im parts) the VS honest compute trace is not a trace of
  the `𝕂′` chip: the slot inverses (columns `43..51`, Im `70..78`) and the two accumulators (`52..57`, Im
  `79..84`) must be refilled over `𝕂′`.  `compTraceQ` is `compTrace` outside those blocks.

  * `slotIQ`: the honest `𝕂′` slot inverse `A′/D′` (read at the base columns and the `𝕂′` coins);
    `accSumXQ / accSumPQ`: the exclusive prefix sums of `Σ 1/recDen′`, `Σ 1/recDenP′` over `𝕂′`;
  * `slotGateQ_eq_evalMQ`: a `𝕂′` slot pair's value is the `K`-generic `evalMQ (slotGate S)` over `𝕂′`
    (`denQH_eq_evalMQ`), so the generic slot lemmas (`export_terms_row`, `path_terms_row`, a generic copy of
    `slotGates_honest_row`) apply at `L := 𝕂′`;
  * `rowQ_facts`: the three slot pairs vanish and the row's export / path terms are the sums of `1/den′`
    over the consumed records;
  * `walk_gates_Q`: the nine walk gates (the walk columns and the base columns are unchanged);
  * **`computeChipVCLHQ_honest_sat`**: `computeChipVCLHQ` accepts `compPolyQ` with its preprocessing.
    Hypotheses are `computeChipVCLH_honest_sat`'s (coin / public readings, `hat`), the `𝕂′` terminals
    `ρ₃ / ρ₄` published as Re / Im limbs of the honest totals, and `hnb`: the priced `𝕂′` pole event
    (`NotBadRow` over `𝕂′`, `poleRow_card` at `1/|𝕂′|`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestPinH
import Nock.NockVMROM.Thm54.VclL.Handle.HonestCompSatH
import Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestCompQ

open Nock Nock.Noun Nock.Walk Nock.Reified Module Nock.Framework Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.FiniteIO Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ Nock.NockVMROM.Thm54.VclL.Handle.ComputeSatHQ
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.TraceGen ComputeTable Nock.NockVMROM.Thm54.SemanticStrategy

noncomputable section

section Bridge
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- **The `𝕂′` compute-coin environment**: `γ` at the compute coin slot `0`, `ρ` at slot `3`; the trace
is given. -/
def eKq (γ ρ : 𝕂′) (tr : ℕ → 𝕂′) : Env 𝕂′ :=
  ⟨tr, fun _ => 0, fun j => if j = chalGammaL then γ else if j = chalRhoL then ρ else 0, fun _ => 0⟩

theorem eKq_gamma (γ ρ : 𝕂′) (tr : ℕ → 𝕂′) : (eKq δ γ ρ tr).chal chalGammaL = γ := by
  simp [eKq, chalGammaL]
theorem eKq_rho (γ ρ : 𝕂′) (tr : ℕ → 𝕂′) : (eKq δ γ ρ tr).chal chalRhoL = ρ := by
  simp [eKq, chalRhoL, chalGammaL]

variable (eK : Env K) (eF : Env F)

theorem rlcKeyQ_val_L : ∀ (r : List ℕ) (m : ℕ), Q.val δ (rlcKeyQ F δ m r) eK eF =
    rlcL (coinsCQ δ eK).gamma m (r.map fun i => algebraMap F 𝕂′ (eF.trace i))
  | [], m => by simp [rlcKeyQ, qconst_val, rlcL]
  | i :: r, m => by
    rw [rlcKeyQ, qadd_val, qmul_val, qpow_val, rlcKeyQ_val_L r (m + 1), qlift_val']
    have hg : Q.val δ (qγH F) eK eF = (coinsCQ δ eK).gamma := by
      rw [qγH, qvar_val]; rfl
    rw [hg, List.map_cons, rlcL]
    simp only [cc, CoeffExpr.eval]
    rw [← aMF]

theorem denQH_val_L (r : List ℕ) : Q.val δ (denQH F δ r) eK eF =
    (coinsCQ δ eK).pole + rlcL (coinsCQ δ eK).gamma 0 (r.map fun i => algebraMap F 𝕂′ (eF.trace i)) := by
  rw [denQH, qadd_val, rlcKeyQ_val_L]
  have hr' : Q.val δ (qρH F) eK eF = (coinsCQ δ eK).pole := by
    rw [qρH, qvar_val]; rfl
  rw [hr']

theorem denQH_eq_evalMQ (eK' : Env 𝕂′) (hγ : (coinsCQ δ eK).gamma = eK'.chal chalGammaL)
    (hρ : (coinsCQ δ eK).pole = eK'.chal chalRhoL) (r : List ℕ) :
    Q.val δ (denQH F δ r) eK eF = evalMQ (den (F := ℚ) r) eK' eF := by
  rw [denQH_val_L, den_eval, hγ, hρ]

/-- **A `𝕂′` slot pair's value is the `K`-generic slot gate evaluated over `𝕂′`.** -/
theorem slotGateQ_eq_evalMQ (S : SlotSpec ℚ) (eK' : Env 𝕂′)
    (hγ : (coinsCQ δ eK).gamma = eK'.chal chalGammaL) (hρ : (coinsCQ δ eK).pole = eK'.chal chalRhoL)
    (hinv : eK'.trace S.inv = invQ δ eK S) :
    Q.val δ (slotGateQ F δ (castSpec S)) eK eF = evalMQ (slotGate S) eK' eF := by
  rw [slotGateQ_val_spec, TeleC.slotGate_val, hinv]
  have hd : ∀ r : List ℕ, Q.val δ (denQH F δ r) eK eF = evalMQ (den (F := ℚ) r) eK' eF :=
    fun r => denQH_eq_evalMQ δ eK eF eK' hγ hρ r
  have e1 : (S.ents.map fun x => algebraMap F 𝕂′ (evalQ x.act eF) * Q.val δ (denQH F δ x.rcd) eK eF) =
      S.ents.map fun x => algebraMap F 𝕂′ (evalQ x.act eF) * evalMQ (den (F := ℚ) x.rcd) eK' eF :=
    List.map_congr_left fun x _ => by rw [hd]
  rw [e1]
  have e2 : pairDaQ δ eK eF S = pairDa S eK' eF := by
    unfold pairDaQ pairDa; cases S.pair with
    | none => rfl
    | some q => obtain ⟨fl, a, c⟩ := q; exact hd a
  have e3 : pairDbQ δ eK eF S = pairDb S eK' eF := by
    unfold pairDbQ pairDb; cases S.pair with
    | none => rfl
    | some q => obtain ⟨fl, a, c⟩ := q; exact hd c
  rw [e2, e3]

end Bridge

section Generic
variable {F L : Type} [Field F] [Field L] [Algebra F L]
variable (cells : List Noun) (r : RowN) (fst lst : F) (eF : Env F) (eK : Env L)

open Classical in
/-- **The three slot gates hold at the honest inverse, over any extension `L`** (the body of
`slotGates_honest_row`, with the environment abstract). -/
theorem slotGates_row_generic (hs : r.Sem) (hE : AtRow cells r fst lst eF)
    (hinv : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], eK.trace S.inv = slotAR eF eK S * (slotDR eF eK S)⁻¹)
    (hpole : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ x ∈ S.ents, evalQ x.act eF = 1 →
      evalMQ (den x.rcd) eK eF ≠ 0)
    (hpoleP : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], ∀ fl a b, S.pair = some (fl, a, b) →
      evalQ (cc fl) eF = 1 → evalMQ (den a) eK eF ≠ 0 ∧ evalMQ (den b) eK eF ≠ 0) :
    ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], evalMQ (slotGate S) eK eF = 0 := by
  have hle := op_le_ten r hs
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

end Generic

section Trace
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K) (cells : List Noun)
  (rows : ℕ → RowN) (N : ℕ) (chalV pubVal : ℕ → F) (ln cnt acc : ℕ → K)

local notation "𝕂′" => Quad (algebraMap F K δ)

/-- The `𝕂′` compute coins `(γH′, ρH′)` read off the challenge vector. -/
def eCQ : Env 𝕂′ := eKq δ (coinsCV b δ chalV).gamma (coinsCV b δ chalV).pole (fun _ => 0)

/-- **The honest `𝕂′` slot inverse** of chip row `r`: `A′ / D′` at the `𝕂′` coins. -/
def slotIQ (r : ℕ) (S : SlotSpec ℚ) : 𝕂′ :=
  slotAR (baseEnvC cells rows N chalV pubVal r) (eCQ δ b chalV) S *
    (slotDR (baseEnvC cells rows N chalV pubVal r) (eCQ δ b chalV) S)⁻¹

open Classical in
/-- Exclusive prefix sum of the export terms over `𝕂′`: `Σ 1/recDen′`. -/
def accSumXQ (r : ℕ) : 𝕂′ :=
  ∑ j ∈ Finset.range r, ((exportEntries (rows j)).map fun x =>
    (recDen (coinsCV b δ chalV).pole (coinsCV b δ chalV).gamma (entryRec (F := F) cells x))⁻¹).sum

open Classical in
def accSumPQ (r : ℕ) : 𝕂′ :=
  ∑ j ∈ Finset.range r, ((consEntries (hn (rows j))).map fun x =>
    (recDenP (coinsCV b δ chalV).pole (coinsCV b δ chalV).gamma (entRecP (F := F) cells x))⁻¹).sum

open Classical in
/-- **The honest `𝕂′` compute column function** (row `r`, column `c`; `0` for `c ≥ 85`): the VS column
function `compTrace` outside the handle blocks; the slot inverses `43..51` / `70..78` and the accumulators
`52..57` / `79..84` are the Re / Im coordinates of the `𝕂′` values. -/
def compTraceQ (r c : ℕ) : F :=
  if 43 ≤ c ∧ c < 46 then coordNA b (Quad.re _ (slotIQ δ b cells rows N chalV pubVal r slot0)) (c - 43)
  else if 46 ≤ c ∧ c < 49 then coordNA b (Quad.re _ (slotIQ δ b cells rows N chalV pubVal r slot1)) (c - 46)
  else if 49 ≤ c ∧ c < 52 then coordNA b (Quad.re _ (slotIQ δ b cells rows N chalV pubVal r slot2)) (c - 49)
  else if 52 ≤ c ∧ c < 55 then coordNA b (Quad.re _ (accSumXQ δ b cells rows chalV r)) (c - 52)
  else if 55 ≤ c ∧ c < 58 then coordNA b (Quad.re _ (accSumPQ δ b cells rows chalV r)) (c - 55)
  else if 70 ≤ c ∧ c < 73 then coordNA b (Quad.im _ (slotIQ δ b cells rows N chalV pubVal r slot0)) (c - 70)
  else if 73 ≤ c ∧ c < 76 then coordNA b (Quad.im _ (slotIQ δ b cells rows N chalV pubVal r slot1)) (c - 73)
  else if 76 ≤ c ∧ c < 79 then coordNA b (Quad.im _ (slotIQ δ b cells rows N chalV pubVal r slot2)) (c - 76)
  else if 79 ≤ c ∧ c < 82 then coordNA b (Quad.im _ (accSumXQ δ b cells rows chalV r)) (c - 79)
  else if 82 ≤ c ∧ c < 85 then coordNA b (Quad.im _ (accSumPQ δ b cells rows chalV r)) (c - 82)
  else compTrace b cells rows N chalV pubVal ln cnt acc r c

theorem compTraceQ_base (r c : ℕ) (hc : c < 43) :
    compTraceQ δ b cells rows N chalV pubVal ln cnt acc r c = colVal cells (rows r) (fstF r) (lstF N r) c := by
  unfold compTraceQ
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact compTrace_base b cells rows N chalV pubVal ln cnt acc r c hc

theorem compTraceQ_walk (r c : ℕ) (hc : 58 ≤ c ∧ c < 70) :
    compTraceQ δ b cells rows N chalV pubVal ln cnt acc r c = compTrace b cells rows N chalV pubVal ln cnt acc r c := by
  unfold compTraceQ
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem compTraceQ_zero (r c : ℕ) (hc : 85 ≤ c) :
    compTraceQ δ b cells rows N chalV pubVal ln cnt acc r c = 0 := by
  unfold compTraceQ
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact compTrace_zero b cells rows N chalV pubVal ln cnt acc r c (by omega)

theorem limbVal_compQ (r c0 : ℕ) (x : K)
    (h : ∀ k : Fin 3, compTraceQ δ b cells rows N chalV pubVal ln cnt acc r (c0 + k) = coordNA b x k) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) c0 = x := by
  refine limbVal_eq_of_coords b x _ c0 fun k => ?_
  rw [h k]; simp [coordNA, k.isLt]


section Poly
variable {n : ℕ} (nodes : Fin n → F)

/-- **The honest `𝕂′` compute trace polynomials**. -/
def compPolyQ (w : ℕ) : Fin w → F[X] := fun c =>
  Lagrange.interpolate Finset.univ nodes (fun i : Fin n =>
    compTraceQ δ b cells rows N chalV pubVal ln cnt acc (i : ℕ) (c : ℕ))

theorem compPolyQ_eval (hinj : Function.Injective nodes) {w : ℕ} (c : Fin w) (i : Fin n) :
    (compPolyQ δ b cells rows N chalV pubVal ln cnt acc nodes w c).eval (nodes i) =
      compTraceQ δ b cells rows N chalV pubVal ln cnt acc (i : ℕ) (c : ℕ) :=
  Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)

theorem compPolyQ_env_trace (hinj : Function.Injective nodes) {w : ℕ} (hw : 85 ≤ w) (ω : F) (i : Fin n)
    (c : ℕ) :
    (Reify.envOfTrace (compPolyQ δ b cells rows N chalV pubVal ln cnt acc nodes w) ω (nodes i) chalV pubVal).trace c
      = compTraceQ δ b cells rows N chalV pubVal ln cnt acc (i : ℕ) c := by
  simp only [Reify.envOfTrace]
  by_cases hc : c < w
  · rw [dif_pos hc]; exact compPolyQ_eval δ b cells rows N chalV pubVal ln cnt acc nodes hinj ⟨c, hc⟩ i
  · rw [dif_neg hc, compTraceQ_zero δ b cells rows N chalV pubVal ln cnt acc _ _ (by omega)]

theorem compPolyQ_env_next (hinj : Function.Injective nodes) {w : ℕ} (hw : 85 ≤ w) (ω : F) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) (hadj : nodes ⟨(i : ℕ) + 1, hi⟩ = ω * nodes i) (c : ℕ) :
    (Reify.envOfTrace (compPolyQ δ b cells rows N chalV pubVal ln cnt acc nodes w) ω (nodes i) chalV pubVal).traceNext c
      = compTraceQ δ b cells rows N chalV pubVal ln cnt acc ((i : ℕ) + 1) c := by
  simp only [Reify.envOfTrace]
  by_cases hc : c < w
  · rw [dif_pos hc, ← hadj]
    exact compPolyQ_eval δ b cells rows N chalV pubVal ln cnt acc nodes hinj ⟨c, hc⟩ ⟨(i : ℕ) + 1, hi⟩
  · rw [dif_neg hc, compTraceQ_zero δ b cells rows N chalV pubVal ln cnt acc _ _ (by omega)]

theorem compPolyQ_first (w : ℕ) (hw : 11 < w) :
    compPolyQ δ b cells rows N chalV pubVal ln cnt acc nodes w ⟨11, hw⟩ = firstRowMask nodes := by
  unfold compPolyQ firstRowMask
  congr 1

theorem compPolyQ_last (hn : 0 < n) (hN : N = n) (w : ℕ) (hw : 12 < w) :
    compPolyQ δ b cells rows N chalV pubVal ln cnt acc nodes w ⟨12, hw⟩ = lastRowMask hn nodes := by
  unfold compPolyQ lastRowMask
  congr 1
  funext i
  show compTraceQ δ b cells rows N chalV pubVal ln cnt acc (i : ℕ) 12 = _
  rw [compTraceQ_base δ b cells rows N chalV pubVal ln cnt acc _ 12 (by omega)]
  have : (i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩) ↔ (i : ℕ) + 1 = n := by
    constructor
    · intro h; subst h; simp; omega
    · intro h; apply Fin.ext; simp; omega
  simp only [colVal, lstF, hN]
  simp only [show ¬ (12 ≤ 10) from by omega, if_false]
  simp only [this]

end Poly

theorem limbQ_inv0 (r : ℕ) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) 43 = Quad.re _ (slotIQ δ b cells rows N chalV pubVal r slot0) := by
  refine limbVal_compQ δ b cells rows N chalV pubVal ln cnt acc r 43 _ fun k => ?_
  have := k.isLt
  simp only [compTraceQ]
  rw [if_pos (by omega)]
  congr 1; omega

theorem limbQ_inv1 (r : ℕ) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) 46 = Quad.re _ (slotIQ δ b cells rows N chalV pubVal r slot1) := by
  refine limbVal_compQ δ b cells rows N chalV pubVal ln cnt acc r 46 _ fun k => ?_
  have := k.isLt
  simp only [compTraceQ]
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limbQ_inv2 (r : ℕ) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) 49 = Quad.re _ (slotIQ δ b cells rows N chalV pubVal r slot2) := by
  refine limbVal_compQ δ b cells rows N chalV pubVal ln cnt acc r 49 _ fun k => ?_
  have := k.isLt
  simp only [compTraceQ]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limbQ_accX (r : ℕ) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) 52 = Quad.re _ (accSumXQ δ b cells rows chalV r) := by
  refine limbVal_compQ δ b cells rows N chalV pubVal ln cnt acc r 52 _ fun k => ?_
  have := k.isLt
  simp only [compTraceQ]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limbQ_accP (r : ℕ) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) 55 = Quad.re _ (accSumPQ δ b cells rows chalV r) := by
  refine limbVal_compQ δ b cells rows N chalV pubVal ln cnt acc r 55 _ fun k => ?_
  have := k.isLt
  simp only [compTraceQ]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limbQ_im0 (r : ℕ) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) 70 = Quad.im _ (slotIQ δ b cells rows N chalV pubVal r slot0) := by
  refine limbVal_compQ δ b cells rows N chalV pubVal ln cnt acc r 70 _ fun k => ?_
  have := k.isLt
  simp only [compTraceQ]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limbQ_im1 (r : ℕ) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) 73 = Quad.im _ (slotIQ δ b cells rows N chalV pubVal r slot1) := by
  refine limbVal_compQ δ b cells rows N chalV pubVal ln cnt acc r 73 _ fun k => ?_
  have := k.isLt
  simp only [compTraceQ]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limbQ_im2 (r : ℕ) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) 76 = Quad.im _ (slotIQ δ b cells rows N chalV pubVal r slot2) := by
  refine limbVal_compQ δ b cells rows N chalV pubVal ln cnt acc r 76 _ fun k => ?_
  have := k.isLt
  simp only [compTraceQ]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limbQ_accXIm (r : ℕ) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) 79 = Quad.im _ (accSumXQ δ b cells rows chalV r) := by
  refine limbVal_compQ δ b cells rows N chalV pubVal ln cnt acc r 79 _ fun k => ?_
  have := k.isLt
  simp only [compTraceQ]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem limbQ_accPIm (r : ℕ) :
    limbVal b (compTraceQ δ b cells rows N chalV pubVal ln cnt acc r) 82 = Quad.im _ (accSumPQ δ b cells rows chalV r) := by
  refine limbVal_compQ δ b cells rows N chalV pubVal ln cnt acc r 82 _ fun k => ?_
  have := k.isLt
  simp only [compTraceQ]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

/-- The `𝕂′` environment of row `j`: the compute coins and the three honest slot inverses. -/
def eKI (j : ℕ) : Env 𝕂′ :=
  eKq δ (coinsCV b δ chalV).gamma (coinsCV b δ chalV).pole (fun i =>
    if i = inv0 then slotIQ δ b cells rows N chalV pubVal j slot0
    else if i = inv1 then slotIQ δ b cells rows N chalV pubVal j slot1
    else if i = inv2 then slotIQ δ b cells rows N chalV pubVal j slot2 else 0)

theorem eKI_trace (j : ℕ) (S : SlotSpec ℚ) (hS : S ∈ [slot0 (F := ℚ), slot1, slot2]) :
    (eKI δ b cells rows N chalV pubVal j).trace S.inv = slotIQ δ b cells rows N chalV pubVal j S := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl <;> simp [eKI, eKq, slot0, slot1, slot2, inv0, inv1, inv2]

theorem eKI_gamma (j : ℕ) : (eKI δ b cells rows N chalV pubVal j).chal chalGammaL = (coinsCV b δ chalV).gamma :=
  eKq_gamma δ _ _ _
theorem eKI_rho (j : ℕ) : (eKI δ b cells rows N chalV pubVal j).chal chalRhoL = (coinsCV b δ chalV).pole :=
  eKq_rho δ _ _ _

variable (j : ℕ) (E : Env F)

/-- **The row facts at the honest `𝕂′` fill**: the three slot pairs vanish and the row's export / path
terms are the sums of `1/recDen′` over the consumed records. -/
theorem rowQ_facts (hEt : ∀ c, E.trace c = compTraceQ δ b cells rows N chalV pubVal ln cnt acc j c)
    (hch : E.chal = chalV) (hs : (rows j).Sem)
    (hhost : (rows j).op = 3 → (rows j).ftth = hdN (rows j).sf1 ∧ (rows j).fttt = tlN (rows j).sf1)
    (hnb : NotBadRow (eCQ δ b chalV) (baseEnvC cells rows N chalV pubVal j)) :
    (∀ S ∈ [slot0 (F := ℚ), slot1, slot2],
      Q.val δ (slotGateQ F δ (castSpec S)) (Compute.TowerD.gatherEnv b E) E = 0) ∧
    termXQ δ b E = ((exportEntries (rows j)).map fun x =>
      (recDen (coinsCV b δ chalV).pole (coinsCV b δ chalV).gamma (entryRec (F := F) cells x))⁻¹).sum ∧
    termPQ δ b E = ((consEntries (hn (rows j))).map fun x =>
      (recDenP (coinsCV b δ chalV).pole (coinsCV b δ chalV).gamma (entRecP (F := F) cells x))⁻¹).sum := by
  classical
  have hAt : AtRow cells (rows j) (fstF j) (lstF N j) E := fun c hc => by
    rw [hEt c, compTraceQ_base δ b cells rows N chalV pubVal ln cnt acc j c (by omega)]
  have hbase : ∀ c < 43, (baseEnvC cells rows N chalV pubVal j).trace c = E.trace c := fun c hc => by
    rw [hAt c (by omega)]; rfl
  have hNB : NotBadRow (eKI δ b cells rows N chalV pubVal j) E :=
    notBadRow_congr (eCQ δ b chalV) (eKI δ b cells rows N chalV pubVal j)
      (baseEnvC cells rows N chalV pubVal j) E hbase
      (by rw [eKI_gamma]; exact eKq_gamma δ _ _ _) (by rw [eKI_rho]; exact eKq_rho δ _ _ _) hnb
  have hinvI : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], (eKI δ b cells rows N chalV pubVal j).trace S.inv =
      slotAR E (eKI δ b cells rows N chalV pubVal j) S * (slotDR E (eKI δ b cells rows N chalV pubVal j) S)⁻¹ := by
    intro S hS
    rw [eKI_trace δ b cells rows N chalV pubVal j S hS]
    unfold slotIQ
    have := slotAD_congr S hS (eCQ δ b chalV) (eKI δ b cells rows N chalV pubVal j)
      (baseEnvC cells rows N chalV pubVal j) E hbase
      (by rw [eKI_gamma]; exact eKq_gamma δ _ _ _) (by rw [eKI_rho]; exact eKq_rho δ _ _ _)
    rw [this.1, this.2]
  have hpole := (poles_of_notBad _ _ hNB).1
  have hpoleP := (poles_of_notBad _ _ hNB).2
  have hgate := slotGates_row_generic cells (rows j) (fstF j) (lstF N j) E (eKI δ b cells rows N chalV pubVal j)
    hs hAt hinvI hpole hpoleP
  have hET : E.trace = compTraceQ δ b cells rows N chalV pubVal ln cnt acc j := funext hEt
  have hinvQ : ∀ S ∈ [slot0 (F := ℚ), slot1, slot2], invQ δ (Compute.TowerD.gatherEnv b E) S =
      (eKI δ b cells rows N chalV pubVal j).trace S.inv := by
    intro S hS
    rw [eKI_trace δ b cells rows N chalV pubVal j S hS]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    have hI : ∀ (c0 c1 : ℕ) (x : 𝕂′), limbVal b E.trace c0 = Quad.re _ x → limbVal b E.trace c1 = Quad.im _ x →
        Quad.mk _ (limbVal b E.trace c0) (limbVal b E.trace c1) = x := fun c0 c1 x h0 h1 => by
      rw [h0, h1, Quad.mk_re_im]
    rcases hS with rfl | rfl | rfl
    · have e : imOf 43 = 70 := by simp [imOf, inv0, invIm0]
      show Quad.mk _ (limbVal b E.trace 43) (limbVal b E.trace (imOf 43)) = _
      rw [e]; exact hI _ _ _ (by rw [hET]; exact limbQ_inv0 δ b cells rows N chalV pubVal ln cnt acc j)
        (by rw [hET]; exact limbQ_im0 δ b cells rows N chalV pubVal ln cnt acc j)
    · have e : imOf 46 = 73 := by simp [imOf, inv0, inv1, invIm0, invIm1]
      show Quad.mk _ (limbVal b E.trace 46) (limbVal b E.trace (imOf 46)) = _
      rw [e]; exact hI _ _ _ (by rw [hET]; exact limbQ_inv1 δ b cells rows N chalV pubVal ln cnt acc j)
        (by rw [hET]; exact limbQ_im1 δ b cells rows N chalV pubVal ln cnt acc j)
    · have e : imOf 49 = 76 := by simp [imOf, inv0, inv1, inv2, invIm0, invIm1, invIm2]
      show Quad.mk _ (limbVal b E.trace 49) (limbVal b E.trace (imOf 49)) = _
      rw [e]; exact hI _ _ _ (by rw [hET]; exact limbQ_inv2 δ b cells rows N chalV pubVal ln cnt acc j)
        (by rw [hET]; exact limbQ_im2 δ b cells rows N chalV pubVal ln cnt acc j)
  have hcoin : ∀ x : 𝕂′, True := fun _ => trivial
  have hγ : (coinsCQ δ (Compute.TowerD.gatherEnv b E)).gamma = (eKI δ b cells rows N chalV pubVal j).chal chalGammaL := by
    rw [eKI_gamma]; simp [coinsCQ, coinsCV, Compute.TowerD.gatherEnv, hch]
  have hρ : (coinsCQ δ (Compute.TowerD.gatherEnv b E)).pole = (eKI δ b cells rows N chalV pubVal j).chal chalRhoL := by
    rw [eKI_rho]; simp [coinsCQ, coinsCV, Compute.TowerD.gatherEnv, hch]
  refine ⟨fun S hS => ?_, ?_, ?_⟩
  · rw [slotGateQ_eq_evalMQ δ (Compute.TowerD.gatherEnv b E) E S _ hγ hρ (hinvQ S hS).symm]
    exact hgate S hS
  · have h := export_terms_row cells (rows j) (fstF j) (lstF N j) E (eKI δ b cells rows N chalV pubVal j) hs hAt hhost
      hinvI hpole hpoleP
    rw [eKI_gamma, eKI_rho] at h
    rw [← h, termXQ]
    refine congrArg List.sum (List.map_congr_left fun S hS => ?_)
    rw [hinvQ S hS, aMF]
  · have h := path_terms_row cells (rows j) (fstF j) (lstF N j) E (eKI δ b cells rows N chalV pubVal j) hs hAt hhost
      hinvI hpole hpoleP
    rw [eKI_gamma, eKI_rho] at h
    rw [← h, termPQ]
    refine congrArg List.sum (List.map_congr_left fun S hS => ?_)
    rw [hinvQ S hS, aMF]

end Trace

section WalkQ
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  [Field Kg] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The nine compute-walk gates hold at the real `𝕂′` chip environment**: the walk gates read only the
base columns `< 43` and the walk columns `58..69`, where `compTraceQ` is `compTrace`. -/
theorem walk_gates_Q
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (cells : List Noun) (α γ : K) (hord : (bfsForest [airReorder t]).length ≤ orderOf α)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
    (hα : limbVal b chalV chalAlphaW = α) (hγ : limbVal b chalV chalGammaW = γ)
    (hpIC : limbVal b pubVal pubIC = α) (hpS : limbVal b pubVal pubSeed = wkSeed (F := F) (bfsForest [airReorder t]) α γ cells)
    (hpO : limbVal b pubVal pubOut = 0)
    (E : Env F) (r : ℕ) (hr : r < (bfsForest [airReorder t]).length)
    (hE0 : ∀ c, E.trace c = compTraceQ δ b cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
      chalV pubVal (wkLn α) (wkCnt (bfsForest [airReorder t]) α)
      (wkAcc (F := F) (bfsForest [airReorder t]) α γ cells) r c)
    (hEn : r + 1 < (bfsForest [airReorder t]).length → ∀ c, E.traceNext c =
      compTraceQ δ b cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
      chalV pubVal (wkLn α) (wkCnt (bfsForest [airReorder t]) α)
      (wkAcc (F := F) (bfsForest [airReorder t]) α γ cells) (r + 1) c)
    (hch : E.chal = chalV) (hpb : E.pub = pubVal) :
    ∀ g ∈ (walkGates : List (MixedExpr ℚ)), evalMQ g (gE b E) E = 0 := by
  intro g hg
  set W := bfsForest [airReorder t] with hW
  let tr : ℕ → ℕ → F := fun r' c => compTrace b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
    (wkAcc (F := F) W α γ cells) r' c
  let E1 : Env F := ⟨tr r, fun c => if r + 1 < W.length then tr (r + 1) c else E.traceNext c, chalV, pubVal⟩
  have h1 := walk_gates_real h cells α γ hord b chalV pubVal hα hγ hpIC hpS hpO E1 r hr (fun c => rfl)
    (fun hlt c => by
      show (if r + 1 < W.length then tr (r + 1) c else E.traceNext c) = _
      rw [if_pos hlt]) rfl rfl g hg
  have hw : ∀ (r' c : ℕ), 58 ≤ c → c < 70 →
      compTraceQ δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
        (wkAcc (F := F) W α γ cells) r' c = tr r' c := fun r' c h1 h2 =>
    compTraceQ_walk δ b cells (wRows W) W.length chalV pubVal _ _ _ r' c ⟨h1, h2⟩
  have hbs : ∀ (r' c : ℕ), c < 43 →
      compTraceQ δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
        (wkAcc (F := F) W α γ cells) r' c = tr r' c := fun r' c h1 => by
    rw [compTraceQ_base δ b cells (wRows W) W.length chalV pubVal _ _ _ r' c h1]
    exact (compTrace_base b cells (wRows W) W.length chalV pubVal _ _ _ r' c h1).symm
  have hK : ∀ p, wkOK p = true → envRd (gE b E) p = envRd (gE b E1) p := by
    rintro ⟨k, c⟩ hp
    cases k
    · simp only [wkOK, Bool.or_eq_true, beq_iff_eq] at hp
      have hc : 58 ≤ c ∧ c + 2 < 70 := by
        rcases hp with ((hc | hc) | hc) | hc <;> subst hc <;> decide
      simp only [envRd, gE, Compute.TowerD.gatherEnv, limbVal]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk := k.isLt
      show E.trace (c + k) • _ = tr r (c + k) • _
      rw [hE0, hw _ _ (by omega) (by omega)]
    · simp only [wkOK, Bool.or_eq_true, beq_iff_eq] at hp
      have hc : 58 ≤ c ∧ c + 2 < 70 := by
        rcases hp with (hc | hc) | hc <;> subst hc <;> decide
      simp only [envRd, gE, Compute.TowerD.gatherEnv, limbVal]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk := k.isLt
      show E.traceNext (c + k) • _ = (if r + 1 < W.length then tr (r + 1) (c + k) else E.traceNext (c + k)) • _
      by_cases hlt : r + 1 < W.length
      · rw [if_pos hlt, hEn hlt, hw _ _ (by omega) (by omega)]
      · rw [if_neg hlt]
    · simp only [envRd, gE, Compute.TowerD.gatherEnv, hch]
      rfl
    · simp only [envRd, gE, Compute.TowerD.gatherEnv, hpb]
      rfl
  have hF : ∀ p, wfOK p = true → envRd E p = envRd E1 p := by
    rintro ⟨k, c⟩ hp
    cases k
    · simp only [wfOK, decide_eq_true_eq] at hp
      show E.trace c = tr r c
      rw [hE0, hbs _ _ hp]
    · simp only [wfOK, decide_eq_true_eq] at hp
      show E.traceNext c = if r + 1 < W.length then tr (r + 1) c else E.traceNext c
      by_cases hlt : r + 1 < W.length
      · rw [if_pos hlt, hEn hlt, hbs _ _ hp]
      · rw [if_neg hlt]
    · simp [wfOK] at hp
    · simp [wfOK] at hp
  rw [← h1]
  exact evalMQ_congr_rds g _ _ _ _ (fun p hp => hK p (walk_readsK g hg p hp))
    (fun p hp => hF p (walk_readsF g hg p hp))

end WalkQ

section Main
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]
  [Field Kg] (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

open Classical in
/-- **The `𝕂′` compute chip accepts the honest `𝕂′` trace** (`compPolyQ`).  Hypotheses as
`computeChipVCLH_honest_sat`, read at the `𝕂′` coins and with the `𝕂′` terminals `ρ₃ / ρ₄` published as
Re / Im limbs (`hρX hρXi hρP hρPi`, the totals `accSumXQ n / accSumPQ n`); `hnb` is the priced pole event at
`1/|𝕂′|` (`NotBadRow` over `𝕂′`). -/
theorem computeChipVCLHQ_honest_sat
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (cells : List Noun) (α γ : K) (hord : (bfsForest [airReorder t]).length ≤ orderOf α)
    {hh n : ℕ} (hn : 0 < n) (hN : n = (bfsForest [airReorder t]).length)
    (nodes : Fin n → F) (hinj : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 hh)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hα : limbVal b chalV chalAlphaW = α) (hγ : limbVal b chalV chalGammaW = γ)
    (hpIC : limbVal b pubVal pubIC = α)
    (hpS : limbVal b pubVal pubSeed = wkSeed (F := F) (bfsForest [airReorder t]) α γ cells)
    (hpO : limbVal b pubVal pubOut = 0)
    (hpub6 : ∀ i < 6, pubVal i = pubVec cells (rowAtW (bfsForest [airReorder t]) 1) i)
    (hρX : ∀ k : Fin 3, pubVal (pubRhoX + k) =
      coord b (Quad.re _ (accSumXQ δ b cells (wRows (bfsForest [airReorder t])) chalV n)) k)
    (hρXi : ∀ k : Fin 3, pubVal (pubRhoXIm + k) =
      coord b (Quad.im _ (accSumXQ δ b cells (wRows (bfsForest [airReorder t])) chalV n)) k)
    (hρP : ∀ k : Fin 3, pubVal (pubRhoP + k) =
      coord b (Quad.re _ (accSumPQ δ b cells (wRows (bfsForest [airReorder t])) chalV n)) k)
    (hρPi : ∀ k : Fin 3, pubVal (pubRhoPIm + k) =
      coord b (Quad.im _ (accSumPQ δ b cells (wRows (bfsForest [airReorder t])) chalV n)) k)
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (hnb : ∀ r < n, NotBadRow (eCQ δ b chalV)
      (baseEnvC cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length chalV pubVal r)) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHQ hn nodes b δ chalV pubVal orbit)
      (compPolyQ δ b cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length chalV pubVal
        (wkLn α) (wkCnt (bfsForest [airReorder t]) α) (wkAcc (F := F) (bfsForest [airReorder t]) α γ cells) nodes
        (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).rap.w) := by
  set W := bfsForest [airReorder t] with hW
  set P := compPolyQ δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
    (wkAcc (F := F) W α γ cells) nodes (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).rap.w with hP
  have hw85 : 85 ≤ (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).rap.w := by
    rw [computeChipVCLHQ_width]
  have hE0 : ∀ i : Fin n, ∀ c, (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal).trace c =
      compTraceQ δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α) (wkAcc (F := F) W α γ cells)
        (i : ℕ) c :=
    fun i c => compPolyQ_env_trace δ b cells (wRows W) W.length chalV pubVal _ _ _ nodes hinj hw85 orbit.ω i c
  have hEn : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), ∀ c,
      (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal).traceNext c =
      compTraceQ δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α) (wkAcc (F := F) W α γ cells)
        ((i : ℕ) + 1) c :=
    fun i hi c => compPolyQ_env_next δ b cells (wRows W) W.length chalV pubVal _ _ _ nodes hinj hw85 orbit.ω i hi
      (hadj i hi) c
  have hlen : W.length = n := hN.symm
  have hrowSem : ∀ r (hr : r < W.length), (wRows W r).Sem := by
    intro r hr
    have hg := label_mem_bfsRows W hW r hr
    unfold wRows; rw [rowAtW_eq W r hr]
    exact rowOfSkelH_sem _ (run_rows_sem hrun _ hg)
  have hrowHost : ∀ r (hr : r < W.length), (wRows W r).op = 3 →
      (wRows W r).ftth = hdN (wRows W r).sf1 ∧ (wRows W r).fttt = tlN (wRows W r).sf1 := by
    intro r hr; unfold wRows; rw [rowAtW_eq W r hr]; exact rowOfSkelH_hosted _
  let envs : ℕ → Env F := fun j =>
    if h : j < n then Reify.envOfTrace P orbit.ω (nodes ⟨j, h⟩) chalV pubVal
    else ⟨fun _ => 0, fun _ => 0, chalV, pubVal⟩
  have henv : ∀ i : Fin n, envs i = Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal := by
    intro i; simp [envs, i.isLt]
  have henv_chal : ∀ j, (envs j).chal = chalV := by
    intro j; by_cases hj : j < n <;> simp [envs, hj, Reify.envOfTrace]
  have henv_pub : ∀ j, (envs j).pub = pubVal := by
    intro j; by_cases hj : j < n <;> simp [envs, hj, Reify.envOfTrace]
  have henvT : ∀ j (hj : j < n) c, (envs j).trace c =
      compTraceQ δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α) (wkAcc (F := F) W α γ cells) j c := by
    intro j hj c; rw [henv ⟨j, hj⟩]; exact hE0 ⟨j, hj⟩ c
  have henvN : ∀ j (hj : j + 1 < n) c, (envs j).traceNext c =
      compTraceQ δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α) (wkAcc (F := F) W α γ cells) (j + 1) c := by
    intro j hj c
    have hj' : j < n := by omega
    rw [henv ⟨j, hj'⟩]; exact hEn ⟨j, hj'⟩ hj c
  have hF : ∀ j (hj : j < n), _ := fun j hj =>
    rowQ_facts δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α) (wkAcc (F := F) W α γ cells) j (envs j)
      (henvT j hj) (henv_chal j) (hrowSem j (by omega)) (hrowHost j (by omega)) (hnb j hj)
  -- the prefix sums of the row terms
  have hSumX : ∀ i ≤ n, Quad.mk _ (∑ j ∈ Finset.range i, termVal b (slotsX (F := F)) (envs j))
      (∑ j ∈ Finset.range i, termVal b (slotsXIm (F := F)) (envs j)) =
      accSumXQ δ b cells (wRows W) chalV i := by
    intro i hi
    unfold accSumXQ
    rw [← mk_fsum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hi
    rw [← (hF j hj').2.1, termXQ_eq]
    rfl
  have hSumP : ∀ i ≤ n, Quad.mk _ (∑ j ∈ Finset.range i, termVal b (slotsP (F := F)) (envs j))
      (∑ j ∈ Finset.range i, termVal b (slotsPIm (F := F)) (envs j)) =
      accSumPQ δ b cells (wRows W) chalV i := by
    intro i hi
    unfold accSumPQ
    rw [← mk_fsum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hi
    rw [← (hF j hj').2.2, termPQ_eq]
    rfl
  have hbind : (computeChipVCLHQ hn nodes b δ chalV pubVal orbit).BindsPreprocessing P := by
    intro j
    fin_cases j
    · exact compPolyQ_first δ b cells (wRows W) W.length chalV pubVal _ _ _ nodes _ (by omega)
    · exact compPolyQ_last δ b cells (wRows W) W.length chalV pubVal _ _ _ nodes hn hlen _ (by omega)
  have h11 : ∀ j (hj : j < n), (envs j).trace 11 = if j = 0 then 1 else 0 := by
    intro j hj
    rw [henvT j hj, compTraceQ_base δ b cells (wRows W) W.length chalV pubVal _ _ _ j 11 (by omega)]
    simp [colVal, fstF]
  have h12 : ∀ j (hj : j < n), (envs j).trace 12 = if j + 1 = W.length then 1 else 0 := by
    intro j hj
    rw [henvT j hj, compTraceQ_base δ b cells (wRows W) W.length chalV pubVal _ _ _ j 12 (by omega)]
    simp [colVal, lstF]
  have hcoord : ∀ (i : ℕ) (base : ℕ) (x : K)
      (hl : limbVal b (compTraceQ δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
        (wkAcc (F := F) W α γ cells) i) base = x) (k : Fin 3),
      compTraceQ δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
        (wkAcc (F := F) W α γ cells) i (base + k) = coord b x k := by
    intro i base x hl k
    have := coord_limbVal b (compTraceQ δ b cells (wRows W) W.length chalV pubVal (wkLn α) (wkCnt W α)
        (wkAcc (F := F) W α γ cells) i) base k
    rw [hl] at this; exact this.symm
  refine (computeChipVCLHQ_sat_iff hn nodes b δ chalV pubVal orbit P).mpr ⟨hbind, fun x hx g hg => ?_⟩
  obtain ⟨i, rfl⟩ := (mem_rowNodeSet_iff nodes x).mp hx
  have hiW : (i : ℕ) < W.length := by omega
  have hgm := label_mem_bfsRows W hW (i : ℕ) hiW
  have harith : ∀ g ∈ (arithGates : List (CoeffExpr ℚ)) ++ (eqGates : List (EqG ℚ)).map EqG.gate,
      evalQ g (Reify.envOfTrace P orbit.ω (nodes i) chalV pubVal) = 0 := by
    intro g hmem
    have hroot : (fstF (i : ℕ) : F) = 0 ∨ ((rowOfSkelH (W[(i : ℕ)]'hiW).label.skel).s = (rowAtW W 1).s ∧
        (rowOfSkelH (W[(i : ℕ)]'hiW).label.skel).f = (rowAtW W 1).f ∧
        (rowOfSkelH (W[(i : ℕ)]'hiW).label.skel).e = (rowAtW W 1).e) := by
      by_cases h0 : (i : ℕ) = 0
      · right
        have hthis : rowOfSkelH (W[(i : ℕ)]'hiW).label.skel = rowAtW W 1 := by
          rw [← rowAtW_eq W (i : ℕ) hiW, h0]
        rw [hthis]; exact ⟨rfl, rfl, rfl⟩
      · left; simp [fstF, h0]
    have hb := honest_row_base_gatesH hrun hgm cells (fstF (i : ℕ)) (lstF W.length (i : ℕ)) (rowAtW W 1)
      (hat _ hgm) hroot g hmem
    rw [← rowAtW_eq W (i : ℕ) hiW] at hb
    rw [eval_mapC_cast] at hb
    rw [← hb]
    refine evalQ_congr_rds g _ _ (fun p hp => ?_)
    have hp' := arith_reads g hmem p hp
    rcases p with ⟨k, c⟩
    cases k
    · simp only [bsOK, decide_eq_true_eq] at hp'
      simp only [envRd, hEnv]
      rw [hE0 i c, compTraceQ_base δ b cells (wRows W) W.length chalV pubVal _ _ _ (i : ℕ) c (by omega)]
      rfl
    · simp [bsOK] at hp'
    · simp [bsOK] at hp'
    · simp only [bsOK, decide_eq_true_eq] at hp'
      simp only [envRd, hEnv, Reify.envOfTrace]
      exact hpub6 c hp'
  have hFi := hF (i : ℕ) i.isLt
  simp only [gatesHQ, List.mem_append, List.mem_flatMap] at hg
  rcases hg with (hg | ⟨q, hq, hg⟩) | ⟨m, hm, hg⟩
  · obtain ⟨t', ht, rfl⟩ := List.mem_map.mp hg
    rw [eval_mapC_cast]
    simp only [baseGatesHQ, List.mem_append] at ht
    rcases ht with (ht | ht) | ht
    · exact harith t' (List.mem_append_left _ ht)
    · simp only [accGatesHQ, List.mem_append] at ht
      have reX : ∀ i' ≤ n, ∑ j ∈ Finset.range i', termVal b (slotsX (F := F)) (envs j) =
          Quad.re _ (accSumXQ δ b cells (wRows W) chalV i') := fun i' hi' => by rw [← hSumX i' hi', Quad.re_mk]
      have imX : ∀ i' ≤ n, ∑ j ∈ Finset.range i', termVal b (slotsXIm (F := F)) (envs j) =
          Quad.im _ (accSumXQ δ b cells (wRows W) chalV i') := fun i' hi' => by rw [← hSumX i' hi', Quad.im_mk]
      have reP : ∀ i' ≤ n, ∑ j ∈ Finset.range i', termVal b (slotsP (F := F)) (envs j) =
          Quad.re _ (accSumPQ δ b cells (wRows W) chalV i') := fun i' hi' => by rw [← hSumP i' hi', Quad.re_mk]
      have imP : ∀ i' ≤ n, ∑ j ∈ Finset.range i', termVal b (slotsPIm (F := F)) (envs j) =
          Quad.im _ (accSumPQ δ b cells (wRows W) chalV i') := fun i' hi' => by rw [← hSumP i' hi', Quad.im_mk]
      have hin : (i : ℕ) < n := i.isLt
      rcases ht with (ht | ht) | ht
      · have hr := accGatesH_honest b W.length (i : ℕ) hiW envs
          (Quad.re _ (accSumXQ δ b cells (wRows W) chalV n)) (Quad.re _ (accSumPQ δ b cells (wRows W) chalV n))
          (h11 _ hin) (h12 _ hin) (by rw [hlen]; exact reX n le_rfl) (by rw [hlen]; exact reP n le_rfl)
          (fun k => by
            rw [henvT _ hin, reX _ hin.le]
            exact hcoord (i : ℕ) accX _ (limbQ_accX δ b cells (wRows W) W.length chalV pubVal _ _ _ _) k)
          (fun hlt k => by
            rw [henvN _ (by omega), reX _ (by omega)]
            exact hcoord ((i : ℕ) + 1) accX _ (limbQ_accX δ b cells (wRows W) W.length chalV pubVal _ _ _ _) k)
          (fun k => by
            rw [henvT _ hin, reP _ hin.le]
            exact hcoord (i : ℕ) accP _ (limbQ_accP δ b cells (wRows W) W.length chalV pubVal _ _ _ _) k)
          (fun hlt k => by
            rw [henvN _ (by omega), reP _ (by omega)]
            exact hcoord ((i : ℕ) + 1) accP _ (limbQ_accP δ b cells (wRows W) W.length chalV pubVal _ _ _ _) k)
          (fun k => by rw [henv_pub]; exact hρX k) (fun k => by rw [henv_pub]; exact hρP k)
        have := hr (mapC (fun q : ℚ => (q : F)) t') (List.mem_map_of_mem ht)
        rwa [eval_mapC_cast, henv i] at this
      · have hmem : mapC (fun q : ℚ => (q : F)) t' ∈ accGates 3 (slotsXIm (F := F)) accXIm pubRhoXIm := by
          rw [slotsXIm, ← accGates_map]; exact List.mem_map_of_mem ht
        have hr := accGates_prefixK b (slotsXIm (F := F)) accXIm pubRhoXIm W.length (i : ℕ) hiW envs
          (Quad.im _ (accSumXQ δ b cells (wRows W) chalV n)) (h11 _ hin) (h12 _ hin)
          (fun k => by
            rw [henvT _ hin, imX _ hin.le]
            exact hcoord (i : ℕ) accXIm _ (limbQ_accXIm δ b cells (wRows W) W.length chalV pubVal _ _ _ _) k)
          (fun hlt k => by
            rw [henvN _ (by omega), imX _ (by omega)]
            exact hcoord ((i : ℕ) + 1) accXIm _ (limbQ_accXIm δ b cells (wRows W) W.length chalV pubVal _ _ _ _) k)
          (fun k => by rw [henv_pub]; exact hρXi k) (by rw [hlen]; exact imX n le_rfl) _ hmem
        rwa [eval_mapC_cast, henv i] at hr
      · have hmem : mapC (fun q : ℚ => (q : F)) t' ∈ accGates 3 (slotsPIm (F := F)) accPIm pubRhoPIm := by
          rw [slotsPIm, ← accGates_map]; exact List.mem_map_of_mem ht
        have hr := accGates_prefixK b (slotsPIm (F := F)) accPIm pubRhoPIm W.length (i : ℕ) hiW envs
          (Quad.im _ (accSumPQ δ b cells (wRows W) chalV n)) (h11 _ hin) (h12 _ hin)
          (fun k => by
            rw [henvT _ hin, imP _ hin.le]
            exact hcoord (i : ℕ) accPIm _ (limbQ_accPIm δ b cells (wRows W) W.length chalV pubVal _ _ _ _) k)
          (fun hlt k => by
            rw [henvN _ (by omega), imP _ (by omega)]
            exact hcoord ((i : ℕ) + 1) accPIm _ (limbQ_accPIm δ b cells (wRows W) W.length chalV pubVal _ _ _ _) k)
          (fun k => by rw [henv_pub]; exact hρPi k) (by rw [hlen]; exact imP n le_rfl) _ hmem
        rwa [eval_mapC_cast, henv i] at hr
    · exact harith t' (List.mem_append_right _ ht)
  · obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hq
    rw [← slots_castSpec] at hT
    obtain ⟨S0, hS0, rfl⟩ := List.mem_map.mp hT
    rw [← henv i]
    have hz : Q.IsZero (slotGateQ F δ (castSpec S0)) (Compute.TowerD.gatherEnv b (envs i)) (envs i) :=
      (Q.isZero_iff δ _ _ _).mpr (hFi.1 S0 hS0)
    exact (Compute.TowerD.qGates_iff b (Compute.TowerD.isCoordEnv_gather b _) _).mpr hz g hg
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hm
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    rw [← henv i]
    have hev : (mapM (fun q : ℚ => (q : F)) g0).eval (Compute.TowerD.gatherEnv b (envs i)) (envs i) = 0 := by
      rw [eval_mapM_cast]
      exact walk_gates_Q δ hrun cells α γ hord b chalV pubVal hα hγ hpIC hpS hpO (envs i) i hiW
        (henvT i i.isLt) (fun hlt c => henvN i (lt_of_lt_of_eq hlt hlen) c) (henv_chal i) (henv_pub i) g0 hg0
    exact ((mixedCompile_zero_iff b Compute.TowerD.col0Id (Compute.TowerD.isCoordEnv_gather b _) _).mp hev) k

end Main

end

end Nock.NockVMROM.Thm54.VclL.Handle.HonestCompQ
