/-
  Nock/NockVMROM/Thm54/VclL/Handle/IOVS.lean

* §1 read-set congruence: every compute request list (`rowXReqs` / `rowPReqs`) reads only the
    round-0 columns `< 43` of its row, and every twin list (`walkXReqs`, `walkPProvs`, `cellProvs`) only
    the twins' round-0 base columns (`< 25` walk, `< 130` cell); none reads a coin or a public.
  * §2 the coin-free record lists `reqX0 / provX0 / reqP0 / provP0` of a trace pair, equal at every
    accepted coin to the lists `vs_served` consumes.
  * §3 **`ioSummandHX` / `ioSummandHP`**: `BadSummand`s on the coins `{γH, ρH} = {χ₁₁, χ₁₂}` with
    `dep = ∅` (the records are round-0 data, so `readsOn` holds for every staged strategy), weights
    `ioFailureUnionBound 5 (3N + W) T |𝕂|` and `ioFailureUnionBound 5 (2N) (2W) |𝕂|`.
  * §4 `served_of_not_mem`: outside both summands, at an accepted coin, the two handle lookups are
    served (`vs_served`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleC

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.IOVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Read-set congruence -/

section Read

/-- An expression reads only current-row trace columns below `B` (constants allowed). -/
def rdOK {G : Type} (B : ℕ) : CoeffExpr G → Bool
  | .const _ => true
  | .var .traceCur i => decide (i < B)
  | .var _ _ => false
  | .add a b => rdOK B a && rdOK B b
  | .sub a b => rdOK B a && rdOK B b
  | .mul a b => rdOK B a && rdOK B b
  | .neg a => rdOK B a
  | .pow a _ => rdOK B a

variable {F : Type} [Field F]

theorem evalQ_congr (B : ℕ) (g : CoeffExpr ℚ) (hg : rdOK B g = true) (e1 e2 : Env F)
    (h : ∀ c < B, e1.trace c = e2.trace c) : evalQ g e1 = evalQ g e2 := by
  induction g with
  | const c => rfl
  | var k i =>
    cases k with
    | traceCur => simp only [rdOK, decide_eq_true_eq] at hg; exact h i hg
    | traceNext => simp [rdOK] at hg
    | challenge => simp [rdOK] at hg
    | publicVal => simp [rdOK] at hg
  | add a b iha ihb =>
    simp only [rdOK, Bool.and_eq_true] at hg; simp only [evalQ, iha hg.1, ihb hg.2]
  | sub a b iha ihb =>
    simp only [rdOK, Bool.and_eq_true] at hg; simp only [evalQ, iha hg.1, ihb hg.2]
  | mul a b iha ihb =>
    simp only [rdOK, Bool.and_eq_true] at hg; simp only [evalQ, iha hg.1, ihb hg.2]
  | neg a iha => simp only [rdOK] at hg; simp only [evalQ, iha hg]
  | pow a n iha => simp only [rdOK] at hg; simp only [evalQ, iha hg]

theorem eval_congr (B : ℕ) (g : CoeffExpr F) (hg : rdOK B g = true) (e1 e2 : Env F)
    (h : ∀ c < B, e1.trace c = e2.trace c) : g.eval e1 = g.eval e2 := by
  induction g with
  | const c => rfl
  | var k i =>
    cases k with
    | traceCur => simp only [rdOK, decide_eq_true_eq] at hg; exact h i hg
    | traceNext => simp [rdOK] at hg
    | challenge => simp [rdOK] at hg
    | publicVal => simp [rdOK] at hg
  | add a b iha ihb =>
    simp only [rdOK, Bool.and_eq_true] at hg; simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | sub a b iha ihb =>
    simp only [rdOK, Bool.and_eq_true] at hg; simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | mul a b iha ihb =>
    simp only [rdOK, Bool.and_eq_true] at hg; simp only [CoeffExpr.eval, iha hg.1, ihb hg.2]
  | neg a iha => simp only [rdOK] at hg; simp only [CoeffExpr.eval, iha hg]
  | pow a n iha => simp only [rdOK] at hg; simp only [CoeffExpr.eval, iha hg]

end Read

section Rows

theorem slots_read : ∀ S ∈ (slots : List (SlotSpec ℚ)), ∀ x ∈ S.ents,
    rdOK 43 x.act = true ∧ ∀ c ∈ x.rcd, c < 43 := by decide

theorem slots_pair_read : ∀ S ∈ (slots : List (SlotSpec ℚ)), ∀ fl a b, S.pair = some (fl, a, b) →
    fl < 43 ∧ (∀ c ∈ a, c < 43) ∧ ∀ c ∈ b, c < 43 := by
  intro S hS fl a b hp
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl
  · simp [slot0] at hp
  · simp [slot1] at hp
  · simp only [slot2, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    exact ⟨by decide, by decide, by decide⟩

variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

theorem entKey_congr (r : List ℕ) (hr : ∀ c ∈ r, c < 43) (e1 e2 : Env F)
    (h : ∀ c < 43, e1.trace c = e2.trace c) : (entKey r e1 : Fin 5 → K) = entKey r e2 := by
  funext c
  simp only [entKey, entKeyN]
  split_ifs with hc
  · rw [h _ (hr _ (by rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem hc))]
  · rfl

/-- **A row's request lists read only its round-0 columns `< 43`.** -/
theorem rowReqs_congr (e1 e2 : Env F) (h : ∀ c < 43, e1.trace c = e2.trace c) :
    (rowXReqs e1 : List (Fin 5 → K)) = rowXReqs e2 ∧ (rowPReqs e1 : List (Fin 5 → K)) = rowPReqs e2 := by
  have hact : ∀ S ∈ (slots : List (SlotSpec ℚ)), ∀ x ∈ S.ents, evalQ x.act e1 = evalQ x.act e2 :=
    fun S hS x hx => evalQ_congr 43 _ (slots_read S hS x hx).1 e1 e2 h
  have hkey : ∀ S ∈ (slots : List (SlotSpec ℚ)), ∀ x ∈ S.ents,
      (entKey x.rcd e1 : Fin 5 → K) = entKey x.rcd e2 :=
    fun S hS x hx => entKey_congr _ (slots_read S hS x hx).2 e1 e2 h
  have hX : ∀ S ∈ (slots : List (SlotSpec ℚ)), activeX S e1 = activeX S e2 := fun S hS => by
    unfold activeX
    refine List.filter_congr fun x hx => ?_
    rw [hact S hS x (List.mem_filter.mp hx).1]
  have hP : ∀ S ∈ (slots : List (SlotSpec ℚ)), activeP S e1 = activeP S e2 := fun S hS => by
    unfold activeP
    refine List.filter_congr fun x hx => ?_
    rw [hact S hS x (List.mem_filter.mp hx).1]
  have hpair : ∀ S ∈ (slots : List (SlotSpec ℚ)), (pairReqs S e1 : List (Fin 5 → K)) = pairReqs S e2 :=
    fun S hS => by
      unfold pairReqs
      cases hp : S.pair with
      | none => rfl
      | some q =>
        obtain ⟨fl, a, b⟩ := q
        obtain ⟨hfl, ha, hb⟩ := slots_pair_read S hS fl a b hp
        simp only [h fl hfl, entKey_congr a ha e1 e2 h, entKey_congr b hb e1 e2 h]
  refine ⟨?_, ?_⟩
  · unfold rowXReqs
    simp only [List.flatMap]
    congr 1
    refine List.map_congr_left fun S hS => ?_
    rw [hX S hS]
    refine List.map_congr_left fun x hx => ?_
    exact hkey S hS x (List.mem_filter.mp (List.mem_filter.mp hx).1).1
  · unfold rowPReqs
    simp only [List.flatMap]
    congr 1
    refine List.map_congr_left fun S hS => ?_
    rw [hP S hS, hpair S hS]
    congr 1
    refine List.map_congr_left fun x hx => ?_
    exact hkey S hS x (List.mem_filter.mp (List.mem_filter.mp hx).1).1

/-- Trace agreement of two row environments built from column families agreeing below `B`. -/
theorem envOfTrace_congr {w : ℕ} (B : ℕ) (Q Q' : Fin w → F[X]) (hQ : ∀ j : Fin w, (j : ℕ) < B → Q j = Q' j)
    (ω x : F) (cv pv cv' pv' : ℕ → F) :
    ∀ c < B, (envOfTrace Q ω x cv pv).trace c = (envOfTrace Q' ω x cv' pv').trace c := by
  intro c hc
  simp only [envOfTrace]
  split_ifs with hw
  · rw [hQ ⟨c, hw⟩ hc]
  · rfl

/-- **The compute request lists read only the round-0 columns** (and no coin, no public). -/
theorem compReqs_congr {h n w : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (cv pv cv' pv' : ℕ → F) (Q Q' : Fin w → F[X]) (hQ : ∀ j : Fin w, (j : ℕ) < 43 → Q j = Q' j) :
    (compXReqs nodes cv pv orbit Q : List (Fin 5 → K)) = compXReqs nodes cv' pv' orbit Q' ∧
      (compPReqs nodes cv pv orbit Q : List (Fin 5 → K)) = compPReqs nodes cv' pv' orbit Q' := by
  have hrow := fun i : Fin n => rowReqs_congr (K := K) (envOfTrace Q orbit.ω (nodes i) cv pv)
    (envOfTrace Q' orbit.ω (nodes i) cv' pv') (envOfTrace_congr 43 Q Q' hQ _ _ _ _ _ _)
  refine ⟨?_, ?_⟩
  · unfold compXReqs; simp only [List.flatMap]; congr 1
    exact List.map_congr_left fun i _ => (hrow i).1
  · unfold compPReqs; simp only [List.flatMap]; congr 1
    exact List.map_congr_left fun i _ => (hrow i).2

end Rows

section Twins
variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

theorem keyVec5_congr (B : ℕ) (l : List (CoeffExpr F)) (hl : ∀ g ∈ l, rdOK B g = true) (e1 e2 : Env F)
    (h : ∀ c < B, e1.trace c = e2.trace c) : (keyVec5 l e1 : Fin 5 → K) = keyVec5 l e2 := by
  funext c
  simp only [keyVec5]
  congr 1
  by_cases hc : (c : ℕ) < l.length
  · rw [List.getD_eq_getElem _ _ hc]
    exact eval_congr B _ (hl _ (List.getElem_mem hc)) e1 e2 h
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

theorem xKeyH_read : ∀ g ∈ (WalkHC.xKeyH : List (CoeffExpr F)), rdOK 25 g = true := by
  simp [WalkHC.xKeyH, rdOK, cv, WChip.idx, WalkHC.kL, WalkHC.vL, WalkHC.kR, WalkHC.vR]

theorem recLH_read : ∀ g ∈ (WalkHC.recLH : List (CoeffExpr F)), rdOK 25 g = true := by
  simp [WalkHC.recLH, rdOK, cv, WChip.ridx, WChip.pre, WalkHC.kL, WalkHC.vL]

theorem recRH_read : ∀ g ∈ (WalkHC.recRH : List (CoeffExpr F)), rdOK 25 g = true := by
  simp [WalkHC.recRH, rdOK, cv, WChip.ridx, WChip.pre, WalkHC.kR, WalkHC.vR]

theorem keyH_read : ∀ g ∈ (CellH.keyH : List (CoeffExpr F)), rdOK 130 g = true := by
  simp [CellH.keyH, CellH.valE, notE, rdOK, cv]; decide

variable (b : Basis (Fin 3) F K) {h n w : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
  (chals pubs chals' pubs' : ℕ → K) (Q Q' : Fin w → F[X])

/-- **The walk twin's lists read only its round-0 base columns `< 25`.** -/
theorem walkLists_congr (hQ : ∀ j : Fin w, (j : ℕ) < 25 → Q j = Q' j) :
    walkXReqs b nodes orbit chals pubs Q = walkXReqs b nodes orbit chals' pubs' Q' ∧
      walkPProvs b nodes orbit chals pubs Q = walkPProvs b nodes orbit chals' pubs' Q' := by
  have he := fun i : Fin n => envOfTrace_congr 25 Q Q' hQ orbit.ω (nodes i) (slotVal b 25 chals)
    (slotVal b 25 pubs) (slotVal b 25 chals') (slotVal b 25 pubs')
  refine ⟨?_, ?_⟩
  · unfold walkXReqs
    exact List.map_congr_left fun i _ => keyVec5_congr 25 _ xKeyH_read _ _ (he i)
  · unfold walkPProvs
    simp only [List.flatMap]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    rw [keyVec5_congr 25 _ recLH_read _ _ (he i), keyVec5_congr 25 _ recRH_read _ _ (he i),
      he i WChip.mL (by decide), he i WChip.mR (by decide)]

/-- **The cell twin's providers read only its round-0 base columns `< 130`.** -/
theorem cellProvs_congr (hQ : ∀ j : Fin w, (j : ℕ) < 130 → Q j = Q' j) :
    cellProvs b nodes orbit chals pubs Q = cellProvs b nodes orbit chals' pubs' Q' := by
  have he := fun i : Fin n => envOfTrace_congr 130 Q Q' hQ orbit.ω (nodes i) (slotVal b 130 chals)
    (slotVal b 130 pubs) (slotVal b 130 chals') (slotVal b 130 pubs')
  unfold cellProvs
  refine List.map_congr_left fun i _ => ?_
  rw [keyVec5_congr 130 _ keyH_read _ _ (he i), he i CellH.mh (by decide)]

end Twins


/-! ## 2–3. The coin-free record lists and the two handle IO summands -/

section Summands
open FrameVS SVFrameG T0Tower

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (hT hP hC : ℕ)

/-- The VS trace pair. -/
abbrev TrVS (F : Type) [Field F] (hT hP hC : ℕ) := Traces F (tableVS hC) (shapeVS hT hP)

/-- **Consumers of the handle-export lookup** (compute `L1–L3, L5` keys, then the walk twin's
consumed keys), read off the round-0 columns only. -/
def reqX0 (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) : List (Fin 5 → K) :=
  compXReqs V.computeNodes (fun _ => 0) (fun _ => 0) V.orbitC tr.1 ++
    walkXReqs V.basis (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) (fun _ => 0) (fun _ => 0)
      (tr.2 (tWS hT hP))

/-- **Providers of the handle-export lookup** (the cell twin's `(keyH, mh)`). -/
def provX0 (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) : List ((Fin 5 → K) × K) :=
  cellProvs V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (fun _ => 0) (fun _ => 0)
    (tr.2 (tCS hT hP))

/-- **Consumers of the handle walk lookup**. -/
def reqP0 (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) : List (Fin 5 → K) :=
  compPReqs V.computeNodes (fun _ => 0) (fun _ => 0) V.orbitC tr.1

/-- **Providers of the handle walk lookup** (the walk twin's two records per row, weights `mL / mR`). -/
def provP0 (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) : List ((Fin 5 → K) × K) :=
  walkPProvs V.basis (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) (fun _ => 0) (fun _ => 0)
    (tr.2 (tWS hT hP))

theorem provX0_length (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    (provX0 hT hP hC V tr).length = V.memRows (tCS hT hP) := by
  simp [provX0, cellProvs]

theorem provP0_length (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    (provP0 hT hP hC V tr).length = 2 * V.memRows (tWS hT hP) := by
  simp [provP0, walkPProvs, List.length_flatMap, mul_comm]

theorem ioUB_mono (m k₁ k₂ n₁ n₂ c : ℕ) (h1 : k₁ ≤ n₁) (h2 : k₂ ≤ n₂) :
    ioFailureUnionBound m k₁ k₂ c ≤ ioFailureUnionBound m n₁ n₂ c := by
  unfold ioFailureUnionBound
  have hs : k₁ + k₂ ≤ n₁ + n₂ := Nat.add_le_add h1 h2
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hs hs)))
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs))

open Classical in
/-- The export event, guarded by the consumer budget `3N + W` (true at every accepted coin). -/
def evX (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) : Finset (K × K) :=
  if (reqX0 hT hP hC V tr).length ≤ 3 * V.N + V.memRows (tWS hT hP) then
    IOFailureEventW (reqX0 hT hP hC V tr) (provX0 hT hP hC V tr) else ∅

open Classical in
/-- The path event, guarded by the consumer budget `2N`. -/
def evP (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) : Finset (K × K) :=
  if (reqP0 hT hP hC V tr).length ≤ 2 * V.N then
    IOFailureEventW (reqP0 hT hP hC V tr) (provP0 hT hP hC V tr) else ∅

theorem evX_card (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    (evX hT hP hC V tr).card ≤
      ioFailureUnionBound 5 (3 * V.N + V.memRows (tWS hT hP)) (V.memRows (tCS hT hP)) (Fintype.card K) := by
  unfold evX
  split_ifs with hl
  · refine (IOFailureEventW_card_le _ _).trans (ioUB_mono _ _ _ _ _ _ hl (le_of_eq (provX0_length hT hP hC V tr)))
  · simp

theorem evP_card (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) :
    (evP hT hP hC V tr).card ≤
      ioFailureUnionBound 5 (2 * V.N) (2 * V.memRows (tWS hT hP)) (Fintype.card K) := by
  unfold evP
  split_ifs with hl
  · refine (IOFailureEventW_card_le _ _).trans (ioUB_mono _ _ _ _ _ _ hl (le_of_eq (provP0_length hT hP hC V tr)))
  · simp

/-- The handle coins `{γH, ρH} = {χ₁₁, χ₁₂}`. -/
abbrev hcoins : Finset (Fin frameVS.n) := {cGamH, cRhoH}

def pairOf (v : {i // i ∈ hcoins} → K) : K × K :=
  (v ⟨cGamH, by simp⟩, v ⟨cRhoH, by simp⟩)

theorem pairOf_inj : Function.Injective (pairOf (K := K)) := by
  intro v v' hv
  simp only [pairOf, Prod.mk.injEq] at hv
  funext ⟨i, hi⟩
  simp only [hcoins, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact hv.1
  · exact hv.2

/-- Staged traces agree, across coins, on every round-0 column. -/
theorem staged_round0 (Q : Coins frameVS K → TrVS F hT hP hC)
    (hQ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) Q) (χ χ' : Coins frameVS K) :
    (∀ j : Fin (tableVS hC).width, (j : ℕ) < 43 → (Q χ).1 j = (Q χ').1 j) ∧
      (∀ j : Fin ((shapeVS hT hP).table (tCS hT hP)).width, (j : ℕ) < 130 →
        (Q χ).2 (tCS hT hP) j = (Q χ').2 (tCS hT hP) j) ∧
      (∀ j : Fin ((shapeVS hT hP).table (tWS hT hP)).width, (j : ℕ) < 25 →
        (Q χ).2 (tWS hT hP) j = (Q χ').2 (tWS hT hP) j) := by
  refine ⟨fun j hj => hQ.1 j χ χ' fun i hi => ?_, fun j hj => hQ.2 _ j χ χ' fun i hi => ?_,
    fun j hj => hQ.2 _ j χ χ' fun i hi => ?_⟩
  · exfalso
    have : (tableVS hC).colRound j = 0 := by
      simp only [tableVS, ChipH.round0W]; simp [hj]
    omega
  · exfalso
    have : ((shapeVS hT hP).table (tCS hT hP)).colRound j = 0 := by
      change colRoundCH j = 0
      simp only [colRoundCH]; rw [if_pos hj]
    omega
  · exfalso
    have : ((shapeVS hT hP).table (tWS hT hP)).colRound j = 0 := by
      change colRoundWH j = 0
      simp only [colRoundWH]; rw [if_pos hj]
    omega

theorem lists_staged (V : VerifierData F K hC (shapeVS hT hP)) (Q : Coins frameVS K → TrVS F hT hP hC)
    (hQ : TracesStaged frameVS (tableVS hC) (shapeVS hT hP) Q) (χ χ' : Coins frameVS K) :
    reqX0 hT hP hC V (Q χ) = reqX0 hT hP hC V (Q χ') ∧ provX0 hT hP hC V (Q χ) = provX0 hT hP hC V (Q χ') ∧
      reqP0 hT hP hC V (Q χ) = reqP0 hT hP hC V (Q χ') ∧ provP0 hT hP hC V (Q χ) = provP0 hT hP hC V (Q χ') := by
  obtain ⟨h1, h2, h3⟩ := staged_round0 hT hP hC Q hQ χ χ'
  have hc := compReqs_congr (K := K) V.computeNodes V.orbitC (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    _ _ h1
  have hw := walkLists_congr V.basis (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) _ _ h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold reqX0; rw [hc.1, hw.1]
  · unfold provX0
    exact cellProvs_congr V.basis _ _ _ _ _ _ _ _ h2
  · unfold reqP0; rw [hc.2]
  · unfold provP0; rw [hw.2]

/-- **The handle-export IO summand** (coins `{11, 12}`, no dependency: round-0 records). -/
def ioSummandHX (V : VerifierData F K hC (shapeVS hT hP)) :
    BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) where
  coins := hcoins
  dep := ∅
  disj := Finset.disjoint_empty_right _
  badSet tr _ := Finset.univ.filter fun v => pairOf v ∈ evX hT hP hC V tr
  weight := ioFailureUnionBound 5 (3 * V.N + V.memRows (tWS hT hP)) (V.memRows (tCS hT hP)) (Fintype.card K)
  card_le tr _ := by
    refine le_trans (Finset.card_le_card_of_injOn pairOf ?_ (fun v _ v' _ h => pairOf_inj h))
      (evX_card hT hP hC V tr)
    intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
    exact hv
  readsOn Q hQ χ χ' _ := by
    obtain ⟨e1, e2, -, -⟩ := lists_staged hT hP hC V Q hQ χ χ'
    simp only [evX, e1, e2]
    rfl

/-- **The handle-path IO summand** (coins `{11, 12}`, no dependency). -/
def ioSummandHP (V : VerifierData F K hC (shapeVS hT hP)) :
    BadSummand frameVS K (TrVS F hT hP hC) (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)) where
  coins := hcoins
  dep := ∅
  disj := Finset.disjoint_empty_right _
  badSet tr _ := Finset.univ.filter fun v => pairOf v ∈ evP hT hP hC V tr
  weight := ioFailureUnionBound 5 (2 * V.N) (2 * V.memRows (tWS hT hP)) (Fintype.card K)
  card_le tr _ := by
    refine le_trans (Finset.card_le_card_of_injOn pairOf ?_ (fun v _ v' _ h => pairOf_inj h))
      (evP_card hT hP hC V tr)
    intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
    exact hv
  readsOn Q hQ χ χ' _ := by
    obtain ⟨-, -, e3, e4⟩ := lists_staged hT hP hC V Q hQ χ χ'
    simp only [evP, e3, e4]
    rfl

theorem mem_ioSummandHX (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) (χ : Coins frameVS K) :
    (ioSummandHX hT hP hC V).mem tr χ ↔ (χ cGamH, χ cRhoH) ∈ evX hT hP hC V tr := by
  unfold BadSummand.mem ioSummandHX
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_ioSummandHP (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC) (χ : Coins frameVS K) :
    (ioSummandHP hT hP hC V).mem tr χ ↔ (χ cGamH, χ cRhoH) ∈ evP hT hP hC V tr := by
  unfold BadSummand.mem ioSummandHP
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

end Summands


/-! ## 4. Outside the two summands, the handle lookups are served -/

section Served
open FrameVS SVFrameG T0Tower

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

/-- At any coin the coin-free lists ARE the lists `vs_served` consumes. -/
theorem lists_at (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    reqX0 hT hP hC V (msg.traces χ) = cXVS δF hT hP kr hC V msg χ ++ wXVS δF hT hP kr hC V msg χ ∧
      provX0 hT hP hC V (msg.traces χ) = tXVS δF hT hP kr hC V msg χ ∧
      reqP0 hT hP hC V (msg.traces χ) = cPVS δF hT hP kr hC V msg χ ∧
      provP0 hT hP hC V (msg.traces χ) = wPVS δF hT hP kr hC V msg χ := by
  have hc := compReqs_congr (K := K) V.computeNodes V.orbitC (fun _ => 0) (fun _ => 0)
    (chalVH V.basis χ) (pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ) (msg.Qc χ) (msg.Qc χ)
    (fun _ _ => rfl)
  have hw := walkLists_congr V.basis (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) (fun _ => 0) (fun _ => 0)
    (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    (msg.Qm χ (tWS hT hP)) (msg.Qm χ (tWS hT hP)) (fun _ _ => rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold reqX0; exact congrArg₂ (· ++ ·) hc.1 hw.1
  · unfold provX0
    exact cellProvs_congr V.basis _ _ _ _ _ _ _ _ (fun _ _ => rfl)
  · unfold reqP0; exact hc.2
  · unfold provP0; exact hw.2

/-- **Outside the two handle IO summands, at an accepted coin, both handle lookups are served.** -/
theorem served_of_not_mem (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hX : ¬ (ioSummandHX hT hP hC V).mem (msg.traces χ) χ)
    (hPm : ¬ (ioSummandHP hT hP hC V).mem (msg.traces χ) χ) :
    (∀ r ∈ cXVS δF hT hP kr hC V msg χ ++ wXVS δF hT hP kr hC V msg χ,
        r ∈ (tXVS δF hT hP kr hC V msg χ).map Prod.fst) ∧
      ∀ r ∈ cPVS δF hT hP kr hC V msg χ, r ∈ (wPVS δF hT hP kr hC V msg χ).map Prod.fst := by
  obtain ⟨hg, hsat⟩ := compute_facts δF hT hP kr hC V msg χ h
  have hc : 11 < ringChar F := lt_trans (by norm_num) hg.2.2.1
  have hcC := compXReqs_len (K := K) V.hN V.computeNodes V.basis _ _ V.orbitC (msg.Qc χ) hsat hc
  have hcP := compPReqs_len (K := K) V.hN V.computeNodes V.basis _ _ V.orbitC (msg.Qc χ) hsat hc
  obtain ⟨e1, e2, e3, e4⟩ := lists_at δF hT hP kr hC V msg χ
  rw [mem_ioSummandHX] at hX
  rw [mem_ioSummandHP] at hPm
  have hX' : (χ cGamH, χ cRhoH) ∉ IOFailureEventW (cXVS δF hT hP kr hC V msg χ ++ wXVS δF hT hP kr hC V msg χ)
      (tXVS δF hT hP kr hC V msg χ) := by
    intro hm
    apply hX
    unfold evX
    rw [if_pos, e1, e2]
    · exact hm
    · rw [e1, List.length_append]
      dsimp only [cXVS, wXVS]
      simp only [walkXReqs, List.length_map, List.length_finRange]
      exact Nat.add_le_add_right hcC _
  have hP' : (χ cGamH, χ cRhoH) ∉ IOFailureEventW (cPVS δF hT hP kr hC V msg χ) (wPVS δF hT hP kr hC V msg χ) := by
    intro hm
    apply hPm
    unfold evP
    rw [if_pos, e3, e4]
    · exact hm
    · rw [e3]; exact hcP
  exact vs_served δF hT hP kr hC V hV msg χ h hX' hP'

end Served

end

end Nock.NockVMROM.Thm54.VclL.Handle.IOVS
