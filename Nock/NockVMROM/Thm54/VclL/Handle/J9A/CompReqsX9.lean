/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/CompReqsX9.lean

* `consQX9 eF bl` — the records a twin row consumes into balance `bl` (`slotsX9`; `TeleCQX.consQX`'s shape).
  * `envsN9` — the twin row environment `Env.viaPerm permX9` of the RAP row (`TeleC.envsN`), i.e. the unpermuted
    twin layout that `computeChipVCLHX9_sat_twin` speaks about.
  * **`compReqsX9`** — the compute request list of balance `bl` at the twin chip (rows `0..n-1` in order).
  * `slotsX9_read` — every twin slot reads only twin columns `c` with `permX9 c < 83`, i.e. RAP round 0
    (`permX9_round0_iff`): the J-8 columns `< 69` and the appended `123..136` (`xId`, `axL`, `limb`, …).
  * **`compReqsX9_congr`** — the list is independent of the coins, the publics and the width, and reads only
    RAP round-0 columns `< 83`.
  * **`compReqsOf9_reads`** — along `StJ9A`, `ReadsOnC frameJ8 ∅` for each balance (the coin-free list read off
    the trace).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.ReadIOJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (permX9 widthHX9 computeChipVCLHX9 slotsX9 Env.viaPerm)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (pairRecsB)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (keyX keyXN mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ReadIOJ8 (reEv_congr keyX_congr)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (staged_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (PubJ9A TrJ9A StJ9A crC9)

noncomputable section

/-! ## 1. Twin read sets: RAP round 0 -/

/-- A twin column is read in RAP round 0. -/
def r0 (c : ℕ) : Bool := decide (permX9 c < 83)

/-- A gate reads only round-0 twin columns of the current row. -/
def rdP : CoeffExpr ℚ → Bool
  | .const _ => true
  | .var .traceCur i => r0 i
  | .var _ _ => false
  | .add a b => rdP a && rdP b
  | .sub a b => rdP a && rdP b
  | .mul a b => rdP a && rdP b
  | .neg a => rdP a
  | .pow a _ => rdP a

/-- A record entry reads a round-0 twin column (or is a constant). -/
def reP : RE → Bool
  | .col i => r0 i
  | .k _ => true

/-- **The twin slots read only RAP round-0 columns**: every entry's activity and record, every pair's flag and
records (the J-8 columns `< 69` and the appended `xId`, `axL`, `limb`). -/
theorem slotsX9_read : ∀ S ∈ (slotsX9 : List (SlotX ℚ)), (∀ x ∈ S.ents,
    rdP x.act = true ∧ x.rcd.all reP = true) ∧
    (match S.pair with
     | some (fl, a, c, _) => r0 fl && a.all reP && c.all reP
     | none => true) = true := by
  decide +kernel

section Cong
variable {F : Type} [Field F]

/-- Two twin environments agreeing on the round-0 columns. -/
def Agree0 (e1 e2 : Env F) : Prop := ∀ c, r0 c = true → e1.trace c = e2.trace c

theorem evalQX_congrP (g : CoeffExpr ℚ) (hg : rdP g = true) {e1 e2 : Env F} (h : Agree0 e1 e2) :
    evalQX g e1 = evalQX g e2 := by
  induction g with
  | const c => rfl
  | var k i =>
    cases k with
    | traceCur => exact h i hg
    | traceNext => simp [rdP] at hg
    | challenge => simp [rdP] at hg
    | publicVal => simp [rdP] at hg
  | add a b iha ihb =>
    simp only [rdP, Bool.and_eq_true] at hg; simp only [evalQX, iha hg.1, ihb hg.2]
  | sub a b iha ihb =>
    simp only [rdP, Bool.and_eq_true] at hg; simp only [evalQX, iha hg.1, ihb hg.2]
  | mul a b iha ihb =>
    simp only [rdP, Bool.and_eq_true] at hg; simp only [evalQX, iha hg.1, ihb hg.2]
  | neg a iha => simp only [rdP] at hg; simp only [evalQX, iha hg]
  | pow a n iha => simp only [rdP] at hg; simp only [evalQX, iha hg]

theorem reEv_congrP (x : RE) (hx : reP x = true) {e1 e2 : Env F} (h : Agree0 e1 e2) :
    x.ev e1.trace = x.ev e2.trace := by
  cases x with
  | col i => exact h i hx
  | k c => rfl

variable {K : Type} [Field K] [Algebra F K]

theorem keyX_congrP (m : ℕ) (r : List RE) (hr : r.all reP = true) {e1 e2 : Env F} (h : Agree0 e1 e2) :
    (keyX m r e1 : Fin m → K) = keyX m r e2 := by
  funext c
  simp only [keyX, keyXN]
  congr 1
  by_cases hc : (c : ℕ) < r.length
  · rw [List.getD_eq_getElem _ _ hc]
    exact reEv_congrP _ (List.all_eq_true.mp hr _ (List.getElem_mem hc)) h
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

/-! ## 2. The twin's consumed records -/

variable [DecidableEq F]

/-- **The records a twin row consumes into balance `bl`** (`TeleCQX.consQX` over `slotsX9`). -/
def consQX9 (eF : Env F) (bl : Bal) : List (List RE) :=
  (slotsX9 (F := ℚ)).flatMap fun S =>
    (((S.ents.filter fun x => decide (x.bal = bl)).filter fun x => decide (evalQX x.act eF = 1)).map
      (·.rcd)) ++ pairRecsB eF bl S

theorem consQX9_congr {e1 e2 : Env F} (h : Agree0 e1 e2) (bl : Bal) : consQX9 e1 bl = consQX9 e2 bl := by
  unfold consQX9
  refine congrArg List.flatten (List.map_congr_left fun S hS => ?_)
  obtain ⟨hE, hP⟩ := slotsX9_read S hS
  congr 1
  · congr 1
    refine List.filter_congr fun x hx => ?_
    rw [evalQX_congrP _ (hE x (List.mem_filter.mp hx).1).1 h]
  · unfold pairRecsB
    cases hp : S.pair with
    | none => rfl
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      rw [hp] at hP
      simp only [Bool.and_eq_true] at hP
      simp only [h fl hP.1.1]

theorem consQX9_read (e : Env F) (bl : Bal) : ∀ r ∈ consQX9 e bl, r.all reP = true := by
  intro r hr
  unfold consQX9 at hr
  obtain ⟨S, hS, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨hE, hP⟩ := slotsX9_read S hS
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact (hE x (List.mem_filter.mp (List.mem_filter.mp hx).1).1).2
  · unfold pairRecsB at hr
    cases hp : S.pair with
    | none => rw [hp] at hr; simp at hr
    | some q =>
      obtain ⟨fl, a, c, b'⟩ := q
      rw [hp] at hr hP
      simp only [Bool.and_eq_true] at hP
      simp only at hr
      split_ifs at hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hP.1.2
        · exact hP.2
      · simp at hr

end Cong

/-! ## 3. The twin compute request lists -/

section Comp
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)

/-- **The twin row environment**: the RAP row read through `permX9` (the unpermuted twin layout). -/
def envsN9 (chalV pubVal : ℕ → F) {w : ℕ} (Q : Fin w → F[X]) (k : ℕ) : Env F :=
  Env.viaPerm permX9 (TeleC.envsN hn nodes chalV pubVal orbit Q k)

/-- **The twin compute request list of balance `bl`**: the keys of the records every twin row consumes into
`bl` (rows `0..n-1` in order), at width `mOf bl`. -/
def compReqsX9 (chalV pubVal : ℕ → F) {w : ℕ} (Q : Fin w → F[X]) (bl : Bal) : List (Fin (mOf bl) → K) :=
  (List.range n).flatMap fun i =>
    (consQX9 (envsN9 hn nodes orbit chalV pubVal Q i) bl).map fun r =>
      keyX (mOf bl) r (envsN9 hn nodes orbit chalV pubVal Q i)

/-- **The twin compute request lists read only RAP round-0 columns `< 83`, no coin, no public, any width.** -/
theorem compReqsX9_congr {chalV pubVal chalV' pubVal' : ℕ → F} {w w' : ℕ}
    (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hw : 83 ≤ w) (hw' : 83 ≤ w')
    (hQ : ∀ (j : ℕ) (h1 : j < w) (h2 : j < w'), j < 83 → Q ⟨j, h1⟩ = Q' ⟨j, h2⟩) (bl : Bal) :
    (compReqsX9 hn nodes orbit chalV pubVal Q bl : List (Fin (mOf bl) → K)) =
      compReqsX9 hn nodes orbit chalV' pubVal' Q' bl := by
  have hE : ∀ i, Agree0 (envsN9 hn nodes orbit chalV pubVal Q i) (envsN9 hn nodes orbit chalV' pubVal' Q' i) := by
    intro i c hc
    have hc' : permX9 c < 83 := by simpa [r0] using hc
    simp only [envsN9, Env.viaPerm, TeleC.envsN, TeleC.rEF]
    split_ifs <;>
      exact DescentVSQ.envOfTrace_congrW 83 Q Q' hw hw' hQ _ _ _ _ _ _ _ _ hc'
  unfold compReqsX9
  refine congrArg List.flatten (List.map_congr_left fun i _ => ?_)
  rw [consQX9_congr (hE i) bl]
  refine List.map_congr_left fun r hr => ?_
  exact keyX_congrP _ r (consQX9_read _ bl r hr) (hE i)

end Comp

/-! ## 4. Along `StJ9A`: constant in the coins -/

section Reads
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [DecidableEq (ZMod p)]

/-- **The twin compute request list of a `J-9 A` trace**, coin- and public-free. -/
def compReqsOf9 (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) (bl : Bal) : List (Fin (mOf bl) → K) :=
  compReqsX9 Pb.hn Pb.nodes Pb.orbit (fun _ => 0) (fun _ => 0) tr.C bl

/-- The coin-carrying list at any coins / publics is the coin-free one. -/
theorem compReqsX9_eq_of9 (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) (chalV pubVal : ℕ → ZMod p) (bl : Bal) :
    (compReqsX9 Pb.hn Pb.nodes Pb.orbit chalV pubVal tr.C bl : List (Fin (mOf bl) → K)) =
      compReqsOf9 Pb tr bl :=
  compReqsX9_congr Pb.hn Pb.nodes Pb.orbit tr.C tr.C (by norm_num) (by norm_num) (fun _ _ _ _ => rfl) bl

/-- **Along `StJ9A` the twin compute request lists are constant in the coins** (`ReadsOnC frameJ8 ∅`): they
read RAP round-0 compute columns only. -/
theorem compReqsOf9_reads (Pb : PubJ9A p) {Q : Coins frameJ8 K → TrJ9A (ZMod p)} (hQ : StJ9A Q) (bl : Bal) :
    ReadsOnC frameJ8 ∅ (fun χ => (compReqsOf9 Pb (Q χ) bl : List (Fin (mOf bl) → K))) := by
  intro χ χ' _
  refine compReqsX9_congr Pb.hn Pb.nodes Pb.orbit (Q χ).C (Q χ').C (by norm_num) (by norm_num)
    (fun j h1 h2 hj => ?_) bl
  exact staged_eq hQ.1 (r := 0) (fun i hi => absurd hi (by omega)) ⟨j, h1⟩ (by simp [crC9, hj])

end Reads

end

end Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9

open Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9 in
#print axioms slotsX9_read
open Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9 in
#print axioms compReqsX9_congr
open Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9 in
#print axioms compReqsOf9_reads
