/-
**`exec_e2e_J8F`**, the reduced end-to-end theorem at the J-8 interface: `exec_e2e_J8` (Exec/E2EJ8.lean, gated)
with every binder that a lemma covers discharged (Exec/E2EJ8P.lean, E2EJ8P2.lean, J8ShapeX.lean, J8/HopsLit.lean).
The binder ledger is at the end of the file. `R` is ABSTRACT (a concrete `RJ8` makes whnf time out); the final instance is `Inst.ofRJ8`.
-/
import NockvmE2E.Exec.E2EJ8
import NockvmE2E.Exec.E2EJ8P
import NockvmE2E.Exec.E2EJ8P2
import NockvmE2E.Exec.J8ShapeX
import NockvmE2E.Exec.J8Chips
import NockvmE2E.Exec.MaskOk
import NockvmE2E.Exec.MaskBridge
import NockvmE2E.Exec.E2EJ8S
import NockvmE2E.J8.HopsLit
import NockvmE2E.Exec.J8ChipsK_compute
import NockvmE2E.Exec.J8ChipsK_cell
import NockvmE2E.Exec.J8ChipsK_atom
import NockvmE2E.Exec.J8ChipsK_jet
import NockvmE2E.Exec.J8ChipsK_walkJ8_1
import NockvmE2E.Exec.J8ChipsK_walkJ8_9
import NockvmE2E.Exec.J8ChipsK_walkJ8_25
import NockvmE2E.Exec.J8ChipsK_walkJ8_42
import NockvmE2E.Exec.J8ChipsK_walkJ8_48
import NockvmE2E.Exec.J8ChipsK_walkJ8_174
import NockvmE2E.Exec.J8ChipsK_walkHQK_1
import NockvmE2E.Exec.J8ChipsK_walkHQK_2
import NockvmE2E.J8.TieJ8G

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.E2EJ8F
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit NockvmE2E.J8 NockvmE2E.J8.TieJ8G
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx)
open NockvmE2E.J8.TieJ8 (HopZero)
open NockvmE2E.Exec.E2EJ8P2 NockvmE2E.Exec.E2EJ8P
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Rap
open NockvmE2E.J8.InstJ8 (Φ0)

/-! ## 1. hop 0 from the exe's chip check: `HopsOK`, `NumOK`, the constraint-count cap -/

def LitTies : Prop :=
  tieB computeSpec chipCompute = true ∧ tieB cellKWSpec chipCell = true ∧ tieB atomSpec chipAtom = true ∧
  tieB jetSpec chipJet = true ∧
  tieB (walkJ8SpecAt 1) chipWalkJ8_1 = true ∧ tieB (walkJ8SpecAt 9) chipWalkJ8_9 = true ∧
  tieB (walkJ8SpecAt 25) chipWalkJ8_25 = true ∧ tieB (walkJ8SpecAt 42) chipWalkJ8_42 = true ∧
  tieB (walkJ8SpecAt 48) chipWalkJ8_48 = true ∧ tieB (walkJ8SpecAt 174) chipWalkJ8_174 = true ∧
  tieB (walkAtomSpecAt 1) chipWalkHQK_1 = true ∧ tieB (walkAtomSpecAt 2) chipWalkHQK_2 = true

/-- **`LitTies` is a theorem**: the 12 per-literal kernel ties (modules `J8ChipsK_*`) -/
theorem litTies : LitTies :=
  ⟨tie_compute, tie_cell, tie_atom, tie_jet, tie_walkJ8_1, tie_walkJ8_9, tie_walkJ8_25, tie_walkJ8_42, tie_walkJ8_48,
    tie_walkJ8_174, tie_walkHQK_1, tie_walkHQK_2⟩

def numOf (d : InstJ8.Datum) (s : Fin 6) : ℕ :=
  if s = 2 then d.Pb.kroots else if s = 5 then d.Pb.krootsV else 0

theorem chipEqB_baseCols (a b : Chip) (h : chipEqB a b = true) : a.baseCols = b.baseCols := by
  unfold chipEqB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem conListEqB_length : ∀ a b : List Con, conListEqB a b = true → a.length = b.length
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp [conListEqB] at h
  | _ :: _, [] => fun h => by simp [conListEqB] at h
  | x :: xs, y :: ys => fun h => by
    simp only [conListEqB, Bool.and_eq_true] at h
    simp [conListEqB_length xs ys h.2]

theorem chipEqB_size (a b : Chip) (h : chipEqB a b = true) : a.cons.size = b.cons.size := by
  unfold chipEqB at h
  simp only [Bool.and_eq_true] at h
  have := conListEqB_length _ _ h.1.1.1.2
  simpa using this

theorem num_find (c : Chip) (k : ℕ) (h : chipNumeral c = some k) :
    ∃ lit, (k, lit) ∈ expectedOf c.id ∧ chipEqB c lit = true := by
  unfold chipNumeral at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨p.2, by simpa using List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp⟩

theorem hop_of (s : TSpec) (lit c : Chip) (n : ℕ) (hb : lit.baseCols = n) (h1 : tieB s lit = true)
    (h2 : chipEqB c lit = true) : HopZero c (emitDag s) jDers jMeta c.baseCols ∧ c.baseCols = n :=
  ⟨HopsLit.hopZero_of_tie s lit c h1 h2, (chipEqB_baseCols c lit h2).trans hb⟩


theorem hops_of_chips (I : Inst) (hc : chipsOk I.XI = true) (LT : LitTies)
    (hnum0 : ∀ t : Fin I.XI.tabs.size, (chipNumeral I.XI.tabs[t].chip).getD 0 = numOf I.d (sigmaX I.XI t)) :
    HopsOK I jDers jMeta ∧ (∀ t, NumOK I.d (sigmaX I.XI t)) ∧ ∀ t : Fin I.XI.tabs.size, I.XI.tabs[t].chip.cons.size ≤ 100000 := by
  have hnum : ∀ t : Fin I.XI.tabs.size, chipNumeral I.XI.tabs[t].chip = some (numOf I.d (sigmaX I.XI t)) := by
    intro t
    have h1 : (chipNumeral I.XI.tabs[t].chip).isSome = true := by
      unfold chipsOk at hc
      exact Array.all_eq_true.mp hc t.1 t.2
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h1
    have := hnum0 t
    rw [hk] at this ⊢
    simpa [Option.getD] using congrArg some this
  obtain ⟨t1, t2, t3, t4, w1, w9, w25, w42, w48, w174, q1, q2⟩ := LT
  have key : ∀ t : Fin I.XI.tabs.size, (HopZero I.XI.tabs[t].chip (DOf I.d (sigmaX I.XI t)) jDers jMeta I.XI.tabs[t].chip.baseCols ∧
      I.XI.tabs[t].chip.baseCols = bcOf (sigmaX I.XI t)) ∧ NumOK I.d (sigmaX I.XI t) ∧ I.XI.tabs[t].chip.cons.size ≤ 100000 := by
    intro t
    have hmem := (ids_of_shape I.hsh).2 _ (Array.getElem_mem_toList t.2)
    obtain ⟨lit, hlit, hE⟩ := num_find _ _ (hnum t)
    have hn := hnum t
    have hs : sigmaX I.XI t = tabIdx I.XI.tabs[t].chip.id := rfl
    generalize I.XI.tabs[t].chip = c at *
    rw [hs] at hn hlit ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hid | hid | hid | hid | hid | hid <;> rw [hid] at hlit hn ⊢
    · simp [expectedOf] at hlit
      obtain ⟨hk, rfl⟩ := hlit
      refine ⟨hop_of computeSpec chipCompute c 69 rfl t1 hE, ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
      rw [chipEqB_size c _ hE]; decide +kernel
    · simp [expectedOf] at hlit
      obtain ⟨hk, rfl⟩ := hlit
      refine ⟨hop_of cellKWSpec chipCell c 134 rfl t2 hE, ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
      rw [chipEqB_size c _ hE]; decide +kernel
    · have e : DOf I.d (tabIdx "walkChipJ8") = emitDag (walkJ8SpecAt I.d.Pb.kroots) := rfl
      have e2 : bcOf (tabIdx "walkChipJ8") = 25 := rfl
      rw [e, e2]
      simp (config := {decide := true}) [expectedOf, numOf, tabIdx] at hlit hn
      rcases hlit with ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩
      · rw [hk]
        refine ⟨hop_of (walkJ8SpecAt 1) chipWalkJ8_1 c 25 rfl w1 hE, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide)⟩, ?_⟩
        rw [chipEqB_size c _ hE]; decide +kernel
      · rw [hk]
        refine ⟨hop_of (walkJ8SpecAt 9) chipWalkJ8_9 c 25 rfl w9 hE, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide)⟩, ?_⟩
        rw [chipEqB_size c _ hE]; decide +kernel
      · rw [hk]
        refine ⟨hop_of (walkJ8SpecAt 25) chipWalkJ8_25 c 25 rfl w25 hE, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide)⟩, ?_⟩
        rw [chipEqB_size c _ hE]; decide +kernel
      · rw [hk]
        refine ⟨hop_of (walkJ8SpecAt 42) chipWalkJ8_42 c 25 rfl w42 hE, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide)⟩, ?_⟩
        rw [chipEqB_size c _ hE]; decide +kernel
      · rw [hk]
        refine ⟨hop_of (walkJ8SpecAt 48) chipWalkJ8_48 c 25 rfl w48 hE, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide)⟩, ?_⟩
        rw [chipEqB_size c _ hE]; decide +kernel
      · rw [hk]
        refine ⟨hop_of (walkJ8SpecAt 174) chipWalkJ8_174 c 25 rfl w174 hE, ⟨fun _ => by rw [hk]; decide, fun h => absurd h (by decide)⟩, ?_⟩
        rw [chipEqB_size c _ hE]; decide +kernel
    · simp [expectedOf] at hlit
      obtain ⟨hk, rfl⟩ := hlit
      refine ⟨hop_of atomSpec chipAtom c 205 rfl t3 hE, ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
      rw [chipEqB_size c _ hE]; decide +kernel
    · have e : DOf I.d (tabIdx "walkChipHQK") = emitDag (walkAtomSpecAt I.d.Pb.krootsV) := rfl
      have e2 : bcOf (tabIdx "walkChipHQK") = 25 := rfl
      rw [e, e2]
      simp (config := {decide := true}) [expectedOf, numOf, tabIdx] at hlit hn
      rcases hlit with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
      · rw [hk]
        refine ⟨hop_of (walkAtomSpecAt 1) chipWalkHQK_1 c 25 rfl q1 hE, ⟨fun h => absurd h (by decide), fun _ => by rw [hk]; decide⟩, ?_⟩
        rw [chipEqB_size c _ hE]; decide +kernel
      · rw [hk]
        refine ⟨hop_of (walkAtomSpecAt 2) chipWalkHQK_2 c 25 rfl q2 hE, ⟨fun h => absurd h (by decide), fun _ => by rw [hk]; decide⟩, ?_⟩
        rw [chipEqB_size c _ hE]; decide +kernel
    · simp [expectedOf] at hlit
      obtain ⟨hk, rfl⟩ := hlit
      refine ⟨hop_of jetSpec chipJet c 29 rfl t4 hE, ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, ?_⟩
      rw [chipEqB_size c _ hE]; decide +kernel
  exact ⟨fun t => (key t).1, fun t => (key t).2.1, fun t => (key t).2.2⟩


theorem tabs_le6 (I : Inst) : I.XI.tabs.size ≤ 6 := by
  obtain ⟨hnd, hmem⟩ := ids_of_shape I.hsh
  have hsub : (I.XI.tabs.toList.map (·.chip.id)) ⊆ ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8"] := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    exact hmem t ht
  have := (hnd.subperm hsub).length_le
  simpa using this

theorem ns_le (I : Inst) (hsz : ∀ t : Fin I.XI.tabs.size, I.XI.tabs[t].chip.cons.size ≤ 100000) : nsK I.XI ≤ 2 ^ 20 := by
  unfold nsK
  have h6 := tabs_le6 I
  have : (sizes I.XI).sum ≤ (sizes I.XI).length • 100000 := by
    apply List.sum_le_card_nsmul
    intro x hx
    unfold sizes at hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    exact hsz ⟨i, by simpa using hi⟩
  rw [sizes_length] at this
  simp only [smul_eq_mul] at this
  nlinarith


/-! ## 2. `hSlotOK`: the loader's `jDers`/`jMeta` slot map is the audited challenge vector -/

theorem order_find : ∀ i : ℕ, i < 19 → (NockvmE2E.Exec.VC.orderOf jMeta).findIdx? (· == i) = some (J8Shape.slotOfJ8[i]!) := by decide +kernel
theorem order_none : ∀ i : ℕ, i < 22 → (NockvmE2E.Exec.VC.orderOf jMeta).findIdx? (· == 19 + i) = none := by decide +kernel
theorem ders_find : ∀ m : ℕ, m < 22 → (match jDers.find? (·.slot == 19 + m) with
    | some d => d.re == 4 && d.im == 6 && d.power == m / 2 && d.isRe == decide (m % 2 = 0)
    | none => false) = true := by decide +kernel
theorem idx4 : (NockvmE2E.Exec.VC.orderOf jMeta).findIdx? (· == 4) = some 15 := by decide +kernel
theorem idx6 : (NockvmE2E.Exec.VC.orderOf jMeta).findIdx? (· == 6) = some 17 := by decide +kernel

theorem chalK_coin (χ : Coins Φ0 KC) (i : ℕ) (hi : i < 19) : chalK Φ0 sl0X sl1X χ J8Shape.slotOfJ8[i]! = χ ⟨i, hi⟩ := by
  have hq := slot_tab ⟨i, hi⟩
  have hcoin := InstJ8.hcoin0 ⟨i, hi⟩
  have hor : Φ0.sampledAfter ⟨i, hi⟩ = 0 ∨ Φ0.sampledAfter ⟨i, hi⟩ = 1 := by omega
  unfold chalK
  rcases hor with h | h
  · have hlt : J8Shape.slotOfJ8[i]! < 13 := hq.1 h
    rw [dif_pos hlt]
    have h0 : (extFrame Φ0 2).sampledAfter (extC Φ0 2 ⟨i, hi⟩) = 0 := by rw [sa_ext]; exact h
    have e : sl0X.symm ⟨J8Shape.slotOfJ8[i]!, hlt⟩ = ⟨extC Φ0 2 ⟨i, hi⟩, h0⟩ :=
      (Equiv.symm_apply_eq _).2 (Fin.ext (sl0X_val ⟨i, hi⟩ h0)).symm
    congr 1
    apply Fin.ext
    simp only [e, extC]
  · have hge : 13 ≤ J8Shape.slotOfJ8[i]! ∧ J8Shape.slotOfJ8[i]! < 19 := hq.2 h
    rw [dif_neg (by omega), dif_pos (by omega)]
    have h1 : (extFrame Φ0 2).sampledAfter (extC Φ0 2 ⟨i, hi⟩) = 1 := by rw [sa_ext]; exact h
    have e : sl1X.symm ⟨J8Shape.slotOfJ8[i]! - 13, by omega⟩ = ⟨extC Φ0 2 ⟨i, hi⟩, h1⟩ :=
      (Equiv.symm_apply_eq _).2 (Fin.ext (sl1X_val ⟨i, hi⟩ h1)).symm
    congr 1
    apply Fin.ext
    simp only [e, extC]

theorem chalE_coin (χ : Coins Φ0 KC) (i : ℕ) (hi : i < 19) :
    NockvmE2E.Exec.DagSemV.chalE jDers jMeta (chalK Φ0 sl0X sl1X χ) i = χ ⟨i, hi⟩ := by
  unfold NockvmE2E.Exec.DagSemV.chalE
  simp only []
  rw [order_find i hi]
  exact chalK_coin χ i hi

theorem slotOK_X (χ : Coins Φ0 KC) :
    NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE jDers jMeta (chalK Φ0 sl0X sl1X χ)) (NockvmE2E.J8.TieJ8.χf χ) := by
  refine ⟨fun i hi => ?_, fun m hm => ?_⟩
  · rw [chalE_coin χ i hi]; simp [NockvmE2E.J8.TieJ8.χf, hi]
  · have h4 : chalK Φ0 sl0X sl1X χ 15 = χ ⟨4, by decide⟩ := chalK_coin χ 4 (by decide)
    have h6 : chalK Φ0 sl0X sl1X χ 17 = χ ⟨6, by decide⟩ := chalK_coin χ 6 (by decide)
    have hf := ders_find m hm
    unfold NockvmE2E.Exec.DagSemV.chalE
    simp only []
    rw [order_none m hm]
    cases hd : jDers.find? (·.slot == 19 + m) with
    | none => rw [hd] at hf; simp at hf
    | some d =>
      rw [hd] at hf
      simp only [Bool.and_eq_true, beq_iff_eq, ] at hf
      obtain ⟨⟨⟨hre, him⟩, hpw⟩, hisre⟩ := hf
      simp only [hre, him, idx4, idx6, hpw, Option.getD, h4, h6]
      have e4 : NockvmE2E.J8.TieJ8.χf χ 4 = χ ⟨4, by decide⟩ := by simp [NockvmE2E.J8.TieJ8.χf]; rfl
      have e6 : NockvmE2E.J8.TieJ8.χf χ 6 = χ ⟨6, by decide⟩ := by simp [NockvmE2E.J8.TieJ8.χf]; rfl
      rw [e4, e6, hisre]
      by_cases hm2 : m % 2 = 0 <;> simp [hm2]


/-! ## 3. the datum-side fact `hat` (atoms are canonical) from `StmtP` and the datum link -/

theorem hat_of (d : InstJ8.Datum) (inp : PE.PubIn) (hS : InstJ8.StmtP d) (hlink : NockvmE2E.J8.RVUJ8.InpLink d inp) :
    ∀ a ∈ inp.atoms, a.2 < NockvmE2E.Exec.p := by
  intro a ha
  rw [hlink.hat] at ha
  obtain ⟨k, -, hk⟩ := List.mem_filterMap.mp ha
  cases hc : Nock.NockVMROM.Thm54.VclL.Handle.FrameVS.claimNoun d.c k with
  | cell _ _ => simp [hc] at hk
  | atom v =>
    simp only [hc, Option.some.injEq] at hk
    subst hk
    exact hS.hclA k v hc

/-! ## 4. `exec_e2e_J8F` -/

namespace F
open NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM
open NockvmE2E.Exec.E2EJ8 NockvmE2E.Exec.E2EJ8.J8X
open NockvmE2E.J8.InstJ8 (Datum DatumOK J8 PbOfX PosX posX_of_shape hNof ω0 StmtP PubP)
open NockvmE2E.J8.TieJ8G (Inst HopsOK NumOK RdSpec Gflat hsz_of_hops gbJ hdagU_J8 hoff_J8 hdom_J8 colJ pubJ chalK)
open NockvmE2E.J8.InstJ8W (sigmaX RJ8 hfree_J8)
open NockvmE2E.Exec.MaskOk (maskOk)

variable (XI0 : ExecInst) (hsh : J8Shape.j8ShapeOk (XI170 XI0) = true) (hshX : J8Shape.j8ShapeXOk (XI170 XI0) = true)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD (J8Shape.hn32_of_shape hsh)
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable [SampleableType KC]
variable (D : DatX (XI170 XI0) hsh) (hdk : DatumOK D.d)
variable (R : TabRestr (J8 D.d hdk)) (hT : R.T' = (XI170 XI0).tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigmaX (XI170 XI0) (Fin.cast hT t)) (hfree : (J8 D.d hdk).AccOn R.q)

set_option hygiene false in
local notation "IX" => (⟨XI170 XI0, hsh, posX_of_shape hsh, D.kroots, D.krootsV, D.Rt, D.regs, D.ids, D.idx, D.rk, D.lay, D.d, D.hd,
  hdk, D.hdN, D.hdω, R, hT, hσ, hfree⟩ : Inst)

set_option hygiene false in
local notation "npubV" => (XI170 XI0).pubOf.size
set_option hygiene false in
local notation "hcapV" => hcap_of_shapeX IX (XI170 XI0).pubOf.size rfl hshX

variable (tp : Fin (IX).Jm.T)

set_option hygiene false in
local notation "JXn" => (IX).JJ (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "prV" => prX IX (XI170 XI0).pubOf.size tp hcapV

/- the executed chip check and the datum numerals (labels in the ledger at the end) -/
variable (hchips : chipsOk (XI170 XI0) = true)
  (hnum0 : ∀ t : Fin (XI170 XI0).tabs.size,
    (chipNumeral (XI170 XI0).tabs[t].chip).getD 0 = numOf D.d (sigmaX (XI170 XI0) t))

set_option hygiene false in
local notation "hd1" => ((J8Shape.d_of_shape hsh).symm : (1 : ℕ+).val = (XI170 XI0).d)
set_option hygiene false in
local notation "hNHV" => hNH_X IX (XI170 XI0).pubOf.size tp hcapV 1 hd1
set_option hygiene false in
local notation "hpdV" => hpd_X IX (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "hopsV" => (hops_of_chips IX hchips litTies hnum0).1
set_option hygiene false in
local notation "hnumV" => (hops_of_chips IX hchips litTies hnum0).2.1
set_option hygiene false in
local notation "GX" => Gflat IX (hsz_of_hops IX jDers jMeta hnumV hopsV)
set_option hygiene false in
local notation "PJ" => (deepParamsJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV).regroup GX gbJ
set_option hygiene false in
local notation "AJ" => (airJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV).regroup GX gbJ
set_option hygiene false in
local notation "R0P" => R0J JXn prV ωS (31 / 64) (friBound s1 1)
set_option hygiene false in
local notation "RestP" => RestJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV
set_option hygiene false in
local notation "RestVP" => RestVJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV
set_option hygiene false in
local notation "cIV" => cIX IX (XI170 XI0).pubOf.size tp hcapV rfl
set_option hygiene false in
local notation "mV" => (XI170 XI0).nc * (JXn).r + (PJ).nq - 1

theorem hmV_X : mV + 1 = (XI170 XI0).nc * (JXn).r + (PJ).nq := by
  have h9 : (PJ).nq = 9 := rfl
  have : (JXn).r = 2 := rfl
  omega

set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cIV (JXn).r (hmV_X XI0 hsh hshX D hdk R hT hσ hfree tp hchips hnum0)

variable [DecidableEq ((PJ).statement (R0P) (RestP)).M0] [Finite ((PJ).statement (R0P) (RestP)).M0]
  [DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)

set_option hygiene false in
local notation "HNQ" => ((nq_of_shapeX hshX).trans rfl : (XI170 XI0).nq = (PJ).nq)
set_option hygiene false in
local notation "HBLK" => hblk_of_shapeX IX (XI170 XI0).pubOf.size tp hcapV rfl hshX
set_option hygiene false in
local notation "HBLKQ" => hblkq_X IX (PJ).nq (HNQ).ge
set_option hygiene false in
local notation "MDV" => mdX (XI170 XI0) (J8Shape.hn1_of_shape hsh) (PJ).colRoundX
  (rkP (XI170 XI0) (PJ) rfl HNQ cIV HBLK HBLKQ) toyEncB
set_option hygiene false in
local notation "LV" => LX (XI170 XI0) (J8Shape.hn32_of_shape hsh)

set_option hygiene false in
local notation "MC" => msC (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 4 s1 1 (XI170 XI0).l DgJ8 encK MDV LV (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask (extFrame (JXn).Φ0 2) KC (MDV).toRapMaskData ((PJ).statement (R0P) (RestP)).M0
  (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 1 (XI170 XI0).l DgJ8 encK LV
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))
set_option hygiene false in
local notation "DA" => daOf (XI170 XI0) (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin DgJ8 MDV cIV sl0X sl1X
  (PJ).ha (PJ).hz
  (single_az (XI170 XI0) JXn prV (ω := ωS) (31 / 64) (friBound s1 1) hNHV hpdV).1
  (single_az (XI170 XI0) JXn prV (ω := ωS) (31 / 64) (friBound s1 1) hNHV hpdV).2 m0 mf
set_option hygiene false in
local notation "EMBF" => fun (π : FlatProof) =>
  embedMsgs dgOf (MC) (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK))
    (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability in
set_option maxHeartbeats 4000000 in
/-- **`exec_e2e_J8F`**: `exec_e2e_J8` with every binder covered by a lemma discharged. The remaining hypotheses, with labels:
  - `hsh`, `hshX`, `hl`: EXECUTED (the verifier exe's shape gates `j8ShapeOk`, `j8ShapeXOk`, and `l = 170`);
  - `hchips`, `hnum0`: EXECUTED chip check (`chipsOk`: each loaded chip equals a literal of `J8Chips`; the 12 literal ties are the theorem `litTies`)
    + DATUM numerals (kroots / krootsV of the datum = numeral of the loaded walk chip);
  - `hmask`, `hnumeralOk`: EXECUTED (`maskOk`, `numeralOk`; the Lagrange bridge is `MaskBridge.hLagr_of`); `hjet`: TCB (the jet's 18 registry columns);
  - `hdk`, `hS`, `hlink`, `hids`: DATUM (`DatumOK`, `StmtP`, `InpLink`, registry ids);
  - `R hT hσ hfree`: the table restriction (instance: `RJ8`, `rfl`, `rfl`, `hfree_J8`, see `inst_RJ8`);
  - `tp`, `I0 I Ifin`, the instances, `encZ decZ hz`, `m0 mf`, the adversary and its bounds: protocol / adversary parameters as in `exec_e2e_final`. -/
theorem exec_e2e_J8F {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [SampleableType (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd)]
    /- [executed] `l = 170` -/
    (hl : XI0.l = 170)
    /- [statement parameters] the statement/salt codec -/
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    /- [datum] the datum satisfies the J-8 side conditions, its claim matches the instance's public input, registry ids are small -/
    (hS : StmtP D.d) (hlink : NockvmE2E.J8.RVUJ8.InpLink D.d (XI170 XI0).pubIn)
    (hids : ∀ id ∈ D.d.Pb.regs, id < NockvmE2E.J8.InstJ8.P)
    /- [executed] `maskOk` and `numeralOk` (both run inside `hop0Check`) -/
    (hmask : maskOk (XI170 XI0) = true) (hnumeralOk : NockvmE2E.Exec.MaskOk.numeralOk (XI170 XI0) = true)
    /- [TCB] the jet's 18 registry fixed columns (`hpreJet`; not covered by `maskOk`) -/
    (hjet : ∀ t : Fin (XI170 XI0).tabs.size, (XI170 XI0).tabs[t].chip.id = "jetChipJ8" →
      ∀ c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub → (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 1 →
        NockvmE2E.Exec.MaskBridge.LagrAt IX (XI170 XI0).pubOf.size tp hcapV t c)
    /- [adversary] as in `exec_e2e_final` -/
    (Aflat : OracleComp (SuccinctSpecK DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC))
      (Option (Statement × Salt × FlatProof × W)))
    (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hFS : FsBound (Q := NQuery (merkleSkels (MC))) (∅ : (ofFn (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))).QueryCache)
      Q_FS (verifiedFS (trueGuards _) (embedAdv DgJ8 EMBF Aflat)))
    (hHq : IsQueryBoundP (embedAdv DgJ8 EMBF Aflat)
      (@isHashQuery (NQuery (merkleSkels (MC))) DgJ8 _ (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))) Q_H)
    (hterm : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (MC)).length) (op : OPN)
      (logs : Fin (merkleSkels (MC)).length → MerkleTreeExtractor.QueryLog (NQuery (merkleSkels (MC))) DgJ8),
      claimsQueryCount (mkClaims (merkleSkels (MC)) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn) :
    Pr{let g ← $ᵗ (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) dd);
       let o ← simulateQ (withTable g) Aflat}[
      match o with
      | none => False
      | some (z, salt, π, _) =>
        AccF XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV encZ decZ
          (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK)) g (z, salt) π ∧ ¬ Nock.Jet.HoldsN D.d.c] ≤
      (2 ^ 82 : ℝ≥0∞)⁻¹ := by
  have hrate := hrate_X hsh 1 hd1
  exact exec_e2e_J8 XI0 (J8Shape.hn32_of_shape hsh) hsh D hdk R hT hσ hfree (XI170 XI0).pubOf.size tp hcapV prV 1 hNHV hpdV
    jDers jMeta hnumV hopsV cIV (hmV_X XI0 hsh hshX D hdk R hT hσ hfree tp hchips hnum0) I0 I Ifin encK MDV LV sl0X sl1X m0 mf
    hl encZ decZ hz (nq_of_shapeX hshX) (hkd_X IX) HBLK HBLKQ (hpub_X IX _ tp hcapV rfl) (hppt_X IX _ tp hcapV) (hgen_X IX _ tp hcapV)
    rfl (rdSpec_X IX _ tp hcapV rfl hshX)
    (by rw [(J8Shape.slotOf_of_shape hsh).2]; rfl) (by rw [(J8Shape.slotOf_of_shape hsh).2]; rfl)
    (fun χ => slotOK_X χ) (hcI_col_X IX _ tp hcapV rfl) (hcI_pub_X IX _ tp hcapV rfl) (hpre0_X IX _ tp hcapV)
    (NockvmE2E.Exec.MaskBridge.hLagr_of IX _ tp hcapV hmask hnumeralOk hnum0 hjet)
    (NockvmE2E.Exec.E2EJ8S.hRVU_X_of' (XI0 := XI0) (hn32 := J8Shape.hn32_of_shape hsh) (hsh := hsh) (D := D) (hdk := hdk) (R := R) (hT := hT) (hσ := hσ)
      (hfree := hfree) (npub := (XI170 XI0).pubOf.size) (tp := tp) (hcap := hcapV) (pr := prV) (dF := 1) (hNH := hNHV) (hpd := hpdV)
      (ders := jDers) (cmeta := jMeta) (hnum := hnumV) (hops := hopsV) (cI := cIV)
      (sl0 := sl0X) (sl1 := sl1X)
      (m0 := m0) (mf := mf)
      hS hlink hids (hpJ_X IX hshX) (hpV_X IX hshX hnumV)
      (fun c0 c1 c2 c3 i => hχ_X (XI170 XI0) hsh c0 c1 c2 c3 i)
      (fun c0 c1 c2 c3 vT vQ hV hP => hrd_X IX _ tp hcapV rfl hshX (hat_of D.d _ hS hlink) mf _ _ vT vQ hV hP))
    rfl rfl (J8Shape.d_of_shape hsh).symm encK_ok hrate hF_X
    (htoPoly_X (J8Shape.hn32_of_shape hsh) JXn prV s1 1 hNHV hpdV hrate)
    (ns_le IX (hops_of_chips IX hchips litTies hnum0).2.2) (hD_X (J8Shape.hn32_of_shape hsh) JXn prV s1 1 hNHV hpdV) (hH_X (J8Shape.hn32_of_shape hsh) JXn prV s1 1 hNHV hpdV) hDg_X
    Aflat Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig

end F

end NockvmE2E.Exec.E2EJ8F

#print axioms NockvmE2E.Exec.E2EJ8F.hops_of_chips
#print axioms NockvmE2E.Exec.E2EJ8F.ns_le
#print axioms NockvmE2E.Exec.E2EJ8F.slotOK_X
#print axioms NockvmE2E.Exec.E2EJ8F.F.exec_e2e_J8F

/-
BINDER LEDGER of `exec_e2e_J8F` (LABEL | source)
  executed : hsh (j8ShapeOk), hshX (j8ShapeXOk), hl (l = 170), hchips (chipsOk), hmask (maskOk)
  kernel ties : DISCHARGED (`litTies` from the 12 J8ChipsK.tie_* theorems)
  datum    : hdk (DatumOK), hS (StmtP), hlink (InpLink), hids, hnum0 (datum kroots/krootsV = numeral of the loaded walk chip)
  executed : hnumeralOk;  TCB : hjet (jet registry columns).  hLagr (hLagr_of) and hslots (hRVU_X_of') are DISCHARGED: no pending hypothesis.
  instance : D, R, hT, hσ, hfree (RJ8, rfl, rfl, hfree_J8), tp
  protocol / adversary : I0 I Ifin, instances, m0 mf, encZ decZ hz, Aflat, Q_FS Q_H V Pn and bounds, as in exec_e2e_final
  DISCHARGED here : hnq9 hkd hblk hblkq hpub hppt hgen hnpub hrdT hn0 hn1 hSlotOK (slotOK_X) hcI_col hcI_pub hpre0 hRVU (hRVU_X_of + hrd_X,
    hχ_X, hpJ_X, hpV_X, hat_of) hmd hL hd hEnc hrate hF htoPoly hnsC (ns_le from the literal sizes) hD hH hDg; npub, hcap, pr, cI, m, dF,
    hNH, hpd, ders, cmeta, hnum, hops, enc, md, L, sl0, sl1 (all now terms).
-/
