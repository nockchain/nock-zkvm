/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulGoldilocksResiduals.lean

  Residual suppliers for `nockCompiles_of_grom_atTree_p62` at the 2×2 matmul
  over Goldilocks (`MatmulConfigGoldilocks`).
-/
import Nock.Field
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenCoinCounting
import Nock.NockVMROM.Thm54.TraceGen.GenGenericRowFacts
import Nock.NockVMROM.Thm54.TraceGen.GenGuardedRom
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulHyps
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMem
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.TraceGen.GenServedRoots
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemWeb

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks

/-! ## `evalGRom` is monotone in the guard.

The 2×2 matmul is a ROM program (`mm_evalG` never hits OP10/11).  The
concrete run is discharged by kernel reduction; the lift `97 → Field.p`
is `evalGRom_mod_le`. -/

theorem evalGRom_mod_le {q q' : ℕ} (hqq : q ≤ q') :
    ∀ (fuel : ℕ) (s f r : Noun),
      evalGRom q fuel s f = some r → evalGRom q' fuel s f = some r := by
  intro fuel
  induction fuel with
  | zero => intro s f r h; simp [evalGRom] at h
  | succ fuel ih =>
    intro s f r h
    match f with
    | .atom _ => simp [evalGRom] at h
    | .cell (.cell b c) d =>
      simp only [evalGRom] at h ⊢
      cases hbc : evalGRom q fuel s (.cell b c) with
      | none => rw [hbc] at h; simp at h
      | some l =>
        cases hd : evalGRom q fuel s d with
        | none => rw [hbc, hd] at h; simp at h
        | some r' =>
          rw [hbc, hd] at h
          rw [ih s (.cell b c) l hbc, ih s d r' hd]
          exact h
    | .cell (.atom op) tail =>
      match op with
      | 0 | 1 => simpa [evalGRom] using h
      | 2 =>
        match tail with
        | .atom _ => simp [evalGRom] at h
        | .cell b c =>
          simp only [evalGRom] at h ⊢
          cases hb : evalGRom q fuel s b with
          | none => rw [hb] at h; simp at h
          | some sb =>
            cases hc : evalGRom q fuel s c with
            | none => rw [hb, hc] at h; simp at h
            | some sc =>
              rw [hb, hc] at h
              rw [ih s b sb hb, ih s c sc hc]
              exact ih sb sc r h
      | 3 =>
        simp only [evalGRom] at h ⊢
        cases ht : evalGRom q fuel s tail with
        | none => rw [ht] at h; simp at h
        | some v =>
          rw [ht] at h
          rw [ih s tail v ht]
          exact h
      | 4 =>
        simp only [evalGRom] at h ⊢
        cases ht : evalGRom q fuel s tail with
        | none => rw [ht] at h; simp at h
        | some v =>
          rw [ht] at h
          rw [ih s tail v ht]
          exact lusGBy_mod_le hqq h
      | 5 =>
        match tail with
        | .atom _ => simp [evalGRom] at h
        | .cell b c =>
          simp only [evalGRom] at h ⊢
          cases hb : evalGRom q fuel s b with
          | none => rw [hb] at h; simp at h
          | some sb =>
            cases hc : evalGRom q fuel s c with
            | none => rw [hb, hc] at h; simp at h
            | some sc =>
              rw [hb, hc] at h
              rw [ih s b sb hb, ih s c sc hc]
              exact h
      | 6 =>
        match tail with
        | .atom _ => simp [evalGRom] at h
        | .cell _ (.atom _) => simp [evalGRom] at h
        | .cell b (.cell c d) =>
          simp only [evalGRom] at h ⊢
          cases hb : evalGRom q fuel s b with
          | none => rw [hb] at h; simp at h
          | some vb =>
            rw [hb] at h
            rw [ih s b vb hb]
            match vb with
            | .atom 0 => exact ih s c r h
            | .atom 1 => exact ih s d r h
            | .atom (_ + 2) => simp at h
            | .cell _ _ => simp at h
      | 7 =>
        match tail with
        | .atom _ => simp [evalGRom] at h
        | .cell b c =>
          simp only [evalGRom] at h ⊢
          cases hb : evalGRom q fuel s b with
          | none => rw [hb] at h; simp at h
          | some sb =>
            rw [hb] at h
            rw [ih s b sb hb]
            exact ih sb c r h
      | 8 =>
        match tail with
        | .atom _ => simp [evalGRom] at h
        | .cell b c =>
          simp only [evalGRom] at h ⊢
          cases hb : evalGRom q fuel s b with
          | none => rw [hb] at h; simp at h
          | some sb =>
            rw [hb] at h
            rw [ih s b sb hb]
            exact ih (.cell sb s) c r h
      | 9 =>
        match tail with
        | .atom _ => simp [evalGRom] at h
        | .cell (.cell _ _) _ => simp [evalGRom] at h
        | .cell (.atom ax) c =>
          simp only [evalGRom] at h ⊢
          cases hc : evalGRom q fuel s c with
          | none => rw [hc] at h; simp at h
          | some core =>
            rw [hc] at h
            rw [ih s c core hc]
            cases hslot : Noun.slot ax core with
            | none => simp [hslot] at h
            | some arm =>
              simp [hslot] at h ⊢
              exact ih core arm r h
      | _ + 10 => simp [evalGRom] at h

/-! ## Guarded-ROM combinators (evalGBy twins) and the 97-run. -/
theorem evalGRom_s0_exact {q fuel axis : ℕ} {subject result : Noun}
    (hslot : Noun.slot axis subject = some result) :
    evalGRom q (fuel + 1) subject (.cell (.atom 0) (.atom axis)) =
      some result := by
  simpa only [evalGRom] using hslot

theorem evalGRom_s1_exact (q fuel : ℕ) (subject result : Noun) :
    evalGRom q (fuel + 1) subject (.cell (.atom 1) result) =
      some result := by
  rfl

theorem evalGRom_s4_exact {q fuel : ℕ} {subject tail value result : Noun}
    (hcall : evalGRom q fuel subject tail = some value)
    (hinc : FieldEmbedding.lusGBy q value = some result) :
    evalGRom q (fuel + 1) subject (.cell (.atom 4) tail) =
      some result := by
  simp only [evalGRom, hcall, Option.bind_some]
  exact hinc

theorem evalGRom_s5_exact {q fuel : ℕ} {subject left right leftResult rightResult : Noun}
    (hleft : evalGRom q fuel subject left = some leftResult)
    (hright : evalGRom q fuel subject right = some rightResult) :
    evalGRom q (fuel + 1) subject
      (.cell (.atom 5) (.cell left right)) =
      some (Noun.tis leftResult rightResult) := by
  simp only [evalGRom, hleft, hright]

theorem evalGRom_s6_zero_exact {q fuel : ℕ}
    {subject condition yesBranch noBranch result : Noun}
    (hcondition : evalGRom q fuel subject condition = some (.atom 0))
    (hbranch : evalGRom q fuel subject yesBranch = some result) :
    evalGRom q (fuel + 1) subject
      (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch))) =
      some result := by
  simp only [evalGRom, hcondition]
  exact hbranch

theorem evalGRom_s6_one_exact {q fuel : ℕ}
    {subject condition yesBranch noBranch result : Noun}
    (hcondition : evalGRom q fuel subject condition = some (.atom 1))
    (hbranch : evalGRom q fuel subject noBranch = some result) :
    evalGRom q (fuel + 1) subject
      (.cell (.atom 6) (.cell condition (.cell yesBranch noBranch))) =
      some result := by
  simp only [evalGRom, hcondition]
  exact hbranch

theorem evalGRom_s7_exact {q fuel : ℕ}
    {subject first second intermediate result : Noun}
    (hfirst : evalGRom q fuel subject first = some intermediate)
    (hsecond : evalGRom q fuel intermediate second = some result) :
    evalGRom q (fuel + 1) subject
      (.cell (.atom 7) (.cell first second)) = some result := by
  simp only [evalGRom, hfirst]
  exact hsecond

theorem evalGRom_s9_exact {q fuel axis : ℕ}
    {subject coreFormula core arm result : Noun}
    (hcore : evalGRom q fuel subject coreFormula = some core)
    (hslot : Noun.slot axis core = some arm)
    (harm : evalGRom q fuel core arm = some result) :
    evalGRom q (fuel + 1) subject
      (.cell (.atom 9) (.cell (.atom axis) coreFormula)) = some result := by
  simp only [evalGRom, hcore, hslot]
  exact harm

theorem evalGRom_cons_exact {q fuel : ℕ}
    {subject headLeft headRight tail leftResult rightResult : Noun}
    (hleft : evalGRom q fuel subject (.cell headLeft headRight) =
      some leftResult)
    (hright : evalGRom q fuel subject tail = some rightResult) :
    evalGRom q (fuel + 1) subject
      (.cell (.cell headLeft headRight) tail) =
      some (.cell leftResult rightResult) := by
  simp only [evalGRom, hleft, hright]

theorem evalGRom_succ {q fuel : ℕ} {subject formula result : Noun}
    (h : evalGRom q fuel subject formula = some result) :
    evalGRom q (fuel + 1) subject formula = some result := by
  induction fuel, subject, formula using evalGRom.induct q
      generalizing result with
  | case11 fuel subject tail ih =>
      simp only [evalGRom, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subject tail ih =>
      simp only [evalGRom, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ => simp_all [evalGRom]

theorem evalGRom_mono {q n m : ℕ} {subject formula result : Noun}
    (hnm : n ≤ m)
    (h : evalGRom q n subject formula = some result) :
    evalGRom q m subject formula = some result := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact evalGRom_succ ih

theorem evalGRom_quote (q fuel : ℕ) (subject result : Noun) :
    evalGRom q (fuel + 1) subject (quote result) = some result :=
  evalGRom_s1_exact q fuel subject result

theorem evalGRom_op1 (q fuel : ℕ) (subject : Noun) (k : ℕ) :
    evalGRom q (fuel + 1) subject (op1 k) = some (.atom k) :=
  evalGRom_s1_exact q fuel subject (.atom k)

theorem evalGRom_op0 (q n axis : ℕ) {subject result : Noun}
    (h : Noun.slot axis subject = some result) :
    evalGRom q (n + 1) subject (op0 axis) = some result :=
  evalGRom_s0_exact h

theorem evalGRom_op4 (q n : ℕ) {subject tail value result : Noun}
    (hcall : evalGRom q n subject tail = some value)
    (hinc : FieldEmbedding.lusGBy q value = some result) :
    evalGRom q (n + 1) subject (op4 tail) = some result :=
  evalGRom_s4_exact hcall hinc

theorem evalGRom_op5 (q n : ℕ) {subject b c rb rc : Noun}
    (hb : evalGRom q n subject b = some rb)
    (hc : evalGRom q n subject c = some rc) :
    evalGRom q (n + 1) subject (op5 b c) = some (Noun.tis rb rc) :=
  evalGRom_s5_exact hb hc

theorem evalGRom_op6_zero (q n : ℕ) {subject b c d result : Noun}
    (hb : evalGRom q n subject b = some (.atom 0))
    (hc : evalGRom q n subject c = some result) :
    evalGRom q (n + 1) subject (op6 b c d) = some result :=
  evalGRom_s6_zero_exact hb hc

theorem evalGRom_op6_one (q n : ℕ) {subject b c d result : Noun}
    (hb : evalGRom q n subject b = some (.atom 1))
    (hd : evalGRom q n subject d = some result) :
    evalGRom q (n + 1) subject (op6 b c d) = some result :=
  evalGRom_s6_one_exact hb hd

theorem evalGRom_op7 (q n : ℕ) {subject b c sb result : Noun}
    (hb : evalGRom q n subject b = some sb)
    (hc : evalGRom q n sb c = some result) :
    evalGRom q (n + 1) subject (op7 b c) = some result :=
  evalGRom_s7_exact hb hc

theorem evalGRom_op9 (q n axis : ℕ) {subject c core arm result : Noun}
    (hc : evalGRom q n subject c = some core)
    (hslot : Noun.slot axis core = some arm)
    (harm : evalGRom q n core arm = some result) :
    evalGRom q (n + 1) subject
      (.cell (.atom 9) (.cell (.atom axis) c)) = some result :=
  evalGRom_s9_exact hc hslot harm

theorem evalGRom_cons (q fuel : ℕ)
    {subject leftHead leftTail tail leftResult rightResult : Noun}
    (hleft : evalGRom q fuel subject (.cell leftHead leftTail) =
      some leftResult)
    (hright : evalGRom q fuel subject tail = some rightResult) :
    evalGRom q (fuel + 1) subject
      (.cell (.cell leftHead leftTail) tail) =
      some (.cell leftResult rightResult) :=
  evalGRom_cons_exact hleft hright

theorem evalGRom_invokeAxis (q n axis : ℕ) {subject core arm result : Noun}
    (hslot1 : Noun.slot 1 subject = some core)
    (hslotA : Noun.slot axis core = some arm)
    (harm : evalGRom q (n + 2) core arm = some result) :
    evalGRom q (n + 3) subject (invokeAxis axis) = some result := by
  have hcore : evalGRom q (n + 2) subject (op0 1) = some core :=
    evalGRom_op0 q (n + 1) 1 hslot1
  exact evalGRom_s9_exact (fuel := n + 2) hcore hslotA harm

/-- `slam batteryF sampleF axis` against `subject`, when `batteryF` is a cell. -/
theorem evalGRom_slam (q fuel : ℕ)
    {subject bHead bTail sampleF battery sample arm result : Noun} {axis : ℕ}
    (hb : evalGRom q (fuel + 3) subject (.cell bHead bTail) =
      some battery)
    (hs : evalGRom q (fuel + 3) subject sampleF = some sample)
    (hslot : Noun.slot axis (.cell battery sample) = some arm)
    (harm : evalGRom q (fuel + 3) (.cell battery sample) arm =
      some result) :
    evalGRom q (fuel + 5) subject
      (slam (.cell bHead bTail) sampleF axis) = some result := by
  have hcons : evalGRom q (fuel + 4) subject
      (.cell (.cell bHead bTail) sampleF) = some (.cell battery sample) :=
    evalGRom_cons q (fuel + 3) hb hs
  have hax : evalGRom q (fuel + 4) (.cell battery sample)
      (invokeAxis axis) = some result :=
    evalGRom_invokeAxis (q := q) (n := fuel + 1) (axis := axis)
      (slot_1 _) hslot harm
  exact evalGRom_op7 q (fuel + 4) hcons hax

/-! ## Add-arm evaluation -/

theorem evalGRom_addArm_done (q n : ℕ) (acc m : Noun) :
    evalGRom q (n + 6) (addCore acc m m) addArm = some acc := by
  have h14 := evalGRom_op0 q (n + 3) 14 (addCore_slot14 acc m m)
  have h15 := evalGRom_op0 q (n + 3) 15 (addCore_slot15 acc m m)
  have hcond := evalGRom_op5 q (n + 4) h14 h15
  have htis : Noun.tis m m = .atom 0 := tis_self m
  rw [htis] at hcond
  have hthen := evalGRom_op0 q (n + 4) 6 (addCore_slot6 acc m m)
  simpa [addArm] using evalGRom_op6_zero q (n + 5) hcond hthen

theorem evalGRom_addNewSample (n acc i m : ℕ) (hacc : acc + 1 < 97) (hi : i + 1 < 97) :
    evalGRom 97 (n + 5) (addCore (.atom acc) (.atom i) (.atom m)) addNewSample =
      some (.cell (.atom (acc + 1)) (.cell (.atom (i + 1)) (.atom m))) := by
  have h6 := evalGRom_op0 97 (n + 2) 6 (addCore_slot6 (.atom acc) (.atom i) (.atom m))
  have h14 := evalGRom_op0 97 (n + 1) 14 (addCore_slot14 (.atom acc) (.atom i) (.atom m))
  have h15 := evalGRom_op0 97 (n + 2) 15 (addCore_slot15 (.atom acc) (.atom i) (.atom m))
  have hincA := evalGRom_op4 97 (n + 3) h6 (lusG_succ hacc)
  have hincI := evalGRom_op4 97 (n + 2) h14 (lusG_succ hi)
  have hinner := evalGRom_cons 97 (n + 3) hincI h15
  exact evalGRom_cons 97 (n + 4) hincA hinner

/-- One increment: `i = 0`, `m = 1`. -/
theorem evalGRom_addArm_one (n acc : ℕ) (hacc : acc + 1 < 97) :
    evalGRom 97 (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      some (.atom (acc + 1)) := by
  have h14 := evalGRom_op0 97 (n + 13) 14
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1))
  have h15 := evalGRom_op0 97 (n + 13) 15
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1))
  have hcond := evalGRom_op5 97 (n + 14) h14 h15
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  have hns := evalGRom_addNewSample (n + 8) acc 0 1 hacc (by decide)
  have hbatt := evalGRom_op0 97 (n + 12) 2
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
  have hdone := evalGRom_addArm_done 97 (n + 7) (.atom (acc + 1)) (.atom 1)
  have hslam := evalGRom_slam (q := 97) (fuel := n + 10)
    (subject := addCore (.atom acc) (.atom 0) (.atom 1))
    (bHead := .atom 0) (bTail := .atom 2) (sampleF := addNewSample)
    (battery := addArm)
    (sample := .cell (.atom (acc + 1)) (.cell (.atom 1) (.atom 1)))
    (axis := 2) (arm := addArm) (result := .atom (acc + 1))
    hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1))
    hdone
  simpa [addArm, slam, op0] using evalGRom_op6_one 97 (n + 15) hcond hslam

theorem evalGRom_macArm_done (q fuel : ℕ) (acc n m : Noun) :
    evalGRom q (fuel + 6) (macCoreAt acc n n m) macArm = some acc := by
  have h14 := evalGRom_op0 q (fuel + 3) 14 (macCoreAt_slot14 acc n n m)
  have h30 := evalGRom_op0 q (fuel + 3) 30 (macCoreAt_slot30 acc n n m)
  have hcond := evalGRom_op5 q (fuel + 4) h14 h30
  rw [tis_self n] at hcond
  have hthen := evalGRom_op0 q (fuel + 4) 6 (macCoreAt_slot6 acc n n m)
  simpa [macArm] using evalGRom_op6_zero q (fuel + 5) hcond hthen

theorem evalGRom_macArm_zero (q fuel : ℕ) (acc m : Noun) :
    evalGRom q (fuel + 6) (macCore acc (.atom 0) m) macArm = some acc :=
  evalGRom_macArm_done q fuel acc (.atom 0) m

/-- Sample formula `[accF [0 [nF mF]]]` with cell-headed `accF`/`nF`. -/
theorem evalGRom_macSampleF (q fuel : ℕ)
    {subject aH aT nH nT mF acc n m : Noun}
    (ha : evalGRom q (fuel + 2) subject (.cell aH aT) = some acc)
    (hn : evalGRom q fuel subject (.cell nH nT) = some n)
    (hm : evalGRom q fuel subject mF = some m) :
    evalGRom q (fuel + 3) subject
      (.cell (.cell aH aT) (.cell (op1 0) (.cell (.cell nH nT) mF))) =
      some (.cell acc (.cell (.atom 0) (.cell n m))) := by
  have hnm := evalGRom_cons q fuel hn hm
  have hz := evalGRom_op1 q fuel subject 0
  have hinner := evalGRom_cons q (fuel + 1) hz hnm
  exact evalGRom_cons q (fuel + 2) ha hinner

theorem evalGRom_invokeMac (q fuel : ℕ)
    {subject aH aT nH nT mF acc n m result : Noun}
    (ha : evalGRom q (fuel + 2) subject (.cell aH aT) = some acc)
    (hn : evalGRom q fuel subject (.cell nH nT) = some n)
    (hm : evalGRom q fuel subject mF = some m)
    (harm : evalGRom q (fuel + 3) (macCore acc n m) macArm =
      some result) :
    evalGRom q (fuel + 5) subject
      (invokeMac (.cell aH aT) (.cell nH nT) mF) = some result := by
  have hqB := evalGRom_quote q (fuel + 2) subject mmBattery
  have hsf := evalGRom_macSampleF q fuel ha hn hm
  have hslot := macCoreAt_slot4 acc (.atom 0) n m
  simpa [invokeMac, slam, quote, macCore, macCoreAt, macSample] using
    evalGRom_slam (q := q) (fuel := fuel)
      (bHead := .atom 1) (bTail := mmBattery)
      hqB hsf hslot harm

theorem evalGRom_addFromMac_m0 (fuel acc : ℕ) :
    evalGRom 97 (fuel + 12)
      (macCore (.atom acc) (.atom 1) (.atom 0)) addFromMac = some (.atom acc) := by
  have h5 := evalGRom_op0 97 (fuel + 9) 5
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hacc := evalGRom_op0 97 (fuel + 8) 6
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hz := evalGRom_op1 97 (fuel + 7)
    (macCore (.atom acc) (.atom 1) (.atom 0)) 0
  have hm := evalGRom_op0 97 (fuel + 7) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinner := evalGRom_cons 97 (fuel + 8) hz hm
  have hsmpl := evalGRom_cons 97 (fuel + 9) hacc hinner
  have hadd := evalGRom_addArm_done 97 (fuel + 4) (.atom acc) (.atom 0)
  simpa [addFromMac, slam, op0, op1, macCore] using
    evalGRom_slam (q := 97) (fuel := fuel + 7)
      (bHead := .atom 0) (bTail := .atom 5)
      h5 hsmpl
      (addCore_slot2 (.atom acc) (.atom 0) (.atom 0))
      hadd

/-- Inner add slammed from a MAC core: `m = 1` so `add` takes one increment. -/
theorem evalGRom_addFromMac_m1 (fuel acc : ℕ) (hacc : acc + 1 < 97) :
    evalGRom 97 (fuel + 21)
      (macCore (.atom acc) (.atom 1) (.atom 1)) addFromMac =
      some (.atom (acc + 1)) := by
  have h5 := evalGRom_op0 97 (fuel + 18) 5
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have haccS := evalGRom_op0 97 (fuel + 17) 6
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hz := evalGRom_op1 97 (fuel + 16)
    (macCore (.atom acc) (.atom 1) (.atom 1)) 0
  have hm := evalGRom_op0 97 (fuel + 16) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinner := evalGRom_cons 97 (fuel + 17) hz hm
  have hsmpl := evalGRom_cons 97 (fuel + 18) haccS hinner
  have hadd := evalGRom_addArm_one (fuel + 3) acc hacc
  simpa [addFromMac, slam, op0, op1, macCore] using
    evalGRom_slam (q := 97) (fuel := fuel + 16)
      (bHead := .atom 0) (bTail := .atom 5)
      h5 hsmpl
      (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
      hadd

/-- `macNewSample` after one MAC trip with `m = 0`. -/
theorem evalGRom_macNewSample_m0 (fuel acc : ℕ) :
    evalGRom 97 (fuel + 14)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample =
      some (.cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0)))) := by
  have hadd := evalGRom_addFromMac_m0 fuel acc
  have h14 := evalGRom_op0 97 (fuel + 10) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinc := evalGRom_op4 97 (fuel + 11) h14 (lusG_succ (n := 0) (by decide))
  have hn := evalGRom_op0 97 (fuel + 10) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hm := evalGRom_op0 97 (fuel + 10) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hnm := evalGRom_cons 97 (fuel + 11) hn hm
  have hrest := evalGRom_cons 97 (fuel + 12) hinc hnm
  exact evalGRom_cons 97 (fuel + 13)
    (evalGRom_mono (q := 97) (show fuel + 12 ≤ fuel + 13 by omega) hadd) hrest

theorem evalGRom_macArm_one_m0 (fuel acc : ℕ) :
    evalGRom 97 (fuel + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = some (.atom acc) := by
  have h14 := evalGRom_op0 97 (fuel + 19) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have h30 := evalGRom_op0 97 (fuel + 19) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hcond := evalGRom_op5 97 (fuel + 20) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  have hns := evalGRom_macNewSample_m0 (fuel + 4) acc
  have hbatt := evalGRom_op0 97 (fuel + 18) 2
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hdone := evalGRom_macArm_done 97 (fuel + 13) (.atom acc) (.atom 1) (.atom 0)
  have hslam := evalGRom_slam (q := 97) (fuel := fuel + 16)
    (bHead := .atom 0) (bTail := .atom 2)
    hbatt
    (evalGRom_mono (q := 97) (show fuel + 4 + 14 ≤ fuel + 16 + 3 by omega) hns)
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0))
    (evalGRom_mono (q := 97) (show fuel + 13 + 6 ≤ fuel + 16 + 3 by omega) hdone)
  simpa [macArm, slam, op0, macNewSample, macCore] using
    evalGRom_op6_one 97 (fuel + 21) hcond hslam

/-- `macNewSample` after one MAC trip with `m = 1`. -/
theorem evalGRom_macNewSample_m1 (fuel acc : ℕ) (hacc : acc + 1 < 97) :
    evalGRom 97 (fuel + 23)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample =
      some (.cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1)))) := by
  have hadd := evalGRom_addFromMac_m1 fuel acc hacc
  have h14 := evalGRom_op0 97 (fuel + 19) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinc := evalGRom_op4 97 (fuel + 20) h14 (lusG_succ (n := 0) (by decide))
  have hn := evalGRom_op0 97 (fuel + 19) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hm := evalGRom_op0 97 (fuel + 19) 31
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hnm := evalGRom_cons 97 (fuel + 20) hn hm
  have hrest := evalGRom_cons 97 (fuel + 21) hinc hnm
  exact evalGRom_cons 97 (fuel + 22)
    (evalGRom_mono (q := 97) (show fuel + 21 ≤ fuel + 22 by omega) hadd) hrest

theorem evalGRom_macArm_one_m1 (fuel acc : ℕ) (hacc : acc + 1 < 97) :
    evalGRom 97 (fuel + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      some (.atom (acc + 1)) := by
  have h14 := evalGRom_op0 97 (fuel + 28) 14
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have h30 := evalGRom_op0 97 (fuel + 28) 30
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hcond := evalGRom_op5 97 (fuel + 29) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  have hns := evalGRom_macNewSample_m1 (fuel + 4) acc hacc
  have hbatt := evalGRom_op0 97 (fuel + 27) 2
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hdone := evalGRom_macArm_done 97 (fuel + 22) (.atom (acc + 1)) (.atom 1) (.atom 1)
  have hslam := evalGRom_slam (q := 97) (fuel := fuel + 25)
    (bHead := .atom 0) (bTail := .atom 2)
    hbatt
    (evalGRom_mono (q := 97) (show fuel + 4 + 23 ≤ fuel + 25 + 3 by omega) hns)
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1))
    (evalGRom_mono (q := 97) (show fuel + 22 + 6 ≤ fuel + 25 + 3 by omega) hdone)
  simpa [macArm, slam, op0, macNewSample, macCore] using
    evalGRom_op6_one 97 (fuel + 30) hcond hslam

theorem evalGRom_mmC00 (fuel : ℕ) :
    evalGRom 97 (fuel + 56) mmSubject mmC00 = some (.atom 2) := by
  have ha0 := evalGRom_op1 97 (fuel + 44) mmSubject 0
  have a00 := evalGRom_op0 97 (fuel + 42) 8 mmSubject_slot8
  have b00 := evalGRom_op0 97 (fuel + 42) 12 mmSubject_slot12
  have innerA := evalGRom_macArm_one_m1 (fuel + 11) 0 (by decide)
  have hinner := evalGRom_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 12) ha0 a00 b00
    (evalGRom_mono (q := 97) (show fuel + 11 + 31 ≤ fuel + 43 + 3 by omega) innerA)
  have a01 := evalGRom_op0 97 (fuel + 50) 9 mmSubject_slot9
  have b10 := evalGRom_op0 97 (fuel + 50) 14 mmSubject_slot14
  have outerA := evalGRom_macArm_one_m1 (fuel + 16) 1 (by decide)
  have houter := evalGRom_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalGRom_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a01 b10
    (evalGRom_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalGRom_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

/-- `c01 = 1·0 + 1·1 = 1`. -/
theorem evalGRom_mmC01 (fuel : ℕ) :
    evalGRom 97 (fuel + 56) mmSubject mmC01 = some (.atom 1) := by
  have ha0 := evalGRom_op1 97 (fuel + 44) mmSubject 0
  have a00 := evalGRom_op0 97 (fuel + 42) 8 mmSubject_slot8
  have b01 := evalGRom_op0 97 (fuel + 42) 13 mmSubject_slot13
  have innerA := evalGRom_macArm_one_m0 (fuel + 20) 0
  have hinner := evalGRom_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 13) ha0 a00 b01
    (evalGRom_mono (q := 97) (show fuel + 20 + 22 ≤ fuel + 43 + 3 by omega) innerA)
  have a01 := evalGRom_op0 97 (fuel + 50) 9 mmSubject_slot9
  have b11 := evalGRom_op0 97 (fuel + 50) 15 mmSubject_slot15
  have outerA := evalGRom_macArm_one_m1 (fuel + 16) 0 (by decide)
  have houter := evalGRom_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalGRom_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a01 b11
    (evalGRom_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC01, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalGRom_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

/-- `c10 = 0·1 + 1·1 = 1`. -/
theorem evalGRom_mmC10 (fuel : ℕ) :
    evalGRom 97 (fuel + 56) mmSubject mmC10 = some (.atom 1) := by
  have ha0 := evalGRom_op1 97 (fuel + 44) mmSubject 0
  have a10 := evalGRom_op0 97 (fuel + 42) 10 mmSubject_slot10
  have b00 := evalGRom_op0 97 (fuel + 42) 12 mmSubject_slot12
  have innerA := evalGRom_macArm_zero 97 (fuel + 40) (.atom 0) (.atom 1)
  have hinner := evalGRom_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 12) ha0 a10 b00
    (evalGRom_mono (q := 97) (show fuel + 40 + 6 ≤ fuel + 43 + 3 by omega) innerA)
  have a11 := evalGRom_op0 97 (fuel + 50) 11 mmSubject_slot11
  have b10 := evalGRom_op0 97 (fuel + 50) 14 mmSubject_slot14
  have outerA := evalGRom_macArm_one_m1 (fuel + 16) 0 (by decide)
  have houter := evalGRom_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalGRom_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a11 b10
    (evalGRom_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalGRom_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

/-- `c11 = 0·0 + 1·1 = 1`. -/
theorem evalGRom_mmC11 (fuel : ℕ) :
    evalGRom 97 (fuel + 56) mmSubject mmC11 = some (.atom 1) := by
  have ha0 := evalGRom_op1 97 (fuel + 44) mmSubject 0
  have a10 := evalGRom_op0 97 (fuel + 42) 10 mmSubject_slot10
  have b01 := evalGRom_op0 97 (fuel + 42) 13 mmSubject_slot13
  have innerA := evalGRom_macArm_zero 97 (fuel + 40) (.atom 0) (.atom 0)
  have hinner := evalGRom_invokeMac (q := 97) (fuel := fuel + 43)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 13) ha0 a10 b01
    (evalGRom_mono (q := 97) (show fuel + 40 + 6 ≤ fuel + 43 + 3 by omega) innerA)
  have a11 := evalGRom_op0 97 (fuel + 50) 11 mmSubject_slot11
  have b11 := evalGRom_op0 97 (fuel + 50) 15 mmSubject_slot15
  have outerA := evalGRom_macArm_one_m1 (fuel + 16) 0 (by decide)
  have houter := evalGRom_invokeMac (q := 97) (fuel := fuel + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using
      evalGRom_mono (q := 97) (show fuel + 43 + 5 ≤ fuel + 51 + 2 by omega) hinner)
    a11 b11
    (evalGRom_mono (q := 97) (show fuel + 16 + 31 ≤ fuel + 51 + 3 by omega) outerA)
  simpa [mmC11, mac2, invokeMac, slam, op7, quote, op1, op0] using
    evalGRom_mono (q := 97) (show fuel + 51 + 5 ≤ fuel + 56 by omega) houter

theorem mm_evalGRom97 :
    evalGRom 97 64 mmSubject mmFormula = some mmC := by
  have h00 := evalGRom_mmC00 6
  have h01 := evalGRom_mmC01 6
  have h10 := evalGRom_mmC10 6
  have h11 := evalGRom_mmC11 6
  have hL := evalGRom_cons 97 62
    (evalGRom_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h00)
    (evalGRom_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h01)
  have hR := evalGRom_cons 97 62
    (evalGRom_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h10)
    (evalGRom_mono (q := 97) (show 6 + 56 ≤ 62 by omega) h11)
  rw [mmFormula, mmC]
  exact evalGRom_cons 97 63 hL hR

theorem mm_grom :
    evalGRom Field.p 64 mmSubject mmFormula = some mmC :=
  evalGRom_mod_le (q := 97) (q' := Field.p)
    (by simp only [Field.p]; norm_num) 64 mmSubject mmFormula mmC mm_evalGRom97

theorem mmSubject_bounded_p : FieldEmbedding.BoundedBy Field.p mmSubject :=
  BoundedBy_mono (by simp only [Field.p]; norm_num) mmSubject_bounded32

theorem mmFormula_bounded_p : FieldEmbedding.BoundedBy Field.p mmFormula :=
  BoundedBy_mono (by simp only [Field.p]; norm_num) mmFormula_bounded32

/-! ## Row counts, accumulator, `hmempos`, `hcard` at the generated tree. -/

theorem mm_comp_rows (z α : K) :
    (bfsForest [genComputeRows z α (mmTree (K := K))]).length = 401 := by
  rw [genComputeRows_bfsForest_length]
  have hsz : (mmTreeAir (K := K)).size = 401 := by
    unfold mmTreeAir
    rw [airReorder_size, mmTree_size]
  have : (bfsRows (airReorder (mmTree (K := K)))).length = 401 := by
    simp [bfsRows, bfsForest_length, totalSize, mmTreeAir] at hsz ⊢
    exact hsz
  exact this

theorem mm_mem_rows (z α : K) :
    programMemRows z α (mmTree (K := K)) = 30936 := by
  unfold programMemRows programMemRowsL
  rw [bfsForest_length, genMemoryForest_eq_thread, threadGenForest_totalSize]
  exact mmMemForest_assigned_totalSize (encC z) z α

theorem mm_mem_roots (z α : K) :
    programMemRoots z α (mmTree (K := K)) = 618 := by
  unfold programMemRoots programMemRootsL
  rw [genMemoryForest_eq_thread, threadGenForest_length]
  exact mmMemForest_assigned_length (encC z) z α

theorem mm_mempos (z α : K) :
    0 < (bfsForest (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (mmTree (K := K)))).length :=
  genMemoryForest_bfsForest_length_pos z α (memInputs z) (mmTree_gen (K := K))

theorem mm_acc_le :
    programAcc (mmTree (K := K)) ≤ 1203 := by
  unfold programAcc
  have hlen : (bfsRows (airReorder (mmTree (K := K)))).length = 401 := by
    have hsz : (airReorder (mmTree (K := K))).size = 401 := by
      rw [airReorder_size, mmTree_size]
    simp [bfsRows, bfsForest_length, totalSize] at hsz ⊢
    exact hsz
  have h := accAt_le_three_mul (airReorder (mmTree (K := K)))
    (bfsRows (airReorder (mmTree (K := K)))).length
  simpa [hlen] using h

/-- The memory half of §1's `hwin` (weakest form) at the
Goldilocks 2×2 matmul: `30936` memory rows, `orderOf α = 2^16`. -/
theorem mm_hmemOrd :
    programMemShape MatmulConfigGoldilocks.alphaA (mmTree (K := K))
      ≤ orderOf MatmulConfigGoldilocks.alphaA := by
  have hm : programMemShape MatmulConfigGoldilocks.alphaA (mmTree (K := K)) = 30936 :=
    mm_mem_rows 0 _
  rw [hm, MatmulConfigGoldilocks.alphaA_order]
  norm_num

theorem mm_hwin :
    programAcc (mmTree (K := K)) + 3 < orderOf MatmulConfigGoldilocks.alphaA := by
  have hacc := mm_acc_le
  have hord : orderOf MatmulConfigGoldilocks.alphaA = 2 ^ 16 :=
    MatmulConfigGoldilocks.alphaA_order
  omega

theorem mm_hcomp (z α : K) :
    (bfsForest [genComputeRows z α (mmTree (K := K))]).length
      ≤ 2 ^ executionOrbit.h := by
  rw [mm_comp_rows, executionOrbit_h]
  norm_num

theorem mm_hmem (z α : K) :
    (bfsForest (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (mmTree (K := K)))).length
      ≤ 2 ^ executionOrbit.h := by
  rw [show (bfsForest (genMemoryForest z α MemoryTable.formRDefault (memInputs z) (mmTree (K := K)))).length =
      programMemRows z α (mmTree (K := K)) from (programMemRows_eq_L _ z α _).symm, mm_mem_rows, executionOrbit_h]
  norm_num

theorem mm_hprogCap :
    programAcc (mmTree (K := K)) + 1 ≤ 2 ^ executionOrbit.h := by
  have hacc := mm_acc_le
  rw [executionOrbit_h]
  omega

theorem mm_hmemCap (z α : K) :
    programMemRows z α (mmTree (K := K)) + 1 ≤ 2 ^ executionOrbit.h := by
  rw [mm_mem_rows, executionOrbit_h]
  norm_num

theorem mm_compilerKsz (z α : K) :
    compilerKszOf z α (mmTree (K := K)) = 1236 := by
  have hacc : programAcc (mmTree (K := K)) ≤ 1203 := mm_acc_le
  have hmf : programMemRoots z α (mmTree (K := K)) = 618 := mm_mem_roots z α
  unfold compilerKszOf compilerKsz
  rw [hmf]
  have : 2 * 618 = 1236 := by norm_num
  rw [this]
  exact Nat.max_eq_right (le_trans hacc (by norm_num))

theorem mm_hKszChar (z α : K) :
    compilerKszOf z α (mmTree (K := K)) < ringChar K := by
  rw [mm_compilerKsz, ringChar_K]
  simp only [Field.p]
  norm_num

theorem mm_compilerN (z α : K) :
    compilerNOf z α (mmTree (K := K)) = 30936 := by
  have hacc : programAcc (mmTree (K := K)) ≤ 1203 := mm_acc_le
  have hmem : programMemRows z α (mmTree (K := K)) = 30936 := mm_mem_rows z α
  unfold compilerNOf compilerN
  rw [hmem]
  exact Nat.max_eq_right (le_trans hacc (by norm_num))

theorem mm_hcard (z α : K) :
    RecordCarrier.honestIOBound
      (compilerNOf z α (mmTree (K := K)))
      (compilerNOf z α (mmTree (K := K)))
      (Fintype.card K) < Fintype.card (K × K) := by
  rw [mm_compilerN]
  exact hcard_of_le_two_pow_92_honest 30936 (by norm_num)

theorem mm_rows_lt_card :
    (bfsForest [airReorder (mmTree (K := K))]).length < Fintype.card K := by
  have hlen : (bfsForest [airReorder (mmTree (K := K))]).length = 401 := by
    have hsz : (airReorder (mmTree (K := K))).size = 401 := by
      rw [airReorder_size, mmTree_size]
    simp [bfsForest_length, totalSize] at hsz ⊢
    exact hsz
  rw [hlen, Field.card_K]
  simp only [Field.p]
  norm_num

/-- `hcoins` exists: 401 compute rows sit below `|K| = p³`. -/
theorem mm_exists_computeCoins :
    ∃ a b c : MatmulConfigGoldilocks.K,
      ComputeCoinsGeneric (K := MatmulConfigGoldilocks.K)
        MatmulConfigGoldilocks.seedZ MatmulConfigGoldilocks.alphaA a b c
        (airReorder (mmTree (K := MatmulConfigGoldilocks.K))) :=
  exists_computeCoinsGeneric_airReorder (K := MatmulConfigGoldilocks.K)
    MatmulConfigGoldilocks.seedZ MatmulConfigGoldilocks.alphaA
    (mmTree (K := MatmulConfigGoldilocks.K)) mm_rows_lt_card

theorem mmSubject_leaves : mmSubject.leaves = 8 := by
  decide

end Nock.NockVMROM.Thm54.TraceGen

