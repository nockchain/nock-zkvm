/-
  Nock/NockVMROM/Thm54/P8Core/Batch1513Thm54SVReadyFuelF.lean

  **The readiness induction at the field C2
  join.**  `Batch1090` (`P8Core/Batch1090Thm54C2ReadyFuel.lean`) transcribed mechanically at
  `SVJoinF.c2JoinFuelF q` (names unchanged, new namespace): the per-fuel readiness bundle
  `C2JoinReadyF`, `computeTreeBinds_of_readyF`, the chip-side bundle `C2ChipReady` (the field twin:
  every join value it mentions — OP3's size window, OP4's atom operand, OP5's `PairFaithful`, the
  dependent children's subjects — is the FIELD join's), `readyF_child_eval_binds`,
  `c2JoinReadyF_of_chipReady` and `computeTreeBinds_of_chipReady`.

  Changes beyond the renaming: the join's modulus is the bundle's own `q` (the `q` of
  `C2ChipReady z q`, the injectivity / `PairFaithful` modulus), and the binding theorems carry
  `[CharP K q]` (OP4, `SVJoinAssemblyF.computeTreeBinds_op4F`); at L-E's instantiation
  `q = ringChar K`.  Not transcribed: the `AtFamily` section (`hcomp_C2_of_chipReady`,
  `bindsAtCoin_C2_of_chipReady`), which is stated at a package's Nat-join strategy
  `strategyOfTracesR0AC2`; the standalone verifier has no package.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1512Thm54SVJoinAssemblyF
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch1090Thm54C2ReadyFuel

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVReadyFuelF

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.SVJoinF
open Nock.NockVMROM.Thm54.SVJoinAssemblyF
open Nock.RedTeam
open Nock.RedTeam.Batch525
open Nock.GlobalCarryRecognizer
variable {K : Type} [Field K] [DecidableEq K]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false
set_option hygiene false in
/-- The FIELD C2 join, at the modulus `q` in scope at the use site (hygiene off on purpose: the
bundles' own `q` parameter is the join modulus). -/
local notation "J" => c2JoinFuelF q (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

inductive C2JoinReadyF (z : K) (q : ℕ) :
    NTree ((State × DTcomp K) × ℕ) → Noun → Noun → Prop
  | op0 {row : (State × DTcomp K) × ℕ} {subj tail : Noun}
      (hstate : row.1.1 = .s0)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s0)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 0) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (he : bindFP z (op0ResF sv ax row.2 subj)
        row.1.2.2.1.e)
      (hax : ((ax (row.2 + 2) : ℕ) : K) =
        row.1.2.2.2.f_t.leaf)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2) :
      C2JoinReadyF z q (.node row []) subj (.cell (.atom 0) tail)
  | op1 {row : (State × DTcomp K) × ℕ} {subj tail : Noun}
      (hstate : row.1.1 = .s1)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s1)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 1) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2) :
      C2JoinReadyF z q (.node row []) subj (.cell (.atom 1) tail)
  | cons {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fh ft : Noun}
      (hstate : row.1.1 = .cons)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .cons)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hfh : bindFP z fh row.1.2.2.2.f_h)
      (hft : bindFP z ft row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heLlink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (heRlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hL : C2JoinReadyF z q c0 subj fh)
      (hR : C2JoinReadyF z q c1 subj ft) :
      C2JoinReadyF z q (.node row [c0, c1]) subj (.cell fh ft)
  | op3 {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)}
      {subj tail : Noun}
      (hstate : row.1.1 = .s3)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s3)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 3) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (hwin : OpcodeSemantics.SizeWindow z
          (J c0.size c0 subj tail).label.evaluation)
      (helink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hC : C2JoinReadyF z q c0 subj tail) :
      C2JoinReadyF z q (.node row [c0]) subj (.cell (.atom 3) tail)
  | op4 {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)}
      {subj tail : Noun} {k : ℕ}
      (hstate : row.1.1 = .s4)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s4)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 4) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (hke : (J c0.size c0 subj tail).label.evaluation =
          .atom k)
      (hcall : bindFP z (.atom k) row.1.2.2.1.sf1_e)
      (hC : C2JoinReadyF z q c0 subj tail) :
      C2JoinReadyF z q (.node row [c0]) subj (.cell (.atom 4) tail)
  | op5 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fth ftt : Noun}
      (hstate : row.1.1 = .s5)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s5)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 5) row.1.2.2.2.f_h)
      (hth : bindFP z fth row.1.2.2.2.f_th)
      (htt : bindFP z ftt row.1.2.2.2.f_tt)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hfaith : OpcodeSemantics.PairFaithful z q
          (J c0.size c0 subj fth).label.evaluation
          (J c1.size c1 subj ftt).label.evaluation)
      (heLlink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (heRlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hL : C2JoinReadyF z q c0 subj fth)
      (hR : C2JoinReadyF z q c1 subj ftt) :
      C2JoinReadyF z q (.node row [c0, c1])
        subj (.cell (.atom 5) (.cell fth ftt))
  | op2 {row : (State × DTcomp K) × ℕ}
      {c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)}
      {subj fth ftt : Noun}
      (hstate : row.1.1 = .s2)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s2)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 2) row.1.2.2.2.f_h)
      (hth : bindFP z fth row.1.2.2.2.f_th)
      (htt : bindFP z ftt row.1.2.2.2.f_tt)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (he1link : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (he2link : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (heApplink : c2.label.1.2.2.1.e = row.1.2.2.1.sf3_e)
      (h1 : C2JoinReadyF z q c0 subj fth)
      (h2 : C2JoinReadyF z q c1 subj ftt)
      (h3 : C2JoinReadyF z q c2
        (J c0.size c0 subj fth).label.evaluation
        (J c1.size c1 subj ftt).label.evaluation) :
      C2JoinReadyF z q (.node row [c0, c1, c2])
        subj (.cell (.atom 2) (.cell fth ftt))
  | op6 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fth ftth fttt : Noun} {b : ℕ}
      (hstate : row.1.1 = .s6)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s6)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 6) row.1.2.2.2.f_h)
      (hth : bindFP z fth row.1.2.2.2.f_th)
      (htth : bindFP z ftth row.1.2.2.2.f_tth)
      (httt : bindFP z fttt row.1.2.2.2.f_ttt)
      (hb : b = 0 ∨ b = 1)
      (hcondE : (J c1.size c1 subj fth).label.evaluation =
          .atom b)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heTakenlink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hcondlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hT : C2JoinReadyF z q c0 subj
        (if b = 0 then ftth else fttt))
      (hC : C2JoinReadyF z q c1 subj fth) :
      C2JoinReadyF z q (.node row [c0, c1])
        subj (.cell (.atom 6) (.cell fth (.cell ftth fttt)))
  | op7 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fth ftt : Noun}
      (hstate : row.1.1 = .s7)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s7)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 7) row.1.2.2.2.f_h)
      (hth : bindFP z fth row.1.2.2.2.f_th)
      (htt : bindFP z ftt row.1.2.2.2.f_tt)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heHelplink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (heConslink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hHelp : C2JoinReadyF z q c1 subj fth)
      (hCons : C2JoinReadyF z q c0
        (J c1.size c1 subj fth).label.evaluation
        ftt) :
      C2JoinReadyF z q (.node row [c0, c1])
        subj (.cell (.atom 7) (.cell fth ftt))
  | op8 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fth ftt : Noun}
      (hstate : row.1.1 = .s8)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s8)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 8) row.1.2.2.2.f_h)
      (hth : bindFP z fth row.1.2.2.2.f_th)
      (htt : bindFP z ftt row.1.2.2.2.f_tt)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heHelplink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (heConslink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hHelp : C2JoinReadyF z q c1 subj fth)
      (hCons : C2JoinReadyF z q c0
        (.cell
          (J c1.size c1 subj fth).label.evaluation
          subj) ftt) :
      C2JoinReadyF z q (.node row [c0, c1])
        subj (.cell (.atom 8) (.cell fth ftt))
  | op9 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj coreF : Noun}
      (hstate : row.1.1 = .s9)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s9)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 9) row.1.2.2.2.f_h)
      (hax : bindFP z (.atom (ax (row.2 + 3)))
        row.1.2.2.2.f_th)
      (hcoreF : bindFP z coreF row.1.2.2.2.f_tt)
      (harm : bindFP z (op9ArmF sv ax row.2 (J c0.size c0 subj coreF).label.evaluation)
        row.1.2.2.1.sf2_f)
      (haxK : ((ax (row.2 + 3) : ℕ) : K) =
        row.1.2.2.2.f_th.leaf)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heCorelink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (heInvlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hCore : C2JoinReadyF z q c0 subj coreF)
      (hInv : C2JoinReadyF z q c1
        (J c0.size c0 subj coreF).label.evaluation
        (op9ArmF sv ax row.2 (J c0.size c0 subj coreF).label.evaluation)) :
      C2JoinReadyF z q (.node row [c0, c1])
        subj (.cell (.atom 9)
          (.cell (.atom (ax (row.2 + 3))) coreF))

theorem computeTreeBinds_of_readyF {z : K} (hz : z ≠ 0) {q fuel : ℕ} [CharP K q]
    {t : NTree ((State × DTcomp K) × ℕ)} {subj formula : Noun}
    (hfuel : t.size ≤ fuel)
    (hR : C2JoinReadyF (sv := sv) (ax := ax) z q t subj formula) :
    ComputeTreeBinds z (J fuel t subj formula) (mapNTree Prod.fst t) := by
  induction hR generalizing fuel with
  | @op0 row subj tail hstate hzRow hpubSt hs hh ht he hax hV =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      exact computeTreeBinds_join_op0 hz subj tail row hstate hzRow hpubSt
        hs hh ht he hax hV
  | @op1 row subj tail hstate hzRow hpubSt hs hh ht hV =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      exact computeTreeBinds_join_op1 hz subj tail row hstate hzRow hpubSt
        hs hh ht hV
  | @cons row c0 c1 subj fh ft hstate hzRow hpubSt hs hfh hft hV
      heLlink heRlink hL hR ihL ihR =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel
        simp [hsz] at this
        omega
      have hn1 : c1.size ≤ n := by
        have := hfuel
        simp [hsz] at this
        omega
      have hLb := ihL hn0
      have hRb := ihR hn1
      have heL : bindFP z
          (J n c0 subj fh).label.evaluation
          row.1.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hLb).2.2.2.2.2.1
        simpa [heLlink] using hb
      have heR : bindFP z
          (J n c1 subj ft).label.evaluation
          row.1.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hRb).2.2.2.2.2.1
        simpa [heRlink] using hb
      exact computeTreeBinds_join_cons hz subj fh ft row c0 c1
        hstate hzRow hpubSt hs hfh hft hV
        (J_subject n c0 subj fh)
        (J_formula n c0 subj fh)
        (J_subject n c1 subj ft)
        (J_formula n c1 subj ft)
        heL heR hLb hRb
  | @op3 row c0 subj tail hstate hzRow hpubSt hs hh ht hV hwin helink hC ih =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0]).size = 1 + c0.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have hn0 : c0.size ≤ n := by
        have := hfuel
        simp [hsz] at this
        omega
      have hCb := ih hn0
      have hcall : bindFP z
          (J n c0 subj tail).label.evaluation
          row.1.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hCb).2.2.2.2.2.1
        simpa [helink] using hb
      have hwin' : OpcodeSemantics.SizeWindow z (J n c0 subj tail).label.evaluation := by
        rw [J_eq_of_le (sv := sv) (ax := ax) (q := q) c0 subj tail (Nat.le_refl _) hn0]
        exact hwin
      exact computeTreeBinds_join_op3 hz subj tail row c0
        hstate hzRow hpubSt hs hh ht hcall hwin' hV
        (J_subject n c0 subj tail)
        (J_formula n c0 subj tail) hCb
  | @op4 row c0 subj tail k hstate hzRow hpubSt hs hh ht hV hke hcall hC ih =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0]).size = 1 + c0.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have hn0 : c0.size ≤ n := by
        have := hfuel
        simp [hsz] at this
        omega
      have hCb := ih hn0
      have hke' : (J n c0 subj tail).label.evaluation = .atom k := by
        rw [J_eq_of_le (sv := sv) (ax := ax) (q := q) c0 subj tail (Nat.le_refl _) hn0]
        exact hke
      exact computeTreeBinds_join_op4 hz subj tail k row c0
        hstate hzRow hpubSt hs hh ht hcall hV
        (J_subject n c0 subj tail)
        (J_formula n c0 subj tail) hke' hCb
  | @op5 row c0 c1 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      hcast hfaith heLlink heRlink hL hR ihL ihR =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hLb := ihL hn0
      have hRb := ihR hn1
      have heL : bindFP z
          (J n c0 subj fth).label.evaluation
          row.1.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hLb).2.2.2.2.2.1
        simpa [heLlink] using hb
      have heR : bindFP z
          (J n c1 subj ftt).label.evaluation
          row.1.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hRb).2.2.2.2.2.1
        simpa [heRlink] using hb
      have hfaith' : OpcodeSemantics.PairFaithful z q
          (J n c0 subj fth).label.evaluation
          (J n c1 subj ftt).label.evaluation := by
        rw [J_eq_of_le (sv := sv) (ax := ax) (q := q) c0 subj fth (Nat.le_refl _) hn0,
          J_eq_of_le (sv := sv) (ax := ax) (q := q) c1 subj ftt (Nat.le_refl _) hn1]
        exact hfaith
      exact computeTreeBinds_join_op5 hz subj fth ftt row c0 c1
        hstate hzRow hpubSt hs hh hth htt heL heR hcast hfaith' hV hLb hRb
  | @op2 row c0 c1 c2 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      he1link he2link heApplink h1 h2 h3 ih1 ih2 ih3 =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1, c2]).size =
          1 + c0.size + c1.size + c2.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn2 : c2.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have h1b := ih1 hn0
      have h2b := ih2 hn1
      have heq0 := J_eq_of_le (sv := sv) (ax := ax) (q := q) c0 subj fth
        (Nat.le_refl _) hn0
      have heq1 := J_eq_of_le (sv := sv) (ax := ax) (q := q) c1 subj ftt
        (Nat.le_refl _) hn1
      have h3b := ih3 hn2
      rw [← heq0, ← heq1] at h3b
      have he1 : bindFP z
          (J n c0 subj fth).label.evaluation
          row.1.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root h1b).2.2.2.2.2.1
        simpa [he1link] using hb
      have he2 : bindFP z
          (J n c1 subj ftt).label.evaluation
          row.1.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root h2b).2.2.2.2.2.1
        simpa [he2link] using hb
      have heApp : bindFP z
          (J n c2
            (J n c0 subj fth).label.evaluation
            (J n c1 subj ftt).label.evaluation).label.evaluation
          row.1.2.2.1.sf3_e := by
        have hb := (ComputeTreeBinds.root h3b).2.2.2.2.2.1
        simpa [heApplink] using hb
      exact computeTreeBinds_join_op2 hz subj fth ftt row c0 c1 c2
        hstate hzRow hpubSt hs hh hth htt he1 he2 heApp hV h1b h2b h3b
  | @op6 row c0 c1 subj fth ftth fttt b hstate hzRow hpubSt hs hh hth htth
      httt hb hcondE hV heTakenlink hcondlink hT hC ihT ihC =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hTb := ihT hn0
      have hCb := ihC hn1
      have hcondE' : (J n c1 subj fth).label.evaluation = .atom b := by
        rw [J_eq_of_le (sv := sv) (ax := ax) (q := q) c1 subj fth (Nat.le_refl _) hn1]
        exact hcondE
      have hcond : bindFP z (.atom b) row.1.2.2.1.sf2_e := by
        have hb' := (ComputeTreeBinds.root hCb).2.2.2.2.2.1
        simpa [hcondlink, hcondE'] using hb'
      have heTaken : bindFP z
          (J n c0 subj
            (if b = 0 then ftth else fttt)).label.evaluation
          row.1.2.2.1.sf1_e := by
        have hb' := (ComputeTreeBinds.root hTb).2.2.2.2.2.1
        simpa [heTakenlink] using hb'
      exact computeTreeBinds_join_op6 hz subj fth ftth fttt b row c0 c1
        hstate hzRow hpubSt hs hh hth htth httt hb hcondE' hcond heTaken
        hV hTb hCb
  | @op7 row c0 c1 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      heHelplink heConslink hHelp hCons ihHelp ihCons =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hHelpb := ihHelp hn1
      have heq := J_eq_of_le (sv := sv) (ax := ax) (q := q) c1 subj fth
        (Nat.le_refl _) hn1
      have hConsb := ihCons hn0
      rw [← heq] at hConsb
      have heHelp : bindFP z
          (J n c1 subj fth).label.evaluation
          row.1.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hHelpb).2.2.2.2.2.1
        simpa [heHelplink] using hb
      have heCons : bindFP z
          (J n c0
            (J n c1 subj fth).label.evaluation
            ftt).label.evaluation
          row.1.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hConsb).2.2.2.2.2.1
        simpa [heConslink] using hb
      exact computeTreeBinds_join_op7 hz subj fth ftt row c0 c1
        hstate hzRow hpubSt hs hh hth htt heHelp heCons hV hConsb hHelpb
  | @op8 row c0 c1 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      heHelplink heConslink hHelp hCons ihHelp ihCons =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hHelpb := ihHelp hn1
      have heq := J_eq_of_le (sv := sv) (ax := ax) (q := q) c1 subj fth
        (Nat.le_refl _) hn1
      have hConsb := ihCons hn0
      rw [← heq] at hConsb
      have heHelp : bindFP z
          (J n c1 subj fth).label.evaluation
          row.1.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hHelpb).2.2.2.2.2.1
        simpa [heHelplink] using hb
      have heCons : bindFP z
          (J n c0
            (.cell (J n c1 subj fth).label.evaluation
              subj) ftt).label.evaluation
          row.1.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hConsb).2.2.2.2.2.1
        simpa [heConslink] using hb
      exact computeTreeBinds_join_op8 hz subj fth ftt row c0 c1
        hstate hzRow hpubSt hs hh hth htt heHelp heCons hV hConsb hHelpb
  | @op9 row c0 c1 subj coreF hstate hzRow hpubSt hs hh hax hcoreF harm haxK
      hV heCorelink heInvlink hCore hInv ihCore ihInv =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (Batch1021.ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hCoreb := ihCore hn0
      have heq := J_eq_of_le (sv := sv) (ax := ax) (q := q) c0 subj coreF
        (Nat.le_refl _) hn0
      have hInvb := ihInv hn1
      rw [← heq] at hInvb
      have heCore : bindFP z
          (J n c0 subj coreF).label.evaluation
          row.1.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hCoreb).2.2.2.2.2.1
        simpa [heCorelink] using hb
      have heInv : bindFP z
          (J n c1
            (J n c0 subj coreF).label.evaluation
            (op9ArmF sv ax row.2 (J n c0 subj coreF).label.evaluation)).label.evaluation
          row.1.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hInvb).2.2.2.2.2.1
        simpa [heInvlink] using hb
      rw [← heq] at harm
      exact computeTreeBinds_join_op9 hz subj coreF row c0 c1
        hstate hzRow hpubSt hs hh hax hcoreF harm heCore heInv haxK hV
        hCoreb hInvb

/-- `C2JoinReadyF` without any subject binding: every row's chip facts, served facts, axis
facts, decompositions and windows, plus the `Fcomp` subject links `c.s = sf_i.s`.  The subject binding of every non-root node is DERIVED by
`c2JoinReadyF_of_chipReady`. -/
inductive C2ChipReady (z : K) (q : ℕ) :
    NTree ((State × DTcomp K) × ℕ) → Noun → Noun → Prop
  | op0 {row : (State × DTcomp K) × ℕ} {subj tail : Noun}
      (hstate : row.1.1 = .s0)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s0)
      (hh : bindFP z (.atom 0) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (he : bindFP z (op0ResF sv ax row.2 subj) row.1.2.2.1.e)
      (hax : ((ax (row.2 + 2) : ℕ) : K) = row.1.2.2.2.f_t.leaf)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2) :
      C2ChipReady z q (.node row []) subj (.cell (.atom 0) tail)
  | op1 {row : (State × DTcomp K) × ℕ} {subj tail : Noun}
      (hstate : row.1.1 = .s1)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s1)
      (hh : bindFP z (.atom 1) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2) :
      C2ChipReady z q (.node row []) subj (.cell (.atom 1) tail)
  | cons {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fh ft : Noun}
      (hstate : row.1.1 = .cons)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .cons)
      (hfh : bindFP z fh row.1.2.2.2.f_h)
      (hft : bindFP z ft row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heLlink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (heRlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hsLlink : c0.label.1.2.2.1.s = row.1.2.2.1.sf1_s)
      (hsRlink : c1.label.1.2.2.1.s = row.1.2.2.1.sf2_s)
      (hL : C2ChipReady z q c0 subj fh)
      (hR : C2ChipReady z q c1 subj ft) :
      C2ChipReady z q (.node row [c0, c1]) subj (.cell fh ft)
  | op3 {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)}
      {subj tail : Noun}
      (hstate : row.1.1 = .s3)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s3)
      (hh : bindFP z (.atom 3) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (hwin : OpcodeSemantics.SizeWindow z (J c0.size c0 subj tail).label.evaluation)
      (helink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hslink : c0.label.1.2.2.1.s = row.1.2.2.1.sf1_s)
      (hC : C2ChipReady z q c0 subj tail) :
      C2ChipReady z q (.node row [c0]) subj (.cell (.atom 3) tail)
  | op4 {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)}
      {subj tail : Noun} {k : ℕ}
      (hstate : row.1.1 = .s4)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s4)
      (hh : bindFP z (.atom 4) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (hke : (J c0.size c0 subj tail).label.evaluation = .atom k)
      (helink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hslink : c0.label.1.2.2.1.s = row.1.2.2.1.sf1_s)
      (hC : C2ChipReady z q c0 subj tail) :
      C2ChipReady z q (.node row [c0]) subj (.cell (.atom 4) tail)
  | op5 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fth ftt : Noun}
      (hstate : row.1.1 = .s5)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s5)
      (hh : bindFP z (.atom 5) row.1.2.2.2.f_h)
      (hth : bindFP z fth row.1.2.2.2.f_th)
      (htt : bindFP z ftt row.1.2.2.2.f_tt)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hfaith : OpcodeSemantics.PairFaithful z q
          (J c0.size c0 subj fth).label.evaluation
          (J c1.size c1 subj ftt).label.evaluation)
      (heLlink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (heRlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hsLlink : c0.label.1.2.2.1.s = row.1.2.2.1.sf1_s)
      (hsRlink : c1.label.1.2.2.1.s = row.1.2.2.1.sf2_s)
      (hL : C2ChipReady z q c0 subj fth)
      (hR : C2ChipReady z q c1 subj ftt) :
      C2ChipReady z q (.node row [c0, c1]) subj (.cell (.atom 5) (.cell fth ftt))
  | op2 {row : (State × DTcomp K) × ℕ}
      {c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)}
      {subj fth ftt : Noun}
      (hstate : row.1.1 = .s2)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s2)
      (hh : bindFP z (.atom 2) row.1.2.2.2.f_h)
      (hth : bindFP z fth row.1.2.2.2.f_th)
      (htt : bindFP z ftt row.1.2.2.2.f_tt)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (he1link : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (he2link : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (heApplink : c2.label.1.2.2.1.e = row.1.2.2.1.sf3_e)
      (hs1link : c0.label.1.2.2.1.s = row.1.2.2.1.sf1_s)
      (hs2link : c1.label.1.2.2.1.s = row.1.2.2.1.sf2_s)
      (hs3link : c2.label.1.2.2.1.s = row.1.2.2.1.sf3_s)
      (h1 : C2ChipReady z q c0 subj fth)
      (h2 : C2ChipReady z q c1 subj ftt)
      (h3 : C2ChipReady z q c2
        (J c0.size c0 subj fth).label.evaluation
        (J c1.size c1 subj ftt).label.evaluation) :
      C2ChipReady z q (.node row [c0, c1, c2]) subj (.cell (.atom 2) (.cell fth ftt))
  | op6 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fth ftth fttt : Noun} {b : ℕ}
      (hstate : row.1.1 = .s6)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s6)
      (hh : bindFP z (.atom 6) row.1.2.2.2.f_h)
      (hth : bindFP z fth row.1.2.2.2.f_th)
      (htth : bindFP z ftth row.1.2.2.2.f_tth)
      (httt : bindFP z fttt row.1.2.2.2.f_ttt)
      (hb : b = 0 ∨ b = 1)
      (hcondE : (J c1.size c1 subj fth).label.evaluation = .atom b)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heTakenlink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hcondlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hsTakenlink : c0.label.1.2.2.1.s = row.1.2.2.1.sf1_s)
      (hscondlink : c1.label.1.2.2.1.s = row.1.2.2.1.sf2_s)
      (hT : C2ChipReady z q c0 subj (if b = 0 then ftth else fttt))
      (hC : C2ChipReady z q c1 subj fth) :
      C2ChipReady z q (.node row [c0, c1])
        subj (.cell (.atom 6) (.cell fth (.cell ftth fttt)))
  | op7 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fth ftt : Noun}
      (hstate : row.1.1 = .s7)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s7)
      (hh : bindFP z (.atom 7) row.1.2.2.2.f_h)
      (hth : bindFP z fth row.1.2.2.2.f_th)
      (htt : bindFP z ftt row.1.2.2.2.f_tt)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heHelplink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (heConslink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hsHelplink : c1.label.1.2.2.1.s = row.1.2.2.1.sf2_s)
      (hsConslink : c0.label.1.2.2.1.s = row.1.2.2.1.sf1_s)
      (hHelp : C2ChipReady z q c1 subj fth)
      (hCons : C2ChipReady z q c0 (J c1.size c1 subj fth).label.evaluation ftt) :
      C2ChipReady z q (.node row [c0, c1]) subj (.cell (.atom 7) (.cell fth ftt))
  | op8 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj fth ftt : Noun}
      (hstate : row.1.1 = .s8)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s8)
      (hh : bindFP z (.atom 8) row.1.2.2.2.f_h)
      (hth : bindFP z fth row.1.2.2.2.f_th)
      (htt : bindFP z ftt row.1.2.2.2.f_tt)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heHelplink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (heConslink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hsHelplink : c1.label.1.2.2.1.s = row.1.2.2.1.sf2_s)
      (hsConslink : c0.label.1.2.2.1.s = row.1.2.2.1.sf1_s)
      (hHelp : C2ChipReady z q c1 subj fth)
      (hCons : C2ChipReady z q c0
        (.cell (J c1.size c1 subj fth).label.evaluation subj) ftt) :
      C2ChipReady z q (.node row [c0, c1]) subj (.cell (.atom 8) (.cell fth ftt))
  | op9 {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
      {subj coreF : Noun}
      (hstate : row.1.1 = .s9)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s9)
      (hh : bindFP z (.atom 9) row.1.2.2.2.f_h)
      (hax : bindFP z (.atom (ax (row.2 + 3))) row.1.2.2.2.f_th)
      (hcoreF : bindFP z coreF row.1.2.2.2.f_tt)
      (harm : bindFP z (op9ArmF sv ax row.2 (J c0.size c0 subj coreF).label.evaluation) row.1.2.2.1.sf2_f)
      (haxK : ((ax (row.2 + 3) : ℕ) : K) = row.1.2.2.2.f_th.leaf)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heCorelink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (heInvlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hsCorelink : c0.label.1.2.2.1.s = row.1.2.2.1.sf1_s)
      (hsInvlink : c1.label.1.2.2.1.s = row.1.2.2.1.sf2_s)
      (hCore : C2ChipReady z q c0 subj coreF)
      (hInv : C2ChipReady z q c1
        (J c0.size c0 subj coreF).label.evaluation
        (op9ArmF sv ax row.2 (J c0.size c0 subj coreF).label.evaluation)) :
      C2ChipReady z q (.node row [c0, c1])
        subj (.cell (.atom 9) (.cell (.atom (ax (row.2 + 3))) coreF))

/-- The root evaluation binding of a ready child, through its `e`-link to the parent slot. -/
theorem readyF_child_eval_binds {z : K} (hz : z ≠ 0) {q : ℕ} [CharP K q]
    {c : NTree ((State × DTcomp K) × ℕ)} {subj formula : Noun} {slot : FP K}
    (hR : C2JoinReadyF (sv := sv) (ax := ax) z q c subj formula)
    (hlink : c.label.1.2.2.1.e = slot) :
    bindFP z (J c.size c subj formula).label.evaluation slot := by
  have hb := (ComputeTreeBinds.root (computeTreeBinds_of_readyF hz (Nat.le_refl _) hR)).2.2.2.2.2.1
  simpa [hlink] using hb

/-- **The interleaved induction.**  The chip-side bundle and the ROOT subject binding give the
per-fuel readiness bundle: each child's subject binding is derived from `V_comp`'s `sf_i.s`
clause, the `Fcomp` subject link, and — for the dependent children
— the sibling's root evaluation binding, a conclusion of `computeTreeBinds_of_readyF`. -/
theorem c2JoinReadyF_of_chipReady {z : K} (hz : z ≠ 0) {q : ℕ} [CharP K q]
    {t : NTree ((State × DTcomp K) × ℕ)} {subj formula : Noun}
    (hC : C2ChipReady (sv := sv) (ax := ax) z q t subj formula) :
    bindFP z subj t.label.1.2.2.1.s →
      C2JoinReadyF (sv := sv) (ax := ax) z q t subj formula := by
  induction hC with
  | @op0 row subj tail hstate hzRow hpubSt hh ht he hax hV =>
      intro hs
      exact C2JoinReadyF.op0 hstate hzRow hpubSt hs hh ht he hax hV
  | @op1 row subj tail hstate hzRow hpubSt hh ht hV =>
      intro hs
      exact C2JoinReadyF.op1 hstate hzRow hpubSt hs hh ht hV
  | @cons row c0 c1 subj fh ft hstate hzRow hpubSt hfh hft hV heLlink heRlink
      hsLlink hsRlink hL hR ihL ihR =>
      intro hs
      have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := hV.2.2.2.2
      simp only [evalV, hpubSt] at hev
      have hs0 : bindFP z subj c0.label.1.2.2.1.s := by rw [hsLlink, hev.1]; exact hs
      have hs1 : bindFP z subj c1.label.1.2.2.1.s := by rw [hsRlink, hev.2.2.1]; exact hs
      exact C2JoinReadyF.cons hstate hzRow hpubSt hs hfh hft hV heLlink heRlink
        (ihL hs0) (ihR hs1)
  | @op3 row c0 subj tail hstate hzRow hpubSt hh ht hV hwin helink hslink hC ih =>
      intro hs
      have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := hV.2.2.2.2
      simp only [evalV, hpubSt] at hev
      have hs0 : bindFP z subj c0.label.1.2.2.1.s := by rw [hslink, hev.1]; exact hs
      exact C2JoinReadyF.op3 hstate hzRow hpubSt hs hh ht hV hwin helink (ih hs0)
  | @op4 row c0 subj tail k hstate hzRow hpubSt hh ht hV hke helink hslink hC ih =>
      intro hs
      have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := hV.2.2.2.2
      simp only [evalV, hpubSt] at hev
      have hs0 : bindFP z subj c0.label.1.2.2.1.s := by rw [hslink, hev.1]; exact hs
      have hR0 := ih hs0
      have hcall : bindFP z (.atom k) row.1.2.2.1.sf1_e := by
        have := readyF_child_eval_binds hz hR0 helink
        rwa [hke] at this
      exact C2JoinReadyF.op4 hstate hzRow hpubSt hs hh ht hV hke hcall hR0
  | @op5 row c0 c1 subj fth ftt hstate hzRow hpubSt hh hth htt hV hcast hfaith
      heLlink heRlink hsLlink hsRlink hL hR ihL ihR =>
      intro hs
      have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := hV.2.2.2.2
      simp only [evalV, hpubSt] at hev
      have hs0 : bindFP z subj c0.label.1.2.2.1.s := by rw [hsLlink, hev.1]; exact hs
      have hs1 : bindFP z subj c1.label.1.2.2.1.s := by rw [hsRlink, hev.2.2.1]; exact hs
      exact C2JoinReadyF.op5 hstate hzRow hpubSt hs hh hth htt hV hcast hfaith heLlink heRlink
        (ihL hs0) (ihR hs1)
  | @op2 row c0 c1 c2 subj fth ftt hstate hzRow hpubSt hh hth htt hV he1link he2link heApplink
      hs1link hs2link hs3link h1 h2 h3 ih1 ih2 ih3 =>
      intro hs
      have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := hV.2.2.2.2
      simp only [evalV, hpubSt] at hev
      have hs0 : bindFP z subj c0.label.1.2.2.1.s := by rw [hs1link, hev.1]; exact hs
      have hs1 : bindFP z subj c1.label.1.2.2.1.s := by rw [hs2link, hev.2.2.1]; exact hs
      have hR0 := ih1 hs0
      have hR1 := ih2 hs1
      -- the dependent subject: `c2.s = sf3_s = sf1_e`, bound by child 0's evaluation
      have hs2 : bindFP z (J c0.size c0 subj fth).label.evaluation c2.label.1.2.2.1.s := by
        rw [hs3link, hev.2.2.2.2.1]
        exact readyF_child_eval_binds hz hR0 he1link
      exact C2JoinReadyF.op2 hstate hzRow hpubSt hs hh hth htt hV he1link he2link heApplink
        hR0 hR1 (ih3 hs2)
  | @op6 row c0 c1 subj fth ftth fttt b hstate hzRow hpubSt hh hth htth httt hb hcondE hV
      heTakenlink hcondlink hsTakenlink hscondlink hT hC ihT ihC =>
      intro hs
      have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := hV.2.2.2.2
      simp only [evalV, hpubSt] at hev
      have hs0 : bindFP z subj c0.label.1.2.2.1.s := by rw [hsTakenlink, hev.1]; exact hs
      have hs1 : bindFP z subj c1.label.1.2.2.1.s := by rw [hscondlink, hev.2.2.2.1]; exact hs
      exact C2JoinReadyF.op6 hstate hzRow hpubSt hs hh hth htth httt hb hcondE hV heTakenlink
        hcondlink (ihT hs0) (ihC hs1)
  | @op7 row c0 c1 subj fth ftt hstate hzRow hpubSt hh hth htt hV heHelplink heConslink
      hsHelplink hsConslink hHelp hCons ihHelp ihCons =>
      intro hs
      have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := hV.2.2.2.2
      simp only [evalV, hpubSt] at hev
      have hs1 : bindFP z subj c1.label.1.2.2.1.s := by rw [hsHelplink, hev.2.2.2.1]; exact hs
      have hRHelp := ihHelp hs1
      -- the dependent subject: `c0.s = sf1_s = sf2_e`, bound by the helper's evaluation
      have hs0 : bindFP z (J c1.size c1 subj fth).label.evaluation c0.label.1.2.2.1.s := by
        rw [hsConslink, hev.1]
        exact readyF_child_eval_binds hz hRHelp heHelplink
      exact C2JoinReadyF.op7 hstate hzRow hpubSt hs hh hth htt hV heHelplink heConslink
        hRHelp (ihCons hs0)
  | @op8 row c0 c1 subj fth ftt hstate hzRow hpubSt hh hth htt hV heHelplink heConslink
      hsHelplink hsConslink hHelp hCons ihHelp ihCons =>
      intro hs
      have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := hV.2.2.2.2
      simp only [evalV, hpubSt] at hev
      have hs1 : bindFP z subj c1.label.1.2.2.1.s := by rw [hsHelplink, hev.2.2.2.1]; exact hs
      have hRHelp := ihHelp hs1
      -- the dependent subject: `c0.s = sf1_s = cons z sf2_e s`
      have hs0 : bindFP z (.cell (J c1.size c1 subj fth).label.evaluation subj)
          c0.label.1.2.2.1.s := by
        rw [hsConslink, hev.1, hzRow]
        exact bindFP_cons hz _ _ _ _ (readyF_child_eval_binds hz hRHelp heHelplink) hs
      exact C2JoinReadyF.op8 hstate hzRow hpubSt hs hh hth htt hV heHelplink heConslink
        hRHelp (ihCons hs0)
  | @op9 row c0 c1 subj coreF hstate hzRow hpubSt hh hax hcoreF harm haxK hV heCorelink
      heInvlink hsCorelink hsInvlink hCore hInv ihCore ihInv =>
      intro hs
      have hev : evalV row.1.2.1 row.1.2.2.1 row.1.2.2.2 := hV.2.2.2.2
      simp only [evalV, hpubSt] at hev
      have hs0 : bindFP z subj c0.label.1.2.2.1.s := by rw [hsCorelink, hev.1]; exact hs
      have hRCore := ihCore hs0
      -- the dependent subject: `c1.s = sf2_s = sf1_e`, bound by the core's evaluation
      have hs1 : bindFP z (J c0.size c0 subj coreF).label.evaluation c1.label.1.2.2.1.s := by
        rw [hsInvlink, hev.2.2.1]
        exact readyF_child_eval_binds hz hRCore heCorelink
      exact C2JoinReadyF.op9 hstate hzRow hpubSt hs hh hax hcoreF harm haxK hV heCorelink
        heInvlink hRCore (ihInv hs1)

/-- `ComputeTreeBinds` of the C2 join from the chip-side bundle and the root subject binding. -/
theorem computeTreeBinds_of_chipReady {z : K} (hz : z ≠ 0) {q fuel : ℕ} [CharP K q]
    {t : NTree ((State × DTcomp K) × ℕ)} {subj formula : Noun}
    (hfuel : t.size ≤ fuel)
    (hC : C2ChipReady (sv := sv) (ax := ax) z q t subj formula)
    (hs : bindFP z subj t.label.1.2.2.1.s) :
    ComputeTreeBinds z (J fuel t subj formula) (mapNTree Prod.fst t) :=
  computeTreeBinds_of_readyF hz hfuel (c2JoinReadyF_of_chipReady hz hC hs)

end Nock.NockVMROM.Thm54.SVReadyFuelF
