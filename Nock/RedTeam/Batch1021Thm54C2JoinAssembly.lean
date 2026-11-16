/-
  Nock/RedTeam/Batch1021Thm54C2JoinAssembly.lean

  `StrategyOfTracesR0AC2.c2JoinFuel` on the S-carrying exec tree
  `NTree ((State × DTcomp K) × ℕ)`, bound against the exec tree `mapNTree Prod.fst t`.

  * §A — the fuel unfoldings `J_*` and the per-opcode `c2SkeletonRow_eq_skelOp*` / `computeTreeBinds_join_op*`;
  * §B — `C2JoinReady`: the per-node premises `V_comp` determines plus child readiness, with the
    served facts `he` (OP0) / `harm` (OP9) and the axis facts `hax` / `haxK` in route-B form;
    `computeTreeBinds_of_ready`: the induction;
  * §D — at `O`: `ComputeTreeBinds z (c2ComputeTree O Qc Qm c) (execOfTraces …).computeTree` from
    readiness of the S-carrying tree.
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
import Nock.RedTeam.Batch525Thm54ComputeTreeBinds
import Nock.RedTeam.Batch530Thm54ComputeTreeBindsDeployed
import Nock.NockVMROM.Thm54.P8Core.Batch1021Thm54C2JoinAssembly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1021

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch525
open Nock.GlobalCarryRecognizer
open scoped Polynomial
open Polynomial

variable {K : Type} [Field K] [DecidableEq K]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}

set_option quotPrecheck false

/-- The C2 join on the S-carrying exec tree, at the served lookup `sv` and the axes `ax`. -/
local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-! ## §A  Fuel unfoldings and the per-opcode join steps -/

/-! ## §B.2  s0 / s2 / s5–s9 -/

/-! ## §B.3  Tree induction: `ComputeJoinReady` packages per-node `V_comp` -/

variable (sv ax) in
/-- Per-node data `V_comp` determines plus child
    readiness.  Child evaluation `bindFP`s are derived from
    `ComputeTreeBinds.root` + `childLink` after the IH. -/
inductive C2JoinReady (z : K) (q : ℕ) :
    NTree ((State × DTcomp K) × ℕ) → Noun → Noun → Prop
  | op0 {row : (State × DTcomp K) × ℕ} {subj tail : Noun}
      (hstate : row.1.1 = .s0)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s0)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 0) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (he : bindFP z (sv .verify_child (row.2 + 2))
        row.1.2.2.1.e)
      (hax : ((ax (row.2 + 2) : ℕ) : K) =
        row.1.2.2.2.f_t.leaf)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2) :
      C2JoinReady z q (.node row []) subj (.cell (.atom 0) tail)
  | op1 {row : (State × DTcomp K) × ℕ} {subj tail : Noun}
      (hstate : row.1.1 = .s1)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s1)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 1) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2) :
      C2JoinReady z q (.node row []) subj (.cell (.atom 1) tail)
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
      (hL : C2JoinReady z q c0 subj fh)
      (hR : C2JoinReady z q c1 subj ft) :
      C2JoinReady z q (.node row [c0, c1]) subj (.cell fh ft)
  | op3 {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)}
      {subj tail : Noun}
      (hstate : row.1.1 = .s3)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s3)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 3) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (hwin : ∀ n : ℕ,
        OpcodeSemantics.SizeWindow z
          (J n c0 subj tail).label.evaluation)
      (helink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hC : C2JoinReady z q c0 subj tail) :
      C2JoinReady z q (.node row [c0]) subj (.cell (.atom 3) tail)
  | op4 {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)}
      {subj tail : Noun} {k : ℕ}
      (hstate : row.1.1 = .s4)
      (hzRow : row.1.2.1.z = z)
      (hpubSt : row.1.2.2.1.state = .s4)
      (hs : bindFP z subj row.1.2.2.1.s)
      (hh : bindFP z (.atom 4) row.1.2.2.2.f_h)
      (ht : bindFP z tail row.1.2.2.2.f_t)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (hke : ∀ n : ℕ,
        (J n c0 subj tail).label.evaluation =
          .atom k)
      (hcall : bindFP z (.atom k) row.1.2.2.1.sf1_e)
      (hC : C2JoinReady z q c0 subj tail) :
      C2JoinReady z q (.node row [c0]) subj (.cell (.atom 4) tail)
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
      (hfaith : ∀ n : ℕ,
        OpcodeSemantics.PairFaithful z q
          (J n c0 subj fth).label.evaluation
          (J n c1 subj ftt).label.evaluation)
      (heLlink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (heRlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hL : C2JoinReady z q c0 subj fth)
      (hR : C2JoinReady z q c1 subj ftt) :
      C2JoinReady z q (.node row [c0, c1])
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
      (h1 : C2JoinReady z q c0 subj fth)
      (h2 : C2JoinReady z q c1 subj ftt)
      (h3 : C2JoinReady z q c2
        (J c0.size c0 subj fth).label.evaluation
        (J c1.size c1 subj ftt).label.evaluation) :
      C2JoinReady z q (.node row [c0, c1, c2])
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
      (hcondE : ∀ n : ℕ,
        (J n c1 subj fth).label.evaluation =
          .atom b)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heTakenlink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (hcondlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hT : C2JoinReady z q c0 subj
        (if b = 0 then ftth else fttt))
      (hC : C2JoinReady z q c1 subj fth) :
      C2JoinReady z q (.node row [c0, c1])
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
      (hHelp : C2JoinReady z q c1 subj fth)
      (hCons : C2JoinReady z q c0
        (J c1.size c1 subj fth).label.evaluation
        ftt) :
      C2JoinReady z q (.node row [c0, c1])
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
      (hHelp : C2JoinReady z q c1 subj fth)
      (hCons : C2JoinReady z q c0
        (.cell
          (J c1.size c1 subj fth).label.evaluation
          subj) ftt) :
      C2JoinReady z q (.node row [c0, c1])
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
      (harm : bindFP z (sv .verify_child (row.2 + 3))
        row.1.2.2.1.sf2_f)
      (haxK : ((ax (row.2 + 3) : ℕ) : K) =
        row.1.2.2.2.f_th.leaf)
      (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
      (heCorelink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
      (heInvlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
      (hCore : C2JoinReady z q c0 subj coreF)
      (hInv : C2JoinReady z q c1
        (J c0.size c0 subj coreF).label.evaluation
        (sv .verify_child (row.2 + 3))) :
      C2JoinReady z q (.node row [c0, c1])
        subj (.cell (.atom 9)
          (.cell (.atom (ax (row.2 + 3))) coreF))

theorem computeTreeBinds_of_ready {z : K} (hz : z ≠ 0) {q fuel : ℕ}
    {t : NTree ((State × DTcomp K) × ℕ)} {subj formula : Noun}
    (hfuel : t.size ≤ fuel)
    (hR : C2JoinReady sv ax z q t subj formula) :
    ComputeTreeBinds z (J fuel t subj formula) (mapNTree Prod.fst t) := by
  induction hR generalizing fuel with
  | @op0 row subj tail hstate hzRow hpubSt hs hh ht he hax hV =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      exact computeTreeBinds_join_op0 hz subj tail row hstate hzRow hpubSt
        hs hh ht he hax hV
  | @op1 row subj tail hstate hzRow hpubSt hs hh ht hV =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      exact computeTreeBinds_join_op1 hz subj tail row hstate hzRow hpubSt
        hs hh ht hV
  | @cons row c0 c1 subj fh ft hstate hzRow hpubSt hs hfh hft hV
      heLlink heRlink hL hR ihL ihR =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
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
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
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
      exact computeTreeBinds_join_op3 hz subj tail row c0
        hstate hzRow hpubSt hs hh ht hcall (hwin n) hV
        (J_subject n c0 subj tail)
        (J_formula n c0 subj tail) hCb
  | @op4 row c0 subj tail k hstate hzRow hpubSt hs hh ht hV hke hcall hC ih =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0]).size = 1 + c0.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have hn0 : c0.size ≤ n := by
        have := hfuel
        simp [hsz] at this
        omega
      have hCb := ih hn0
      exact computeTreeBinds_join_op4 hz subj tail k row c0
        hstate hzRow hpubSt hs hh ht hcall hV
        (J_subject n c0 subj tail)
        (J_formula n c0 subj tail) (hke n) hCb
  | @op5 row c0 c1 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      hcast hfaith heLlink heRlink hL hR ihL ihR =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
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
      exact computeTreeBinds_join_op5 hz subj fth ftt row c0 c1
        hstate hzRow hpubSt hs hh hth htt heL heR hcast (hfaith n) hV hLb hRb
  | @op2 row c0 c1 c2 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      he1link he2link heApplink h1 h2 h3 ih1 ih2 ih3 =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
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
      have heq0 := J_eq_of_le (sv := sv) (ax := ax) c0 subj fth
        (Nat.le_refl _) hn0
      have heq1 := J_eq_of_le (sv := sv) (ax := ax) c1 subj ftt
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
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
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
      have hcond : bindFP z (.atom b) row.1.2.2.1.sf2_e := by
        have hb' := (ComputeTreeBinds.root hCb).2.2.2.2.2.1
        simpa [hcondlink, hcondE n] using hb'
      have heTaken : bindFP z
          (J n c0 subj
            (if b = 0 then ftth else fttt)).label.evaluation
          row.1.2.2.1.sf1_e := by
        have hb' := (ComputeTreeBinds.root hTb).2.2.2.2.2.1
        simpa [heTakenlink] using hb'
      exact computeTreeBinds_join_op6 hz subj fth ftth fttt b row c0 c1
        hstate hzRow hpubSt hs hh hth htth httt hb (hcondE n) hcond heTaken
        hV hTb hCb
  | @op7 row c0 c1 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      heHelplink heConslink hHelp hCons ihHelp ihCons =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hHelpb := ihHelp hn1
      have heq := J_eq_of_le (sv := sv) (ax := ax) c1 subj fth
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
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hHelpb := ihHelp hn1
      have heq := J_eq_of_le (sv := sv) (ax := ax) c1 subj fth
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
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hCoreb := ihCore hn0
      have heq := J_eq_of_le (sv := sv) (ax := ax) c0 subj coreF
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
            (sv .verify_child (row.2 + 3))).label.evaluation
          row.1.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hInvb).2.2.2.2.2.1
        simpa [heInvlink] using hb
      exact computeTreeBinds_join_op9 hz subj coreF row c0 c1
        hstate hzRow hpubSt hs hh hax hcoreF harm heCore heInv haxK hV
        hCoreb hInvb


variable [Fintype K] [CharP K (ringChar K)]

theorem C2JoinReady.label_z {z : K} {q : ℕ}
    {t : NTree ((State × DTcomp K) × ℕ)} {subj formula : Noun}
    (hR : C2JoinReady sv ax z q t subj formula) :
    t.label.1.2.1.z = z := by
  cases hR <;> assumption

theorem bindFP_vcomp_opcode {z : K} {inp : ComputeTable.Inputs K}
    {pub : ComputeTable.Pub K} {dec : ComputeTable.Dec K}
    (hV : Vcomp inp pub dec) (hz : inp.z = z) {op : ℕ}
    (hst : pub.state.toNat = op) (hcons : pub.state ≠ State.cons) :
    bindFP z (.atom op) dec.f_h := by
  rw [bindFP, vcomp_f_h_eq_atomFP hV hst hcons, hz, enc_atom]

/-- Child `(s,f,e)` is the parent's `sfTriple` (`childLinkComp`, `:1690`). -/
theorem fcomp_child_sfe {lbl : State × DTcomp K}
    {xout : Fin 3 → Option (State × DTcomp K)}
    (hF : Fcomp lbl xout) (i : Fin 3)
    (hi : (i : ℕ) < fanoutComp lbl.1) {c : State × DTcomp K}
    (hc : xout i = some c) :
    (c.2.2.1.s, c.2.2.1.f, c.2.2.1.e) = sfTriple lbl.2.2.1 i := by
  have hlink := hF.2.2.2 i hi
  simpa [hc] using hlink

/-- `ComputeJoinReady` of a `s0` leaf — every noun is `V_comp`-determined. -/
theorem c2JoinReady_op0_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ} {subj tail : Noun}
    (hstate : row.1.1 = .s0)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s0)
    (hs : bindFP z subj row.1.2.2.1.s)
    (ht : bindFP z tail row.1.2.2.2.f_t)
    (he : bindFP z (sv .verify_child (row.2 + 2))
      row.1.2.2.1.e)
    (hax : ((ax (row.2 + 2) : ℕ) : K) =
      row.1.2.2.2.f_t.leaf)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2) :
    C2JoinReady sv ax z q (.node row []) subj (.cell (.atom 0) tail) := by
  have hcons : row.1.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.1.2.2.1.state.toNat = 0 := by simp [hpubSt, State.toNat]
  have hh := Batch530.bindFP_vcomp_opcode hV hzRow hst hcons
  exact C2JoinReady.op0 hstate hzRow hpubSt hs hh ht he hax hV

/-- `ComputeJoinReady` of a `s1` leaf. -/
theorem c2JoinReady_op1_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ} {subj tail : Noun}
    (hstate : row.1.1 = .s1)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s1)
    (hs : bindFP z subj row.1.2.2.1.s)
    (ht : bindFP z tail row.1.2.2.2.f_t)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2) :
    C2JoinReady sv ax z q (.node row []) subj (.cell (.atom 1) tail) := by
  have hcons : row.1.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.1.2.2.1.state.toNat = 1 := by simp [hpubSt, State.toNat]
  have hh := Batch530.bindFP_vcomp_opcode hV hzRow hst hcons
  exact C2JoinReady.op1 hstate hzRow hpubSt hs hh ht hV

/-- `cons` packages `V_comp` plus both child `Ready`s (`evalV` `:1728-1742`). -/
theorem c2JoinReady_cons_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
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
    (hL : C2JoinReady sv ax z q c0 subj fh)
    (hR : C2JoinReady sv ax z q c1 subj ft) :
    C2JoinReady sv ax z q (.node row [c0, c1]) subj (.cell fh ft) :=
  C2JoinReady.cons hstate hzRow hpubSt hs hfh hft hV heLlink heRlink hL hR

theorem c2JoinReady_op3_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)}
    {subj tail : Noun}
    (hstate : row.1.1 = .s3)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s3)
    (hs : bindFP z subj row.1.2.2.1.s)
    (ht : bindFP z tail row.1.2.2.2.f_t)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hwin : ∀ n : ℕ,
      OpcodeSemantics.SizeWindow z
        (J n c0 subj tail).label.evaluation)
    (helink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
    (hC : C2JoinReady sv ax z q c0 subj tail) :
    C2JoinReady sv ax z q (.node row [c0]) subj (.cell (.atom 3) tail) := by
  have hcons : row.1.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.1.2.2.1.state.toNat = 3 := by simp [hpubSt, State.toNat]
  have hh := Batch530.bindFP_vcomp_opcode hV hzRow hst hcons
  exact C2JoinReady.op3 hstate hzRow hpubSt hs hh ht hV hwin helink hC

theorem c2JoinReady_op4_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ} {c0 : NTree ((State × DTcomp K) × ℕ)}
    {subj tail : Noun} {k : ℕ}
    (hstate : row.1.1 = .s4)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s4)
    (hs : bindFP z subj row.1.2.2.1.s)
    (ht : bindFP z tail row.1.2.2.2.f_t)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hke : ∀ n : ℕ,
      (J n c0 subj tail).label.evaluation =
        .atom k)
    (hcall : bindFP z (.atom k) row.1.2.2.1.sf1_e)
    (hC : C2JoinReady sv ax z q c0 subj tail) :
    C2JoinReady sv ax z q (.node row [c0]) subj (.cell (.atom 4) tail) := by
  have hcons : row.1.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.1.2.2.1.state.toNat = 4 := by simp [hpubSt, State.toNat]
  have hh := Batch530.bindFP_vcomp_opcode hV hzRow hst hcons
  exact C2JoinReady.op4 hstate hzRow hpubSt hs hh ht hV hke hcall hC

theorem c2JoinReady_op5_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
    {subj fth ftt : Noun}
    (hstate : row.1.1 = .s5)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s5)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hth : bindFP z fth row.1.2.2.2.f_th)
    (htt : bindFP z ftt row.1.2.2.2.f_tt)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hfaith : ∀ n : ℕ,
      OpcodeSemantics.PairFaithful z q
        (J n c0 subj fth).label.evaluation
        (J n c1 subj ftt).label.evaluation)
    (heLlink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
    (heRlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
    (hL : C2JoinReady sv ax z q c0 subj fth)
    (hR : C2JoinReady sv ax z q c1 subj ftt) :
    C2JoinReady sv ax z q (.node row [c0, c1])
      subj (.cell (.atom 5) (.cell fth ftt)) := by
  have hcons : row.1.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.1.2.2.1.state.toNat = 5 := by simp [hpubSt, State.toNat]
  have hh := Batch530.bindFP_vcomp_opcode hV hzRow hst hcons
  exact C2JoinReady.op5 hstate hzRow hpubSt hs hh hth htt hV
    hcast hfaith heLlink heRlink hL hR

theorem c2JoinReady_op2_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ}
    {c0 c1 c2 : NTree ((State × DTcomp K) × ℕ)}
    {subj fth ftt : Noun}
    (hstate : row.1.1 = .s2)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s2)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hth : bindFP z fth row.1.2.2.2.f_th)
    (htt : bindFP z ftt row.1.2.2.2.f_tt)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (he1link : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
    (he2link : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
    (heApplink : c2.label.1.2.2.1.e = row.1.2.2.1.sf3_e)
    (h1 : C2JoinReady sv ax z q c0 subj fth)
    (h2 : C2JoinReady sv ax z q c1 subj ftt)
    (h3 : C2JoinReady sv ax z q c2
      (J c0.size c0 subj fth).label.evaluation
      (J c1.size c1 subj ftt).label.evaluation) :
    C2JoinReady sv ax z q (.node row [c0, c1, c2])
      subj (.cell (.atom 2) (.cell fth ftt)) := by
  have hcons : row.1.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.1.2.2.1.state.toNat = 2 := by simp [hpubSt, State.toNat]
  have hh := Batch530.bindFP_vcomp_opcode hV hzRow hst hcons
  exact C2JoinReady.op2 hstate hzRow hpubSt hs hh hth htt hV
    he1link he2link heApplink h1 h2 h3

theorem c2JoinReady_op6_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
    {subj fth ftth fttt : Noun} {b : ℕ}
    (hstate : row.1.1 = .s6)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s6)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hth : bindFP z fth row.1.2.2.2.f_th)
    (htth : bindFP z ftth row.1.2.2.2.f_tth)
    (httt : bindFP z fttt row.1.2.2.2.f_ttt)
    (hb : b = 0 ∨ b = 1)
    (hcondE : ∀ n : ℕ,
      (J n c1 subj fth).label.evaluation =
        .atom b)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (heTakenlink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
    (hcondlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
    (hT : C2JoinReady sv ax z q c0 subj
      (if b = 0 then ftth else fttt))
    (hC : C2JoinReady sv ax z q c1 subj fth) :
    C2JoinReady sv ax z q (.node row [c0, c1])
      subj (.cell (.atom 6) (.cell fth (.cell ftth fttt))) := by
  have hcons : row.1.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.1.2.2.1.state.toNat = 6 := by simp [hpubSt, State.toNat]
  have hh := Batch530.bindFP_vcomp_opcode hV hzRow hst hcons
  exact C2JoinReady.op6 hstate hzRow hpubSt hs hh hth htth httt hb
    hcondE hV heTakenlink hcondlink hT hC

theorem c2JoinReady_op7_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
    {subj fth ftt : Noun}
    (hstate : row.1.1 = .s7)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s7)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hth : bindFP z fth row.1.2.2.2.f_th)
    (htt : bindFP z ftt row.1.2.2.2.f_tt)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (heHelplink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
    (heConslink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
    (hHelp : C2JoinReady sv ax z q c1 subj fth)
    (hCons : C2JoinReady sv ax z q c0
      (J c1.size c1 subj fth).label.evaluation
      ftt) :
    C2JoinReady sv ax z q (.node row [c0, c1])
      subj (.cell (.atom 7) (.cell fth ftt)) := by
  have hcons : row.1.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.1.2.2.1.state.toNat = 7 := by simp [hpubSt, State.toNat]
  have hh := Batch530.bindFP_vcomp_opcode hV hzRow hst hcons
  exact C2JoinReady.op7 hstate hzRow hpubSt hs hh hth htt hV
    heHelplink heConslink hHelp hCons

theorem c2JoinReady_op8_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
    {subj fth ftt : Noun}
    (hstate : row.1.1 = .s8)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s8)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hth : bindFP z fth row.1.2.2.2.f_th)
    (htt : bindFP z ftt row.1.2.2.2.f_tt)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (heHelplink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
    (heConslink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
    (hHelp : C2JoinReady sv ax z q c1 subj fth)
    (hCons : C2JoinReady sv ax z q c0
      (.cell
        (J c1.size c1 subj fth).label.evaluation
        subj) ftt) :
    C2JoinReady sv ax z q (.node row [c0, c1])
      subj (.cell (.atom 8) (.cell fth ftt)) := by
  have hcons : row.1.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.1.2.2.1.state.toNat = 8 := by simp [hpubSt, State.toNat]
  have hh := Batch530.bindFP_vcomp_opcode hV hzRow hst hcons
  exact C2JoinReady.op8 hstate hzRow hpubSt hs hh hth htt hV
    heHelplink heConslink hHelp hCons

theorem c2JoinReady_op9_of_vcomp {z : K} {q : ℕ}
    {row : (State × DTcomp K) × ℕ} {c0 c1 : NTree ((State × DTcomp K) × ℕ)}
    {subj coreF : Noun}
    (hstate : row.1.1 = .s9)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s9)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hax : bindFP z (.atom (ax (row.2 + 3)))
      row.1.2.2.2.f_th)
    (hcoreF : bindFP z coreF row.1.2.2.2.f_tt)
    (harm : bindFP z (sv .verify_child (row.2 + 3))
      row.1.2.2.1.sf2_f)
    (haxK : ((ax (row.2 + 3) : ℕ) : K) =
      row.1.2.2.2.f_th.leaf)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (heCorelink : c0.label.1.2.2.1.e = row.1.2.2.1.sf1_e)
    (heInvlink : c1.label.1.2.2.1.e = row.1.2.2.1.sf2_e)
    (hCore : C2JoinReady sv ax z q c0 subj coreF)
    (hInv : C2JoinReady sv ax z q c1
      (J c0.size c0 subj coreF).label.evaluation
      (sv .verify_child (row.2 + 3))) :
    C2JoinReady sv ax z q (.node row [c0, c1])
      subj (.cell (.atom 9)
        (.cell (.atom (ax (row.2 + 3))) coreF)) := by
  have hcons : row.1.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.1.2.2.1.state.toNat = 9 := by simp [hpubSt, State.toNat]
  have hh := Batch530.bindFP_vcomp_opcode hV hzRow hst hcons
  exact C2JoinReady.op9 hstate hzRow hpubSt hs hh hax hcoreF harm haxK hV
    heCorelink heInvlink hCore hInv

/-! ## §D  At `O`: the C2 compute tree binds the exec tree from readiness -/

section AtO

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F] [FiniteDimensional F K]
  {hOrb : ℕ}
  (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-- `P.computeChip` at `O` (as in `StrategyOfTracesR0AC2`). -/
local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

/-- **`ComputeTreeBinds` of the C2 compute tree against the decoded exec tree**, from readiness of
the S-carrying tree at the traces' served lookup and certificate axes. -/
theorem computeTreeBinds_C2_of_ready
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) {z : K} (hz : z ≠ 0) {q : ℕ}
    (hR : C2JoinReady (c2ServedOf O Qm c) (c2AxOf O Qc c) z q (c2TreeOfTraces O Qc c)
      O.verifier.raw.claim.subject O.verifier.raw.claim.formula) :
    ComputeTreeBinds z (c2ComputeTree O Qc Qm c) (execOfTraces O Qc Qm c h).computeTree := by
  have h1 := computeTreeBinds_of_ready (sv := c2ServedOf O Qm c) (ax := c2AxOf O Qc c) hz
    (Nat.le_refl (c2TreeOfTraces O Qc c).size) hR
  rw [c2TreeOfTraces_fst O Qc Qm c h] at h1
  exact h1

end AtO

end Nock.RedTeam.Batch1021

#print axioms Nock.RedTeam.Batch1021.computeTreeBinds_join_cons
#print axioms Nock.RedTeam.Batch1021.computeTreeBinds_join_op0
#print axioms Nock.RedTeam.Batch1021.computeTreeBinds_join_op9
#print axioms Nock.RedTeam.Batch1021.computeTreeBinds_of_ready
#print axioms Nock.RedTeam.Batch1021.c2JoinReady_op0_of_vcomp
#print axioms Nock.RedTeam.Batch1021.c2JoinReady_op9_of_vcomp
#print axioms Nock.RedTeam.Batch1021.computeTreeBinds_C2_of_ready
