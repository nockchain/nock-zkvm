/-
  Nock/RedTeam/Batch1090Thm54C2ReadyFuel.lean

  * §B `computeTreeBinds_of_readyF` — the induction against it (`J_eq_of_le` at the four sites).
  * §C `C2ChipReady` — the bundle with NO subject binding, plus the `Fcomp` subject links
    `c.s = sf_i.s`; `c2JoinReadyF_of_chipReady` — readiness is
    interleaved with binding: every child's subject binding is derived from `V_comp`'s `sf_i.s`
    clause, and for the dependent subjects (OP2's third child,
    OP7 / OP8's first, OP9's second) from the sibling's root evaluation binding, a conclusion of
    `computeTreeBinds_of_readyF` inside the same induction.  OP4's `hcall` is derived from `hke`.
  * §F — `BindsAtCoin` at `strategyOfTracesR0AC2` from `C2ChipReady` + the root subject binding.
-/
import Nock.RedTeam.Batch1021Thm54C2JoinAssembly
import Nock.RedTeam.Batch1024Thm54C2BindsAtCoin
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1090

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1021
open Nock.RedTeam.Batch525
open Nock.GlobalCarryRecognizer

variable {K : Type} [Field K] [DecidableEq K]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}

set_option quotPrecheck false

local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-! ## §A  The per-fuel bundle (verbatim `ReadyFuelRestated.C2JoinReadyF`) -/

/-! ## §B  The induction, restated against the per-fuel bundle -/

/-! ## §C  The `hs`-free chip-side bundle and the interleaved induction -/

/-! ## §D  Tree A — `[4 [3 [0 b]]]` with a cell served at the OP0 row, against QK's event -/

section TreeA

variable (row4 row3 row0 : (State × DTcomp K) × ℕ) (subj b : Noun)

abbrev treeA : NTree ((State × DTcomp K) × ℕ) := .node row4 [.node row3 [.node row0 []]]

abbrev formulaA : Noun := .cell (.atom 4) (.cell (.atom 3) (.cell (.atom 0) b))

/-- Fuel 1 on `[0 b]` served a cell: the OP0 node's evaluation is the served cell. -/
theorem J1_op0_eval (h0 : row0.1.1 = .s0) (x y : Noun)
    (hcell : sv .verify_child (row0.2 + 2) = .cell x y) :
    (J 1 (.node row0 []) subj (.cell (.atom 0) b)).label.evaluation = .cell x y := by
  simp [c2JoinFuel, c2SkeletonRow, c2Evaluation, h0, hcell]

/-- Fuel 2 on `[3 [0 b]]` served a cell: `wut (cell x y) = atom 0`. -/
theorem J2_op3_eval (h3 : row3.1.1 = .s3) (h0 : row0.1.1 = .s0) (x y : Noun)
    (hcell : sv .verify_child (row0.2 + 2) = .cell x y) :
    (J 2 (.node row3 [.node row0 []]) subj (.cell (.atom 3) (.cell (.atom 0) b))).label.evaluation
      = .atom 0 := by
  simp [c2JoinFuel, c2SkeletonRow, c2Evaluation, h3, h0, kidSkel, hcell, Noun.wut]

/-- The built C2 skeleton of tree A (memory forest irrelevant to the size-window nouns). -/
abbrev skelA : SemanticSkeleton :=
  { computeTree := J (treeA row4 row3 row0).size (treeA row4 row3 row0) subj (formulaA b)
    memoryForest := [] }

/-- **The served cell is a size-window noun of the built skeleton** — the noun QK's event
(`guardedSizeWindowFailure` of `skeletonEv`) prices at the OP3 row (`requiredSizeWindowNouns`,
`.s3 ↦ skeletonSubformula s 0.result`). -/
theorem treeA_servedCell_mem_sizeWindowNouns
    (h4 : row4.1.1 = .s4) (h3 : row3.1.1 = .s3) (h0 : row0.1.1 = .s0) (x y : Noun)
    (hcell : sv .verify_child (row0.2 + 2) = .cell x y) :
    Noun.cell x y ∈ SizeWindowCounting.skeletonSizeWindowNouns (skelA (sv := sv) (ax := ax) row4 row3 row0 subj b) := by
  -- the OP3 skeleton row
  have hsz : (treeA row4 row3 row0).size = 3 := by simp [treeA, NTree.size]
  let s3 : ComputeRowSkeleton :=
    (J 2 (.node row3 [.node row0 []]) subj (.cell (.atom 3) (.cell (.atom 0) b))).label
  have hmem : s3 ∈ computeSkeletonRows (skelA (sv := sv) (ax := ax) row4 row3 row0 subj b) := by
    simp only [computeSkeletonRows, hsz]
    refine List.mem_map.2 ⟨J 2 (.node row3 [.node row0 []]) subj (.cell (.atom 3) (.cell (.atom 0) b)),
      ?_, rfl⟩
    rw [mem_bfsForest]
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [J_s4 (hstate := h4)]
    refine InTree.sub ?_ (InTree.here _)
    simp [formulaA, nounTail]
  have hst : s3.state = .s3 := by
    simp [s3, c2JoinFuel, c2SkeletonRow, h3]
  have hsub : P8Census.skeletonSubformula s3 0 .result = Noun.cell x y := by
    simp [s3, P8Census.skeletonSubformula, c2JoinFuel, c2SkeletonRow, c2Evaluation, h3, h0,
      fanoutComp, hcell]
  rw [← hsub]
  exact SizeWindowCounting.s3_window_noun_mem _ s3 hmem hst

/-- **Tree A is chip-ready**, from the three rows' chip facts, the served cell, the root-free
links, and the window in the shape QK's event supplies.  `hke` at the OP4 row is DERIVED
(`k = 0`); no premise is stated at a fuel other than the child's own. -/
theorem treeA_chipReady (z : K) (q Λ : ℕ) (x y : Noun)
    (hcell : sv .verify_child (row0.2 + 2) = .cell x y)
    -- QK's event, consumer shape (`P8EventEv.window_of_not_mem_guardedSizeWindowFailure`)
    (hwinEv : ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns (skelA (sv := sv) (ax := ax) row4 row3 row0 subj b),
      n.leaves ≤ Λ → OpcodeSemantics.SizeWindow z n)
    (hΛ : (Noun.cell x y).leaves ≤ Λ)
    -- row 0 (OP0)
    (hstate0 : row0.1.1 = .s0) (hzRow0 : row0.1.2.1.z = z) (hpubSt0 : row0.1.2.2.1.state = .s0)
    (hh0 : bindFP z (.atom 0) row0.1.2.2.2.f_h)
    (ht0 : bindFP z b row0.1.2.2.2.f_t)
    (he0 : bindFP z (sv .verify_child (row0.2 + 2)) row0.1.2.2.1.e)
    (hax0 : ((ax (row0.2 + 2) : ℕ) : K) = row0.1.2.2.2.f_t.leaf)
    (hV0 : Vcomp row0.1.2.1 row0.1.2.2.1 row0.1.2.2.2)
    -- row 3 (OP3)
    (hstate3 : row3.1.1 = .s3) (hzRow3 : row3.1.2.1.z = z) (hpubSt3 : row3.1.2.2.1.state = .s3)
    (hh3 : bindFP z (.atom 3) row3.1.2.2.2.f_h)
    (ht3 : bindFP z (.cell (.atom 0) b) row3.1.2.2.2.f_t)
    (hV3 : Vcomp row3.1.2.1 row3.1.2.2.1 row3.1.2.2.2)
    (helink3 : row0.1.2.2.1.e = row3.1.2.2.1.sf1_e)
    (hslink3 : row0.1.2.2.1.s = row3.1.2.2.1.sf1_s)
    -- row 4 (OP4)
    (hstate4 : row4.1.1 = .s4) (hzRow4 : row4.1.2.1.z = z) (hpubSt4 : row4.1.2.2.1.state = .s4)
    (hh4 : bindFP z (.atom 4) row4.1.2.2.2.f_h)
    (ht4 : bindFP z (.cell (.atom 3) (.cell (.atom 0) b)) row4.1.2.2.2.f_t)
    (hV4 : Vcomp row4.1.2.1 row4.1.2.2.1 row4.1.2.2.2)
    (helink4 : row3.1.2.2.1.e = row4.1.2.2.1.sf1_e)
    (hslink4 : row3.1.2.2.1.s = row4.1.2.2.1.sf1_s) :
    C2ChipReady (sv := sv) (ax := ax) z q (treeA row4 row3 row0) subj (formulaA b) := by
  have hr0 : C2ChipReady (sv := sv) (ax := ax) z q (.node row0 []) subj (.cell (.atom 0) b) :=
    C2ChipReady.op0 hstate0 hzRow0 hpubSt0 hh0 ht0 he0 hax0 hV0
  have hwin : OpcodeSemantics.SizeWindow z
      (J (NTree.node row0 []).size (.node row0 []) subj (.cell (.atom 0) b)).label.evaluation := by
    have hsz : (NTree.node row0 ([] : List (NTree ((State × DTcomp K) × ℕ)))).size = 1 := by
      simp [NTree.size]
    rw [hsz, J1_op0_eval row0 subj b hstate0 x y hcell]
    exact hwinEv _ (treeA_servedCell_mem_sizeWindowNouns row4 row3 row0 subj b hstate4 hstate3
      hstate0 x y hcell) hΛ
  have hr3 : C2ChipReady (sv := sv) (ax := ax) z q (.node row3 [.node row0 []]) subj
      (.cell (.atom 3) (.cell (.atom 0) b)) :=
    C2ChipReady.op3 hstate3 hzRow3 hpubSt3 hh3 ht3 hV3 hwin helink3 hslink3 hr0
  have hke : (J (NTree.node row3 [.node row0 []]).size (.node row3 [.node row0 []]) subj
      (.cell (.atom 3) (.cell (.atom 0) b))).label.evaluation = .atom 0 := by
    have hsz : (NTree.node row3 [NTree.node row0 ([] : List (NTree ((State × DTcomp K) × ℕ)))]).size
        = 2 := by simp [NTree.size]
    rw [hsz]
    exact J2_op3_eval row3 row0 subj b hstate3 hstate0 x y hcell
  exact C2ChipReady.op4 (k := 0) hstate4 hzRow4 hpubSt4 hh4 ht4 hV4 hke helink4 hslink4 hr3

theorem treeA_binds (z : K) (hz : z ≠ 0) (q Λ : ℕ) (x y : Noun)
    (hcell : sv .verify_child (row0.2 + 2) = .cell x y)
    (hwinEv : ∀ n ∈ SizeWindowCounting.skeletonSizeWindowNouns (skelA (sv := sv) (ax := ax) row4 row3 row0 subj b),
      n.leaves ≤ Λ → OpcodeSemantics.SizeWindow z n)
    (hΛ : (Noun.cell x y).leaves ≤ Λ)
    (hstate0 : row0.1.1 = .s0) (hzRow0 : row0.1.2.1.z = z) (hpubSt0 : row0.1.2.2.1.state = .s0)
    (hh0 : bindFP z (.atom 0) row0.1.2.2.2.f_h)
    (ht0 : bindFP z b row0.1.2.2.2.f_t)
    (he0 : bindFP z (sv .verify_child (row0.2 + 2)) row0.1.2.2.1.e)
    (hax0 : ((ax (row0.2 + 2) : ℕ) : K) = row0.1.2.2.2.f_t.leaf)
    (hV0 : Vcomp row0.1.2.1 row0.1.2.2.1 row0.1.2.2.2)
    (hstate3 : row3.1.1 = .s3) (hzRow3 : row3.1.2.1.z = z) (hpubSt3 : row3.1.2.2.1.state = .s3)
    (hh3 : bindFP z (.atom 3) row3.1.2.2.2.f_h)
    (ht3 : bindFP z (.cell (.atom 0) b) row3.1.2.2.2.f_t)
    (hV3 : Vcomp row3.1.2.1 row3.1.2.2.1 row3.1.2.2.2)
    (helink3 : row0.1.2.2.1.e = row3.1.2.2.1.sf1_e)
    (hslink3 : row0.1.2.2.1.s = row3.1.2.2.1.sf1_s)
    (hstate4 : row4.1.1 = .s4) (hzRow4 : row4.1.2.1.z = z) (hpubSt4 : row4.1.2.2.1.state = .s4)
    (hh4 : bindFP z (.atom 4) row4.1.2.2.2.f_h)
    (ht4 : bindFP z (.cell (.atom 3) (.cell (.atom 0) b)) row4.1.2.2.2.f_t)
    (hV4 : Vcomp row4.1.2.1 row4.1.2.2.1 row4.1.2.2.2)
    (helink4 : row3.1.2.2.1.e = row4.1.2.2.1.sf1_e)
    (hslink4 : row3.1.2.2.1.s = row4.1.2.2.1.sf1_s)
    (hsRoot : bindFP z subj row4.1.2.2.1.s) :
    C2JoinReadyF (sv := sv) (ax := ax) z q (treeA row4 row3 row0) subj (formulaA b) ∧
      ComputeTreeBinds z (J 3 (treeA row4 row3 row0) subj (formulaA b))
        (mapNTree Prod.fst (treeA row4 row3 row0)) := by
  have hC := treeA_chipReady row4 row3 row0 subj b z q Λ x y hcell hwinEv hΛ
    hstate0 hzRow0 hpubSt0 hh0 ht0 he0 hax0 hV0
    hstate3 hzRow3 hpubSt3 hh3 ht3 hV3 helink3 hslink3
    hstate4 hzRow4 hpubSt4 hh4 ht4 hV4 helink4 hslink4
  have hR := c2JoinReadyF_of_chipReady hz hC hsRoot
  refine ⟨hR, ?_⟩
  have hsz : (treeA row4 row3 row0).size ≤ 3 := by simp [treeA, NTree.size]
  exact computeTreeBinds_of_readyF hz hsz hR

end TreeA

/-! ## §E  Tree B — one OP2 node `[2 [1 x] [1 [1 w]]]`: the third child's subject is derived -/

section TreeB

variable (row2 rowA rowB rowC : (State × DTcomp K) × ℕ) (subj x w : Noun)

abbrev treeB : NTree ((State × DTcomp K) × ℕ) :=
  .node row2 [.node rowA [], .node rowB [], .node rowC []]

abbrev formulaB : Noun :=
  .cell (.atom 2) (.cell (.cell (.atom 1) x) (.cell (.atom 1) (.cell (.atom 1) w)))

theorem J1_op1_eval (row : (State × DTcomp K) × ℕ) (h1 : row.1.1 = .s1) (s tail : Noun) :
    (J 1 (.node row []) s (.cell (.atom 1) tail)).label.evaluation = tail := by
  simp [c2JoinFuel, c2SkeletonRow, c2Evaluation, h1, nounTail]

/-- **Tree B is chip-ready and binds.**  The third child's subject `x` (child 0's evaluation) and
formula `[1 w]` (child 1's evaluation) are NOT bound by hypothesis: `rowC.s` is tied only through
the links `rowC.s = sf3_s`, `rowA.e = sf1_e` and `V_comp`'s `sf3_s = sf1_e`; its binding is a
conclusion of child 0's `ComputeTreeBinds` inside `c2JoinReadyF_of_chipReady`. -/
theorem treeB_binds (z : K) (hz : z ≠ 0) (q : ℕ)
    -- row 2 (OP2)
    (hstate2 : row2.1.1 = .s2) (hzRow2 : row2.1.2.1.z = z) (hpubSt2 : row2.1.2.2.1.state = .s2)
    (hh2 : bindFP z (.atom 2) row2.1.2.2.2.f_h)
    (hth2 : bindFP z (.cell (.atom 1) x) row2.1.2.2.2.f_th)
    (htt2 : bindFP z (.cell (.atom 1) (.cell (.atom 1) w)) row2.1.2.2.2.f_tt)
    (hV2 : Vcomp row2.1.2.1 row2.1.2.2.1 row2.1.2.2.2)
    (he1link : rowA.1.2.2.1.e = row2.1.2.2.1.sf1_e)
    (he2link : rowB.1.2.2.1.e = row2.1.2.2.1.sf2_e)
    (heApplink : rowC.1.2.2.1.e = row2.1.2.2.1.sf3_e)
    (hs1link : rowA.1.2.2.1.s = row2.1.2.2.1.sf1_s)
    (hs2link : rowB.1.2.2.1.s = row2.1.2.2.1.sf2_s)
    (hs3link : rowC.1.2.2.1.s = row2.1.2.2.1.sf3_s)
    -- row A (OP1, `[1 x]`)
    (hstateA : rowA.1.1 = .s1) (hzRowA : rowA.1.2.1.z = z) (hpubStA : rowA.1.2.2.1.state = .s1)
    (hhA : bindFP z (.atom 1) rowA.1.2.2.2.f_h) (htA : bindFP z x rowA.1.2.2.2.f_t)
    (hVA : Vcomp rowA.1.2.1 rowA.1.2.2.1 rowA.1.2.2.2)
    -- row B (OP1, `[1 [1 w]]`)
    (hstateB : rowB.1.1 = .s1) (hzRowB : rowB.1.2.1.z = z) (hpubStB : rowB.1.2.2.1.state = .s1)
    (hhB : bindFP z (.atom 1) rowB.1.2.2.2.f_h)
    (htB : bindFP z (.cell (.atom 1) w) rowB.1.2.2.2.f_t)
    (hVB : Vcomp rowB.1.2.1 rowB.1.2.2.1 rowB.1.2.2.2)
    -- row C (OP1, `[1 w]` at subject `x`): NO subject binding assumed
    (hstateC : rowC.1.1 = .s1) (hzRowC : rowC.1.2.1.z = z) (hpubStC : rowC.1.2.2.1.state = .s1)
    (hhC : bindFP z (.atom 1) rowC.1.2.2.2.f_h) (htC : bindFP z w rowC.1.2.2.2.f_t)
    (hVC : Vcomp rowC.1.2.1 rowC.1.2.2.1 rowC.1.2.2.2)
    -- the root subject
    (hsRoot : bindFP z subj row2.1.2.2.1.s) :
    C2JoinReadyF (sv := sv) (ax := ax) z q (treeB row2 rowA rowB rowC) subj (formulaB x w) ∧
      bindFP z x rowC.1.2.2.1.s ∧
      ComputeTreeBinds z (J 4 (treeB row2 rowA rowB rowC) subj (formulaB x w))
        (mapNTree Prod.fst (treeB row2 rowA rowB rowC)) := by
  have hrA : C2ChipReady (sv := sv) (ax := ax) z q (.node rowA []) subj (.cell (.atom 1) x) :=
    C2ChipReady.op1 hstateA hzRowA hpubStA hhA htA hVA
  have hrB : C2ChipReady (sv := sv) (ax := ax) z q (.node rowB []) subj
      (.cell (.atom 1) (.cell (.atom 1) w)) :=
    C2ChipReady.op1 hstateB hzRowB hpubStB hhB htB hVB
  have hevA : (J (NTree.node rowA []).size (.node rowA []) subj (.cell (.atom 1) x)).label.evaluation
      = x := by
    have hsz : (NTree.node rowA ([] : List (NTree ((State × DTcomp K) × ℕ)))).size = 1 := by
      simp [NTree.size]
    rw [hsz]; exact J1_op1_eval rowA hstateA subj x
  have hevB : (J (NTree.node rowB []).size (.node rowB []) subj
      (.cell (.atom 1) (.cell (.atom 1) w))).label.evaluation = .cell (.atom 1) w := by
    have hsz : (NTree.node rowB ([] : List (NTree ((State × DTcomp K) × ℕ)))).size = 1 := by
      simp [NTree.size]
    rw [hsz]; exact J1_op1_eval rowB hstateB subj _
  have hrC : C2ChipReady (sv := sv) (ax := ax) z q (.node rowC [])
      (J (NTree.node rowA []).size (.node rowA []) subj (.cell (.atom 1) x)).label.evaluation
      (J (NTree.node rowB []).size (.node rowB []) subj
        (.cell (.atom 1) (.cell (.atom 1) w))).label.evaluation := by
    rw [hevA, hevB]
    exact C2ChipReady.op1 hstateC hzRowC hpubStC hhC htC hVC
  have hC : C2ChipReady (sv := sv) (ax := ax) z q (treeB row2 rowA rowB rowC) subj (formulaB x w) :=
    C2ChipReady.op2 hstate2 hzRow2 hpubSt2 hh2 hth2 htt2 hV2 he1link he2link heApplink
      hs1link hs2link hs3link hrA hrB hrC
  have hR := c2JoinReadyF_of_chipReady hz hC hsRoot
  refine ⟨hR, ?_, ?_⟩
  · -- the derived subject binding of the third child, read off the ready tree
    cases hR with
    | op2 _ _ _ _ _ _ _ _ _ _ _ _ _ h3 =>
        have := h3
        rw [hevA, hevB] at this
        cases this with
        | op1 _ _ _ hs _ _ _ => exact hs
  · have hsz : (treeB row2 rowA rowB rowC).size ≤ 4 := by simp [treeB, NTree.size]
    exact computeTreeBinds_of_readyF hz hsz hR

end TreeB


section AtFamily

open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.RedTeam.Batch1024

variable {F K' : Type} [Field F] [Field K'] [Algebra F K']
  [Fintype F] [DecidableEq F]
  [Fintype K'] [DecidableEq K'] [CharP K' (ringChar K')] [FiniteDimensional F K']
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K' hOrb)
  (c : OptimizedProductionChallengeTuple K' F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)

end AtFamily

end Nock.RedTeam.Batch1090

#print axioms Nock.RedTeam.Batch1090.computeTreeBinds_of_readyF
#print axioms Nock.RedTeam.Batch1090.c2JoinReadyF_of_chipReady
#print axioms Nock.RedTeam.Batch1090.treeA_servedCell_mem_sizeWindowNouns
#print axioms Nock.RedTeam.Batch1090.treeA_binds
#print axioms Nock.RedTeam.Batch1090.treeB_binds
#print axioms Nock.RedTeam.Batch1090.hcomp_C2_of_chipReady
#print axioms Nock.RedTeam.Batch1090.bindsAtCoin_C2_of_chipReady
