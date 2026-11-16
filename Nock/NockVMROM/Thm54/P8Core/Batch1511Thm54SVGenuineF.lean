/-
  Nock/NockVMROM/Thm54/P8Core/Batch1511Thm54SVGenuineF.lean

  **Genuineness under the field semantics, and
  the field call tree.**

  * **§A `RowOutputF q` / `GenuineSkelF q`.**  `ComputedWindow.RowOutput` / `GenuineSkel` with the
    OP4 arm at the field increment: `lusFBy q k0.evaluation = some e` (equivalently: the operand is
    an atom and `e = incMod q k0.evaluation`, `rowOutputF_s4_iff`).  `FormulaShape` and `KidInputs`
    are semantics-free and are reused verbatim.
  * **§B `genuineF_evalFBy`.**  A field-genuine tree is a successful `evalFBy q` run of its root at
    fuel `T.size`: `evalFBy q T.size T.label.subject T.label.formula = some T.label.evaluation`.  So
    a field-genuine tree whose root carries the claim's `(s, f, r)` proves
    `HoldsF q x := ∃ fuel, evalFBy q fuel x.subject x.formula = some x.result` (`holdsF_of_genuineF`).
    No window, no fuel hypothesis, no honest run.
  * **§C `CallTreeF q S0 F0 d s f`** — the field call tree of the claim `(S0, F0)`: `(s, f)` is a
    call at depth `d` of `evalFBy q` started at `(S0, F0)`, over the chip's ISA (OP0–OP9 and cons;
    `evalFBy`'s OP10/OP11 have no chip state).  It is a function of the claim alone (no trace, no
    coin, no honest run) and finitely branching (at most three kids per call), so each depth
    prefix `{(s, f) | ∃ d ≤ N, CallTreeF … d s f}` is finite.  Its OP6 arm follows the join's
    branch selector `condBit` (so it over-approximates `evalFBy`'s calls by the off-`{0, 1}`
    continuation, still a function of the claim).
  * **§D `callTreeF_kid`** — `ComputedWindow.honestCall_kid` at `CallTreeF`: at a row whose inputs
    are a call at depth `d` (formula of its state's shape, children fed the join's inputs), the
    `i`-th child in evaluation order is a call at depth `d + 1` as soon as the children before it
    in evaluation order are field-genuine.  **No honest tree `G`, no generator run.**  `callTreeF_rows` is the bottom-up corollary:
    every row of a field-genuine tree rooted at a call is a call.

  **Window abstraction (binding, SV-STAGE1-LANES-BRIEF).**  Nothing here mentions a window, a
  leaf count, `programLeafBound` or `leafBoundF`.  The window enters downstream only as an
  abstract premise over the calls of `CallTreeF`, e.g. `∀ d ≤ N, CallTreeF q S0 F0 d s f →
  s.leaves ≤ W ∧ f.leaves ≤ W` (and on the results of calls); its instantiation is the
  tight-window lane's.

  Paper: the paper (Nock's rules), `:1531-1534` (field increment), `:1443-1448`
  (the language), `:348`, `:1093` (nouns over 𝔽).
-/
import Nock.NockVMROM.Thm54.P8Core.ComputedWindow
import Nock.NockVMROM.Thm54.GlobalOpcodeScheduling

namespace Nock.NockVMROM.Thm54.SVGenuineF

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.FieldEmbedding
open Nock.NockVMROM.Thm54.TraceGen

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## §A  Field genuineness -/

/-- **The row's evaluation as its opcode's FIELD output**. -/
def RowOutputF (q : ℕ) : State → Noun → Noun → List ComputeRowSkeleton → Noun → Prop
  | .s0, s, f, _, e => Noun.slot (op0Axis f) s = some e
  | .s1, _, f, _, e => e = tl f
  | .cons, _, _, [k0, k1], e => e = .cell k0.evaluation k1.evaluation
  | .s3, _, _, [k0], e => e = Noun.wut k0.evaluation
  | .s4, _, _, [k0], e => lusFBy q k0.evaluation = some e
  | .s5, _, _, [k0, k1], e => e = Noun.tis k0.evaluation k1.evaluation
  | .s2, _, _, [_, _, k2], e => e = k2.evaluation
  | .s6, _, _, [kT, kC], e =>
      (kC.evaluation = .atom 0 ∨ kC.evaluation = .atom 1) ∧ e = kT.evaluation
  | .s7, _, _, [kM, _], e => e = kM.evaluation
  | .s8, _, _, [kM, _], e => e = kM.evaluation
  | .s9, _, _, [_, kI], e => e = kI.evaluation
  | _, _, _, _, _ => False

/-- OP4's field output is `incMod q` of an atom operand. -/
theorem rowOutputF_s4_iff (q : ℕ) (s f : Noun) (k0 : ComputeRowSkeleton) (e : Noun) :
    RowOutputF q .s4 s f [k0] e ↔
      (∃ n, k0.evaluation = .atom n) ∧ e = OpcodeSemantics.incMod q k0.evaluation := by
  simp only [RowOutputF]
  cases h : k0.evaluation with
  | atom n =>
      simp [lusFBy, OpcodeSemantics.incMod, eq_comm]
  | cell a b => simp [lusFBy]

/-- **A field-genuine built tree**: every row obeys its Nock step under the field semantics. -/
inductive GenuineSkelF (q : ℕ) : NTree ComputeRowSkeleton → Prop
  | node {s : ComputeRowSkeleton} {kids : List (NTree ComputeRowSkeleton)}
      (shape : FormulaShape s.state s.formula)
      (inputs : KidInputs s.state s.subject s.formula (kids.map NTree.label))
      (output : RowOutputF q s.state s.subject s.formula (kids.map NTree.label) s.evaluation)
      (children : ∀ k ∈ kids, GenuineSkelF q k) :
      GenuineSkelF q (.node s kids)

theorem rowOutputF_unique {q : ℕ} {st : State} {s f : Noun} {ks : List ComputeRowSkeleton}
    {e₁ e₂ : Noun} (h₁ : RowOutputF q st s f ks e₁) (h₂ : RowOutputF q st s f ks e₂) : e₁ = e₂ := by
  cases st <;> rcases ks with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    simp only [RowOutputF] at h₁ h₂ <;>
    first
    | exact False.elim h₁
    | (rw [h₁] at h₂; exact Option.some.inj h₂)
    | (rw [h₁.2, h₂.2])
    | (rw [h₁, h₂])

theorem genuineF_root {q : ℕ} {T : NTree ComputeRowSkeleton} (hT : GenuineSkelF q T) :
    FormulaShape T.label.state T.label.formula ∧
      KidInputs T.label.state T.label.subject T.label.formula (T.children.map NTree.label) ∧
      RowOutputF q T.label.state T.label.subject T.label.formula (T.children.map NTree.label)
        T.label.evaluation := by
  cases hT with
  | node shape inputs output _ => exact ⟨shape, inputs, output⟩

theorem genuineF_child {q : ℕ} {T k : NTree ComputeRowSkeleton} (hT : GenuineSkelF q T)
    (hk : k ∈ T.children) : GenuineSkelF q k := by
  cases hT with
  | node _ _ _ children => exact children k hk

theorem genuineF_sub {q : ℕ} {T u : NTree ComputeRowSkeleton} (hT : GenuineSkelF q T)
    (hu : InTree T u) : GenuineSkelF q u := by
  induction hu with
  | here => exact hT
  | sub hs _ ih => exact ih (genuineF_child hT hs)

/-! ## §B  A field-genuine tree is a successful `evalFBy` run -/

theorem size_pos {α : Type*} (t : NTree α) : 1 ≤ t.size := by
  cases t
  simp [NTree.size]

theorem size_child_lt {α : Type*} {row : α} {kids : List (NTree α)} {k : NTree α}
    (hk : k ∈ kids) : k.size < (NTree.node row kids).size := by
  have hsz : (NTree.node row kids).size = 1 + (kids.map NTree.size).sum := by
    simp [NTree.size]
  have hmem : k.size ∈ kids.map NTree.size := List.mem_map.mpr ⟨k, hk, rfl⟩
  have : k.size ≤ (kids.map NTree.size).sum := List.le_sum_of_mem hmem
  omega

/-- **Field genuineness is a successful field run.**  At fuel `T.size`, `evalFBy q` of the root's
inputs returns the root evaluation. -/
theorem genuineF_evalFBy {q : ℕ} {T : NTree ComputeRowSkeleton} (hT : GenuineSkelF q T) :
    evalFBy q T.size T.label.subject T.label.formula = some T.label.evaluation := by
  induction hT with
  | @node s kids shape inputs output children ih =>
    -- the kids' runs, at the parent's fuel minus one
    obtain ⟨m, hm, hkm⟩ : ∃ m, (NTree.node s kids).size = m + 1 ∧ ∀ k ∈ kids, k.size ≤ m := by
      refine ⟨(NTree.node s kids).size - 1, ?_, fun k hk => ?_⟩
      · have := size_pos (NTree.node s kids); omega
      · have := size_child_lt (row := s) hk; omega
    have run : ∀ k ∈ kids, evalFBy q m k.label.subject k.label.formula = some k.label.evaluation :=
      fun k hk => GlobalOpcodeScheduling.evalFBy_mono (hkm k hk) (ih k hk)
    rw [hm]
    simp only [NTree.label]
    cases hst : s.state with
    | s0 =>
      rw [hst] at shape inputs output
      obtain ⟨ax, hf⟩ := shape
      simp only [RowOutputF, hf, op0Axis] at output
      rw [hf]; simpa [evalFBy] using output
    | s1 =>
      rw [hst] at shape inputs output
      obtain ⟨t, hf⟩ := shape
      simp only [RowOutputF, hf, tl, StrategyOfTraces.nounTail] at output
      rw [hf, output]; simp [evalFBy]
    | cons =>
      rw [hst] at shape inputs output
      obtain ⟨b, c, d, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputs] at inputs
      obtain ⟨hs0, hf0, hs1, hf1⟩ := inputs
      simp only [RowOutputF, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp)
      have r1 := run k1 (by simp)
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      rw [hf, output]; simp [evalFBy, r0, r1]
    | s3 =>
      rw [hst] at shape inputs output
      obtain ⟨t, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputs] at inputs
      obtain ⟨hs0, hf0⟩ := inputs
      simp only [RowOutputF, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp)
      rw [hs0, hf0, hf] at r0
      simp only [tl, StrategyOfTraces.nounTail] at r0
      rw [hf, output]; simp [evalFBy, r0]
    | s4 =>
      rw [hst] at shape inputs output
      obtain ⟨t, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp only [List.map, KidInputs] at inputs
      obtain ⟨hs0, hf0⟩ := inputs
      simp only [RowOutputF, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp)
      rw [hs0, hf0, hf] at r0
      simp only [tl, StrategyOfTraces.nounTail] at r0
      rw [hf]; simp [evalFBy, r0, output]
    | s5 =>
      rw [hst] at shape inputs output
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputs] at inputs
      obtain ⟨hs0, hf0, hs1, hf1⟩ := inputs
      simp only [RowOutputF, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp)
      have r1 := run k1 (by simp)
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      rw [hf, output]; simp [evalFBy, r0, r1]
    | s2 =>
      rw [hst] at shape inputs output
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
        simp only [List.map, KidInputs] at inputs
      obtain ⟨hs0, hf0, hs1, hf1, hs2, hf2⟩ := inputs
      simp only [RowOutputF, List.map_cons, List.map_nil] at output
      have r0 := run k0 (by simp)
      have r1 := run k1 (by simp)
      have r2 := run k2 (by simp)
      rw [hs0, hf0, hf] at r0
      rw [hs1, hf1, hf] at r1
      rw [hs2, hf2] at r2
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at r0 r1
      rw [hf, output]; simp [evalFBy, r0, r1, r2]
    | s6 =>
      rw [hst] at shape inputs output
      obtain ⟨b, c, d, hf⟩ := shape
      rcases kids with _ | ⟨kT, _ | ⟨kC, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputs] at inputs
      obtain ⟨hsC, hfC, hsT, hfT⟩ := inputs
      simp only [RowOutputF, List.map_cons, List.map_nil] at output
      obtain ⟨hb, he⟩ := output
      have rC := run kC (by simp)
      have rT := run kT (by simp)
      rw [hsC, hfC, hf] at rC
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rC
      rw [hsT, hfT, hf] at rT
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rT
      rw [hf, he]
      rcases hb with hb | hb
      · rw [hb] at rC rT; simp [condBit] at rT; simp [evalFBy, rC, rT]
      · rw [hb] at rC rT; simp [condBit] at rT; simp [evalFBy, rC, rT]
    | s7 =>
      rw [hst] at shape inputs output
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputs] at inputs
      obtain ⟨hsH, hfH, hsM, hfM⟩ := inputs
      simp only [RowOutputF, List.map_cons, List.map_nil] at output
      have rH := run kH (by simp)
      have rM := run kM (by simp)
      rw [hsH, hfH, hf] at rH
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rH
      rw [hsM, hfM, hf] at rM
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rM
      rw [hf, output]; simp [evalFBy, rH, rM]
    | s8 =>
      rw [hst] at shape inputs output
      obtain ⟨b, c, hf⟩ := shape
      rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputs] at inputs
      obtain ⟨hsH, hfH, hsM, hfM⟩ := inputs
      simp only [RowOutputF, List.map_cons, List.map_nil] at output
      have rH := run kH (by simp)
      have rM := run kM (by simp)
      rw [hsH, hfH, hf] at rH
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rH
      rw [hsM, hfM, hf] at rM
      simp only [hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail] at rM
      rw [hf, output]; simp [evalFBy, rH, rM]
    | s9 =>
      rw [hst] at shape inputs output
      obtain ⟨ax, c, hf⟩ := shape
      rcases kids with _ | ⟨kC, _ | ⟨kI, _ | ⟨k2, rest⟩⟩⟩ <;>
        simp only [List.map, KidInputs] at inputs
      obtain ⟨hsC, hfC, hsI, hslot⟩ := inputs
      simp only [RowOutputF, List.map_cons, List.map_nil] at output
      have rC := run kC (by simp)
      have rI := run kI (by simp)
      rw [hsC, hfC, hf] at rC
      simp only [tl, StrategyOfTraces.nounTail] at rC
      rw [hsI] at rI
      rw [hf] at hslot
      simp only [op9Axis] at hslot
      rw [hf, output]; simp [evalFBy, rC, hslot, rI]

/-- The field language. -/
def HoldsF (q : ℕ) (x : P8PublicClaim) : Prop :=
  ∃ fuel, evalFBy q fuel x.subject x.formula = some x.result

/-- **A field-genuine tree rooted at the claim proves the claim under `HoldsF`.** -/
theorem holdsF_of_genuineF {q : ℕ} {T : NTree ComputeRowSkeleton} (hT : GenuineSkelF q T)
    {x : P8PublicClaim} (hs : T.label.subject = x.subject) (hf : T.label.formula = x.formula)
    (he : T.label.evaluation = x.result) : HoldsF q x :=
  ⟨T.size, by rw [← hs, ← hf, ← he]; exact genuineF_evalFBy hT⟩

/-! ## §C  The field call tree of the claim -/

/-- **The field call tree of `(S0, F0)`**: `CallTreeF q S0 F0 d s f` says `(s, f)` is a call at
depth `d` of the field evaluation started at `(S0, F0)`, over the chip ISA (OP0–OP9, cons).  Each
arm passes down exactly the children's inputs `KidInputs` names, with the dependent inputs read off
successful `evalFBy q` runs of the earlier children (OP2's applied pair, OP6's branch at the join's
selector `condBit`, OP7/OP8's mutated subject, OP9's core and arm).  A function of the claim only. -/
inductive CallTreeF (q : ℕ) (S0 F0 : Noun) : ℕ → Noun → Noun → Prop
  | root : CallTreeF q S0 F0 0 S0 F0
  | consL {d : ℕ} {s b c e : Noun} :
      CallTreeF q S0 F0 d s (.cell (.cell b c) e) → CallTreeF q S0 F0 (d + 1) s (.cell b c)
  | consR {d : ℕ} {s b c e : Noun} :
      CallTreeF q S0 F0 d s (.cell (.cell b c) e) → CallTreeF q S0 F0 (d + 1) s e
  | op2L {d : ℕ} {s b c : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 2) (.cell b c)) → CallTreeF q S0 F0 (d + 1) s b
  | op2R {d : ℕ} {s b c : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 2) (.cell b c)) → CallTreeF q S0 F0 (d + 1) s c
  | op2App {d n m : ℕ} {s b c sb sc : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 2) (.cell b c)) →
        evalFBy q n s b = some sb → evalFBy q m s c = some sc → CallTreeF q S0 F0 (d + 1) sb sc
  | op3 {d : ℕ} {s t : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 3) t) → CallTreeF q S0 F0 (d + 1) s t
  | op4 {d : ℕ} {s t : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 4) t) → CallTreeF q S0 F0 (d + 1) s t
  | op5L {d : ℕ} {s b c : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 5) (.cell b c)) → CallTreeF q S0 F0 (d + 1) s b
  | op5R {d : ℕ} {s b c : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 5) (.cell b c)) → CallTreeF q S0 F0 (d + 1) s c
  | op6C {d : ℕ} {s b c e : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 6) (.cell b (.cell c e))) →
        CallTreeF q S0 F0 (d + 1) s b
  | op6T {d n : ℕ} {s b c e r : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 6) (.cell b (.cell c e))) →
        evalFBy q n s b = some r →
        CallTreeF q S0 F0 (d + 1) s (if condBit r = 0 then c else e)
  | op7H {d : ℕ} {s b c : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 7) (.cell b c)) → CallTreeF q S0 F0 (d + 1) s b
  | op7M {d n : ℕ} {s b c sb : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 7) (.cell b c)) →
        evalFBy q n s b = some sb → CallTreeF q S0 F0 (d + 1) sb c
  | op8H {d : ℕ} {s b c : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 8) (.cell b c)) → CallTreeF q S0 F0 (d + 1) s b
  | op8M {d n : ℕ} {s b c sb : Noun} :
      CallTreeF q S0 F0 d s (.cell (.atom 8) (.cell b c)) →
        evalFBy q n s b = some sb → CallTreeF q S0 F0 (d + 1) (.cell sb s) c
  | op9C {d : ℕ} {s c : Noun} {ax : ℕ} :
      CallTreeF q S0 F0 d s (.cell (.atom 9) (.cell (.atom ax) c)) → CallTreeF q S0 F0 (d + 1) s c
  | op9I {d n : ℕ} {s c core arm : Noun} {ax : ℕ} :
      CallTreeF q S0 F0 d s (.cell (.atom 9) (.cell (.atom ax) c)) →
        evalFBy q n s c = some core → Noun.slot ax core = some arm →
        CallTreeF q S0 F0 (d + 1) core arm

/-! ## §D  Calls propagate down the evaluation order -/

/-- A field-genuine kid's evaluation is its inputs' field run (`genuineF_evalFBy`, packaged). -/
theorem kid_run {q : ℕ} {k : NTree ComputeRowSkeleton} (hk : GenuineSkelF q k) :
    evalFBy q k.size k.label.subject k.label.formula = some k.label.evaluation :=
  genuineF_evalFBy hk

/-- **`callTreeF_kid` — calls propagate down the evaluation order** (`honestCall_kid` at the field
call tree, without the honest tree `G`).  At a row whose inputs `(subj, f)` are a call at depth `d`,
whose formula has its state's shape and whose children receive the join's inputs, the `i`-th child
in evaluation order is a call at depth `d + 1` as soon as the children before it in evaluation
order are field-genuine. -/
theorem callTreeF_kid {q : ℕ} {S0 F0 : Noun} {d : ℕ} {st : State} {subj f : Noun}
    {kids : List (NTree ComputeRowSkeleton)}
    (hcall : CallTreeF q S0 F0 d subj f) (hshape : FormulaShape st f)
    (hin : KidInputs st subj f (kids.map NTree.label)) :
    ∀ (i : ℕ) (k : NTree ComputeRowSkeleton), (evalOrder st kids)[i]? = some k →
      (∀ (j : ℕ) (k' : NTree ComputeRowSkeleton), j < i →
        (evalOrder st kids)[j]? = some k' → GenuineSkelF q k') →
      CallTreeF q S0 F0 (d + 1) k.label.subject k.label.formula := by
  intro i k hk hprev
  cases st with
  | s0 =>
    have hkids : kids = [] := by simpa [KidInputs] using hin
    subst hkids; simp [evalOrder, airNeedsSwap] at hk
  | s1 =>
    have hkids : kids = [] := by simpa [KidInputs] using hin
    subst hkids; simp [evalOrder, airNeedsSwap] at hk
  | cons =>
    obtain ⟨b, c, e, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hs0, hf0, hs1, hf1⟩ := hin
    rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap] at hk <;> subst hk
    · rw [hs0, hf0]; exact .consL hcall
    · rw [hs1, hf1]; exact .consR hcall
  | s3 =>
    obtain ⟨t, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp [KidInputs, tl_cell] at hin
    obtain ⟨hs0, hf0⟩ := hin
    rcases i with _ | i <;> simp [evalOrder, airNeedsSwap] at hk <;> subst hk
    rw [hs0, hf0]; exact .op3 hcall
  | s4 =>
    obtain ⟨t, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp [KidInputs, tl_cell] at hin
    obtain ⟨hs0, hf0⟩ := hin
    rcases i with _ | i <;> simp [evalOrder, airNeedsSwap] at hk <;> subst hk
    rw [hs0, hf0]; exact .op4 hcall
  | s5 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hs0, hf0, hs1, hf1⟩ := hin
    rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap] at hk <;> subst hk
    · rw [hs0, hf0]; exact .op5L hcall
    · rw [hs1, hf1]; exact .op5R hcall
  | s2 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hs0, hf0, hs1, hf1, hs2, hf2⟩ := hin
    rcases i with _ | _ | _ | i <;> simp [evalOrder, airNeedsSwap] at hk <;> subst hk
    · rw [hs0, hf0]; exact .op2L hcall
    · rw [hs1, hf1]; exact .op2R hcall
    · have g0 := hprev 0 k0 (by omega) (by simp [evalOrder, airNeedsSwap])
      have g1 := hprev 1 k1 (by omega) (by simp [evalOrder, airNeedsSwap])
      have r0 := kid_run g0
      have r1 := kid_run g1
      rw [hs0, hf0] at r0
      rw [hs1, hf1] at r1
      rw [hs2, hf2]
      exact .op2App hcall r0 r1
  | s6 =>
    obtain ⟨b, c, e, rfl⟩ := hshape
    rcases kids with _ | ⟨kT, _ | ⟨kC, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hsC, hfC, hsT, hfT⟩ := hin
    rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap, swapPair] at hk <;> subst hk
    · rw [hsC, hfC]; exact .op6C hcall
    · have gC := hprev 0 kC (by omega) (by simp [evalOrder, airNeedsSwap, swapPair])
      have rC := kid_run gC
      rw [hsC, hfC] at rC
      rw [hsT, hfT]
      exact .op6T hcall rC
  | s7 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hsH, hfH, hsM, hfM⟩ := hin
    rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap, swapPair] at hk <;> subst hk
    · rw [hsH, hfH]; exact .op7H hcall
    · have gH := hprev 0 kH (by omega) (by simp [evalOrder, airNeedsSwap, swapPair])
      have rH := kid_run gH
      rw [hsH, hfH] at rH
      rw [hsM, hfM]
      exact .op7M hcall rH
  | s8 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hsH, hfH, hsM, hfM⟩ := hin
    rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap, swapPair] at hk <;> subst hk
    · rw [hsH, hfH]; exact .op8H hcall
    · have gH := hprev 0 kH (by omega) (by simp [evalOrder, airNeedsSwap, swapPair])
      have rH := kid_run gH
      rw [hsH, hfH] at rH
      rw [hsM, hfM]
      exact .op8M hcall rH
  | s9 =>
    obtain ⟨ax, c, rfl⟩ := hshape
    rcases kids with _ | ⟨kC, _ | ⟨kI, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, tl_cell, op9Axis] at hin
    obtain ⟨hsC, hfC, hsI, hslot⟩ := hin
    rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap] at hk <;> subst hk
    · rw [hsC, hfC]; exact .op9C hcall
    · have gC := hprev 0 kC (by omega) (by simp [evalOrder, airNeedsSwap])
      have rC := kid_run gC
      rw [hsC, hfC] at rC
      rw [hsI]
      exact .op9I hcall rC hslot

/-- Every child of a field-genuine row lies in the parent's evaluation order. -/
theorem mem_evalOrder_iff {α : Type*} (st : State) (l : List α) (x : α) :
    x ∈ evalOrder st l ↔ x ∈ l := by
  unfold evalOrder
  split
  · unfold swapPair
    split <;> simp_all [or_comm]
  · rfl

/-- **Bottom-up form**: every row of a field-genuine tree whose root inputs are a call at depth `d`
is a call, at depth `d + (its depth in the tree)` — here stated as `∃ d' ≥ d`, with the depth
bounded by the tree size: `d' < d + T.size`. -/
theorem callTreeF_rows {q : ℕ} {S0 F0 : Noun} {T : NTree ComputeRowSkeleton}
    (hT : GenuineSkelF q T) :
    ∀ {d : ℕ}, CallTreeF q S0 F0 d T.label.subject T.label.formula →
      ∀ u, InTree T u → ∃ d', d ≤ d' ∧ d' < d + T.size ∧
        CallTreeF q S0 F0 d' u.label.subject u.label.formula := by
  induction hT with
  | @node s kids shape inputs output children ih =>
    intro d hcall u hu
    have hpos := size_pos (NTree.node s kids)
    cases hu with
    | here => exact ⟨d, le_rfl, by omega, hcall⟩
    | sub hk hku =>
      simp only [NTree.children] at hk
      -- the child is in evaluation order at some index; all children are genuine
      have hkmem : _ ∈ evalOrder s.state kids := (mem_evalOrder_iff _ _ _).2 hk
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hkmem
      have hkcall := callTreeF_kid (q := q) (st := s.state) (kids := kids) hcall shape inputs i _
        hi (fun j k' _ hj' =>
          children k' ((mem_evalOrder_iff _ _ _).1 (List.mem_of_getElem? hj')))
      obtain ⟨d', h1, h2, h3⟩ := ih _ hk hkcall u hku
      have hlt := size_child_lt (row := s) hk
      exact ⟨d', by omega, by omega, h3⟩

end Nock.NockVMROM.Thm54.SVGenuineF
