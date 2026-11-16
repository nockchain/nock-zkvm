/-
  Nock/NockVMROM/Thm54/P8Core/ComputedWindow.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.ComputedWindow`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/ComputedWindow.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.BuildTFWindow
import Nock.NockVMROM.Thm54.P8Core.StrategyOfTraces
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenAirOrderLinked
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenTraceConfined

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.ComputedWindow

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TraceGen

/-- The join's formula head (`StrategyOfTraces.nounHead`). -/
abbrev hd : Noun → Noun := StrategyOfTraces.nounHead

/-- The join's formula tail (`StrategyOfTraces.nounTail`). -/
abbrev tl : Noun → Noun := StrategyOfTraces.nounTail

/-- Axis of an OP0 formula `[0 ax]` (`0` off-shape). -/
def op0Axis : Noun → ℕ
  | .cell _ (.atom ax) => ax
  | _ => 0

/-- Axis of an OP9 formula `[9 [ax c]]` (`0` off-shape). -/
def op9Axis : Noun → ℕ
  | .cell _ (.cell (.atom ax) _) => ax
  | _ => 0

/-- The join's branch selector (`mapComputeJoinInFuel` `.s6`: atom value, `0` on a cell). -/
def condBit : Noun → ℕ
  | .atom k => k
  | _ => 0

/-- The formula shape of a row of state `st`. -/
def FormulaShape : State → Noun → Prop
  | .s0, f => ∃ ax : ℕ, f = .cell (.atom 0) (.atom ax)
  | .s1, f => ∃ t, f = .cell (.atom 1) t
  | .s2, f => ∃ b c, f = .cell (.atom 2) (.cell b c)
  | .s3, f => ∃ t, f = .cell (.atom 3) t
  | .s4, f => ∃ t, f = .cell (.atom 4) t
  | .s5, f => ∃ b c, f = .cell (.atom 5) (.cell b c)
  | .s6, f => ∃ b c d, f = .cell (.atom 6) (.cell b (.cell c d))
  | .s7, f => ∃ b c, f = .cell (.atom 7) (.cell b c)
  | .s8, f => ∃ b c, f = .cell (.atom 8) (.cell b c)
  | .s9, f => ∃ ax : ℕ, ∃ c, f = .cell (.atom 9) (.cell (.atom ax) c)
  | .cons, f => ∃ b c d, f = .cell (.cell b c) d

/-- The children's inputs `(subject, formula)`, in the **exec/AIR** child order, exactly as the
join `StrategyOfTraces.mapComputeJoinInFuel` passes them down: heads/tails of the row formula,
sibling results for the mutated subjects (OP2/7/8/9), the join's branch selector for OP6.  The
only non-structural input is OP9's arm, which a genuine row fetches from the core. -/
def KidInputs : State → Noun → Noun → List ComputeRowSkeleton → Prop
  | .s0, _, _, ks => ks = []
  | .s1, _, _, ks => ks = []
  | .cons, s, f, [k0, k1] =>
      k0.subject = s ∧ k0.formula = hd f ∧ k1.subject = s ∧ k1.formula = tl f
  | .s3, s, f, [k0] => k0.subject = s ∧ k0.formula = tl f
  | .s4, s, f, [k0] => k0.subject = s ∧ k0.formula = tl f
  | .s5, s, f, [k0, k1] =>
      k0.subject = s ∧ k0.formula = hd (tl f) ∧ k1.subject = s ∧ k1.formula = tl (tl f)
  | .s2, s, f, [k0, k1, k2] =>
      k0.subject = s ∧ k0.formula = hd (tl f) ∧ k1.subject = s ∧ k1.formula = tl (tl f) ∧
        k2.subject = k0.evaluation ∧ k2.formula = k1.evaluation
  | .s6, s, f, [kT, kC] =>
      kC.subject = s ∧ kC.formula = hd (tl f) ∧ kT.subject = s ∧
        kT.formula = (if condBit kC.evaluation = 0 then hd (tl (tl f)) else tl (tl (tl f)))
  | .s7, s, f, [kM, kH] =>
      kH.subject = s ∧ kH.formula = hd (tl f) ∧ kM.subject = kH.evaluation ∧
        kM.formula = tl (tl f)
  | .s8, s, f, [kM, kH] =>
      kH.subject = s ∧ kH.formula = hd (tl f) ∧ kM.subject = .cell kH.evaluation s ∧
        kM.formula = tl (tl f)
  | .s9, s, f, [kC, kI] =>
      kC.subject = s ∧ kC.formula = tl (tl f) ∧ kI.subject = kC.evaluation ∧
        Noun.slot (op9Axis f) kC.evaluation = some kI.formula
  | _, _, _, _ => False

/-- The row's evaluation as its opcode's output from the children (`Nock.evalN`; the cases of
`StrategyOfTraces.joinEvaluation`).  OP0's value is the served slot. -/
def RowOutput : State → Noun → Noun → List ComputeRowSkeleton → Noun → Prop
  | .s0, s, f, _, e => Noun.slot (op0Axis f) s = some e
  | .s1, _, f, _, e => e = tl f
  | .cons, _, _, [k0, k1], e => e = .cell k0.evaluation k1.evaluation
  | .s3, _, _, [k0], e => e = Noun.wut k0.evaluation
  | .s4, _, _, [k0], e => Noun.lus k0.evaluation = some e
  | .s5, _, _, [k0, k1], e => e = Noun.tis k0.evaluation k1.evaluation
  | .s2, _, _, [_, _, k2], e => e = k2.evaluation
  | .s6, _, _, [kT, kC], e =>
      (kC.evaluation = .atom 0 ∨ kC.evaluation = .atom 1) ∧ e = kT.evaluation
  | .s7, _, _, [kM, _], e => e = kM.evaluation
  | .s8, _, _, [kM, _], e => e = kM.evaluation
  | .s9, _, _, [_, kI], e => e = kI.evaluation
  | _, _, _, _, _ => False

/-- **A genuine built tree**: every row obeys its Nock step.  This is the predicate the binding
induction carries (rule 8(b)): it is NOT a property of arbitrary committed traces. -/
inductive GenuineSkel : NTree ComputeRowSkeleton → Prop
  | node {s : ComputeRowSkeleton} {kids : List (NTree ComputeRowSkeleton)}
      (shape : FormulaShape s.state s.formula)
      (inputs : KidInputs s.state s.subject s.formula (kids.map NTree.label))
      (output : RowOutput s.state s.subject s.formula (kids.map NTree.label) s.evaluation)
      (children : ∀ k ∈ kids, GenuineSkel k) :
      GenuineSkel (.node s kids)

theorem rowOutput_unique {st : State} {s f : Noun} {ks : List ComputeRowSkeleton} {e₁ e₂ : Noun}
    (h₁ : RowOutput st s f ks e₁) (h₂ : RowOutput st s f ks e₂) : e₁ = e₂ := by
  cases st <;> rcases ks with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    simp only [RowOutput] at h₁ h₂ <;>
    first
    | exact False.elim h₁
    | (rw [h₁] at h₂; exact Option.some.inj h₂)
    | (rw [h₁.2, h₂.2])
    | (rw [h₁, h₂])

variable {K : Type} [Field K]

/-- Simp set that evaluates the join's head/tail on literal cells. -/
theorem hd_cell (a b : Noun) : hd (.cell a b) = a := rfl

theorem tl_cell (a b : Noun) : tl (.cell a b) = b := rfl

/-- Row-label agreement of a built row with an honest generated row. -/
def LabelMatch (s : ComputeRowSkeleton) (g : GenComputeRow K) : Prop :=
  g.skel.state = s.state ∧ g.skel.subject = s.subject ∧ g.skel.formula = s.formula ∧
    g.skel.evaluation = s.evaluation

/-- Row-for-row alignment of a built tree with an honest generated tree (same shape, matching
labels, children in the same order). -/
inductive Aligned : NTree ComputeRowSkeleton → NTree (GenComputeRow K) → Prop
  | node {s : ComputeRowSkeleton} {kids : List (NTree ComputeRowSkeleton)}
      {g : GenComputeRow K} {gs : List (NTree (GenComputeRow K))}
      (hl : LabelMatch s g) (hk : List.Forall₂ Aligned kids gs) :
      Aligned (.node s kids) (.node g gs)

theorem airReorder_node (g : GenComputeRow K) (cs : List (NTree (GenComputeRow K))) :
    airReorder (.node g cs) =
      if airNeedsSwap g.skel.state then .node g (swapPair (cs.map airReorder))
      else .node g (cs.map airReorder) := by
  simp [airReorder]

theorem forall₂_exists_of_mem {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, ha => by simp at ha
  | _, _, .cons (a := x) (b := y) hxy hrest, a, ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨y, List.mem_cons_self .., hxy⟩
      · obtain ⟨b, hb, hab⟩ := forall₂_exists_of_mem hrest ha
        exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

/-- Alignment transports `InTree`: every row of the built tree is a row of the honest tree. -/
theorem Aligned.inTree {T : NTree ComputeRowSkeleton} {u : NTree ComputeRowSkeleton}
    (hu : InTree T u) : ∀ {A : NTree (GenComputeRow K)}, Aligned T A →
      ∃ v, InTree A v ∧ LabelMatch u.label v.label := by
  induction hu with
  | here c =>
      intro A h
      cases h with
      | node hl hk => exact ⟨_, InTree.here _, hl⟩
  | sub hs _ ih =>
      intro A h
      cases h with
      | node hl hk =>
          obtain ⟨a, ha, hal⟩ := forall₂_exists_of_mem hk (by simpa [NTree.children] using hs)
          obtain ⟨v, hv, hlab⟩ := ih hal
          exact ⟨v, InTree.sub (by simpa [NTree.children] using ha) hv, hlab⟩

/-- The induction hypothesis shape `step_align` consumes for each child. -/
def AlignsWithGen (k : NTree ComputeRowSkeleton) : Prop :=
  ∀ (n : ℕ) (sub : NTree (GenComputeRow K)) (r : Noun),
    genComputeSkeleton (K := K) n k.label.subject k.label.formula = .ok (sub, r) →
      r = k.label.evaluation ∧ Aligned k (airReorder sub)

/-- **One alignment step.**  At a row whose formula has its state's shape and whose children
receive the join's inputs, a successful generator run at the row's inputs produces an honest row
with the same state / subject / formula, its result is the opcode's output from the children,
and — given the children align (IH) — the children align with the honest children in AIR order. -/
theorem step_align {n : ℕ} {st : State} {subj f : Noun}
    {kids : List (NTree ComputeRowSkeleton)}
    {sub : NTree (GenComputeRow K)} {r : Noun}
    (hgen : genComputeSkeleton (K := K) n subj f = .ok (sub, r))
    (hshape : FormulaShape st f)
    (hin : KidInputs st subj f (kids.map NTree.label))
    (ih : ∀ k ∈ kids, AlignsWithGen (K := K) k) :
    RowOutput st subj f (kids.map NTree.label) r ∧
      (airReorder sub).label.skel.state = st ∧ (airReorder sub).label.skel.subject = subj ∧
      (airReorder sub).label.skel.formula = f ∧ (airReorder sub).label.skel.evaluation = r ∧
      List.Forall₂ Aligned kids (airReorder sub).children := by
  cases n with
  | zero => simp [genComputeSkeleton] at hgen
  | succ n =>
  cases st with
  | s0 =>
    obtain ⟨ax, rfl⟩ := hshape
    have hk : kids = [] := by simpa [KidInputs] using hin
    subst hk
    cases hsl : Noun.slot ax subj with
    | none => simp [genComputeSkeleton, hsl] at hgen
    | some res =>
      simp [genComputeSkeleton, hsl] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      refine ⟨by simpa [RowOutput, op0Axis] using hsl, ?_⟩
      simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp0, NTree.label, NTree.children]
  | s1 =>
    obtain ⟨t, rfl⟩ := hshape
    have hk : kids = [] := by simpa [KidInputs] using hin
    subst hk
    simp [genComputeSkeleton] at hgen
    obtain ⟨rfl, rfl⟩ := hgen
    refine ⟨by simp [RowOutput, tl_cell], ?_⟩
    simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp1, NTree.label, NTree.children]
  | cons =>
    obtain ⟨b, c, d, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hs0, hf0, hs1, hf1⟩ := hin
    cases hc0 : genComputeSkeleton (K := K) n subj (.cell b c) with
    | error e => simp [genComputeSkeleton, hc0] at hgen
    | ok p0 =>
    cases hc1 : genComputeSkeleton (K := K) n subj d with
    | error e => simp [genComputeSkeleton, hc0, hc1] at hgen
    | ok p1 =>
      obtain ⟨t0, r0⟩ := p0
      obtain ⟨t1, r1⟩ := p1
      simp [genComputeSkeleton, hc0, hc1] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      obtain ⟨he0, hal0⟩ := ih k0 (by simp) n t0 r0 (by rw [hs0, hf0]; exact hc0)
      obtain ⟨he1, hal1⟩ := ih k1 (by simp) n t1 r1 (by rw [hs1, hf1]; exact hc1)
      refine ⟨by simp [RowOutput, he0, he1], ?_⟩
      simp [airReorder_node, airNeedsSwap, skelNode, genSkelCons, NTree.label, NTree.children,
        hal0, hal1]
  | s3 =>
    obtain ⟨t, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp [KidInputs, tl_cell] at hin
    obtain ⟨hs0, hf0⟩ := hin
    cases hc : genComputeSkeleton (K := K) n subj t with
    | error e => simp [genComputeSkeleton, hc] at hgen
    | ok p =>
      obtain ⟨t1, r1⟩ := p
      simp [genComputeSkeleton, hc] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      obtain ⟨he0, hal0⟩ := ih k0 (by simp) n t1 r1 (by rw [hs0, hf0]; exact hc)
      refine ⟨by simp [RowOutput, he0], ?_⟩
      simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp3, NTree.label, NTree.children, hal0]
  | s4 =>
    obtain ⟨t, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp [KidInputs, tl_cell] at hin
    obtain ⟨hs0, hf0⟩ := hin
    cases hc : genComputeSkeleton (K := K) n subj t with
    | error e => simp [genComputeSkeleton, hc] at hgen
    | ok p =>
      obtain ⟨t1, r1⟩ := p
      cases hl : Noun.lus r1 with
      | none => simp [genComputeSkeleton, hc, hl] at hgen
      | some res =>
        simp [genComputeSkeleton, hc, hl] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        obtain ⟨he0, hal0⟩ := ih k0 (by simp) n t1 r1 (by rw [hs0, hf0]; exact hc)
        refine ⟨by simpa [RowOutput, he0] using hl, ?_⟩
        simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp4, NTree.label, NTree.children,
          hal0]
  | s5 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hs0, hf0, hs1, hf1⟩ := hin
    cases hc0 : genComputeSkeleton (K := K) n subj b with
    | error e => simp [genComputeSkeleton, hc0] at hgen
    | ok p0 =>
    cases hc1 : genComputeSkeleton (K := K) n subj c with
    | error e => simp [genComputeSkeleton, hc0, hc1] at hgen
    | ok p1 =>
      obtain ⟨t0, r0⟩ := p0
      obtain ⟨t1, r1⟩ := p1
      simp [genComputeSkeleton, hc0, hc1] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      obtain ⟨he0, hal0⟩ := ih k0 (by simp) n t0 r0 (by rw [hs0, hf0]; exact hc0)
      obtain ⟨he1, hal1⟩ := ih k1 (by simp) n t1 r1 (by rw [hs1, hf1]; exact hc1)
      refine ⟨by simp [RowOutput, he0, he1], ?_⟩
      simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp5, NTree.label, NTree.children,
        hal0, hal1]
  | s2 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hs0, hf0, hs1, hf1, hs2, hf2⟩ := hin
    cases hc0 : genComputeSkeleton (K := K) n subj b with
    | error e => simp [genComputeSkeleton, hc0] at hgen
    | ok p0 =>
    cases hc1 : genComputeSkeleton (K := K) n subj c with
    | error e => simp [genComputeSkeleton, hc0, hc1] at hgen
    | ok p1 =>
      obtain ⟨t0, r0⟩ := p0
      obtain ⟨t1, r1⟩ := p1
      obtain ⟨he0, hal0⟩ := ih k0 (by simp) n t0 r0 (by rw [hs0, hf0]; exact hc0)
      obtain ⟨he1, hal1⟩ := ih k1 (by simp) n t1 r1 (by rw [hs1, hf1]; exact hc1)
      cases hc2 : genComputeSkeleton (K := K) n r0 r1 with
      | error e => simp [genComputeSkeleton, hc0, hc1, hc2] at hgen
      | ok p2 =>
        obtain ⟨t2, r2⟩ := p2
        simp [genComputeSkeleton, hc0, hc1, hc2] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        obtain ⟨he2, hal2⟩ := ih k2 (by simp) n t2 r2
          (by rw [hs2, hf2, ← he0, ← he1]; exact hc2)
        refine ⟨by simp [RowOutput, he2], ?_⟩
        simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp2, NTree.label, NTree.children,
          hal0, hal1, hal2]
  | s6 =>
    obtain ⟨b, c, d, rfl⟩ := hshape
    rcases kids with _ | ⟨kT, _ | ⟨kC, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hsC, hfC, hsT, hfT⟩ := hin
    cases hc : genComputeSkeleton (K := K) n subj b with
    | error e => simp [genComputeSkeleton, hc] at hgen
    | ok p =>
      obtain ⟨tC, rc⟩ := p
      obtain ⟨heC, halC⟩ := ih kC (by simp) n tC rc (by rw [hsC, hfC]; exact hc)
      rcases rc with v | ⟨x, y⟩
      · rcases v with _ | _ | v
        · have hfT' : kT.label.formula = c := by rw [hfT, ← heC]; simp [condBit]
          cases ht : genComputeSkeleton (K := K) n subj c with
          | error e => simp [genComputeSkeleton, hc, ht] at hgen
          | ok q =>
            obtain ⟨tT, rT⟩ := q
            simp [genComputeSkeleton, hc, ht] at hgen
            obtain ⟨rfl, rfl⟩ := hgen
            obtain ⟨heT, halT⟩ := ih kT (by simp) n tT rT (by rw [hsT, hfT']; exact ht)
            refine ⟨by simp [RowOutput, ← heC, heT], ?_⟩
            simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp6, NTree.label,
              NTree.children, swapPair, halT, halC]
        · have hfT' : kT.label.formula = d := by rw [hfT, ← heC]; simp [condBit]
          cases ht : genComputeSkeleton (K := K) n subj d with
          | error e => simp [genComputeSkeleton, hc, ht] at hgen
          | ok q =>
            obtain ⟨tT, rT⟩ := q
            simp [genComputeSkeleton, hc, ht] at hgen
            obtain ⟨rfl, rfl⟩ := hgen
            obtain ⟨heT, halT⟩ := ih kT (by simp) n tT rT (by rw [hsT, hfT']; exact ht)
            refine ⟨by simp [RowOutput, ← heC, heT], ?_⟩
            simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp6, NTree.label,
              NTree.children, swapPair, halT, halC]
        · simp [genComputeSkeleton, hc] at hgen
      · simp [genComputeSkeleton, hc] at hgen
  | s7 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hsH, hfH, hsM, hfM⟩ := hin
    cases hb : genComputeSkeleton (K := K) n subj b with
    | error e => simp [genComputeSkeleton, hb] at hgen
    | ok p =>
      obtain ⟨tB, sb⟩ := p
      obtain ⟨heH, halH⟩ := ih kH (by simp) n tB sb (by rw [hsH, hfH]; exact hb)
      cases hcc : genComputeSkeleton (K := K) n sb c with
      | error e => simp [genComputeSkeleton, hb, hcc] at hgen
      | ok q =>
        obtain ⟨tC, rC⟩ := q
        simp [genComputeSkeleton, hb, hcc] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        obtain ⟨heM, halM⟩ := ih kM (by simp) n tC rC (by rw [hsM, hfM, ← heH]; exact hcc)
        refine ⟨by simp [RowOutput, heM], ?_⟩
        simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp7, NTree.label,
          NTree.children, swapPair, halM, halH]
  | s8 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hsH, hfH, hsM, hfM⟩ := hin
    cases hb : genComputeSkeleton (K := K) n subj b with
    | error e => simp [genComputeSkeleton, hb] at hgen
    | ok p =>
      obtain ⟨tB, sb⟩ := p
      obtain ⟨heH, halH⟩ := ih kH (by simp) n tB sb (by rw [hsH, hfH]; exact hb)
      cases hcc : genComputeSkeleton (K := K) n (.cell sb subj) c with
      | error e => simp [genComputeSkeleton, hb, hcc] at hgen
      | ok q =>
        obtain ⟨tC, rC⟩ := q
        simp [genComputeSkeleton, hb, hcc] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        obtain ⟨heM, halM⟩ := ih kM (by simp) n tC rC (by rw [hsM, hfM, ← heH]; exact hcc)
        refine ⟨by simp [RowOutput, heM], ?_⟩
        simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp8, NTree.label,
          NTree.children, swapPair, halM, halH]
  | s9 =>
    obtain ⟨ax, c, rfl⟩ := hshape
    rcases kids with _ | ⟨kC, _ | ⟨kI, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, tl_cell, op9Axis] at hin
    obtain ⟨hsC, hfC, hsI, hslot⟩ := hin
    cases hc : genComputeSkeleton (K := K) n subj c with
    | error e => simp [genComputeSkeleton, hc] at hgen
    | ok p =>
      obtain ⟨tC, core⟩ := p
      obtain ⟨heC, halC⟩ := ih kC (by simp) n tC core (by rw [hsC, hfC]; exact hc)
      have hsl : Noun.slot ax core = some kI.label.formula := by rw [heC]; exact hslot
      cases hi : genComputeSkeleton (K := K) n core kI.label.formula with
      | error e => simp [genComputeSkeleton, hc, hsl, hi] at hgen
      | ok q =>
        obtain ⟨tI, rI⟩ := q
        simp [genComputeSkeleton, hc, hsl, hi] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        obtain ⟨heI, halI⟩ := ih kI (by simp) n tI rI (by rw [hsI, ← heC]; exact hi)
        refine ⟨by simp [RowOutput, heI], ?_⟩
        simp [airReorder_node, airNeedsSwap, skelNode, genSkelOp9, NTree.label,
          NTree.children, halC, halI]

theorem ntree_eta {α : Type*} (t : NTree α) : t = .node t.label t.children := by
  cases t; rfl

/-- **Theorem 1 (honest-tree alignment).**  A genuine built tree is, row for row in AIR order, the
honest generated tree of its own root inputs: whenever the generator succeeds at
`(root subject, root formula)`, its result is the root evaluation and `airReorder` of its tree
is aligned with the built tree (equal state, subject, formula and evaluation at every row, the
children matched in order).  Nock determinism, no field and no coin. -/
theorem genuine_aligned {T : NTree ComputeRowSkeleton} (hT : GenuineSkel T) :
    AlignsWithGen (K := K) T := by
  induction hT with
  | @node s kids shape inputs output children ih =>
    intro n sub r hgen
    obtain ⟨hout, hst, hsj, hf, he, hall⟩ := step_align hgen shape inputs ih
    have hr : r = s.evaluation := rowOutput_unique hout output
    refine ⟨hr, ?_⟩
    rw [ntree_eta (airReorder sub)]
    exact .node ⟨hst, hsj, hf, he.trans hr⟩ hall

/-- Row nouns of a skeleton row are within `Λ`. -/
def RowNounsLe (Λ : ℕ) (s : ComputeRowSkeleton) : Prop :=
  s.subject.leaves ≤ Λ ∧ s.formula.leaves ≤ Λ ∧ s.evaluation.leaves ≤ Λ

/-- An aligned tree sitting inside a generated tree `G` inherits `G`'s window. -/
theorem aligned_rows_le {T : NTree ComputeRowSkeleton} {A G : NTree (GenComputeRow K)}
    (h : Aligned T A) (hA : InTree G A) :
    ∀ u, InTree T u → RowNounsLe (programLeafBound G) u.label := by
  intro u hu
  obtain ⟨v, hv, hl⟩ := Aligned.inTree hu h
  have hc := confined_inTree (traceConfined_of_leafBound (le_refl (programLeafBound G)))
    (InTree_trans hA hv)
  obtain ⟨hst, hsj, hf, he⟩ := hl
  obtain ⟨c1, c2, c3⟩ := hc
  exact ⟨hsj ▸ c1, hf ▸ c2, he ▸ c3⟩

/-- **Theorem 1, window form.**  A genuine built tree whose root inputs are the claim `(S, F)` of
a successful generator run is aligned with the honest AIR-order tree, its root evaluation is the
honest result, and every noun of every row has `≤ programLeafBound (airReorder G)` leaves — the
compiler's `Λ` (`GenNockCompilesCarrier.lean` group 8: `Λ := programLeafBound`). -/
theorem genuine_rows_le_programLeafBound {fuel : ℕ} {S Fm R : Noun}
    {G : NTree (GenComputeRow K)}
    (hG : genComputeSkeleton (K := K) fuel S Fm = .ok (G, R))
    {T : NTree ComputeRowSkeleton} (hT : GenuineSkel T)
    (hS : T.label.subject = S) (hF : T.label.formula = Fm) :
    R = T.label.evaluation ∧ Aligned T (airReorder G) ∧
      ∀ u, InTree T u → RowNounsLe (programLeafBound (airReorder G)) u.label := by
  have h := genuine_aligned (K := K) hT fuel G R (by rw [hS, hF]; exact hG)
  exact ⟨h.1, h.2, aligned_rows_le h.2 (InTree.here _)⟩

/-- `(s, f)` is an **honest call** of the generated tree `G`: some generator run at `(s, f)`
succeeds, and its AIR-order tree is a subtree of `airReorder G`.  The root claim is one
(`honestCall_root`); Theorem 2 propagates it down the evaluation order. -/
def HonestCall (G : NTree (GenComputeRow K)) (s f : Noun) : Prop :=
  ∃ (n : ℕ) (sub : NTree (GenComputeRow K)) (r : Noun),
    genComputeSkeleton (K := K) n s f = .ok (sub, r) ∧ InTree (airReorder G) (airReorder sub)

theorem honestCall_root {fuel : ℕ} {S Fm R : Noun} {G : NTree (GenComputeRow K)}
    (hG : genComputeSkeleton (K := K) fuel S Fm = .ok (G, R)) : HonestCall G S Fm :=
  ⟨fuel, G, R, hG, InTree.here _⟩

/-- An honest call's inputs are inside the window (the row's subject and formula, before the row
is bound: what `PairFaithful` on the formula needs to discharge `FormulaShape`). -/
theorem honestCall_inputs_le {G : NTree (GenComputeRow K)} {s f : Noun}
    (hc : HonestCall G s f) :
    s.leaves ≤ programLeafBound (airReorder G) ∧ f.leaves ≤ programLeafBound (airReorder G) := by
  obtain ⟨n, sub, r, hgen, hG⟩ := hc
  obtain ⟨hs, hf, _⟩ := genComputeSkeleton_root_sfe hgen
  have hc := confined_inTree (traceConfined_of_leafBound
    (le_refl (programLeafBound (airReorder G)))) hG
  rw [airReorder_label] at hc
  exact ⟨hs ▸ hc.1, hf ▸ hc.2.1⟩

/-- A genuine tree at an honest call: every row is in the window. -/
theorem genuine_rows_le_of_honestCall {G : NTree (GenComputeRow K)}
    {T : NTree ComputeRowSkeleton} (hc : HonestCall G T.label.subject T.label.formula)
    (hT : GenuineSkel T) :
    ∀ u, InTree T u → RowNounsLe (programLeafBound (airReorder G)) u.label := by
  obtain ⟨n, sub, r, hgen, hG⟩ := hc
  exact aligned_rows_le (genuine_aligned (K := K) hT n sub r hgen).2 hG

/-- Evaluation order of a row's children: the generator's DFS order, i.e. the exec/AIR order
with OP6/7/8 swapped back (`airNeedsSwap`). -/
def evalOrder {α : Type*} (st : State) (l : List α) : List α :=
  if airNeedsSwap st then swapPair l else l

theorem honestCall_of_child {G sub t : NTree (GenComputeRow K)} {n : ℕ} {s f r : Noun}
    (hG : InTree (airReorder G) (airReorder sub))
    (hc : genComputeSkeleton (K := K) n s f = .ok (t, r))
    (hmem : airReorder t ∈ (airReorder sub).children) : HonestCall G s f :=
  ⟨n, t, r, hc, InTree_trans hG (InTree.sub hmem (InTree.here _))⟩

/-- **Theorem 2(a) — honest calls propagate down the evaluation order.**  At a row whose inputs
are an honest call (formula of its state's shape, children fed the join's inputs), the `i`-th
child in evaluation order is itself at an honest call as soon as the children before it in
evaluation order are genuine.  This is what lets the binding induction recurse into child `i`
with the window available (Theorem 2(b) at that child) before child `i` is bound. -/
theorem honestCall_kid {G : NTree (GenComputeRow K)} {st : State} {subj f : Noun}
    {kids : List (NTree ComputeRowSkeleton)}
    (hcall : HonestCall G subj f) (hshape : FormulaShape st f)
    (hin : KidInputs st subj f (kids.map NTree.label)) :
    ∀ (i : ℕ) (k : NTree ComputeRowSkeleton), (evalOrder st kids)[i]? = some k →
      (∀ (j : ℕ) (k' : NTree ComputeRowSkeleton), j < i →
        (evalOrder st kids)[j]? = some k' → GenuineSkel k') →
      HonestCall G k.label.subject k.label.formula := by
  obtain ⟨n, sub, r, hgen, hG⟩ := hcall
  cases n with
  | zero => simp [genComputeSkeleton] at hgen
  | succ n =>
  intro i k hk hprev
  cases st with
  | s0 =>
    have hkids : kids = [] := by simpa [KidInputs] using hin
    subst hkids; simp [evalOrder, airNeedsSwap] at hk
  | s1 =>
    have hkids : kids = [] := by simpa [KidInputs] using hin
    subst hkids; simp [evalOrder, airNeedsSwap] at hk
  | cons =>
    obtain ⟨b, c, d, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hs0, hf0, hs1, hf1⟩ := hin
    cases hc0 : genComputeSkeleton (K := K) n subj (.cell b c) with
    | error e => simp [genComputeSkeleton, hc0] at hgen
    | ok p0 =>
    cases hc1 : genComputeSkeleton (K := K) n subj d with
    | error e => simp [genComputeSkeleton, hc0, hc1] at hgen
    | ok p1 =>
      obtain ⟨t0, r0⟩ := p0
      obtain ⟨t1, r1⟩ := p1
      simp [genComputeSkeleton, hc0, hc1] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap] at hk <;> subst hk
      · exact honestCall_of_child hG (by rw [hs0, hf0]; exact hc0) (by simp [airReorder_node, airNeedsSwap, skelNode,
          genSkelCons, NTree.children])
      · exact honestCall_of_child hG (by rw [hs1, hf1]; exact hc1) (by simp [airReorder_node, airNeedsSwap, skelNode,
          genSkelCons, NTree.children])
  | s3 =>
    obtain ⟨t, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp [KidInputs, tl_cell] at hin
    obtain ⟨hs0, hf0⟩ := hin
    cases hc : genComputeSkeleton (K := K) n subj t with
    | error e => simp [genComputeSkeleton, hc] at hgen
    | ok p =>
      obtain ⟨t1, r1⟩ := p
      simp [genComputeSkeleton, hc] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      rcases i with _ | i <;> simp [evalOrder, airNeedsSwap] at hk
      subst hk
      exact honestCall_of_child hG (by rw [hs0, hf0]; exact hc) (by simp [airReorder_node, airNeedsSwap, skelNode,
        genSkelOp3, NTree.children])
  | s4 =>
    obtain ⟨t, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, rest⟩⟩ <;> simp [KidInputs, tl_cell] at hin
    obtain ⟨hs0, hf0⟩ := hin
    cases hc : genComputeSkeleton (K := K) n subj t with
    | error e => simp [genComputeSkeleton, hc] at hgen
    | ok p =>
      obtain ⟨t1, r1⟩ := p
      cases hl : Noun.lus r1 with
      | none => simp [genComputeSkeleton, hc, hl] at hgen
      | some res =>
        simp [genComputeSkeleton, hc, hl] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        rcases i with _ | i <;> simp [evalOrder, airNeedsSwap] at hk
        subst hk
        exact honestCall_of_child hG (by rw [hs0, hf0]; exact hc) (by simp [airReorder_node, airNeedsSwap, skelNode,
          genSkelOp4, NTree.children])
  | s5 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hs0, hf0, hs1, hf1⟩ := hin
    cases hc0 : genComputeSkeleton (K := K) n subj b with
    | error e => simp [genComputeSkeleton, hc0] at hgen
    | ok p0 =>
    cases hc1 : genComputeSkeleton (K := K) n subj c with
    | error e => simp [genComputeSkeleton, hc0, hc1] at hgen
    | ok p1 =>
      obtain ⟨t0, r0⟩ := p0
      obtain ⟨t1, r1⟩ := p1
      simp [genComputeSkeleton, hc0, hc1] at hgen
      obtain ⟨rfl, rfl⟩ := hgen
      rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap] at hk <;> subst hk
      · exact honestCall_of_child hG (by rw [hs0, hf0]; exact hc0) (by simp [airReorder_node, airNeedsSwap, skelNode,
          genSkelOp5, NTree.children])
      · exact honestCall_of_child hG (by rw [hs1, hf1]; exact hc1) (by simp [airReorder_node, airNeedsSwap, skelNode,
          genSkelOp5, NTree.children])
  | s2 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, rest⟩⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hs0, hf0, hs1, hf1, hs2, hf2⟩ := hin
    cases hc0 : genComputeSkeleton (K := K) n subj b with
    | error e => simp [genComputeSkeleton, hc0] at hgen
    | ok p0 =>
    cases hc1 : genComputeSkeleton (K := K) n subj c with
    | error e => simp [genComputeSkeleton, hc0, hc1] at hgen
    | ok p1 =>
      obtain ⟨t0, r0⟩ := p0
      obtain ⟨t1, r1⟩ := p1
      cases hc2 : genComputeSkeleton (K := K) n r0 r1 with
      | error e => simp [genComputeSkeleton, hc0, hc1, hc2] at hgen
      | ok p2 =>
        obtain ⟨t2, r2⟩ := p2
        simp [genComputeSkeleton, hc0, hc1, hc2] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        rcases i with _ | _ | _ | i <;> simp [evalOrder, airNeedsSwap] at hk <;> subst hk
        · exact honestCall_of_child hG (by rw [hs0, hf0]; exact hc0) (by simp [airReorder_node, airNeedsSwap, skelNode,
            genSkelOp2, NTree.children])
        · exact honestCall_of_child hG (by rw [hs1, hf1]; exact hc1) (by simp [airReorder_node, airNeedsSwap, skelNode,
            genSkelOp2, NTree.children])
        · have g0 : GenuineSkel k0 := hprev 0 k0 (by omega) (by simp [evalOrder, airNeedsSwap])
          have g1 : GenuineSkel k1 := hprev 1 k1 (by omega) (by simp [evalOrder, airNeedsSwap])
          have he0 := (genuine_aligned (K := K) g0 n t0 r0 (by rw [hs0, hf0]; exact hc0)).1
          have he1 := (genuine_aligned (K := K) g1 n t1 r1 (by rw [hs1, hf1]; exact hc1)).1
          exact honestCall_of_child hG (by rw [hs2, hf2, ← he0, ← he1]; exact hc2) (by simp [airReorder_node, airNeedsSwap, skelNode,
            genSkelOp2, NTree.children])
  | s6 =>
    obtain ⟨b, c, d, rfl⟩ := hshape
    rcases kids with _ | ⟨kT, _ | ⟨kC, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hsC, hfC, hsT, hfT⟩ := hin
    cases hc : genComputeSkeleton (K := K) n subj b with
    | error e => simp [genComputeSkeleton, hc] at hgen
    | ok p =>
      obtain ⟨tC, rc⟩ := p
      rcases rc with v | ⟨x, y⟩
      · rcases v with _ | _ | v
        · cases ht : genComputeSkeleton (K := K) n subj c with
          | error e => simp [genComputeSkeleton, hc, ht] at hgen
          | ok q =>
            obtain ⟨tT, rT⟩ := q
            simp [genComputeSkeleton, hc, ht] at hgen
            obtain ⟨rfl, rfl⟩ := hgen
            rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap, swapPair] at hk <;>
              subst hk
            · exact honestCall_of_child hG (by rw [hsC, hfC]; exact hc) (by simp [airReorder_node, airNeedsSwap, skelNode,
                genSkelOp6, swapPair, NTree.children])
            · have gC : GenuineSkel kC :=
                hprev 0 kC (by omega) (by simp [evalOrder, airNeedsSwap, swapPair])
              have heC := (genuine_aligned (K := K) gC n tC _ (by rw [hsC, hfC]; exact hc)).1
              have hfT' : kT.label.formula = c := by rw [hfT, ← heC]; simp [condBit]
              exact honestCall_of_child hG (by rw [hsT, hfT']; exact ht) (by simp [airReorder_node, airNeedsSwap, skelNode,
                genSkelOp6, swapPair, NTree.children])
        · cases ht : genComputeSkeleton (K := K) n subj d with
          | error e => simp [genComputeSkeleton, hc, ht] at hgen
          | ok q =>
            obtain ⟨tT, rT⟩ := q
            simp [genComputeSkeleton, hc, ht] at hgen
            obtain ⟨rfl, rfl⟩ := hgen
            rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap, swapPair] at hk <;>
              subst hk
            · exact honestCall_of_child hG (by rw [hsC, hfC]; exact hc) (by simp [airReorder_node, airNeedsSwap, skelNode,
                genSkelOp6, swapPair, NTree.children])
            · have gC : GenuineSkel kC :=
                hprev 0 kC (by omega) (by simp [evalOrder, airNeedsSwap, swapPair])
              have heC := (genuine_aligned (K := K) gC n tC _ (by rw [hsC, hfC]; exact hc)).1
              have hfT' : kT.label.formula = d := by rw [hfT, ← heC]; simp [condBit]
              exact honestCall_of_child hG (by rw [hsT, hfT']; exact ht) (by simp [airReorder_node, airNeedsSwap, skelNode,
                genSkelOp6, swapPair, NTree.children])
        · simp [genComputeSkeleton, hc] at hgen
      · simp [genComputeSkeleton, hc] at hgen
  | s7 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hsH, hfH, hsM, hfM⟩ := hin
    cases hb : genComputeSkeleton (K := K) n subj b with
    | error e => simp [genComputeSkeleton, hb] at hgen
    | ok p =>
      obtain ⟨tB, sb⟩ := p
      cases hcc : genComputeSkeleton (K := K) n sb c with
      | error e => simp [genComputeSkeleton, hb, hcc] at hgen
      | ok q =>
        obtain ⟨tC, rC⟩ := q
        simp [genComputeSkeleton, hb, hcc] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap, swapPair] at hk <;> subst hk
        · exact honestCall_of_child hG (by rw [hsH, hfH]; exact hb) (by simp [airReorder_node, airNeedsSwap, skelNode,
            genSkelOp7, swapPair, NTree.children])
        · have gH : GenuineSkel kH :=
            hprev 0 kH (by omega) (by simp [evalOrder, airNeedsSwap, swapPair])
          have heH := (genuine_aligned (K := K) gH n tB sb (by rw [hsH, hfH]; exact hb)).1
          exact honestCall_of_child hG (by rw [hsM, hfM, ← heH]; exact hcc) (by simp [airReorder_node, airNeedsSwap, skelNode,
            genSkelOp7, swapPair, NTree.children])
  | s8 =>
    obtain ⟨b, c, rfl⟩ := hshape
    rcases kids with _ | ⟨kM, _ | ⟨kH, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, hd_cell, tl_cell] at hin
    obtain ⟨hsH, hfH, hsM, hfM⟩ := hin
    cases hb : genComputeSkeleton (K := K) n subj b with
    | error e => simp [genComputeSkeleton, hb] at hgen
    | ok p =>
      obtain ⟨tB, sb⟩ := p
      cases hcc : genComputeSkeleton (K := K) n (.cell sb subj) c with
      | error e => simp [genComputeSkeleton, hb, hcc] at hgen
      | ok q =>
        obtain ⟨tC, rC⟩ := q
        simp [genComputeSkeleton, hb, hcc] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap, swapPair] at hk <;> subst hk
        · exact honestCall_of_child hG (by rw [hsH, hfH]; exact hb) (by simp [airReorder_node, airNeedsSwap, skelNode,
            genSkelOp8, swapPair, NTree.children])
        · have gH : GenuineSkel kH :=
            hprev 0 kH (by omega) (by simp [evalOrder, airNeedsSwap, swapPair])
          have heH := (genuine_aligned (K := K) gH n tB sb (by rw [hsH, hfH]; exact hb)).1
          exact honestCall_of_child hG (by rw [hsM, hfM, ← heH]; exact hcc) (by simp [airReorder_node, airNeedsSwap, skelNode,
            genSkelOp8, swapPair, NTree.children])
  | s9 =>
    obtain ⟨ax, c, rfl⟩ := hshape
    rcases kids with _ | ⟨kC, _ | ⟨kI, _ | ⟨k2, rest⟩⟩⟩ <;>
      simp [KidInputs, tl_cell, op9Axis] at hin
    obtain ⟨hsC, hfC, hsI, hslot⟩ := hin
    cases hc : genComputeSkeleton (K := K) n subj c with
    | error e => simp [genComputeSkeleton, hc] at hgen
    | ok p =>
      obtain ⟨tC, core⟩ := p
      cases hsl : Noun.slot ax core with
      | none => simp [genComputeSkeleton, hc, hsl] at hgen
      | some arm =>
      cases hi : genComputeSkeleton (K := K) n core arm with
      | error e => simp [genComputeSkeleton, hc, hsl, hi] at hgen
      | ok q =>
        obtain ⟨tI, rI⟩ := q
        simp [genComputeSkeleton, hc, hsl, hi] at hgen
        obtain ⟨rfl, rfl⟩ := hgen
        rcases i with _ | _ | i <;> simp [evalOrder, airNeedsSwap] at hk <;> subst hk
        · exact honestCall_of_child hG (by rw [hsC, hfC]; exact hc) (by simp [airReorder_node, airNeedsSwap, skelNode,
            genSkelOp9, NTree.children])
        · have gC : GenuineSkel kC := hprev 0 kC (by omega) (by simp [evalOrder, airNeedsSwap])
          have heC := (genuine_aligned (K := K) gC n tC core (by rw [hsC, hfC]; exact hc)).1
          have harm : kI.label.formula = arm := by
            rw [← heC] at hslot; rw [hsl] at hslot; exact (Option.some.inj hslot).symm
          exact honestCall_of_child hG (by rw [hsI, harm, ← heC]; exact hi) (by simp [airReorder_node, airNeedsSwap, skelNode,
            genSkelOp9, NTree.children])

end Nock.NockVMROM.Thm54.ComputedWindow
