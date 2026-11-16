import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestFill

/-!
# The walk gates of the tower compute chip at the honest BFS walk

A-free copies of `exact_finalWalk_transition_sources`, `walk_steps_eq`, `queue_eq` and `endpoints_eq`
(`Unhosted309Canonical`) over an `HonestWalk L` (generic field `L = 𝕂′`): the BFS rows of a tree `root`, the
`RLC^γ` node valuation, the walk columns `ln / cnt / acc` with `Walk.WalkSat` at `initial_count = α` and
the root seed.  `HonestWalk.hEnc/htopo/hpub` are `WalkLabelObligations` restated per BFS row; the walk
exists at every `(α, γ)` (`honestWalk_exists`, no condition on the coins).

* `NextReads` / `FirstReads`: the label reads of the successor / first row (selectors one-hot, restored
  sources = fingerprints, hosted child tags, coins) — the A-free restatement of
  `exactFinalCurrentEnv_{selectors,sourcePubAtR,childTagHost}`.  `.label /.cc /.cm` evaluate the in-gate
  `labelRLC / childSumCC / selectorCM` (`ComputeWalkLabel`, reader-generic).
* `walk_transition_sources`, `walk_{ln1,count1,accInit,out}_source`, `HonestWalk.acc_last` (perfect
  completeness, `Walk.walk_completeness` + `bfs_isFullBFT`), `HonestWalk.cnt_last` (tiling),
  `HonestWalk.cnt_ne_ln` (needs `h ≤ orderOf α`; `Batch478.honest_ratio_gate`).
* The typed gates at `Env309 F L`: `gate73..77`, `aux0`, `aux1`, `ep_ln1`, `ep_count1`, `ep_out`,
  `ep4_accInit`, and the headline `walk_row_holds` from `WalkRowEnv`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.OptimizedComputeCodec

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The honest BFS walk -/

/-- **The honest BFS walk at `(α, γ)`** over a generic field `L` (`L = 𝕂′`).  The tree rows are the
generator's BFS rows (`root`); `nodeVal` is the `RLC^γ` valuation; `ln / cnt / acc` are the walk columns
(`W0 = cnt`, `W1 = acc`, role `61 = ln`) with `WalkSat` at `initial_count = α` and the claim seed.
`hEnc` / `htopo` are `WalkLabelObligations` restated per BFS row; `hpub` names the row's `Pub`. -/
structure HonestWalk (L : Type) [Field L] where
  root : Walk.NTree (State × DTcomp L)
  nodeVal : Walk.NTree (State × DTcomp L) → L
  α : L
  γ : L
  seed : L
  ln : ℕ → L
  cnt : ℕ → L
  acc : ℕ → L
  pubAt : ℕ → Pub L
  hEnc : ∀ t, nodeVal t = Walk.rlc γ (labelVecOfPub t.label.2.2.1)
  htopo : ∀ t ∈ Walk.bfsForest [root],
    t.label.1 = t.label.2.2.1.state ∧ fanoutComp t.label.1 = t.children.length ∧
      childLinkComp t.label (fun j => t.childLabel j)
  hpub : ∀ i (hi : i < (Walk.bfsForest [root]).length),
    ((Walk.bfsForest [root])[i]).label.2.2.1 = pubAt i
  sat : Walk.WalkSat (Walk.curCol nodeVal (Walk.bfsForest [root]))
    (Walk.chldCol nodeVal (Walk.bfsForest [root])) (Walk.foCol (Walk.bfsForest [root]))
    ln cnt acc α seed α (Walk.bfsForest [root]).length
  seed_eq : seed = Walk.rlc γ (labelVecOfPub (pubAt 0)) * α

section Honest
variable {L : Type} [Field L] (D : HonestWalk L)

/-- The BFS row list. -/
abbrev HonestWalk.W : List (Walk.NTree (State × DTcomp L)) := Walk.bfsForest [D.root]

theorem HonestWalk.cur_eq (i : ℕ) (hi : i < D.W.length) :
    Walk.curCol D.nodeVal D.W (i + 1) = Walk.rlc D.γ (labelVecOfPub (D.pubAt i)) := by
  have hp : D.W[i].label.2.2.1 = D.pubAt i := D.hpub i hi
  simp only [Walk.curCol, Nat.add_sub_cancel, List.getElem?_eq_getElem hi, Option.map_some,
    Option.getD_some, D.hEnc, hp]

theorem HonestWalk.fo_eq (i : ℕ) (hi : i < D.W.length) :
    Walk.foCol D.W (i + 1) = fanoutComp (D.pubAt i).state := by
  obtain ⟨hst, hfan, -⟩ := D.htopo _ (List.getElem_mem hi)
  simp only [Walk.foCol, Nat.add_sub_cancel, List.getElem?_eq_getElem hi, Option.map_some,
    Option.getD_some]
  have hp : D.W[i].label.2.2.1 = D.pubAt i := D.hpub i hi
  rw [← hfan, hst, hp]

theorem HonestWalk.chld_eq (i : ℕ) (hi : i < D.W.length) (l : ℕ) (hl1 : 1 ≤ l)
    (hl : l ≤ fanoutComp (D.pubAt i).state) :
    Walk.chldCol D.nodeVal D.W (i + 1) l =
      Walk.rlc D.γ (ComputeWalkLabel.childVecN (D.pubAt i)
        (fun j => childStateTagCol D.W (i + 1) j) (l - 1)) := by
  obtain ⟨hst, hfan, hlink⟩ := D.htopo _ (List.getElem_mem hi)
  set t := D.W[i] with htdef
  have ht : D.W[i]? = some t := List.getElem?_eq_getElem hi
  have hpub : D.pubAt i = t.label.2.2.1 := (D.hpub i hi).symm
  have hfo : fanoutComp (D.pubAt i).state = t.children.length := by
    rw [hpub, ← hst, hfan]
  have hlt : l - 1 < t.children.length := by omega
  have hle3 : l - 1 < 3 := by
    have := ComputeWalkLabel.fanoutComp_le_three (D.pubAt i).state
    omega
  obtain ⟨c, hc⟩ : ∃ c, t.children[l - 1]? = some c :=
    ⟨t.children[l - 1], List.getElem?_eq_getElem hlt⟩
  have hlinkj' : (c.label.2.2.1.s, c.label.2.2.1.f, c.label.2.2.1.e) =
      sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩ := by
    have hlinkj := hlink ⟨l - 1, hle3⟩ (by
      show l - 1 < fanoutComp t.label.1
      rw [hst, ← hpub]; omega)
    simp only [Walk.NTree.childLabel, Walk.NTree.childOpt, hc, Option.map_some] at hlinkj
    exact Option.some.inj hlinkj
  have hcs : c.label.2.2.1.s = (sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩).1 :=
    congrArg Prod.fst hlinkj'
  have hcf : c.label.2.2.1.f = (sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩).2.1 :=
    congrArg (fun x => x.2.1) hlinkj'
  have hce : c.label.2.2.1.e = (sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩).2.2 :=
    congrArg (fun x => x.2.2) hlinkj'
  have htag : childStateTagCol D.W (i + 1) (l - 1) =
      stateTagField c.label.2.2.1.state := by
    simp [childStateTagCol, ht, hc]
  simp only [Walk.chldCol, Nat.add_sub_cancel, ht, Option.bind_some, hc, Option.map_some,
    Option.getD_some, D.hEnc]
  congr 1
  rw [hpub]
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, (j : ℕ) = l - 1 := ⟨⟨l - 1, hle3⟩, rfl⟩
  rw [← hj, ComputeWalkLabel.childVecN_fin]
  funext k
  have hj' : (⟨l - 1, hle3⟩ : Fin 3) = j := Fin.ext hj.symm
  rw [hj'] at hcs hcf hce
  rw [← hj] at htag
  fin_cases k <;>
    simp [labelVecOfPub, ComputeWalkLabel.childVec, htag, hcs, hcf, hce]


/-! ## 2. The label reads of the successor row and of the first row (the walk-row hypotheses) -/

/-- **Successor-row reads** (`nextReader` at row `j`): the A-free restatement of
`exactFinalCurrentEnv_selectors`, `_sourcePubAtR`, `_childTagHost` and `walkChallenge` for the transition
environment: one-hot state selectors, restored sources = the row's fingerprints (hypothesis (1)/(2)), the
hosted child tags = the tree's, and the walk coins. -/
structure NextReads (S : Env L) (j : ℕ) : Prop where
  sel : ∀ st, S.traceNext (Nock.Reified.opCol st) = if st = (D.pubAt j).state then 1 else 0
  src : ∀ (role c : ℕ) (hr : role < 12) (hc : c < 3),
    (sourcePubAtR curReader (D.pubAt j).state role c).eval (shiftNext S) =
      fpCoordinate (pubFingerprint (D.pubAt j) ⟨role, hr⟩) ⟨c, hc⟩
  tag : ∀ k : Fin 3, (childTagHost curReader (D.pubAt j).state k).eval (shiftNext S) =
    childStateTagCol D.W (j + 1) k
  alpha : (walkChallenge 0).eval S = D.α
  gamma : walkGammaChallenge.eval S = D.γ

/-- **First-row reads** (`firstReader`: the public initial-state masks `20 + opCol`). -/
structure FirstReads (S : Env L) : Prop where
  sel : ∀ st, S.pub (20 + Nock.Reified.opCol st) = if st = (D.pubAt 0).state then 1 else 0
  src : ∀ (role c : ℕ) (hr : role < 12) (hc : c < 3),
    (sourcePubAtR curReader (D.pubAt 0).state role c).eval S =
      fpCoordinate (pubFingerprint (D.pubAt 0) ⟨role, hr⟩) ⟨c, hc⟩
  tag : ∀ k : Fin 3, (childTagHost curReader (D.pubAt 0).state k).eval S =
    childStateTagCol D.W 1 k
  alpha : (walkChallenge 0).eval S = D.α
  gamma : walkGammaChallenge.eval S = D.γ

variable {D}

theorem NextReads.label {S : Env L} {j : ℕ} (R : NextReads D S j) :
    (labelRLC nextReader).eval S = Walk.rlc D.γ (labelVecOfPub (D.pubAt j)) := by
  rw [labelRLC_next_eval]
  exact labelRLC_eval curReader (shiftNext S) (D.pubAt j) D.γ
    (fun st => by
      show (shiftNext S).trace (Nock.Reified.opCol st) = _
      exact R.sel st)
    R.src (by rw [gamma_eval_shift]; exact R.gamma)

theorem NextReads.cc {S : Env L} {j : ℕ} (R : NextReads D S j) :
    (childSumCC nextReader).eval S =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (D.pubAt j).state), D.α ^ l *
        Walk.rlc D.γ (childVecN (D.pubAt j) (fun k => childStateTagCol D.W (j + 1) k) (l - 1)) := by
  rw [childSumCC_next_eval]
  exact childSumCC_eval curReader (shiftNext S) (D.pubAt j) D.α D.γ
    (fun k => childStateTagCol D.W (j + 1) k)
    (fun st => by
      show (shiftNext S).trace (Nock.Reified.opCol st) = _
      exact R.sel st)
    R.src (by rw [alpha_eval_shift]; exact R.alpha) (by rw [gamma_eval_shift]; exact R.gamma) R.tag

theorem NextReads.cm {S : Env L} {j : ℕ} (R : NextReads D S j) :
    (selectorCM nextReader).eval S = D.α ^ fanoutComp (D.pubAt j).state := by
  rw [selectorCM_next_eval]
  exact selectorCM_eval curReader (shiftNext S) (D.pubAt j) D.α
    (fun st => by
      show (shiftNext S).trace (Nock.Reified.opCol st) = _
      exact R.sel st)
    (by rw [alpha_eval_shift]; exact R.alpha)

theorem FirstReads.label {S : Env L} (R : FirstReads D S) :
    (labelRLC firstReader).eval S = Walk.rlc D.γ (labelVecOfPub (D.pubAt 0)) :=
  labelRLC_eval firstReader S (D.pubAt 0) D.γ
    (fun st => by
      show S.pub (20 + Nock.Reified.opCol st) = _
      exact R.sel st)
    (fun role c hr hc => by rw [sourcePubAtR_first]; exact R.src role c hr hc) R.gamma

theorem FirstReads.cc {S : Env L} (R : FirstReads D S) :
    (childSumCC firstReader).eval S =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (D.pubAt 0).state), D.α ^ l *
        Walk.rlc D.γ (childVecN (D.pubAt 0) (fun k => childStateTagCol D.W 1 k) (l - 1)) :=
  childSumCC_eval firstReader S (D.pubAt 0) D.α D.γ (fun k => childStateTagCol D.W 1 k)
    (fun st => by
      show S.pub (20 + Nock.Reified.opCol st) = _
      exact R.sel st)
    (fun role c hr hc => by rw [sourcePubAtR_first]; exact R.src role c hr hc) R.alpha R.gamma
    (fun k => by rw [childTagHost_first]; exact R.tag k)

theorem FirstReads.cm {S : Env L} (R : FirstReads D S) :
    (selectorCM firstReader).eval S = D.α ^ fanoutComp (D.pubAt 0).state :=
  selectorCM_eval firstReader S (D.pubAt 0) D.α
    (fun st => by
      show S.pub (20 + Nock.Reified.opCol st) = _
      exact R.sel st) R.alpha


/-! ## 3. The 309 walk sources, unfolded -/

section Unfold
variable {K : Type} [Field K]

theorem walkLnStep_eval' (env : Env K) :
    (Trans.walkLnStep.subst finalWalkSubstInGate).eval env =
      (finalWalkLine .traceNext).eval env - (walkChallenge 0).eval env *
        (finalWalkLine .traceCur).eval env := by
  rw [Expr.eval_subst]; rfl

theorem walkCountStep309_eval' (env : Env K) :
    walkCountStep309.eval env =
      env.traceNext 303 - env.trace 303 * (selectorCM nextReader).eval env := by
  rw [walkCountStep309, Expr.eval_subst]; rfl

theorem walkAccStep309_eval' (env : Env K) :
    walkAccStep309.eval env =
      (finalWalkLine .traceNext).eval env * (labelRLC nextReader).eval env + env.traceNext 306 -
        env.trace 306 - env.trace 303 * (childSumCC nextReader).eval env := by
  rw [walkAccStep309, Expr.eval_subst]; rfl

theorem walkCount1_309_eval' (env : Env K) :
    (Trans.walkCount1.subst finalWalkInitialSubst309).eval env =
      env.trace 303 - env.pub 0 * (selectorCM firstReader).eval env := by
  rw [Expr.eval_subst]; rfl

theorem walkAccInit_309_eval' (env : Env K) :
    (Trans.walkAccInit.subst finalWalkInitialSubst309).eval env =
      (finalWalkLine .traceCur).eval env * (labelRLC firstReader).eval env + env.trace 306 -
        (env.pub 0 * (childSumCC firstReader).eval env + env.pub 1) := by
  rw [Expr.eval_subst]; rfl

theorem walkOut_309_eval' (env : Env K) :
    (Trans.walkOut.subst finalWalkTerminalSubst309).eval env = env.trace 306 := by
  rw [Expr.eval_subst]; rfl

theorem walkLn1_eval' (env : Env K) :
    (Trans.walkLn1.subst finalWalkInitialSubst).eval env =
      (finalWalkLine .traceCur).eval env - (walkChallenge 0).eval env := by
  rw [Expr.eval_subst]; rfl

end Unfold

/-! ## 4. The transition: the three walk sources at the honest BFS walk -/

section Transition

/-- **The three walk-transition sources vanish at a nonterminal row** (the A-free copy of
`exact_finalWalk_transition_sources` + `walk_steps_eq`, on `W0`/`W1`): `ln` is `α·ln`, the count steps by
`α^{fanout}`, the accumulator by the declared child sum. -/
theorem walk_transition_sources {S : Env L} {i : ℕ} (hi : i + 1 < D.W.length)
    (R : NextReads D S (i + 1))
    (hc0 : S.trace 303 = D.cnt (i + 1)) (hc1 : S.traceNext 303 = D.cnt (i + 1 + 1))
    (ha0 : S.trace 306 = D.acc (i + 1)) (ha1 : S.traceNext 306 = D.acc (i + 1 + 1))
    (hl0 : (finalWalkLine .traceCur).eval S = D.ln (i + 1))
    (hl1 : (finalWalkLine .traceNext).eval S = D.ln (i + 1 + 1)) :
    (Trans.walkLnStep.subst finalWalkSubstInGate).eval S = 0 ∧
      walkCountStep309.eval S = 0 ∧ walkAccStep309.eval S = 0 := by
  have hlen : (Walk.bfsForest [D.root]).length = D.W.length := rfl
  have h1 : 1 ≤ i + 1 := by omega
  have h2 : i + 1 < (Walk.bfsForest [D.root]).length := hi
  have hfo := D.fo_eq (i + 1) hi
  refine ⟨?_, ?_, ?_⟩
  · rw [walkLnStep_eval', hl0, hl1, R.alpha, sub_eq_zero]
    exact D.sat.lnInc (i + 1) h1 h2
  · rw [walkCountStep309_eval', hc0, hc1, R.cm, sub_eq_zero]
    have := D.sat.countInc (i + 1) h1 h2
    rw [this]
    exact congrArg (fun e => D.cnt (i + 1) * D.α ^ e) hfo
  · rw [walkAccStep309_eval', hl1, R.label, ha0, ha1, hc0, R.cc, ← D.cur_eq (i + 1) hi]
    have hacc := D.sat.accStep (i + 1) h1 h2
    have hfo2 : Walk.foCol D.W (i + 1 + 1) = fanoutComp (D.pubAt (i + 1)).state := hfo
    have hsum : D.cnt (i + 1) * (∑ l ∈ Finset.Icc 1 (fanoutComp (D.pubAt (i + 1)).state), D.α ^ l *
        Walk.rlc D.γ (childVecN (D.pubAt (i + 1)) (fun k => childStateTagCol D.W (i + 1 + 1) k) (l - 1))) =
        ∑ l ∈ Finset.Icc 1 (Walk.foCol D.W (i + 1 + 1)), D.α ^ l * D.cnt (i + 1) *
          Walk.chldCol D.nodeVal D.W (i + 1 + 1) l := by
      rw [hfo2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Finset.mem_Icc] at hl
      rw [D.chld_eq (i + 1) hi l hl.1 hl.2]
      ring
    rw [hsum]
    exact sub_eq_zero.mpr hacc


end Transition

/-! ## 5. The boundary rows: first row (`count(1)`, `ln(1)`, `acc(1)`), last row (`out_walk`, tiling) -/

section Boundary
variable {S : Env L}

theorem HonestWalk.hpos : 1 ≤ D.W.length := D.sat.hpos

/-- `ln(1) = α` at the first row. -/
theorem walk_ln1_source (R : FirstReads D S) (hl0 : (finalWalkLine .traceCur).eval S = D.ln 1) :
    (Trans.walkLn1.subst finalWalkInitialSubst).eval S = 0 := by
  rw [walkLn1_eval', hl0, R.alpha, sub_eq_zero]
  exact D.sat.ln1

/-- `count(1) = initial_count · α^{fanout(1)}` on `W0`. -/
theorem walk_count1_source (R : FirstReads D S) (hc0 : S.trace 303 = D.cnt 1)
    (hp0 : S.pub 0 = D.α) :
    (Trans.walkCount1.subst finalWalkInitialSubst309).eval S = 0 := by
  rw [walkCount1_309_eval', hc0, hp0, R.cm, sub_eq_zero]
  have hfo : Walk.foCol D.W 1 = fanoutComp (D.pubAt 0).state := D.fo_eq 0 D.hpos
  have := D.sat.count1
  rw [this]
  exact congrArg (fun e => D.α * D.α ^ e) hfo

/-- The row-0 accumulator identity on `W1`. -/
theorem walk_accInit_source (R : FirstReads D S) (hl0 : (finalWalkLine .traceCur).eval S = D.ln 1)
    (ha0 : S.trace 306 = D.acc 1) (hp0 : S.pub 0 = D.α) (hp1 : S.pub 1 = D.seed) :
    (Trans.walkAccInit.subst finalWalkInitialSubst309).eval S = 0 := by
  rw [walkAccInit_309_eval', hl0, R.label, ha0, hp0, hp1, R.cc, ← D.cur_eq 0 D.hpos]
  have hfo : Walk.foCol D.W 1 = fanoutComp (D.pubAt 0).state := D.fo_eq 0 D.hpos
  have hacc : D.ln 1 * Walk.curCol D.nodeVal D.W 1 + D.acc 1 =
      (∑ l ∈ Finset.Icc 1 (Walk.foCol D.W 1), D.α ^ l * D.α * Walk.chldCol D.nodeVal D.W 1 l) +
        D.seed := D.sat.accInit
  have hsum : D.α * (∑ l ∈ Finset.Icc 1 (fanoutComp (D.pubAt 0).state), D.α ^ l *
        Walk.rlc D.γ (childVecN (D.pubAt 0) (fun k => childStateTagCol D.W 1 k) (l - 1))) =
      ∑ l ∈ Finset.Icc 1 (Walk.foCol D.W 1), D.α ^ l * D.α * Walk.chldCol D.nodeVal D.W 1 l := by
    rw [hfo, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_Icc] at hl
    rw [D.chld_eq 0 D.hpos l hl.1 hl.2]
    ring
  rw [hsum]
  exact sub_eq_zero.mpr hacc

/-- **`out_walk = acc(h) = 0`** (perfect completeness of the BFS walk): the accumulator at the last row. -/
theorem HonestWalk.acc_last : D.acc D.W.length = 0 := by
  have hseed : D.seed = Walk.curCol D.nodeVal D.W 1 * D.α := by
    rw [D.cur_eq 0 D.hpos]; exact D.seed_eq
  exact Walk.walk_completeness D.sat hseed rfl (Walk.bfs_isFullBFT D.root)

theorem walk_out_source (hl : S.trace 306 = D.acc D.W.length) :
    (Trans.walkOut.subst finalWalkTerminalSubst309).eval S = 0 := by
  rw [walkOut_309_eval', hl]; exact D.acc_last

/-- **Tiling**: `count(h) = ln(h)` at the last row. -/
theorem HonestWalk.cnt_last : D.cnt D.W.length = D.ln D.W.length := by
  have hc := Walk.count_closed D.sat D.W.length D.hpos le_rfl
  have hl := Walk.ln_closed D.sat D.W.length D.hpos le_rfl
  have ht' : 1 + Walk.Sf (Walk.foCol D.W) D.W.length = D.W.length :=
    Walk.foCol_Sf_tilingF [D.root] (List.cons_ne_nil _ _)
  change D.cnt D.W.length = D.α * D.α ^ Walk.Sf (Walk.foCol D.W) D.W.length at hc
  rw [hc, hl, ← pow_succ']
  exact congrArg (fun e => D.α ^ e) (by omega)

/-- **Queue non-emptiness** at a nonterminal walk index (`1 ≤ j < h`): `count(j) ≠ ln(j)`, given
`h ≤ orderOf α` (the order of the walk coin; the honest-bad condition, see the report). -/
theorem HonestWalk.cnt_ne_ln (hord : D.W.length ≤ orderOf D.α) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : j < D.W.length) : D.cnt j ≠ D.ln j := by
  have hv : Walk.BFSValidF 1 (Walk.foCol D.W) D.W.length :=
    Walk.foCol_BFSValidF [D.root] (List.cons_ne_nil _ _)
  have ht : 1 + Walk.Sf (Walk.foCol D.W) D.W.length = D.W.length :=
    Walk.foCol_Sf_tilingF [D.root] (List.cons_ne_nil _ _)
  have hneq := (Nock.RedTeam.Batch478.honest_ratio_gate (K := L) hv ht hord).1 j hj1 hj
  have hc := Walk.count_closed D.sat j hj1 hj.le
  have hl := Walk.ln_closed D.sat j hj1 hj.le
  change D.cnt j = D.α * D.α ^ Walk.Sf (Walk.foCol D.W) j at hc
  rw [hc, hl, ← pow_succ', Nat.add_comm]
  exact hneq

end Boundary

end Honest

/-! ## 6. The typed gates at `Env309` -/

section Gates
variable {F L : Type} [Field F] [Field L] [Algebra F L]

theorem src_ln_cur (env : Env309 F L) :
    (finalWalkLine .traceCur).eval env.toSourceEnv = env.base.extTrace 61 := by
  simp [finalWalkLine, finalWalkLineIndex, finalWalkLineRole, ext0, Expr.eval, Env309.toSourceEnv,
    CorrectedFinalTypedEnv.toSourceEnv]

theorem src_ln_next (env : Env309 F L) :
    (finalWalkLine .traceNext).eval env.toSourceEnv = env.base.extTraceNext 61 := by
  simp [finalWalkLine, finalWalkLineIndex, finalWalkLineRole, ext0, Expr.eval, Env309.toSourceEnv,
    CorrectedFinalTypedEnv.toSourceEnv]

theorem src_inv (env : Env309 F L) :
    (walkInv .traceCur).eval env.toSourceEnv = env.base.extTrace 62 := by
  simp [walkInv, walkInvIndex, walkInvRole, ext0, Expr.eval, Env309.toSourceEnv,
    CorrectedFinalTypedEnv.toSourceEnv]

theorem src_b12 (env : Env309 F L) :
    env.toSourceEnv.trace 12 = algebraMap F L (env.base.baseTrace 12) := by
  simp [Env309.toSourceEnv, CorrectedFinalTypedEnv.toSourceEnv]

theorem src_b11 (env : Env309 F L) :
    env.toSourceEnv.trace 11 = algebraMap F L (env.base.baseTrace 11) := by
  simp [Env309.toSourceEnv, CorrectedFinalTypedEnv.toSourceEnv]

theorem src_w0 (env : Env309 F L) : env.toSourceEnv.trace 303 = env.walk 0 := by
  simp [Env309.toSourceEnv]
theorem src_w1 (env : Env309 F L) : env.toSourceEnv.trace 306 = env.walk 1 := by
  simp [Env309.toSourceEnv]
theorem src_w0n (env : Env309 F L) : env.toSourceEnv.traceNext 303 = env.walkNext 0 := by
  simp [Env309.toSourceEnv]
theorem src_w1n (env : Env309 F L) : env.toSourceEnv.traceNext 306 = env.walkNext 1 := by
  simp [Env309.toSourceEnv]
theorem src_pub0 (env : Env309 F L) : env.toSourceEnv.pub 0 = env.base.extensionPublic 0 := by
  simp [Env309.toSourceEnv, CorrectedFinalTypedEnv.toSourceEnv]
theorem src_pub1 (env : Env309 F L) : env.toSourceEnv.pub 1 = env.base.extensionPublic 1 := by
  simp [Env309.toSourceEnv, CorrectedFinalTypedEnv.toSourceEnv]

theorem lowerW_eval' (env : Env309 F L) (e : Expr) (h : (lower309 e).isSome) :
    (lowerW e).eval env = e.eval env.toSourceEnv :=
  (lower309_eval env e _ (lower309_some e h)).symm

theorem gate73_eval (env : Env309 F L) :
    (correctedFinalExtGate packedWalkLnId).eval env.base =
      (Trans.walkLnStep.subst finalWalkSubstInGate).eval env.toSourceEnv := by
  have h73 : OptimizedComputeGateBasis.finalExtTransitionGates.get ⟨73, by decide⟩ =
      Trans.walkLnStep.subst finalWalkSubstInGate := by decide
  rw [← h73, eval_toSourceEnv309_of_noWalkVars env _
    (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
  exact (correctedFinalExtGate_eval_source env.base ⟨73, by decide⟩).symm

theorem residual0_eval (env : Env309 F L) :
    (residualSource309 0).eval env = walkCountStep309.eval env.toSourceEnv :=
  lowerW_eval' env _ lower309_total.1

theorem residual1_eval (env : Env309 F L) :
    (residualSource309 1).eval env = walkAccStep309.eval env.toSourceEnv :=
  lowerW_eval' env _ lower309_total.2.1

/-- `1 - b = 0` or the body vanishes: the `notLast` mask. -/
theorem mask_zero {x : L} (b : F) (h : b = 1 ∨ x = 0) :
    (1 - algebraMap F L b) * x = 0 := by
  rcases h with h | h
  · simp [h]
  · simp [h]

/-- **Core `73`** (`notLast · (ln' − α·ln)`). -/
theorem gate73 (env : Env309 F L)
    (h : env.base.baseTrace 12 = 1 ∨
      (Trans.walkLnStep.subst finalWalkSubstInGate).eval env.toSourceEnv = 0) :
    (specialTarget packedWalkLnId).eval env = 0 := by
  have : (specialTarget packedWalkLnId).eval env =
      (1 - algebraMap F L (env.base.baseTrace 12)) *
        (correctedFinalExtGate packedWalkLnId).eval env.base := by
    simp [specialTarget, WTyped.eval, maskT, CorrectedFinalTypedExpr.eval, packedWalkCountId,
      packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId, packedChainId, packedWalkLnId]
  rw [this, gate73_eval]
  exact mask_zero _ h

/-- **Core `74`** (`notLast · w_58`, with `w_58` the residual `walkCountStep309`). -/
theorem gate74 (env : Env309 F L) (h58 : env.base.extTrace 58 = (residualSource309 0).eval env)
    (h : env.base.baseTrace 12 = 1 ∨ walkCountStep309.eval env.toSourceEnv = 0) :
    (specialTarget ⟨74, by decide⟩).eval env = 0 := by
  have : (specialTarget ⟨74, by decide⟩).eval env =
      (1 - algebraMap F L (env.base.baseTrace 12)) * env.base.extTrace 58 := by
    simp [specialTarget, WTyped.eval, maskT, CorrectedFinalTypedExpr.eval, packedWalkCountId]
  rw [this, h58, residual0_eval]
  exact mask_zero _ h

/-- **Core `75`**. -/
theorem gate75 (env : Env309 F L) (h59 : env.base.extTrace 59 = (residualSource309 1).eval env)
    (h : env.base.baseTrace 12 = 1 ∨ walkAccStep309.eval env.toSourceEnv = 0) :
    (specialTarget ⟨75, by decide⟩).eval env = 0 := by
  have : (specialTarget ⟨75, by decide⟩).eval env =
      (1 - algebraMap F L (env.base.baseTrace 12)) * env.base.extTrace 59 := by
    simp [specialTarget, WTyped.eval, maskT, CorrectedFinalTypedExpr.eval, packedWalkCountId,
      packedWalkAccId]
  rw [this, h59, residual1_eval]
  exact mask_zero _ h

/-- **Core `76`** (queue non-empty): `notLast · (walk_inv · (W0 − ln) − 1)`. -/
theorem gate76 (env : Env309 F L)
    (h : env.base.baseTrace 12 = 1 ∨
      env.base.extTrace 62 * (env.walk 0 - env.base.extTrace 61) = 1) :
    (specialTarget ⟨76, by decide⟩).eval env = 0 := by
  have hs : specialTarget ⟨76, by decide⟩ = queueNonEmpty309 := by
    simp [specialTarget, packedWalkCountId, packedWalkAccId, packedQueueNonEmptyId]
  rw [hs, queueNonEmpty309, lowerW_eval' env _ lower309_total.2.2.1]
  simp only [walkQueueNonEmpty309, Expr.eval, walkCountCol, src_b12, src_inv, src_w0, src_ln_cur]
  rcases h with h | h
  · simp [h]
  · rw [h]; simp

/-- **Core `77`** (queue tiling): `isLast · (W0 − ln)`. -/
theorem gate77 (env : Env309 F L)
    (h : env.base.baseTrace 12 = 0 ∨ env.walk 0 = env.base.extTrace 61) :
    (specialTarget ⟨77, by decide⟩).eval env = 0 := by
  have hs : specialTarget ⟨77, by decide⟩ = queueTiling309 := by
    simp [specialTarget, packedWalkCountId, packedWalkAccId, packedQueueNonEmptyId,
      packedQueueTilingId]
  rw [hs, queueTiling309, lowerW_eval' env _ lower309_total.2.2.2.1]
  simp only [walkQueueTiling309, Expr.eval, walkCountCol, src_b12, src_w0, src_ln_cur]
  rcases h with h | h
  · simp [h]
  · rw [h]; simp

/-- **Aux `0`**: `w_58 − walkCountStep309`. -/
theorem aux0 (env : Env309 F L) (h58 : env.base.extTrace 58 = (residualSource309 0).eval env) :
    (auxTarget 0).eval env = 0 := by
  simp [auxTarget, aux309Idx, residualWitnessRole, WTyped.eval, CorrectedFinalTypedExpr.eval]
  exact sub_eq_zero.mpr h58

/-- **Aux `1`**: `w_59 − walkAccStep309`. -/
theorem aux1 (env : Env309 F L) (h59 : env.base.extTrace 59 = (residualSource309 1).eval env) :
    (auxTarget 1).eval env = 0 := by
  simp [auxTarget, aux309Idx, residualWitnessRole, WTyped.eval, CorrectedFinalTypedExpr.eval]
  exact sub_eq_zero.mpr h59

/-- **Endpoint `walkLn1`**: `isFirst · (ln − α)`. -/
theorem ep_ln1 (env : Env309 F L)
    (h : env.base.baseTrace 11 = 0 ∨
      (Trans.walkLn1.subst finalWalkInitialSubst).eval env.toSourceEnv = 0) :
    (lowerLeaf finalMaskedWalkLn1).eval env = 0 := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp lowerLeaf_total.1
  have h1 : (lowerLeaf finalMaskedWalkLn1).eval env = finalMaskedWalkLn1.eval env.base.toSourceEnv := by
    simp only [lowerLeaf, ht, Option.getD, WTyped.eval]
    exact (correctedLowerFinal_eval env.base _ _ ht).symm
  have hnw : noWalkVars (Trans.walkLn1.subst finalWalkInitialSubst) = true := by decide
  rw [h1]
  simp only [finalMaskedWalkLn1, finalOptimizedWalkLn1, Expr.eval, OptimizedComputeTemplate.fixedIsFirst]
  rw [← eval_toSourceEnv309_of_noWalkVars env _ hnw]
  have hb : env.base.toSourceEnv.trace 11 = algebraMap F L (env.base.baseTrace 11) := by
    simp [CorrectedFinalTypedEnv.toSourceEnv]
  rw [hb]
  rcases h with h | h
  · simp [h]
  · rw [h]; simp

/-- **Endpoint `walkCount1`**: `isFirst · (W0 − initial_count · cm(1))`. -/
theorem ep_count1 (env : Env309 F L)
    (h : env.base.baseTrace 11 = 0 ∨
      (Trans.walkCount1.subst finalWalkInitialSubst309).eval env.toSourceEnv = 0) :
    (lowerW finalMaskedWalkCount1_309).eval env = 0 := by
  rw [lowerW_eval' env _ lower309_total.2.2.2.2.1]
  simp only [finalMaskedWalkCount1_309, Expr.eval, OptimizedComputeTemplate.fixedIsFirst, src_b11]
  rcases h with h | h
  · simp [h]
  · rw [h]; simp

/-- **Endpoint `walkOut`**: `isLast · W1`. -/
theorem ep_out (env : Env309 F L)
    (h : env.base.baseTrace 12 = 0 ∨
      (Trans.walkOut.subst finalWalkTerminalSubst309).eval env.toSourceEnv = 0) :
    (lowerW finalMaskedWalkOut309).eval env = 0 := by
  rw [lowerW_eval' env _ lower309_total.2.2.2.2.2.1]
  simp only [finalMaskedWalkOut309, Expr.eval, OptimizedComputeTemplate.fixedIsLast, src_b12]
  rcases h with h | h
  · simp [h]
  · rw [h]; simp

/-- **Endpoint `walkAccInit` (degree four)**: `isFirst² · (ln·cur + W1 − (ic·cc + seed))`. -/
theorem ep4_accInit (env : Env309 F L)
    (h : env.base.baseTrace 11 = 0 ∨
      (Trans.walkAccInit.subst finalWalkInitialSubst309).eval env.toSourceEnv = 0) :
    (lowerW finalMaskedWalkAccInit309).eval env = 0 := by
  rw [lowerW_eval' env _ lower309_total.2.2.2.2.2.2]
  simp only [finalMaskedWalkAccInit309, Expr.eval, OptimizedComputeTemplate.fixedIsFirst, src_b11]
  rcases h with h | h
  · simp [h]
  · rw [h]; simp

end Gates

/-! ## 7. The row theorem: every walk gate of the tower chip at a BFS row -/

section Row
variable {F L : Type} [Field F] [Field L] [Algebra F L] {D : HonestWalk L}

/-- **The walk-row hypotheses** at BFS row `i` of an `Env309` (what the honest fill places): the walk columns
`W0 / W1` and the line / inverse roles carry the honest walk, the residual roles `58`/`59` carry their
sources (by definition of the honest fill), the base masks are `isFirst` / `isLast`, the walk coins and
the claim seed sit at the `𝕂′` publics `0`/`1`, and the label reads of `NextReads` / `FirstReads` hold
(restatements of (1)-(3) of DESIGN §(a)). -/
structure WalkRowEnv (D : HonestWalk L) (env : Env309 F L) (i : ℕ) : Prop where
  hi : i < D.W.length
  cnt : env.walk 0 = D.cnt (i + 1)
  acc : env.walk 1 = D.acc (i + 1)
  ln : env.base.extTrace 61 = D.ln (i + 1)
  inv : env.base.extTrace 62 = (D.cnt (i + 1) - D.ln (i + 1))⁻¹
  r58 : env.base.extTrace 58 = (residualSource309 0).eval env
  r59 : env.base.extTrace 59 = (residualSource309 1).eval env
  b11 : env.base.baseTrace 11 = if i = 0 then 1 else 0
  b12 : env.base.baseTrace 12 = if i + 1 = D.W.length then 1 else 0
  pub0 : env.base.extensionPublic 0 = D.α
  pub1 : env.base.extensionPublic 1 = D.seed
  nxt : i + 1 < D.W.length →
    env.walkNext 0 = D.cnt (i + 1 + 1) ∧ env.walkNext 1 = D.acc (i + 1 + 1) ∧
      env.base.extTraceNext 61 = D.ln (i + 1 + 1) ∧ NextReads D env.toSourceEnv (i + 1)
  fst : i = 0 → FirstReads D env.toSourceEnv

/-- The transition sources at a nonterminal row, from the row hypotheses. -/
theorem WalkRowEnv.transition {env : Env309 F L} {i : ℕ} (R : WalkRowEnv D env i)
    (hi : i + 1 < D.W.length) :
    (Trans.walkLnStep.subst finalWalkSubstInGate).eval env.toSourceEnv = 0 ∧
      walkCountStep309.eval env.toSourceEnv = 0 ∧ walkAccStep309.eval env.toSourceEnv = 0 := by
  obtain ⟨hn0, hn1, hnl, RN⟩ := R.nxt hi
  exact walk_transition_sources hi RN (by rw [src_w0, R.cnt]) (by rw [src_w0n, hn0])
    (by rw [src_w1, R.acc]) (by rw [src_w1n, hn1]) (by rw [src_ln_cur, R.ln])
    (by rw [src_ln_next, hnl])

/-- **The walk gates of the tower chip** (core `73..77`, aux `0`/`1`, ep2 `walkLn1`/`walkCount1`/`walkOut`,
ep4 `walkAccInit`) all vanish in `𝕂′` at the walk-language environment `env`. -/
def WalkGatesHold (env : Env309 F L) : Prop :=
  (specialTarget packedWalkLnId).eval env = 0 ∧
    (specialTarget ⟨74, by decide⟩).eval env = 0 ∧
    (specialTarget ⟨75, by decide⟩).eval env = 0 ∧
    (specialTarget ⟨76, by decide⟩).eval env = 0 ∧
    (specialTarget ⟨77, by decide⟩).eval env = 0 ∧
    (auxTarget 0).eval env = 0 ∧ (auxTarget 1).eval env = 0 ∧
    (lowerLeaf finalMaskedWalkLn1).eval env = 0 ∧
    (lowerW finalMaskedWalkCount1_309).eval env = 0 ∧
    (lowerW finalMaskedWalkOut309).eval env = 0 ∧
    (lowerW finalMaskedWalkAccInit309).eval env = 0

/-- **Headline (C2b).**  At BFS row `i`, given the row hypotheses and `count ≠ ln` at the nonterminal
walk index (core `76`; `walk_row_holds_of_order` derives it from `h ≤ orderOf α`), every walk gate of the
tower chip holds in `𝕂′`. -/
theorem walk_row_holds {env : Env309 F L} {i : ℕ} (R : WalkRowEnv D env i)
    (hne : i + 1 < D.W.length → D.cnt (i + 1) ≠ D.ln (i + 1)) : WalkGatesHold env := by
  unfold WalkGatesHold
  have hb12 := R.b12
  have hb11 := R.b11
  have hn := R.hi
  -- the first / last row dichotomies
  have hfirst : env.base.baseTrace 11 = 0 ∨ i = 0 := by
    by_cases h0 : i = 0
    · exact Or.inr h0
    · exact Or.inl (by rw [hb11, if_neg h0])
  have hlastcase : env.base.baseTrace 12 = 0 ∨ i + 1 = D.W.length := by
    by_cases hl : i + 1 = D.W.length
    · exact Or.inr hl
    · exact Or.inl (by rw [hb12, if_neg hl])
  refine ⟨?_, ?_, ?_, ?_, ?_, aux0 env R.r58, aux1 env R.r59, ?_, ?_, ?_, ?_⟩
  · -- 73
    by_cases hl : i + 1 = D.W.length
    · exact gate73 env (Or.inl (by rw [hb12, if_pos hl]))
    · exact gate73 env (Or.inr (R.transition (by omega)).1)
  · by_cases hl : i + 1 = D.W.length
    · exact gate74 env R.r58 (Or.inl (by rw [hb12, if_pos hl]))
    · exact gate74 env R.r58 (Or.inr (R.transition (by omega)).2.1)
  · by_cases hl : i + 1 = D.W.length
    · exact gate75 env R.r59 (Or.inl (by rw [hb12, if_pos hl]))
    · exact gate75 env R.r59 (Or.inr (R.transition (by omega)).2.2)
  · by_cases hl : i + 1 = D.W.length
    · exact gate76 env (Or.inl (by rw [hb12, if_pos hl]))
    · refine gate76 env (Or.inr ?_)
      rw [R.inv, R.cnt, R.ln]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne (by omega)))
  · by_cases hl : i + 1 = D.W.length
    · refine gate77 env (Or.inr ?_)
      rw [R.cnt, R.ln, hl]
      exact D.cnt_last
    · exact gate77 env (Or.inl (by rw [hb12, if_neg hl]))
  · -- ep ln1
    rcases hfirst with h | h
    · exact ep_ln1 env (Or.inl h)
    · subst h
      refine ep_ln1 env (Or.inr ?_)
      exact walk_ln1_source (R.fst rfl) (by rw [src_ln_cur, R.ln])
  · rcases hfirst with h | h
    · exact ep_count1 env (Or.inl h)
    · subst h
      refine ep_count1 env (Or.inr ?_)
      exact walk_count1_source (R.fst rfl) (by rw [src_w0, R.cnt]) (by rw [src_pub0, R.pub0])
  · rcases hlastcase with h | h
    · exact ep_out env (Or.inl h)
    · refine ep_out env (Or.inr ?_)
      exact walk_out_source (by rw [src_w1, R.acc, h])
  · rcases hfirst with h | h
    · exact ep4_accInit env (Or.inl h)
    · subst h
      refine ep4_accInit env (Or.inr ?_)
      exact walk_accInit_source (R.fst rfl) (by rw [src_ln_cur, R.ln]) (by rw [src_w1, R.acc])
        (by rw [src_pub0, R.pub0]) (by rw [src_pub1, R.pub1])

/-- **Headline with the coin condition**: `h ≤ orderOf α` (the honest-bad event on the walk coin) gives
`count ≠ ln` at every nonterminal walk index, hence every walk gate. -/
theorem walk_row_holds_of_order {env : Env309 F L} {i : ℕ} (R : WalkRowEnv D env i)
    (hord : D.W.length ≤ orderOf D.α) : WalkGatesHold env :=
  walk_row_holds R (fun hi => D.cnt_ne_ln hord (i + 1) (by omega) hi)

end Row

/-! ## 8. Existence of the honest walk, the seed, and the negative controls -/

section Exist
variable {L : Type} [Field L]

/-- The BFS row list of any tree is nonempty. -/
theorem bfsForest_length_pos (root : Walk.NTree (State × DTcomp L)) :
    1 ≤ (Walk.bfsForest [root]).length := by
  rw [Walk.walk_tail_eq root]; simp

/-- **The honest BFS walk exists at every `(α, γ)`** (no condition on the coins): from the label
obligations (`WalkLabelObligations`, restated per BFS row) and the root seed `RLC^γ(root)·α`, the
walk columns `ln / count / acc` exist (closed forms of `Walk.walkSat_exists`). -/
theorem honestWalk_exists (root : Walk.NTree (State × DTcomp L)) (α γ seed : L)
    (pubAt : ℕ → Pub L)
    (hpub : ∀ i (hi : i < (Walk.bfsForest [root]).length),
      ((Walk.bfsForest [root])[i]).label.2.2.1 = pubAt i)
    (htopo : ∀ t ∈ Walk.bfsForest [root],
      t.label.1 = t.label.2.2.1.state ∧ fanoutComp t.label.1 = t.children.length ∧
        childLinkComp t.label (fun j => t.childLabel j))
    (hseed : seed = Walk.rlc γ (labelVecOfPub (pubAt 0)) * α) :
    ∃ D : HonestWalk L, D.root = root ∧ D.α = α ∧ D.γ = γ ∧ D.seed = seed := by
  obtain ⟨ln, cnt, acc, hsat⟩ := Walk.walkSat_exists
    (Walk.curCol (fun t : Walk.NTree (State × DTcomp L) => Walk.rlc γ (labelVecOfPub t.label.2.2.1))
      (Walk.bfsForest [root]))
    (Walk.chldCol (fun t : Walk.NTree (State × DTcomp L) => Walk.rlc γ (labelVecOfPub t.label.2.2.1))
      (Walk.bfsForest [root]))
    (Walk.foCol (Walk.bfsForest [root])) α seed α (bfsForest_length_pos root)
  exact ⟨HonestWalk.mk root (fun t => Walk.rlc γ (labelVecOfPub t.label.2.2.1)) α γ seed ln cnt acc
    pubAt (fun _ => rfl) htopo hpub hsat hseed, rfl, rfl, rfl, rfl⟩

/-- The seed of the walk is the claim seed once the root row carries the claim's label
(`BindsAt.root_bindings` at `z`): `seed = RLC^γ(claim label)·α`. -/
theorem seed_eq_of_claim (z : L) (claim : P8PublicClaim) (pub0 : Pub L) (γ α seed : L)
    (hroot : labelVecOfPub pub0 = ComputeWalkSeed.claimLabelVec z claim)
    (hseed : seed = Walk.rlc γ (ComputeWalkSeed.claimLabelVec z claim) * α) :
    seed = Walk.rlc γ (labelVecOfPub pub0) * α := by
  rw [hroot]; exact hseed

/-- **Negative control (count column)**: perturbing the successor's `W0` by `ε` makes the count source
equal to `ε` (so the gate discriminates; it is not vacuous). -/
theorem count_step_perturb {D : HonestWalk L} {S : Env L} {i : ℕ} (hi : i + 1 < D.W.length)
    (R : NextReads D S (i + 1)) (ε : L)
    (hc0 : S.trace 303 = D.cnt (i + 1)) (hc1 : S.traceNext 303 = D.cnt (i + 1 + 1) + ε) :
    walkCountStep309.eval S = ε := by
  rw [walkCountStep309_eval', hc0, hc1, R.cm]
  have := D.sat.countInc (i + 1) (by omega) hi
  have hfo : Walk.foCol D.W (i + 1 + 1) = fanoutComp (D.pubAt (i + 1)).state := D.fo_eq (i + 1) hi
  rw [this]
  have : D.α ^ Walk.foCol D.W (i + 1 + 1) = D.α ^ fanoutComp (D.pubAt (i + 1)).state :=
    congrArg (fun e => D.α ^ e) hfo
  change D.cnt (i + 1) * D.α ^ Walk.foCol D.W (i + 1 + 1) + ε - D.cnt (i + 1) * _ = ε
  rw [this]; ring

end Exist

section NC
variable {F L : Type} [Field F] [Field L] [Algebra F L]

/-- **Negative control (queue witness)**: on a nonterminal row with `W0 = ln` (the case `count ≠ ln`
excludes) core `76` equals `-1`, whatever the inverse role carries. -/
theorem gate76_eq_neg_one (env : Env309 F L) (h12 : env.base.baseTrace 12 = 0)
    (h : env.walk 0 = env.base.extTrace 61) :
    (specialTarget ⟨76, by decide⟩).eval env = -1 := by
  have hs : specialTarget ⟨76, by decide⟩ = queueNonEmpty309 := by
    simp [specialTarget, packedWalkCountId, packedWalkAccId, packedQueueNonEmptyId]
  rw [hs, queueNonEmpty309, lowerW_eval' env _ lower309_total.2.2.1]
  simp only [walkQueueNonEmpty309, Expr.eval, walkCountCol, src_b12, src_inv, src_w0, src_ln_cur, h12,
    h]
  simp

/-- **Negative control (`out_walk`)**: at the last row the terminal endpoint equals `W1`. -/
theorem ep_out_eq (env : Env309 F L) (h12 : env.base.baseTrace 12 = 1) :
    (lowerW finalMaskedWalkOut309).eval env = env.walk 1 := by
  rw [lowerW_eval' env _ lower309_total.2.2.2.2.2.1]
  simp only [finalMaskedWalkOut309, Expr.eval, OptimizedComputeTemplate.fixedIsLast, src_b12, h12]
  rw [walkOut_309_eval', src_w1]; simp

end NC

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
