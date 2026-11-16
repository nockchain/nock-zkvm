import Nock.NockVMROM.Thm54.VclL.Compute.RowAxQ7
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch490Thm54TopologyAssembly

/-!
# V4T5 : the VCL compute topology — walk ⇒ `RVT Fcomp` at the patched row labels

.

* **§1 the patched decode agrees with the unpatched decode on every `Pub` fingerprint**
  (`lnPatch_pub_sfe`): the source columns `11..46` (`s, f, e, sf1..sf3`) never read the patched
  coordinates (roles 54/55 = source 67/68, challenges 0/9 and the `λ`-power block) —
  `okLn (computeTraceSubst.traceCur i)` is decided for every `i < 47`.  Hence `labelVecOfPub`,
  `childVecN` and `sfTriple` agree (`labelVec_lnPatch`, `childVecN_lnPatch`).
* **§2 the generic walk ⇒ topology lemma** (`rvt_of_walk`, chip-free): a `WalkSat` at
  `seed = root·α`, `initial_count = α`, at the RLC images of a 1-indexed label table, with
  `out = 0`, outside the `α`-root event `alphaBadOf (rootDiffP …)` and the prefix `γ`-event
  `prefixBadGammas`, with queue validity, the tiling and the per-row `state` / `Vcomp`, gives
  `RVT Fcomp (reconTree fo lbl N)` and the arity (`Batch490.execOfTraces_compute_rvt` /
  `_arity`, package-free).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TopoQ7

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Reified Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.RedTeam.Batch471

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The patched decode on the `Pub` fingerprints -/

/-- An expression reads no patched coordinate (source trace `67`/`68`, challenges `0`/`9`, the
`λ`-power block `100..163`) and no next-row column. -/
def okLn : Expr → Bool
  | .Var .traceCur i => i != 67 && i != 68
  | .Var .traceNext _ => false
  | .Var .challenge i => i != 0 && i != 9 && !(100 ≤ i && i < 164)
  | .Var .publicVal _ => true
  | .Const _ => true
  | .Add a b => okLn a && okLn b
  | .Sub a b => okLn a && okLn b
  | .Mul a b => okLn a && okLn b
  | .Neg a => okLn a
  | .Pow a _ => okLn a

section bridge
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem eval_lnPatch_of_okLn (env : CorrectedFinalTypedEnv F K) :
    ∀ e : Expr, okLn e = true → e.eval (lnPatch env).toSourceEnv = e.eval env.toSourceEnv
  | .Var .traceCur i, h => by
      simp only [okLn, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact lnPatch_source_trace env i h.1 h.2
  | .Var .traceNext _, h => by simp [okLn] at h
  | .Var .challenge i, h => by
      simp only [okLn, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
      refine lnPatch_source_chal env i h.1.1 h.1.2 ?_
      intro ⟨h1, h2⟩; have h' := h.2; simp [h1, h2] at h'
  | .Var .publicVal _, _ => rfl
  | .Const _, _ => rfl
  | .Add a b, h => by
      simp only [okLn, Bool.and_eq_true] at h
      simp only [Expr.eval, eval_lnPatch_of_okLn env a h.1, eval_lnPatch_of_okLn env b h.2]
  | .Sub a b, h => by
      simp only [okLn, Bool.and_eq_true] at h
      simp only [Expr.eval, eval_lnPatch_of_okLn env a h.1, eval_lnPatch_of_okLn env b h.2]
  | .Mul a b, h => by
      simp only [okLn, Bool.and_eq_true] at h
      simp only [Expr.eval, eval_lnPatch_of_okLn env a h.1, eval_lnPatch_of_okLn env b h.2]
  | .Neg a, h => by
      simp only [okLn] at h
      simp only [Expr.eval, eval_lnPatch_of_okLn env a h]
  | .Pow a _, h => by
      simp only [okLn] at h
      simp only [Expr.eval, eval_lnPatch_of_okLn env a h]

/-- The instrument: every source `Pub` fingerprint column below `47` reads no patched coordinate. -/
theorem okLn_pub_cols : ∀ i < 47, okLn (computeTraceSubst .traceCur i) = true := by
  decide +kernel

theorem lnPatch_source_lt47 (env : CorrectedFinalTypedEnv F K) (i : ℕ) (hi : i < 47) :
    (decodeSource (lnPatch env)).trace i = (decodeSource env).trace i := by
  simp only [decodeSource, Env.ofSubst, computeSubst]
  exact eval_lnPatch_of_okLn env _ (okLn_pub_cols i hi)

theorem fpOf_lnPatch_lt47 (env : CorrectedFinalTypedEnv F K) (j : ℕ) (hj : j + 2 < 47) :
    fpOf (decodeSource (lnPatch env)) j = fpOf (decodeSource env) j := by
  simp only [fpOf]
  rw [lnPatch_source_lt47 env j (by omega), lnPatch_source_lt47 env (j + 1) (by omega),
    lnPatch_source_lt47 env (j + 2) (by omega)]

/-- **The patched `Pub` has the row's state and `(s, f, e, sf1..sf3)` fingerprints.** -/
theorem lnPatch_pub_sfe (env : CorrectedFinalTypedEnv F K) (st : State) :
    let p := decodePub (lnPatch env) st
    let q := decodePub env st
    p.state = q.state ∧ p.s = q.s ∧ p.f = q.f ∧ p.e = q.e ∧ p.sf1_s = q.sf1_s ∧ p.sf1_f = q.sf1_f ∧
      p.sf1_e = q.sf1_e ∧ p.sf2_s = q.sf2_s ∧ p.sf2_f = q.sf2_f ∧ p.sf2_e = q.sf2_e ∧
      p.sf3_s = q.sf3_s ∧ p.sf3_f = q.sf3_f ∧ p.sf3_e = q.sf3_e := by
  intro p q
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact fpOf_lnPatch_lt47 env _ (by norm_num)

theorem labelVec_lnPatch (env : CorrectedFinalTypedEnv F K) (st : State) :
    labelVecOfPub (decodePub (lnPatch env) st) = labelVecOfPub (decodePub env st) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := lnPatch_pub_sfe env st
  funext k
  fin_cases k <;> simp [labelVecOfPub, h0, h1, h2, h3]

theorem childVecN_lnPatch (env : CorrectedFinalTypedEnv F K) (st : State) (tags : Fin 3 → K)
    (l : ℕ) : childVecN (decodePub (lnPatch env) st) tags l = childVecN (decodePub env st) tags l := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := lnPatch_pub_sfe env st
  have hsf : ∀ j : Fin 3, sfTriple (decodePub (lnPatch env) st) j = sfTriple (decodePub env st) j := by
    intro j
    fin_cases j <;> simp only [sfTriple] <;> simp_all
  have hc : ∀ j : Fin 3, childVec (decodePub (lnPatch env) st) tags j =
      childVec (decodePub env st) tags j := by
    intro j; funext k; fin_cases k <;> simp [childVec, hsf]
  rcases l with _ | _ | _ | l <;> simp only [childVecN, hc]

end bridge

/-! ## 2. The generic walk ⇒ topology lemma -/

section generic
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- **Walk ⇒ `RVT Fcomp`**, chip-free (`Batch490.execOfTraces_compute_rvt` without a package). -/
theorem rvt_of_walk (lbl : ℕ → State × DTcomp K) (tags : ℕ → Fin 3 → K)
    {ln count acc : ℕ → K} {α γ root : K} {N : ℕ}
    (hw : WalkSat (fun i => Walk.rlc γ (labelVecOfPub (lbl i).2.2.1))
      (fun i l => Walk.rlc γ (childVecN (lbl i).2.2.1 (tags i) (l - 1)))
      (fun i => fanoutComp (lbl i).1) ln count acc α (root * α) α N)
    (hout : acc N = 0)
    (hα : α ∉ alphaBadOf (rootDiffP (fun i => Walk.rlc γ (labelVecOfPub (lbl i).2.2.1))
      (fun i l => Walk.rlc γ (childVecN (lbl i).2.2.1 (tags i) (l - 1)))
      (fun i => fanoutComp (lbl i).1) root N))
    (hγ : γ ∉ prefixBadGammas (fun i => labelVecOfPub (lbl i).2.2.1)
      (fun i l => childVecN (lbl i).2.2.1 (tags i) (l - 1)) (fun i => fanoutComp (lbl i).1) N)
    (hv : BFSValid (fun i => fanoutComp (lbl i).1) N)
    (htile : Sf (fun i => fanoutComp (lbl i).1) N + 1 = N)
    (hrow : ∀ i, 1 ≤ i → i ≤ N →
      (lbl i).2.2.1.state = (lbl i).1 ∧ Vcomp (lbl i).2.1 (lbl i).2.2.1 (lbl i).2.2.2) :
    RVT (Fcomp (K := K)) (reconTree (fun i => fanoutComp (lbl i).1) lbl N) := by
  set fo : ℕ → ℕ := fun i => fanoutComp (lbl i).1 with hfo
  set V : ℕ → Fin 10 → K := fun i => labelVecOfPub (lbl i).2.2.1
  set Cv : ℕ → ℕ → Fin 10 → K := fun i l => childVecN (lbl i).2.2.1 (tags i) (l - 1)
  have hcur1 := cur_one_eq_root_of_walkSat hw hout hα
  have hseed : root * α = Walk.rlc γ (V 1) * α := by rw [← hcur1]
  rw [hseed] at hw
  have hαP : α ∉ walkPrefixAlphaEvent (fun i => Walk.rlc γ (V i)) (fun i l => Walk.rlc γ (Cv i l)) fo N := by
    rw [Nock.RedTeam.Batch490.walkPrefixAlphaEvent_eq_alphaBadOf hcur1]; exact hα
  have hh : 1 ≤ N := hw.hpos
  have hbft : VecBFT V Cv fo N := by
    rcases isFullBFT_or_mem_alphaEvent hw rfl rfl hout with hb | hmem
    · have hpre := prefixBFT_of_isFullBFT V Cv fo hh hγ hb
      have hlen : prefixLen fo N = N := prefixLen_eq_of_bfsValid _ hv
      obtain ⟨_, hcase⟩ := hpre
      rw [hlen] at hcase
      rcases hcase with ⟨_, hb'⟩ | ⟨_, hgt, _⟩
      · exact hb'
      · omega
    · exact absurd hmem hαP
  have hb' : VecBFT (fun i => encSFE (lbl i)) (fun i l => encSFE (clabOf lbl i l)) fo N := by
    have hproj := vecBFT_map sfeProj hbft
    refine vecBFT_congr_children (fun i l hl => ?_) hproj
    have hl3 : l < 3 := lt_of_lt_of_le hl ((comp_stateSep (K := K)).fanout_le _)
    show sfeProj (Cv i (l + 1)) = sfeProj (labelVecOfPub (childOfSlot (lbl i).2.2.1
      ⟨(l + 1 - 1) % 3, Nat.mod_lt _ (by norm_num)⟩))
    have hl' : l + 1 - 1 = l := by omega
    have hfin : (⟨(l + 1 - 1) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = ⟨l, hl3⟩ :=
      Fin.ext (by rw [hl']; exact Nat.mod_eq_of_lt hl3)
    rw [hfin, encSFE_clab (lbl i).2.2.1 (tags i) ⟨l, hl3⟩]
    congr 1
    show childVecN _ _ (l + 1 - 1) = _
    rw [hl']
    exact childVecN_fin (lbl i).2.2.1 (tags i) ⟨l, hl3⟩
  have harity : ∀ i, fo i ≤ 3 := fun i => (comp_stateSep (K := K)).fanout_le _
  refine VecBFT_reconstruct_of_label (comp_stateSep (K := K)) sfeOf respects_sfe encSFE encSFE_label
    lbl (clabOf lbl) fo htile hv harity (fun i _ _ => rfl) (fun i hi1 hih => ?_) hb'
  obtain ⟨hst, hV⟩ := hrow i hi1 hih
  refine ⟨hst, hV, ?_, ?_⟩
  · intro j
    simp only [hfo]
    constructor
    · intro hj; simp [hj]
    · intro hne; by_contra hj; simp [hj] at hne
  · intro j hj
    simp only [hfo]
    rw [if_pos hj]
    simp only [Option.map_some, clabOf, childOfSlot]
    have hm : ((j : ℕ) + 1 - 1) % 3 = j := by
      rw [show (j : ℕ) + 1 - 1 = (j : ℕ) by omega]; exact Nat.mod_eq_of_lt j.isLt
    have hfin : (⟨((j : ℕ) + 1 - 1) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = j := Fin.ext hm
    rw [hfin]

/-- **The arity of the reconstructed tree** (`Batch490.execOfTraces_compute_arity`, chip-free). -/
theorem children_length_of_rvt (lbl : ℕ → State × DTcomp K) {N : ℕ}
    (hv : BFSValid (fun i => fanoutComp (lbl i).1) N)
    (htile : Sf (fun i => fanoutComp (lbl i).1) N + 1 = N)
    (hrvt : RVT (Fcomp (K := K)) (reconTree (fun i => fanoutComp (lbl i).1) lbl N)) :
    ∀ s, InTree (reconTree (fun i => fanoutComp (lbl i).1) lbl N) s → s.children.length ≤ 3 := by
  have harity : ∀ i, fanoutComp (lbl i).1 ≤ 3 := fun i => (comp_stateSep (K := K)).fanout_le _
  have hbind := reconTree_bindings (comp_stateSep (K := K)) _ lbl N htile hv harity hrvt
  intro s hs
  have hs' : s ∈ bfsForest [reconTree (fun i => fanoutComp (lbl i).1) lbl N] :=
    (mem_bfsForest _ s).mpr ⟨_, List.mem_singleton.mpr rfl, hs⟩
  exact (hbind.1 s hs').symm.trans_le ((comp_stateSep (K := K)).fanout_le _)

end generic

/-! ## 3. The instance at the Q7 chip: the patched row labels -/

section chip
open Nock.NockVMROM.Thm54.SVCompute
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.SVWalk
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputePaperPacking (oneHot_ofSubst)

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {h : ℕ}
variable (D : ChipDataG F K h) (chalV pubVal : ℕ → F) {w : ℕ} (Q : Fin w → F[X])
  (hadj : D.Adjacent) (RF : RowFactsQ7 D chalV pubVal Q)
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)

/-- **The patched row label** at walk index `i` (1-indexed, row `rowOfG i`). -/
def lblQ (i : ℕ) : State × DTcomp K :=
  rowLabel (lnPatch (BV D chalV pubVal Q (rowOfG D i)))

include RF hchar in
/-- The patched label's state is the one-hot state of the row. -/
theorem lblQ_fst (i : ℕ) : (lblQ D chalV pubVal Q i).1 = stAt D chalV pubVal Q RF hchar (rowOfG D i) :=
  WrapFixesVcomp.computeStateOf_of_oneHot
    (oneHot_ofSubst _ _ (oneHot_lnPatch _ _ (stAt_spec D chalV pubVal Q RF hchar (rowOfG D i))))

include RF hchar in
theorem lblQ_pub (i : ℕ) : (lblQ D chalV pubVal Q i).2.2.1 =
    decodePub (lnPatch (BV D chalV pubVal Q (rowOfG D i))) (stAt D chalV pubVal Q RF hchar (rowOfG D i)) := by
  have h1 := lblQ_fst D chalV pubVal Q RF hchar i
  unfold lblQ rowLabel at h1 ⊢
  simp only at h1 ⊢
  rw [h1]

include RF hchar in
theorem curW_eq_lblQ (i : ℕ) : curW D chalV pubVal Q RF hchar i =
    Walk.rlc (gammaQ D chalV) (labelVecOfPub (lblQ D chalV pubVal Q i).2.2.1) := by
  rw [curW, lblQ_pub D chalV pubVal Q RF hchar, labelVec_lnPatch]; rfl

include RF hchar in
theorem chldW_eq_lblQ (i l : ℕ) : chldW D chalV pubVal Q RF hchar i l =
    Walk.rlc (gammaQ D chalV)
      (childVecN (lblQ D chalV pubVal Q i).2.2.1 (tagsAt D chalV pubVal Q RF hchar (rowOfG D i)) (l - 1)) := by
  rw [chldW, lblQ_pub D chalV pubVal Q RF hchar, childVecN_lnPatch]; rfl

include RF hchar in
theorem foW_eq_lblQ : foW D chalV pubVal Q RF hchar = fun i => fanoutComp (lblQ D chalV pubVal Q i).1 := by
  funext i; rw [foW, lblQ_fst D chalV pubVal Q RF hchar]

include RF hchar in
/-- **`state` and `V_comp` at every patched row label** (`WalkQ7.vcomp_at`). -/
theorem lblQ_row (hz : zQ D chalV ≠ 0) (hzi : D.G.chalSlot chalV 5 = (zQ D chalV)⁻¹) (i : ℕ) :
    (lblQ D chalV pubVal Q i).2.2.1.state = (lblQ D chalV pubVal Q i).1 ∧
      Vcomp (lblQ D chalV pubVal Q i).2.1 (lblQ D chalV pubVal Q i).2.2.1 (lblQ D chalV pubVal Q i).2.2.2 := by
  refine ⟨by unfold lblQ rowLabel; rfl, ?_⟩
  obtain ⟨st, hst, hV⟩ := vcomp_at D chalV pubVal Q RF hchar hz hzi (rowOfG D i)
  have hst' : (lblQ D chalV pubVal Q i).1 = st :=
    WrapFixesVcomp.computeStateOf_of_oneHot (oneHot_ofSubst _ _ hst)
  unfold lblQ rowLabel at hst' ⊢
  simp only at hst' ⊢
  rw [hst']
  exact hV

include hadj RF hchar in
/-- **The VCL compute topology at the Q7 chip**: given the frame's walk publics, outside the
`α`-root event (the one `q7_root_binds` reads), the prefix `γ`-event and the `α`-tiling event,
`RVT Fcomp` holds on the reconstruction over the patched row labels, with arity `≤ 3`. -/
theorem q7_topology {z : K} (hinit : initQ D pubVal = alphaQ D chalV)
    (hseed : seedQ D pubVal = Walk.rlc (gammaQ D chalV) (claimLabelVec z D.claim) * alphaQ D chalV)
    (hz : zQ D chalV ≠ 0) (hzi : D.G.chalSlot chalV 5 = (zQ D chalV)⁻¹)
    (hα : alphaQ D chalV ∉ alphaBadOf (rootDiffP (curW D chalV pubVal Q RF hchar)
      (chldW D chalV pubVal Q RF hchar) (foW D chalV pubVal Q RF hchar)
      (Walk.rlc (gammaQ D chalV) (claimLabelVec z D.claim)) D.N))
    (hγ : gammaQ D chalV ∉ prefixBadGammas
      (fun i => labelVecOfPub (pubAt D chalV pubVal Q RF hchar (rowOfG D i)))
      (fun i l => childVecN (pubAt D chalV pubVal Q RF hchar (rowOfG D i))
        (tagsAt D chalV pubVal Q RF hchar (rowOfG D i)) (l - 1))
      (foW D chalV pubVal Q RF hchar) D.N)
    (htα : ¬ (alphaQ D chalV ^ (1 + Sf (foW D chalV pubVal Q RF hchar) D.N) =
      alphaQ D chalV ^ D.N ∧ 1 + Sf (foW D chalV pubVal Q RF hchar) D.N ≠ D.N)) :
    RVT (Fcomp (K := K)) (reconTree (fun i => fanoutComp (lblQ D chalV pubVal Q i).1)
        (lblQ D chalV pubVal Q) D.N) ∧
      ∀ s, InTree (reconTree (fun i => fanoutComp (lblQ D chalV pubVal Q i).1)
        (lblQ D chalV pubVal Q) D.N) s → s.children.length ≤ 3 := by
  have hv := q7_bfsValid D chalV pubVal Q hadj RF hchar hinit
  have ht := q7_tiling D chalV pubVal Q hadj RF hchar hinit htα
  have hw := q7_walkSat D chalV pubVal Q hadj RF hchar
  have hout := q7_walk_out D chalV pubVal Q RF hchar
  have hcur : curW D chalV pubVal Q RF hchar = fun i =>
      Walk.rlc (gammaQ D chalV) (labelVecOfPub (lblQ D chalV pubVal Q i).2.2.1) :=
    funext (curW_eq_lblQ D chalV pubVal Q RF hchar)
  have hch : chldW D chalV pubVal Q RF hchar = fun i l => Walk.rlc (gammaQ D chalV)
      (childVecN (lblQ D chalV pubVal Q i).2.2.1 (tagsAt D chalV pubVal Q RF hchar (rowOfG D i)) (l - 1)) :=
    funext fun i => funext fun l => chldW_eq_lblQ D chalV pubVal Q RF hchar i l
  have hfo := foW_eq_lblQ D chalV pubVal Q RF hchar
  have hV : (fun i => labelVecOfPub (pubAt D chalV pubVal Q RF hchar (rowOfG D i))) =
      fun i => labelVecOfPub (lblQ D chalV pubVal Q i).2.2.1 := by
    funext i; rw [lblQ_pub D chalV pubVal Q RF hchar, labelVec_lnPatch]; rfl
  have hC : (fun i l => childVecN (pubAt D chalV pubVal Q RF hchar (rowOfG D i))
        (tagsAt D chalV pubVal Q RF hchar (rowOfG D i)) (l - 1)) =
      fun i l => childVecN (lblQ D chalV pubVal Q i).2.2.1
        (tagsAt D chalV pubVal Q RF hchar (rowOfG D i)) (l - 1) := by
    funext i l; rw [lblQ_pub D chalV pubVal Q RF hchar, childVecN_lnPatch]; rfl
  rw [hinit, hseed, hcur, hch, hfo] at hw
  rw [hcur, hch, hfo] at hα
  rw [hV, hC, hfo] at hγ
  rw [hfo] at hv ht
  have hrvt := rvt_of_walk (lblQ D chalV pubVal Q) (fun i => tagsAt D chalV pubVal Q RF hchar (rowOfG D i))
    hw hout hα hγ hv ht (fun i _ _ => lblQ_row D chalV pubVal Q RF hchar hz hzi i)
  exact ⟨hrvt, children_length_of_rvt _ hv ht hrvt⟩

end chip

end

end TopoQ7
end VclL.Compute
end Nock.NockVMROM.Thm54
