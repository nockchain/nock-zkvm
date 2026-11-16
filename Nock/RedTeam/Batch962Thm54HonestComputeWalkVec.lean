/-
  Nock/RedTeam/Batch962Thm54HonestComputeWalkVec.lean

  §A: at the canonical compute trace the source environment agrees with the exact current-row
  environment `exactFinalCurrentEnv` on every column below `71` (base cells are `finalBaseCell`,
  extension roles `< 58` are `formRLeafCore = coreExtensionValue`, `formRLeafCore_eq_core_all`),
  so the decoded row label is the exec row's `LT_comp` label (`rowLabelVec_honest`) and the
  declared child payload of every active slot is the child's label (`rowChildVec_honest`,
  through the package's own `WalkLabelObligations`, `childLinkComp`).

  §B: with `Batch960.forest_vec_identity` at the one-tree forest `[computeTree]`, the committed
  vectors satisfy `curValsV V N = V 1 :: flatBlksV Cv fo N`; so the prefix-γ event is EMPTY for
  every coin (component 8, every package), and the root walk polynomial vanishes identically
  (`IsFullBFT` at every γ); with the root label equal to the claim label at the honest seed
  (the `HonestFill` root equalities `hst`/`hs`/`hf`/`he`, `labelVecOfPub_eq_claimLabelVec`)
  the walk root event misses the honest tuple (component 5).

  Status: component 8 **proved** (honest-trace identity, every coin, every package);
  component 5 **proved** at every package from the `HonestFill` root equalities (no coin choice).
-/
import Nock.RedTeam.Batch960Thm54HonestMemoryForestVec
import Nock.RedTeam.Batch958Thm54HonestComputeTiling
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch962

open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.RedTeam.Batch960
open Nock.Framework
open Nock.Framework.Reify

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## A. The canonical source row against the exact current row -/

set_option maxRecDepth 4000 in
/-- The canonical compute source row agrees with the exact current-row environment below `71`. -/
theorem src_trace_exact (i : Fin P.optimized.family.problem.cfg.compRows) :
    ∀ j, j < 71 → (P.computeSourceEnv (canonicalComputeTrace P) i).trace j =
      (exactFinalCurrentEnv P.optimized.sampled i).toSourceEnv.trace j := by
  intro j hj
  have hbase := canonical_gather_base_current P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
    P.optimized.computePublic P.optimized.orbit i
  have hext := canonical_gather_ext_core P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
    P.optimized.computePublic P.optimized.orbit i
  change (CorrectedFinalTypedEnv.toSourceEnv (gatherCorrectedFinalTypedEnv P.optimized.basis
    (envOfTrace (correctedCanonicalFinalTrace P.optimized.sampled
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
      P.optimized.basis P.optimized.computeChallenge P.optimized.computePublic
      P.optimized.orbit) P.optimized.orbit.ω (P.optimized.computeNodes i)
      P.optimized.computeChallenge P.optimized.computePublic))).trace j = _
  by_cases h13 : j < 13
  · simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_pos h13, exactFinalCurrentEnv]
    rw [hbase ⟨j, h13⟩]
  · have h76 : j < 76 := Nat.lt_trans hj (by decide)
    have h58 : j - 13 < 58 := by omega
    simp only [CorrectedFinalTypedEnv.toSourceEnv, dif_neg h13, dif_pos h76,
      exactFinalCurrentEnv, exactFinalExtensionRow]
    rw [hext ⟨j - 13, h58⟩, formRLeafCore_eq_core_all]
    simp [h58]

theorem src_sel (i : Fin P.optimized.family.problem.cfg.compRows) (st : State) :
    (P.computeSourceEnv (canonicalComputeTrace P) i).trace (opCol st) =
      if st = (P.optimized.family.problem.exec.computePubAt i).state then 1 else 0 := by
  rw [src_trace_exact P i _ (by cases st <;> decide)]
  exact exactFinalCurrentEnv_selectors P.optimized.sampled i st

theorem src_sourcePubAtR (i : Fin P.optimized.family.problem.cfg.compRows) (r c : ℕ)
    (hr : r < 12) (hc : c < 3) :
    (ComputeWalkLabel.sourcePubAtR ComputeWalkLabel.curReader
        (P.optimized.family.problem.exec.computePubAt i).state r c).eval
        (P.computeSourceEnv (canonicalComputeTrace P) i) =
      OptimizedComputeCodec.fpCoordinate
        (OptimizedComputeCodec.pubFingerprint (P.optimized.family.problem.exec.computePubAt i)
          ⟨r, hr⟩) ⟨c, hc⟩ := by
  rw [ComputeWalkLabel.sourcePubAtR_cur_eval_congr (src_trace_exact P i) _ r c hr hc]
  exact exactFinalCurrentEnv_sourcePubAtR P.optimized.sampled P.optimized.computeObligations
    i r c hr hc

theorem src_tags (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3) :
    (ComputeWalkLabel.childTagHost ComputeWalkLabel.curReader
        (P.optimized.family.problem.exec.computePubAt i).state j).eval
        (P.computeSourceEnv (canonicalComputeTrace P) i) =
      ComputeTable.childStateTagCol P.optimized.family.computeWalkRows ((i : ℕ) + 1) j := by
  rw [ComputeWalkLabel.childTagHost_cur_eval_congr (src_trace_exact P i)]
  exact exactFinalCurrentEnv_childTagHost P.optimized.sampled i j

/-- The decoded fingerprint slot `r` of the canonical row is the exec row's. -/
theorem src_fp (i : Fin P.optimized.family.problem.cfg.compRows) (r : ℕ) (hr : r < 12) :
    fpOf (Env.ofSubst computeSubst
        (P.computeSourceEnv (canonicalComputeTrace P) i)) (11 + 3 * r) =
      OptimizedComputeCodec.pubFingerprint (P.optimized.family.problem.exec.computePubAt i)
        ⟨r, hr⟩ := by
  have hsel : ∀ st, (P.computeSourceEnv (canonicalComputeTrace P) i).trace (opCol st) =
      if st = (P.optimized.family.problem.exec.computePubAt i).state then 1 else 0 :=
    src_sel P i
  have hcoord : ∀ c (hc : c < 3),
      (Env.ofSubst computeSubst (P.computeSourceEnv (canonicalComputeTrace P) i)).trace
        (11 + 3 * r + c) =
      OptimizedComputeCodec.fpCoordinate
        (OptimizedComputeCodec.pubFingerprint (P.optimized.family.problem.exec.computePubAt i)
          ⟨r, hr⟩) ⟨c, hc⟩ := by
    intro c hc
    have hsub : computeTraceSubst .traceCur (11 + 3 * r + c) = semanticPub .traceCur r c := by
      have h1 : ¬ (11 + 3 * r + c < 11) := by omega
      have h2 : 11 + 3 * r + c < 47 := by omega
      have h3 : (11 + 3 * r + c - 11) / 3 = r := by omega
      have h4 : (11 + 3 * r + c - 11) % 3 = c := by omega
      simp only [computeTraceSubst, if_neg h1, if_pos h2, h3, h4]
    show (computeSubst .traceCur (11 + 3 * r + c)).eval _ = _
    rw [show computeSubst .traceCur (11 + 3 * r + c) =
        computeTraceSubst .traceCur (11 + 3 * r + c) from rfl, hsub,
      ← sourcePubAt_eval_eq_semanticPub _ _ hsel r c hr hc,
      ← ComputeWalkLabel.sourcePubAtR_cur]
    exact src_sourcePubAtR P i r c hr hc
  have h0 := hcoord 0 (by norm_num)
  have h1 := hcoord 1 (by norm_num)
  have h2 := hcoord 2 (by norm_num)
  unfold fpOf
  rw [show 11 + 3 * r + 1 = 11 + 3 * r + 1 from rfl, show 11 + 3 * r + 2 = 11 + 3 * r + 2 from rfl]
  rw [show (11 + 3 * r) = 11 + 3 * r + 0 from rfl, h0, h1, h2]
  rfl

/-- The decoded row public agrees with the exec row's on the state and all twelve
fingerprints. -/
theorem rowPub_honest (i : Fin P.optimized.family.problem.cfg.compRows) :
    (rowPub (P.computeSourceEnv (canonicalComputeTrace P) i)).state =
        (P.optimized.family.problem.exec.computePubAt i).state ∧
      ∀ (r : ℕ) (hr : r < 12),
        OptimizedComputeCodec.pubFingerprint (rowPub (P.computeSourceEnv (canonicalComputeTrace P) i))
            ⟨r, hr⟩ =
          OptimizedComputeCodec.pubFingerprint (P.optimized.family.problem.exec.computePubAt i)
            ⟨r, hr⟩ := by
  refine ⟨Batch958.src_rowState_honest P i, ?_⟩
  intro r hr
  rw [← src_fp P i r hr]
  interval_cases r <;> rfl

/-- **The decoded row label at the canonical compute trace is the exec row's `LT_comp` label.** -/
theorem rowLabelVec_honest (i : Fin P.optimized.family.problem.cfg.compRows) :
    rowLabelVec (P.computeSourceEnv (canonicalComputeTrace P) i) =
      labelVecOfPub (P.optimized.family.problem.exec.computePubAt i) := by
  obtain ⟨hst, hfp⟩ := rowPub_honest P i
  have e0 := hfp 0 (by norm_num)
  have e1 := hfp 1 (by norm_num)
  have e2 := hfp 2 (by norm_num)
  simp only [OptimizedComputeCodec.pubFingerprint] at e0 e1 e2
  unfold rowLabelVec
  funext k
  fin_cases k <;> simp [labelVecOfPub, hst, e0, e1, e2]

theorem rowTags_honest (i : Fin P.optimized.family.problem.cfg.compRows) :
    rowTags (P.computeSourceEnv (canonicalComputeTrace P) i) =
      fun j : Fin 3 =>
        ComputeTable.childStateTagCol P.optimized.family.computeWalkRows ((i : ℕ) + 1) j := by
  funext j
  unfold rowTags
  rw [Batch958.src_rowState_honest P i]
  exact src_tags P i j

/-- The declared child payload at the canonical compute trace. -/
theorem rowChildVec_honest (i : Fin P.optimized.family.problem.cfg.compRows) (l : ℕ) :
    rowChildVec (P.computeSourceEnv (canonicalComputeTrace P) i) l =
      ComputeWalkLabel.childVecN (P.optimized.family.problem.exec.computePubAt i)
        (fun j : Fin 3 => ComputeTable.childStateTagCol P.optimized.family.computeWalkRows
          ((i : ℕ) + 1) j) l := by
  obtain ⟨-, hfp⟩ := rowPub_honest P i
  unfold rowChildVec
  rw [rowTags_honest P i]
  have hsf : ∀ j : Fin 3, ComputeTable.sfTriple
      (rowPub (P.computeSourceEnv (canonicalComputeTrace P) i)) j =
      ComputeTable.sfTriple (P.optimized.family.problem.exec.computePubAt i) j := by
    intro j
    have a := hfp (3 + 3 * j) (by omega)
    have b := hfp (4 + 3 * j) (by omega)
    have c := hfp (5 + 3 * j) (by omega)
    fin_cases j <;>
      simp [OptimizedComputeCodec.pubFingerprint, ComputeTable.sfTriple] at a b c ⊢ <;>
      exact ⟨a, b, c⟩
  match l with
  | 0 => funext k; have := hsf 0; simp only [ComputeWalkLabel.childVecN, ComputeWalkLabel.childVec, this]
  | 1 => funext k; have := hsf 1; simp only [ComputeWalkLabel.childVecN, ComputeWalkLabel.childVec, this]
  | 2 => funext k; have := hsf 2; simp only [ComputeWalkLabel.childVecN, ComputeWalkLabel.childVec, this]
  | n + 3 => rfl

/-! ## B. The committed compute vectors and the two components -/

/-- The `LT_comp` label of a compute walk node. -/
def gComp (t : NTree (State × DTcomp K)) : Fin 10 → K := labelVecOfPub t.label.2.2.1

theorem foOf_foCol (i : ℕ) (hi1 : 1 ≤ i) (hiN : i ≤ P.optimized.family.problem.cfg.compRows) :
    foOf (P.computeSourceEnv (canonicalComputeTrace P)) i =
      Walk.foCol P.optimized.family.computeWalkRows i := by
  have hlt : i - 1 < P.optimized.family.problem.cfg.compRows := by omega
  unfold foOf
  rw [dif_pos ⟨hi1, hlt⟩]
  unfold rowFanout
  rw [Batch958.src_rowState_honest]
  have h := foCol_eq_fanout (R := P.optimized.family) P.optimized.computeObligations.2.2.2.2
    ⟨i - 1, hlt⟩
  have hi : ((⟨i - 1, hlt⟩ : Fin _) : ℕ) + 1 = i := by simp; omega
  rw [hi] at h
  exact h.symm

theorem committedComputeV_honest (i : ℕ) (hi1 : 1 ≤ i)
    (hiN : i ≤ P.optimized.family.problem.cfg.compRows) :
    committedComputeV (P.computeSourceEnv (canonicalComputeTrace P)) i =
      vcur gComp P.optimized.family.computeWalkRows i := by
  have hlt : i - 1 < P.optimized.family.problem.cfg.compRows := by omega
  unfold committedComputeV vcur
  rw [dif_pos ⟨hi1, hlt⟩, rowLabelVec_honest]
  obtain ⟨t, ht, hl⟩ := computeWalkRows_getElem?_row (R := P.optimized.family) ⟨i - 1, hlt⟩
  simp only at ht
  rw [ht]
  simp only [Option.map_some, Option.getD_some, gComp, hl]
  rfl

theorem committedComputeCv_honest (i l : ℕ) (hi1 : 1 ≤ i)
    (hiN : i ≤ P.optimized.family.problem.cfg.compRows) (hl1 : 1 ≤ l)
    (hlfo : l ≤ Walk.foCol P.optimized.family.computeWalkRows i) :
    committedComputeCv (P.computeSourceEnv (canonicalComputeTrace P)) i l =
      vchld gComp P.optimized.family.computeWalkRows i l := by
  have hlt : i - 1 < P.optimized.family.problem.cfg.compRows := by omega
  set ii : Fin P.optimized.family.problem.cfg.compRows := ⟨i - 1, hlt⟩ with hii
  have htopo := P.optimized.computeObligations.2.2.2.2
  obtain ⟨t, ht, hlbl⟩ := computeWalkRows_getElem?_row (R := P.optimized.family) ii
  obtain ⟨hst, hfan, hlink⟩ := htopo t (List.mem_of_getElem? ht)
  have hpub : P.optimized.family.problem.exec.computePubAt ii = t.label.2.2.1 := by
    show (P.optimized.family.problem.exec.computeRowAt ii).2.2.1 = _
    rw [hlbl]
  have hfoi : Walk.foCol P.optimized.family.computeWalkRows i = t.children.length := by
    unfold Walk.foCol
    have : (ii : ℕ) = i - 1 := rfl
    rw [← this, ht]; rfl
  have hlt2 : l - 1 < t.children.length := by omega
  have hle3 : l - 1 < 3 := by
    have := ComputeWalkLabel.fanoutComp_le_three t.label.1
    omega
  obtain ⟨c, hc⟩ : ∃ c, t.children[l - 1]? = some c :=
    ⟨t.children[l - 1], List.getElem?_eq_getElem hlt2⟩
  have hlinkj' : (c.label.2.2.1.s, c.label.2.2.1.f, c.label.2.2.1.e) =
      sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩ := by
    have hlinkj := hlink ⟨l - 1, hle3⟩ (by
      show l - 1 < fanoutComp t.label.1
      rw [hfan]; exact hlt2)
    simp only [Walk.NTree.childLabel, Walk.NTree.childOpt, hc, Option.map_some] at hlinkj
    exact Option.some.inj hlinkj
  have hcs : c.label.2.2.1.s = (sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩).1 :=
    congrArg Prod.fst hlinkj'
  have hcf : c.label.2.2.1.f = (sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩).2.1 :=
    congrArg (fun x => x.2.1) hlinkj'
  have hce : c.label.2.2.1.e = (sfTriple t.label.2.2.1 ⟨l - 1, hle3⟩).2.2 :=
    congrArg (fun x => x.2.2) hlinkj'
  have htag : ComputeTable.childStateTagCol P.optimized.family.computeWalkRows ((ii : ℕ) + 1)
      (l - 1) = stateTagField c.label.2.2.1.state := by
    have : ((ii : ℕ) + 1) - 1 = (ii : ℕ) := by omega
    simp [ComputeTable.childStateTagCol, this, ht, hc]
  unfold committedComputeCv vchld
  rw [dif_pos ⟨hi1, hlt⟩]
  rw [show (⟨i - 1, hlt⟩ : Fin _) = ii from rfl, rowChildVec_honest P ii]
  have hii1 : i - 1 = (ii : ℕ) := rfl
  rw [hii1, ht]
  simp only [Option.bind_some, hc, Option.map_some, Option.getD_some, gComp]
  rw [hpub]
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, (j : ℕ) = l - 1 := ⟨⟨l - 1, hle3⟩, rfl⟩
  rw [← hj, ComputeWalkLabel.childVecN_fin]
  funext k
  have hj' : (⟨l - 1, hle3⟩ : Fin 3) = j := Fin.ext hj.symm
  rw [hj'] at hcs hcf hce
  rw [← hj] at htag
  fin_cases k <;>
    simp [ComputeTable.labelVecOfPub, ComputeWalkLabel.childVec, htag, hcs, hcf, hce]

/-- **The committed compute vector BFS identity at the canonical trace** (every package). -/
theorem committed_vecBFT_honest :
    curValsV (committedComputeV (P.computeSourceEnv (canonicalComputeTrace P)))
        P.optimized.family.problem.cfg.compRows =
      committedComputeV (P.computeSourceEnv (canonicalComputeTrace P)) 1 ::
        flatBlksV (committedComputeCv (P.computeSourceEnv (canonicalComputeTrace P)))
          (foOf (P.computeSourceEnv (canonicalComputeTrace P)))
          P.optimized.family.problem.cfg.compRows := by
  have hN := P.optimized.family.problem.cfg.compRows_pos
  have hV : ∀ h, h ≤ P.optimized.family.problem.cfg.compRows →
      curValsV (committedComputeV (P.computeSourceEnv (canonicalComputeTrace P))) h =
      curValsV (vcur gComp P.optimized.family.computeWalkRows) h := fun h hh =>
    curValsV_congr_on (fun i h1 h2 => committedComputeV_honest P i h1 (le_trans h2 hh))
  have hC : flatBlksV (committedComputeCv (P.computeSourceEnv (canonicalComputeTrace P)))
        (foOf (P.computeSourceEnv (canonicalComputeTrace P)))
        P.optimized.family.problem.cfg.compRows =
      flatBlksV (vchld gComp P.optimized.family.computeWalkRows)
        (Walk.foCol P.optimized.family.computeWalkRows) P.optimized.family.problem.cfg.compRows :=
    flatBlksV_congr_on (fun i h1 h2 => foOf_foCol P i h1 h2)
      (fun i l h1 h2 hl1 hl2 => committedComputeCv_honest P i l h1 h2 hl1
        (by rw [← foOf_foCol P i h1 h2]; exact hl2))
  have h1 : committedComputeV (P.computeSourceEnv (canonicalComputeTrace P)) 1 =
      vcur gComp P.optimized.family.computeWalkRows 1 :=
    committedComputeV_honest P 1 le_rfl hN
  rw [hV _ le_rfl, hC, h1]
  have hW : P.optimized.family.computeWalkRows =
      bfsForest [P.optimized.family.problem.exec.computeTree] := rfl
  have hlenW : P.optimized.family.computeWalkRows.length =
      P.optimized.family.problem.cfg.compRows := by
    have := P.optimized.family.problem.exec.computeRows_length
    simpa [ExactExecution.computeRows, PlusIOSegmentedFamily.computeWalkRows,
      List.length_map] using this
  have := forest_vec_identity (by norm_num : 0 < 10) gComp
    [P.optimized.family.problem.exec.computeTree] (by simp)
  rw [← hW, hlenW] at this
  rw [this]
  simp [curValsV]

/-- **Component 8 at the honest instance**: the compute prefix-γ event is empty at the canonical
trace, for every coin, at every package. -/
theorem computePrefixGamma_empty_honest :
    P.computePrefixGammaEventOf (canonicalComputeTrace P) = ∅ := by
  ext ω
  simp only [Finset.notMem_empty, iff_false]
  intro hω
  have h := (computePrefixGammaEventOf_eq_prefix _ ω).1 hω
  unfold prefixBadGammas at h
  rw [← committed_vecBFT_honest P, List.take_of_length_le (by rw [curValsV_length])] at h
  rw [badRLCList_self] at h
  exact Finset.notMem_empty _ h

/-- `IsFullBFT` of the committed compute columns at every `γ`. -/
theorem isFullBFT_honest (γ : K) :
    IsFullBFT (curOf (P.computeSourceEnv (canonicalComputeTrace P)) γ)
      (chldOf (P.computeSourceEnv (canonicalComputeTrace P)) γ)
      (foOf (P.computeSourceEnv (canonicalComputeTrace P)))
      P.optimized.family.problem.cfg.compRows := by
  have hcur : curOf (P.computeSourceEnv (canonicalComputeTrace P)) γ =
      fun i => rlc γ (committedComputeV (P.computeSourceEnv (canonicalComputeTrace P)) i) := by
    funext i
    unfold curOf committedComputeV
    split_ifs <;> simp [rlc]
  have hchld : chldOf (P.computeSourceEnv (canonicalComputeTrace P)) γ =
      fun i l => rlc γ (committedComputeCv (P.computeSourceEnv (canonicalComputeTrace P)) i l) := by
    funext i l
    unfold chldOf committedComputeCv
    split_ifs <;> simp [rlc]
  unfold IsFullBFT
  rw [nodeListP_eq_lpoly_gen, nodeQueueP_eq_gen, hcur, hchld, curVals_rlc, flatBlks_rlc,
    committed_vecBFT_honest P, List.map_cons, lpoly_cons]
  simp

/-- **Component 5 at the honest instance**, at every package, from the `HonestFill` root
equalities: the walk root event misses the honest tuple. -/
theorem walkRoot_honest (H : Batch906.HonestFill P) :
    P.honestTuple.1 ∉ P.computeWalkRootEvent (canonicalComputeTrace P) := by
  have hN := P.optimized.family.problem.cfg.compRows_pos
  refine notMem_rootEvent_of_root_eq_of_isFullBFT _ _ _ _ hN rfl ?_ (isFullBFT_honest P _)
  rw [rowLabelVec_honest P ⟨0, hN⟩]
  exact (ComputeWalkSeed.labelVecOfPub_eq_claimLabelVec _ _ _ H.hst H.hs H.hf H.he).symm

end

end Nock.RedTeam.Batch962

#print axioms Nock.RedTeam.Batch962.rowLabelVec_honest
#print axioms Nock.RedTeam.Batch962.rowChildVec_honest
#print axioms Nock.RedTeam.Batch962.committed_vecBFT_honest
#print axioms Nock.RedTeam.Batch962.computePrefixGamma_empty_honest
#print axioms Nock.RedTeam.Batch962.walkRoot_honest
