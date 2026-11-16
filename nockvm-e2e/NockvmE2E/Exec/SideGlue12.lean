/-
 conjunct 5, word0 link, step 2: the position of an entry of `opList` is `offX j + o` (`opList_nodup`, `opList_idx`), and
`ops_forall2`: the openings of the flat side verifier (`fixOps`) are position by position the batched openings of `stmtOf` (coefficient `cs^i`, point
`ptKX`, claimed value, honest base value).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue12` is complete.
-/
import NockvmE2E.Exec.SideGlue11

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue12
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SideInst NockvmE2E.Exec.SideGlue

theorem opList_nodup (XI : ExecInst) : (opList XI).Nodup := by
  unfold opList
  rw [List.nodup_flatMap]
  refine ⟨fun j _ => ?_, ?_⟩
  · exact (List.nodup_range).map (fun a b h => by simpa using h)
  · refine List.pairwise_iff_getElem.mpr (fun a b ha hb hab => ?_)
    intro x hx1 hx2
    simp only [List.mem_map] at hx1 hx2
    obtain ⟨o1, _, h1⟩ := hx1
    obtain ⟨o2, _, h2⟩ := hx2
    have := congrArg Prod.fst (h1.trans h2.symm)
    simp only [List.getElem_range] at this
    omega

/-- every position `i` of `opList` holds `(j,o)` with `i = offX j + o` -/
theorem opList_idx (XI : ExecInst) (i : ℕ) (hi : i < (opList XI).length) :
    ∃ j o, j < (fixCols XI).size ∧ o < fixLen XI (fixCols XI)[j]! ∧ (opList XI)[i] = (j, o) ∧ i = offX XI j + o := by
  have hmem : (opList XI)[i] ∈ opList XI := List.getElem_mem hi
  have hp : (opList XI)[i] = ((opList XI)[i].1, (opList XI)[i].2) := rfl
  rw [hp, mem_opList] at hmem
  obtain ⟨hj, ho⟩ := hmem
  refine ⟨_, _, hj, ho, hp, ?_⟩
  have h := opList_getElem? XI _ _ hj ho
  obtain ⟨hb, hq⟩ := List.getElem?_eq_some_iff.mp h
  have := (List.Nodup.getElem_inj_iff (opList_nodup XI)).mp (hq.trans hp : (opList XI)[offX XI (opList XI)[i].1 + (opList XI)[i].2] = (opList XI)[i])
  exact this.symm

theorem fixOps_toList (XI : ExecInst) (cs : VF.K3) (vF : Array (Array VF.K3)) :
    (fixOps XI (fixCols XI) cs vF).toList =
      (opList XI).map (fun p => (p.1, p.2, pw cs VF.K3.one (offX XI p.1 + p.2), (vF[p.1]!)[p.2]!)) := by
  rw [fixOps_eq]
  unfold opList offX
  simp [List.map_flatMap, List.map_map, Function.comp_def]

/-- **`ops_forall2`**: the flat openings are, position by position, the batched openings of `stmtOf` -/
theorem ops_forall2 (XI : ExecInst) (hpos : 0 < (opList XI).length) (st : SideStmt) (cs : VF.K3) (vF : Array (Array VF.K3))
    (hvF : st.vF = vF) (hfl : ∀ j, j < (fixCols XI).size → fixLen XI (fixCols XI)[j]! ≤ XI.r + 2)
    (pts : Array VF.K3) (hpts : pts = openPts XI (VF.K3.ofLimbs (st.ctx.drop (st.ctx.length - 3))))
    (baseAt : ℕ → ℕ → VF.G) (idx : ℕ) (idx' : Fin (2 ^ XI.nD)) (hidx : (idx' : ℕ) = idx)
    (hbase : ∀ j, j < (fixCols XI).size → homV.ψ (baseAt j idx) = honestWord XI (fixCols XI)[j]! idx') :
    List.Forall₂ (fun (o : ℕ × ℕ × VF.K3 × VF.K3) (j : Fin (mSX XI + 1)) =>
      o.2.1 < XI.r + 2 ∧ homV.φ o.2.2.1 = toKV cs ^ (j : ℕ) ∧ homV.φ pts[o.2.1]! = (SideCfg.mk (m := mSX XI) XI (opIdxX XI) (ptKX XI)).pt st j ∧
      homV.φ o.2.2.2 = (SideCfg.mk (m := mSX XI) XI (opIdxX XI) (ptKX XI)).val st j ∧
      homV.ψ (baseAt o.1 idx) = honestWord XI ((SideCfg.mk (m := mSX XI) XI (opIdxX XI) (ptKX XI)).col j) idx')
    (fixOps XI (fixCols XI) cs vF).toList (List.finRange (mSX XI + 1)) := by
  have hlen : mSX XI + 1 = (opList XI).length := by unfold mSX; omega
  rw [fixOps_toList, List.forall₂_iff_get]
  refine ⟨by simp [hlen], fun i h1 h2 => ?_⟩
  have hi : i < (opList XI).length := by simpa using h1
  obtain ⟨j, o, hj, ho, hget, hioff⟩ := opList_idx XI i hi
  have hfin : (List.finRange (mSX XI + 1)).get ⟨i, h2⟩ = ⟨i, by omega⟩ := by
    simp [List.get_eq_getElem]
  have hel : ((opList XI).map (fun p => (p.1, p.2, pw cs VF.K3.one (offX XI p.1 + p.2), (vF[p.1]!)[p.2]!))).get ⟨i, h1⟩ =
      (j, o, pw cs VF.K3.one i, (vF[j]!)[o]!) := by
    simp only [List.get_eq_getElem, List.getElem_map, hget]
    rw [← hioff]
  rw [hel, hfin]
  have hop : opIdxX XI ⟨i, by omega⟩ = (j, o) := by
    unfold opIdxX
    rw [getElem!_pos (opList XI) i hi]; exact hget
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show o < XI.r + 2
    have := hfl j hj; omega
  · show toKV (pw cs VF.K3.one i) = toKV cs ^ i
    exact toKV_pw cs i
  · rw [hpts]
    show _ = toKV (ptKX XI st.ctx ⟨i, _⟩)
    unfold ptKX; rw [hop]
    rfl
  · show _ = toKV ((st.vF[(opIdxX XI ⟨i, _⟩).1]!)[(opIdxX XI ⟨i, _⟩).2]!)
    rw [hop, hvF]; rfl
  · show _ = honestWord XI ((fixCols XI)[(opIdxX XI ⟨i, _⟩).1]!) idx'
    rw [hop]
    exact hbase j hj

end NockvmE2E.Exec.SideGlue12

#print axioms NockvmE2E.Exec.SideGlue12.opList_idx
#print axioms NockvmE2E.Exec.SideGlue12.ops_forall2
