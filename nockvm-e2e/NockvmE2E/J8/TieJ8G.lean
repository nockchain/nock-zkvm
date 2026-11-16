/-
finish the tie.  Builds on `J8/TieJ8.lean` (per-table ties `tieD_*`, routes `rtJ8`,
`fiber_global`, `aeval_Cfun`) and delivers the binders of `HdagU.hdagU_of_tie` at `plusJ ∘ minusT (RJ8 …)` of `J8 d hd`.
-/
import NockvmE2E.J8.TieJ8
import NockvmE2E.J8.InstJ8W
import NockvmE2E.Exec.HdagU
import NockvmE2E.Exec.J8Shape
import NockvmE2E.Exec.E2EInstGen

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

open Polynomial

namespace NockvmE2E.J8.TieJ8G

open NockvmE2E.J8 NockvmE2E.J8.TieJ8 NockvmE2E.Rap NockvmE2E.Emit Nock.Emit
open NockvmE2E.Exec NockvmE2E.Exec.DagSem NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen
open NockvmE2E.J8.InstJ8 (Datum DatumOK Msg Ι Φ0 J8 PbOfX PosX hNof tabOf tabId ω0 sz tabSfun HtOf HdomOf omegaOf)
open NockvmE2E.J8.InstJ8W (RJ8 sigmaX tabIdx hfree_J8)

/-! ## 1. flat indices (the loader's `flatMap` order) -/

theorem flatIdx_off : ∀ (L : List ℕ) (t l : ℕ) (ht : t < L.length), l < L[t] →
    flatIdx L ((L.take t).sum + l) = (t, l)
  | [], t, l, ht, _ => by simp at ht
  | s :: ss, 0, l, _, hl => by
    simp only [List.getElem_cons_zero] at hl
    simp [flatIdx, hl]
  | s :: ss, t + 1, l, ht, hl => by
    have ht' : t < ss.length := by simpa using ht
    have hl' : l < ss[t] := by simpa using hl
    have h1 := flatIdx_off ss t l ht' hl'
    have hn : ¬ (s + (ss.take t).sum + l < s) := by omega
    have e : s + (ss.take t).sum + l - s = (ss.take t).sum + l := by omega
    simp only [List.take_succ_cons, List.sum_cons, flatIdx, hn, if_false, e, h1]

theorem off_lt : ∀ (L : List ℕ) (t l : ℕ) (ht : t < L.length), l < L[t] → (L.take t).sum + l < L.sum
  | [], t, l, ht, _ => by simp at ht
  | s :: ss, 0, l, _, hl => by
    simp only [List.getElem_cons_zero] at hl
    simp; omega
  | s :: ss, t + 1, l, ht, hl => by
    have ht' : t < ss.length := by simpa using ht
    have hl' : l < ss[t] := by simpa using hl
    have := off_lt ss t l ht' hl'
    simp only [List.take_succ_cons, List.sum_cons]; omega

theorem flatIdx_fst_lt : ∀ (L : List ℕ) (i : ℕ), i < L.sum → (flatIdx L i).1 < L.length
  | [], i, h => by simp at h
  | s :: ss, i, h => by
    by_cases hi : i < s
    · simp [flatIdx, hi]
    · have h2 : i - s < ss.sum := by simp at h; omega
      have := flatIdx_fst_lt ss (i - s) h2
      simp [flatIdx, hi]; omega

theorem flatIdx_snd_lt : ∀ (L : List ℕ) (i : ℕ) (h : i < L.sum), (flatIdx L i).2 < L[(flatIdx L i).1]'(flatIdx_fst_lt L i h)
  | [], i, h => by simp at h
  | s :: ss, i, h => by
    by_cases hi : i < s
    · simp [flatIdx, hi]
    · have h2 : i - s < ss.sum := by simp at h; omega
      have := flatIdx_snd_lt ss (i - s) h2
      simp only [flatIdx, hi, if_false]
      simpa using this

theorem flatIdx_inv : ∀ (L : List ℕ) (i : ℕ), i < L.sum →
    (L.take (flatIdx L i).1).sum + (flatIdx L i).2 = i
  | [], i, h => by simp at h
  | s :: ss, i, h => by
    by_cases hi : i < s
    · simp [flatIdx, hi]
    · have h2 : i - s < ss.sum := by simp at h; omega
      have := flatIdx_inv ss (i - s) h2
      simp only [flatIdx, hi, if_false, List.take_succ_cons, List.sum_cons]
      omega

/-- injectivity of the flat index on the valid pairs -/
theorem off_inj (L : List ℕ) (t t' l l' : ℕ) (ht : t < L.length) (ht' : t' < L.length) (hl : l < L[t]) (hl' : l' < L[t'])
    (h : (L.take t).sum + l = (L.take t').sum + l') : t = t' ∧ l = l' := by
  have h1 := flatIdx_off L t l ht hl
  have h2 := flatIdx_off L t' l' ht' hl'
  rw [h] at h1
  have := h1.symm.trans h2
  exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj this).2⟩

/-! ## 2. the layout of the columns of table `s` in `Ι` -/

/-- the interface column of local column `n` of table `s` (total: out of range wraps) -/
def colI : Fin 6 → ℕ → Ι
  | 0, n => Sum.inl ⟨n % 123, Nat.mod_lt _ (by norm_num)⟩
  | 1, n => Sum.inr (Sum.inl ⟨n % 242, Nat.mod_lt _ (by norm_num)⟩)
  | 2, n => Sum.inr (Sum.inr (Sum.inl ⟨n % 166, Nat.mod_lt _ (by norm_num)⟩))
  | 3, n => Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨n % 71, Nat.mod_lt _ (by norm_num)⟩)))
  | 4, n => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨n % 349, Nat.mod_lt _ (by norm_num)⟩))))
  | 5, n => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨n % 166, Nat.mod_lt _ (by norm_num)⟩))))

/-- the local width of the non-public columns of table `s` -/
def wOf : Fin 6 → ℕ
  | 0 => 123 | 1 => 242 | 2 => 166 | 3 => 71 | 4 => 349 | 5 => 166

/-- the number of public values of table `s` -/
def npubOf : Fin 6 → ℕ
  | 0 => 33 | 1 => 6 | 2 => 8 | 3 => 4 | 4 => 12 | 5 => 8

theorem tabΙ_colI (s : Fin 6) (n : ℕ) : InstJ8.tabΙ (colI s n) = s := by
  fin_cases s <;> rfl

theorem w_jet : Nock.Emit.jetTemplate.width 3 = 71 := by decide +kernel
theorem w_atom : Nock.Emit.atomTemplate.width 3 = 349 := by decide +kernel

theorem eCell_eq (j : Fin (Nock.Emit.cellKWTemplate.width 3)) : eCell j = colI 1 j.1 := by
  have h : j.1 < 242 := lt_of_lt_of_eq j.2 w_cell
  simp only [eCell, colI]
  congr 3
  exact Fin.ext (Nat.mod_eq_of_lt h).symm

theorem eWalk_eq (k : ℕ) (j : Fin ((tWalkJ8 k).width 3)) : eWalk k j = colI 2 j.1 := by
  have h : j.1 < 166 := j.2
  simp only [eWalk, colI]
  congr 4
  exact Fin.ext (Nat.mod_eq_of_lt h).symm

theorem eJet_eq (j : Fin (Nock.Emit.jetTemplate.width 3)) : eJet j = colI 3 j.1 := by
  have h : j.1 < 71 := lt_of_lt_of_eq j.2 w_jet
  simp only [eJet, colI]
  congr 5
  exact Fin.ext (Nat.mod_eq_of_lt h).symm

theorem eAtom_eq (j : Fin (Nock.Emit.atomTemplate.width 3)) : eAtom j = colI 4 j.1 := by
  have h : j.1 < 349 := lt_of_lt_of_eq j.2 w_atom
  simp only [eAtom, colI]
  congr 6
  exact Fin.ext (Nat.mod_eq_of_lt h).symm

theorem eWalkV_eq (k : ℕ) (j : Fin ((tWalkV k).width 3)) : eWalkV k j = colI 5 j.1 := by
  have h : j.1 < 166 := j.2
  simp only [eWalkV, colI]
  congr 6
  exact Fin.ext (Nat.mod_eq_of_lt h).symm

theorem eComp_eq (j : Fin 123) : eComp j = colI 0 j.1 := by
  simp only [eComp, colI]
  congr 1
  exact Fin.ext (by simp [Nat.mod_eq_of_lt j.2])

/-! ## 3. the per-table tie, uniformly in the table -/

/-- the emitted DAG document of table `s` (hop 0 compares the loaded chip with `verifierChipT` of its parse) -/
def DOf (d : Datum) : Fin 6 → DagGates
  | 0 => Nock.Emit.emit_compute
  | 1 => Nock.Emit.emit_cellKW
  | 2 => emitDag (Nock.Emit.walkJ8SpecAt d.Pb.kroots)
  | 3 => Nock.Emit.emit_jet
  | 4 => Nock.Emit.emit_atom
  | 5 => emitDag (Nock.Emit.walkAtomSpecAt d.Pb.krootsV)

/-- the base-column count of each J-8 chip -/
def bcOf : Fin 6 → ℕ
  | 0 => 69 | 1 => 134 | 2 => 25 | 3 => 29 | 4 => 205 | 5 => 25

/-- what `pr.rd` must hand the chip of table `s` -/
def PubsOK (M : Msg) (env : KEnv) : Fin 6 → Prop
  | 0 => ∀ s < 33, InstJ8.xpF M.2 s = env.pub s
  | 1 => ∀ i < 6, M.1.pubsC i = NockvmE2E.Emit.pubK env i
  | 2 => ∀ i < 8, M.1.pubsW i = NockvmE2E.Emit.pubK env i
  | 3 => ∀ i < 4, M.1.pubsJ i = NockvmE2E.Emit.pubK env i
  | 4 => ∀ i < 12, M.1.pubsA i = NockvmE2E.Emit.pubK env i
  | 5 => ∀ i < 8, M.1.pubsV i = NockvmE2E.Emit.pubK env i

/-- the tie of one table against its loaded chip (`tieD_*`, uniformly) -/
def TieAt (d : Datum) (χ : Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (env : KEnv) (ch : NockvmE2E.Exec.Tr.Chip)
    (s : Fin 6) : Prop :=
  ∀ ℓ < (rtJ8 d s).nK, ∑ k ∈ Finset.range ((rtJ8 d s).mult ℓ), cf k * consAt d χ M s val ((rtJ8 d s).jOf ℓ k) =
    (evalDagK ch env)[ℓ]!

/-- the kroots / krootsV numerals the emitted walk chips exist for (named hypothesis of the bundle) -/
def NumOK (d : Datum) (s : Fin 6) : Prop :=
  (s = 2 → d.Pb.kroots ∈ [1, 9, 25, 42, 48, 174]) ∧ (s = 5 → d.Pb.krootsV ∈ [1, 2])

set_option maxHeartbeats 1600000 in
theorem tieAt (d : Datum) (χ : Coins Φ0 KN) (M : Msg) (val : Ι × Fin 2 → KN) (ders : Array NockvmE2E.Exec.Aux.Der)
    (cmeta : Array (ℕ × ℕ)) (env : KEnv) (ch : NockvmE2E.Exec.Tr.Chip) (s : Fin 6) (hnum : NumOK d s)
    (hop : HopZero ch (DOf d s) ders cmeta ch.baseCols) (hbc : ch.baseCols = bcOf s) (hbe : env.bc = bcOf s)
    (hcur : ∀ n < wOf s, env.cur n = val (colI s n, 0)) (hnext : ∀ n < wOf s, env.next n = val (colI s n, 1))
    (hE : NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta env.chal) (χf χ)) (hpub : PubsOK M env s) :
    TieAt d χ M val env ch s := by
  fin_cases s
  · exact tieD_comp d χ M val ders cmeta env ch hop hbe
      (fun n hn => by rw [eComp_eq]; exact hcur n hn) (fun n hn => by rw [eComp_eq]; exact hnext n hn) hE hpub
  · exact tieD_cell d χ M val ders cmeta env ch hop hbe hbc
      (fun n hn => by rw [eCell_eq]; exact hcur n (by have := hn; rwa [w_cell] at this))
      (fun n hn => by rw [eCell_eq]; exact hnext n (by have := hn; rwa [w_cell] at this)) hE hpub
  · exact tieD_walk d χ M val ders cmeta env ch (hnum.1 rfl) hop hbe
      (fun n hn => by rw [eWalk_eq]; exact hcur n hn) (fun n hn => by rw [eWalk_eq]; exact hnext n hn) hE hpub
  · exact tieD_jet d χ M val ders cmeta env ch hop hbe
      (fun n hn => by rw [eJet_eq]; exact hcur n (by have := hn; rwa [w_jet] at this))
      (fun n hn => by rw [eJet_eq]; exact hnext n (by have := hn; rwa [w_jet] at this)) hE hpub
  · exact tieD_atom d χ M val ders cmeta env ch hop hbe
      (fun n hn => by rw [eAtom_eq]; exact hcur n (by have := hn; rwa [w_atom] at this))
      (fun n hn => by rw [eAtom_eq]; exact hnext n (by have := hn; rwa [w_atom] at this)) hE hpub
  · exact tieD_walkV d χ M val ders cmeta env ch (hnum.2 rfl) hop hbe
      (fun n hn => by rw [eWalkV_eq]; exact hcur n hn) (fun n hn => by rw [eWalkV_eq]; exact hnext n hn) hE hpub

/-! ## 4. the instance and the sizes -/

/-- the data of one J-8 interface instance over a loaded `XI` (`PbOfX`, the datum of `J8`, its union domain, the table restriction).
The restriction `R` is a FIELD (abstract for the elaborator: unifying `Fin (RJ8 …).ns'` with `Fin (minusT …).ns` is very slow); the
instance of the final theorem is `R := RJ8 XI d hd` (`Inst.ofRJ8`). -/
structure Inst where
  XI : ExecInst
  hsh : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true
  hpos : PosX XI
  kroots : ℕ
  krootsV : ℕ
  Rt : ℕ → Nock.Jet.Autogen.Tpl
  regs : List ℕ
  ids : List ℕ
  idx : ℕ → ℕ
  rk : ℕ → ℕ × ℕ
  lay : Fin (hNof XI "jetChipJ8") → Nock.Jet.ChipJ8.PRow
  d : Datum
  hd : d.Pb = PbOfX XI hsh hpos kroots krootsV Rt regs ids idx rk lay
  hdk : DatumOK d
  /-- the datum's union domain is the verifier's (`Datum.hN`, `Datum.ω`) -/
  hdN : d.hN = XI.hN
  hdω : d.ω = ω0 XI
  /-- the table restriction (the instance: `RJ8 XI d hd`) -/
  R : TabRestr (J8 d hdk)
  hT : R.T' = XI.tabs.size
  hσ : ∀ t : Fin R.T', R.σ t = sigmaX XI (Fin.cast hT t)
  hfree : (J8 d hdk).AccOn R.q

namespace Inst
variable (I : Inst)

/-- `J−`: the present tables of `J8 d hd` -/
noncomputable def Jm : RapAirJ (ZMod InstJ8.P) KN := minusT (J8 I.d I.hdk) I.R I.hfree

/-- the cap of `plusJ` (the new `cap_m`): width of the interface with `npub` public columns -/
def Cap (npub : ℕ) : Prop := (Fintype.card I.Jm.ι0 + Fintype.card (Fin npub)) * I.Jm.r + 3 * (I.Jm.d - 1) ≤ 2 ^ 12

/-- the interface of the final theorem: `plusJ ∘ minusT` -/
noncomputable def JJ (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub) :
    RapAirJ (ZMod NockvmE2E.Exec.p) NockvmE2E.Exec.KC := plusJ I.Jm (Fin npub) tp hcap

end Inst

/-- the table sizes of the loader's flat order -/
def sizes (XI : ExecInst) : List ℕ := XI.tabs.toList.map (·.chip.cons.size)

/-- the number of flat DAG constraints -/
def nsK (XI : ExecInst) : ℕ := (sizes XI).sum

theorem sizes_length (XI : ExecInst) : (sizes XI).length = XI.tabs.size := by simp [sizes]

theorem sizes_get (XI : ExecInst) (t : ℕ) (ht : t < (sizes XI).length) :
    (sizes XI)[t] = (XI.tabs[t]'(by rwa [sizes_length] at ht)).chip.cons.size := by simp [sizes]

/-- the chips' constraint counts are the routes' DAG gate counts -/
def HSz (I : Inst) : Prop :=
  ∀ t : Fin I.XI.tabs.size, I.XI.tabs[t].chip.cons.size = (rtJ8 I.d (sigmaX I.XI t)).nK

/-! ## 5. the chip's constraint count from hop 0 -/

section Cons
variable (d : Datum) (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ))

theorem consSize_of (s : Fin 6) (hnum : NumOK d s) (ch : NockvmE2E.Exec.Tr.Chip)
    (hop : HopZero ch (DOf d s) ders cmeta ch.baseCols) : ch.cons.size = (rtJ8 d s).nK := by
  let env0 : KEnv := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0⟩
  have hsz : (evalDagK ch env0).size = ch.cons.size := by simp [evalDagK]
  rw [← hsz]
  fin_cases s
  · have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_compute) ders cmeta hop env0
    rw [dagVals_comp] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1]
    show _ = (cRoute cArith.length cEq.length cAcc.length (cSlot ++ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.walkGatesFX).length).nK
    simp only [compVals, List.length_append, List.length_map, cRoute]
  · have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_cellKW) ders cmeta hop env0
    rw [show Nock.Emit.cellKWSpec.gates = ((TSpec.ofTemplate Nock.Emit.cellKWTemplate).rename Nock.Emit.fM id id).gates from rfl,
      dagVals_nc Nock.Emit.cellKWTemplate rfl rfl rfl rfl Nock.Emit.fM] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · have hv := evalDagK_hop ch _ _ (decL_of_decR (decR_walkJ8_at _ (hnum.1 rfl))) ders cmeta hop env0
    rw [show (Nock.Emit.walkJ8SpecAt d.Pb.kroots).gates = ((TSpec.ofTemplate (tWalkJ8 d.Pb.kroots)).rename Nock.Emit.fM id id).gates
      from rfl, dagVals_nc (tWalkJ8 d.Pb.kroots) rfl rfl rfl rfl Nock.Emit.fM] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_jet) ders cmeta hop env0
    rw [show Nock.Emit.jetSpec.gates = ((TSpec.ofTemplate Nock.Emit.jetTemplate).rename Nock.Emit.fJ id id).gates from rfl,
      dagVals_nc Nock.Emit.jetTemplate rfl rfl rfl rfl Nock.Emit.fJ] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.Emit.decR_atom) ders cmeta hop env0
    rw [show Nock.Emit.atomSpec.gates = ((TSpec.ofTemplate Nock.Emit.atomTemplate).rename Nock.Emit.fA id id).gates from rfl,
      dagVals_nc Nock.Emit.atomTemplate rfl rfl rfl rfl Nock.Emit.fA] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · have hv := evalDagK_hop ch _ _ (decL_of_decR (decR_walkV_at _ (hnum.2 rfl))) ders cmeta hop env0
    rw [show (Nock.Emit.walkAtomSpecAt d.Pb.krootsV).gates = ((TSpec.ofTemplate (tWalkV d.Pb.krootsV)).rename Nock.Emit.fM id id).gates
      from rfl, dagVals_nc (tWalkV d.Pb.krootsV) rfl rfl rfl rfl Nock.Emit.fM] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl

end Cons

/-! ## 6. the regroup `G` over the present constraints of `minusT` -/

theorem glob_ext (d : Datum) (a b : Fin (InstJ8.ns d)) (h1 : tabSfun d a = tabSfun d b)
    (h2 : loc (sz d) a = loc (sz d) b) : a = b := by
  obtain ⟨⟨s, l⟩, ha⟩ : ∃ x, (finSigmaFinEquiv (n := sz d)).symm a = x := ⟨_, rfl⟩
  obtain ⟨⟨s', l'⟩, hb⟩ : ∃ x, (finSigmaFinEquiv (n := sz d)).symm b = x := ⟨_, rfl⟩
  unfold tabSfun at h1
  unfold loc at h2
  rw [ha, hb] at h1 h2
  simp only at h1 h2
  subst h1
  have : l = l' := Fin.ext h2
  subst this
  exact (finSigmaFinEquiv (n := sz d)).symm.injective (ha.trans hb.symm)

section Greg
variable (I : Inst)

/-- the table (of the instance) of the `k`-th present constraint -/
noncomputable def tk (k : Fin I.R.ns') : Fin I.XI.tabs.size := Fin.cast I.hT (I.R.tabS' k)

/-- the J-8 table of the `k`-th present constraint -/
noncomputable def sOf (k : Fin I.R.ns') : Fin 6 := tabSfun I.d (I.R.ρ k)
/-- its local index -/
noncomputable def lOf (k : Fin I.R.ns') : ℕ := loc (sz I.d) (I.R.ρ k)
/-- its (DAG gate, coordinate) -/
noncomputable def rOf (k : Fin I.R.ns') : ℕ × ℕ := (rtJ8 I.d (sOf I k)).route (lOf I k)

theorem sOf_eq (k : Fin I.R.ns') : sigmaX I.XI (tk I k) = sOf I k := (I.hσ _).symm.trans (I.R.hρtab k)

theorem lOf_lt (k : Fin I.R.ns') : lOf I k < sz I.d (sOf I k) := ((finSigmaFinEquiv (n := sz I.d)).symm (I.R.ρ k)).2.2

set_option maxRecDepth 20000 in
theorem rOf_spec (k : Fin I.R.ns') :
    (rOf I k).1 < (rtJ8 I.d (sOf I k)).nK ∧ (rOf I k).2 < (rtJ8 I.d (sOf I k)).mult (rOf I k).1 ∧
      (rtJ8 I.d (sOf I k)).jOf (rOf I k).1 (rOf I k).2 = lOf I k :=
  (rtJ8 I.d (sOf I k)).h1 _ (by rw [rtJ8_N]; exact lOf_lt I k)

theorem rOf_crd_lt (k : Fin I.R.ns') : (rOf I k).2 < 3 :=
  lt_of_lt_of_le (rOf_spec I k).2.1 ((rtJ8 I.d (sOf I k)).hmult _)

theorem rOf_lt_cons (hsz : HSz I) (k : Fin I.R.ns') : (rOf I k).1 < I.XI.tabs[tk I k].chip.cons.size := by
  have h := (rOf_spec I k).1
  rw [← sOf_eq] at h
  rw [hsz]; exact h

theorem grp_lt (hsz : HSz I) (k : Fin I.R.ns') :
    ((sizes I.XI).take (tk I k).1).sum + (rOf I k).1 < nsK I.XI := by
  have ht : (tk I k).1 < (sizes I.XI).length := by rw [sizes_length]; exact (tk I k).2
  exact off_lt (sizes I.XI) _ _ ht (by rw [sizes_get]; exact rOf_lt_cons I hsz k)

/-- **`G`**: the present J-8 constraint `k` (table `t'`, DAG gate `ℓ`, coordinate `κ`) goes to the flat DAG gate `off t' + ℓ`
with coordinate `κ` -/
noncomputable def Gflat (hsz : HSz I) : Regroup I.R.ns' (nsK I.XI) where
  grp k := ⟨((sizes I.XI).take (tk I k).1).sum + (rOf I k).1, grp_lt I hsz k⟩
  crd k := ⟨(rOf I k).2, rOf_crd_lt I k⟩
  hinj j j' hg hc := by
    have hg' := congrArg Fin.val hg
    have hc' := congrArg Fin.val hc
    simp only at hg' hc'
    have ht : (tk I j).1 < (sizes I.XI).length := by rw [sizes_length]; exact (tk I j).2
    have ht' : (tk I j').1 < (sizes I.XI).length := by rw [sizes_length]; exact (tk I j').2
    obtain ⟨h1, h2⟩ := off_inj (sizes I.XI) _ _ _ _ ht ht' (by rw [sizes_get]; exact rOf_lt_cons I hsz j)
      (by rw [sizes_get]; exact rOf_lt_cons I hsz j') hg'
    have h1' : tk I j = tk I j' := Fin.ext h1
    have hs : sOf I j = sOf I j' := by rw [← sOf_eq, ← sOf_eq, h1']
    have hr : rOf I j = rOf I j' := Prod.ext h2 hc'
    have e1 := (rOf_spec I j).2.2
    have e2 := (rOf_spec I j').2.2
    rw [hs, hr] at e1
    have hl : lOf I j = lOf I j' := e1.symm.trans e2
    exact I.R.hρ (glob_ext I.d _ _ hs hl)

end Greg

/-! ## 7. columns, publics and valuations of the final interface -/

section Cols
variable (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)

theorem colI_mem (t : Fin I.XI.tabs.size) (c : ℕ) : I.R.p (colI (sigmaX I.XI t) c) :=
  (I.R.hp _).2 ⟨Fin.cast I.hT.symm t, by rw [I.hσ]; simp only [Fin.cast_cast, Fin.cast_eq_self]; exact (tabΙ_colI _ _).symm⟩

/-- the interface column of local column `c` of the instance's table `t` -/
noncomputable def colJ (t : Fin I.XI.tabs.size) (c : ℕ) : (I.JJ npub tp hcap).ι0 :=
  Sum.inl ⟨colI (sigmaX I.XI t) c, colI_mem I t c⟩

/-- the public column `s` of table `t` (the flat public index `pubBase + s`; a junk column out of range) -/
noncomputable def pubJ (t : Fin I.XI.tabs.size) (s : ℕ) : (I.JJ npub tp hcap).ι0 :=
  if h : I.XI.tabs[t].pubBase + s < npub then Sum.inr ⟨I.XI.tabs[t].pubBase + s, h⟩ else colJ I npub tp hcap t 0

/-- the valuation of `J8` induced by a valuation of the final interface (absent columns `0`) -/
noncomputable def val8 (val : (I.JJ npub tp hcap).ι0 × Fin (I.JJ npub tp hcap).r → NockvmE2E.Exec.KC) : Ι × Fin 2 → KN :=
  fun q => @dite _ (I.R.p q.1) (I.R.dp q.1) (fun h => val (Sum.inl ⟨q.1, h⟩, q.2)) (fun _ => 0)

theorem val8_apply (val : (I.JJ npub tp hcap).ι0 × Fin (I.JJ npub tp hcap).r → NockvmE2E.Exec.KC) (j : Ι) (h : I.R.p j)
    (k : Fin 2) : val8 I npub tp hcap val (j, k) = val (Sum.inl ⟨j, h⟩, k) := dif_pos h

theorem JJ_C_eq (χ : Coins Φ0 KN) (M : Msg) (j : Fin I.R.ns') :
    (I.JJ npub tp hcap).C χ M j = MvPolynomial.rename (Prod.map Sum.inl id) (I.Jm.C χ M j) := rfl

/-- `aeval` of a constraint of the final interface is `aeval` of the `J8` constraint at the induced valuation -/
theorem aeval_JJ_C (χ : Coins Φ0 KN) (M : Msg) (j : Fin I.R.ns') (val : (I.JJ npub tp hcap).ι0 × Fin (I.JJ npub tp hcap).r → NockvmE2E.Exec.KC) :
    MvPolynomial.aeval (R := ZMod NockvmE2E.Exec.p) val ((I.JJ npub tp hcap).C χ M j) =
      MvPolynomial.aeval (val8 I npub tp hcap val) ((J8 I.d I.hdk).C χ M (I.R.ρ j)) := by
  have h1 : MvPolynomial.aeval (R := ZMod NockvmE2E.Exec.p) val ((I.JJ npub tp hcap).C χ M j) =
      MvPolynomial.aeval (R := ZMod NockvmE2E.Exec.p) (val ∘ Prod.map Sum.inl id) (I.Jm.C χ M j) := by
    rw [JJ_C_eq]
    exact MvPolynomial.aeval_rename (Prod.map Sum.inl id) val _
  refine h1.trans ?_
  have h2 := aeval_minusT_C (A := KN) (J8 I.d I.hdk) I.R I.hfree χ M j (fun q => val (Prod.map Sum.inl id q))
  exact h2

/-- the coordinate weights -/
noncomputable def gbJ : Fin 3 → NockvmE2E.Exec.KC := ![1, NockvmE2E.Exec.xr, NockvmE2E.Exec.xr ^ 2]

theorem gbJ_cf (k : Fin 3) : gbJ k = cf k := by
  fin_cases k <;> simp [gbJ, cf] <;> exact rfl

end Cols

/-! ## 8. chip ids are injective on the instance's tables -/

theorem distinctB_nodup : ∀ l : List String, NockvmE2E.Exec.J8Shape.distinctB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [NockvmE2E.Exec.J8Shape.distinctB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨?_, distinctB_nodup l h.2⟩
    simpa using h.1

theorem tabIdx_inj : ∀ a b : String, a ∈ ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8"] →
    b ∈ ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8"] →
    tabIdx a = tabIdx b → a = b := by
  intro a b ha hb h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert h; decide)

theorem ids_of_shape {XI : ExecInst} (h : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) :
    (XI.tabs.toList.map (·.chip.id)).Nodup ∧ ∀ t ∈ XI.tabs.toList, t.chip.id ∈
      ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8"] := by
  have hm := InstJ8.mandOk_of_shape h
  unfold NockvmE2E.Exec.J8Shape.mandatoryOk at hm
  simp only [Bool.and_eq_true] at hm
  refine ⟨distinctB_nodup _ hm.1.1, fun t ht => ?_⟩
  have := hm.1.2
  simp only [List.all_eq_true] at this
  simpa using this t.chip.id (List.mem_map.mpr ⟨t, ht, rfl⟩)

/-- **`sigmaX` is injective** on the instance's tables (their chip ids are pairwise distinct J-8 chip names) -/
theorem sigmaX_inj (XI : ExecInst) (h : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) : Function.Injective (sigmaX XI) := by
  obtain ⟨hnd, hmem⟩ := ids_of_shape h
  intro a b hab
  have h1 : XI.tabs[a].chip.id = XI.tabs[b].chip.id :=
    tabIdx_inj _ _ (hmem _ (Array.getElem_mem_toList a.2)) (hmem _ (Array.getElem_mem_toList b.2)) hab
  have hnd' : (XI.tabs.toList.map (·.chip.id)).Nodup := hnd
  rw [List.nodup_iff_injective_get] at hnd'
  have := @hnd' ⟨a.1, by simp⟩ ⟨b.1, by simp⟩ (by simpa using h1)
  exact Fin.ext (by simpa using congrArg Fin.val this)

/-! ## 9. `htie` -/

/-- the flat constraint index `i` lives in the instance's table `tabX i` -/
def tabX (XI : ExecInst) (i : Fin (nsK XI)) : Fin XI.tabs.size :=
  ⟨(flatIdx (sizes XI) i.1).1, by have := flatIdx_fst_lt (sizes XI) i.1 i.2; simpa [sizes] using this⟩

instance instNeZeroJJ (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub) : NeZero (I.JJ npub tp hcap).r :=
  ⟨(by norm_num : (2 : ℕ) ≠ 0)⟩

/-- hop 0 for every loaded table (named hypothesis; discharged by the exe check `J8Chips`) -/
def HopsOK (I : Inst) (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) : Prop :=
  ∀ t : Fin I.XI.tabs.size,
    HopZero I.XI.tabs[t].chip (DOf I.d (sigmaX I.XI t)) ders cmeta I.XI.tabs[t].chip.baseCols ∧
      I.XI.tabs[t].chip.baseCols = bcOf (sigmaX I.XI t)

theorem hsz_of_hops (I : Inst) (ders cmeta) (hnum : ∀ t, NumOK I.d (sigmaX I.XI t)) (hops : HopsOK I ders cmeta) : HSz I :=
  fun t => consSize_of I.d ders cmeta _ (hnum t) _ (hops t).1

/-- what `pr.rd` hands the chip of table `t` (the public message read; `Mof` / `rd` plumbing): `PubsOK` reads only `env.pub` -/
def RdSpec (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub) (pr : PubRead (I.JJ npub tp hcap)) : Prop :=
  ∀ (v : (I.JJ npub tp hcap).ι0 → KN) (t : Fin I.XI.tabs.size) (env : KEnv),
    (∀ s, env.pub s = HdagU.coord0 (v (pubJ I npub tp hcap t s))) → PubsOK (pr.rd v) env (sigmaX I.XI t)

section HtieS
variable (I : Inst) (hsz : HSz I) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)

set_option maxRecDepth 8000 in
theorem gfilter (i : Fin (nsK I.XI)) :
    (Finset.univ.filter fun j : Fin I.R.ns' => (Gflat I hsz).grp j = i) =
      Finset.univ.filter fun j : Fin I.R.ns' => tk I j = tabX I.XI i ∧ (rOf I j).1 = (flatIdx (sizes I.XI) i.1).2 := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hi : i.1 < (sizes I.XI).sum := i.2
  have ht : (tk I j).1 < (sizes I.XI).length := by rw [sizes_length]; exact (tk I j).2
  have hfj := flatIdx_off (sizes I.XI) _ _ ht (by rw [sizes_get]; exact rOf_lt_cons I hsz j)
  constructor
  · intro h
    have h' : ((sizes I.XI).take (tk I j).1).sum + (rOf I j).1 = i.1 := congrArg Fin.val h
    rw [h'] at hfj
    have e1 : (tk I j).1 = (flatIdx (sizes I.XI) i.1).1 := (Prod.mk.inj hfj.symm).1
    exact ⟨Fin.ext e1, (Prod.mk.inj hfj.symm).2⟩
  · rintro ⟨h1, h2⟩
    apply Fin.ext
    show ((sizes I.XI).take (tk I j).1).sum + (rOf I j).1 = i.1
    have := flatIdx_inv (sizes I.XI) i.1 hi
    have h1' : (tk I j).1 = (flatIdx (sizes I.XI) i.1).1 := congrArg Fin.val h1
    rw [h1', h2]; exact this

end HtieS

section ImgT
variable (I : Inst)

set_option maxHeartbeats 400000 in
theorem himg_of (t' : Fin I.XI.tabs.size) (s : Fin 6) (hsd : s = sigmaX I.XI t') (l : ℕ) :
    (Finset.univ.filter fun j : Fin I.R.ns' => tk I j = t' ∧ (rOf I j).1 = l).image I.R.ρ =
      Finset.univ.filter (fun j' : Fin (InstJ8.ns I.d) =>
      ((finSigmaFinEquiv (n := sz I.d)).symm j').1 = s ∧ ((rtJ8 I.d s).route (loc (sz I.d) j')).1 = l) := by
  have hsj : ∀ j : Fin I.R.ns', tk I j = t' → sOf I j = s := by
    intro j hj
    rw [← sOf_eq, hj, hsd]
  have hrj : ∀ j : Fin I.R.ns', tk I j = t' → rOf I j = (rtJ8 I.d s).route (loc (sz I.d) (I.R.ρ j)) := by
    intro j hj
    unfold rOf lOf
    rw [hsj j hj]
  refine Finset.ext fun (j' : Fin (InstJ8.ns I.d)) => ?_
  constructor
  · intro hm
    obtain ⟨j, hj, hjj⟩ := Finset.mem_image.mp hm
    have hj' := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [← hjj]; exact hsj j hj'.2.1
    · rw [← hjj, ← hrj j hj'.2.1]; exact hj'.2.2
  · intro hm
    obtain ⟨-, h1, h2⟩ := (Finset.mem_filter).mp hm
    obtain ⟨k, hk⟩ : ∃ k, I.R.ρ k = j' := by
      obtain ⟨k, hk⟩ := I.R.hρcov j' (Fin.cast I.hT.symm t') (by
        rw [I.hσ]
        simp only [Fin.cast_cast, Fin.cast_eq_self]
        rw [← hsd]; exact h1.symm)
      exact ⟨k, hk⟩
    have hsk : sOf I k = s := by
      unfold sOf; rw [hk]; exact h1
    have htk : tk I k = t' := sigmaX_inj I.XI I.hsh (by rw [sOf_eq, hsk, hsd])
    refine Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htk, ?_⟩, hk⟩
    rw [hrj k htk, hk]; exact h2

end ImgT

section HtieMain
variable (I : Inst) (hsz : HSz I) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **`htie` at the final interface**: the regrouped constraint sum of the present J-8 constraints equals the loaded chip's DAG value,
under hop 0 (`HopsOK`), the slot facts (`hSlotOK`), the public reads (`RdSpec`) and the kroots numerals (`NumOK`). -/
theorem htie_J8 (pr : PubRead (I.JJ npub tp hcap)) (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ))
    (hnum : ∀ t, NumOK I.d (sigmaX I.XI t)) (hops : HopsOK I ders cmeta)
    (chalK : Coins (I.JJ npub tp hcap).Φ0 NockvmE2E.Exec.KC → ℕ → NockvmE2E.Exec.KC)
    (hSlotOK : ∀ χ : Coins (I.JJ npub tp hcap).Φ0 NockvmE2E.Exec.KC,
      NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta (chalK χ)) (χf χ))
    (hrd : RdSpec I npub tp hcap pr) :
    ∀ (i : Fin (nsK I.XI)) (χ : Coins (I.JJ npub tp hcap).Φ0 NockvmE2E.Exec.KC)
      (v val : (I.JJ npub tp hcap).ι0 × Fin (I.JJ npub tp hcap).r → NockvmE2E.Exec.KC),
      ∑ j ∈ Finset.univ.filter (fun j : Fin I.R.ns' => (Gflat I hsz).grp j = i),
          gbJ ((Gflat I hsz).crd j) *
            MvPolynomial.aeval val ((I.JJ npub tp hcap).C χ (pr.rd (fun c => v (c, 0))) j) =
        (evalDagK I.XI.tabs[tabX I.XI i].chip
          ⟨fun c => val (colJ I npub tp hcap (tabX I.XI i) c, 0),
           fun c => val (colJ I npub tp hcap (tabX I.XI i) c, ⟨1 % (I.JJ npub tp hcap).r, Nat.mod_lt _ (NeZero.pos _)⟩),
           fun s => HdagU.coord0 (v (pubJ I npub tp hcap (tabX I.XI i) s, 0)), chalK χ,
           I.XI.tabs[tabX I.XI i].chip.baseCols⟩)[(flatIdx (sizes I.XI) i.1).2]! := by
  intro i χ v val
  have hi : i.1 < (sizes I.XI).sum := i.2
  have hlt1 : (flatIdx (sizes I.XI) i.1).2 < I.XI.tabs[tabX I.XI i].chip.cons.size := by
    have h := flatIdx_snd_lt (sizes I.XI) i.1 hi
    have e := sizes_get I.XI (flatIdx (sizes I.XI) i.1).1 (flatIdx_fst_lt _ _ hi)
    exact lt_of_lt_of_eq h e
  set t' : Fin I.XI.tabs.size := tabX I.XI i with ht'e
  set l : ℕ := (flatIdx (sizes I.XI) i.1).2 with hle
  have hlt : l < (rtJ8 I.d (sigmaX I.XI t')).nK := by rw [← hsz t']; exact hlt1
  obtain ⟨hop, hbc⟩ := hops t'
  -- the chip environment of `htie`
  have hT : TieAt I.d χ (pr.rd (fun c => v (c, 0))) (val8 I npub tp hcap val)
      ⟨fun c => val (colJ I npub tp hcap t' c, 0),
       fun c => val (colJ I npub tp hcap t' c, ⟨1 % (I.JJ npub tp hcap).r, Nat.mod_lt _ (NeZero.pos _)⟩),
       fun s => HdagU.coord0 (v (pubJ I npub tp hcap t' s, 0)), chalK χ, I.XI.tabs[t'].chip.baseCols⟩
      I.XI.tabs[t'].chip (sigmaX I.XI t') := by
    refine tieAt I.d χ _ _ ders cmeta _ _ _ (hnum t') hop hbc hbc ?_ ?_ (hSlotOK χ) ?_
    · intro n hn
      show val (colJ I npub tp hcap t' n, 0) = val8 I npub tp hcap val (colI (sigmaX I.XI t') n, 0)
      rw [val8_apply I npub tp hcap _ _ (colI_mem I t' n)]
      rfl
    · intro n hn
      show val (colJ I npub tp hcap t' n, ⟨1 % (I.JJ npub tp hcap).r, _⟩) = val8 I npub tp hcap val (colI (sigmaX I.XI t') n, 1)
      rw [val8_apply I npub tp hcap _ _ (colI_mem I t' n)]
      rfl
    · exact hrd (fun c => v (c, 0)) t' _ (fun _ => rfl)
  have hT' := hT l hlt
  set M : Msg := pr.rd (fun c => v (c, 0)) with hM
  set s : Fin 6 := sigmaX I.XI t' with hsdef
  rw [gfilter I hsz i]
  set Fs : Finset (Fin I.R.ns') :=
    Finset.univ.filter (fun j : Fin I.R.ns' => tk I j = t' ∧ (rOf I j).1 = l) with hFs
  let Fg : Fin (InstJ8.ns I.d) → KN := fun j' =>
    MvPolynomial.aeval (val8 I npub tp hcap val) ((J8 I.d I.hdk).C χ M j')
  have hsj : ∀ j ∈ Fs, sOf I j = s := by
    intro j hj
    have hj' : tk I j = t' := (Finset.mem_filter.mp hj).2.1
    rw [← sOf_eq, hj']
  have hrj : ∀ j ∈ Fs, rOf I j = (rtJ8 I.d s).route (loc (sz I.d) (I.R.ρ j)) := by
    intro j hj
    unfold rOf lOf
    rw [hsj j hj]
  have hB : ∀ j ∈ Fs, gbJ ((Gflat I hsz).crd j) *
      MvPolynomial.aeval val ((I.JJ npub tp hcap).C χ M j) =
        cf ((rtJ8 I.d s).route (loc (sz I.d) (I.R.ρ j))).2 * Fg (I.R.ρ j) := by
    intro j hj
    rw [aeval_JJ_C I npub tp hcap χ M j val]
    have h1 : gbJ ((Gflat I hsz).crd j) = cf (rOf I j).2 := gbJ_cf _
    rw [h1, hrj j hj]
    rfl
  rw [Finset.sum_congr rfl hB]
  have himg : Fs.image I.R.ρ = _ := himg_of I t' s hsdef l
  have hsum := Finset.sum_image (s := Fs) (g := I.R.ρ)
    (f := fun j' : Fin (InstJ8.ns I.d) => cf ((rtJ8 I.d s).route (loc (sz I.d) j')).2 * Fg j')
    (fun a _ b _ h => I.R.hρ h)
  refine hsum.symm.trans ((Finset.sum_congr himg (fun _ _ => rfl)).trans ((fiber_global (InstJ8.sz I.d) (rtJ8 I.d) (rtJ8_N I.d) s l hlt Fg).trans ?_))
  refine Eq.trans (Finset.sum_congr rfl ?_) hT'
  intro k hk
  have hjl : (rtJ8 I.d s).jOf l k < sz I.d s := by
    have := ((rtJ8 I.d s).h2 l hlt k (Finset.mem_range.mp hk)).1
    rwa [rtJ8_N] at this
  rw [dif_pos hjl]
  congr 1
  have h3 := aeval_Cfun I.d χ M (val8 I npub tp hcap val) (finSigmaFinEquiv (n := sz I.d) ⟨s, ⟨_, hjl⟩⟩)
  rw [tabS_jglob, loc_jglob] at h3
  exact h3

end HtieMain

/-! ## 10. the domain binders: `hoff`, `hdom`, `hdomt`, `hinj` -/

theorem hShift_of_shape {XI : ExecInst} (h : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) : XI.hShift = 1 := by
  unfold NockvmE2E.Exec.J8Shape.j8ShapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

theorem omegaOf_eq (I : Inst) (s : Fin 6) : omegaOf I.d s = ω0 I.XI := by
  unfold omegaOf
  rw [I.hd]
  fin_cases s <;> rfl

theorem tabId_tabIdx (id : String)
    (h : id ∈ ["computeChipVCLHX", "cellChipHQKW", "walkChipJ8", "atomChipHQL", "walkChipHQK", "jetChipJ8"]) :
    tabId (tabIdx id) = id := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem tabId_sigmaX (XI : ExecInst) (hsh : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) (t : Fin XI.tabs.size) :
    tabId (sigmaX XI t) = XI.tabs[t].chip.id :=
  tabId_tabIdx _ ((ids_of_shape hsh).2 _ (Array.getElem_mem_toList t.2))

theorem find_tab (XI : ExecInst) (hsh : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) (t : Fin XI.tabs.size) :
    tabOf XI XI.tabs[t].chip.id = some XI.tabs[t] := by
  have hnd : (XI.tabs.toList.map (·.chip.id)).Nodup := (ids_of_shape hsh).1
  rw [List.nodup_iff_injective_get] at hnd
  unfold tabOf
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, t.1, by simpa using t.2, by simp, ?_⟩
  intro j hj
  by_contra hc
  have hjl : j < XI.tabs.toList.length := by have := t.2; simp; omega
  have hc' : XI.tabs.toList[j].chip.id = XI.tabs[t].chip.id := by simpa using hc
  have := @hnd ⟨j, by simpa using hjl⟩ ⟨t.1, by simpa using t.2⟩ (by simpa using hc')
  have := congrArg Fin.val this
  simp at this
  omega

theorem hNof_tab (XI : ExecInst) (hsh : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) (t : Fin XI.tabs.size) :
    hNof XI (tabId (sigmaX XI t)) = XI.tabs[t].hN := by
  rw [tabId_sigmaX XI hsh]
  unfold hNof
  rw [find_tab XI hsh]
  rfl

theorem rowNodeSet_pows {n : ℕ} (a : ZMod InstJ8.P) (nodes : Fin n → ZMod InstJ8.P) (h : ∀ i, nodes i = a ^ (i : ℕ)) :
    Nock.Framework.rowNodeSet nodes = (Finset.range n).image (fun i => a ^ i) := by
  ext x
  unfold Nock.Framework.rowNodeSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, (h i).symm⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, h _⟩

theorem HtOf_eq (I : Inst) (s : Fin 6) (hs : s = 5 → (tabOf I.XI "walkChipHQK").isSome = true) :
    HtOf I.d s = (Finset.range (hNof I.XI (tabId s))).image (fun i => ω0 I.XI ^ i) := by
  unfold HtOf
  rw [I.hd]
  fin_cases s
  · exact rowNodeSet_pows _ _ (fun i => rfl)
  · exact rowNodeSet_pows _ _ (fun i => rfl)
  · exact rowNodeSet_pows _ _ (fun i => rfl)
  · exact rowNodeSet_pows _ _ (fun i => rfl)
  · exact rowNodeSet_pows _ _ (fun i => rfl)
  · have h5 := hs rfl
    have := rowNodeSet_pows (ω0 I.XI) (PbOfX I.XI I.hsh I.hpos I.kroots I.krootsV I.Rt I.regs I.ids I.idx I.rk I.lay).nodesV
      (fun i => rfl)
    refine this.trans ?_
    show (Finset.range (if (tabOf I.XI "walkChipHQK").isSome then hNof I.XI "walkChipHQK" else 1)).image _ = _
    rw [if_pos h5]
    rfl

section DomJ
variable (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)

/-- `hoff` -/
theorem hoff_J8 (t : Fin (I.JJ npub tp hcap).T) (k : Fin (I.JJ npub tp hcap).r) :
    (I.JJ npub tp hcap).off t k = ω0 I.XI ^ k.1 := by
  exact congrArg (· ^ (k : ℕ)) (omegaOf_eq I (I.R.σ t))

/-- `hdom` -/
theorem hdom_J8 : (I.JJ npub tp hcap).H = (Finset.range I.XI.hN).image
    (fun i => NockvmE2E.Exec.VL.zv I.XI.hShift * NockvmE2E.Exec.VL.zv I.XI.hGen ^ i) :=
  InstJ8.H_J8_eq I.XI I.d I.hdk (hShift_of_shape I.hsh) I.hdN I.hdω

/-- `hdomt` (the tabJ of the bundle is `Fin.cast`) -/
theorem hdomt_J8 (t : Fin I.XI.tabs.size) :
    (I.JJ npub tp hcap).Ht (Fin.cast I.hT.symm t) = (Finset.range I.XI.tabs[t].hN).image
      (fun i => NockvmE2E.Exec.VL.zv I.XI.hShift * NockvmE2E.Exec.VL.zv I.XI.hGen ^ i) := by
  have hs : sigmaX I.XI t = 5 → (tabOf I.XI "walkChipHQK").isSome = true := by
    intro h5
    have h1 := tabId_sigmaX I.XI I.hsh t
    rw [h5] at h1
    have h2 : I.XI.tabs[t].chip.id = "walkChipHQK" := h1.symm
    rw [h2.symm, find_tab I.XI I.hsh]
    rfl
  show HtOf I.d (I.R.σ (Fin.cast I.hT.symm t)) = _
  rw [I.hσ, Fin.cast_cast, Fin.cast_eq_self, HtOf_eq I _ hs, hNof_tab I.XI I.hsh, hShift_of_shape I.hsh,
    NockvmE2E.Exec.VL.zv_one]
  simp only [one_mul]
  rfl

/-- `hinj` -/
theorem hinj_J8 : Set.InjOn (fun i => NockvmE2E.Exec.VL.zv I.XI.hShift * NockvmE2E.Exec.VL.zv I.XI.hGen ^ i)
    (Finset.range I.XI.hN : Set ℕ) := by
  rw [hShift_of_shape I.hsh, NockvmE2E.Exec.VL.zv_one]
  intro a ha b hb hab
  simp only [one_mul] at hab
  have hinj := InstJ8.inj_pows I.hsh (n := I.XI.hN) le_rfl
  have ha' : a < I.XI.hN := by simpa using ha
  have hb' : b < I.XI.hN := by simpa using hb
  have := hinj (a₁ := ⟨a, ha'⟩) (a₂ := ⟨b, hb'⟩) hab
  exact congrArg Fin.val this

end DomJ

/-! ## 11. `hslot`: the coin of verifier slot `q` -/

section Slot
variable (Φ : CoinFrame)

theorem lt_of_sa (i : Fin (extFrame Φ 2).n) (h : (extFrame Φ 2).sampledAfter i < 2) : i.1 < Φ.n := by
  by_contra hc
  simp [extFrame, hc] at h
  omega

/-- the coin of slot `q`: the round-0 coins in `sl0` order, then the round-1 coins in `sl1` order -/
noncomputable def chalK {n0 n1 : ℕ} (sl0 : {i : Fin (extFrame Φ 2).n // (extFrame Φ 2).sampledAfter i = 0} ≃ Fin n0)
    (sl1 : {i : Fin (extFrame Φ 2).n // (extFrame Φ 2).sampledAfter i = 1} ≃ Fin n1) (χ : Coins Φ KC) (q : ℕ) : KC :=
  if h : q < n0 then χ ⟨(sl0.symm ⟨q, h⟩).1.1, lt_of_sa Φ _ (by rw [(sl0.symm ⟨q, h⟩).2]; norm_num)⟩
  else if h : q - n0 < n1 then χ ⟨(sl1.symm ⟨q - n0, h⟩).1.1, lt_of_sa Φ _ (by rw [(sl1.symm ⟨q - n0, h⟩).2]; norm_num)⟩ else 0

theorem chi_blk (c0 : Block (extFrame Φ 2) KC 0) (c1 : Block (extFrame Φ 2) KC 1) (c2 : Block (extFrame Φ 2) KC 2)
    (c3 : Block (extFrame Φ 2) KC 3) (i : Fin (extFrame Φ 2).n) :
    (∀ h : (extFrame Φ 2).sampledAfter i = 0, chiOfBlocks c0 c1 c2 c3 i = c0 ⟨i, h⟩) ∧
    (∀ h : (extFrame Φ 2).sampledAfter i = 1, chiOfBlocks c0 c1 c2 c3 i = c1 ⟨i, h⟩) := by
  constructor
  · intro h
    simp [chiOfBlocks, setBlock, h]
  · intro h
    simp [chiOfBlocks, setBlock, h]

theorem hslot_gen (XI : ExecInst) (hder : XI.derived = #[]) {n0 n1 : ℕ} (hn0 : XI.nCoins[0]! = n0) (hn1 : XI.nCoins[1]! = n1)
    (sl0 : {i : Fin (extFrame Φ 2).n // (extFrame Φ 2).sampledAfter i = 0} ≃ Fin n0)
    (sl1 : {i : Fin (extFrame Φ 2).n // (extFrame Φ 2).sampledAfter i = 1} ≃ Fin n1)
    (c0 : Block (extFrame Φ 2) KC 0) (c1 : Block (extFrame Φ 2) KC 1) (c2 : Block (extFrame Φ 2) KC 2)
    (c3 : Block (extFrame Φ 2) KC 3) (q : ℕ) (hq : q < n0 + n1) :
    toKV (slotsAt XI (blockEnc sl0 c0) (blockEnc sl1 c1))[q]! = chalK Φ sl0 sl1 (restr 2 (chiOfBlocks c0 c1 c2 c3)) q := by
  have hsl : slotsAt XI (blockEnc sl0 c0) (blockEnc sl1 c1) =
      NockvmE2E.Exec.V.k3s (blockEnc sl0 c0) n0 ++ NockvmE2E.Exec.V.k3s (blockEnc sl1 c1) n1 := by
    simp [slotsAt, hder, hn0, hn1]
  rw [hsl]
  have hs0 : (NockvmE2E.Exec.V.k3s (blockEnc sl0 c0) n0).size = n0 := by simp [NockvmE2E.Exec.V.k3s]
  unfold chalK
  by_cases h0 : q < n0
  · rw [dif_pos h0, getElem!_pos _ _ (by simp [NockvmE2E.Exec.V.k3s]; omega), Array.getElem_append_left (by simp [NockvmE2E.Exec.V.k3s]; omega)]
    simp only [NockvmE2E.Exec.V.k3s, Array.getElem_map, Array.getElem_range]
    have := blockEnc_slot sl0 c0 ⟨q, h0⟩
    refine this.trans ?_
    have hb := (chi_blk Φ c0 c1 c2 c3 (sl0.symm ⟨q, h0⟩).1).1 (sl0.symm ⟨q, h0⟩).2
    simp only [restr, extC]
    exact hb.symm
  · have h1 : q - n0 < n1 := by omega
    rw [dif_neg h0, dif_pos h1]
    have hb1 : q - n0 < (NockvmE2E.Exec.V.k3s (blockEnc sl1 c1) n1).size := by simp [NockvmE2E.Exec.V.k3s]; exact h1
    have e1 : (NockvmE2E.Exec.V.k3s (blockEnc sl0 c0) n0 ++ NockvmE2E.Exec.V.k3s (blockEnc sl1 c1) n1)[q]! =
        (NockvmE2E.Exec.V.k3s (blockEnc sl1 c1) n1)[q - n0]! := by
      rw [getElem!_pos _ q (by simp [NockvmE2E.Exec.V.k3s]; omega), getElem!_pos (NockvmE2E.Exec.V.k3s (blockEnc sl1 c1) n1) (q - n0) hb1,
        Array.getElem_append_right (by simp [NockvmE2E.Exec.V.k3s]; omega)]
      simp only [hs0]
    rw [e1, getElem!_pos (NockvmE2E.Exec.V.k3s (blockEnc sl1 c1) n1) (q - n0) hb1]
    simp only [NockvmE2E.Exec.V.k3s, Array.getElem_map, Array.getElem_range]
    refine (blockEnc_slot sl1 c1 ⟨q - n0, h1⟩).trans ?_
    have hb := (chi_blk Φ c0 c1 c2 c3 (sl1.symm ⟨q - n0, h1⟩).1).2 (sl1.symm ⟨q - n0, h1⟩).2
    simp only [restr, extC]
    exact hb.symm

end Slot

/-! ## 12. the bundle -/

section Bundle
open NockvmE2E.Exec.Cover NockvmE2E.Succ NockvmE2E.Deep Fri.Spec Domain
open scoped NNReal

variable (I : Inst) (npub : ℕ) (tp : Fin I.Jm.T) (hcap : I.Cap npub)

theorem htabS_J8 (hsz : HSz I) (j : Fin I.R.ns') :
    (I.JJ npub tp hcap).tabS j = Fin.cast I.hT.symm (tabX I.XI ((Gflat I hsz).grp j)) := by
  apply Fin.ext
  have ht : (tk I j).1 < (sizes I.XI).length := by rw [sizes_length]; exact (tk I j).2
  have := flatIdx_off (sizes I.XI) _ _ ht (by rw [sizes_get]; exact rOf_lt_cons I hsz j)
  show (I.R.tabS' j).1 = (flatIdx (sizes I.XI) _).1
  rw [show ((Gflat I hsz).grp j).1 = ((sizes I.XI).take (tk I j).1).sum + (rOf I j).1 from rfl, this]
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **`hdagU` at the J-8 interface**: the `hdagU_of_tie` conclusion for `plusJ ∘ minusT (R) (J8 d hd)` with the regroup `Gflat`.
NAMED hypotheses: `hops` (hop 0, loaded chips = emitted: exe check `J8Chips`), `hnum` (kroots numerals), `hSlotOK` (`SlotOK` of the loader's
`ders`/`cmeta` at the slot order `sl0 ++ sl1`), `hrd` (the message read of `pr.rd`), `hpre0` / `hcur1` (fixed columns: `none` off `preIdxJ8`;
mask polynomials, `maskOk`), `hcI_*` (layout of `cI`), `hnpub`. Everything else is proved here. -/
theorem hdagU_J8 (hnpub : npub = I.XI.pubOf.size) (pr : PubRead (I.JJ npub tp hcap)) {n : ℕ}
    (ω : SmoothCosetFftDomain n KC) (δ : NNReal) (N : ℕ) (hNH : N ≤ (I.JJ npub tp hcap).H.card)
    (hpd : ∀ j c, (I.JJ npub tp hcap).pre j = some c → c.natDegree ≤ (I.JJ npub tp hcap).H.card)
    (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ)) (hnum : ∀ t, NumOK I.d (sigmaX I.XI t))
    (hops : HopsOK I ders cmeta) (hrd : RdSpec I npub tp hcap pr) {n0 n1 : ℕ}
    (sl0 : {i : Fin (extFrame (I.JJ npub tp hcap).Φ0 2).n // (extFrame (I.JJ npub tp hcap).Φ0 2).sampledAfter i = 0} ≃ Fin n0)
    (sl1 : {i : Fin (extFrame (I.JJ npub tp hcap).Φ0 2).n // (extFrame (I.JJ npub tp hcap).Φ0 2).sampledAfter i = 1} ≃ Fin n1)
    (hn0 : I.XI.nCoins[0]! = n0) (hn1 : I.XI.nCoins[1]! = n1)
    (hSlotOK : ∀ χ : Coins (I.JJ npub tp hcap).Φ0 KC,
      NockvmE2E.Emit.SlotOK (NockvmE2E.Exec.DagSemV.chalE ders cmeta (chalK (I.JJ npub tp hcap).Φ0 sl0 sl1 χ)) (χf χ))
    (cI : (I.JJ npub tp hcap).ι0 ≃ Fin I.XI.nc)
    (hcI_col : ∀ (t : Fin I.XI.tabs.size) c, c < I.XI.tabs[t].nc - I.XI.tabs[t].npub →
      ((cI (colJ I npub tp hcap t c) : Fin I.XI.nc) : ℕ) = I.XI.tabs[t].col0 + c)
    (hcI_pub : ∀ (t : Fin I.XI.tabs.size) s, s < I.XI.tabs[t].npub →
      ((cI (pubJ I npub tp hcap t s) : Fin I.XI.nc) : ℕ) = I.XI.pubOf[I.XI.tabs[t].pubBase + s]!)
    (hpre0 : ∀ (t : Fin I.XI.tabs.size) c, c < I.XI.tabs[t].nc - I.XI.tabs[t].npub →
      I.XI.colKind[I.XI.tabs[t].col0 + c]! = 0 → (I.JJ npub tp hcap).pre (colJ I npub tp hcap t c) = none)
    (hcur1 : ∀ (t : Fin I.XI.tabs.size) c, c < I.XI.tabs[t].nc - I.XI.tabs[t].npub → I.XI.colKind[I.XI.tabs[t].col0 + c]! = 1 →
      (I.JJ npub tp hcap).pre (colJ I npub tp hcap t c) = some (((List.range I.XI.pre[I.XI.tabs[t].col0 + c]!.size).map fun m =>
        Polynomial.monomial m (zv (I.XI.pre[I.XI.tabs[t].col0 + c]!)[m]!)).sum)) :
    ∀ (c0 : Block (extFrame (I.JJ npub tp hcap).Φ0 2) KC 0) (c1 : Block (extFrame (I.JJ npub tp hcap).Φ0 2) KC 1)
      (c2 : Block (extFrame (I.JJ npub tp hcap).Φ0 2) KC 2) (c3 : Block (extFrame (I.JJ npub tp hcap).Φ0 2) KC 3)
      (ζ : VF.K3) (vT : Array (Array VF.K3)),
      CanonIn (slotsAt I.XI (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT →
      ∀ i : Fin (((deepParamsJ (I.JJ npub tp hcap) pr ω δ N hNH hpd).regroup
          (Gflat I (hsz_of_hops I ders cmeta hnum hops)) gbJ)).ns,
        (termsAt I.XI (slotsAt I.XI (blockEnc sl0 c0) (blockEnc sl1 c1)) ζ vT)[i.1]? =
          some (((airJ (I.JJ npub tp hcap) pr ω δ N hNH hpd).regroup (Gflat I (hsz_of_hops I ders cmeta hnum hops)) gbJ).Cv
            (chiOfBlocks c0 c1 c2 c3) (toKV ζ) i (vTOfG I.XI cI (I.JJ npub tp hcap).r vT)) := by
  have hsz := hsz_of_hops I ders cmeta hnum hops
  obtain ⟨hread, hcanon, hpreC, hS, hle, hcolB, hpubB, hnpubB, hkind, hr2⟩ :=
    NockvmE2E.Exec.J8Shape.hdagU_shape_of_j8 I.hsh
  have hc19 := NockvmE2E.Exec.J8Shape.coins19_of_shape I.hsh
  refine HdagU.hdagU_of_tie (I.JJ npub tp hcap) pr ω δ N hNH hpd I.XI (Gflat I hsz) gbJ (blockEnc sl0) (blockEnc sl1)
    (vTOfG I.XI cI (I.JJ npub tp hcap).r) rfl (tabX I.XI) (fun t => Fin.cast I.hT.symm t) (htabS_J8 I npub tp hcap hsz)
    (fun _ => rfl) (colJ I npub tp hcap) (pubJ I npub tp hcap) hread hcanon hpreC hS hle hcolB hpubB hnpubB hkind ?_ hcur1 ?_ hr2 rfl
    (fun t k => hoff_J8 I npub tp hcap t k) (chalK (I.JJ npub tp hcap).Φ0 sl0 sl1) ?_ (hdom_J8 I npub tp hcap)
    (fun t => hdomt_J8 I npub tp hcap t) (hinj_J8 I) (htie_J8 I hsz npub tp hcap pr ders cmeta hnum hops
      (chalK (I.JJ npub tp hcap).Φ0 sl0 sl1) hSlotOK hrd)
  · intro t c hc hk
    refine ⟨hpre0 t c hc hk, fun vT k => ?_⟩
    have e := hcI_col t c hc
    have hk' : I.XI.colKind[(cI (colJ I npub tp hcap t c) : ℕ)]! = 0 := by rw [e]; exact hk
    simp only [vTOfG, hk', e]
    rw [if_neg (fun h2 => by have := hk.symm.trans h2; omega)]
  · intro t s vT hs
    have e := hcI_pub t s hs
    simp only [vTOfG]
    rw [e]
    simp
  · intro c0 c1 c2 c3 q hq
    exact hslot_gen _ I.XI (NockvmE2E.Exec.J8Shape.derived_of_shape I.hsh) hn0 hn1 sl0 sl1 c0 c1 c2 c3 q (by subst hn0 hn1; omega)

end Bundle

/-! ## 13. the instance of the final theorem -/

/-- the `Inst` of the final theorem: `R := RJ8 XI d hd`, `hfree := hfree_J8 …` (so `Jm = minusT (J8 d hd) (RJ8 …) (hfree_J8 …)`, `rfl`) -/
noncomputable def Inst.ofRJ8 (XI : ExecInst) (hsh : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) (hpos : PosX XI) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → Nock.Jet.ChipJ8.PRow) (d : Datum)
    (hd : d.Pb = PbOfX XI hsh hpos kroots krootsV Rt regs ids idx rk lay) (hdk : DatumOK d) (hdN : d.hN = XI.hN) (hdω : d.ω = ω0 XI) :
    Inst where
  XI := XI
  hsh := hsh
  hpos := hpos
  kroots := kroots
  krootsV := krootsV
  Rt := Rt
  regs := regs
  ids := ids
  idx := idx
  rk := rk
  lay := lay
  d := d
  hd := hd
  hdk := hdk
  hdN := hdN
  hdω := hdω
  R := RJ8 XI d hdk
  hT := rfl
  hσ := fun _ => rfl
  hfree := hfree_J8 XI hsh hpos kroots krootsV Rt regs ids idx rk lay d hd hdk

theorem Inst.ofRJ8_Jm (XI : ExecInst) (hsh : NockvmE2E.Exec.J8Shape.j8ShapeOk XI = true) (hpos : PosX XI) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → Nock.Jet.ChipJ8.PRow) (d : Datum)
    (hd : d.Pb = PbOfX XI hsh hpos kroots krootsV Rt regs ids idx rk lay) (hdk : DatumOK d) (hdN : d.hN = XI.hN) (hdω : d.ω = ω0 XI) :
    (Inst.ofRJ8 XI hsh hpos kroots krootsV Rt regs ids idx rk lay d hd hdk hdN hdω).Jm =
      minusT (J8 d hdk) (RJ8 XI d hdk) (hfree_J8 XI hsh hpos kroots krootsV Rt regs ids idx rk lay d hd hdk) := rfl

end NockvmE2E.J8.TieJ8G

#print axioms NockvmE2E.J8.TieJ8G.Gflat
#print axioms NockvmE2E.J8.TieJ8G.htie_J8
#print axioms NockvmE2E.J8.TieJ8G.hdagU_J8
#print axioms NockvmE2E.J8.TieJ8G.hdomt_J8
#print axioms NockvmE2E.J8.TieJ8G.hinj_J8
#print axioms NockvmE2E.J8.TieJ8G.hslot_gen
#print axioms NockvmE2E.J8.TieJ8G.htabS_J8
#print axioms NockvmE2E.J8.TieJ8G.sigmaX_inj
#print axioms NockvmE2E.J8.TieJ8G.tieAt
#print axioms NockvmE2E.J8.TieJ8G.consSize_of
#print axioms NockvmE2E.J8.TieJ8G.Inst.ofRJ8_Jm
