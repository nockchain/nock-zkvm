/-
C2 (`E2EJ9ALP`): the J-9 AL twin of `J9A/E2EJ9AP.lean`: the chip constraint counts of the nine tables from
hop 0 (`consSize9L`, `hsz9L`, no `ders` argument: `dersL`), the instance atoms (`hat9L`), and `hrd9L` (the public read at the generic interface,
`PubJ9LP` / `Mof9L`).  `hχ_F` of `E2EJ9AP` is generic over `F` and is reused unchanged.  Not zero-knowledge.
-/
import NockvmE2E.J9A.E2EJ9AP
import NockvmE2E.J9AL.HtieJ9AL
import NockvmE2E.J9AL.PubSoundJ9AL
import NockvmE2E.J9AL.E2EJ9ALQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.J9AL.E2EJ9ALP

open NockvmE2E.J8 NockvmE2E.J8.TieJ8 NockvmE2E.Rap NockvmE2E.Emit Nock.Emit
open NockvmE2E.Exec NockvmE2E.Exec.DagSem NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen
open NockvmE2E.Exec.E2EGen NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.E2EJ8P2 NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.TieJ9A NockvmE2E.J9A.GenJ9A
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.TieJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.TieAluJ9AL NockvmE2E.J9AL.LagrJ9AL
open NockvmE2E.J8.InstJ8 (P Φ0 ω0)
open NockvmE2E.J9A.E2EJ9AP (consSize9 hat9 readPub_eq_G)

/-! ## 1. constraint counts -/

section Cons
variable (d : Datum9AL) (ders : Array NockvmE2E.Exec.Aux.Der) (cmeta : Array (ℕ × ℕ))

theorem consSize9L (s : Fin 9) (hnum : NumOK9L d s) (ch : NockvmE2E.Exec.Tr.Chip)
    (hop : HopZero ch (DOf9L d s) ders cmeta ch.baseCols) : ch.cons.size = (rt9L d s).nK := by
  by_cases h8 : s = 8
  · subst h8
    let env0 : KEnv := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 83⟩
    have hsz : (evalDagK ch env0).size = ch.cons.size := by simp [evalDagK]
    rw [← hsz]
    have hv := evalDagK_hop ch _ _ (decL_of_decR NockvmE2E.J9AL.TieAluJ9AL.decR_alu) ders cmeta hop env0
    rw [show (Nock.Emit.aluSpec).gates = ((TSpec.ofTemplate Nock.Emit.aluTemplate).rename Nock.Emit.fL id id).gates from rfl,
      dagVals_nc Nock.Emit.aluTemplate rfl rfl rfl rfl Nock.Emit.fL] at hv
    have h1 := congrArg List.length hv; rw [Array.length_toList] at h1
    rw [h1, length_tplVals]; rfl
  · obtain ⟨s', rfl⟩ : ∃ s' : Fin 8, s = s'.castSucc := ⟨⟨s.val, by omega⟩, Fin.ext rfl⟩
    rw [rt9L_old]
    rw [NumOK9L_old] at hnum
    rw [DOf9L_old] at hop
    exact consSize9 d.toA ders cmeta s' hnum ch hop

end Cons

section Sizes
variable {XI : ExecInst} (hsh : shapeOkF famJ9AL XI = true) (d : Datum9AL) (hdk : DatumOK9AL d) (L : Link9L XI d)
  (R : TabRestr (J9AL d hdk)) (hT : R.T' = XI.tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigma9L XI (Fin.cast hT t)) (hfree : (J9AL d hdk).AccOn R.q)

theorem hsz9L (cmeta : Array (ℕ × ℕ))
    (hnum : ∀ t : Fin XI.tabs.size, NumOK9L d (sigma9L XI t))
    (hop : ∀ t : Fin XI.tabs.size, HopZero XI.tabs[t].chip (DOf9L d (sigma9L XI t)) (dersL (sigma9L XI t)) cmeta
      XI.tabs[t].chip.baseCols ∧ XI.tabs[t].chip.baseCols = bcOf9L (sigma9L XI t)) :
    HSzG (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) :=
  fun t => consSize9L d (dersL (sigma9L XI t)) cmeta _ (hnum t) _ (hop t).1

end Sizes

/-! ## 2. the public read at the generic interface -/

section Rd
open NockvmE2E.Exec.E2EJ8P (readPub readPub_get)
open NockvmE2E.Exec.E2EJ8P2 (canonPub canon_cf)
open NockvmE2E.Exec.E2EFinal NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EFri
open NockvmE2E.Lift NockvmE2E.Lift.Alternating

/-- the instance atoms are canonical (from the J-9 AL datum link) -/
theorem hat9L (d : Datum9AL) (inp : PE.PubIn) (hlink : NockvmE2E.J9AL.RVUJ9AL.InpLink9L d inp) :
    ∀ a ∈ inp.atoms, a.2 < NockvmE2E.Exec.p := hat9 d.toA inp hlink.toA

/-- **`hrd` at J-9 AL**: the exec chain carries the J-9 AL public relation `PubJ9LP` (`pubMode = 3`, `PubSound`) -/
theorem hrd9L {XI : ExecInst} (hsh : shapeOkF famJ9AL XI = true) (d : Datum9AL) (hdk : DatumOK9AL d) (L : Link9L XI d)
    (R : TabRestr (J9AL d hdk)) (hT : R.T' = XI.tabs.size)
    (hσ : ∀ t : Fin R.T', R.σ t = sigma9L XI (Fin.cast hT t)) (hfree : (J9AL d hdk).AccOn R.q)
    (npub : ℕ) (tp) (hcap) (hnpub : npub = XI.pubOf.size)
    (hlink : NockvmE2E.J9AL.RVUJ9AL.InpLink9L d XI.pubIn)
    {M0 : Type} (m0 : M0) (nq : ℕ) (slots : Array VF.K3) (vT : Array (Array VF.K3)) (vQ : Array VF.K3) (hv : VShape XI vT vQ)
    (hP : NockvmE2E.J9AL.RVUJ9AL.PubJ9LP XI.pubIn XI.pubLay XI.slotOf slots (pubAt XI vT)) :
    ∃ pub : Array UInt64, (∀ g ∈ pub, canon g) ∧ NockvmE2E.J9AL.RVUJ9AL.PubJ9LP XI.pubIn XI.pubLay XI.slotOf slots pub ∧
      (prG (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap).rd
        (fun c => (finDecG XI (cIG (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap hnpub)
          ((InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).JJ npub tp hcap).r nq m0 (deepMsg vT vQ)).2.1 (c, 0)) =
        NockvmE2E.J9AL.InstJ9AL.Mof9L XI.pubLay pub := by
  refine ⟨canonPub (pubAt XI vT), ?_, NockvmE2E.J9AL.PubSoundJ9AL.pubJ9LP_canon _ _ _ _ _ (hat9L d _ hlink) hP, ?_⟩
  · intro g hg
    obtain ⟨a, -, rfl⟩ := Array.mem_map.mp hg
    exact canon_cf a
  · show NockvmE2E.J9AL.InstJ9AL.Mof9L XI.pubLay (readPub npub (fun j => (finDecG XI (cIG (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap hnpub)
      ((InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree).JJ npub tp hcap).r nq m0 (deepMsg vT vQ)).2.1 (Sum.inr j, 0))) = _
    rw [readPub_eq_G (InstG.ofJ9AL XI hsh d hdk L R hT hσ hfree) npub tp hcap hnpub (by show (2 : ℕ) = XI.r; exact (r_of_shapeF hsh).symm)
      (hkd_F hsh) m0 nq vT vQ hv]

end Rd

end NockvmE2E.J9AL.E2EJ9ALP

#print axioms NockvmE2E.J9AL.E2EJ9ALP.consSize9L
#print axioms NockvmE2E.J9AL.E2EJ9ALP.hsz9L
#print axioms NockvmE2E.J9AL.E2EJ9ALP.hat9L
#print axioms NockvmE2E.J9AL.E2EJ9ALP.hrd9L
