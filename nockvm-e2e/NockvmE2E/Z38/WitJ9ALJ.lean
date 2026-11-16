/-
NockvmE2E/Z38/WitJ9ALJ.lean

`witness9LJ`: the datum-side witness `Wit9LJ XI c Q` of the template-jet headline from the link gate's proposition `LinkOK9LJ XI c`, the family shape, `pregOkF`,
`jetPreOkF` and the canonicity of the public input; and `linkGate9LJ_wit` (the runtime gate gives it).  Twin of `J9AL/WitJ9AL.lean` (`witness9L`).
Not zero-knowledge.
-/
import NockvmE2E.Z38.DatX9LJOk
import NockvmE2E.Z38.PreJBridge
import NockvmE2E.J9AL.WitJ9AL
import NockvmE2E.J9AL.RunGate9LVRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Z38.WitJ9ALJ

open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.GenJ9AL NockvmE2E.J9AL.PbOfX9L NockvmE2E.J9AL.PregJ9AL
  NockvmE2E.J9AL.InstJ9ALW NockvmE2E.J9AL.LagrJ9AL NockvmE2E.J9AL.RVUJ9AL
open NockvmE2E.J9AL.WitJ9AL (hprim_PbOfX9L sigma9L_castSucc sigma9L_alu numOf9L_last)
open NockvmE2E.J9AL.RunGate9LVRun (primsCan_of_inpCanOkL)
open NockvmE2E.J9A.RunGate9L (PrimsLink kOfL kVOfL pregOkF inpCanOkL)
open NockvmE2E.J8.InstJ8 (P tabOf hNof)
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open NockvmE2E.Z38.JetPre (layJ regsOfPub idxOfPub rkOfPub jetPreOkF)
open NockvmE2E.Z38.IfaceJ (layOfX DX9LJ Wit9LJ PreJLink)
open NockvmE2E.Z38.DatX9LJOk (PbJ link9L_DX9LJ datX9LJ_ok hpin_PbOfX9LJ layout_ofFn CNJ)
open NockvmE2E.Z38.PreJBridge (preJLink_of_jetPreOkF)
open NockvmE2E.Z38.RunGate9LJ (LinkOK9LJ LinkBaseLJ JetLink linkGate9LJ)

noncomputable section

theorem witness9LJ (XI : ExecInst) (c : P8PublicClaim) (h : shapeOkF famJ9AL XI = true)
    (hpreg : pregOkF XI = true) (hjp : jetPreOkF XI = true) (hcan : PrimsCan XI.pubIn) (hL : LinkOK9LJ XI c)
    (Q : Datum9AL → Prop)
    (hQ : ∀ hlen : (layJ XI.pubIn).length = hNof XI "jetChipJ8", Q (DX9LJ XI h hlen (kOfL XI) (kVOfL XI) c)) :
    Wit9LJ XI c Q := by
  obtain ⟨hB, hJ⟩ := hL
  obtain ⟨hk1, hkW, hV, hV0, ⟨hc1, hc2, hc3⟩, hcl, hat, hnum, hnumL, hpJ, hpV, hpX, hpS, hpl⟩ := hB
  have hJ' := hJ
  obtain ⟨hlen, jPB, jPN, jRC, jRN, jD, jS, jU, jCl⟩ := hJ'
  obtain ⟨hdk, hS⟩ := datX9LJ_ok XI h hlen (kOfL XI) (kVOfL XI) hk1 hkW hV hV0 c ⟨hc1, hc2, hc3⟩ hpreg hpl hJ
  obtain ⟨hrt, hprb, hnd, -, -, -, habs⟩ := hpl
  refine ⟨DX9LJ XI h hlen (kOfL XI) (kVOfL XI) c, hdk, link9L_DX9LJ XI h hlen _ _ c, hS,
    ⟨⟨hcl, hpin_PbOfX9LJ XI jRN jPN, hat⟩, ?_⟩, hcan, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨RJ9AL XI _ hdk, rfl, fun _ => rfl,
      hfree_J9AL XI h _ _ CNJ.Rt (regsOfPub XI.pubIn) XI.pubIn.calls (idxOfPub XI.pubIn) (rkOfPub XI.pubIn) (layOfX XI hlen) _ rfl hdk⟩,
    rfl, hQ hlen⟩
  · exact hprim_PbOfX9L XI hrt hnd
  · intro id hid
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hid
    exact lt_of_lt_of_eq (jPB q hq).1 (NockvmE2E.J9AL.DatX9LOk.P_eq_PN).symm
  · intro t
    by_cases ha : XI.tabs[t].chip.id = "aluChipJ9"
    · rw [sigma9L_alu XI t ha, numOf9L_last]; exact hnumL t ha
    · rw [sigma9L_castSucc XI t ha, numOf9L_castSucc]; exact hnum t ha
  · exact hpJ
  · exact hpV
  · exact hpX
  · exact hpS
  · intro hoff
    exact (habs hoff).2
  · intro t hid k
    exact preL_PbOfX9L XI h t hid k
  · exact preJLink_of_jetPreOkF XI h hjp _ (link9L_DX9LJ XI h hlen _ _ c) (layout_ofFn XI hlen) jS

theorem linkGate9LJ_wit (XI : ExecInst) (c : P8PublicClaim) (h : shapeOkF famJ9AL XI = true) (hpreg : pregOkF XI = true)
    (hjp : jetPreOkF XI = true) (hcan : inpCanOkL XI.pubIn = true) (hg : linkGate9LJ XI c = true) :
    Wit9LJ XI c (fun _ => True) :=
  witness9LJ XI c h hpreg hjp (primsCan_of_inpCanOkL hcan) (of_decide_eq_true hg) _ (fun _ => trivial)

end

end NockvmE2E.Z38.WitJ9ALJ

#print axioms NockvmE2E.Z38.WitJ9ALJ.witness9LJ
#print axioms NockvmE2E.Z38.WitJ9ALJ.linkGate9LJ_wit
