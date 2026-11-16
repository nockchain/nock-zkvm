/-
  Nock/NockVMROM/Thm54/VclL/Handle/DecodeH.lean

* `decode_key`: five base entries equal to `recF r` (numbers `< p`) decode, through `natOf` and the
    kind bits, to exactly `r`.
  * `exportRec_bounds`: a cell row's export record has its numbers `< p`.
  * **`walk_hHX_of_served`**: if a walk row's consumed key is among the cell twin's provided keys
    (the output of `ServeH.keys_served`), then the row's decoded record is `exportRec` of a row of the
    cell table read off the (restricted) cell trace — `hHX` of `walkH_records_genuine`, row by row.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ServeH

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.DecodeH

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open scoped Polynomial

noncomputable section

section Decode
variable {F : Type} [Field F] [DecidableEq F]

theorem decide_kind (k : Bool) : decide ((if k then (1 : F) else 0) = 1) = k := by
  cases k <;> simp

/-- **Decoding a matched key.** -/
theorem decode_key (hF : GeneratedField.PrimeFieldElems F) (r : ℕ × VHandle × VHandle)
    (h0 : r.1 < ringChar F) (h1 : r.2.1.2 < ringChar F) (h2 : r.2.2.2 < ringChar F) (eF : Env F)
    (h : [eF.trace WChip.idx, eF.trace WalkHC.kL, eF.trace WalkHC.vL, eF.trace WalkHC.kR,
      eF.trace WalkHC.vR] = recF r) :
    (natOf (eF.trace WChip.idx), childHOf eF false, childHOf eF true) = r := by
  obtain ⟨i, ⟨k1, v1⟩, ⟨k2, v2⟩⟩ := r
  have e : ∀ k : ℕ, [eF.trace WChip.idx, eF.trace WalkHC.kL, eF.trace WalkHC.vL, eF.trace WalkHC.kR,
      eF.trace WalkHC.vR].getD k 0 = (recF (i, (k1, v1), (k2, v2))).getD k 0 := fun k => by rw [h]
  have hi := e 0
  have hk1 := e 1
  have hv1 := e 2
  have hk2 := e 3
  have hv2 := e 4
  simp only [recF, hF2, List.cons_append, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ] at hi hk1 hv1 hk2 hv2
  simp only [childHOf, Bool.false_eq_true, if_false, if_true, hi, hk1, hv1, hk2, hv2,
    natOf_natCast hF h0, natOf_natCast hF h1, natOf_natCast hF h2, decide_kind]

/-- A cell row's export record has its numbers below `p`. -/
theorem exportRec_bounds (hF : GeneratedField.PrimeFieldElems F) [NeZero (ringChar F)] (eF : Env F) :
    (exportRec (cellB0Of eF)).1 < ringChar F ∧ (exportRec (cellB0Of eF)).2.1.2 < ringChar F ∧
      (exportRec (cellB0Of eF)).2.2.2 < ringChar F := by
  refine ⟨natOf_lt hF _, ?_, ?_⟩
  · simp only [exportRec, hL, cellB0Of]
    by_cases hc : decide (eF.trace Cell.wL = 1) = true
    · simp only [hc, if_true]; exact natOf_lt hF _
    · simp only [hc, if_false]; exact ZMod.val_lt _
  · simp only [exportRec, hR, cellB0Of]
    by_cases hc : decide (eF.trace Cell.wR = 1) = true
    · simp only [hc, if_true]; exact natOf_lt hF _
    · simp only [hc, if_false]; exact ZMod.val_lt _

end Decode

section Served
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))] [Fact (ringChar F).Prime]
  (b : Basis (Fin 3) F K)
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
  (kroots : ℕ) {h' n' : ℕ} (hn' : 0 < n') (nodes' : Fin n' → F) (orbit' : StrictOrbitDomain F 3 h')
  (chals pubs pubs' : ℕ → K)
  (Q : Fin (cellChipH δF b hn nodes orbit chals pubs).rap.w → F[X])
  (Q' : Fin (walkChipH δF kroots b hn' nodes' orbit' chals pubs').rap.w → F[X])

theorem keyVec5_inj {eF eF' : Env F} {l l' : List (CoeffExpr F)}
    (h : (keyVec5 l eF : Fin 5 → K) = keyVec5 l' eF') (c : Fin 5) :
    (l.getD c (.const 0)).eval eF = (l'.getD c (.const 0)).eval eF' :=
  (algebraMap F K).injective (congrFun h c)

/-- **`hHX` from a served walk key.** -/
theorem walk_hHX_of_served (hF : GeneratedField.PrimeFieldElems F)
    (hsat : (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies Q) (j : Fin n')
    (hmem : keyVec5 WalkHC.xKeyH (wEF b nodes' orbit' chals pubs' Q' j) ∈
      (cellProvs (K := K) b nodes orbit chals pubs Q).map Prod.fst) :
    ∃ c ∈ cellTableOf δF b nodes orbit chals pubs (restrictCell δF b hn nodes orbit chals pubs Q),
      (natOf ((wEF b nodes' orbit' chals pubs' Q' j).trace WChip.idx),
        childHOf (wEF b nodes' orbit' chals pubs' Q' j) false,
        childHOf (wEF b nodes' orbit' chals pubs' Q' j) true) = exportRec c.b0 := by
  haveI : NeZero (ringChar F) := ⟨(Fact.out : (ringChar F).Prime).ne_zero⟩
  obtain ⟨q, hq, hqk⟩ := List.mem_map.mp hmem
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
  -- the cell row's provided key is its export record
  have hbase := (cellH_rows δF b hn nodes orbit chals pubs Q hsat i).1
  have hbool : ∀ w, boolE (cv w) ∈ Cell.baseGates (F := F) →
      (cEF b nodes orbit chals pubs Q i).trace w = 0 ∨ (cEF b nodes orbit chals pubs Q i).trace w = 1 := by
    intro w hw
    have g := hbase _ hw
    simp only [CoeffExpr.eval, cv] at g
    exact bool_val g
  have hkey := keyH_eval hF (cEF b nodes orbit chals pubs Q i)
    (hbool Cell.wL (by simp [Cell.baseGates])) (hbool Cell.wR (by simp [Cell.baseGates]))
  have hent : ∀ c : Fin 5, (CellH.keyH.getD c (.const 0)).eval (cEF b nodes orbit chals pubs Q i) =
      (WalkHC.xKeyH.getD c (.const 0)).eval (wEF b nodes' orbit' chals pubs' Q' j) :=
    keyVec5_inj hqk
  set r := exportRec (cellB0Of (cEF b nodes orbit chals pubs Q i)) with hr
  have hlist : [(wEF b nodes' orbit' chals pubs' Q' j).trace WChip.idx,
      (wEF b nodes' orbit' chals pubs' Q' j).trace WalkHC.kL,
      (wEF b nodes' orbit' chals pubs' Q' j).trace WalkHC.vL,
      (wEF b nodes' orbit' chals pubs' Q' j).trace WalkHC.kR,
      (wEF b nodes' orbit' chals pubs' Q' j).trace WalkHC.vR] = recF r := by
    rw [← hkey]
    have e0 := hent ⟨0, by decide⟩; have e1 := hent ⟨1, by decide⟩; have e2 := hent ⟨2, by decide⟩
    have e3 := hent ⟨3, by decide⟩; have e4 := hent ⟨4, by decide⟩
    simp only [WalkHC.xKeyH, CellH.keyH, List.getD_cons_zero, List.getD_cons_succ,
      Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, CoeffExpr.eval, cv] at e0 e1 e2 e3 e4 ⊢
    simp only [List.map_cons, List.map_nil, CoeffExpr.eval, cv]
    rw [e0, e1, e2, e3, e4]
  obtain ⟨b0, b1, b2⟩ := exportRec_bounds hF (cEF b nodes orbit chals pubs Q i)
  refine ⟨cellRowOf δF (cellEnvK δF b nodes orbit chals pubs (restrictCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictCell δF b hn nodes orbit chals pubs Q) i),
    List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
  rw [decode_key hF r b0 b1 b2 _ hlist, hr]
  exact congrArg exportRec (cellB0Of_twin δF b hn nodes orbit chals pubs Q i)

end Served

end

end Nock.NockVMROM.Thm54.VclL.Handle.DecodeH
