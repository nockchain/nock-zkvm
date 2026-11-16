/-
  Nock/NockVMROM/Thm54/VclL/Handle/HxvJ8.lean

  **`hHXV` from the atom export balance (`hbalA'`).**

  * `cellB0Of_atom`: the atom table's row record (`cellB0Of`, base columns `< 129`) is the restriction's.
  * **`atom_hHX_of_served`** (the twin of `DecodeH.walk_hHX_of_served` for the atom table `atomChipHQ` and the atom
    walk `walkChipHQK`): a served walk read key decodes to `exportRec` of a decoded atom-table row.
  * **`hHXV_of_served`** at `AcceptsJ8Z` (the atom side at `chalsAJ8Z`): from `houtA` (summand #4 outside), the
    public export balance `hbalA` (`AcceptsJ8''.hbalA'`: `pubsA 4/5 = pubsA 10/11 + pubsV 4/5`, through the walk
    telescope) and the count `< p` (`AtomServedQ.atom_consume_served`), every atom-walk row's read names a decoded
    atom-table row: `LinkJ8X''.hHXV`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HxvJ8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Nock.NockVMROM.Thm54.VclL.Handle.DecodeH
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (atomChipHQ restrictAtomCell)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)

noncomputable section

section Served
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))] [Fact (ringChar F).Prime]
  (b : Basis (Fin 3) F K)
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
  (kroots : ℕ) {h' n' : ℕ} (hn' : 0 < n') (nodes' : Fin n' → F) (orbit' : StrictOrbitDomain F 3 h')
  (chals pubs pubs' : ℕ → K)
  (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])
  (Q' : Fin (walkChipHQK δF kroots b hn' nodes' orbit' chals pubs').rap.w → F[X])

theorem aEF_restrict_trace (i : Fin n) {j : ℕ} (hj : j < 129) :
    (AtomServedQ.aEF b nodes orbit chals pubs Q i).trace j =
      (cellEnvF b nodes orbit chals pubs (restrictAtomCell δF b hn nodes orbit chals pubs Q) i).trace j := by
  have hw : (cellChip δF b hn nodes orbit chals pubs).rap.w = 225 :=
    (cellChip_fingerprint δF b hn nodes orbit chals pubs).1
  have h0 : j < (cellChip δF b hn nodes orbit chals pubs).rap.w := by rw [hw]; omega
  have h1 : j < (atomChipHQ δF b hn nodes orbit chals pubs).rap.w := by
    rw [AtomChipHQ.atomChipHQ_width]; omega
  simp only [AtomServedQ.aEF, cellEnvF, Reify.envOfTrace, dif_pos h0, dif_pos h1, restrictAtomCell, restrictQ]
  congr 2
  · apply Fin.ext
    simp [shiftCol, hj]

/-- `cellB0Of` reads only base columns `< 129`: the atom row and the restriction's row are one record. -/
theorem cellB0Of_atom (i : Fin n) :
    cellB0Of (AtomServedQ.aEF b nodes orbit chals pubs Q i) =
      cellB0Of (cellEnvF b nodes orbit chals pubs (restrictAtomCell δF b hn nodes orbit chals pubs Q) i) := by
  simp only [cellB0Of, aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idx < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idL < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.idR < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.wL < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.wR < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.aL < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.aR < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.lo < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hi < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.loL < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hiL < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.loR < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.hiR < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.carry < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.mv < 129),
    aEF_restrict_trace δF b hn nodes orbit chals pubs Q i (by decide : Cell.mx < 129)]

/-- **`hHX` for the atom table and the atom walk, from a served walk read key.** -/
theorem atom_hHX_of_served (hF : GeneratedField.PrimeFieldElems F)
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) (j : Fin n')
    (hmem : keyVec5 WalkHC.xKeyH (wEF b nodes' orbit' chals pubs' Q' j) ∈
      (AtomServedQ.atomProvs (K := K) b nodes orbit chals pubs Q).map Prod.fst) :
    ∃ c ∈ cellTableOf δF b nodes orbit chals pubs (restrictAtomCell δF b hn nodes orbit chals pubs Q),
      (natOf ((wEF b nodes' orbit' chals pubs' Q' j).trace WChip.idx),
        childHOf (wEF b nodes' orbit' chals pubs' Q' j) false,
        childHOf (wEF b nodes' orbit' chals pubs' Q' j) true) = exportRec c.b0 := by
  haveI : NeZero (ringChar F) := ⟨(Fact.out : (ringChar F).Prime).ne_zero⟩
  obtain ⟨q, hq, hqk⟩ := List.mem_map.mp hmem
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
  have hbase := AtomServedQ.atom_base δF b hn nodes orbit chals pubs Q hsat i
  have hbool : ∀ w, boolE (cv w) ∈ Cell.baseGates (F := F) →
      (AtomServedQ.aEF b nodes orbit chals pubs Q i).trace w = 0 ∨
        (AtomServedQ.aEF b nodes orbit chals pubs Q i).trace w = 1 := by
    intro w hw
    have g := hbase _ (List.mem_append_left _ hw)
    simp only [CoeffExpr.eval, cv] at g
    exact bool_val g
  have hkey := keyH_eval hF (AtomServedQ.aEF b nodes orbit chals pubs Q i)
    (hbool Cell.wL (by simp [Cell.baseGates])) (hbool Cell.wR (by simp [Cell.baseGates]))
  have hent : ∀ c : Fin 5, (CellH.keyH.getD c (.const 0)).eval (AtomServedQ.aEF b nodes orbit chals pubs Q i) =
      (WalkHC.xKeyH.getD c (.const 0)).eval (wEF b nodes' orbit' chals pubs' Q' j) :=
    keyVec5_inj hqk
  set r := exportRec (cellB0Of (AtomServedQ.aEF b nodes orbit chals pubs Q i)) with hr
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
  obtain ⟨b0, b1, b2⟩ := exportRec_bounds hF (AtomServedQ.aEF b nodes orbit chals pubs Q i)
  refine ⟨cellRowOf δF (cellEnvK δF b nodes orbit chals pubs (restrictAtomCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictAtomCell δF b hn nodes orbit chals pubs Q) i),
    List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
  rw [decode_key hF r b0 b1 b2 _ hlist, hr]
  exact congrArg exportRec (cellB0Of_atom δF b hn nodes orbit chals pubs Q i)

end Served

end

end Nock.NockVMROM.Thm54.VclL.Handle.HxvJ8
