/-
  Nock/NockVMROM/Thm54/VclL/Handle/ServedVS.lean

  Additive.

  * `decode_key5`: five base entries equal to `recF r` (numbers `< p`) decode through `natOf` and the
    kind bits (`hdc`) to `r`;
  * `comp_x_of_served`: a compute export record whose key is among the cell twin's provided keys is
    `exportRec` of a row of the decoded (restricted) cell table;
  * `xok_of_row`: on a `TableAccepts` table such a record is `XOK` for `denH` (`exportRec_grounded`);
  * **`xok_VS`**: at VS (`AcceptsG`, `V.Checks`), outside `ioSummandHX`, `ioSummandHP`, `valSummand`, with
    `zVS ≠ 0`, every export record a compute row consumes is `XOK` for `denVS` (`denH` of the decoded
    restricted cell table) — the export half of `rowSem_of_chip`'s hypotheses, derived.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
import Nock.NockVMROM.Thm54.VclL.Handle.DecodeH
import Nock.NockVMROM.Thm54.VclL.Handle.CensusVS
import Nock.NockVMROM.Thm54.VclL.Handle.Ground

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ServedVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Module
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVS
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS
open scoped Polynomial

noncomputable section

section Decode
variable {F : Type} [Field F] [DecidableEq F]

/-- **Decoding five matched entries** to an export record. -/
theorem decode_key5 (hF : GeneratedField.PrimeFieldElems F) (r : ℕ × VHandle × VHandle)
    (h0 : r.1 < ringChar F) (h1 : r.2.1.2 < ringChar F) (h2 : r.2.2.2 < ringChar F) (eF : Env F)
    (pv lk lv rk rv : ℕ)
    (h : [eF.trace pv, eF.trace lk, eF.trace lv, eF.trace rk, eF.trace rv] = recF r) :
    (natOf (eF.trace pv), hdc eF lk lv, hdc eF rk rv) = r := by
  obtain ⟨i, ⟨k1, v1⟩, ⟨k2, v2⟩⟩ := r
  simp only [recF, hF2, List.cons_append, List.nil_append, List.cons.injEq, and_true] at h
  obtain ⟨hi, hk1, hv1, hk2, hv2⟩ := h
  simp only [hdc, hi, hk1, hv1, hk2, hv2, natOf_natCast hF h0, natOf_natCast hF h1,
    natOf_natCast hF h2, DecodeH.decide_kind]

end Decode

section Served
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))] [Fact (ringChar F).Prime]
  (b : Basis (Fin 3) F K)
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
  (chals pubs : ℕ → K)
  (Q : Fin (cellChipH δF b hn nodes orbit chals pubs).rap.w → F[X])

/-- A compute record's key entries are its columns lifted. -/
theorem entKey_eq (eF : Env F) (pv lk lv rk rv : ℕ) (c : Fin 5) :
    (entKey [pv, lk, lv, rk, rv] eF : Fin 5 → K) c =
      algebraMap F K ([eF.trace pv, eF.trace lk, eF.trace lv, eF.trace rk, eF.trace rv].getD c 0) := by
  fin_cases c <;> simp [entKey, entKeyN]

/-- **A served compute export record is a table row's export record.** -/
theorem comp_x_of_served (hF : GeneratedField.PrimeFieldElems F)
    (hsat : (cellChipH δF b hn nodes orbit chals pubs).rap.Satisfies Q) (eF : Env F)
    (pv lk lv rk rv : ℕ)
    (hmem : (entKey [pv, lk, lv, rk, rv] eF : Fin 5 → K) ∈
      (cellProvs (K := K) b nodes orbit chals pubs Q).map Prod.fst) :
    ∃ c ∈ cellTableOf δF b nodes orbit chals pubs (restrictCell δF b hn nodes orbit chals pubs Q),
      (natOf (eF.trace pv), hdc eF lk lv, hdc eF rk rv) = exportRec c.b0 := by
  haveI : NeZero (ringChar F) := ⟨by
    have := natOf_lt hF (0 : F); omega⟩
  obtain ⟨q, hq, hqk⟩ := List.mem_map.mp hmem
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
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
      [eF.trace pv, eF.trace lk, eF.trace lv, eF.trace rk, eF.trace rv].getD c 0 := by
    intro c
    have := congrFun hqk c
    simp only at this
    rw [entKey_eq] at this
    exact (algebraMap F K).injective this
  set r := exportRec (cellB0Of (cEF b nodes orbit chals pubs Q i)) with hr
  have hlist : [eF.trace pv, eF.trace lk, eF.trace lv, eF.trace rk, eF.trace rv] = recF r := by
    rw [← hkey]
    have e0 := hent ⟨0, by decide⟩; have e1 := hent ⟨1, by decide⟩; have e2 := hent ⟨2, by decide⟩
    have e3 := hent ⟨3, by decide⟩; have e4 := hent ⟨4, by decide⟩
    simp only [CellH.keyH, List.getD_cons_zero, List.getD_cons_succ, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] at e0 e1 e2 e3 e4 ⊢
    simp only [List.map_cons, List.map_nil]
    rw [← e0, ← e1, ← e2, ← e3, ← e4]
  obtain ⟨b0, b1, b2⟩ := DecodeH.exportRec_bounds hF (cEF b nodes orbit chals pubs Q i)
  refine ⟨cellRowOf δF (cellEnvK δF b nodes orbit chals pubs (restrictCell δF b hn nodes orbit chals pubs Q) i)
      (cellEnvF b nodes orbit chals pubs (restrictCell δF b hn nodes orbit chals pubs Q) i),
    List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
  rw [decode_key5 hF r b0 b1 b2 eF pv lk lv rk rv hlist, hr]
  exact congrArg exportRec (cellB0Of_twin δF b hn nodes orbit chals pubs Q i)

end Served

section Table
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp] [Fact q.Prime]

/-- **A record matching a row of an accepted table is `XOK`** for the table's `denH`. -/
theorem xok_of_row {F : Type} [Field F] [DecidableEq F] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl) {c : CellRow q Kfp}
    (hc : c ∈ t) (eF : Env F) (pv lk lv rk rv : ℕ)
    (he : (natOf (eF.trace pv), hdc eF lk lv, hdc eF rk rv) = exportRec c.b0) :
    Cell3 (denH (t.map (·.b0))) (true, natOf (eF.trace pv)) (hdc eF lk lv) (hdc eF rk rv) := by
  obtain ⟨L, R, h1, h2, h3⟩ := exportRec_grounded hq hz h hc
  simp only [exportRec, Prod.mk.injEq] at he
  obtain ⟨e1, e2, e3⟩ := he
  exact ⟨L, R, by rw [e1]; exact h1, by rw [e2]; exact h2, by rw [e3]; exact h3⟩

end Table

section VS
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

attribute [local instance] ClaimDenVS.quadCharF ClaimDenVS.quadZAlg

/-- Compute row `i`'s base environment at VS. -/
abbrev cEnvVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (i : Fin V.N) : Env F :=
  rEF V.computeNodes (chalVH V.basis χ) (pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC
    (msg.Qc χ) i

/-- The denotation at VS: `denH` of the decoded (restricted) cell table. -/
abbrev denVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :
    VHandle → Option Noun :=
  denH ((tVS δF hT hP kr hC V msg χ).map (·.b0))

/-- **Every compute export record is `XOK` at VS**: outside the handle IO summands and `valSummand`,
with the seed nonzero. -/
theorem xok_VS (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hX : ¬ (ioSummandHX hT hP hC V).mem (msg.traces χ) χ)
    (hPm : ¬ (ioSummandHP hT hP hC V).mem (msg.traces χ) χ)
    (hval : ¬ (valSummand δF hT hP hC V msg.msg0C).mem (msg.traces χ) χ)
    (hz : zVS δF χ ≠ 0) (i : Fin V.N) :
    ∀ r ∈ activeXRecs (cEnvVS δF hT hP kr hC V msg χ i),
      XOK (denVS δF hT hP kr hC V msg χ) (cEnvVS δF hT hP kr hC V msg χ i) r := by
  intro r hr pv lk lv rk rv hr5
  obtain ⟨hgM, hw, hsatT⟩ := cell_facts δF hT hP kr hC V msg χ h
  have hq : 2 ^ 63 < ringChar F := hgM.2.2.2.1
  haveI : Fact (ringChar F).Prime :=
    ⟨(CharP.char_is_prime_or_zero F (ringChar F)).resolve_right (by omega)⟩
  obtain ⟨S, hS, hx⟩ := List.mem_flatMap.mp hr
  obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hx
  have hkey : entKey x.rcd (cEnvVS δF hT hP kr hC V msg χ i) ∈ cXVS δF hT hP kr hC V msg χ :=
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_flatMap.mpr ⟨S, hS, List.mem_map.mpr ⟨x, hx', rfl⟩⟩⟩
  have hsrv := (served_of_not_mem δF hT hP kr hC V hV msg χ h hX hPm).1 _ (List.mem_append_left _ hkey)
  rw [hr5] at hsrv
  obtain ⟨c, hc, he⟩ := comp_x_of_served δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
    (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    (fun j => msg.Qm χ (tCS hT hP) (Fin.cast hw j)) hgM.2.2.1 hsatT.1 _ pv lk lv rk rv hsrv
  exact xok_of_row hq hz (claim_table_VS δF hT hP kr hC V hV msg χ h hval hz) hc _ pv lk lv rk rv he

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.ServedVS
