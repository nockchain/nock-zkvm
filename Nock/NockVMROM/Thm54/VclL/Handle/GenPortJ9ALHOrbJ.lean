/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHOrbJ.lean

  **Honest link, file 4: the J chip of an abstract record `I : InJ9A` at the J-9 AL data `DL`**
  (`GenPortJ9AHOrbJ` §5 `lay_layJ` / `j_at` re-instantiated). §1-4 of `GenPortJ9AHOrbJ`
  (`jchip_at`, `jGen_*`, `lay_len`, `lay_pointwise`) are abstract in the row list and are reused as they are.

  The record `I` is abstract.  The three link equations are the J-layer facts that `j_at` gets by `rfl` at `recJ9AXJ`:
  `hlay` (the layout is the layout of the DL J rows), `hJcols` (the J columns are `jGen I.χ DL.jrows`), `hpJ` (the J
  publics are `(jGen I.χ DL.jrows).2`).  The J binder is the prim-aware `hRtJ` (`ComplJ9ALData.jrows_gateL`); the coin
  hypothesis is `B8L.Good` (`GenPortJ9ALHMemSat.hin_B8L`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHMemSat

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.Jet.ChipJ8 (CRow PRow)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsJJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbJ (jchip_at lay_len lay_pointwise)
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm reorb withOrb)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)

noncomputable section

section Glue

variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × Nock.Jet.Prim.PrimOp))
  {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DL" => j9alDataOf P Rg Rt prims hgen

/-- The J row count of a record whose layout is the layout of the DL J rows. -/
theorem jlenL (I : InJ9A) (hlay : List.ofFn I.lay = (DL).jrows.map CRow.pre) :
    I.J.n = (DL).jrows.length :=
  lay_len _ _ hlay

/-- **`lay_layJ` at `DL`**: the verifier's layout at `withOrb I o` is `layJ` of the honest DL J rows. -/
theorem lay_layJL (I : InJ9A) (o : OrbJ9A) (hv' : ValidJ9A (withOrb I o))
    (hlay : List.ofFn I.lay = (DL).jrows.map CRow.pre) :
    (mkPbA (withOrb I o) hv').lay =
      Nock.Jet.ChipJ8T.HonestRAP.layJ
        (fun i : Fin I.J.n => (DL).jrows.get (Fin.cast (jlenL Rt prims hgen I hlay) i)) :=
  funext (lay_pointwise _ _ hlay (jlenL Rt prims hgen I hlay))

/-- **The `hJk` field of `AcceptsJ9A` at `withOrb I o`, at `DL`** (`GenPortJ9AHOrbJ.j_at`), present or absent. -/
theorem j_atL (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (hRtJ : ∀ id ∈ ComplJ8Jet.CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate P, Nock.Jet.Autogen.compile P (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped P)
    (I : InJ9A)
    (hlay : List.ofFn I.lay = (DL).jrows.map CRow.pre)
    (hJcols : ∀ (j : ℕ) (i : Fin I.J.n), j < 71 →
      I.J.cols j i = (((jGen I.χ (DL).jrows).1).getD (i : ℕ) #[]).getD j 0)
    (hpJ : I.M.pubsJ = (jGen I.χ (DL).jrows).2)
    (o : OrbJ9A) (ho : OrbAdm I o)
    (hv' : ValidJ9A (withOrb I o))
    (hχ : (ComplJ9ALRun.B8L deltaF powerBasis3 Rt hgen prims hpG
      (ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A)).Good (toχ I.χ)) :
    JGenJ8.JChipOK deltaF powerBasis3 (mkPbA (withOrb I o) hv').nodesJ
      (mkPbA (withOrb I o) hv').orbitJ
      (chalsJJ8 (toχ (withOrb I o).χ))
      (withOrb I o).toMsg.pubsJ (mkPbA (withOrb I o) hv').lay
      (qJ deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8
        (chalsJJ8 (toχ (withOrb I o).χ))
        (withOrb I o).toMsg.pubsJ) := by
  have hp : 0 < P := (Fact.out : P.Prime).pos
  have h31 := ComplJ9ALRun.rows31L_of_A Rt hgen prims h31A
  have hin := GenPortJ9ALHMemSat.hin_B8L deltaF powerBasis3 Rt prims hgen hpG h31 (toχ I.χ) hχ
  have hn := jlenL Rt prims hgen I hlay
  have hlay' := lay_pointwise _ _ hlay hn
  have hoq : OrbOK (reorb I.J o.J) := ho.J.1
  obtain ⟨hinj0, hadj0⟩ := GenPortJ9AHOrbA.nodes_ok _ hoq ho.J.2
  have hpole0 := ComplJ8Bad.jNoPole deltaF (ComplJ8Jet.jKeysT (DL).jrows.get)
    (ComplJ8Jet.jKeysX (DL).jrows.get) (toχ I.χ)
    (fun e he => hin _
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) e he)
  have hpole := ComplJ8Jet.notJPole_of_keys deltaF _ _ hpole0.1 hpole0.2
  exact jchip_at I.χ (DL).jrows
    (fun x hx => ComplJ9ALData.jrows_gateL Rt prims hgen hp hRtJ x hx) hpole
    (reorb I.J o.J) hoq hinj0 hadj0 hn
    (mkPbA (withOrb I o) hv').lay hlay'
    (withOrb I o).toMsg.pubsJ (funext fun j => by
      show K3.toK (I.M.pubsJ j) = K3.toK ((jGen I.χ (DL).jrows).2 j)
      rw [hpJ])
    (fun j i hj => hJcols j i hj)

end Glue

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHOrbJ
