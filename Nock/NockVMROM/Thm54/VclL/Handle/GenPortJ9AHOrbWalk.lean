/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHOrbWalk.lean

* `walkOK_reidx_kr`     : F1b `walkOK_reidx` + a change of the root count `kr = kr'`;
  * `walk_pubs_at`        : `walkGenRowsB_pubs` at `regD DA` and an arbitrary injective orbit `O`;
  * `walk_interp_at`      : `genJ9AX_walk_interp` at a chip `q = reorb I.W O'`;
  * `walk_at`             : `hsatW ∧ hbindW` at `mkPbA (withOrb I o) hv'`, `I'.toMsg`/`toTr`, coin `toχ χe`.
  The honest walk chip is never instantiated at `DA`; only `DA`'s families are moved to `regD DA`
  (`genJ9AX_walk_ok`).  Never compares `mkPbA` with `B.Pb`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHChipCast
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRun
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfMem

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbWalk

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHProj
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell (interp_cast)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qW)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRun (regD)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkOrd
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkBfs
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkGlue
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkPubs
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalk

noncomputable section

section Generic
open Polynomial
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Module.Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- F1b `walkOK_reidx`, with the root count changed along `kr = kr'` (so the target may carry `Pb.kroots`). -/
theorem walkOK_reidx_kr {n m : ℕ} (e : n = m) (hn : 0 < n) (hm : 0 < m) (ν : Fin n → ZMod p) (μ : Fin m → ZMod p)
    (hνμ : ∀ i : Fin n, ν i = μ (Fin.cast e i)) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (chals pubs : ℕ → K) {kr kr' : ℕ} (hk : kr = kr') (T : Fin 166 → (ZMod p)[X])
    (H : (WalkJ8.walkChipJ8 δ kr' b hm μ o chals pubs).rap.Satisfies
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width δ kr' b hm μ o chals pubs) j)) ∧
      (WalkJ8.walkChipJ8 δ kr' b hm μ o chals pubs).BindsPreprocessing
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width δ kr' b hm μ o chals pubs) j))) :
    (WalkJ8.walkChipJ8 δ kr b hn ν o chals pubs).rap.Satisfies
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width δ kr b hn ν o chals pubs) j)) ∧
      (WalkJ8.walkChipJ8 δ kr b hn ν o chals pubs).BindsPreprocessing
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width δ kr b hn ν o chals pubs) j)) := by
  subst hk
  exact GenPortJ9AHChipCast.walkOK_reidx δ b e hn hm ν μ hνμ o chals pubs kr T H

end Generic

theorem n_reorb (W q : ChipIn) (O' : Orb) (hq : q = reorb W O') : q.n = W.n := by
  subst hq; rfl

theorem cols_reorb (W q : ChipIn) (O' : Orb) (hq : q = reorb W O') (i : Fin q.n) (c : ℕ) :
    q.cols c i = W.cols c (Fin.cast (n_reorb W q O' hq) i) := by
  subst hq; rfl

section Final
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]

/-- The final assembly of `walk_at`, abstract in the input `I` (so no big term is ever unified). -/
theorem walk_final
    (I : InJ9A) (o : OrbJ9A) (hv' : ValidJ9A (withOrb I o)) (χ : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC) {m : ℕ} (hn : I.W.n = m) (hm : 0 < m)
    {kr' : ℕ} (hk : I.kroots = kr') (pubs : ℕ → KC) (hpubs : (withOrb I o).toMsg.pubsW = pubs)
    (T : Fin 166 → Polynomial (ZMod P)) (hI : ∀ j : Fin 166, interpOf (reorb I.W o.W) j = T j)
    (hνμ : ∀ i : Fin (reorb I.W o.W).n,
      nodesOf (reorb I.W o.W) i = ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hv'.oW) m (Fin.cast hn i))
    (H : (WalkJ8.walkChipJ8 deltaF kr' powerBasis3 hm (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hv'.oW) m)
        (mkOrbit (reorb I.W o.W) hv'.oW) (chalsMJ8 deltaF χ) pubs).rap.Satisfies
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width deltaF kr' powerBasis3 hm
          (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hv'.oW) m)
          (mkOrbit (reorb I.W o.W) hv'.oW) (chalsMJ8 deltaF χ) pubs) j)) ∧
      (WalkJ8.walkChipJ8 deltaF kr' powerBasis3 hm (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hv'.oW) m)
        (mkOrbit (reorb I.W o.W) hv'.oW) (chalsMJ8 deltaF χ) pubs).BindsPreprocessing
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width deltaF kr' powerBasis3 hm
          (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hv'.oW) m)
          (mkOrbit (reorb I.W o.W) hv'.oW) (chalsMJ8 deltaF χ) pubs) j))) :
    (WalkJ8.walkChipJ8 deltaF (mkPbA (withOrb I o) hv').kroots powerBasis3
        (mkPbA (withOrb I o) hv').hnW (mkPbA (withOrb I o) hv').nodesW
        (mkPbA (withOrb I o) hv').orbitW (chalsMJ8 deltaF χ) (withOrb I o).toMsg.pubsW).rap.Satisfies
      (qW deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF χ) (withOrb I o).toMsg.pubsW) ∧
    (WalkJ8.walkChipJ8 deltaF (mkPbA (withOrb I o) hv').kroots powerBasis3
        (mkPbA (withOrb I o) hv').hnW (mkPbA (withOrb I o) hv').nodesW
        (mkPbA (withOrb I o) hv').orbitW (chalsMJ8 deltaF χ) (withOrb I o).toMsg.pubsW).BindsPreprocessing
      (qW deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF χ) (withOrb I o).toMsg.pubsW) := by
  subst hpubs
  have hq : qW deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF χ) (withOrb I o).toMsg.pubsW =
      fun j => T (Fin.cast (WalkJ8.walkChipJ8_width deltaF (mkPbA (withOrb I o) hv').kroots powerBasis3
        (mkPbA (withOrb I o) hv').hnW (mkPbA (withOrb I o) hv').nodesW
        (mkPbA (withOrb I o) hv').orbitW (chalsMJ8 deltaF χ) (withOrb I o).toMsg.pubsW) j) :=
    funext fun j => hI _
  rw [hq]
  exact walkOK_reidx_kr deltaF powerBasis3 hn hv'.nW hm _ _ hνμ _ _ _ hk _ H

/-- `walk_final` with the injectivity/orbit facts derived, still abstract in `I`. -/
theorem walk_abs
    (I : InJ9A) (o : OrbJ9A) (ho : OrbAdm I o) (hv' : ValidJ9A (withOrb I o))
    (χ : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC)
    {m : ℕ} (hn : I.W.n = m) (hm : 0 < m) {kr' : ℕ} (hk : I.kroots = kr') (pubs : ℕ → KC)
    (T : Fin 166 → Polynomial (ZMod P))
    (Hall : ∀ (hoW : OrbOK (reorb I.W o.W)) (hinj0 : Function.Injective (nodesOf (reorb I.W o.W)))
      (hinjN : Function.Injective (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW) m)),
      (withOrb I o).toMsg.pubsW = pubs ∧
      (∀ j : Fin 166, interpOf (reorb I.W o.W) j = T j) ∧
      ((WalkJ8.walkChipJ8 deltaF kr' powerBasis3 hm (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW) m)
        (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF χ) pubs).rap.Satisfies
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width deltaF kr' powerBasis3 hm
          (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW) m)
          (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF χ) pubs) j)) ∧
      (WalkJ8.walkChipJ8 deltaF kr' powerBasis3 hm (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW) m)
        (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF χ) pubs).BindsPreprocessing
        (fun j => T (Fin.cast (WalkJ8.walkChipJ8_width deltaF kr' powerBasis3 hm
          (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW) m)
          (mkOrbit (reorb I.W o.W) hoW) (chalsMJ8 deltaF χ) pubs) j)))) :
    (WalkJ8.walkChipJ8 deltaF (mkPbA (withOrb I o) hv').kroots powerBasis3
        (mkPbA (withOrb I o) hv').hnW (mkPbA (withOrb I o) hv').nodesW
        (mkPbA (withOrb I o) hv').orbitW (chalsMJ8 deltaF χ) (withOrb I o).toMsg.pubsW).rap.Satisfies
      (qW deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF χ) (withOrb I o).toMsg.pubsW) ∧
    (WalkJ8.walkChipJ8 deltaF (mkPbA (withOrb I o) hv').kroots powerBasis3
        (mkPbA (withOrb I o) hv').hnW (mkPbA (withOrb I o) hv').nodesW
        (mkPbA (withOrb I o) hv').orbitW (chalsMJ8 deltaF χ) (withOrb I o).toMsg.pubsW).BindsPreprocessing
      (qW deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF χ) (withOrb I o).toMsg.pubsW) := by
  have hoW : OrbOK (reorb I.W o.W) := hv'.oW
  have hinj0 : Function.Injective (nodesOf (reorb I.W o.W)) :=
    GenPortJ9AHOrb.nodesOf_inj _ hoW ho.W.2
  have hnodes : nodesOf (reorb I.W o.W) = ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW) I.W.n :=
    GenPortJ9AHOrbA.nodesOf_powN _ hoW
  subst hn
  have hinjN : Function.Injective (ComplJ8Of.powN (mkOrbit (reorb I.W o.W) hoW) I.W.n) := by
    rw [← hnodes]; exact hinj0
  obtain ⟨hp, hT, H⟩ := Hall hoW hinj0 hinjN
  exact walk_final I o hv' χ rfl hm hk pubs hp T hT (fun i => congrFun hnodes i) H

end Final

section Run
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hnc : callsOf (ComplJ8Data.rowsOfT t) = [])
  (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
include hnc hwalk9

local notation "DR" => regD (j9aDataOf P Rg Rt hgen)

/-- `walkGenRowsB_pubs` at `regD DA` and an arbitrary injective orbit `O`. -/
theorem walk_pubs_at (χe : CoinsE) {h : ℕ} (O : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN O (walkRows (DR).cells (DR).reads).length)) (j : ℕ) :
    K3.toK ((recJ9AX s f χe t r).M.pubsW j) =
      ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) O (toχ χe) j := by
  have a : ∀ c ∈ (DR).cells, c.isCell = true := GenPortJ9AHCellRun.hcs_DA Rt hgen hnc χe
  have b := GenPortJ9AHWalkRun.hwcell_DR Rt hgen hnc hwalk9
  have c := GenPortJ9AHWalkRun.hwroot_DR Rt hgen hnc hwalk9
  have e1 := GenPortJ9AHWalkPubs.walkGenRowsB_pubs χe (DR) a b c O hinj j
  rw [GenPortJ9AHWalkRun.recJ9AX_pubsW Rt hgen hnc hwalk9 χe]
  exact e1

/-- `genJ9AX_walk_interp` at a chip `q = reorb I.W O'` (same columns, other orbit). -/
theorem walk_interp_at (χe : CoinsE) (q : ChipIn) (O' : Orb) (hq : q = reorb (recJ9AX s f χe t r).W O')
    (ho : OrbOK q) (hinj : Function.Injective (nodesOf q)) (j : ℕ) (hj : j < 166) :
    interpOf q j =
      ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit q ho) (walkRows (DR).cells (DR).reads).length)
        (mkOrbit q ho) (VerJ8.chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit q ho))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) ⟨j, hj⟩ := by
  have hn : q.n = (walkRows (DR).cells (DR).reads).length := by
    exact (n_reorb _ q O' hq).trans (GenPortJ9AHWalkRun.genJ9AX_walk_n' Rt hgen hnc hwalk9 χe)
  have hinj' : Function.Injective
      (ComplJ8Of.powN (mkOrbit q ho) (walkRows (DR).cells (DR).reads).length) := by
    have hI : Function.Injective (nodesOf q ∘ Fin.cast hn.symm) := hinj.comp (Fin.cast_injective _)
    rw [GenPortJ9AHWalkRun.nodes_cast q ho hn] at hI
    exact hI
  have hcols : ∀ (i : Fin q.n) (c : ℕ) (hc : c < 166), q.cols c i =
      fullCol (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (HonestK8.certUp
          (ComplJ8Enc.wColHQBE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
            (ComplJ8Of.powN (mkOrbit q ho) _) (mkOrbit q ho) (VerJ8.chalsMJ8 deltaF (toχ χe))
            (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit q ho) (toχ χe))
            (ComplJ8Of.encR deltaF (toχ χe))
            (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe)) (DR).cells (DR).reads
            (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR)))
          (ComplJ8Walk.lenB (DR).cells (DR).reads)) c (Fin.cast hn i) := by
    intro i c hc
    have h := GenPortJ9AHWalkRun.genJ9AX_walk_cols Rt hgen hnc hwalk9 χe (mkOrbit q ho) hinj'
      (Fin.cast (n_reorb _ q O' hq) i) c hc
    rw [cols_reorb _ q O' hq i c]
    exact h
  unfold interpOf
  rw [interp_cast hn, GenPortJ9AHWalkRun.nodes_cast q ho hn]
  unfold ComplJ8Enc.walkTrWE honestQ
  refine congrArg (Lagrange.interpolate Finset.univ
    (ComplJ8Of.powN (mkOrbit q ho) (walkRows (DR).cells (DR).reads).length)) ?_
  funext i'
  exact hcols (Fin.cast hn.symm i') j hj

theorem walk_famV (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    ∀ e ∈ ComplJ8Of.famWalkV deltaF (j9aDataOf P Rg Rt hgen) (K := KC), toχ χe ∉ e.ev :=
  fun e he => ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ _
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))) e he

theorem walk_famH (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    ∀ e ∈ ComplJ8Of.famWalkH deltaF (j9aDataOf P Rg Rt hgen) (K := KC), toχ χe ∉ e.ev :=
  fun e he => ComplJ9AOfMem.goodJA deltaF powerBasis3 Rt hgen hpG h31A hχ _
      (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) e he

/-- The `Hall` input of `walk_abs` at `I := recJ9AX …` (binder-free: no `Algebra Fp (Quad …)`). -/
theorem walk_hall (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (o : OrbJ9A)
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe))
    (hoW : OrbOK (reorb (recJ9AX s f χe t r).W o.W))
    (hinj0 : Function.Injective (nodesOf (reorb (recJ9AX s f χe t r).W o.W)))
    (hinjN : Function.Injective (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW)
      (walkRows (DR).cells (DR).reads).length)) :
    (withOrb (recJ9AX s f χe t r) o).toMsg.pubsW =
      ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
        (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (toχ χe) ∧
    (∀ j : Fin 166, interpOf (reorb (recJ9AX s f χe t r).W o.W) j =
      ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) j) ∧
    ((WalkJ8.walkChipJ8 deltaF (krW (DR).cells (DR).reads) powerBasis3
        (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (chalsMJ8 deltaF (toχ χe))
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
          (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (toχ χe))).rap.Satisfies
      (fun j => (fun j : Fin 166 => ComplJ8Enc.walkTrWE deltaF powerBasis3
        (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) j)
        (Fin.cast (WalkJ8.walkChipJ8_width deltaF (krW (DR).cells (DR).reads) powerBasis3
          (ComplJ8Of.walk_pos (DR).cells (DR).reads)
          (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW)
            (walkRows (DR).cells (DR).reads).length)
          (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (chalsMJ8 deltaF (toχ χe))
          (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
            (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (toχ χe))) j))) ∧
    (WalkJ8.walkChipJ8 deltaF (krW (DR).cells (DR).reads) powerBasis3
        (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (chalsMJ8 deltaF (toχ χe))
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
          (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (toχ χe))).BindsPreprocessing
      (fun j => (fun j : Fin 166 => ComplJ8Enc.walkTrWE deltaF powerBasis3
        (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) j)
        (Fin.cast (WalkJ8.walkChipJ8_width deltaF (krW (DR).cells (DR).reads) powerBasis3
          (ComplJ8Of.walk_pos (DR).cells (DR).reads)
          (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW)
            (walkRows (DR).cells (DR).reads).length)
          (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (chalsMJ8 deltaF (toχ χe))
          (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
            (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) (toχ χe))) j)) := by
  have hV := walk_famV Rt hgen hnc hwalk9 hpG h31A χe hχ
  have hH := walk_famH Rt hgen hnc hwalk9 hpG h31A χe hχ
  refine ⟨funext fun j => walk_pubs_at Rt hgen hnc hwalk9 χe _ hinjN j, ?_,
    GenPortJ9AHWalkRun.genJ9AX_walk_ok Rt hgen hnc hwalk9
      (ComplJ9AChains.hp63_of_G hpG) h31A
      (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hoW) hinjN (toχ χe) hV hH⟩
  intro j
  exact walk_interp_at Rt hgen hnc hwalk9 χe _ o.W rfl hoW hinj0 j j.2

/-- **`hsatW ∧ hbindW` of `AcceptsJ9A` at `withOrb I o`.** -/
theorem walk_at (hpG : P = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (j9aDataOf P Rg Rt hgen))
    (χe : CoinsE) (I : InJ9A) (hI : I = recJ9AX s f χe t r) (o : OrbJ9A) (ho : OrbAdm I o)
    (hv' : ValidJ9A (withOrb I o))
    (hχ : (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe)) :
    (WalkJ8.walkChipJ8 deltaF (mkPbA (withOrb I o) hv').kroots powerBasis3
        (mkPbA (withOrb I o) hv').hnW (mkPbA (withOrb I o) hv').nodesW
        (mkPbA (withOrb I o) hv').orbitW
        (chalsMJ8 deltaF (toχ χe)) (withOrb I o).toMsg.pubsW).rap.Satisfies
      (qW deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb I o).toMsg.pubsW) ∧
    (WalkJ8.walkChipJ8 deltaF (mkPbA (withOrb I o) hv').kroots powerBasis3
        (mkPbA (withOrb I o) hv').hnW (mkPbA (withOrb I o) hv').nodesW
        (mkPbA (withOrb I o) hv').orbitW
        (chalsMJ8 deltaF (toχ χe)) (withOrb I o).toMsg.pubsW).BindsPreprocessing
      (qW deltaF powerBasis3 (mkPbA (withOrb I o) hv').toPubJ8
        (withOrb I o).toTr.toJ8 (chalsMJ8 deltaF (toχ χe))
        (withOrb I o).toMsg.pubsW) := by
  subst hI
  have hn : (recJ9AX s f χe t r).W.n = (walkRows (DR).cells (DR).reads).length :=
    GenPortJ9AHWalkRun.genJ9AX_walk_n' Rt hgen hnc hwalk9 χe
  have hm := ComplJ8Of.walk_pos (DR).cells (DR).reads
  have hk :(recJ9AX s f χe t r).kroots = krW (DR).cells (DR).reads :=
    GenPortJ9AHWalkRun.recJ9AX_kroots' Rt hgen hnc hwalk9 χe
  refine walk_abs (recJ9AX s f χe t r) o ho hv' (toχ χe) hn hm hk
    (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR)
      (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hv'.oW) (toχ χe))
    (fun j => ComplJ8Enc.walkTrWE deltaF powerBasis3 (ComplJ8Of.walk_pos (DR).cells (DR).reads)
        (ComplJ8Of.powN (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hv'.oW)
          (walkRows (DR).cells (DR).reads).length)
        (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hv'.oW) (chalsMJ8 deltaF)
        (ComplJ8Of.pubsWOf deltaF powerBasis3 (DR) (mkOrbit (reorb (recJ9AX s f χe t r).W o.W) hv'.oW))
        (ComplJ8Of.γV deltaF) (ComplJ8Of.ρV deltaF) (ComplJ8Of.encR deltaF) (DR).cells (DR).reads
        (ComplJ8Of.kLW (DR)) (ComplJ8Of.vLW (DR)) (ComplJ8Of.kRW (DR)) (ComplJ8Of.vRW (DR))
        (toχ χe) j) ?_
  intro hoW hinj0 hinjN
  exact walk_hall Rt hgen hnc hwalk9 hpG h31A χe o hχ hoW hinj0 hinjN

end Run

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbWalk

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbWalk in
#print axioms walkOK_reidx_kr
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbWalk in
#print axioms walk_pubs_at
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbWalk in
#print axioms walk_interp_at
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbWalk in
#print axioms walk_at
