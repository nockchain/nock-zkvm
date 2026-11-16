/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestVS.lean

  Additive.

  * `rhoVS` / `msgVS`: the honest VS message of a run: the compute trace `compPoly` over the memory datum's
    own cell list `H.d.cells` (`H.d = demandH2 rows`), the memory traces `cellTraceH` (over `cellColB` at the
    claim's binds, `mh = mhH2`) and `walkTraceH` (child handles `hdl`), the requests
    `ρ = (vTotB, xTot − yTot, pTot, accSumX, accSumP)` and the round-2 message `(yTot, yHVS)`;
  * Every other hypothesis is a run fact, a field fact or a
    verifier-shape fact; none is a twin terminal or a handle column any more (they are `HonestTermH`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTermH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Module
open scoped Polynomial

noncomputable section

section Msg
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr) (t : NTree (GenComputeRow Kg))

/-- The compute rows of the run, as a forest (`bfsForest [airReorder t]`). -/
abbrev fW : List (NTree (GenComputeRow Kg)) := bfsForest [airReorder t]

def rhoVS (χ : Coins frameVS K) : Fin 5 → Quad (algebraMap F K δF) :=
  ![vTotB H (claimBinds H.V.claim) (toVCL χ), H.xTot (toVCL χ) - H.yTot (toVCL χ), H.pTot (toVCL χ),
    Quad.mk _ (accSumX H.V.basis H.d.cells (wRows (fW t)) (chalVH H.V.basis χ) (fW t).length) 0,
    Quad.mk _ (accSumP H.V.basis H.d.cells (wRows (fW t)) (chalVH H.V.basis χ) (fW t).length) 0]

/-- The honest compute trace polynomials. -/
def qcVS (x : ClaimMsgVS) (χ : Coins frameVS K) : Fin (tableVS hC).width → F[X] :=
  compPoly H.V.basis H.d.cells (wRows (fW t)) (fW t).length (chalVH H.V.basis χ)
    (pubVH δF H.V.basis H.V.claim x (rhoVS H t χ) χ) (wkLn (χ cAlphaW)) (wkCnt (fW t) (χ cAlphaW))
    (wkAcc (F := F) (fW t) (χ cAlphaW) (χ cGamW) H.d.cells) H.V.computeNodes (tableVS hC).width

/-- The honest cell twin trace. -/
def qCellVS (χ : Coins frameVS K) : Fin 232 → F[X] :=
  CellTraceH.cellTraceH δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
    (chalsVS δF χ) (pubsCH δF (rhoVS H t χ) (H.yTot (toVCL χ)) (yHVS H χ))
    (cellColB H (claimBinds H.V.claim) (toVCL χ)) (mhvH H (bfsRows (airReorder t)))

/-- The honest walk twin trace. -/
def qWalkVS (χ : Coins frameVS K) : Fin 151 → F[X] :=
  WalkTraceH.walkTraceH δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
    (chalsVS δF χ) (pubsWH δF (rhoVS H t χ) (H.yTot (toVCL χ)) (yHVS H χ)) (walkColVS H χ)
    (kLvH H) (vLvH H) (kRvH H) (vRvH H)

theorem width_VS_cell (tt : Fin (shapeVS hT hP).k) (h : (tt : ℕ) = 0) :
    ((shapeVS hT hP).table tt).width = 232 := by
  change (if (tt : ℕ) = 0 then (⟨232, colRoundCH, hT⟩ : TableSpec) else ⟨151, colRoundWH, hP⟩).width = 232
  rw [if_pos h]

theorem width_VS_walk (tt : Fin (shapeVS hT hP).k) (h : ¬ (tt : ℕ) = 0) :
    ((shapeVS hT hP).table tt).width = 151 := by
  change (if (tt : ℕ) = 0 then (⟨232, colRoundCH, hT⟩ : TableSpec) else ⟨151, colRoundWH, hP⟩).width = 151
  rw [if_neg h]

/-- **The honest VS messages of a run** (claim message `x`). -/
def msgVS {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}
    (x : ClaimMsgVS) : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM) where
  Qc := qcVS H t x
  Qm := fun χ tt j =>
    if h : (tt : ℕ) = 0 then qCellVS H t χ ⟨j, lt_of_lt_of_eq j.isLt (width_VS_cell tt h)⟩
    else qWalkVS H t χ ⟨j, lt_of_lt_of_eq j.isLt (width_VS_walk tt h)⟩
  msg0C := x
  msg0M := ()
  requests := rhoVS H t
  msg2M := fun χ => (H.yTot (toVCL χ), yHVS H χ)

end Msg

section Accepted
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {hT hP hC kr : ℕ} (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- `hlen` from the datum's size fields. -/
theorem cells_len_lt : H.d.cells.length < ringChar F := by
  have := H.hrows (tCW hT hP); rw [H.hC0] at this; omega

/-- **`honest_accepted_VS_run`: the honest VS run is accepted at `frameVS` outside the honest bad events.** -/
theorem honest_accepted_VS_run
    {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
    {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow Kg)} {result : Noun}
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hd : H.d = demandH2 (bfsRows (airReorder t)))
    (x : ClaimMsgVS) (hm : HonestClaimMsgFull H.d.cells H.V.claim x)
    (hN : (vsOf H.V).N = (bfsForest [airReorder t]).length)
    (hinj : Function.Injective (vsOf H.V).computeNodes) (hadj : (vsOf H.V).AdjacentC)
    (hroot : (rowAtW (bfsForest [airReorder t]) 1).s = H.V.claim.subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = H.V.claim.formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = H.V.claim.result)
    (hbs : ∀ b ∈ (claimBinds H.V.claim).flatMap selfCell, b ∈ H.d.cells)
    (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) (hreads : H.d.reads = [])
    (hat : ∀ g ∈ bfsRows (airReorder t),
      AtomsLt (ringChar F) (rowOfSkelH g.skel).sf1 ∧ AtomsLt (ringChar F) (rowOfSkelH g.skel).sf2)
    (χ : Coins frameVS K)
    (hbf : HonestBadFreeVSB H (claimBinds H.V.claim) χ (rhoVS H t χ) (H.yTot (toVCL χ)) (yHVS H χ)
      (mhvH H (bfsRows (airReorder t))) (kLvH H) (vLvH H) (kRvH H) (vRvH H))
    (hnb : ∀ r < (vsOf H.V).N, NotBadRow (gE (vsOf H.V).basis (baseEnvC H.d.cells (wRows (bfsForest [airReorder t]))
        (bfsForest [airReorder t]).length (chalVH (vsOf H.V).basis χ)
        (pubVH δF (vsOf H.V).basis (vsOf H.V).claim x (rhoVS H t χ) χ) r))
      (baseEnvC H.d.cells (wRows (bfsForest [airReorder t])) (bfsForest [airReorder t]).length
        (chalVH (vsOf H.V).basis χ) (pubVH δF (vsOf H.V).basis (vsOf H.V).claim x (rhoVS H t χ) χ) r))
    (hord : (bfsForest [airReorder t]).length ≤ orderOf (χ cAlphaW)) :
    AcceptsG (vsOf H.V) (msgVS (sumC := sumC) (sumM := sumM) H t x) χ := by
  have hsem := run_rows_sem hrun
  have hpk := run_rows_pks hrun
  have hρ3 : Quad.re _ (rhoVS H t χ 3) = accSumX H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVH H.V.basis χ) (bfsForest [airReorder t]).length := by
    simp [rhoVS, Quad.re_mk]
  have hρ4 : Quad.re _ (rhoVS H t χ 4) = accSumP H.V.basis H.d.cells (wRows (bfsForest [airReorder t]))
      (chalVH H.V.basis χ) (bfsForest [airReorder t]).length := by
    simp [rhoVS, Quad.re_mk]
  have hcl : HonestClaimMsg H.d.cells (vsOf H.V).claim x := fun k hk => by rw [hm k hk]; rfl
  have hcomp := hcomp_pinned (sumC := sumC) (sumM := sumM) H (msgVS H t x) χ hrun hd hN hinj hadj hcl hroot hord
    (by rw [hN]; exact hρ3) (by rw [hN]; exact hρ4) hat hnb rfl
  refine honest_accepted_VS' H (msgVS H t x) χ (rhoVS H t χ) (H.yTot (toVCL χ)) (yHVS H χ)
    (mhvH H (bfsRows (airReorder t))) (kLvH H) (vLvH H) (kRvH H) (vRvH H) rfl rfl
    (fun j => ?_) (fun j => ?_) hbf rfl ?_ rfl rfl (kLvH_bool H) (kRvH_bool H)
    (hpubC_honest H χ _ _ _ hd hsem hpk (cells_len_lt H) hslot hρ3)
    (hpubX_honest H χ _ _)
    (hpubP_honest H χ _ _ _ hd hsem hρ4)
    hslot hreads hadj hinj hbs hm (by simp [rhoVS, Quad.im_mk]) (by simp [rhoVS, Quad.im_mk]) hcomp
  · simp only [msgVS]; exact dif_pos rfl
  · simp only [msgVS]; exact dif_neg Nat.one_ne_zero
  · show H.xTot (toVCL χ) - H.yTot (toVCL χ) + H.yTot (toVCL χ) = H.xTot (toVCL χ)
    exact sub_add_cancel _ _

end Accepted

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
