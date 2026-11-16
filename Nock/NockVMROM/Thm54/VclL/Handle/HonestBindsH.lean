/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestBindsH.lean

The 39th's honest datum `HonestVCLW` has its validity consumers `vcsOf cells []` (no root bindings), so
  its validity total is `0` (P4-6h finding).  Here the cell rows are re-generated over `vcsOf cells binds`
  with `binds` = the claim's nouns, over the SAME datum (`H : HonestVCLW`, nothing existing edited):
  * `cellRowsB H bs`, `vTotB`, `xTotB`, `cellColB`, `keys0B/1B`;
  * `vTotB_eq` (`cell_vTotal`): the validity total is `Σ_{b ∈ bs.flatMap selfCell} cinv (vReq b)`;
  * `xTotB_eq`, `keys0B_eq`, `keys1B_eq`: the export total and the pole keys do not read the validity
    multiplicity, so they ARE the 39th's;
  * `claimRecs_eq_vReq` / `vTotB_eq_claimValSum`: for `bs = [subject, formula, result]` and the honest claim
    message (serial `idxOf`, rank limbs) the validity total IS the verifier-computed `claimValSum` at the
    `frameVS` coins.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestClaimH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Noun Nock.Walk Nock.Reified Nock.Framework Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.TraceGen
open scoped Polynomial

noncomputable section

section Binds
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}
  (H : HonestVCLW (K := K) δF hT hP hC kr) (bs : List Noun)

/-- The honest cell rows over the validity consumers `vcsOf cells bs` (the claim's root bindings). -/
def cellRowsB (z : Quad (algebraMap F K δF)) : ℕ → CellVals F (Quad (algebraMap F K δF)) :=
  cellRows0 δF z H.d.cells (vcsOf H.d.cells bs) (xs0W H.d) (xs1W H.d)

def vTotB (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  ∑ k ∈ Finset.range (H.V.memRows (tCW hT hP)),
    vTermOf δF (cellFillInv δF (γC χ) (ρC χ) (cellRowsB H bs (zC χ) k))

def xTotB (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  ∑ k ∈ Finset.range (H.V.memRows (tCW hT hP)),
    xTermOf δF (cellFillInv δF (γC χ) (ρC χ) (cellRowsB H bs (zC χ) k))

/-- The honest cell columns over `cellRowsB` at the old coins. -/
def cellColB (χ : Coins frameVCL K) : ℕ → Fin (H.V.memRows (tCW hT hP)) → F :=
  cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
    cellFill δF (γC χ) (ρC χ) (cellRowsB H bs (zC χ)) i')

theorem cellRowsB_nil (z : Quad (algebraMap F K δF)) : cellRowsB H [] z = H.cellRows z := rfl

/-- The pole keys read no validity multiplicity: the validity keys are the 39th's. -/
theorem keys0B_eq (χ : Coins frameVCL K) (j : ℕ) :
    vKeyOf δF (cellRowsB H bs (zC χ) j) = vKeyOf δF (H.cellRows (zC χ) j) ∧
    lKeyOf δF (cellRowsB H bs (zC χ) j) = lKeyOf δF (H.cellRows (zC χ) j) ∧
    rKeyOf δF (cellRowsB H bs (zC χ) j) = rKeyOf δF (H.cellRows (zC χ) j) :=
  ⟨rfl, rfl, rfl⟩

theorem keys1B_eq (χ : Coins frameVCL K) (j : ℕ) (b : Bool) :
    xKeyOf δF (cellRowsB H bs (zC χ) j) (if b then 1 else 0) =
      xKeyOf δF (H.cellRows (zC χ) j) (if b then 1 else 0) := rfl

theorem xTotB_eq (hslot : ∀ r ∈ pathReads H.d.preads, (Noun.slot r.2 r.1).isSome) (χ : Coins frameVCL K) :
    xTotB H bs χ = H.xTot χ := by
  obtain ⟨hnd, -, -⟩ := H.cells_hyps
  have h := fun vcs => cell_xTotal (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells vcs (xs0W H.d) (xs1W H.d)
      hnd (H.xs0W_subset hslot) H.xs1W_subset
  unfold xTotB HonestVCLW.xTot cellRowsB HonestVCLW.cellRows
  rw [H.hC0, h, h]

/-- **The validity total over `bs`** (`cell_vTotal`): `Σ_{b ∈ bs.flatMap selfCell} cinv (vReq b)`. -/
theorem vTotB_eq (hbs : ∀ b ∈ bs.flatMap selfCell, b ∈ H.d.cells) (χ : Coins frameVCL K) :
    vTotB H bs χ = ((bs.flatMap selfCell).map fun c => cinv δF (γC χ) (ρC χ) (vReq δF (zC χ) H.d.cells c)).sum := by
  obtain ⟨hnd, hcell, hclosed⟩ := H.cells_hyps
  unfold vTotB cellRowsB
  rw [H.hC0]
  exact cell_vTotal (δF := δF) (γC χ) (ρC χ) (zC χ) H.d.cells bs (xs0W H.d) (xs1W H.d) hnd hcell hclosed hbs

end Binds

section ClaimId
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}
  (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- **The honest claim message in full**: every cell claim noun carries its serial `idxOf` in `cells` and its
rank limbs `(rank / 2^62, rank % 2^62)`. -/
def HonestClaimMsgFull (cells : List Noun) (c : P8PublicClaim) (m : ClaimMsgVS) : Prop :=
  ∀ k : Fin 3, (claimNoun c k).isCell = true →
    m k = (cells.idxOf (claimNoun c k), rankOf (claimNoun c k) / 2 ^ 62, rankOf (claimNoun c k) % 2 ^ 62)

/-- The claim's nouns, as the binds list. -/
def claimBinds (c : P8PublicClaim) : List Noun := [c.subject, c.formula, c.result]

theorem claimKey_eq_vReq (χ : Coins frameVS K) (cells : List Noun) (c : P8PublicClaim) (m : ClaimMsgVS)
    (hm : HonestClaimMsgFull cells c m) (k : Fin 3) (hk : (claimNoun c k).isCell = true) :
    claimKey δF χ (claimNoun c k) (m k) = vReq δF (zC (δF := δF) (toVCL χ)) cells (claimNoun c k) := by
  rw [hm k hk]
  have hz : zVS δF χ = zC (δF := δF) (toVCL χ) := rfl
  unfold claimKey vReq
  rw [hz]
  generalize GlobalCarryRecognizer.enc (zC (δF := δF) (toVCL χ)) (claimNoun c k) = e
  generalize rankOf (claimNoun c k) = r
  generalize cells.idxOf (claimNoun c k) = j
  show ![_, _, _, _, _] = ![_, _, _, _, _]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  exact Quad.mk_base (algebraMap F K δF) _

theorem claimRecs_eq_vReq (χ : Coins frameVS K) (cells : List Noun) (c : P8PublicClaim) (m : ClaimMsgVS)
    (hm : HonestClaimMsgFull cells c m) :
    claimRecs δF c m χ = ((claimBinds c).flatMap selfCell).map (vReq δF (zC (δF := δF) (toVCL χ)) cells) := by
  have h0 := fun hk => claimKey_eq_vReq (δF := δF) χ cells c m hm 0 hk
  have h1 := fun hk => claimKey_eq_vReq (δF := δF) χ cells c m hm 1 hk
  have h2 := fun hk => claimKey_eq_vReq (δF := δF) χ cells c m hm 2 hk
  simp only [claimNoun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2
  unfold claimRecs claimBinds
  have hf : List.finRange 3 = [0, 1, 2] := by decide
  rw [hf]
  simp only [claimNoun, List.filter_cons, List.filter_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  generalize c.subject = a at *
  generalize c.formula = b at *
  generalize c.result = r at *
  cases a <;> cases b <;> cases r <;> simp_all [selfCell, isCellN, Noun.isCell]

/-- **The honest validity total over the claim's nouns IS the verifier-computed `claimValSum`.** -/
theorem vTotB_eq_claimValSum (hbs : ∀ b ∈ (claimBinds H.V.claim).flatMap selfCell, b ∈ H.d.cells)
    (m : ClaimMsgVS) (hm : HonestClaimMsgFull H.d.cells H.V.claim m) (χ : Coins frameVS K) :
    vTotB H (claimBinds H.V.claim) (toVCL χ) = claimValSum δF H.V.claim m χ := by
  rw [vTotB_eq H _ hbs, claimValSum, claimRecs_eq_vReq (δF := δF) χ H.d.cells H.V.claim m hm,
    List.map_map]
  rfl

end ClaimId

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
