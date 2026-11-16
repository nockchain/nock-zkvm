/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BComp.lean

  **J-9 B completeness : the compute chip at the J-9 publics `pubVJ9`.**  New module, additive.
  Generic over the honest data `H`, `pd`, `W = bfsForest [t]` and the claim `c` (as `ComplJ8Comp`).

  * `pubCOf9` / `trCOf9`: `ComplJ8Comp.pubCOf` / `trCOf` at `ClaimJ9.pubVJ9`;
  * `claimKH_hdl`: under `HdlOK p H`, the J-9 claim handle of a noun at its own serial IS `H x` (small, big, cell);
    so `labelJ9 = hlX H (s, f, r)` (`labelJ9_eq`) with NO claim-leaf bound (J-8's `hcl` is gone);
  * `hpIC9 hpO9 hρ9 hpub9 hpS9`: the compute walk / claim / terminal publics; `staged_trCOf9`;
  * **`computeChip_sat9`**: the compute chip honest at the generated tree at `pubVJ9` (one chip template; the
    good-coin events `hord hnb` are inputs, as `ComplJ8Comp.computeChip_sat`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BComp

open Nock Nock.Noun Nock.Walk Nock.Edit Nock.Edit.GenX Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (chalAlphaW chalGammaW pubIC pubSeed pubOut pubRhoX pubRhoP)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ (pubRhoXIm pubRhoPIm)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.HonestTraceX
open Nock.NockVMROM.Thm54.VclL.Handle.HonestWalkX
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (rkC)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp (mCOf ρCOf ρSCOf pubCOf)

noncomputable section

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (c : P8PublicClaim)

/-- **The J-9 compute publics of the honest message** (`pubVJ9` at J-8's message, terminals). -/
def pubCOf9 (χ : Coins frameJ8 K) : ℕ → ZMod p :=
  ClaimJ9.pubVJ9 δ b c (mCOf H c) (ρCOf δ b H pd W c χ) (ρSCOf δ b H pd W c χ) χ

/-- The honest J-9 compute trace `polyX` at `pubCOf9` (width `123`). -/
def trCOf9 (χ : Coins frameJ8 K) {n : ℕ} (nodes : Fin n → ZMod p) : Fin 123 → (ZMod p)[X] :=
  polyX b δ H pd W (chalVJ8 b χ) (pubCOf9 δ b H pd W c χ) (lnW (InhabJ8Comp.αC0 b χ)) (cntW W (InhabJ8Comp.αC0 b χ))
    (accW (F := ZMod p) H W (InhabJ8Comp.αC0 b χ) (InhabJ8Comp.γC0 b χ)) nodes 123

/-- `pubVJ9` agrees with `pubVJ8` at publics `≥ 12`. -/
theorem pub9_hi (χ : Coins frameJ8 K) (j : ℕ) (hj : 12 ≤ j) : pubCOf9 δ b H pd W c χ j = pubCOf δ b H pd W c χ j :=
  ClaimJ9.pubVJ9_hi δ b c _ _ _ χ j hj

theorem hpIC9 (χ : Coins frameJ8 K) : limbVal b (pubCOf9 δ b H pd W c χ) pubIC = InhabJ8Comp.αC0 b χ :=
  ClaimJ9.pubVJ9_IC δ b c _ _ _ χ

theorem hpO9 (χ : Coins frameJ8 K) : limbVal b (pubCOf9 δ b H pd W c χ) pubOut = 0 :=
  ClaimJ9.pubVJ9_out δ b c _ _ _ χ

theorem hρ9 (χ : Coins frameJ8 K) :
    ∀ a < 6, ∀ k : Fin 3, pubCOf9 δ b H pd W c χ (pubOfA a + k) =
      coord b (accV b δ H pd W (chalVJ8 b χ) (pubCOf9 δ b H pd W c χ) a W.length) k := by
  intro a ha k
  have h12 : 12 ≤ pubOfA a + k := by
    interval_cases a <;> simp [pubOfA, pubRhoX, pubRhoXIm, pubRhoP, pubRhoPIm, pubRhoSX, pubRhoSXi] <;> omega
  rw [pub9_hi δ b H pd W c χ _ h12, ComplJ8Comp.hρ δ b H pd W c χ a ha k,
    InhabJ8Comp.accV_pub δ b H pd W (chalVJ8 b χ) (pubCOf δ b H pd W c χ) (pubCOf9 δ b H pd W c χ)]

variable {H} {c}

/-- **The J-9 claim handle is the handle map** (any noun, no leaf bound). -/
theorem claimKH_hdl (hH : HdlOK p H) (x : Noun) : ClaimJ9.claimKH p x (H x).2 = H x := by
  cases x with
  | atom v =>
    by_cases hv : p ≤ v
    · simp only [ClaimJ9.claimKH, if_pos hv]
      exact Prod.ext (hH.big v hv).symm rfl
    · simp only [ClaimJ9.claimKH, if_neg hv]
      rw [hH.small v (by omega)]
  | cell a d =>
    simp only [ClaimJ9.claimKH]
    exact Prod.ext (hH.cell a d).symm rfl

theorem labelJ9_eq (hH : HdlOK p H) :
    ClaimJ9.labelJ9 p c (mCOf H c) = hlX (F := ZMod p) H (c.subject, c.formula, c.result) := by
  unfold ClaimJ9.labelJ9 ClaimJ9.claimHJ9 hlX
  simp only [mCOf, claimKH_hdl hH, hk, hv]
  simp [claimNoun]

theorem pub9_lo (χ : Coins frameJ8 K) (j : ℕ) (hj : j < 6) :
    pubCOf9 δ b H pd W c χ j = (ClaimJ9.labelJ9 p c (mCOf H c)).getD j 0 :=
  ClaimJ9.pubVJ9_label δ b c _ _ _ χ j hj

theorem hpub9 (hH : HdlOK p H) (χ : Coins frameJ8 K) :
    pubCOf9 δ b H pd W c χ 0 = hk H c.subject ∧ pubCOf9 δ b H pd W c χ 1 = hv H c.subject ∧
    pubCOf9 δ b H pd W c χ 2 = hk H c.formula ∧ pubCOf9 δ b H pd W c χ 3 = hv H c.formula ∧
    pubCOf9 δ b H pd W c χ 4 = hk H c.result ∧ pubCOf9 δ b H pd W c χ 5 = hv H c.result := by
  have h := labelJ9_eq (c := c) hH
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [pub9_lo δ b pd W χ _ (by norm_num), h] <;> simp [hlX]

/-- The walk seed at `pubVJ9`. -/
theorem hpS9 (hH : HdlOK p H) {t : NTree SkelX} (hW : W = bfsForest [t])
    (hroot : tripOf t = (c.subject, c.formula, c.result)) (χ : Coins frameJ8 K) :
    limbVal b (pubCOf9 δ b H pd W c χ) pubSeed =
      curW (F := ZMod p) H W (InhabJ8Comp.γC0 b χ) 1 * InhabJ8Comp.αC0 b χ := by
  have hcur : curW (F := ZMod p) H W (InhabJ8Comp.γC0 b χ) 1 =
      Nock.NockVMROM.Thm54.VclL.Handle.rlcL (InhabJ8Comp.γC0 b χ) 0
        ((hlX (F := ZMod p) H (c.subject, c.formula, c.result)).map (algebraMap (ZMod p) K)) := by
    have hne : [t] ≠ [] := List.cons_ne_nil _ _
    have h0 : W[0]? = some t := by
      rw [hW, bfsForest_cons_eq _ hne]; simp
    simp only [curW, Walk.curCol, h0, Nat.sub_self, Option.map_some, Option.getD_some, nodeValX, lblX, hroot]
  rw [hcur, InhabJ8Comp.αC0_eq, InhabJ8Comp.γC0_eq]
  rw [show limbVal b (pubCOf9 δ b H pd W c χ) pubSeed = ClaimJ9.seedJ9 (p := p) c (mCOf H c) (toVS (toVSQ χ)) from
    ClaimJ9.limb_pubVJ9_seed δ b c _ _ _ χ]
  unfold ClaimJ9.seedJ9
  rw [labelJ9_eq hH]
  simp [hlX, Nock.NockVMROM.Thm54.VclL.Handle.rlcL, toVS, toVSQ, cAlphaW, cGamW, List.zipIdx]
  ring

/-- **The J-9 compute trace is staged.** -/
theorem staged_trCOf9 {n : ℕ} (nodes : Fin n → ZMod p) :
    StagedCols frameJ8 crC (fun χ => trCOf9 δ b H pd W c χ nodes) := by
  intro j χ χ' h
  unfold trCOf9 polyX
  refine congrArg (fun f => Lagrange.interpolate Finset.univ nodes f) (funext fun i => ?_)
  by_cases hj : (j : ℕ) < 69
  · rw [trX_base _ _ _ _ _ _ _ _ _ _ _ _ hj, trX_base _ _ _ _ _ _ _ _ _ _ _ _ hj]
  · have h0 := InhabJ8Stage.zero_of_one χ χ' (crC j) (by simp [crC, hj]) h
    have hcv := InhabJ8Stage.chalVJ8_agree b χ χ' h0
    have hα : InhabJ8Comp.αC0 b χ = InhabJ8Comp.αC0 b χ' := by
      rw [InhabJ8Comp.αC0_eq, InhabJ8Comp.αC0_eq, h0 _ rfl]
    have hγ : InhabJ8Comp.γC0 b χ = InhabJ8Comp.γC0 b χ' := by
      rw [InhabJ8Comp.γC0_eq, InhabJ8Comp.γC0_eq, h0 _ rfl]
    rw [InhabJ8Stage.trX_pub δ b _ _ _ _ (pubCOf9 δ b H pd W c χ) (pubCOf9 δ b H pd W c χ'), hcv, hα, hγ]

end Gen

section Chip
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

open Classical in
/-- **The compute chip, honest at the generated tree, at the J-9 publics** (one chip template): as
`ComplJ8Comp.computeChip_sat` with `pubCOf9` / `trCOf9`, and WITHOUT the claim-atom bound `hcl` (a big claim atom
is a kind-2 handle, `claimKH_hdl`). -/
theorem computeChip_sat9 {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX R fuel s f = some (t, r)) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ))
    (hH : HdlOK (ringChar (ZMod p)) H) (hp : 16 ≤ ringChar (ZMod p))
    (hsm : ∀ u, InTree t u → HonestRowX.SmallX (ringChar (ZMod p)) (rowOfSkelX u.label))
    (hpair : ∀ u, InTree t u → isPair H (rowOfSkelX u.label) → PairOK (F := ZMod p) (pd (rowOfSkelX u.label)))
    {hh n : ℕ} (hn : 0 < n) (hN : n = (bfsForest [t]).length) (nodes : Fin n → ZMod p)
    (orbit : StrictOrbitDomain (ZMod p) 3 hh) (hnodes : ∀ i, nodes i = orbit.ω ^ (i : ℕ)) (hle : n ≤ 2 ^ hh)
    (χ : Coins frameJ8 K)
    (hord : (bfsForest [t]).length ≤ orderOf (InhabJ8Comp.αC0 b χ))
    (hnb : ∀ j < n, ∀ S ∈ Nock.NockVMROM.Thm54.VclL.Handle.ChipHX.slotsX (F := ZMod p),
      HonestSlotX.dVal b δ S (env0 H pd (bfsForest [t]) (chalVJ8 b χ) (pubCOf9 δ b H pd (bfsForest [t]) (cJ s f r) χ) j) ≠ 0 ∨
        HonestSlotX.aVal b δ S (env0 H pd (bfsForest [t]) (chalVJ8 b χ) (pubCOf9 δ b H pd (bfsForest [t]) (cJ s f r) χ) j) = 0) :
    RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX hn nodes b δ (chalVJ8 b χ) (pubCOf9 δ b H pd (bfsForest [t]) (cJ s f r) χ) orbit)
      (trCOf9 δ b H pd (bfsForest [t]) (cJ s f r) χ nodes) := by
  have hlab := genX_label hgen
  have hroot : tripOf t = ((cJ s f r).subject, (cJ s f r).formula, (cJ s f r).result) := by
    simp [tripOf, cJ, hlab.1, hlab.2.1, hlab.2.2.1]
  have hH' : HdlOK p H := by rwa [ZMod.ringChar_zmod_n] at hH
  have hρ' := hρ9 δ b H pd (bfsForest [t]) (cJ s f r) χ
  rw [← hN] at hρ'
  exact computeChipVCLHX_honest_sat δ hgen H pd hH hp hsm hpair (InhabJ8Comp.αC0 b χ) (InhabJ8Comp.γC0 b χ)
    hord hn hN nodes (ComplJ8Comp.hinjX_of orbit nodes hnodes hle) b (chalVJ8 b χ)
    (pubCOf9 δ b H pd (bfsForest [t]) (cJ s f r) χ)
    orbit (fun i hi => ((ComplJ8Comp.hadjX_of orbit nodes hnodes i hi).trans (mul_comm _ _)))
    rfl rfl (hpIC9 δ b H pd _ _ χ) (hpS9 δ b pd _ hH' rfl hroot χ) (hpO9 δ b H pd _ _ χ)
    (hpub9 δ b pd _ hH' χ) hρ' hnb

end Chip

end
end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BComp
