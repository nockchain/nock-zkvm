/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/CanonOrbP1.lean

 **Trace uniqueness on the P1 fragment: the canonical trace and message at a parameter orbit.**

 * §1 `trCanon` / `msgCanon`: twins of `ComplJ8Of.trOf` / `msgOf` whose tables are interpolated over the nodes
 `i ↦ ω^i` of an ARBITRARY strict orbit `o` (in use: the canonical layout's `omegaG` orbit), with the P1
 constants: the J trace and the atom-walk trace are `0`, the J and atom-walk publics are `0`, and the claim
 message carries the serial of each cell claim noun and nothing else (`mCanon`).
 * §2 the claim message: `mCanon` and the honest `mCOf` give the same claim handles, labels, compute publics and
 claim records, so `AcceptsJ8V` transports from the one to the other (`accepts_mCanon`).
 * §3 `DegOK` of the canonical trace at the canonical layout (`trCanon_degOK`): every table is an interpolant over
 its own distinct nodes; `J = 0` at `nJ = 0`; `V = 0`.
 * §4 `MsgSupp` of the canonical message (`msgCanon_supp`).
 * §5 E9: the honest compute walk inverse `wInv` (columns `120..122`) is `0` at the last row
 (`trCOf_wInv_last`, `trCanon_wInv_last`): its value is `(cnt − ln)⁻¹` at the walk's end, and `cnt = ln` there
 (tiling, `foCol_Sf_tilingF`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
import Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun isCellN claimH labelF)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' claimRecsJ8 claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

noncomputable section

/-! ## 1. The canonical trace and message at a parameter orbit -/

/-- **The canonical claim message**: the handle serial of each cell claim noun; `0` on atom claim nouns; no rank
limbs (the verifier recomputes them, `claimRecsJ8`). -/
def mCanon (c : P8PublicClaim) (H : Noun → ℕ × ℕ) : FrameVS.ClaimMsgVS := fun k =>
  (if isCellN (claimNoun c k) then (H (claimNoun c k)).2 else 0, 0, 0)

section Defs
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
  (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) (hA : 0 < D.acs.length)
  {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)

/-- **The canonical trace at a coin**: `trOf` with every table over the nodes `powN o`, `J = V = 0`. -/
def trCanon (χ : Coins frameJ8 K) : TrJ8 (ZMod p) where
  C := ComplJ8Comp.trCOf δ b D.H D.pd (bfsForest [D.t]) (cJ s f r) χ (powN o (bfsForest [D.t]).length)
  M := ComplJ8Enc.cellTrME δ b hC (powN o _) o (chalsMJ8 δ)
    (pubsCOf δ b D hC o) (γV δ) (ρV δ) (zJ δ) (encR δ) (bigOf D) D.cells (mvF D) (mxF D) (fun _ => 0) (mhF D) χ
  W := ComplJ8Enc.walkTrWE δ b (walk_pos D.cells D.reads) (powN o _) o (chalsMJ8 δ)
    (pubsWOf δ b D o) (γV δ) (ρV δ) (encR δ) D.cells D.reads (kLW D) (vLW D) (kRW D) (vRW D) χ
  J := fun _ => 0
  A := trAOf δ b D hA o χ
  V := fun _ => 0

/-- **The canonical message at a coin**: `msgOf` at the orbit `o`, the claim message `mCanon`, `J` and atom-walk
publics `0`. -/
def msgCanon (χ : Coins frameJ8 K) : MsgJ8' p K δ where
  m := mCanon (cJ s f r) D.H
  ρ := ComplJ8Comp.ρCOf δ b D.H D.pd (bfsForest [D.t]) (cJ s f r) χ
  ρS := ComplJ8Comp.ρSCOf δ b D.H D.pd (bfsForest [D.t]) (cJ s f r) χ
  pubsC := pubsCOf δ b D hC o χ
  pubsW := pubsWOf δ b D o χ
  pubsJ := fun _ => 0
  pubsA := pubsAOf δ b D hA o χ
  pubsV := fun _ => 0

end Defs

/-! ## 2. The claim message -/

section Claim
variable {F : Type} [Field F]

/-- `mCanon` and the honest claim message `mCOf` give the same claim handles. -/
theorem claimH_mCanon (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (k : Fin 3) :
    claimH c (mCanon c H) k = claimH c (ComplJ8Comp.mCOf H c) k := by
  unfold claimH mCanon ComplJ8Comp.mCOf
  rcases hk : claimNoun c k with v | ⟨x, y⟩
  · simp [claimHandle]
  · simp [claimHandle, isCellN]

/-- Two claim messages with the same handles have the same label. -/
theorem labelF_congr (c : P8PublicClaim) {m m' : FrameVS.ClaimMsgVS} (hH : ∀ k, claimH c m k = claimH c m' k) :
    labelF (F := F) c m = labelF (F := F) c m' := by
  simp only [labelF, hH]

/-- Two claim messages that agree on the cell serials have the same claim records. -/
theorem claimRecs_congr {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [Fintype K]
    (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
    (χ : Coins frameJ8 K) (c : P8PublicClaim) {m m' : FrameVS.ClaimMsgVS}
    (hI : ∀ k, isCellN (claimNoun c k) = true → (m k).1 = (m' k).1) :
    claimRecsJ8 δ χ c m = claimRecsJ8 δ χ c m' := by
  unfold claimRecsJ8
  refine List.map_congr_left fun k hk => ?_
  have : isCellN (claimNoun c k) = true := by
    unfold claimCells at hk
    simpa using (List.mem_filter.mp hk).2
  rw [hI k this]

end Claim

section ClaimV
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K} [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- Two claim messages with the same handles give the same compute publics. -/
theorem pubVJ8_congr (c : P8PublicClaim) {m m' : FrameVS.ClaimMsgVS} (hH : ∀ k, claimH c m k = claimH c m' k)
    (ρ : Fin 5 → Quad (algebraMap (ZMod p) K δ)) (ρS : Quad (algebraMap (ZMod p) K δ)) (χ : Coins frameJ8 K) :
    pubVJ8 δ b c m ρ ρS χ = pubVJ8 δ b c m' ρ ρS χ := by
  have hL := labelF_congr (F := ZMod p) c hH
  funext j
  simp only [pubVJ8, FrameVSQ.pubVHQ, FrameVS.pubVH, FrameVS.seedVS, hL]

/-- **`AcceptsJ8V` reads the claim message only through the claim handles and the cell serials.** -/
theorem accepts_m_congr {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (hacc : AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r g) (m' : FrameVS.ClaimMsgVS)
    (hH : ∀ k, claimH c m' k = claimH c M.m k)
    (hI : ∀ k, isCellN (claimNoun c k) = true → (m' k).1 = (M.m k).1) :
    AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ { M with m := m' } tr r g := by
  have hp := pubVJ8_congr (b := b) c hH M.ρ M.ρS χ
  have hr := claimRecs_congr δ χ c hI
  obtain ⟨mm, ρ, ρS, pC, pW, pJ, pA, pV⟩ := M
  dsimp only at hp hr hH hI ⊢
  exact
  { hsatX := by rw [hp]; exact hacc.hsatX
    hinjX := hacc.hinjX
    hadjX := hacc.hadjX
    hsatC := hacc.hsatC
    hbindC := hacc.hbindC
    hinjC := hacc.hinjC
    hadjC := hacc.hadjC
    hnpC := hacc.hnpC
    hsatW := hacc.hsatW
    hbindW := hacc.hbindW
    hinjW := hacc.hinjW
    hadjW := hacc.hadjW
    hkW := hacc.hkW
    hknW := hacc.hknW
    hkpW := hacc.hkpW
    hJk := hacc.hJk
    hsatA := hacc.hsatA
    hbindA := hacc.hbindA
    hinjA := hacc.hinjA
    hadjA := hacc.hadjA
    hnpA := hacc.hnpA
    hVk := hacc.hVk
    hGx := hacc.hGx
    hGp := hacc.hGp
    hGS := hacc.hGS
    hlay := hacc.hlay
    hsmall := hacc.hsmall
    huniq := hacc.huniq
    hTpl := hacc.hTpl
    hnd := hacc.hnd
    hidx := hacc.hidx
    hrk := hacc.hrk
    hlt := hacc.hlt
    hsumC' := by rw [hr]; exact hacc.hsumC'
    hbalA' := hacc.hbalA'
    hvalA0 := hacc.hvalA0
    hfxC := hacc.hfxC
    hfxA := hacc.hfxA
    hclA := hacc.hclA
    hclI := fun k hk => by rw [hI k hk]; exact hacc.hclI k hk
    hclR := hacc.hclR
    hcen := hacc.hcen
    hlenC := hacc.hlenC
    hlenA := hacc.hlenA
    hcellF := hacc.hcellF
    hnA62 := hacc.hnA62
    hbud := hacc.hbud
    hbudV := hacc.hbudV
    hsatL := hacc.hsatL
    hbindL := hacc.hbindL }

/-- **The honest claim message can be replaced by `mCanon`.** -/
theorem accepts_mCanon {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (H : Noun → ℕ × ℕ)
    (hm : M.m = ComplJ8Comp.mCOf H c) (hacc : AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r g) :
    AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ { M with m := mCanon c H } tr r g := by
  refine accepts_m_congr hacc _ (fun k => by rw [hm]; exact claimH_mCanon c H k) fun k hk => ?_
  rw [hm]; simp [mCanon, ComplJ8Comp.mCOf, hk]

end ClaimV

/-! ## 3. `DegOK` of the canonical trace -/

section Deg
variable {p : ℕ} [Fact p.Prime]

theorem deg_interp {n : ℕ} (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes) (v : Fin n → ZMod p) :
    (Lagrange.interpolate Finset.univ nodes v).degree < (n : WithBot ℕ) := by
  have := Lagrange.degree_interpolate_lt (s := Finset.univ) v hinj.injOn
  rwa [Finset.card_univ, Fintype.card_fin] at this

theorem powN_inj {h n : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hn : n ≤ 2 ^ h) :
    Function.Injective (powN o n) := (powN_ok o hn).1

variable {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
  (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) (hA : 0 < D.acs.length)

/-- **`DegOK` of the canonical trace at the canonical layout of sizes `sz`**: when the layout's compute, cell and
walk sizes are the datum's and the atom table is the single pad row, every column of `trCanon` (at the layout's
own orbit) has degree below its table height. -/
theorem trCanon_degOK (hpG : p = Nock.Atoms.p) (sz : SizesP1) (χ : Coins frameJ8 K) (ax : AuxP1 (ZMod p))
    (hn : sz.n = (bfsForest [D.t]).length) (hnC : sz.nC = D.cells.length)
    (hnW : sz.nW = (walkRows D.cells D.reads).length) (hA1 : D.acs.length = 1)
    (hauxM : ∀ j, (ax.M j).degree < (sz.nC : WithBot ℕ)) (hauxW : ∀ j, (ax.W j).degree < (sz.nW : WithBot ℕ)) :
    DegOK (canonPbOf hpG sz) (trCanon δ b D hC hA (canonPbOf hpG sz).orbit χ) ax := by
  have hfit := sz.fit_ht
  have hfn : (bfsForest [D.t]).length ≤ 2 ^ sz.ht := hn ▸ le_trans (le_max_left _ _) hfit
  have hfC : D.cells.length ≤ 2 ^ sz.ht := hnC ▸ le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hfit
  have hfW : (walkRows D.cells D.reads).length ≤ 2 ^ sz.ht :=
    hnW ▸ le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hfit
  have hfA : D.acs.length ≤ 2 ^ sz.ht := by rw [hA1]; exact Nat.one_le_two_pow
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, hauxM, hauxW⟩
  · rw [show (canonPbOf hpG sz).n = sz.n from rfl, hn]
    exact deg_interp _ (powN_inj _ hfn) _
  · rw [show (canonPbOf hpG sz).nC = sz.nC from rfl, hnC]
    exact deg_interp _ (powN_inj _ hfC) _
  · rw [show (canonPbOf hpG sz).nW = sz.nW from rfl, hnW]
    exact deg_interp _ (powN_inj _ hfW) _
  · show (0 : (ZMod p)[X]).degree < _
    rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
  · rw [show (canonPbOf hpG sz).nA = 1 from rfl, ← hA1]
    exact deg_interp _ (powN_inj _ hfA) _
  · show (0 : (ZMod p)[X]).degree < _
    rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _

end Deg

/-! ## 4. `MsgSupp` of the canonical message -/

section Supp
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
  (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) (hA : 0 < D.acs.length)
  {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)

/-- **The extra pin (E6) for the canonical message**: every entry outside the read set is `0`. -/
theorem msgCanon_supp (χ : Coins frameJ8 K) : MsgSupp (cJ s f r) (msgCanon δ b D hC hA o χ) where
  mRk := fun k => rfl
  mAtom := fun k hk => by simp [msgCanon, mCanon, hk]
  rho := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [msgCanon, ComplJ8Comp.ρCOf]
  pubsC := fun j hj => by
    simp only [msgCanon, pubsCOf]
    rw [if_neg (by omega), if_neg (by omega)]
  pubsW := fun j hj => by
    simp only [msgCanon, pubsWOf]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  pubsJ := fun j => rfl
  pubsA := fun j hj => by
    simp only [msgCanon, pubsAOf]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  pubsV := fun j => rfl

end Supp

/-! ## 5. the extra pin (E9): the honest compute walk inverse at the last row -/

section E9
open Nock.NockVMROM.Thm54.VclL.HonestTraceX
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] [DecidableEq F]

/-- **Tiling**: at the end of the BFS walk of one tree the counter equals the line, `cnt(h) = ln(h)`. -/
theorem cntW_last (t : NTree SkelX) (α : K) :
    cntW (bfsForest [t]) α (bfsForest [t]).length = lnW α (bfsForest [t]).length := by
  have ht := foCol_Sf_tilingF [t] (List.cons_ne_nil _ _)
  simp only [List.length_singleton] at ht
  simp only [cntW, lnW, Nock.NockVMROM.Thm54.VclL.Compute.TowerD.cntClosed,
    Nock.NockVMROM.Thm54.VclL.Compute.TowerD.lnClosed]
  rw [← pow_succ']
  exact congrArg (fun e => α ^ e) (by omega)

/-- **The extra pin (E9) at the honest compute row values**: the walk inverse limbs `120..122` vanish at the last row. -/
theorem trX_wInv_last (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
    (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (t : NTree SkelX) (chalV pubVal : ℕ → F)
    (α : K) (acc : ℕ → K) (k : ℕ) (hk : k < 3) :
    trX b δ H pd (bfsForest [t]) chalV pubVal (lnW α) (cntW (bfsForest [t]) α) acc
      ((bfsForest [t]).length - 1) (120 + k) = 0 := by
  have hpos := bfs_pos t
  unfold trX
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have h1 : (120 + k - 111) / 3 = 3 := by omega
  have h2 : (120 + k - 111) % 3 = k := by omega
  have h3 : (bfsForest [t]).length - 1 + 1 = (bfsForest [t]).length := by omega
  rw [h1, h2, h3]
  show cNA b ((cntW (bfsForest [t]) α (bfsForest [t]).length - lnW α (bfsForest [t]).length)⁻¹) k = 0
  rw [cntW_last, sub_self, inv_zero]
  simp [cNA, coord]

end E9

section E9C
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
  (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) (hA : 0 < D.acs.length)
  {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)

/-- **The extra pin (E9) at the canonical trace**: at the last compute node, the walk inverse columns `120..122` evaluate to `0`
(so the side gate `isLast·wInv` of `canonC2` holds there). -/
theorem trCanon_wInv_last (χ : Coins frameJ8 K) (hfit : (bfsForest [D.t]).length ≤ 2 ^ h) (k : ℕ) (hk : k < 3) :
    ((trCanon δ b D hC hA o χ).C ⟨120 + k, by omega⟩).eval
      (powN o (bfsForest [D.t]).length ⟨(bfsForest [D.t]).length - 1, by have := bfs_pos D.t; omega⟩) = 0 := by
  show (ComplJ8Comp.trCOf δ b D.H D.pd (bfsForest [D.t]) (cJ s f r) χ _ _).eval _ = 0
  unfold ComplJ8Comp.trCOf
  rw [HonestTraceX.polyX_eval _ _ _ _ _ _ _ _ _ _ _ (powN_inj o hfit)]
  exact trX_wInv_last b δ D.H D.pd D.t _ _ _ _ k hk

end E9C

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1.claimH_mCanon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1.pubVJ8_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1.accepts_m_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1.accepts_mCanon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1.trCanon_degOK
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1.msgCanon_supp
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1.cntW_last
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1.trX_wInv_last
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1.trCanon_wInv_last
