/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8Q1.lean

* §1 **`walkDataOf_congr_off`**: the walk data reads only the restricted columns `< 93` OUTSIDE `14..20`
    (the `u` / certificate-bit block): `lblRow` reads B0 columns `4..8`, `keyRow` reads column `3`, and the
    gathered `𝕂` roles sit at columns `21 + 3r + k ≥ 21`.  So it is invariant under `WalkJ8.bitFix`
    (`walkDataOf_bitFix`): the part-13 "real mismatch" of `rdWW` is NOT a mismatch — no retarget, no figure
    change.
  * §2 **`layPb`**: the `TraceJ8.LayJ8` layout read off the verifier's `PubJ8` (compute `n`, cell `nC`, walk
    `nW` / `kroots`, atom `nA`, atom walk `nV` / `krootsV`); the J-8 data `realize40 L0 (layPb Pb …) hL`.
  * §3 **`rdWW_realize40`**: `LinkJ8.rdWW` at `L := realize40 L0 (layPb Pb …) hL`, any `L0`, any trace, any
    coins, any messages (no acceptance needed).
  * §4 **`rdWC_realize40`**: `LinkJ8.rdWC` at the same `L`, from `AcceptsJ8.hsatX` (every compute row's base
    gates hold, so its one-hot state is `stX`, which `TraceJ8.stOfEnv` recovers) and `17 < p`.
  * §5 **`linkJ8_L2`**: the two together.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8 bitFix bitFix_off)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayJ8 LayLe realize40 wdWJ8 cRowsJ8 envCJ8 stOfEnv
  stOfIdx stOfIdx_stIdx rowW_congr shV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (stIdx)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8 (stX stX_spec baseX_of_sat)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8 (rowW rowsWX)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8

noncomputable section

/-! ## 1. The walk data ignores the certificate block `14..20` -/

section Congr
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h)

/-- `lblRow` reads B0 columns `4..8` only (`< 14`). -/
theorem lblRow_congr14 {eK eK' : Env K} {eF eF' : Env F} (hK : ∀ r < 24, eK.trace r = eK'.trace r)
    (hF : ∀ j < 14, eF.trace j = eF'.trace j) : lblRow δF eK eF = lblRow δF eK' eF' := by
  simp only [lblRow, QFP.ev_var, ev_var, WChip.cL, WChip.cR, WChip.pre, WChip.ridx, WChip.len,
    WChip.pR, WChip.rootR, hF 7 (by norm_num), hF 8 (by norm_num), hF 4 (by norm_num),
    hF 5 (by norm_num), hF 6 (by norm_num), hK 0 (by norm_num), hK 1 (by norm_num),
    hK 2 (by norm_num), hK 3 (by norm_num), hK 4 (by norm_num), hK 5 (by norm_num),
    hK 18 (by norm_num), hK 19 (by norm_num), hK 20 (by norm_num), hK 21 (by norm_num),
    hK 22 (by norm_num), hK 23 (by norm_num)]
  rfl

/-- `keyRow` reads B0 column `3` only (`< 14`). -/
theorem keyRow_congr14 {eK eK' : Env K} {eF eF' : Env F} (hK : ∀ r < 24, eK.trace r = eK'.trace r)
    (hF : ∀ j < 14, eF.trace j = eF'.trace j) : keyRow δF eK eF = keyRow δF eK' eF' := by
  simp only [keyRow, QFP.ev_var, ev_var, WChip.idx, WChip.pR, WChip.lR, WChip.rR,
    hF 3 (by norm_num), hK 0 (by norm_num), hK 1 (by norm_num),
    hK 2 (by norm_num), hK 3 (by norm_num), hK 4 (by norm_num), hK 5 (by norm_num),
    hK 6 (by norm_num), hK 7 (by norm_num), hK 8 (by norm_num), hK 9 (by norm_num),
    hK 10 (by norm_num), hK 11 (by norm_num), hK 12 (by norm_num), hK 13 (by norm_num),
    hK 14 (by norm_num), hK 15 (by norm_num), hK 16 (by norm_num), hK 17 (by norm_num)]

/-- **The walk data reads only the columns `< 93` outside `14..20`**: any coins, any publics, any width. -/
theorem walkDataOf_congr_off {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hw : 93 ≤ w)
    (hw' : 93 ≤ w') (hQ : ∀ (j : ℕ) (hj : j < 93), (j < 14 ∨ 21 ≤ j) → Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩)
    (chals pubs chals' pubs' : ℕ → K) :
    walkDataOf δF kroots b hn nodes orbit chals pubs Q =
      walkDataOf δF kroots b hn nodes orbit chals' pubs' Q' := by
  have hF : ∀ i, ∀ j < 93, (j < 14 ∨ 21 ≤ j) → (Chips.ChipRAP.walkEnvF b hn nodes orbit chals pubs Q i).trace j =
      (Chips.ChipRAP.walkEnvF b hn nodes orbit chals' pubs' Q' i).trace j := by
    intro i j hj hoff
    unfold Chips.ChipRAP.walkEnvF
    rw [envOfTrace_trace Q _ _ _ _ (by omega : j < w), envOfTrace_trace Q' _ _ _ _ (by omega : j < w'),
      hQ j hj hoff]
  have hK : ∀ i, ∀ r < 24, (Chips.ChipRAP.walkEnvK δF kroots b hn nodes orbit chals pubs Q i).trace r =
      (Chips.ChipRAP.walkEnvK δF kroots b hn nodes orbit chals' pubs' Q' i).trace r := by
    intro i
    unfold Chips.ChipRAP.walkEnvK
    refine gather_trace_congr b _ (BK := 24) (fun r hr k hk => hF i _ ?_ ?_)
    · simp only [ChipTemplate.col0, walkTemplate_baseCols]; omega
    · simp only [ChipTemplate.col0, walkTemplate_baseCols]; omega
  have hL : ∀ i, lblRow δF (Chips.ChipRAP.walkEnvK δF kroots b hn nodes orbit chals pubs Q i)
      (Chips.ChipRAP.walkEnvF b hn nodes orbit chals pubs Q i) =
      lblRow δF (Chips.ChipRAP.walkEnvK δF kroots b hn nodes orbit chals' pubs' Q' i)
        (Chips.ChipRAP.walkEnvF b hn nodes orbit chals' pubs' Q' i) :=
    fun i => lblRow_congr14 δF (hK i) (fun j hj => hF i j (by omega) (Or.inl hj))
  have hk : ∀ i, keyRow δF (Chips.ChipRAP.walkEnvK δF kroots b hn nodes orbit chals pubs Q i)
      (Chips.ChipRAP.walkEnvF b hn nodes orbit chals pubs Q i) =
      keyRow δF (Chips.ChipRAP.walkEnvK δF kroots b hn nodes orbit chals' pubs' Q' i)
        (Chips.ChipRAP.walkEnvF b hn nodes orbit chals' pubs' Q' i) :=
    fun i => keyRow_congr14 δF (hK i) (fun j hj => hF i j (by omega) (Or.inl hj))
  simp only [walkDataOf, hL, hk]

/-- **`bitFix` is invisible to the walk data**: the raw J-8 walk trace (restricted `21 → 25`) and the
`bitFix` view (restricted by `restrictWalkK`) have the same walk data, at any coins and publics. -/
theorem walkDataOf_bitFix (chals pubs chals' pubs' : ℕ → K) (W : Fin 166 → F[X]) :
    walkDataOf δF kroots b hn nodes orbit chals' pubs'
        (restrictWalkK δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs
          (fun j => W (Fin.cast (WalkJ8.walkChipJ8_width δF kroots b hn nodes orbit chals pubs) j)))) =
      walkDataOf δF kroots b hn nodes orbit (fun _ => 0) (fun _ => 0) (Handle.restrictQ 21 25 shV W) := by
  refine walkDataOf_congr_off δF kroots b hn nodes orbit _ _
    (by rw [walk_w δF kroots b hn nodes orbit chals pubs]; norm_num) (by norm_num) (fun j hj hoff => ?_) _ _ _ _
  simp only [restrictWalkK, Handle.restrictQ]
  erw [bitFix_off]
  · rfl
  · simp only [Handle.shiftCol]; split_ifs <;> omega

end Congr

/-! ## 2. The layout read off `PubJ8` -/

section Lay
variable {p : ℕ} [Fact p.Prime]

/-- **The J-8 readout layout of the verifier's public parameters**: compute `(n, nodes, orbit)`, cell
`(nC, nodesC, orbitC)`, J-8 walk `(nW, …, kroots)`, atom table `(nA, …)`, atom walk `(nV, …, krootsV)`, and a
census skeleton. -/
def layPb (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3) : LayJ8 (p := p) where
  hC := Pb.h
  nC := Pb.n
  hnC := Pb.hn
  nodesC := Pb.nodes
  orbitC := Pb.orbit
  hM := Pb.hC
  nM := Pb.nC
  nodesM := Pb.nodesC
  orbitM := Pb.orbitC
  hW := Pb.hW
  nW := Pb.nW
  hnW := Pb.hnW
  nodesW := Pb.nodesW
  orbitW := Pb.orbitW
  krootsW := Pb.kroots
  hA := Pb.hA
  nA := Pb.nA
  nodesA := Pb.nodesA
  orbitA := Pb.orbitA
  hV := Pb.hV
  nV := Pb.nV
  hnV := Pb.hnV
  nodesV := Pb.nodesV
  orbitV := Pb.orbitV
  krootsV := Pb.krootsV
  skel := skel
  skel_le := hs

end Lay

/-! ## 3–5. `rdWW` and `rdWC` at `realize40` -/

section Read
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {r : RowsJ8}

/-- **`LinkJ8.rdWW` (L2)** at `L := realize40 L0 (layPb Pb …) hL`: the walk-chain readout `wdWJ8` (raw J-8
walk columns) IS the walk data at the `bitFix` view, at any trace, coins and messages. -/
theorem rdWW_realize40 (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hL : LayLe (layPb Pb skel hs) r) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    (realize40 δ b L0 (layPb Pb skel hs) hL).wdW tr (toVSQ χ) =
      walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))) :=
  (walkDataOf_bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ _ tr.W).symm

/-- `stOfEnv` recovers a one-hot state. -/
theorem stOfEnv_of_oneHot {e : Env (ZMod p)} {st : Edit.StateX} (h : OneHotAt e (stIdx st)) :
    stOfEnv e = st := by
  unfold stOfEnv
  rw [Handle.CWalkChipVS.find_congr _ (fun j => decide (j = stIdx st)) _ (fun j hj => by
    have hj' : j < 17 := List.mem_range.mp hj
    rw [h j hj']
    by_cases hjs : j = stIdx st <;> simp [hjs])]
  cases st <;> rfl

variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`LinkJ8.rdWC` (L2)** at `L := realize40 L0 (layPb Pb …) hL`: on a trace whose compute chip is accepted
(`AcceptsJ8.hsatX`), over `17 < p`, the compute rows `cRowsJ8` (coin-free environments, `stOfEnv`) are
`rowsWX` of the `frameJ8` environments `envX` and their one-hot states `stX`, and `cH = n`. -/
theorem rdWC_realize40 (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hL : LayLe (layPb Pb skel hs) r) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) (hp : 17 < p) :
    (realize40 δ b L0 (layPb Pb skel hs) hL).cRows tr =
        rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
      (realize40 δ b L0 (layPb Pb skel hs) hL).cH tr = Pb.n := by
  refine ⟨?_, rfl⟩
  show cRowsJ8 Pb.hn Pb.nodes Pb.orbit tr = _
  funext i
  show rowW (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C (i - 1)) (stOfEnv (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C (i - 1))) =
    rowW (envX δ b Pb c χ M tr (i - 1)) (stX (envX δ b Pb c χ M tr (i - 1)))
  generalize i - 1 = k
  have htr : (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C k).trace = (envX δ b Pb c χ M tr k).trace := by
    simp only [envCJ8, envX, TeleC.envsN]
    split_ifs <;> rfl
  have hB : BaseHoldsX (envX δ b Pb c χ M tr k) := by
    simp only [envX, TeleC.envsN]
    split_ifs
    · exact baseX_of_sat Pb.hn Pb.nodes b δ _ _ Pb.orbit _ hacc.hsatX _ (mem_rowNodeSet _ _)
    · exact baseX_of_sat Pb.hn Pb.nodes b δ _ _ Pb.orbit _ hacc.hsatX _ (mem_rowNodeSet _ _)
  have hc : nStates < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact hp
  have hoh := stX_spec hB hc
  have hoh' : OneHotAt (envCJ8 Pb.hn Pb.nodes Pb.orbit tr.C k) (stIdx (stX (envX δ b Pb c χ M tr k))) :=
    fun j hj => by rw [congrFun htr j]; exact hoh j hj
  rw [stOfEnv_of_oneHot hoh', rowW_congr (fun j _ => congrFun htr j)]

/-- **L2 of `LinkJ8`, both fields**, at `L := realize40 L0 (layPb Pb …) hL`. -/
theorem linkJ8_L2 (Pb : PubJ8 p) (skel : List Noun) (hs : skel.length ≤ 3)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hL : LayLe (layPb Pb skel hs) r) {Rg : Nock.Jet.Registry} (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) (hp : 17 < p) :
    ((realize40 δ b L0 (layPb Pb skel hs) hL).cRows tr =
        rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
      (realize40 δ b L0 (layPb Pb skel hs) hL).cH tr = Pb.n) ∧
    (realize40 δ b L0 (layPb Pb skel hs) hL).wdW tr (toVSQ χ) =
      walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))) :=
  ⟨rdWC_realize40 δ b Pb skel hs L0 hL c χ M tr hacc hp, rdWW_realize40 δ b Pb skel hs L0 hL χ M tr⟩

end Read

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1
