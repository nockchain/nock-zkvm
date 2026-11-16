/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8Q1H.lean

  **`LinkJ8.hHXW` (L4, the J-8 walk's handle-export
  lookup).**

  * **`walkEnvFA_bitFix_trace`**: the `bitFix` view's row environment agrees with the raw J-8 walk row (`wEF`) off
    the certificate block `14..20`.
  * **`hHXW_of_served`**: if every J-8 walk row's handle read `keyVec5 xKeyH` is a provided key of the cell
    table (`cellProvsW`), then every row's `(idx, h_L, h_R)` is `exportRecK` of a row of the decoded cell table
    (`keyHK_eval` on the cell side, `natOf_natCast` under `exportRecK_lt`).  Needs only the cell table's
    satisfaction.
  * **`walkX_served`**: on an `AcceptsJ8` trace, outside the compute's three handle IO events (at the real lists
    `reqsOf` / `provsJ8`, `s` at the effective providers) with the `x` count `< p`, every walk read is served:
    `BalSJ8.balJ8_frameJ8S` (the verifier's `hGx hGp hGS`), the compute telescope `compReqsX_sum`,
    `ServeH.served_of_balance` (the `x` half of `BalXJ8.ext_served`).
  * **`hHXW_of_accepts`**: the two composed — `LinkJ8.hHXW`.  Its IO hypotheses are exactly the ones `hsoundJ8`
    derives from `OutJ8` and the L1 readouts (`rdX`, `rdP`, `rdS`, budgets) and `hcount.x`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1H

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)
open Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW restrictHQKWCell cellB0Of_hqkw
  cellChipHQKW_width)
open Nock.NockVMROM.Thm54.VclL.Handle.ProvXJ8 (exportRecK_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8 bitFix bitFix_off)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal computeChipVCLHX nStates)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf compReqsX compReqsX_sum)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (BalJ8 reqsJ8 liftP den_prov_ne_of_out)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Jet.FibreJ8 (effP)
open Nock.ComputeTable (FP)

noncomputable section

/-! ## 1. The `bitFix` view's rows off the certificate block -/

section View
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

theorem walkEnvFA_bitFix_trace (QW : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
    (j : ℕ) (hj : j < n) (w : ℕ) (hw : w < 14 ∨ 21 ≤ w) (hw' : w < 166) :
    (walkEnvFA δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs QW) j).trace w =
      (wEF b nodes orbit chals pubs QW ⟨j, hj⟩).trace w := by
  simp only [walkEnvFA, dif_pos hj, wEF]
  rw [envOfTrace_trace _ _ _ _ _ (by rw [CellTwinK.walkChipHQK_width]; exact hw'),
    envOfTrace_trace _ _ _ _ _ (by rw [WalkJ8.walkChipJ8_width]; exact hw'), bitFix_off]
  simpa using hw

end View

/-! ## 2. `hHX` from a served walk read (wire-key cell twin, J-8 walk) -/

section Served
variable {p : ℕ} [hpF : Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))]
  (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
  (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K) [Fact (ringChar (ZMod p)).Prime]

/-- **`hHXW` from served walk reads.** -/
theorem hHXW_of_served (hp2 : 2 < p)
    (Q : Fin (cellChipHQKW δF b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])
    (hsat : (cellChipHQKW δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (QW : Fin (walkChipJ8 δF kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hmem : ∀ j : Fin nW, ServeH.keyVec5 (K := K) WalkHC.xKeyH (wEF b nodesW orbitW chalsW pubsW QW j) ∈
      (cellProvsW b nodes orbit chals pubs Q).map Prod.fst) :
    ∀ j < nW, ∃ c' ∈ cellTableOf δF b nodes orbit chals pubs (restrictHQKWCell δF b hn nodes orbit chals pubs Q),
      (natOf ((walkEnvFA δF kroots b hnW nodesW orbitW chalsW pubsW
          (bitFix δF kroots b hnW nodesW orbitW chalsW pubsW QW) j).trace WChip.idx),
        childHOfK (walkEnvFA δF kroots b hnW nodesW orbitW chalsW pubsW
          (bitFix δF kroots b hnW nodesW orbitW chalsW pubsW QW) j) false,
        childHOfK (walkEnvFA δF kroots b hnW nodesW orbitW chalsW pubsW
          (bitFix δF kroots b hnW nodesW orbitW chalsW pubsW QW) j) true) = exportRecK c'.b0 := by
  intro j hj
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  obtain ⟨q, hq, hqk⟩ := List.mem_map.mp (hmem ⟨j, hj⟩)
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
  -- the cell row's provided key is its wire export record
  have hbase := ((expandChip_satisfies_iff_language _ b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)).1
  have hbool : ∀ w, boolE (cv w) ∈ Cell.baseGates (F := ZMod p) →
      (hqkEF b nodes orbit chals pubs Q i).trace w = 0 ∨ (hqkEF b nodes orbit chals pubs Q i).trace w = 1 := by
    intro w hw
    have g := hbase _ (List.mem_append_left _ hw)
    simp only [CoeffExpr.eval, cv] at g
    exact bool_val g
  have hkind : ∀ g ∈ (CellTwinK.kindGates (F := ZMod p)), g.eval (hqkEF b nodes orbit chals pubs Q i) = 0 :=
    fun g hg => hbase g (List.mem_append_right _ hg)
  have hkey := keyHK_eval hF (by rw [hrc]; exact hpF.out.pos) _ hkind
    (hbool Cell.wL (by simp [Cell.baseGates])) (hbool Cell.wR (by simp [Cell.baseGates]))
  set c := cellB0Of (hqkEF b nodes orbit chals pubs Q i) with hc
  have hent : ∀ e : Fin 5, ((keyHK (F := ZMod p)).getD e (.const 0)).eval (hqkEF b nodes orbit chals pubs Q i) =
      (WalkHC.xKeyH.getD e (.const 0)).eval (wEF b nodesW orbitW chalsW pubsW QW ⟨j, hj⟩) :=
    DecodeH.keyVec5_inj hqk
  have hlist : [(wEF b nodesW orbitW chalsW pubsW QW ⟨j, hj⟩).trace WChip.idx,
      (wEF b nodesW orbitW chalsW pubsW QW ⟨j, hj⟩).trace WalkHC.kL,
      (wEF b nodesW orbitW chalsW pubsW QW ⟨j, hj⟩).trace WalkHC.vL,
      (wEF b nodesW orbitW chalsW pubsW QW ⟨j, hj⟩).trace WalkHC.kR,
      (wEF b nodesW orbitW chalsW pubsW QW ⟨j, hj⟩).trace WalkHC.vR] = recFK (exportRecK c) := by
    rw [← hkey]
    have e0 := hent ⟨0, by decide⟩; have e1 := hent ⟨1, by decide⟩; have e2 := hent ⟨2, by decide⟩
    have e3 := hent ⟨3, by decide⟩; have e4 := hent ⟨4, by decide⟩
    simp only [WalkHC.xKeyH, keyHK, List.getD_cons_zero, List.getD_cons_succ,
      Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, CoeffExpr.eval, cv] at e0 e1 e2 e3 e4 ⊢
    simp only [List.map_cons, List.map_nil, CoeffExpr.eval, cv]
    rw [e0, e1, e2, e3, e4]
  simp only [recFK, exportRecK, List.cons.injEq] at hlist
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := hlist
  have hlt := exportRecK_lt hp2 (hqkEF b nodes orbit chals pubs Q i)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  obtain ⟨l0, l1, l2, l3, l4⟩ := hlt
  set Q0 := restrictHQKWCell δF b hn nodes orbit chals pubs Q
  refine ⟨cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q0 i) (cellEnvF b nodes orbit chals pubs Q0 i),
    List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
  have hb0 : (cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q0 i)
      (cellEnvF b nodes orbit chals pubs Q0 i)).b0 = c := (cellB0Of_hqkw δF b hn nodes orbit chals pubs Q i).symm
  rw [hb0]
  have t0 := walkEnvFA_bitFix_trace δF kroots b hnW nodesW orbitW chalsW pubsW QW j hj WChip.idx
    (by decide) (by decide)
  have t1 := walkEnvFA_bitFix_trace δF kroots b hnW nodesW orbitW chalsW pubsW QW j hj WalkHC.kL
    (by decide) (by decide)
  have t2 := walkEnvFA_bitFix_trace δF kroots b hnW nodesW orbitW chalsW pubsW QW j hj WalkHC.vL
    (by decide) (by decide)
  have t3 := walkEnvFA_bitFix_trace δF kroots b hnW nodesW orbitW chalsW pubsW QW j hj WalkHC.kR
    (by decide) (by decide)
  have t4 := walkEnvFA_bitFix_trace δF kroots b hnW nodesW orbitW chalsW pubsW QW j hj WalkHC.vR
    (by decide) (by decide)
  simp only [childHOfK, exportRecK, Bool.false_eq_true, if_false, if_true]
  rw [t0, t1, t2, t3, t4, h0, h1, h2, h3, h4,
    natOf_natCast hF (l0.trans_eq hrc.symm), natOf_natCast hF (l1.trans_eq hrc.symm),
    natOf_natCast hF (l2.trans_eq hrc.symm), natOf_natCast hF (l3.trans_eq hrc.symm),
    natOf_natCast hF (l4.trans_eq hrc.symm)]

end Served

/-! ## 3. The walk reads are served on an accepted trace -/

section Accepts
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **Every J-8 walk read is a cell-table provided key** on an accepted trace, outside the compute's handle IO
events at the real lists (`s` at the effective providers), with the `x` count `< p`. -/
theorem walkX_served [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) (liftP (provsJ8 δ b Pb χ M tr .x)))
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) (liftP (provsJ8 δ b Pb χ M tr .p)))
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) (effP (liftP (provsJ8 δ b Pb χ M tr .s))))
    (hcx : (reqsOf δ b Pb c χ M tr .x).length < p) :
    ∀ j : Fin Pb.nW, ServeH.keyVec5 (K := K) WalkHC.xKeyH
        (wEF b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) j) ∈
      (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)).map
        Prod.fst := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hF := GeneratedField.primeFieldElems_zmod p
  have B : TeleCQX.BCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) :=
    ⟨by rw [hrc]; show 17 < p; omega, hacc.hsatX, hacc.hinjX, hacc.hadjX⟩
  have hcv := VerJ8.coinsCV_J8 δ b χ
  have hG := (VerJ8.goodCJ8_iff (δ := δ) (b := b) c M.m M.ρ M.ρS χ M.pubsC M.pubsW M.pubsJ M.ρS 0).2
    ⟨hacc.hGx, hacc.hGp, add_zero _⟩
  have he := BalXJ8.extX_sumQ δ b (coinsCV b δ (chalVJ8 b χ)) Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) hacc.hsatW hacc.hbindW hF (by rw [hrc]; exact hp)
    hacc.hinjW hacc.hadjW ((VerJ8.mcoins_J8 δ χ).trans hcv.symm)
    Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
    hacc.hsatJ hacc.hbindJ hacc.hinjJ hacc.hnJ hacc.hadjJ ((VerJ8.coinsJX_J8 δ χ).trans hcv.symm)
  have hpr := BalXJ8.provsX_sumQ δ b (coinsCV b δ (chalVJ8 b χ)) Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) hacc.hsatC hacc.hbindC hacc.hinjC hacc.hadjC
    ((VerJ8.mcoins_J8 δ χ).trans hcv.symm)
  have hbx : ServedJ8.rhoX (b := b) (δ := δ) (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) .x +
      ((extJ8 δ b Pb c χ M tr .x).map fun r => (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum =
      ((provsJ8 δ b Pb χ M tr .x).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
    show _ + ((ServeH.walkXReqs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) ++
      Nock.Jet.RapJetJ8.jRd b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)).map
        _).sum = ((cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)).map
          _).sum
    convert hG .x using 2 <;> first | exact he | exact hpr
  have hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
      (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
      (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r) ≠ 0 := by
    intro bl r hr
    cases bl with
    | s => exact TeleC.den_ne_of_out _ _ _ _ hs _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | x => exact TeleC.den_ne_of_out _ _ _ _ hx _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | p => exact TeleC.den_ne_of_out _ _ _ _ hpp _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hserved : ∀ r ∈ reqsOf δ b Pb c χ M tr .x, r ∈ (liftP (provsJ8 δ b Pb χ M tr .x)).map Prod.fst := by
    refine ServeH.served_of_balance (p := p) _ _ _ _ (TeleC.den_ne_of_out _ _ _ _ hx)
      (den_prov_ne_of_out _ _ _ _ hx) ?_ hcx hx
    have h1 := compReqsX_sum B hne .x
    have h2 := hbx
    unfold reqsOf reqsJ8 liftP
    rw [List.map_map, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1]
    exact h2
  intro j
  have hc : ServeH.keyVec5 (K := K) WalkHC.xKeyH
      (wEF b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) j) ∈
      extJ8 δ b Pb c χ M tr .x :=
    List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange j))
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hserved _ (List.mem_map_of_mem (List.mem_append_right _ hc)))
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨q0, hq0, liftRec_inj hqe⟩

/-- **`LinkJ8.hHXW` (L4)** on an accepted trace outside the compute's handle IO events at the real lists. -/
theorem hHXW_of_accepts [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) (liftP (provsJ8 δ b Pb χ M tr .x)))
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) (liftP (provsJ8 δ b Pb χ M tr .p)))
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) (effP (liftP (provsJ8 δ b Pb χ M tr .s))))
    (hcx : (reqsOf δ b Pb c χ M tr .x).length < p) :
    ∀ j < Pb.nW, ∃ c' ∈ cellT δ b Pb χ M tr,
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j).trace WChip.idx),
        WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) false,
        WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) true) = exportRecK c'.b0 :=
  hHXW_of_served δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW
    (chalsMJ8 δ χ) M.pubsW (by omega) _ hacc.hsatC _
    (walkX_served δ b Pb c χ M tr hacc hp hx hpp hs hcx)

end Accepts

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1H
