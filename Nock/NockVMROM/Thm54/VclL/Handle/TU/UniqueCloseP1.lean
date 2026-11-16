/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/UniqueCloseP1.lean

 **Trace uniqueness on the P1 fragment: the uniqueness half assembled from the close lemmas.**

 `Comp12P1.trace_unique_good''` leaves only the fields of `UniqueP1.OpenP1` open. This module builds `OpenP1` from
 the three close lemmas and states **`trace_unique_closed`**: two transcripts accepted by `AcceptsCanon2` at the
 canonical claim, with a coin outside every event of the absent-atom-walk data (`Comp12P1.dataA`) at both traces,
 are equal.

 * the twins: `LinkJ8A.linkXUA_of_R5` gives `LinkJ8XUA` with the atom reader `rA = rAT b Pb tr` (the producer's),
 which is exactly the reader `OpenR0CCloseP1.r0C_closed` pins; `TwinLinkJ8A.hsoundJ8XUA_exA` at that reader gives
 the compute rows' `RowsAccXI`, the forest goal and the three root denotations at `denJ8 … (rAT b Pb tr)`, which
 is `NounSetCloseP1.denC … (extB p (rAT b Pb tr))` by definition.
 * `r0M`, `auxM`: `NounSetCloseP1.r0M_auxM_closed''` with `ext = extB p (rAT …)` (atoms only, `extB_atoms`), the
 positional bridge `RowBridgeP1.rowBridge` from the twins, the root denotations from the twins.
 * `r0C`, `claim`: `OpenR0CCloseP1.r0C_closed`, fed `r0M`.
 * `r0W`, `auxW`, `r1W`: `WalkCloseP1.walk_closed`, with `hX`, `hH` the link's `hXW`, `hHXW`, the walk event
 from `Lift40J8.wchain_out` at the walk readout `rdWW`, and `hcell` derived: `cell_rows_eq'` from `r0M` gives every
 cell column at every row, the degree lift gives `tr.M = tr'.M`, and the cell table reads neither the cell publics
 (`cellTab_pubs`) nor anything of the trace but `tr.M` (`cellTab_tr`).
 * `servedC`, `servedC'`: `ServedP1.cell_served_P1` at the same link.

 Still hypotheses: the cell balances in count form (`hbal*`, with `extraV = M.xsC` the message's extra validity
 providers in the J-8 balance, `LinkJ8XUA.rdV`), the cross-trace `hreqs`, `hkey` (circular with `r0M` in the
 present decomposition: the keys and the consumer lists are only known equal after `r0M`), the walk path-record
 balance and `hreqW`, the cell fingerprint injectivity `hfp`, the root bounds `hk1 hkn hkp`, the reads `Rd hszW hprov`
 and the E10 pins (`noPath hE10 hnW1`), the size `hsz`, the run `hrun` at the acceptance registry.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CCloseP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRowsP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.ServedP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueCloseP1

noncomputable section

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qW qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (bitFix)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A (rAT)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1 (dataA trace_unique_good'')
open Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1 (qCell keyVOf keyXOf keyHOf r0M_auxM_closed'' extB_atoms)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1 (envB)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (WT)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1 (cellTab readClosure walk_closed)
open Nock.Edit.GenX (P1Frag genX SkelX)
open Nock.V1J8.Gen (cellsOfRoots rootsOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)

section Close
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The cell table does not read the cell publics. -/
theorem cellTab_pubs {Pb : PubJ8 p} (χ : Coins frameJ8 K) (pubs pubs' : ℕ → K) (tr : TrJ8 (ZMod p)) :
    cellTab δ b (Pb := Pb) χ pubs tr = cellTab δ b (Pb := Pb) χ pubs' tr := by
  simp only [cellTab, cellTableOf]
  congr 1

/-- The cell table reads the trace only through `tr.M`. -/
theorem cellTab_tr {Pb : PubJ8 p} (χ : Coins frameJ8 K) (pubs : ℕ → K) {tr tr' : TrJ8 (ZMod p)}
    (h : tr.M = tr'.M) :
    cellTab δ b (Pb := Pb) χ pubs tr = cellTab δ b (Pb := Pb) χ pubs tr' := by
  simp only [cellTab, qM, h]

/-- **`trace_unique_closed`**: two tuples accepted by `AcceptsCanon2` at one claim `c`, layout `Pb` and coin `χ`,
outside every event of the absent-atom-walk data (`dataA`) at BOTH traces, are equal, given the remaining facts
listed in the hypotheses (see the module docstring and the final report for each one's class). -/
theorem trace_unique_closed [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) {c : P8PublicClaim}
    -- the event data (`LinkJ8A.probJ8V_absent`)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    -- the row parameters
    (hr : WeightsJ8.RowsLe r EncInjJ8.cornerC) (hgN : g ≤ 2 ^ 31) (hmax : Pb.nA + 2 ≤ r.maxlen)
    (hqM : ∀ x < ringChar (ZMod p), Nock.Atoms.lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hg : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr χ)
    (hg' : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr' χ)
    -- the generated run at the acceptance registry, and the cell-table size
    {fuel : ℕ} {tg : NTree SkelX} {res : Noun} (hrun : genX Rg fuel c.subject c.formula = some (tg, res))
    (hsz : Pb.nC = (cellsOfRoots (rootsOf c (rowsOfT tg))).length)
    -- the cell balances (V, X with an extra provider list; H at `cellProvsW`)
    {reqsV reqsV' : List (Fin 5 → 𝕂′)} {reqsX reqsX' : List (Fin 11 → 𝕂′)} {reqsH reqsH' : List (Fin 5 → K)}
    (extraV : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hbalV : ∀ r, (reqsV.count r : 𝕂′) =
      pw (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)) ++ extraV) r)
    (hdeV : (extraV.map Prod.fst).Nodup)
    (hdisV : ∀ a ∈ (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr))).map
      Prod.fst, ∀ e ∈ extraV.map Prod.fst, a ≠ e)
    (extraX : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbalX : ∀ r, (reqsX.count r : 𝕂′) =
      pw (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)) ++ extraX) r)
    (hdeX : (extraX.map Prod.fst).Nodup)
    (hdisX : ∀ a ∈ (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr))).map
      Prod.fst, ∀ e ∈ extraX.map Prod.fst, a ≠ e)
    (hbalH : ∀ r, (reqsH.count r : K) = pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) r)
    (extraV' : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hbalV' : ∀ r, (reqsV'.count r : 𝕂′) =
      pw (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')) ++ extraV') r)
    (hdeV' : (extraV'.map Prod.fst).Nodup)
    (hdisV' : ∀ a ∈ (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr'))).map
      Prod.fst, ∀ e ∈ extraV'.map Prod.fst, a ≠ e)
    (extraX' : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbalX' : ∀ r, (reqsX'.count r : 𝕂′) =
      pw (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')) ++ extraX') r)
    (hdeX' : (extraX'.map Prod.fst).Nodup)
    (hdisX' : ∀ a ∈ (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr'))).map
      Prod.fst, ∀ e ∈ extraX'.map Prod.fst, a ≠ e)
    (hbalH' : ∀ r, (reqsH'.count r : K) = pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC)) r)
    -- cross-trace: equal consumer lists and equal row keys
    (hreqs : reqsV = reqsV' ∧ reqsX = reqsX' ∧ reqsH = reqsH')
    (hkey : ∀ i < Pb.nC, keyVOf δ b Pb χ M tr i = keyVOf δ b Pb χ M' tr' i ∧
      keyXOf δ b 0 Pb χ M tr i = keyXOf δ b 0 Pb χ M' tr' i ∧
      keyXOf δ b 1 Pb χ M tr i = keyXOf δ b 1 Pb χ M' tr' i ∧ keyHOf δ b Pb χ M tr i = keyHOf δ b Pb χ M' tr' i)
    -- the walk
    (hk1 : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hfp : ∀ c1 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr, ∀ c2 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      c1.p = c2.p → c1.b0.idx = c2.b0.idx)
    (reqsW reqsW' : List (Fin 5 → K)) (provsW provsW' : List ((Fin 5 → K) × K))
    (hbalW : ∀ r, (reqsW.count r : K) = pw provsW r) (hdW : (provsW.map Prod.fst).Nodup)
    (hsubW : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW), q ∈ provsW)
    (hbalW' : ∀ r, (reqsW'.count r : K) = pw provsW' r) (hdW' : (provsW'.map Prod.fst).Nodup)
    (hsubW' : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
      (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW), q ∈ provsW')
    (hreqW : ∀ r, reqsW.count r = reqsW'.count r)
    (noPath : Prop)
    (hE10 : noPath → (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hE10' : noPath → (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hnW1 : noPath → Pb.nW = 1)
    (Rd : Finset (ℕ × ℕ)) (hszW : ¬ noPath → (readClosure Rd).card = Pb.nW)
    (hprov : ¬ noPath → ∀ s ∈ Rd, ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.pre) = s.2 / 2)
    (hprov' : ¬ noPath → ∀ s ∈ Rd, ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.pre) = s.2 / 2) :
    (tr, ax, M) = (tr', ax', M') := by
  have hPb := h.1.2.hPb
  have h0 : Pb.krootsV = 0 := by rw [hPb]; rfl
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hn : 1 ≤ Pb.n := by rw [hPb]; exact (sz c).hn
  have hfrag : P1Frag c.formula := AsmRowsP1.P1FragC.p1Frag h.1.2.hfrag
  -- the twins, at the producer's atom reader
  have hl := LinkJ8A.linkXUA_of_R5 δ b Pb c χ M tr R0 L0 skel hs hL hP hnM hreg hpG hr hgN hmax h.1.1 h0 hg
  have hl' := LinkJ8A.linkXUA_of_R5 δ b Pb c χ M' tr' R0 L0 skel hs hL hP hnM hreg hpG hr hgN hmax h'.1.1 h0 hg'
  -- the validity-served cell tables (`ServedP1.cell_served_P1`)
  have hS := ServedP1.cell_served_P1 δ b hpG rfl h.1.1 h0 h.1.2.hApad hg hl
  have hS' := ServedP1.cell_served_P1 δ b hpG rfl h'.1.1 h0 h'.1.2.hApad hg' hl'
  -- the J-8 walk event (`Lift40J8.wchain_out` at the walk readout `rdWW`)
  have houtW := Lift40J8.wchain_out _ (ListJ8C.outside40C _ _ (AtomFpxJ8.outsideC_of_outsideX _ hg))
  rw [hl.rdWW, ← (AcceptsJ8.coinW_J8 δ χ).1, ← (AcceptsJ8.coinW_J8 δ χ).2] at houtW
  have houtW' := Lift40J8.wchain_out _ (ListJ8C.outside40C _ _ (AtomFpxJ8.outsideC_of_outsideX _ hg'))
  rw [hl'.rdWW, ← (AcceptsJ8.coinW_J8 δ χ).1, ← (AcceptsJ8.coinW_J8 δ χ).2] at houtW'
  obtain ⟨-, A, hG, -, hden, -⟩ := TwinLinkJ8A.hsoundJ8XUA_exA δ b Pb hRg c χ M tr _ _ hpG hqM hk h.1.1 h0 hg hl
  obtain ⟨-, A', hG', -, hden', -⟩ :=
    TwinLinkJ8A.hsoundJ8XUA_exA δ b Pb hRg c χ M' tr' _ _ hpG hqM hk h'.1.1 h0 hg' hl'
  -- the cell table: round 0 and aux
  have hD := AtomBigJ8.denOKX_extB ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    (qCell δ b Pb χ M tr)).map (·.b0)) p (rAT b Pb tr)
  have hD' := AtomBigJ8.denOKX_extB ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
    (qCell δ b Pb χ M' tr')).map (·.b0)) p (rAT b Pb tr')
  have hB := RowBridgeP1.rowBridge (K := K) hp hRg hD hn A hG c (hden 0) (hden 1) hfrag hrun
  have hB' := RowBridgeP1.rowBridge (K := K) hp hRg hD' hn A' hG' c (hden' 0) (hden' 1) hfrag hrun
  obtain ⟨hr0M, hauxM⟩ := r0M_auxM_closed'' δ b h.1 h'.1 hS hS' (extB_atoms p (rAT b Pb tr))
    (extB_atoms p (rAT b Pb tr')) hfrag hrun hsz hB hB' ⟨_, hden 0⟩ ⟨_, hden 1⟩ ⟨_, hden 2⟩
    ⟨_, hden' 0⟩ ⟨_, hden' 1⟩ ⟨_, hden' 2⟩
    extraV hbalV hdeV hdisV extraX hbalX hdeX hdisX hbalH
    extraV' hbalV' hdeV' hdisV' extraX' hbalX' hdeX' hdisX' hbalH' hreqs hkey
  -- the cell tables agree (all columns: `cell_rows_eq'`, then the degree lift)
  have hMall := (AsmRoundsP1.cell_rows_eq' δ b h.1.1 h'.1.1 (two63_lt_ringChar hpG) (zC_of_outside δ rfl hg)
    hS hS' hr0M).1
  have htrM : tr.M = tr'.M := funext fun j =>
    DegLiftP1.poly_eq_of_rows h.1.1.hinjC (h.1.2.hdeg.M j) (h'.1.2.hdeg.M j) (hMall j)
  have hcell := (cellTab_pubs δ b (Pb := Pb) χ M.pubsC M'.pubsC tr).trans (cellTab_tr δ b (Pb := Pb) χ M'.pubsC htrM)
  -- the compute table: round 0, and the claim serials
  obtain ⟨hr0C, hclaim⟩ := OpenR0CCloseP1.r0C_closed δ b hPb hRg χ M M' tr tr' ax _ _ _ _ hqM hk hqM hk
    h.1.1 h'.1.1 h0 hg hg' hl hl' h.1.2.hC h'.1.2.hC h.1.2.hM h.1.2.hApad h'.1.2.hApad hr0M hfrag hrun
  -- the walk
  obtain ⟨hr0W, hauxW, hr1W⟩ := walk_closed δ b h h' hk1 hkn hkp houtW houtW' hl.hXW hl'.hXW hcell hfp hl.hHXW hl'.hHXW
    reqsW reqsW' provsW provsW' hbalW hdW hsubW hbalW' hdW' hsubW' hreqW noPath hE10 hE10' hnW1 Rd hszW
    hprov hprov'
  exact trace_unique_good'' δ b R0 L0 skel hs hL hP hnM hreg h0 h h' hg
    ⟨hr0C, hr0M, hauxM, hr0W, hauxW, hr1W, hS, hS', hclaim⟩

end Close

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueCloseP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueCloseP1.cellTab_pubs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueCloseP1.cellTab_tr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueCloseP1.trace_unique_closed
