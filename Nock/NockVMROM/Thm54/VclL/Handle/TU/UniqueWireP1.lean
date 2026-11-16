/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/UniqueWireP1.lean

 **Trace uniqueness on the P1 fragment: wiring the consumer lists of `trace_unique_closed'`.** No existing module edited.

 * §1 `hreqX`: the X consumer list is `fxReqsJ8 … tr` (`hbalX_canon`). **`fxReqsJ8_congr`**: it reads the walk
 columns `< 14` and `25 .. 96` only (the J-8 restriction `21 → 25` of `wXInt_congr_off`'s read set: the base
 columns `< 14` and the fingerprint roles `pR lR rR`, which sit at walk columns `≥ 25`, i.e. walk ROUND 1 as
 `walk_closed_nm` splits it, not round 0). **`fxReqs_eq`**: equal from the walk round-0 and round-1
 agreement (degree lift).
 * §2 `hreqH`: the H consumer list, pinned from the J-8 handle `.x` balance: `reqsHW` = the compute `.x`
 requests (`DenXJ8.compReqsX … .x`) ++ `extJ8 … .x` = `ServeH.walkXReqs (qW) ++ jRd (qJ)`; `reqsOf_x`: its lift
 is `reqsOf … .x` (`LinkJ8XUA.rdX`). Read set: compute columns `< 69` (no coin, no public), walk columns
 `3, 21 .. 24` (`xKeyH`, round 0), and the J table, which is empty on the P1 fragment (`nJ = 0`, `jRd_nil`).
 No message field is read (the walk publics `pubsW`, `pubsJ` enter only through environments whose trace part
 is read). **`reqsHW_eq`**.
 * §3 **`trace_unique_closed''`**: `trace_unique_closed'` with `hreqW`, `hdeV`, `hdisV`, `hbalX`, `hdeX`,
 `hdisX`, `hreqX`, `hreqH` discharged (`extraV := xsC`, `extraX := []`, `reqsW := reqsPW …`,
 `reqsX := fxReqsJ8 …`, `reqsH := reqsHW …`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1
import Nock.NockVMROM.Thm54.VclL.Handle.JGenJ8
import Nock.NockVMROM.Thm54.VclL.Handle.IOVS
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZHG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (ClaimMsgVS)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 pubVJ8 chalsMJ8 chalsJJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX qW qM qJ reqsOf extJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (bitFix)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A (rAT)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8 (fxReqsJ8 fxProvsJ8)
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
open Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (toMsgJ8ZA)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1
open Nock.Jet.RapJetJ8 (jRd)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (AcceptsJ8ZA acceptsJ8ZA_of_V)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (compReqsX compReqsX_sum)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (reqsJ8 liftP den_prov_ne_of_out)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec liftRec_inj)

noncomputable section

/-! ## 1. `hreqX`: the walk's consumed export keys read walk columns `< 14` and `25 .. 96` -/

section ReqX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

/-- **The X consumer congruence**: `fxReqsJ8` reads only the walk columns `< 14` and `25 .. 96` (as polynomials):
`wXInt_congr_off`'s read set (`< 93` off the certificate block `14 .. 20`) pushed through the restriction
`21 → 25`. -/
theorem fxReqsJ8_congr (Pb : PubJ8 p) {tr tr' : TrJ8 (ZMod p)}
    (hW : ∀ j : Fin 166, ((j : ℕ) < 14 ∨ 25 ≤ (j : ℕ)) → (j : ℕ) < 97 → tr.W j = tr'.W j) :
    fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr = fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr' := by
  unfold RealVJ8.fxReqsJ8
  refine RealVJ8.wXInt_congr_off δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ (by norm_num) (by norm_num)
    (fun j hj hoff => ?_) _ _ _ _
  simp only [Handle.restrictQ]
  apply hW
  · simp only [Handle.shiftCol]; split_ifs <;> omega
  · simp only [Handle.shiftCol]; split_ifs <;> omega

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`hreqX` at two `AcceptsCanon2` tuples**: the walk round-0 (`< 25`) and round-1 (`25 .. 96`) agreement at
every row (what `walk_closed_nm` gives) gives equal X consumer lists. -/
theorem fxReqs_eq {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hr0W : ∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i))
    (hr1W : ∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
      ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) :
    fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr = fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr' :=
  fxReqsJ8_congr δ b Pb fun j hj hj97 =>
    DegLiftP1.poly_eq_of_rows h.1.1.hinjW (h.1.2.hdeg.W j) (h'.1.2.hdeg.W j) (by
      rcases hj with hj | hj
      · exact hr0W j (by omega)
      · exact hr1W j hj hj97)

end ReqX

/-! ## 2. `hreqH`: the H consumer list of the J-8 handle `.x` balance -/

section ReqH
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The H consumer list** (in `K`) of the J-8 handle `.x` balance, against the providers `cellProvsW`
(`provsJ8 … .x`): the compute `.x` requests, the J-8 walk's consumed handle-export keys `walkXReqs`, the J chip's
reads `jRd` (`extJ8 … .x`). -/
def reqsHW (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    (pubsW pubsJ : ℕ → K) (tr : TrJ8 (ZMod p)) : List (Fin 5 → K) :=
  List.append (α := Fin 5 → K) (DenXJ8.compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
    (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := Pb.orbit) (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ))
    .x)
  (ServeH.walkXReqs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) pubsW (qW δ b Pb tr (chalsMJ8 δ χ) pubsW) ++
    jRd b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) pubsJ))

/-- `reqsOf … .x` (what `LinkJ8XUA.rdX` reads) is the lift of `reqsHW`. -/
theorem reqsOf_x (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : AcceptsJ8.MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p)) :
    reqsOf δ b Pb c χ M tr .x =
      (reqsHW δ b Pb c χ M.m M.ρ M.ρS M.pubsW M.pubsJ tr).map (BalanceQ.liftRec (L := 𝕂′)) :=
  rfl

/-- The walk part reads the walk columns `< 25` (row values), no public. -/
theorem walkXReqs_congr (Pb : PubJ8 p) (χ : Coins frameJ8 K) {pubs pubs' : ℕ → K} {tr tr' : TrJ8 (ZMod p)}
    (hW : ∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) :
    ServeH.walkXReqs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) pubs (qW δ b Pb tr (chalsMJ8 δ χ) pubs) =
      ServeH.walkXReqs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) pubs' (qW δ b Pb tr' (chalsMJ8 δ χ) pubs') := by
  unfold ServeH.walkXReqs
  refine List.map_congr_left fun i _ => ?_
  refine IOVS.keyVec5_congr 25 _ IOVS.xKeyH_read _ _ fun c hc => ?_
  rw [envOfTrace_trace _ _ _ _ _ (by rw [WalkJ8.walkChipJ8_width]; omega),
    envOfTrace_trace _ _ _ _ _ (by rw [WalkJ8.walkChipJ8_width]; omega)]
  exact hW ⟨c, by omega⟩ hc i

/-- **The H consumer congruence**: `reqsHW` reads the compute columns `< 69` (as polynomials), the walk columns
`< 25` (row values), and nothing of the message when the J table is empty. -/
theorem reqsHW_congr (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (hJ : Pb.nJ = 0)
    {m m' : ClaimMsgVS} {ρ ρ' : Fin 5 → 𝕂′} {ρS ρS' : 𝕂′} {pW pW' pJ pJ' : ℕ → K} {tr tr' : TrJ8 (ZMod p)}
    (hC : ∀ j : Fin 123, (j : ℕ) < 69 → tr.C j = tr'.C j)
    (hW : ∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) :
    reqsHW δ b Pb c χ m ρ ρS pW pJ tr = reqsHW δ b Pb c χ m' ρ' ρS' pW' pJ' tr' := by
  unfold reqsHW
  rw [walkXReqs_congr δ b Pb χ (pubs := pW) (pubs' := pW') hW, JGenJ8.jRd_nil hJ, JGenJ8.jRd_nil hJ]
  exact congrArg (fun l => List.append (α := Fin 5 → K) l _)
    (ReadIOJ8.compReqsX_congr _ _ (fun j h1 h2 hj => hC ⟨j, h1⟩ hj) .x)

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`hreqH` at two `AcceptsCanon2` tuples**: the compute round-0 and walk round-0 agreement at every row give
equal H consumer lists. -/
theorem reqsHW_eq {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hr0C : ∀ j : Fin 123, (j : ℕ) < 69 → ∀ i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i))
    (hr0W : ∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) :
    reqsHW δ b Pb c χ M.m M.ρ M.ρS M.pubsW M.pubsJ tr = reqsHW δ b Pb c χ M'.m M'.ρ M'.ρS M'.pubsW M'.pubsJ tr' := by
  have hJ : Pb.nJ = 0 := by rw [h.1.2.hPb]; exact (canonPb_consts hpG sz c).1
  exact reqsHW_congr δ b Pb c χ hJ (fun j hj =>
    DegLiftP1.poly_eq_of_rows h.1.1.hinjX (h.1.2.hdeg.C j) (h'.1.2.hdeg.C j) (hr0C j hj)) hr0W

end ReqH


/-! ## 2b. `hbalH` from the event: the J-8 handle `.x` balance in count form -/

section BalH
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`hbalH` from the `.x` handle IO event** (the count twin of `AcceptsJ8ZHG.walkX_servedZ`): on an `AcceptsJ8ZA`
trace, outside the compute's handle IO events (`.x` at the real lists; `.p`, `.s` at any provider lists, read only
for the compute requests' denominators), the H consumers `reqsHW` balance `cellProvsW` record by record, in `K`
(`fibre_counts` in `𝕂′`, then `counts_lift`). -/
theorem hbalH_of_ioA [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : AcceptsJ8.MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) (liftP (AcceptsJ8.provsJ8 δ b Pb χ M tr .x)))
    {provsP : List ((Fin (DenXJ8.mOf .p) → 𝕂′) × 𝕂′)} {provsS : List ((Fin (DenXJ8.mOf .s) → 𝕂′) × 𝕂′)}
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) provsP)
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) provsS) :
    ∀ x, ((reqsHW δ b Pb c χ M.m M.ρ M.ρS M.pubsW M.pubsJ tr).count x : K) =
      pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) x := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hF := GeneratedField.primeFieldElems_zmod p
  have B : TeleCQX.BCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) :=
    ⟨by rw [hrc]; show 17 < p; omega, hacc.hsatX, hacc.hinjX, hacc.hadjX⟩
  have hcv := VerJ8.coinsCV_J8 δ b χ
  have hG := (VerJ8.goodCJ8_iff (δ := δ) (b := b) c M.m M.ρ M.ρS χ M.pubsC M.pubsW M.pubsJ M.ρS 0).2
    ⟨hacc.hGx, hacc.hGp, add_zero _⟩
  have he := JGenJ8.extX_sumQG δ b (coinsCV b δ (chalVJ8 b χ)) Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) hacc.hsatW hacc.hbindW hF (by rw [hrc]; exact hp)
    hacc.hinjW hacc.hadjW ((VerJ8.mcoins_J8 δ χ).trans hcv.symm)
    Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
    hacc.hJk ((VerJ8.coinsJX_J8 δ χ).trans hcv.symm)
  have hpr := BalXJ8.provsX_sumQ δ b (coinsCV b δ (chalVJ8 b χ)) Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) hacc.hsatC hacc.hbindC hacc.hinjC hacc.hadjC
    ((VerJ8.mcoins_J8 δ χ).trans hcv.symm)
  have hbx : ServedJ8.rhoX (b := b) (δ := δ) (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) .x +
      ((extJ8 δ b Pb c χ M tr .x).map fun r => (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum =
      ((AcceptsJ8.provsJ8 δ b Pb χ M tr .x).map fun q =>
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
  have hsum : ((reqsOf δ b Pb c χ M tr .x).map fun r => (compress (coinsCV b δ (chalVJ8 b χ)) r)⁻¹).sum =
      ((liftP (AcceptsJ8.provsJ8 δ b Pb χ M tr .x)).map fun q =>
        q.2 * (compress (coinsCV b δ (chalVJ8 b χ)) q.1)⁻¹).sum := by
    have h1 := compReqsX_sum B hne .x
    unfold reqsOf reqsJ8 liftP
    rw [List.map_map, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1]
    exact hbx
  have hdA := TeleC.den_ne_of_out _ _ _ _ hx
  have hdB := den_prov_ne_of_out _ _ _ _ hx
  rw [mem_IOFailureEventW_iff] at hx
  push Not at hx
  have hL := BalanceQ.fibre_counts _ _ (coinsCV b δ (chalVJ8 b χ)) hdA hdB hsum hx.1 hx.2.2
  exact BalanceQ.counts_lift (L := 𝕂′) liftRec liftRec_inj _ _ hL

/-- **`hbalH` at `AcceptsCanon2`** with the `dataA` event (the hypotheses `trace_unique_closed''` carries): the
three compute handle events come from `ListJ8C` at the readouts of `LinkJ8A.linkXUA_of_R5`. -/
theorem hbalH_canon [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {r : RowsJ8} {P g : ℕ}
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hr : WeightsJ8.RowsLe r EncInjJ8.cornerC) (hgN : g ≤ 2 ^ 31) (hmax : Pb.nA + 2 ≤ r.maxlen)
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g)
    (hg : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr χ) :
    ∀ x, ((reqsHW δ b Pb c χ M.m M.ρ M.ρS M.pubsW M.pubsJ tr).count x : K) =
      pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) x := by
  have h0 : Pb.krootsV = 0 := by rw [h.1.2.hPb]; rfl
  have hp64 : 64 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hl := LinkJ8A.linkXUA_of_R5 δ b Pb c χ M tr R0 L0 skel hs hL hP hnM hreg hpG hr hgN hmax h.1.1 h0 hg
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hg
  have hx := ListJ8C.hout_x_of_outsideC _ b hoC _ _ hl.rdX.1 hl.rdX.2
    (hl.rdX.1 ▸ hl.budX.1) (hl.rdX.2 ▸ hl.budX.2)
  have hpp := ListJ8C.hout_p_of_outside40C _ _ b hoC _ _ hl.rdP.1 hl.rdP.2
    (hl.rdP.1 ▸ hl.budP.1) (hl.rdP.2 ▸ hl.budP.2)
  have hss := ListJ8C.hout_s_of_outsideC _ b hoC _ _ hl.rdS.1 hl.rdS.2
    (hl.rdS.1 ▸ hl.budS.1) (hl.rdS.2 ▸ hl.budS.2)
  exact hbalH_of_ioA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr (acceptsJ8ZA_of_V h.1.1 h0) hp64 hx hpp hss

/-- **`hbalW` from the `.p` handle IO event**: the path consumers `reqsPW` balance the walk's provided records
`walkPProvs` (`provsJ8 … .p`; `.p` has no external consumer) record by record, in `K`. -/
theorem hbalW_of_ioA [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : AcceptsJ8.MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    {provsX : List ((Fin (DenXJ8.mOf .x) → 𝕂′) × 𝕂′)} {provsS : List ((Fin (DenXJ8.mOf .s) → 𝕂′) × 𝕂′)}
    (hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .x) provsX)
    (hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .p) (liftP (AcceptsJ8.provsJ8 δ b Pb χ M tr .p)))
    (hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsOf δ b Pb c χ M tr .s) provsS) :
    ∀ x, ((reqsPW δ b Pb c χ M.m M.ρ M.ρS tr).count x : K) =
      pw (ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) x := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hF := GeneratedField.primeFieldElems_zmod p
  have B : TeleCQX.BCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) :=
    ⟨by rw [hrc]; show 17 < p; omega, hacc.hsatX, hacc.hinjX, hacc.hadjX⟩
  have hcv := VerJ8.coinsCV_J8 δ b χ
  have hG := (VerJ8.goodCJ8_iff (δ := δ) (b := b) c M.m M.ρ M.ρS χ M.pubsC M.pubsW M.pubsJ M.ρS 0).2
    ⟨hacc.hGx, hacc.hGp, add_zero _⟩
  have hpr := BalXJ8.provsP_sumQ δ b (coinsCV b δ (chalVJ8 b χ)) Pb.kroots Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) hacc.hsatW hacc.hbindW hF (by rw [hrc]; exact hp)
    hacc.hinjW hacc.hadjW ((VerJ8.mcoins_J8 δ χ).trans hcv.symm)
  have hbp : ServedJ8.rhoX (b := b) (δ := δ) (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) .p +
      ((extJ8 δ b Pb c χ M tr .p).map fun r => (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum =
      ((AcceptsJ8.provsJ8 δ b Pb χ M tr .p).map fun q =>
        algebraMap K 𝕂′ q.2 * (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) q.1))⁻¹).sum := by
    have h := hG .p
    show _ + (0 : 𝕂′) =
      ((ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)).map
        _).sum
    rw [add_zero]
    refine Eq.trans ?_ hpr.symm
    simpa only [BalXJ8.TprovJ8, BalXJ8.TextJ8, add_zero] using h
  have hne : ∀ bl, ∀ r ∈ compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
      (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
      (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r) ≠ 0 := by
    intro bl r hr
    cases bl with
    | s => exact TeleC.den_ne_of_out _ _ _ _ hs _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | x => exact TeleC.den_ne_of_out _ _ _ _ hx _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | p => exact TeleC.den_ne_of_out _ _ _ _ hpp _ (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hsum : ((reqsOf δ b Pb c χ M tr .p).map fun r => (compress (coinsCV b δ (chalVJ8 b χ)) r)⁻¹).sum =
      ((liftP (AcceptsJ8.provsJ8 δ b Pb χ M tr .p)).map fun q =>
        q.2 * (compress (coinsCV b δ (chalVJ8 b χ)) q.1)⁻¹).sum := by
    have h1 := compReqsX_sum B hne .p
    unfold reqsOf reqsJ8 liftP
    rw [List.map_map, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1]
    exact hbp
  have hdA := TeleC.den_ne_of_out _ _ _ _ hpp
  have hdB := den_prov_ne_of_out _ _ _ _ hpp
  rw [mem_IOFailureEventW_iff] at hpp
  push Not at hpp
  have hL := BalanceQ.fibre_counts _ _ (coinsCV b δ (chalVJ8 b χ)) hdA hdB hsum hpp.1 hpp.2.2
  rw [reqsOf_p] at hL
  exact BalanceQ.counts_lift (L := 𝕂′) liftRec liftRec_inj _ _ hL

/-- **`hbalW` at `AcceptsCanon2`** with the `dataA` event, at `provsW := walkPProvs …`. -/
theorem hbalW_canon [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {r : RowsJ8} {P g : ℕ}
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hr : WeightsJ8.RowsLe r EncInjJ8.cornerC) (hgN : g ≤ 2 ^ 31) (hmax : Pb.nA + 2 ≤ r.maxlen)
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g)
    (hg : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr χ) :
    ∀ x, ((reqsPW δ b Pb c χ M.m M.ρ M.ρS tr).count x : K) =
      pw (ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) x := by
  have h0 : Pb.krootsV = 0 := by rw [h.1.2.hPb]; rfl
  have hp64 : 64 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hl := LinkJ8A.linkXUA_of_R5 δ b Pb c χ M tr R0 L0 skel hs hL hP hnM hreg hpG hr hgN hmax h.1.1 h0 hg
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hg
  have hx := ListJ8C.hout_x_of_outsideC _ b hoC _ _ hl.rdX.1 hl.rdX.2
    (hl.rdX.1 ▸ hl.budX.1) (hl.rdX.2 ▸ hl.budX.2)
  have hpp := ListJ8C.hout_p_of_outside40C _ _ b hoC _ _ hl.rdP.1 hl.rdP.2
    (hl.rdP.1 ▸ hl.budP.1) (hl.rdP.2 ▸ hl.budP.2)
  have hss := ListJ8C.hout_s_of_outsideC _ b hoC _ _ hl.rdS.1 hl.rdS.2
    (hl.rdS.1 ▸ hl.budS.1) (hl.rdS.2 ▸ hl.budS.2)
  exact hbalW_of_ioA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr (acceptsJ8ZA_of_V h.1.1 h0) hp64 hx hpp hss

/-- **`hbalV` at `AcceptsCanon2`** with the `dataA` event: the validity balance (`LinkJ8XUA.rdV`) in count form,
extra providers `xsC` (the `cell_child_served2` data with `fibre_counts` in place of the lookup). -/
theorem hbalV_canon [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {r : RowsJ8} {P g : ℕ}
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hr : WeightsJ8.RowsLe r EncInjJ8.cornerC) (hgN : g ≤ 2 ^ 31) (hmax : Pb.nA + 2 ≤ r.maxlen)
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g)
    (hg : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr χ) :
    ∀ x, ((vReqs δ b Pb c χ M tr).count x : 𝕂′) =
      pw (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)) ++
        (toMsgJ8ZA δ b Pb c χ M tr).xsC) x := by
  have h0 : Pb.krootsV = 0 := by rw [h.1.2.hPb]; rfl
  have hl := LinkJ8A.linkXUA_of_R5 δ b Pb c χ M tr R0 L0 skel hs hL hP hnM hreg hpG hr hgN hmax h.1.1 h0 hg
  have hacc := acceptsJ8ZA_of_V h.1.1 h0
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hg
  have O := BundleJ8.outJ8_of_outside _ _ b hoC
  have houtC := O.valid hl.budV.1 hl.budV.2
  erw [hl.rdV.1, hl.rdV.2] at houtC
  have hsatC0 : (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) :=
    CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hacc.hsatC
  have hbindC0 : (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) :=
    CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hacc.hbindC
  have hv := cell_validity_sum δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hsatC0 hbindC0 hacc.hinjC
    hacc.hadjC _ _ (ProbJ8.chalsOK_J8 (δ := δ) χ)
  set MF := cellValidityFacts δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hsatC0 hbindC0 hacc.hinjC
    hacc.hadjC _ _ (ProbJ8.chalsOK_J8 (δ := δ) χ) with hMF
  have hd := TeleC.den_ne_of_out _ _ _ _ houtC
  have hdB : ∀ q ∈ SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) ++
      (toMsgJ8ZA δ b Pb c χ M tr).xsC,
      FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ q.1 ≠ 0 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact MF.ne_zero r hr
    · exact hacc.hxneC q hq
  have hsum : ((toMsgJ8ZA δ b Pb c χ M tr).reqsC.map fun r =>
      (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
      Quad.mk _ (M.pubsC 0) (M.pubsC 1) + ((toMsgJ8ZA δ b Pb c χ M tr).xsC.map fun x =>
        x.2 * (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1)⁻¹).sum :=
    hacc.hsumC
  have hsum' : (((toMsgJ8ZA δ b Pb c χ M tr).reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
      M.pubsC (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))).map fun r =>
        (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
      ((SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) ++
        (toMsgJ8ZA δ b Pb c χ M tr).xsC).map fun q =>
          q.2 * (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ q.1)⁻¹).sum := by
    rw [List.map_append, List.sum_append, hsum, List.map_append, List.sum_append]
    simp only [SVFrame.liftWts, List.map_map, Function.comp_def]
    rw [hv]; ring
  rw [mem_IOFailureEventW_iff] at houtC
  push Not at houtC
  exact BalanceQ.fibre_counts _ _ ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ hd hdB hsum' houtC.1 houtC.2.2

end BalH

/-! ## 3. `trace_unique_closed''` -/

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`trace_unique_closed''`**: `trace_unique_closed'` with the auxiliary balances wired: the V extra providers
are `xsC = []` (`xsC_nil`); the X balance is the export balance (`hbalX_canon`, consumers `fxReqsJ8 … tr`, no extra
provider); the path consumers are `reqsPW …` (`hreqW_canon`); the X and H consumer lists are equal by their
congruences (`fxReqs_eq`, `reqsHW_eq`). Remaining: the event-side balances `hbalV`, `hbalH`, `hbalW` (with its
provider list), `hfp`, and the walk-read hypotheses. -/
theorem trace_unique_closed'' [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
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
    -- the cell balances V (extra providers `xsC`) and H (consumers `reqsHW`, providers `cellProvsW`)
    (hbalV : ∀ r, ((vReqs δ b Pb c χ M tr).count r : 𝕂′) =
      pw (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)) ++
        (toMsgJ8ZA δ b Pb c χ M tr).xsC) r)
    (hbalH : ∀ r, ((reqsHW δ b Pb c χ M.m M.ρ M.ρS M.pubsW M.pubsJ tr).count r : K) =
      pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) r)
    (hbalV' : ∀ r, ((vReqs δ b Pb c χ M' tr').count r : 𝕂′) =
      pw (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')) ++
        (toMsgJ8ZA δ b Pb c χ M' tr').xsC) r)
    (hbalH' : ∀ r, ((reqsHW δ b Pb c χ M'.m M'.ρ M'.ρS M'.pubsW M'.pubsJ tr').count r : K) =
      pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC)) r)
    -- the walk
    (hk1 : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hfp : ∀ c1 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr, ∀ c2 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      c1.p = c2.p → c1.b0.idx = c2.b0.idx)
    (provsW provsW' : List ((Fin 5 → K) × K))
    (hbalW : ∀ r, ((reqsPW δ b Pb c χ M.m M.ρ M.ρS tr).count r : K) = pw provsW r)
    (hdW : (provsW.map Prod.fst).Nodup)
    (hsubW : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW), q ∈ provsW)
    (hbalW' : ∀ r, ((reqsPW δ b Pb c χ M'.m M'.ρ M'.ρS tr').count r : K) = pw provsW' r)
    (hdW' : (provsW'.map Prod.fst).Nodup)
    (hsubW' : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
      (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW), q ∈ provsW')
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
  have hz := zC_of_outside δ rfl hg
  -- (i) the non-multiplicity round-0 cell columns
  obtain ⟨hnm, -⟩ := r0M_nm_closed δ b h.1 h'.1 hS hS' (extB_atoms p (rAT b Pb tr))
    (extB_atoms p (rAT b Pb tr')) hfrag hrun hsz hB hB' ⟨_, hden 0⟩ ⟨_, hden 1⟩ ⟨_, hden 2⟩
    ⟨_, hden' 0⟩ ⟨_, hden' 1⟩ ⟨_, hden' 2⟩
  -- (ii) the keys
  have hkey := keys_of_nm δ b (hpG := hpG) h.1.1 h'.1.1 hz hS hS' hnm
  -- the compute round 0 and the claim serials
  obtain ⟨hr0C, hclaim⟩ := r0C_closed_nm δ b hPb hRg χ M M' tr tr' ax _ _ _ _ hqM hk hqM hk
    h.1.1 h'.1.1 h0 hg hg' hl hl' h.1.2.hC h'.1.2.hC h.1.2.hM h.1.2.hApad h'.1.2.hApad hnm hfrag hrun
  -- `hreqW` (the path consumers `reqsPW`), from the compute round 0
  have hreqW := hreqW_canon δ b h h' hr0C
  -- the walk, over the non-multiplicity cell table
  have hcellN := hcellN_of_nm δ b (hpG := hpG) h.1.1 h'.1.1 hz hS hS' hnm
  obtain ⟨hr0W, hauxW, hr1W⟩ := walk_closed_nm δ b h h' hk1 hkn hkp houtW houtW' hl.hXW hl'.hXW hcellN hfp
    hl.hHXW hl'.hHXW _ _ provsW provsW' hbalW hdW hsubW hbalW' hdW' hsubW' hreqW noPath hE10 hE10' hnW1
    Rd hszW hprov hprov'
  -- (iii) the consumer lists
  have hreqs : vReqs δ b Pb c χ M tr = vReqs δ b Pb c χ M' tr' ∧
      fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr = fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr' ∧
      reqsHW δ b Pb c χ M.m M.ρ M.ρS M.pubsW M.pubsJ tr = reqsHW δ b Pb c χ M'.m M'.ρ M'.ρS M'.pubsW M'.pubsJ tr' :=
    ⟨vReqs_eq δ b (hpG := hpG) h.1.1 h'.1.1 hz hS hS' hnm hclaim, fxReqs_eq δ b h h' hr0W hr1W,
      reqsHW_eq δ b h h' hr0C hr0W⟩
  -- the X balance and the extra providers
  have hbalX := hbalX_canon δ b R0 L0 skel hs hL hP hnM hreg h hg
  have hbalX' := hbalX_canon δ b R0 L0 skel hs hL hP hnM hreg h' hg'
  -- (iv) the multiplicities, hence every round-0 and aux cell column
  obtain ⟨hr0M, hauxM⟩ := r0M_auxM_closed'' δ b h.1 h'.1 hS hS' (extB_atoms p (rAT b Pb tr))
    (extB_atoms p (rAT b Pb tr')) hfrag hrun hsz hB hB' ⟨_, hden 0⟩ ⟨_, hden 1⟩ ⟨_, hden 2⟩
    ⟨_, hden' 0⟩ ⟨_, hden' 1⟩ ⟨_, hden' 2⟩
    _ hbalV (hdeV_canon δ b h.1.2) (hdisV_canon δ b h.1.2 _) [] hbalX List.nodup_nil (fun _ _ _ he => absurd he List.not_mem_nil) hbalH
    _ hbalV' (hdeV_canon δ b h'.1.2) (hdisV_canon δ b h'.1.2 _) [] hbalX' List.nodup_nil (fun _ _ _ he => absurd he List.not_mem_nil) hbalH'
    hreqs hkey
  exact trace_unique_good'' δ b R0 L0 skel hs hL hP hnM hreg h0 h h' hg
    ⟨hr0C, hr0M, hauxM, hr0W, hauxW, hr1W, hS, hS', hclaim⟩


/-- **`trace_unique_closed'''`**: `trace_unique_closed''` with the event-side balances `hbalV`, `hbalH`, `hbalW`
discharged from the `dataA` event (`hbalV_canon`, `hbalH_canon`, `hbalW_canon`) at `provsW := walkPProvs …`
(so `hsubW` is trivial). Remaining: `hdW` (distinct keys of the walk's provided path records), `hfp`, the walk-read
hypotheses. -/
theorem trace_unique_closed''' [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) {c : P8PublicClaim}
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hr : WeightsJ8.RowsLe r EncInjJ8.cornerC) (hgN : g ≤ 2 ^ 31) (hmax : Pb.nA + 2 ≤ r.maxlen)
    (hqM : ∀ x < ringChar (ZMod p), Nock.Atoms.lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hg : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr χ)
    (hg' : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr' χ)
    {fuel : ℕ} {tg : NTree SkelX} {res : Noun} (hrun : genX Rg fuel c.subject c.formula = some (tg, res))
    (hsz : Pb.nC = (cellsOfRoots (rootsOf c (rowsOfT tg))).length)
    (hk1 : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hfp : ∀ c1 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr, ∀ c2 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      c1.p = c2.p → c1.b0.idx = c2.b0.idx)
    (hdW : ((ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)).map Prod.fst).Nodup)
    (hdW' : ((ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
      (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)).map Prod.fst).Nodup)
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
    (tr, ax, M) = (tr', ax', M') :=
  trace_unique_closed'' δ b hRg R0 L0 skel hs hL hP hnM hreg hr hgN hmax hqM hk h h' hg hg' hrun hsz
    (hbalV_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h hg)
    (hbalH_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h hg)
    (hbalV_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h' hg')
    (hbalH_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h' hg')
    hk1 hkn hkp hfp _ _
    (hbalW_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h hg) hdW (fun _ hq => hq)
    (hbalW_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h' hg') hdW' (fun _ hq => hq)
    noPath hE10 hE10' hnW1 Rd hszW hprov hprov'

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.fxReqsJ8_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.fxReqs_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.reqsOf_x
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.walkXReqs_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.reqsHW_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.reqsHW_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.trace_unique_closed''
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.hbalH_of_ioA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.hbalH_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.hbalW_of_ioA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.hbalW_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.hbalV_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1.trace_unique_closed'''
