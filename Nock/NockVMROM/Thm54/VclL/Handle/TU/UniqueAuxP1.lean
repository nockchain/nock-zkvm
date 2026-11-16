/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/UniqueAuxP1.lean

 **Trace uniqueness on the P1 fragment: three auxiliary discharges for `UniqueCloseP1.trace_unique_closed`.**
 No existing module edited.

 * §A `hreqW`: the compute path requests (`.p`) in `K` (`reqsPW`, = `DenXJ8.compReqsX … .p`; `reqsOf … .p` is
 their lift, `reqsOf_p`). **`reqsPW_congr`**: they depend only on the round-0 compute columns `< 69` (as
 polynomials) — no coin, no public, so in particular not on `M.m M.ρ M.ρS` (`ReadIOJ8.compReqsX_congr`).
 **`hreqW_canon`**: two `AcceptsCanon2` tuples whose round-0 compute columns agree at every row (`OpenP1.r0C`,
 what `r0C_closed` gives) have equal path-request lists (the degree lift `DegLiftP1.poly_eq_of_rows`).
 * §B the extra validity providers of the J-8 balance are `(toMsgJ8ZA … M tr).xsC = mbXs (atom table)`, a
 readout of the committed atom table (rows with `mb ≠ 0`), not a free message column. On the P1 fragment the
 atom table is the pad row on its round-0 columns (`CanonP1.hApad`), and `mb = 196 < 205` with `padA 196 = 0`,
 so **`xsC_nil`**: `xsC = []` — derivable, no new pin needed. `hdeV_canon`, `hdisV_canon`.
 * §C `hbalX`: the 11-wide export balance over `cXRec` is the J-8 walk's fingerprint-export balance
 (`RealVJ8.fxReqsJ8` / `fxProvsJ8`: the J-8 walk's consumed keys `walkXInternal` against the cell table's
 `cellXRecords`, internal on both sides, terminal `pubsC(2,3) = pubsW(0,1)`, `AcceptsJ8V.hfxC`), whose lookup
 form is `LinkJ8A.hXW_of_ioA`. **`walk_export_counts`** (chip level: `BalanceQ.fibre_counts` in place of
 `finiteIO_lookup_sound_weighted`), **`hbalX_of_ioA`**, **`hbalX_of_R5`** (under `linkXUA_of_R5`'s hypotheses),
 **`hbalX_canon`** (at `AcceptsCanon2` and the `dataA` event, the hypothesis list of `trace_unique_closed`):
 `reqsX = fxReqsJ8 … tr`, `extraX = []`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1
import Nock.NockVMROM.Thm54.VclL.Handle.ReadIOJ8
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (ClaimMsgVS)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 pubVJ8 chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX qA qM qW reqsOf extJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG mbXs)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (toMsgJ8ZA AcceptsJ8ZA acceptsJ8ZA_of_V)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (c4 c5 c6 c7)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell)
open Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8 (fxReqsJ8 fxProvsJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1 (AcceptsCanon2)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1 (qCell)

noncomputable section

/-! ## A. `hreqW`: the compute path requests read the round-0 compute columns only -/

section ReqP
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The compute path requests** (`.p`) in `K` at the claim message `(m, ρ, ρS)`: `DenXJ8.compReqsX … .p` at the
J-8 compute view. (`reqsOf … .p` is their lift, `reqsOf_p`; the `.p` balance has no external requests.) -/
def reqsPW (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    (tr : TrJ8 (ZMod p)) : List (Fin 5 → K) :=
  DenXJ8.compReqsX (K := K) (hn := Pb.hn) (nodes := Pb.nodes) (chalV := chalVJ8 b χ)
    (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := Pb.orbit) (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ))
    .p

/-- `reqsOf … .p` is the lift of `reqsPW`. -/
theorem reqsOf_p (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : AcceptsJ8.MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    reqsOf δ b Pb c χ M tr .p = (reqsPW δ b Pb c χ M.m M.ρ M.ρS tr).map (BalanceQ.liftRec (L := 𝕂′)) := by
  show List.map _ (_ ++ []) = _
  rw [List.append_nil]
  rfl

/-- **The path-request congruence**: `reqsPW` depends only on the round-0 compute columns `< 69`; not on the
coin-independent claim message `(m, ρ, ρS)` at all (and the coin `χ` enters only through the view, which reads no
coin, `ReadIOJ8.compReqsX_congr`). -/
theorem reqsPW_congr (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) {m m' : ClaimMsgVS}
    {ρ ρ' : Fin 5 → 𝕂′} {ρS ρS' : 𝕂′} {tr tr' : TrJ8 (ZMod p)}
    (hC : ∀ j : Fin 123, (j : ℕ) < 69 → tr.C j = tr'.C j) :
    reqsPW δ b Pb c χ m ρ ρS tr = reqsPW δ b Pb c χ m' ρ' ρS' tr' :=
  ReadIOJ8.compReqsX_congr _ _ (fun j h1 h2 hj => hC ⟨j, h1⟩ hj) .p

/-- The lifted form (`reqsOf … .p`, what `LinkJ8XUA.rdP` reads). -/
theorem reqsOf_p_congr (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) {M M' : AcceptsJ8.MsgJ8 p K δ}
    {tr tr' : TrJ8 (ZMod p)} (hC : ∀ j : Fin 123, (j : ℕ) < 69 → tr.C j = tr'.C j) :
    reqsOf δ b Pb c χ M tr .p = reqsOf δ b Pb c χ M' tr' .p := by
  rw [reqsOf_p, reqsOf_p, reqsPW_congr δ b Pb c χ hC]

variable [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`hreqW` at two `AcceptsCanon2` tuples**: equal round-0 compute columns at every row (`OpenP1.r0C`) give equal
path-request lists, hence equal counts. -/
theorem hreqW_canon {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hr0C : ∀ j : Fin 123, (j : ℕ) < 69 → ∀ i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i)) :
    ∀ x, (reqsPW δ b Pb c χ M.m M.ρ M.ρS tr).count x = (reqsPW δ b Pb c χ M'.m M'.ρ M'.ρS tr').count x := by
  intro x
  rw [reqsPW_congr δ b Pb c χ (m' := M'.m) (ρ' := M'.ρ) (ρS' := M'.ρS) (tr' := tr') fun j hj =>
    DegLiftP1.poly_eq_of_rows h.1.1.hinjX (h.1.2.hdeg.C j) (h'.1.2.hdeg.C j) (hr0C j hj)]

end ReqP

/-! ## B. the extra validity providers are `[]` on the P1 fragment -/

section XsC
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`xsC = []`**: the extra validity providers `(toMsgJ8ZA … M tr).xsC` are the atom table's `mb ≠ 0` rows
(`mbXs`); with the atom table's round-0 columns the pad row (`CanonP1.hApad`), the `mb` column (`196`) is
`padA 196 = 0` at every row. -/
theorem xsC_nil (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (hApad : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j)) :
    (toMsgJ8ZA δ b Pb c χ M tr).xsC = [] := by
  show mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) = []
  unfold mbXs
  refine List.flatMap_eq_nil_iff.mpr fun i _ => if_pos ?_
  simp only [AtomServedQ.aEF]
  rw [envOfTrace_trace _ _ _ _ _ (by rw [AtomChipHQ.atomChipHQ_width]; decide)]
  show (tr.A ⟨196, by norm_num⟩).eval _ = 0
  rw [hApad ⟨196, by norm_num⟩ (by norm_num)]
  simp [padA]

/-- `hdeV` at `extraV = xsC`. -/
theorem hdeV_canon {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p} {c : P8PublicClaim}
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (h : CanonP1 δ b hpG sz Pb c M tr ax) : ((toMsgJ8ZA δ b Pb c χ M tr).xsC.map Prod.fst).Nodup := by
  rw [xsC_nil δ b Pb c χ M tr h.hApad]; exact List.nodup_nil

/-- `hdisV` at `extraV = xsC` (any left list). -/
theorem hdisV_canon {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p} {c : P8PublicClaim}
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (h : CanonP1 δ b hpG sz Pb c M tr ax) (L : List ((Fin 5 → 𝕂′) × 𝕂′)) :
    ∀ a ∈ L.map Prod.fst, ∀ e ∈ (toMsgJ8ZA δ b Pb c χ M tr).xsC.map Prod.fst, a ≠ e := by
  rw [xsC_nil δ b Pb c χ M tr h.hApad]; simp

end XsC

/-! ## C. `hbalX`: the J-8 walk's fingerprint-export balance in count form -/

section ChipX
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (kroots : ℕ)
  (b : Basis (Fin 3) F K) {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → F)
  (orbitC : StrictOrbitDomain F 3 hC) {hP nP : ℕ} (hnP : 0 < nP) (nodesP : Fin nP → F)
  (orbitP : StrictOrbitDomain F 3 hP) (chals pubsC pubsP : ℕ → K)
  (QC : Fin (cellChip δF b hnC nodesC orbitC chals pubsC).rap.w → F[X])
  (QP : Fin (walkChip δF kroots b hnP nodesP orbitP chals pubsP).rap.w → F[X])
  [Fintype K] [DecidableEq (Quad (algebraMap F K δF))]

/-- **The export balance in count form** (`walk_keys_exported`'s data, `fibre_counts` in place of the lookup):
outside the weighted IO event at `reqs ++ internal`, every 11-wide key's consumer count is its provider weight in
the cell table's export records. -/
theorem walk_export_counts
    (hsatC : (cellChip δF b hnC nodesC orbitC chals pubsC).rap.Satisfies QC)
    (hbindC : (cellChip δF b hnC nodesC orbitC chals pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hsatP : (walkChip δF kroots b hnP nodesP orbitP chals pubsP).rap.Satisfies QP)
    (hbindP : (walkChip δF kroots b hnP nodesP orbitP chals pubsP).BindsPreprocessing QP)
    (hinjP : Function.Injective nodesP)
    (hadjP : ∀ (i : Fin nP) (hi : (i : ℕ) + 1 < nP), nodesP ⟨(i : ℕ) + 1, hi⟩ = nodesP i * orbitP.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) (ρX : Quad (algebraMap F K δF))
    (hpub : Quad.mk _ (pubsC 2) (pubsC 3) = ρX + Quad.mk _ (pubsP 0) (pubsP 1))
    (reqs : List (Fin 11 → Quad (algebraMap F K δF)))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r)⁻¹).sum = ρX)
    (hne : ∀ r ∈ reqs, FiniteIO.compress (m := 11) ⟨γ, ρ⟩ r ≠ 0)
    (hγ : γ ∉ FiniteIO.IORLCCollisionEvent (FiniteIO.recordsW (reqs ++ walkXInternal δF kroots b hnP nodesP orbitP
      chals pubsP QP) (SVFrame.liftWts (cellXRecords δF b hnC nodesC orbitC chals pubsC QC))))
    (hpole : ρ ∉ FiniteIO.IOLogDerivEventW (reqs ++ walkXInternal δF kroots b hnP nodesP orbitP chals pubsP QP)
      (SVFrame.liftWts (cellXRecords δF b hnC nodesC orbitC chals pubsC QC)) γ) :
    ∀ r, ((reqs ++ walkXInternal δF kroots b hnP nodesP orbitP chals pubsP QP).count r :
      Quad (algebraMap F K δF)) = pw (SVFrame.liftWts (cellXRecords δF b hnC nodesC orbitC chals pubsC QC)) r := by
  set M := cellExportFactsW δF kroots b hnC nodesC orbitC hnP nodesP orbitP chals pubsC pubsP QC QP
    hsatC hbindC hinjC hadjC hsatP hbindP hinjP hadjP γ ρ hok ρX hpub with hM
  exact BalanceQ.fibre_counts
    (reqs ++ walkXInternal δF kroots b hnP nodesP orbitP chals pubsP QP) (SVFrame.liftWts M.records) ⟨γ, ρ⟩
    (by
      intro r hr
      rcases List.mem_append.mp hr with h | h
      · exact hne r h
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
        have hj' := List.mem_range.mp hj
        rw [walk_compressK δF kroots b hnP nodesP orbitP chals pubsP QP γ ρ hok WChip.xKey (m := 11) rfl le_rfl j]
        exact (walk_xinv δF kroots b hnP nodesP orbitP chals pubsP QP hsatP j hj').1)
    (by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact M.ne_zero r hr)
    (by
      rw [List.map_append, List.sum_append, hsum]
      have := M.sum_eq
      simp only [SVFrame.liftWts, List.map_map, Function.comp_def]
      exact this.symm)
    hγ hpole

end ChipX

section HbalX
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`hbalX` from the export balance** (the count twin of `LinkJ8A.hXW_of_ioA`): on an `AcceptsJ8ZA` trace with
`pubsC(2,3) = pubsW(0,1)`, outside the IO failure event of the export balance, the J-8 walk's consumed export keys `fxReqsJ8`
balance the cell table's export records `cXRec` record by record (no extra providers). -/
theorem hbalX_of_ioA [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : AcceptsJ8.MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8ZA δ b Pb Rg c χ M tr)
    (hp : 64 ≤ p)
    (hWC : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 2) (M.pubsC 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsW 0) (M.pubsW 1))
    (hout : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr) (fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr)) :
    ∀ x, ((fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr).count x : 𝕂′) =
      pw (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
          (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) ++ []) x := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp64 : 64 ≤ ringChar (ZMod p) := by rw [hrc]; exact hp
  have hsatC := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hacc.hsatC
  have hbindC := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _
    hacc.hbindC
  have hsatP := AtomWalkAW.walkChipHQK_restrict_sat δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _
    (WalkJ8.walkChipJ8_bitFix_sat δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _ hF hp64 hacc.hsatW)
  have hbindP := AtomWalkAW.walkChipHQK_restrict_bind δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsW _ (WalkJ8.walkChipJ8_bitFix_bind δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW _
      hacc.hbindW)
  have hrq : walkXInternal δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (AtomWalkAW.restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))) = fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr :=
    RealVJ8.wXInt_bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ _ tr.W
  have hpv : liftWts (cellXRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) = fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr := by
    have hw : 183 ≤ (cellChip δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.w := by
      rw [cell_w]; norm_num
    rw [cXRec_chip]
    exact congrArg liftWts
      (cXRec_congr δ b Pb.nodesC Pb.orbitC _ _ _ _ _ _ hw (by norm_num) fun j hj => congrArg tr.M (Fin.ext rfl))
  rw [← hrq, ← hpv] at hout
  have key := walk_export_counts δ Pb.kroots b Pb.hnC Pb.nodesC Pb.orbitC Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ)
    M.pubsC M.pubsW _ _ hsatC hbindC hacc.hinjC hacc.hadjC hsatP hbindP hacc.hinjW hacc.hadjW _ _
    (ProbJ8.chalsOK_J8 δ χ) 0 (by rw [zero_add]; exact hWC) [] (by simp) (by simp)
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inl hc)))
    (fun hc => hout (mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc))))
  intro x
  rw [List.append_nil, ← hrq]
  exact key x

/-- **`hbalX` under `linkXUA_of_R5`'s hypotheses** (at the message `toMsgJ8ZA … M tr`, whose `pubsC` is
`M.pubsC`): the terminal match is `AcceptsJ8V.hfxC`, the event is the export-balance IO event (`Lift40J8.fpx_out` of the `L` data). -/
theorem hbalX_of_R5 [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    (hpG : p = Nock.Atoms.p)
    (hacc3 : AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r g) (h0 : Pb.krootsV = 0)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b
      (ListJ8C.withLiftC (AbsentVJ8.RR4A δ b (g := g + r.N) R0 Pb c skel hs hL hP hnM hreg)
        (LinkJ8R4.LL4 δ b L0 Pb skel hs hL))
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA), ¬ s.mem tr χ) :
    ∀ x, ((fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr).count x : 𝕂′) =
      pw (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)) ++ []) x := by
  have hp64 : 64 ≤ p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hacc := acceptsJ8ZA_of_V hacc3 h0
  have hB := hacc3.hbud
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hout
  have hfx := Lift40J8.fpx_out (LinkJ8R4.LL4 δ b L0 Pb skel hs hL) (ListJ8C.outside40C _ _ hoC)
    (by show (RealVJ8.fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr).length ≤ r.W
        rw [RealVJ8.fxReqsJ8, walkXInternal_length]; exact hL.W)
    (by show (RealVJ8.fxProvsJ8 δ b Pb.nodesC Pb.orbitC tr).length ≤ 2 * r.D
        rw [RealVJ8.fxProvsJ8, liftWts_length]
        exact (cXRec_length δ b _ _ _ _ _).trans (by have := hB.x2; omega))
  exact hbalX_of_ioA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr hacc hp64
    (by show Quad.mk _ (M.pubsC 2) (M.pubsC 3) = Quad.mk _ (M.pubsW 0) (M.pubsW 1)
        rw [hacc3.hfxC.1, hacc3.hfxC.2]) hfx

/-- **`hbalX` at `AcceptsCanon2`** with the `dataA` event, the hypotheses `trace_unique_closed` already carries:
`reqsX := fxReqsJ8 … tr`, `extraX := []` (so `hdeX`, `hdisX` hold trivially). -/
theorem hbalX_canon [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim}
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g)
    (hg : ∀ s ∈ allJ8X (Comp12P1.dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr χ) :
    ∀ x, ((fxReqsJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW tr).count x : 𝕂′) =
      pw (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)) ++ []) x := by
  have hPb := h.1.2.hPb
  have h0 : Pb.krootsV = 0 := by rw [hPb]; rfl
  exact hbalX_of_R5 δ b Pb c χ M tr R0 L0 skel hs hL hP hnM hreg hpG h.1.1 h0 hg

end HbalX

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.reqsOf_p
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.reqsPW_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.reqsOf_p_congr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.hreqW_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.xsC_nil
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.hdeV_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.hdisV_canon
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.walk_export_counts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.hbalX_of_ioA
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.hbalX_of_R5
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1.hbalX_canon
