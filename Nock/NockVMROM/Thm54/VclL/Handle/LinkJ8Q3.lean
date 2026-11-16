/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkJ8Q3.lean

* §1 **L8 (`hs`) is FALSE on accepted traces: the verifier is blind to the content of the claim's cell
    nouns.**  `AcceptsJ8` reads the claim `c` only through `pubVJ8 … c M.m …`, i.e. through `labelF c M.m`;
    a cell noun's label is `(1, idx)` with `idx` a PROVER message, so the content of a cell noun is read by
    no check (`pubVJ8_claim_congr`, `acceptsJ8_claim_congr`).  Instance: `cTrue = *[[0 0] [0 1]] = [0 0]`
    (true) and `cFalse = *[[1 1] [0 1]] = [0 0]` (false) have the same labels (`labelF_cTrue_cFalse`), so
    every `(χ, M, tr)` accepted for `cTrue` is accepted for `cFalse` (`acceptsJ8_cFalse_of_cTrue`), and
    `HoldsN cFalse` is false (`not_holdsN_cFalse`).  By `hsoundJ8`, at such a coin outside `allJ8C` no
    `LinkJ8` at `cFalse` exists (`no_linkJ8_cFalse`); every field of `LinkJ8 … cFalse …` other than `hs` is
    the SAME proposition as at `cTrue` (`linkJ8_cFalse_of_cTrue`: from `LinkJ8 … cTrue …` and the `cFalse`
    `hs` one gets `LinkJ8 … cFalse …`), so the false field is `hs` (`hs_false_cFalse`).  The same holds for
    atoms `v` and `v + p` (`labelF_atom_wrap`, `acceptsJ8_atom_wrap`): an atom claim noun is read mod `p`.
    Missing verifier checks: the claim's cell records `claimVec (E x) idx hi lo` among the cell-validity
    external requests (the 40th's `ρ₀ = claimValSum`), and the claim's atoms `< p` (the 40th's `hclaim`).
  * §2 **L1 (`hcountC`, `rdV`) cannot hold at every accepted message: the messages are unstaged.**
    `padM M r` appends `p` copies of `r` to `M.reqsC`; `hsumC` is unchanged in characteristic `p` and
    `hpinC` is monotone, so `padM` preserves `AcceptsJ8` (`acceptsJ8_padM`) and violates `hcountC`
    (`not_linkJ8_padM`).  Hence `probJ8_final`'s hypothesis `hlink` (`LinkJ8` at EVERY accepted `M`) forces
    the verifier to accept nowhere (`hlink_forces_no_accept`): the conditional figure is vacuous.
    Independently of the count, `padX M x` adds one request `x.1` and one external provide `(x.1, 1)` for an
    existing `x ∈ M.xsC` (`acceptsJ8_padX`), so at one `(tr, χ)` two accepted messages have different
    `reqsC`, and `rdV` (a readout of `(tr, χ)` alone) fails at one of them (`not_rdV_both`): `M.reqsC` /
    `M.xsC` are post-coin messages, not staged before `γ′ρ′`.
  * §3 **L8 `hseed` / `hreal`, discharged** from `AcceptsJ8` alone (binder `17 < p`): `row0_claim` (row 0's
    `s f e` handles are the claim publics `0..5`, `claimEq` under `isFirst`), `hseedJ8` (the seed public
    `pubSeed` is `rlc γW (encT row-0 label) · αW`), `hrealJ8` (row 0 is not a chain state when the claim's
    formula is a cell: kind `1` against `s10L_row` / `s10T_row`'s kind `0`).  At an ATOM formula `hreal` is
    not derived (the claim is false; whether such a trace is accepted is open).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q3

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (compReqsX)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.Atoms (lenL)

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8

noncomputable section

/-! ## 1. L8: the claim's cell nouns are read by no check -/

/-- `*[[0 0] [0 1]] = [0 0]`: a TRUE claim. -/
def cTrue : P8PublicClaim :=
  ⟨.cell (.atom 0) (.atom 0), .cell (.atom 0) (.atom 1), .cell (.atom 0) (.atom 0)⟩

/-- `*[[1 1] [0 1]] = [0 0]`: a FALSE claim with the same shape. -/
def cFalse : P8PublicClaim :=
  ⟨.cell (.atom 1) (.atom 1), .cell (.atom 0) (.atom 1), .cell (.atom 0) (.atom 0)⟩

theorem holdsN_cTrue : Nock.Jet.HoldsN cTrue := ⟨1, by simp [cTrue, Nock.evalN, Nock.Noun.slot]⟩

theorem not_holdsN_cFalse : ¬ Nock.Jet.HoldsN cFalse := by
  rintro ⟨fuel, h⟩
  cases fuel with
  | zero => simp [Nock.evalN] at h
  | succ n => simp [cFalse, Nock.evalN, Nock.Noun.slot] at h

section Congr
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K)

/-- **The compute publics read the claim only through its labels.** -/
theorem pubVJ8_claim_congr {c c' : P8PublicClaim} {m : ClaimMsgVS} (h : labelF (F := F) c m = labelF (F := F) c' m)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (ρS : Quad (algebraMap F K δF)) (χ : Coins frameJ8 K) :
    pubVJ8 δF b c m ρ ρS χ = pubVJ8 δF b c' m ρ ρS χ := by
  funext j
  simp only [pubVJ8, pubVHQ, pubVH, seedVS, h]

/-- The two claims have the same labels at EVERY message (all six nouns are cells or equal). -/
theorem labelF_cTrue_cFalse (m : ClaimMsgVS) : labelF (F := F) cTrue m = labelF (F := F) cFalse m := rfl

end Congr

/-- An atom claim noun is read mod `p`: `v` and `v + p` have the same label. -/
theorem labelF_atom_wrap {p : ℕ} [Fact p.Prime] (v : ℕ) (f e : Noun) (m : ClaimMsgVS) :
    labelF (F := ZMod p) ⟨.atom v, f, e⟩ m = labelF (F := ZMod p) ⟨.atom (v + p), f, e⟩ m := by
  simp [labelF, hvalF, claimH, claimNoun, claimHandle] <;> (repeat' apply And.intro) <;> rfl

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`AcceptsJ8` depends on the claim only through its labels.** -/
theorem acceptsJ8_claim_congr (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) {c c' : P8PublicClaim}
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (h : labelF (F := ZMod p) c M.m = labelF (F := ZMod p) c' M.m) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) :
    AcceptsJ8 δ b Pb Rg c' χ M tr := by
  have hs := hacc.hsatX
  rw [pubVJ8_claim_congr δ b h M.ρ M.ρS χ] at hs
  exact { hacc with hsatX := hs }

/-- **Every `(χ, M, tr)` accepted for the true `cTrue` is accepted for the false `cFalse`.** -/
theorem acceptsJ8_cFalse_of_cTrue (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg cTrue χ M tr) :
    AcceptsJ8 δ b Pb Rg cFalse χ M tr :=
  acceptsJ8_claim_congr δ b Pb Rg χ M tr (labelF_cTrue_cFalse M.m) hacc

/-- **The atom wrap**: accepted for `*[v f] = e` ⇒ accepted for `*[(v + p) f] = e`. -/
theorem acceptsJ8_atom_wrap (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (v : ℕ) (f e : Noun) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hacc : AcceptsJ8 δ b Pb Rg ⟨.atom v, f, e⟩ χ M tr) :
    AcceptsJ8 δ b Pb Rg ⟨.atom (v + p), f, e⟩ χ M tr :=
  acceptsJ8_claim_congr δ b Pb Rg χ M tr (labelF_atom_wrap v f e M.m) hacc

variable {r : RowsJ8} {P g : ℕ}

/-- **Every `LinkJ8` field but `hs` is the same proposition at `cTrue` and `cFalse`**: from `LinkJ8` at `cTrue`
and the `cFalse` root subject, `LinkJ8` at `cFalse`. -/
theorem linkJ8_cFalse_of_cTrue (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (rA : ℕ → ARow) (hl : LinkJ8 δ b Pb cTrue χ M tr R L rA)
    (hs : denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
      (hdV (envX δ b Pb cFalse χ M tr 0) xS) = some cFalse.subject) :
    LinkJ8 δ b Pb cFalse χ M tr R L rA :=
  { hl with hs := hs }

/-- **No `LinkJ8` at `cFalse`** at a coin accepted for `cTrue` outside `allJ8C` (by `hsoundJ8`). -/
theorem no_linkJ8_cFalse [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves)
    (hacc : AcceptsJ8 δ b Pb Rg cTrue χ M tr)
    (hout : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    (hWV : R.wdC tr χ = walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)))
    (rA : ℕ → ARow) : ¬ LinkJ8 δ b Pb cFalse χ M tr R L rA := fun hl =>
  not_holdsN_cFalse (hsoundJ8 δ b Pb hRg cFalse χ M tr R L hpG hqM hk
    (acceptsJ8_cFalse_of_cTrue δ b Pb Rg χ M tr hacc) hout hWV hl)


/-- A link `LinkJ8 … cTrue …` at an accepted coin yields acceptance of the false claim `cFalse`, with `cFalse` not holding and the J-8 denotation of the subject differing from `cFalse.subject`. -/
theorem hs_false_cFalse [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves)
    (hacc : AcceptsJ8 δ b Pb Rg cTrue χ M tr)
    (hout : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    (hWV : R.wdC tr χ = walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)))
    (rA : ℕ → ARow) (hl : LinkJ8 δ b Pb cTrue χ M tr R L rA) :
    AcceptsJ8 δ b Pb Rg cFalse χ M tr ∧ ¬ Nock.Jet.HoldsN cFalse ∧
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
        (hdV (envX δ b Pb cFalse χ M tr 0) xS) ≠ some cFalse.subject :=
  ⟨acceptsJ8_cFalse_of_cTrue δ b Pb Rg χ M tr hacc, not_holdsN_cFalse, fun hs =>
    no_linkJ8_cFalse δ b Pb hRg χ M tr R L hpG hqM hk hacc hout hWV rA
      (linkJ8_cFalse_of_cTrue δ b Pb χ M tr R L rA hl hs)⟩

/-! ## 2. L1: the messages are unstaged -/

/-- `p` more copies of `r` in the cell validity's external requests. -/
def padM (M : MsgJ8 p K δ) (r0 : Fin 5 → 𝕂′) : MsgJ8 p K δ :=
  { M with reqsC := M.reqsC ++ List.replicate p r0 }

/-- **`padM` preserves acceptance** (`p` equal reciprocals sum to `0` in characteristic `p`). -/
theorem acceptsJ8_padM [CharP 𝕂′ p] (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (r0 : Fin 5 → 𝕂′)
    (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) : AcceptsJ8 δ b Pb Rg c χ (padM δ M r0) tr := by
  refine { hacc with hsumC := ?_, hpinC := ?_ }
  · have h := hacc.hsumC
    simp only [padM, List.map_append, List.sum_append, List.map_replicate, List.sum_replicate, nsmul_eq_mul,
      CharP.cast_eq_zero, zero_mul, add_zero]
    exact h
  · intro id hid
    exact List.mem_append_left _ (hacc.hpinC id hid)

/-- **`LinkJ8` fails at `padM`** (`hcountC`). -/
theorem not_linkJ8_padM (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (rA : ℕ → ARow) (r0 : Fin 5 → 𝕂′) : ¬ LinkJ8 δ b Pb c χ (padM δ M r0) tr R L rA := fun hl => by
  have h := hl.hcountC
  simp only [padM, List.length_append, List.length_replicate] at h
  omega


/-- If every accepted message links to a witness `rA` (`hlink`), then no message is accepted (under the stated side conditions). -/
theorem hlink_forces_no_accept [CharP 𝕂′ p] (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim)
    (Q : Coins frameJ8 K → TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hlink : ∀ χ (M : MsgJ8 p K δ), AcceptsJ8 δ b Pb Rg c χ M (Q χ) → ∃ rA, LinkJ8 δ b Pb c χ M (Q χ) R L rA) :
    ∀ χ (M : MsgJ8 p K δ), ¬ AcceptsJ8 δ b Pb Rg c χ M (Q χ) := fun χ M hacc => by
  obtain ⟨rA, hl⟩ := hlink χ (padM δ M 0) (acceptsJ8_padM δ b Pb Rg c χ M (Q χ) 0 hacc)
  exact not_linkJ8_padM δ b Pb c χ M (Q χ) R L rA 0 hl

/-- One more request `x.1` and one more external provide `(x.1, 1)`, for an existing `x ∈ M.xsC`. -/
def padX (M : MsgJ8 p K δ) (x : (Fin 5 → 𝕂′) × 𝕂′) : MsgJ8 p K δ :=
  { M with reqsC := M.reqsC ++ [x.1], xsC := M.xsC ++ [(x.1, 1)] }

/-- **`padX` preserves acceptance.** -/
theorem acceptsJ8_padX (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (x : (Fin 5 → 𝕂′) × 𝕂′) (hx : x ∈ M.xsC)
    (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) : AcceptsJ8 δ b Pb Rg c χ (padX δ M x) tr := by
  refine { hacc with hsumC := ?gS, hpinC := ?gP, hxneC := ?gN, hxC := ?gX }
  case gS =>
    have h := hacc.hsumC
    simp only [padX, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, one_mul]
    rw [h]; ring
  case gP =>
    intro id hid
    exact List.mem_append_left _ (hacc.hpinC id hid)
  case gN =>
    intro y hy
    simp only [padX, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hacc.hxneC y hy
    · exact hacc.hxneC x hx
  case gX =>
    intro y hy
    simp only [padX, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hacc.hxC y hy
    · exact hacc.hxC x hx


/-- A message `M` and its padding `padX M x` (one extra request and provide) cannot both be linked: the V-table read lists would differ in length. -/
theorem not_rdV_both (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (rA rA' : ℕ → ARow) (x : (Fin 5 → 𝕂′) × 𝕂′) :
    ¬ (LinkJ8 δ b Pb c χ M tr R L rA ∧ LinkJ8 δ b Pb c χ (padX δ M x) tr R L rA') := fun ⟨h1, h2⟩ => by
  have e := h1.rdV.1.symm.trans h2.rdV.1
  have := congrArg List.length e
  simp only [padX, List.length_append, List.length_singleton] at this
  omega

end Accept

/-! ## 3. L8: the root binding `hseed` / `hreal` (discharged; `hreal` at a cell formula) -/

section Root
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- The compute context `XCtx` of an accepted trace (as inside `hsoundJ8`). -/
theorem xctxJ8 (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) :
    XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
      (limbVal b (chalVJ8 b χ) chalAlphaW) (limbVal b (chalVJ8 b χ) chalGammaW)
      (limbVal b (pubVJ8 δ b c M.m M.ρ M.ρS χ) pubSeed) :=
  ⟨hp, hacc.hsatX, hacc.hinjX, hacc.hadjX, rfl, rfl, pubVJ8_IC δ b c M.m M.ρ M.ρS χ, rfl,
    pubVJ8_out δ b c M.m M.ρ M.ρS χ⟩

/-- **Row 0's claim handles are the claim publics** (`claimEq` under `isFirst`). -/
theorem row0_claim (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) :
    (envX δ b Pb c χ M tr 0).trace xS.k = pubVJ8 δ b c M.m M.ρ M.ρS χ 0 ∧
    (envX δ b Pb c χ M tr 0).trace xS.v = pubVJ8 δ b c M.m M.ρ M.ρS χ 1 ∧
    (envX δ b Pb c χ M tr 0).trace xF.k = pubVJ8 δ b c M.m M.ρ M.ρS χ 2 ∧
    (envX δ b Pb c χ M tr 0).trace xF.v = pubVJ8 δ b c M.m M.ρ M.ρS χ 3 ∧
    (envX δ b Pb c χ M tr 0).trace xE.k = pubVJ8 δ b c M.m M.ρ M.ρS χ 4 ∧
    (envX δ b Pb c χ M tr 0).trace xE.v = pubVJ8 δ b c M.m M.ρ M.ρS χ 5 := by
  have XC := xctxJ8 δ b Pb Rg c χ M tr hp hacc
  have hB := RapWalkJ8.baseE XC Pb.hn
  have hF : (envX δ b Pb c χ M tr 0).trace firstX = 1 := by
    have := (RapWalkJ8.walkRowsX_of_sat XC).first 0 Pb.hn
    simpa using this
  have key : ∀ (x y : ℕ), (⟨cc firstX, x, .pub y⟩ : EqG ℚ) ∈ (claimEq (F := ℚ)) →
      (envX δ b Pb c χ M tr 0).trace x = pubVJ8 δ b c M.m M.ρ M.ρS χ y := by
    intro x y hg
    have h := RowSemChipX.eqg hB (List.mem_append_right _ hg) (by simpa [evalQX, cc] using hF)
    simpa [Opnd.expr, evalQX, RapWalkJ8.pubE XC 0] using h
  exact ⟨key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub]),
    key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub]),
    key _ _ (by simp [claimEq, hpub]), key _ _ (by simp [claimEq, hpub])⟩

theorem trip_rowOfX (env : Env (ZMod p)) (st : Nock.Edit.StateX) :
    (rowOfX env st).trip = (hdV env xS, hdV env xF, hdV env xE) := rfl

/-- **L8 `hseed`, discharged**: the seed public is the walk seed of row 0's label. -/
theorem hseedJ8 (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) :
    limbVal b (pubVJ8 δ b c M.m M.ρ M.ρS χ) pubSeed =
      Walk.rlc (limbVal b (chalVJ8 b χ) chalGammaW) (encT (K := K)
        (rowW (envX δ b Pb c χ M tr 0) (stX (envX δ b Pb c χ M tr 0))).trip) *
          limbVal b (chalVJ8 b χ) chalAlphaW := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := row0_claim δ b Pb Rg c χ M tr hp hacc
  rw [limbVal_pubVJ8_low δ b c M.m M.ρ M.ρS χ _ (by simp [pubSeed]),
    limbVal_pubVHQ_low δ b c M.m M.ρ _ _ (by simp [pubSeed]), FrameVS.limb_pubVH_seed,
    Lift40J8.limb_gammaW_J8, Lift40J8.limb_alphaW_J8, rowW_trip, trip_rowOfX]
  have hA : toVS (toVSQ χ) cAlphaW = χ c13 := rfl
  have hG : toVS (toVSQ χ) cGamW = χ c14 := rfl
  simp only [encT, encH, hdV, WalkBridgeJ8.alg_val, p0, p1, p2, p3, p4, p5]
  simp [pubVJ8, pubVHQ, pubVH, seedVS, labelF, hvalF, List.zipIdx, Walk.rlc, Fin.sum_univ_succ, hA, hG]
  ring

/-- **L8 `hreal`, discharged at a cell formula**: row 0's formula handle has kind `1`, and a chain state's
formula handle has kind `0` (`s10L_row`, `s10T_row`). -/
theorem hrealJ8 (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr)
    (hfc : isCellN c.formula = true) :
    (stX (envX δ b Pb c χ M tr 0)).isChain = false := by
  obtain ⟨-, -, p2, -, -, -⟩ := row0_claim δ b Pb Rg c χ M tr hp hacc
  have XC := xctxJ8 δ b Pb Rg c χ M tr hp hacc
  have hB := RapWalkJ8.baseE XC Pb.hn
  have hoh := RapWalkJ8.ohE XC Pb.hn
  have hk1 : (envX δ b Pb c χ M tr 0).trace xF.k = 1 := by
    rw [p2]
    obtain ⟨f, hf⟩ : ∃ l r, c.formula = .cell l r := by
      cases h : c.formula with
      | atom v => rw [h] at hfc; simp [isCellN] at hfc
      | cell l r => exact ⟨l, r, rfl⟩
    obtain ⟨r, hf⟩ := hf
    simp [pubVJ8, pubVHQ, pubVH, labelF, hvalF, claimH, claimNoun, claimHandle, hf]
  have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
  cases hst : stX (envX δ b Pb c χ M tr 0)
  all_goals (try rfl)
  all_goals rw [hst] at hoh
  · have := s10L_row hB (RowSemChipX.oh_one hoh (by decide)) (RowSemChipX.oh_zero hoh (by decide) (by decide))
      (RowSemChipX.oh_zero hoh (by decide) (by decide))
    exact absurd (hk1.symm.trans this.1) h10
  · have := s10T_row hB (RowSemChipX.oh_one hoh (by decide)) (RowSemChipX.oh_zero hoh (by decide) (by decide))
    exact absurd (hk1.symm.trans this.1) h10

end Root

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q3
