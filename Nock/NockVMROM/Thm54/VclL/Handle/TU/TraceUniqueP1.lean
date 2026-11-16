/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/TraceUniqueP1.lean

 **Final assembly: trace uniqueness of the J-8 AIR on the P1 fragment.**

 * §0 the two `AcceptsCanon2` copies agree (`acceptsCanon2_iff`); `AcceptsCanonP1` = `AcceptsCanon2` and the extra pin (E10).
 * §1 `hfp`: on an accepted tuple outside its events, the cell fingerprint `p` determines the serial
 (`hfp_P1`: `row_genuine2`, outside the bivariate census event on the decoded nouns, `CellUniqP1.serial_inj_table`).
 * §2 `hdW`: the walk's provided path-record keys are distinct (`hdW_P1`: the BFS structure `keys_inj`, the root
 order `root_mono`, the prefix bound `pre < 2^61`).
 * §3 `trace_unique_closed4`: `UniqueWireP1.trace_unique_closed'''` with `hfp`, `hdW` and `hprov` discharged; the
 provenance comes from a cover of the reads by the SECOND tuple's compute path requests (`hcov'`) and the equal
 request counts of the two tuples (`hreqW_canon`).
 * §4 `RdP1_lt`, `ReqCoverP1`, **(A) `trace_unique_good_final`** at `canonPb hpG (szOfClaim p) c`: every
 statement-side hypothesis from `ClaimSizesP1` / `UniqueProvP1`; remaining: `P1SizeOK` (explicit), the row parameters, the event data, and `hcov'`.
 * §5 the canonical triple `canonOfP1` (`trCanon`, `axP1`, `msgCanon` at the `omegaG` orbit), `canon_accepts_P1`
 (completeness via `CanonSideP1.canon_complete'`), **(B) `canon_eq_final`**, `trC_staged`, and **(C)
 `trace_unique_prob_final`**: `Pr[AcceptsCanonP1 (Q χ) ∧ Q χ ≠ canonOf χ] ≤ 2·ε(allJ8X dataA) + ε_c`.
 Requires: `hcovC`, the canonical trace's compute path requests cover `RdP1`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueProvP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonSideP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 pubVJ8 chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX qW qM encJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG hcountC_of')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (toMsgJ8ZA acceptsJ8ZA_of_V)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A (LinkJ8XUA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A (rAT)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1 (AcceptsCanon2 two63_lt_ringChar)
open Nock.Atoms (lenL)
open Nock.ComputeTable (FP)

noncomputable section

/-! ## 0. The two `AcceptsCanon2` copies; `AcceptsCanonP1` -/

section Defs
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K) [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`CanonCompleteP1`'s local `AcceptsCanon2` is `UniqueP1.AcceptsCanon2`** (both verbatim the same definition). -/
theorem acceptsCanon2_iff (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (Pb : PubJ8 p)
    (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (ax : AuxP1 (ZMod p)) (r : RowsJ8) (g : ℕ) :
    CanonCompleteP1.AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g ↔ AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g :=
  Iff.rfl

/-- **`AcceptsCanonP1`**: `AcceptsCanon2` and the verifier-side E10 pin (with no path read in the claim's run, the
walk's `idx` vanishes at the first walk node). -/
def AcceptsCanonP1 (hpG : p = Nock.Atoms.p) (sz : P8PublicClaim → SizesP1) (Pb : PubJ8 p) (Rg : Nock.Jet.Registry)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p))
    (r : RowsJ8) (g : ℕ) : Prop :=
  AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g ∧
    (ClaimSizesP1.noPathReads c → (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, Pb.hnW⟩) = 0)

end Defs

/-! ## 1. `hfp`: the cell fingerprint determines the serial -/

section Census
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp] [Fact q.Prime]

/-- A decoded serial's noun is a decoded noun. -/
theorem mem_decodedNouns2_of {t : List (CellRowB0 q)} {ext : ℕ → Option Noun} {i : ℕ} {X : Noun}
    (h : preZNounOfTable2 t ext i = some X) : X ∈ decodedNouns2 t ext := by
  have hi : i < t.length := CellUniqP1.lt_of_decode (show decodeTree _ _ _ _ = _ from h)
  exact List.mem_filterMap.mpr ⟨i, List.mem_range.mpr hi, h⟩

/-- **The bivariate census on the decoded nouns themselves** (`LinkQ2J8.hinjE_of_sep` with no extra nouns): if the
census readout covers the census list, `encZY z y` is injective on the decoded nouns. -/
theorem decoded_inj_of_sep [Algebra Nock.Atoms.Fp Kfp] (hq : 2 ^ 63 < q) {z y : Kfp} (hz : z ≠ 0)
    (hE : InlineAtoms q z (encZY z y)) {t : List (CellRow q Kfp)} {vp : List (VKey Kfp)}
    {ext : ℕ → Option Noun} (h : TableAccepts2 z t vp) (hvp : AtomLeaves (encZY z y) vp ext)
    {k M : ℕ} (hext : ∀ j m, ext j = some m → ∃ v, m = .atom v ∧ lenL v ≤ M)
    (hqM : ∀ x < q, lenL x ≤ M) (hk : 2 * fuelChip ≤ k) {prs : List (List ℕ × List ℕ)}
    (hsub : ∀ pr ∈ censusPairs (censusList2 (t.map (·.b0)) ext), pr ∈ prs) (hsep : SepAt y z prs k M) :
    ∀ a ∈ decodedNouns2 (t.map (·.b0)) ext, ∀ d ∈ decodedNouns2 (t.map (·.b0)) ext,
      encZY z y a = encZY z y d → a = d := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hM1 : 1 ≤ M := (Nock.Atoms.one_le_lenL 0).trans (hqM 0 (by have := (Fact.out : q.Prime).pos; omega))
  have hextM : ∀ j m, ext j = some m → ∀ x ∈ m.leafList, lenL x ≤ M := by
    intro j m hj x hx
    obtain ⟨v, rfl, hv⟩ := hext j m hj
    simp only [Noun.leafList, List.mem_singleton] at hx
    exact hx ▸ hv
  have hS : ∀ n ∈ censusList2 (t.map (·.b0)) ext,
      n.leaves ≤ fuelChip ∧ ∀ x ∈ n.leafList, lenL x ≤ M := by
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · refine ⟨decoded2_leaves_le hq (encZY_cell z y) hE h hvp hn, ?_⟩
      obtain ⟨i, -, hd⟩ := List.mem_filterMap.mp hn
      intro x hx
      rcases decodeTree2_atoms _ ext _ _ _ hd x hx with hx | ⟨j, m, hj, hxm⟩
      · exact hqM x hx
      · exact hextM j m hj x hxm
    · obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hn
      obtain ⟨s, -, hs⟩ := List.mem_filterMap.mp hc
      unfold kidOf at hs
      split_ifs at hs with hw h0
      · cases hs
        refine ⟨by simp [Noun.leaves, fuelChip], ?_⟩
        intro x hx
        simp only [Noun.leafList, List.mem_singleton] at hx
        exact hx ▸ hqM _ (ZMod.val_lt _)
      · obtain ⟨v, rfl, hv⟩ := hext _ n hs
        refine ⟨by simp [Noun.leaves, fuelChip], ?_⟩
        intro x hx
        simp only [Noun.leafList, List.mem_singleton] at hx
        exact hx ▸ hv
  have hinj := encZY_inj_of_sep hz hsub hsep (fun n hn => (hS n hn).1) hk hM1 (fun n hn => (hS n hn).2)
  intro a ha d hd he
  exact hinj a (List.mem_append_left _ ha) d (List.mem_append_left _ hd) he

end Census

section Fp
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1 (cellTab)

/-- **`hfp` of `trace_unique_closed'''`**: on an `AcceptsCanon2` tuple outside every summand of its event data, under
the readout link `LinkJ8XUA`, two cell rows with the same fingerprint `p` have the same serial. Route:
`row_genuine2` (each row decodes to a cell noun `N` with `p = E N`), the bivariate census (outside its summand
`E` is injective on the decoded nouns), and one serial per decoded noun (`CellUniqP1.serial_inj_table`, the
sorted table `canonM`). -/
theorem hfp_P1 [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ}
    {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)} {r0 : RowsJ8} {g0 : ℕ}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r0 g0)
    {R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g}
    {L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r}
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hout : ∀ s ∈ allJ8X (AtomFpxJ8.withFpxV δ b (withLiftC R L) Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV
      Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    (hl : LinkJ8XUA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr R L (rAT b Pb tr)) :
    ∀ c1 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr, ∀ c2 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      c1.p = c2.p → c1.b0.idx = c2.b0.idx := by
  have hacc3 := h.1.1
  have hPb := h.1.2.hPb
  have hpad := h.1.2.hApad
  have hM := h.1.2.hM
  subst hPb
  have h0 : (canonPb hpG sz c).krootsV = 0 := rfl
  have hacc := acceptsJ8ZA_of_V hacc3 h0
  have hoC := AtomFpxJ8.outsideC_of_outsideX _ hout
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  have O := outJ8_of_outside R L b hoC
  set Pb := canonPb hpG sz c with hPbd
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hcountC := hcountC_of' δ b Pb c χ M tr hacc3.hlenC
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (ProbJ8.chalsOK_J8 (δ := δ) χ) _ _ hacc.hsumC houtC
    hacc.hxneC hcountC _ hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  -- the census on the decoded nouns
  have hinj := decoded_inj_of_sep hq' O.z_ne hE htabC hl.hvp hl.hext hqM hk hl.hprs
    (fun _pr hpr hlen hne hkk hM1 hM2 => ListJ8C.biv_out_of_outsideC (withLiftC R L) hoC hpr hlen hne hkk hM1 hM2)
  -- one serial per decoded noun
  have hext := AtomPadP1.extB_rAT_none b Pb (by omega) hpad
  have hvp0 := hl.hvp
  rw [hext] at hvp0
  have hser := CellUniqP1.serial_inj_table hpG hq' (fun a b' => rfl) hE htabC hvp0 (by simp [cellTableOf, hPbd])
    (CellUniqP1.b0_of_canon δ b ax _ _) (CellUniqP1.tableM_of δ b hM hacc.hsatC hacc.hbindC hacc.hinjC)
    (by have := hacc.hnpC; rw [hrc] at this; simp only [hPbd] at this ⊢; omega)
  rw [hext] at hinj
  intro e1 he1 e2 he2 hpe
  obtain ⟨L1, R1, hd1, hp1, -⟩ := row_genuine2 hq' (fun a b' => rfl) hE htabC hvp0 he1
  obtain ⟨L2, R2, hd2, hp2, -⟩ := row_genuine2 hq' (fun a b' => rfl) hE htabC hvp0 he2
  have heq : Noun.cell L1 R1 = Noun.cell L2 R2 :=
    hinj _ (mem_decodedNouns2_of hd1) _ (mem_decodedNouns2_of hd2) (hp1.symm.trans (hpe.trans hp2))
  rw [heq] at hd1
  exact hser _ _ _ hd1 hd2

end Fp

/-! ## 2. `hdW`: the walk's provided path-record keys are distinct -/

section DW
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K) [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Pb : PubJ8 p}

open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1 (envB envB_eval)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (WT lbl_cols pF walkJ8_bfsRows keys_inj root_mono)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1 (a_lt walkEnvFA_col cellTab roots_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8_width)

/-- The two path-record keys of a walk row, as a function of the side. -/
abbrev keyW (E : Env (ZMod p)) (s : Bool) : Fin 5 → K :=
  if s then ServeH.keyVec5 (K := K) WalkHC.recRH E else ServeH.keyVec5 (K := K) WalkHC.recLH E

theorem keyW_0 (E : Env (ZMod p)) (s : Bool) :
    keyW (K := K) E s 0 = algebraMap (ZMod p) K (E.trace WChip.ridx) := by
  cases s <;> simp [keyW, ServeH.keyVec5, WalkHC.recLH, WalkHC.recRH, cv, CoeffExpr.eval]

theorem keyW_1 (E : Env (ZMod p)) (s : Bool) :
    keyW (K := K) E s 1 =
      algebraMap (ZMod p) K (2 * E.trace WChip.pre + ((if s then 1 else 0 : ℕ) : ZMod p)) := by
  cases s <;> simp [keyW, ServeH.keyVec5, WalkHC.recLH, WalkHC.recRH, cv, CoeffExpr.eval]

/-- **`hdW` of `trace_unique_closed'''`**: on an `AcceptsCanon2` tuple outside the walk event, with the walk's
export keys exported by cell rows (`hX`, for the root bound), the keys `(ridx, 2·pre + side, k, v, 0)` of the walk's
provided path records are pairwise distinct. Rows have distinct `(ridx, pre)` (`keys_inj` on the BFS rows, the
roots strictly increasing by `root_mono`), the side is the parity of `2·pre + side`, and `pre < 2^61` keeps
`2·pre + side` below `p`. -/
theorem hdW_P1 [CharP K p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    {r : RowsJ8} {g : ℕ} (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g)
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (hX : KeysExported (cellTab δ b (Pb := Pb) χ M.pubsC tr) (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr).X) :
    ((ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)).map Prod.fst).Nodup := by
  have hA := h.1.1
  set chals := chalsMJ8 δ χ with hchals
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hq : 2 ^ 63 < ringChar (ZMod p) := two63_lt_ringChar hpG
  have hp : 2 ^ 63 < p := by rw [← hrc]; exact hq
  have hp64 : 64 ≤ ringChar (ZMod p) := by
    have : (64 : ℕ) ≤ 2 ^ 63 := by norm_num
    omega
  have hkp' : Pb.kroots + Pb.nW < ringChar (ZMod p) := by rw [hrc]; exact hkp
  have B := walkJ8_bfsRows δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW _ hA.hsatW hA.hbindW
    hA.hinjW hA.hadjW pF hk hkn hkp' hq hout
  have L := fun j (hj : j < Pb.nW) => lbl_cols δ b Pb tr chals M.pubsW hj
  -- the roots are distinct
  have mono := root_mono δ b hpG hA h.1.2.hW hkn (roots_lt δ b h hkn hX)
  have hroots : ∀ i < Pb.kroots, ∀ j < Pb.kroots,
      ((WT δ b Pb chals M.pubsW tr).lbl (i + 1)).2.ridx.val =
        ((WT δ b Pb chals M.pubsW tr).lbl (j + 1)).2.ridx.val → i = j := by
    intro i hi j hj hr
    rw [(L i (by omega)).2.1, (L j (by omega)).2.1] at hr
    rcases lt_trichotomy i j with hij | hij | hij
    · exact absurd hr (ne_of_lt (mono i j hij hj))
    · exact hij
    · exact absurd hr.symm (ne_of_lt (mono j i hij hi))
  have hinjK := keys_inj B hroots Pb.nW
  -- the prefix bound
  have hpre : ∀ j < Pb.nW, natOf ((envB δ b Pb tr chals M.pubsW j).trace WChip.pre) < 2 ^ 61 := by
    intro j hj
    have hal := a_lt B j hj
    have hpa : ((WT δ b Pb chals M.pubsW tr).lbl (j + 1)).2.pre.val <
        2 ^ (((WT δ b Pb chals M.pubsW tr).lbl (j + 1)).2.len.val + 1) := hal
    rw [(L j hj).2.2.1, (L j hj).2.2.2] at hpa
    have hlen := WalkJ8.walkJ8_len_le_60 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW
      (qW δ b Pb tr chals M.pubsW) pF hp64 hA.hsatW j hj
    rw [walkEnvFA_col δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW _ hj (Or.inl (by decide))
      (by decide)] at hlen
    have hlen' : natOf ((envB δ b Pb tr chals M.pubsW j).trace WChip.len) ≤ 60 := by
      rw [envB_eval δ b Pb tr chals M.pubsW (by decide) hj]; exact hlen
    exact lt_of_lt_of_le hpa (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- equal keys: equal rows and sides
  have hkey : ∀ (j j' : Fin Pb.nW) (s s' : Bool),
      keyW (K := K) (TeleH.wEF b Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) j) s =
        keyW (K := K) (TeleH.wEF b Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) j') s' →
      j = j' ∧ s = s' := by
    intro j j' s s' hkk
    have k0 := congrFun hkk 0
    have k1 := congrFun hkk 1
    rw [keyW_0, keyW_0] at k0
    rw [keyW_1, keyW_1] at k1
    have k0' := (algebraMap (ZMod p) K).injective k0
    have k1' := (algebraMap (ZMod p) K).injective k1
    rw [UniqueProvP1.wEF_trace δ b tr chals M.pubsW j (c := WChip.ridx) (by decide),
      UniqueProvP1.wEF_trace δ b tr chals M.pubsW j' (c := WChip.ridx) (by decide)] at k0'
    rw [UniqueProvP1.wEF_trace δ b tr chals M.pubsW j (c := WChip.pre) (by decide),
      UniqueProvP1.wEF_trace δ b tr chals M.pubsW j' (c := WChip.pre) (by decide)] at k1'
    have c1 := natOf_cast pF ((envB δ b Pb tr chals M.pubsW j).trace WChip.pre)
    have c2 := natOf_cast pF ((envB δ b Pb tr chals M.pubsW j').trace WChip.pre)
    rw [← c1, ← c2] at k1'
    have hb1 := hpre j j.isLt
    have hb2 := hpre j' j'.isLt
    set v1 := natOf ((envB δ b Pb tr chals M.pubsW j).trace WChip.pre)
    set v2 := natOf ((envB δ b Pb tr chals M.pubsW j').trace WChip.pre)
    have k1n : (((2 * v1 + (if s then 1 else 0) : ℕ)) : ZMod p) =
        ((2 * v2 + (if s' then 1 else 0) : ℕ) : ZMod p) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using k1'
    have hs1 : (if s then 1 else 0 : ℕ) ≤ 1 := by split <;> omega
    have hs2 : (if s' then 1 else 0 : ℕ) ≤ 1 := by split <;> omega
    have hnat := CellOrderP1.natCast_inj_lt k1n (by omega) (by omega)
    have hv : v1 = v2 := by omega
    have hss : (if s then 1 else 0 : ℕ) = (if s' then 1 else 0 : ℕ) := by omega
    have hjj : (j : ℕ) = j' := by
      refine hinjK j j.isLt j' j'.isLt j.isLt j'.isLt ?_ ?_
      · rw [(L j j.isLt).2.1, (L j' j'.isLt).2.1, k0']
      · rw [(L j j.isLt).2.2.1, (L j' j'.isLt).2.2.1]; exact hv
    refine ⟨Fin.ext hjj, ?_⟩
    have key : ∀ x y : Bool, ((if x then 1 else 0 : ℕ) = if y then 1 else 0) → x = y := by decide
    exact key s s' hss
  -- the list
  have hmap : (ServeH.walkPProvs b Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW)).map Prod.fst =
      (List.finRange Pb.nW).flatMap fun j =>
        [keyW (K := K) (TeleH.wEF b Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) j) false,
         keyW (K := K) (TeleH.wEF b Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) j) true] := by
    simp only [ServeH.walkPProvs, List.map_flatMap, List.map_cons, List.map_nil, keyW]
    rfl
  rw [hmap, List.nodup_flatMap]
  refine ⟨fun j _ => ?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨fun hm => ?_, List.nodup_singleton _⟩
    rw [List.mem_singleton] at hm
    exact absurd (hkey j j false true hm).2 (by decide)
  · refine (List.nodup_finRange Pb.nW).imp fun {j j'} hne => ?_
    show List.Disjoint _ _
    rw [List.disjoint_left]
    intro x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
    apply hne
    rcases hx with rfl | rfl <;> rcases hx' with h2 | h2 <;> exact (hkey _ _ _ _ h2).1

end DW

/-! ## 3. `trace_unique_closed4`: `trace_unique_closed'''` with `hfp`, `hdW` and `hprov` discharged -/

section Closed4
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1 (dataA trace_unique_good'')
open Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1 (qCell r0M_auxM_closed'' extB_atoms)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1 (envB)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (WT)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1 (cellTab readClosure)
open Nock.Edit.GenX (P1Frag genX SkelX)
open Nock.V1J8.Gen (cellsOfRoots rootsOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueWireP1
open Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8 (fxReqsJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellProvsW)

/-- **`trace_unique_closed4`**: `trace_unique_closed'''` with `hfp` (`hfp_P1`), `hdW`, `hdW'` (`hdW_P1`) and the read
provenance `hprov`, `hprov'` discharged. The provenance comes from a COVER of the reads by the second tuple's
compute path requests (`hcov'`: every read `(σ, a) ∈ Rd` is the first two coordinates of a request of `tr'`), the
path balances (`hbalW_canon`), and the equal request counts of the two tuples (`hreqW_canon`, from the compute
round 0). Remaining: the statement-side hypotheses (run, sizes, root bounds, the E10 data, `Rd` with its size and
bounds) and `hcov'`. -/
theorem trace_unique_closed4 [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
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
    -- the walk
    (hk1 : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (noPath : Prop)
    (hE10 : noPath → (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hE10' : noPath → (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hnW1 : noPath → Pb.nW = 1)
    (Rd : Finset (ℕ × ℕ)) (hszW : ¬ noPath → (readClosure Rd).card = Pb.nW)
    (hRd : ¬ noPath → ∀ s ∈ Rd, s.1 < p ∧ s.2 < p)
    (hcov' : ¬ noPath → ∀ s ∈ Rd, ∃ x ∈ reqsPW δ b Pb c χ M'.m M'.ρ M'.ρS tr', x 0 = (s.1 : K) ∧ x 1 = (s.2 : K)) :
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
  -- the event-side balances (`hbalV_canon`, `hbalH_canon`, `hbalW_canon`)
  have hbalV := hbalV_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h hg
  have hbalH := hbalH_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h hg
  have hbalV' := hbalV_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h' hg'
  have hbalH' := hbalH_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h' hg'
  have hbalW := hbalW_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h hg
  have hbalW' := hbalW_canon δ b R0 L0 skel hs hL hP hnM hreg hr hgN hmax h' hg'
  -- `hfp` and `hdW` (§1, §2)
  have hfp := hfp_P1 δ b h hqM hk hg hl
  have hdW := hdW_P1 δ b h hk1 hkn hkp houtW hl.hXW
  have hdW' := hdW_P1 δ b h' hk1 hkn hkp houtW' hl'.hXW
  -- `hprov`, `hprov'`: the reads are covered by the second tuple's path requests (`hcov'`), and the first tuple's
  -- requests have the same counts (`hreqW`)
  have hbud : (reqsPW δ b Pb c χ M.m M.ρ M.ρS tr).length < p := by
    have := hl.hcount .p; rw [reqsOf_p] at this; exact lt_of_le_of_lt (le_of_eq (List.length_map _).symm) this
  have hbud' : (reqsPW δ b Pb c χ M'.m M'.ρ M'.ρS tr').length < p := by
    have := hl'.hcount .p; rw [reqsOf_p] at this; exact lt_of_le_of_lt (le_of_eq (List.length_map _).symm) this
  obtain ⟨hprov, hprov'⟩ := UniqueProvP1.hprov_pair δ b h h' hk1 hkn hkp houtW houtW' _ _ _ _ hbalW (fun _ hq => hq)
    hbalW' (fun _ hq => hq) hbud hbud' noPath Rd hRd (reqsPW δ b Pb c χ M'.m M'.ρ M'.ρS tr') hreqW (fun _ => rfl) hcov'
  -- the walk, over the non-multiplicity cell table
  have hcellN := hcellN_of_nm δ b (hpG := hpG) h.1.1 h'.1.1 hz hS hS' hnm
  obtain ⟨hr0W, hauxW, hr1W⟩ := walk_closed_nm δ b h h' hk1 hkn hkp houtW houtW' hl.hXW hl'.hXW hcellN hfp
    hl.hHXW hl'.hHXW _ _ _ _ hbalW hdW (fun _ hq => hq) hbalW' hdW' (fun _ hq => hq) hreqW noPath hE10 hE10' hnW1
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

end Closed4

/-! ## 4. The statement side and (A) `trace_unique_good_final` -/

section ReadBound
variable (p : ℕ) [Fact p.Prime]
attribute [local instance] ClaimSizesP1.fact_rc

/-- **The honest read keys are below `p`**: the root serial is `≤ 2^31` (`RdP1_fst_le`, `Rows31`) and the axis is
`< 2^61` (`CanonRunP1.canon_read`). -/
theorem RdP1_lt (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} (hc : P1FragC c) (hok : ClaimSizesP1.P1SizeOK p c) :
    ∀ s ∈ ClaimSizesP1.RdP1 p c, s.1 < p ∧ s.2 < p := by
  intro s hs
  have h1 := UniqueProvP1.RdP1_fst_le p hok s hs
  have hp : 2 ^ 61 < p := CanonRunP1.p61_of hpG
  refine ⟨by omega, ?_⟩
  obtain ⟨t, h, -⟩ := ClaimSizesP1.hrun_of_fragC hc
  rw [ClaimSizesP1.RdP1_of p h] at hs
  unfold ClaimSizesP1.RdOf at hs
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
  have hy1 := (Nock.NockVMROM.Thm54.VclL.GenWalk.mem_pathKind.mp hy).1
  have hy2 := (CanonGenP1.ord8Canon.permR _ _).mem_iff.mp hy1
  have hc' : P1FragC ⟨c.subject, c.formula, c.result⟩ := by cases c; exact hc
  obtain ⟨-, hlt, -⟩ := CanonRunP1.canon_read (Rt := ClaimSizesP1.Rt0) hpG (ClaimSizesP1.runP1_gen h) hc' hy2
  omega

end ReadBound

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1 (dataA)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1 (reqsPW)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1 (szOfClaim P1SizeOK noPathReads RdP1)

variable (p) in
/-- **The read cover of a request list**: every honest read key `(cells.idxOf root, axis) ∈ RdP1 p c` is the first
two coordinates of some request. -/
def ReqCoverP1 (c : P8PublicClaim) (reqs : List (Fin 5 → K)) : Prop :=
  ∀ s ∈ RdP1 p c, ∃ x ∈ reqs, x 0 = (s.1 : K) ∧ x 1 = (s.2 : K)

/-- **(A) `trace_unique_good_final`: trace uniqueness on the P1 fragment at a good coin.** For a claim `c` on the
fragment (`P1FragC`) with the size premise `P1SizeOK` (explicit; open), at the canonical layout
`canonPb hpG (szOfClaim p) c`, two tuples accepted by `AcceptsCanonP1` (`AcceptsCanon2` and the extra pin (E10)) at one coin
`χ` outside every event of the absent-data list `allJ8X (dataA …)` at both traces are equal, provided the second
tuple's compute path requests cover the honest reads (`hcov'`). Every other statement-side hypothesis of
`trace_unique_closed'''` (the run, `hsz`, the root bounds, `noPath`/`hnW1`/E10, `Rd`/`hszW`/its bounds, `hfp`, `hdW`,
`hprov`) is discharged. -/
theorem trace_unique_good_final [CharP K p] [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {Rg : Nock.Jet.Registry}
    (hRg : Rg.Faithful) {c : P8PublicClaim} (hc : P1FragC c) (hok : P1SizeOK p c)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb (canonPb hpG (szOfClaim p) c) skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb (canonPb hpG (szOfClaim p) c) skel hs).nM ≤ 2 ^ 31)
    (hreg : (censusG (canonPb hpG (szOfClaim p) c) c).length ≤ 2 ^ 31)
    (hr : WeightsJ8.RowsLe r EncInjJ8.cornerC) (hgN : g ≤ 2 ^ 31)
    (hmax : (canonPb hpG (szOfClaim p) c).nA + 2 ≤ r.maxlen)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Rg c χ M tr ax r g)
    (h' : AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Rg c χ M' tr' ax' r g)
    (hg : ∀ s ∈ allJ8X (dataA δ b (g := g) (canonPb hpG (szOfClaim p) c) c R0 L0 skel hs hL hP hnM hreg),
      ¬ s.mem tr χ)
    (hg' : ∀ s ∈ allJ8X (dataA δ b (g := g) (canonPb hpG (szOfClaim p) c) c R0 L0 skel hs hL hP hnM hreg),
      ¬ s.mem tr' χ)
    (hcov' : ReqCoverP1 p c (reqsPW δ b (canonPb hpG (szOfClaim p) c) c χ M'.m M'.ρ M'.ρS tr')) :
    (tr, ax, M) = (tr', ax', M') := by
  obtain ⟨t, -, hrunR⟩ := ClaimSizesP1.hrun_of_fragC hc
  have hrun := hrunR Rg
  obtain ⟨hk1, hkn, hkp⟩ := UniqueProvP1.hk_canon p hpG c
  exact trace_unique_closed4 δ b hRg R0 L0 skel hs hL hP hnM hreg hr hgN hmax hqM hk h.1 h'.1 hg hg' hrun
    (ClaimSizesP1.hsz_of p hc hok hrun) hk1 hkn hkp (noPathReads c) h.2 h'.2 (ClaimSizesP1.hnW1_of p hc hok)
    (RdP1 p c) (ClaimSizesP1.hszW_of p hc hok) (fun _ => RdP1_lt p hpG hc hok) (fun _ => hcov')

end Final

/-! ## 5. (B) `canon_eq_final` and (C) `trace_unique_prob_final` -/

section Canon
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {P : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1 (dataA)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1 (reqsPW)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1 (szOfClaim P1SizeOK noPathReads RdP1 runP1 runP1_gen DC Rt0)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.J8Gen
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonGenP1 (j8DataCanon j8DataCanon_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonOrbP1 (trCanon msgCanon)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CanonCompleteP1 (BP1 oP1 axP1)
open Nock.Edit.GenX (SkelX)

/-- The size premise's `Rows31` at the claim's P1 run. -/
abbrev hR31 {c : P8PublicClaim} {t : NTree SkelX} (h : runP1 c = some (t, c.result)) (hok : P1SizeOK p c) :
    ComplJ8Of.Rows31 (DC p h) :=
  ((ClaimSizesP1.P1SizeOK_of p h).mp hok).1

/-- **The honest record** of the claim's P1 run at the canonical datum and the `omegaG` orbit. -/
abbrev BC (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (hok : P1SizeOK p c) :=
  BP1 δ b hpG (runP1_gen h) (hR31 h hok) (K := K) (Rt := Rt0)

/-- **The canonical trace** of the claim at a coin. -/
abbrev trC (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (hok : P1SizeOK p c) (χ : Coins frameJ8 K) : TrJ8 (ZMod p) :=
  trCanon δ b (DC p h) (j8DataCanon_ok p _ Rt0 (runP1_gen h)).cells_pos (j8DataCanon_ok p _ Rt0 (runP1_gen h)).acs_pos
    (oP1 hpG (runP1_gen h) (hR31 h hok)) χ

/-- **The canonical message** of the claim at a coin. -/
abbrev msgC (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (hok : P1SizeOK p c) (χ : Coins frameJ8 K) : MsgJ8' p K δ :=
  msgCanon δ b (DC p h) (j8DataCanon_ok p _ Rt0 (runP1_gen h)).cells_pos (j8DataCanon_ok p _ Rt0 (runP1_gen h)).acs_pos
    (oP1 hpG (runP1_gen h) (hR31 h hok)) χ

/-- **The canonical aux** of the claim at a coin (at the canonical layout's orbit). -/
abbrev axC (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (χ : Coins frameJ8 K) : AuxP1 (ZMod p) :=
  axP1 δ b (DC p h) (j8DataCanon_ok p _ Rt0 (runP1_gen h)).cells_pos (canonPb hpG (szOfClaim p) c).orbit χ

/-- **The canonical triple** `canonOf c χ`. -/
abbrev canonOfP1 (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (hok : P1SizeOK p c) (χ : Coins frameJ8 K) : TripP1 p K δ :=
  (trC δ b hpG h hok χ, axC δ b hpG h χ, msgC δ b hpG h hok χ)

/-- **Completeness at the final statement**: at a good coin of `BC`, the canonical triple is accepted by
`AcceptsCanonP1` at the canonical layout (`CanonSideP1.canon_complete'`, the two `AcceptsCanon2` copies agree, E10
from `noPathReads_iff`). -/
theorem canon_accepts_P1 (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} (hc : P1FragC c) (hok : P1SizeOK p c)
    {t : NTree SkelX} (h : runP1 c = some (t, c.result)) {χ : Coins frameJ8 K} (hχ : (BC δ b hpG h hok).Good χ) :
    AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
      (msgC δ b hpG h hok χ) (trC δ b hpG h hok χ) (axC δ b hpG h χ) (BC δ b hpG h hok).rows (BC δ b hpG h hok).g := by
  have hc' : P1FragC ⟨c.subject, c.formula, c.result⟩ := by cases c; exact hc
  obtain ⟨hfit, hsz⟩ := ClaimSizesP1.szOfClaim_eq p h hok
  have H := (CanonSideP1.canon_complete' δ b (Rt := Rt0) hpG (runP1_gen h) hc' (hR31 h hok)
    ((ClaimSizesP1.P1SizeOK_of p h).mp hok).2 (szOfClaim p) hsz).1 χ hχ
  refine ⟨(acceptsCanon2_iff δ b _ _ _ _ _ _ _ _ _ _ _).mp H.1, fun hno => H.2 ?_⟩
  exact (ClaimSizesP1.noPathReads_iff p _ Rt0 (AsmRowsP1.P1FragC.p1Frag hc) (runP1_gen h)).mp hno

/-- **(B) `canon_eq_final`: every accepted transcript is the canonical one.** On a P1 claim with the size
premise, at the canonical layout and the empty (faithful) registry, at the honest record's rows and budget: a tuple
accepted by `AcceptsCanonP1` at a coin `χ` that is good for the honest record (`hχ`) and outside the absent-data
events at both the tuple's trace (`hg`) and the canonical trace (`hgC`) IS the canonical triple, provided the
canonical trace's compute path requests cover the honest reads (`hcovC`, an honest-side fact). -/
theorem canon_eq_final [CharP K p] [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} (hc : P1FragC c)
    (hok : P1SizeOK p c) {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8
      (BC δ b hpG h hok).rows P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 (BC δ b hpG h hok).rows)
    (skel : List Noun) (hs : skel.length ≤ 3)
    (hL : LayLe (layPb (canonPb hpG (szOfClaim p) c) skel hs) (BC δ b hpG h hok).rows)
    (hP : P = 2 ^ 66) (hnM : (layPb (canonPb hpG (szOfClaim p) c) skel hs).nM ≤ 2 ^ 31)
    (hreg : (censusG (canonPb hpG (szOfClaim p) c) c).length ≤ 2 ^ 31)
    (hr : WeightsJ8.RowsLe (BC δ b hpG h hok).rows EncInjJ8.cornerC) (hgN : (BC δ b hpG h hok).g ≤ 2 ^ 31)
    (hmax : (canonPb hpG (szOfClaim p) c).nA + 2 ≤ (BC δ b hpG h hok).rows.maxlen)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ (BC δ b hpG h hok).rows.maxlen)
    (hk : 2 * fuelChip ≤ (BC δ b hpG h hok).rows.leaves)
    {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {ax : AuxP1 (ZMod p)}
    (hacc : AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
      M tr ax (BC δ b hpG h hok).rows (BC δ b hpG h hok).g)
    (hχ : (BC δ b hpG h hok).Good χ)
    (hg : ∀ s ∈ allJ8X (dataA δ b (g := (BC δ b hpG h hok).g) (canonPb hpG (szOfClaim p) c) c R0 L0 skel hs hL hP
      hnM hreg), ¬ s.mem tr χ)
    (hgC : ∀ s ∈ allJ8X (dataA δ b (g := (BC δ b hpG h hok).g) (canonPb hpG (szOfClaim p) c) c R0 L0 skel hs hL hP
      hnM hreg), ¬ s.mem (trC δ b hpG h hok χ) χ)
    (hcovC : ReqCoverP1 p c (reqsPW δ b (canonPb hpG (szOfClaim p) c) c χ (msgC δ b hpG h hok χ).m
      (msgC δ b hpG h hok χ).ρ (msgC δ b hpG h hok χ).ρS (trC δ b hpG h hok χ))) :
    (tr, ax, M) = canonOfP1 δ b hpG h hok χ :=
  trace_unique_good_final δ b hpG Nock.Jet.VerifiedRegistry.empty.faithful hc hok R0 L0 skel hs hL hP hnM hreg hr
    hgN hmax hqM hk hacc (canon_accepts_P1 δ b hpG hc hok h hχ) hg hgC hcovC

end Canon

section Prob
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {P : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1 (dataA)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueAuxP1 (reqsPW)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.ClaimSizesP1 (szOfClaim P1SizeOK noPathReads RdP1 runP1 runP1_gen DC Rt0)
open Nock.Edit.GenX (SkelX)

/-- **The canonical strategy is staged** (`complJ8_P1`'s `StJ8 B.tr` on the compute, cell, walk and atom columns;
`J = V = 0`). -/
theorem trC_staged (hpG : p = Nock.Atoms.p) {c : P8PublicClaim} (hc : P1FragC c) (hok : P1SizeOK p c)
    {t : NTree SkelX} (h : runP1 c = some (t, c.result)) :
    StJ8 (fun χ : Coins frameJ8 K => trC δ b hpG h hok χ) := by
  have hc' : P1FragC ⟨c.subject, c.formula, c.result⟩ := by cases c; exact hc
  have hB := (CanonCompleteP1.complJ8_P1 δ b (Rt := Rt0) hpG (runP1_gen h) hc' (hR31 h hok)
    ((ClaimSizesP1.P1SizeOK_of p h).mp hok).2 (K := K)).2.2.1
  exact ⟨hB.1, hB.2.1, hB.2.2.1, stagedCols_const _ _ _, hB.2.2.2.2.1, stagedCols_const _ _ _⟩

open Classical in
/-- **`trace_unique_prob_final`:** for any staged prover strategy `Q` (trace, aux, message
at each coin), the probability over the coin that `Q χ` is accepted by `AcceptsCanonP1` and is NOT the canonical
triple is at most twice the event mass `epsilonOf (allJ8X X)` of the absent-data list (once for `Q`'s trace, once for
the canonical trace) plus the honest completeness error `ε_c` of the honest record. Hypotheses as `canon_eq_final`,
with the honest-side cover `hcovC` at every coin. -/
theorem trace_unique_prob_final [CharP K p] [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p) {c : P8PublicClaim}
    (hc : P1FragC c) (hok : P1SizeOK p c) {t : NTree SkelX} (h : runP1 c = some (t, c.result))
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8
      (BC δ b hpG h hok).rows P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 (BC δ b hpG h hok).rows)
    (skel : List Noun) (hs : skel.length ≤ 3)
    (hL : LayLe (layPb (canonPb hpG (szOfClaim p) c) skel hs) (BC δ b hpG h hok).rows)
    (hP : P = 2 ^ 66) (hnM : (layPb (canonPb hpG (szOfClaim p) c) skel hs).nM ≤ 2 ^ 31)
    (hreg : (censusG (canonPb hpG (szOfClaim p) c) c).length ≤ 2 ^ 31)
    (hr : WeightsJ8.RowsLe (BC δ b hpG h hok).rows EncInjJ8.cornerC) (hgN : (BC δ b hpG h hok).g ≤ 2 ^ 31)
    (hmax : (canonPb hpG (szOfClaim p) c).nA + 2 ≤ (BC δ b hpG h hok).rows.maxlen)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ (BC δ b hpG h hok).rows.maxlen)
    (hk : 2 * fuelChip ≤ (BC δ b hpG h hok).rows.leaves)
    (hcovC : ∀ χ : Coins frameJ8 K, ReqCoverP1 p c (reqsPW δ b (canonPb hpG (szOfClaim p) c) c χ
      (msgC δ b hpG h hok χ).m (msgC δ b hpG h hok χ).ρ (msgC δ b hpG h hok χ).ρS (trC δ b hpG h hok χ)))
    (Q : Coins frameJ8 K → TripP1 p K δ) (hQ : StJ8 fun χ => (Q χ).1) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
          (Q χ).2.2 (Q χ).1 (Q χ).2.1 (BC δ b hpG h hok).rows (BC δ b hpG h hok).g ∧
        Q χ ≠ canonOfP1 δ b hpG h hok χ).card : ℚ) / Fintype.card (Coins frameJ8 K) ≤
      2 * epsilonOf (allJ8X (dataA δ b (g := (BC δ b hpG h hok).g) (canonPb hpG (szOfClaim p) c) c R0 L0 skel hs
        hL hP hnM hreg)) + (BC δ b hpG h hok).epsC := by
  have hc' : P1FragC ⟨c.subject, c.formula, c.result⟩ := by cases c; exact hc
  obtain ⟨hfit, hsz⟩ := ClaimSizesP1.szOfClaim_eq p h hok
  set L := allJ8X (dataA δ b (g := (BC δ b hpG h hok).g) (canonPb hpG (szOfClaim p) c) c R0 L0 skel hs hL hP hnM
    hreg) with hLd
  set E1 := unionEvent L (fun χ => (Q χ).1)
  set E2 := unionEvent L (fun χ => trC δ b hpG h hok χ)
  set E3 := Finset.univ.filter fun χ : Coins frameJ8 K => ¬ (BC δ b hpG h hok).Good χ
  have hsub : (Finset.univ.filter fun χ : Coins frameJ8 K =>
        AcceptsCanonP1 δ b hpG (szOfClaim p) (canonPb hpG (szOfClaim p) c) Nock.Jet.VerifiedRegistry.empty.R c χ
          (Q χ).2.2 (Q χ).1 (Q χ).2.1 (BC δ b hpG h hok).rows (BC δ b hpG h hok).g ∧
        Q χ ≠ canonOfP1 δ b hpG h hok χ) ⊆ E1 ∪ E2 ∪ E3 := by
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    by_contra hno
    simp only [Finset.mem_union, E1, E2, E3, unionEvent, Finset.mem_filter, Finset.mem_univ, true_and,
      not_or, not_exists, not_and, not_not] at hno
    obtain ⟨⟨h1, h2⟩, h3⟩ := hno
    exact hχ.2 (canon_eq_final δ b hpG hc hok h R0 L0 skel hs hL hP hnM hreg hr hgN hmax hqM hk hχ.1 h3
      (fun s hs' => h1 s hs') (fun s hs' => h2 s hs') (hcovC χ))
  have hcard := Finset.card_le_card hsub
  have hu := (Finset.card_union_le (E1 ∪ E2) E3).trans (Nat.add_le_add_right (Finset.card_union_le E1 E2) _)
  have hpos : (0 : ℚ) < Fintype.card (Coins frameJ8 K) := by exact_mod_cast Fintype.card_pos
  have b1 := union_prob_le L (fun χ => (Q χ).1) hQ
  have b2 := union_prob_le L (fun χ => trC δ b hpG h hok χ) (trC_staged δ b hpG hc hok h)
  have b3 := (CanonSideP1.canon_complete' δ b (Rt := Rt0) hpG (runP1_gen h) hc' (hR31 h hok)
    ((ClaimSizesP1.P1SizeOK_of p h).mp hok).2 (szOfClaim p) hsz (K := K)).2
  calc _ ≤ ((E1.card + E2.card + E3.card : ℕ) : ℚ) / Fintype.card (Coins frameJ8 K) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard.trans hu) hpos.le
    _ = (E1.card : ℚ) / Fintype.card (Coins frameJ8 K) + (E2.card : ℚ) / Fintype.card (Coins frameJ8 K) +
        (E3.card : ℚ) / Fintype.card (Coins frameJ8 K) := by push_cast; ring
    _ ≤ epsilonOf L + epsilonOf L + (BC δ b hpG h hok).epsC := add_le_add (add_le_add b1 b2) b3
    _ = _ := by ring

end Prob

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.acceptsCanon2_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.decoded_inj_of_sep
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.hfp_P1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.hdW_P1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.trace_unique_closed4
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.RdP1_lt
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.trace_unique_good_final
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.canon_accepts_P1
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.canon_eq_final
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.trC_staged
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.TraceUniqueP1.trace_unique_prob_final
