/-
  Nock/RedTeam/Batch4881Thm54J9APredNC.lean

  **J-9 A predicate witnesses: non-vacuity of `AcceptsJ9A`, the four classic R1 witnesses, and the
  deferred predicate-level attacks**.

  ## 1. Non-vacuity (kernel-checked)
  At Goldilocks (`K = KC`, `δ = deltaF`, `b = powerBasis3`, the empty registry `Rg0`), the J-9 B demo claim
  `c9 = *[[(p+5) 0] [0 2]] = p+5` (big result) is ACCEPTED by `AcceptsJ9A` at the census corner `cornerC9`:
  `nvA_goldilocks` / **`probJ9A_nonvacuous_demo`**.  The witness: the J-9 B input `I9`, its compute row
  lifted to the 137-column twin (`Batch4880.liftX9`, new columns `0`, twin kernel check `Batch4880.i9_X9`), the axis
  and split chips ABSENT (`axOn = spOn = false`, their publics `0`), via `AcceptsJ9A.of_V`.  Every numeric binder of
  `probJ9A_final_clean` holds at the witness (`nvA_in_regime`), and `nvA_hyps_final_clean` conjoins it with that
  theorem's conclusion.
  **NOT covered (labelled):** an inhabitant with the axis chip PRESENT (`axOn = true`).  It needs an honest J-9 A
  trace: an axis-chip chain (≥ 2 rows: `isFirstT·(1−head)`, `isLastT·(1−cl)`, `head·cl` exclude a 1-row table, so a
  present axis chip always consumes limb and path records), the atom table's service multiplicities and the J-8
  walk's path provides for those consumes, twin compute rows in `s0B`/`s10B`/`s10S`, and every LogUp public
  recomputed at the coins.  No J-9 A tracegen exists.  Not discharged either (as at J-9 B):
  `hQ : StJ9A Q` and the instances `[CharP KC p] [CharP 𝕂′ p]` in `nvA_hyps_final_clean`.

  ## 2. The four classic R1 witnesses
  * **Label-equal false claim** (`LinkJ8Q3.cTrue` / `cFalse`, equal J-9 labels `labelJ9_cTrue_cFalse`):
    `cFalse_rejected` — `Pr_χ[∃ M, AcceptsJ9A … cFalse …] < 2^-155` at every in-regime verifier datum.
  * **Padding by `p` copies**: the message carries NO record list (`msgJ9A_ext`: a message is its ten scalar
    fields); the predicate's own lists are verifier-computed (`claimRecsJ9 ≤ 3` records, `inpred_claim_len`;
    `pinCons` / `pinRecsJ8` functions of `Pb`); the bus lists are trace readouts of length `< p` at an accepted trace
    (`bus_len_lt_p`, from `BudLenJ9A.hcountA9`), so `p` copies do not fit.
  * **Post-coin record lists**: `postcoin_lists` — along `StJ9A`, EVERY J-9 A record list (twin compute requests
    `compReqsOf9`, axis limb / path consumes, `TAG_ax` provides, split provides, and the assembled `reqsA` /
    `provsA` / `extA` of all three balances, for every flag value) is `ReadsOnC frameJ8 ∅`.
  * **Out-of-regime inhabitant**: `nAS_out_rejected` (`2^57 ≤ nA + nS`), `axOff_forged_rejected` /
    `spOff_forged_rejected` (flag off, a chip public forged nonzero), `axOn_forces_chip` / `spOn_forces_chip`, `rows_out_rejected` (`nX + n ≥ p` or `2 nS ≥ p`).

  ## 3.
  * wrong limb order (#6): `AxisSoundX9.served_limb_cons` (served limb keys meet `WalkAOK9`) + `NounAx.slot_combL_atom`;
  * leading extra row `(R, 2^{k+1}−1, 0, ·)`: `NounAx.slot_combL_atom` (not an atom axis of the comb), `wrap62`;
  * `TAG_ax` key mismatch consumed by compute: `RowSemChipX9.tagAx9` (the consume's served record fixes
    `V xId = n`, `2^32 ≤ n`, `slot n X = Y`), `SubJ9A.notJ7_of_tag`, `FinalJ9AX9.axTag_entry7`;
  * claim-leaf collision: `LinkJ9A.mb_fp_ne`, `LinkJ9A.hostile_mb_rejected` (J-9 B, unchanged);
  * split record posing as an atom limb (`D (2, nA+s) = none`): `DenJ9A.denOK9_split`, `NounAx.valId_split`,
    `DenJ9A.hden2_valReader`;
  * `s10B` wrong `xId`: `ChipHX9.s10B_row` (route label), `ChipHX9.arithGatesX9_allowlist_xId`, `RowSemChipX9.sem_s10B`;
  * `s10L` / `s10S` served-record checks: `RowSemChipX9.s10S_limb`, `RowSemChipX9.sem_s10S`, `ServedXJ9A.served9`,
    `CompWalkJ9A.hrealA`.
-/
import Nock.RedTeam.Batch4880Thm54J9ACompX9
import Nock.RedTeam.Batch4812Thm54J9bNVFinal
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ProbJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.BudLenJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch4881

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun ClaimMsgVS)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe corner31)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (claimBigs labelJ9 claimRecsJ9 claimRecsJ9_length)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9 permX9)
open Nock.Atoms (lenL)
open Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.RedTeam.Batch4810 Nock.RedTeam.Batch4811 Nock.RedTeam.Batch4812 Nock.RedTeam.Batch4880

noncomputable section

/-! ## 1. Non-vacuity -/

/-- The demo's compute table lifted to the twin. -/
def X9 : ChipIn := liftX9 I9.X

/-- **The J-9 A verifier data** of the demo: the J-8 data of `I9`, both new chips ABSENT (one dummy row each). -/
def PbA (hv : ValidJ8 I9) : PubJ9A Nock.Field.p :=
  { toPubJ8 := mkPb I9 hv, hX := (mkPb I9 hv).h, nX := 1, hnX := Nat.one_pos, nodesX := fun _ => 1,
    orbitX := (mkPb I9 hv).orbit, hS := (mkPb I9 hv).h, nS := 1, hnS := Nat.one_pos, nodesS := fun _ => 1,
    orbitS := (mkPb I9 hv).orbit, axOn := false, spOn := false }

/-- The demo message: J-9 B's, the new chips' publics `0`. -/
def MsgA : MsgJ9A' Nock.Field.p KC deltaF :=
  { toMsgJ8' := I9.M.toMsg, pubsX := fun _ => 0, pubsS := fun _ => 0 }

/-- The demo traces: the lifted compute, J-9 B's memory-side tables, the new chips' traces `0`. -/
def trA : TrJ9A (ZMod Nock.Field.p) :=
  { C := fun j => interpOf X9 j, M := (mkTr I9).M, W := (mkTr I9).W, J := (mkTr I9).J, A := (mkTr I9).A,
    V := (mkTr I9).V, X := fun _ => 0, S := fun _ => 0 }

/-- The twin's J-8 projection is J-9 B's trace. -/
theorem trA_toJ8 : trA.toJ8 = mkTr I9 := by
  show TrJ8.mk _ _ _ _ _ _ = TrJ8.mk _ _ _ _ _ _
  congr 1
  funext j
  show interpOf X9 (permX9 j) = interpOf I9.X j
  unfold interpOf
  congr 1
  funext i
  show liftCols I9.X.cols (permX9 j) i = I9.X.cols j i
  rw [liftCols_perm _ _ j.isLt]

theorem quad_zero : (Quad.mk (algebraMap (ZMod Nock.Field.p) KC deltaF) (0 : KC) 0) = 0 := Quad.mk_zero' _

/-- **`AcceptsJ9A` holds at the demo** (axis / split chips absent), at the census corner `cornerC9`. -/
theorem nvA_goldilocks : ∃ hv : ValidJ8 I9,
    AcceptsJ9A deltaF powerBasis3 (PbA hv) Rg0 c9 (toχ I9.χ) MsgA trA cornerC9 I9.g ∧
      Nock.Jet.HoldsN c9 ∧ claimBigs Nock.Field.p c9 = [2] ∧ Rg0.Faithful ∧
      (PbA hv).axOn = false ∧ (PbA hv).spOn = false := by
  haveI : Fact (ringChar (ZMod Nock.Field.p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
  haveI hcp : CharP KC (ringChar (ZMod Nock.Field.p)) := by
    rw [ZMod.ringChar_zmod_n]; exact charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) KC).injective _
  letI : Algebra (ZMod (ringChar (ZMod Nock.Field.p))) KC := ZMod.algebra KC _
  obtain ⟨hv, hA, hH, hB, hF, -⟩ := nv9_in_regime
  refine ⟨hv, ?_, hH, hB, hF, rfl, rfl⟩
  have hA' : AcceptsJ9V.AcceptsJ9V deltaF powerBasis3 (PbA hv).toPubJ8 Rg0 c9 (toχ I9.χ) MsgA.toMsgJ8'
      trA.toJ8 cornerC9.toRowsJ8 I9.g := by rw [trA_toJ8]; exact hA
  have eX := computeChipX9_iff (tabX9A I9) hv.nX (mkOrbit I9.X hv.oX)
    (qX9 deltaF powerBasis3 (PbA hv) trA (tabX9A I9).chal (tabX9A I9).pub)
    hA.hinjX (adj_of I9.X hv.oX hA.hadjX) rfl (fun j => rfl)
  have hsat := eX.mpr i9_X9
  have hcv := chalVJ8_eq I9.χ
  have hpv := Nock.V1J9.Check9.pubVJ9_eq I9.c I9.M.m I9.M.ρ I9.M.ρS I9.χ
  have hbv := hA.hbudV
  have hn1 : (PbA hv).n = 1 := rfl
  have hnX : (PbA hv).nX = 1 := rfl
  have hnS : (PbA hv).nS = 1 := rfl
  have hnA : (PbA hv).nA = 2 := rfl
  have hcN : cornerC9.N = 2 ^ 31 := rfl
  have hcAX : cornerC9.AX = 2 ^ 31 := rfl
  have hcSP : cornerC9.SP = 2 ^ 31 := rfl
  refine AcceptsJ9A.of_V deltaF powerBasis3 hA' ?_ ?_ ?_ ?_ ?_ ?_ (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (Or.inr ⟨rfl, rfl, rfl⟩) ?_
  · show RAP.SatisfiesWithPreprocessing _ _
    rw [hcv]
    erw [hpv]
    exact hsat
  · show I9.M.toMsg.ρ 4 + Quad.mk _ 0 0 = _
    rw [quad_zero, add_zero]; exact hA.hGp
  · show _ + Quad.mk _ 0 0 = _ + Quad.mk _ 0 0
    rw [quad_zero, add_zero, add_zero]; exact hA.hGS
  · show (PbA hv).nA + (PbA hv).nS < 2 ^ 57
    rw [hnA, hnS]; norm_num
  · have hb' := hA'.hbud
    exact ⟨hb'.x1, hb'.x2, by have := hb'.p1; rw [hnX, hcN]; rw [hn1] at this ⊢; omega, hb'.p2,
      by have := hb'.s1; rw [hnX, hcAX]; omega,
      by have := hb'.s2; rw [hnX, hnS, hcAX, hcSP]; omega⟩
  · exact ⟨hbv.1, hbv.2.1, hbv.2.2.1, hbv.2.2.2, by rw [hnX, hcAX]; norm_num, by rw [hnS, hcSP]; norm_num⟩
  · rw [hnX, hn1, hnS]; norm_num [Nock.Field.p]

/-- **The demo inside `probJ9A_final_clean`'s regime**: every numeric binder of that theorem at `Pb := PbA hv`,
`r := cornerC9`, `g := I9.g`. -/
theorem nvA_in_regime : ∃ hv : ValidJ8 I9,
    AcceptsJ9A deltaF powerBasis3 (PbA hv) Rg0 c9 (toχ I9.χ) MsgA trA cornerC9 I9.g ∧
    Nock.Jet.HoldsN c9 ∧ claimBigs Nock.Field.p c9 = [2] ∧ Rg0.Faithful ∧
    Nock.Field.p = Nock.Atoms.p ∧ Fintype.card KC = Nock.NockVMROM.Thm54.VclL.Events.cK ∧
    RowsLe cornerC9.toRowsJ8 EncInjJ8.cornerC ∧ cornerC9.AX ≤ 2 ^ 31 ∧ cornerC9.SP ≤ 2 ^ 31 ∧
    (∀ x < ringChar (ZMod Nock.Field.p), lenL x ≤ cornerC9.maxlen) ∧
    2 * fuelChip ≤ cornerC9.leaves ∧
    (PbA hv).nA + 2 ≤ cornerC9.maxlen ∧ I9.g ≤ 2 ^ 31 ∧
    (PbA hv).n ≤ cornerC9.N ∧ (PbA hv).nC ≤ cornerC9.D ∧
    (PbA hv).nW ≤ cornerC9.W ∧ (PbA hv).nA ≤ cornerC9.A ∧
    (PbA hv).nV ≤ cornerC9.AW ∧ (PbA hv).nC ≤ 2 ^ 31 ∧
    (censusG (PbA hv).toPubJ8 c9).length + 6 ≤ 2 ^ 31 := by
  obtain ⟨hv, hA, hH, hB, hF, -, -⟩ := nvA_goldilocks
  obtain ⟨hv', -, -, -, -, hpG, hcK, hr, hqM, hk, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg⟩ := nv9_in_regime
  exact ⟨hv, hA, hH, hB, hF, hpG, hcK, hr, le_refl _, le_refl _, hqM, hk, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM,
    hreg⟩

/-- **`probJ9A_nonvacuous_demo`: `AcceptsJ9A` is satisfiable at a big-atom claim, in-regime.** -/
theorem probJ9A_nonvacuous_demo : ∃ (Pb : PubJ9A Nock.Field.p) (χ : Coins frameJ8 KC)
    (M : MsgJ9A' Nock.Field.p KC deltaF) (tr : TrJ9A (ZMod Nock.Field.p)) (g : ℕ),
    AcceptsJ9A deltaF powerBasis3 Pb Rg0 c9 χ M tr cornerC9 g ∧ Nock.Jet.HoldsN c9 ∧
      claimBigs Nock.Field.p c9 = [2] ∧ Pb.axOn = false ∧ Pb.spOn = false ∧
      Pb.nA + 2 ≤ cornerC9.maxlen ∧ g ≤ 2 ^ 31 ∧ Pb.n ≤ cornerC9.N ∧ Pb.nC ≤ cornerC9.D ∧
      Pb.nW ≤ cornerC9.W ∧ Pb.nA ≤ cornerC9.A ∧ Pb.nV ≤ cornerC9.AW ∧ Pb.nC ≤ 2 ^ 31 ∧
      (censusG Pb.toPubJ8 c9).length + 6 ≤ 2 ^ 31 := by
  obtain ⟨hv, hA, hH, hB, -, -, -, -, -, -, -, -, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg⟩ := nvA_in_regime
  exact ⟨PbA hv, toχ I9.χ, MsgA, trA, I9.g, hA, hH, hB, rfl, rfl, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg⟩

open Classical in
/-- **`nvA_hyps_final_clean`**: the witness conjoined with `probJ9A_final_clean`'s conclusion at it.  Still taken as
arguments: `hQ : StJ9A Q` and the two `CharP` instances. -/
theorem nvA_hyps_final_clean [CharP KC Nock.Field.p]
    [CharP (Quad (algebraMap (ZMod Nock.Field.p) KC deltaF)) Nock.Field.p]
    (Q : Coins frameJ8 KC → TrJ9A (ZMod Nock.Field.p)) (hQ : StJ9A Q) :
    ∃ hv : ValidJ8 I9,
      AcceptsJ9A deltaF powerBasis3 (PbA hv) Rg0 c9 (toχ I9.χ) MsgA trA cornerC9 I9.g ∧
      ((Finset.univ.filter fun χ : Coins frameJ8 KC =>
        (∃ M : MsgJ9A' Nock.Field.p KC deltaF, AcceptsJ9A deltaF powerBasis3
          (PbA hv) Rg0 c9 χ M (Q χ) cornerC9 I9.g) ∧ ¬ Nock.Jet.HoldsN c9).card : ℚ) /
        Fintype.card (Coins frameJ8 KC) < 1 / (2 : ℚ) ^ 155 := by
  obtain ⟨hv, hA, hH, hB, hF, hpG, hcK, hr, hAX, hSP, hqM, hk, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg⟩ :=
    nvA_in_regime
  exact ⟨hv, hA, ProbJ9A.probJ9A_final_clean deltaF powerBasis3 (PbA hv) hF c9 Q hQ hpG hcK hr hAX hSP hqM hk hmax
    hg hLC hLM hLW hLA hLV hnM hreg⟩

end

/-! ## 2–3. Label-equal claims, message and list bounds, and chip flags (generic) -/

section Generic
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ9A} {g : ℕ}

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q3 (cTrue cFalse holdsN_cTrue not_holdsN_cFalse)

open Classical in
/-- **A false claim is accepted with probability `< 2^-155`** (`probJ9A_final_clean`
at `¬ HoldsN c`; the filter drops the redundant conjunct). -/
theorem false_claim_rejected [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9A p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (hc : ¬ Nock.Jet.HoldsN c) (Q : Coins frameJ8 K → TrJ9A (ZMod p)) (hQ : StJ9A Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9 : (censusG Pb.toPubJ8 c).length + 6 ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        ∃ M : MsgJ9A' p K δ, AcceptsJ9A δ b Pb Rg c χ M (Q χ) r g).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have h := ProbJ9A.probJ9A_final_clean δ b Pb hRg c Q hQ hpG hcK hr hAX hSP hqM hk hmax hg hLC hLM hLW hLA hLV
    hnM hreg9
  have he : (Finset.univ.filter fun χ : Coins frameJ8 K =>
        ∃ M : MsgJ9A' p K δ, AcceptsJ9A δ b Pb Rg c χ M (Q χ) r g) =
      Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ9A' p K δ, AcceptsJ9A δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c :=
    Finset.filter_congr fun χ _ => ⟨fun h => ⟨h, hc⟩, fun h => h.1⟩
  rw [he]; exact h

/-- **R1 (a), label-equal claims**: `cTrue` (true) and `cFalse` (false) have the SAME J-9 claim label at every
message (all six nouns are cells or equal), so the compute chip's claim publics cannot tell them apart. -/
theorem labelJ9_cTrue_cFalse (m : ClaimMsgVS) : labelJ9 p cTrue m = labelJ9 p cFalse m := rfl

open Classical in
/-- **R1 (a), the label-equal false claim is rejected**: at every in-regime verifier datum,
`Pr_χ[∃ M, AcceptsJ9A … cFalse …] < 2^-155` (contrast J-8's `acceptsJ8_cFalse_of_cTrue`: there acceptance
transferred from `cTrue`). -/
theorem cFalse_rejected [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9A p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9A (ZMod p)) (hQ : StJ9A Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC) (hAX : r.AX ≤ 2 ^ 31) (hSP : r.SP ≤ 2 ^ 31)
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9 : (censusG Pb.toPubJ8 cFalse).length + 6 ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        ∃ M : MsgJ9A' p K δ, AcceptsJ9A δ b Pb Rg cFalse χ M (Q χ) r g).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  false_claim_rejected δ b Pb hRg cFalse not_holdsN_cFalse Q hQ hpG hcK hr hAX hSP hqM hk hmax hg hLC hLM hLW hLA
    hLV hnM hreg9

/-- **R1 (b), no message list to pad**: a J-9 A message is determined by its ten scalar / function fields (no
field of `MsgJ9A'` is a record list). -/
theorem msgJ9A_ext {M M' : MsgJ9A' p K δ} (hm : M.m = M'.m) (hρ : M.ρ = M'.ρ) (hρS : M.ρS = M'.ρS)
    (hC : M.pubsC = M'.pubsC) (hW : M.pubsW = M'.pubsW) (hJ : M.pubsJ = M'.pubsJ) (hA : M.pubsA = M'.pubsA)
    (hV : M.pubsV = M'.pubsV) (hX : M.pubsX = M'.pubsX) (hS : M.pubsS = M'.pubsS) : M = M' := by
  obtain ⟨⟨m, ρ, ρS, pC, pW, pJ, pA, pV⟩, pX, pS⟩ := M
  obtain ⟨⟨m', ρ', ρS', pC', pW', pJ', pA', pV'⟩, pX', pS'⟩ := M'
  simp only at hm hρ hρS hC hW hJ hA hV hX hS
  subst hm hρ hρS hC hW hJ hA hV hX hS
  rfl

/-- **R1 (b), the predicate's own claim list has at most three records** (verifier-computed from the claim and
`M.m`; `pinCons` / `pinRecsJ8` are functions of `Pb`). -/
theorem inpred_claim_len (χ : Coins frameJ8 K) (c : P8PublicClaim) (M : MsgJ9A' p K δ) :
    (claimRecsJ9 δ χ c M.m).length ≤ 3 := claimRecsJ9_length δ χ c M.m

/-- **R1 (b), the bus lists of an accepted trace are shorter than `p`** (`BudLenJ9A.hcountA9` at the predicate's
`hbud` / `hsatX`): appending `p` copies of a record would break the budget. -/
theorem bus_len_lt_p {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} (hacc : AcceptsJ9A δ b Pb Rg c χ M tr r g) (hp : 20 < p)
    (hcap : 3 * (RR49A.rowsB r).N + (RR49A.rowsB r).W + (RR49A.rowsB r).rd < p ∧
      2 * (RR49A.rowsB r).N < p ∧ (RR49A.rowsB r).N + 2 * (RR49A.rowsB r).J + (g + r.N + r.AX) < p)
    (gA : Bool) (bl : ChipHX.Bal) : (RR49A.reqsA δ b gA Pb tr bl).length < p :=
  BudLenJ9A.hcountA9 δ b hp hacc.hbud gA _ _ hacc.hsatX hcap bl

/-- **R1 (c), post-coin lists: none.**  Along any staged prover `StJ9A Q`, every J-9 A record list is
`ReadsOnC frameJ8 ∅` (a function of round-0 trace columns only): the twin compute requests, the four new lists, and
the assembled requests / providers / externals of every balance at every flag value. -/
theorem postcoin_lists (Pb : PubJ9A p) {Q : Coins frameJ8 K → TrJ9A (ZMod p)} (hQ : StJ9A Q) :
    (∀ bl, ReadsOnC frameJ8 ∅ (fun χ => (CompReqsX9.compReqsOf9 (K := K) Pb (Q χ) bl))) ∧
    ReadsOnC frameJ8 ∅ (fun χ => axLimbReqsOf (K := K) b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => axPathReqsOf (K := K) b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => axTagProvsOf (K := K) b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => splitProvsOf (K := K) b Pb (Q χ)) ∧
    (∀ gA gS bl, ReadsOnC frameJ8 ∅ (fun χ => RR49A.reqsA δ b gA Pb (Q χ) bl) ∧
      ReadsOnC frameJ8 ∅ (fun χ => RR49A.provsA b gA gS Pb (Q χ) bl) ∧
      ReadsOnC frameJ8 ∅ (fun χ => RR49A.extA b gA Pb (Q χ) bl)) := by
  obtain ⟨h1, h2, h3, h4⟩ := lists_reads b Pb hQ
  refine ⟨fun bl => CompReqsX9.compReqsOf9_reads Pb hQ bl, h1, h2, h3, h4, fun gA gS bl => ⟨?_, ?_, ?_⟩⟩
  · exact fun χ χ' _ => (RR49A.lists_const δ b gA gS Pb hQ χ χ' bl).1
  · exact fun χ χ' _ => (RR49A.lists_const δ b gA gS Pb hQ χ χ' bl).2
  · intro χ χ' _
    obtain ⟨h, hX, -⟩ := RR49A.agreeA hQ χ χ'
    exact RR49A.extA_congr b h hX gA Pb bl

/-- **R1 (d), out of regime: `2^57 ≤ nA + nS` is rejected** (the id bound is the verifier's `hnAS`). -/
theorem nAS_out_rejected {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} (h : 2 ^ 57 ≤ Pb.nA + Pb.nS) :
    ¬ AcceptsJ9A δ b Pb Rg c χ M tr r g := fun hacc => by have := hacc.hnAS; omega

/-- **R1 (d), out of regime: rows beyond the field** (`nX + n ≥ p` or `2 nS ≥ p`) are rejected. -/
theorem rows_out_rejected {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} (h : p ≤ Pb.nX + Pb.n ∨ p ≤ 2 * Pb.nS) :
    ¬ AcceptsJ9A δ b Pb Rg c χ M tr r g := fun hacc => by
  have := hacc.hlenX; rcases h with h | h <;> omega


/-- **Axis flag off with a forged axis public**: if `Pb.axOn = false` and one of the axis publics `pubAXs`, `pubAXp`
(or its successor) of the message is nonzero, then `AcceptsJ9A` fails. -/
theorem axOff_forged_rejected {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} (hoff : Pb.axOn = false)
    (hf : M.pubsX AxisChipJ9.pubAXs ≠ 0 ∨ M.pubsX (AxisChipJ9.pubAXs + 1) ≠ 0 ∨
      M.pubsX AxisChipJ9.pubAXp ≠ 0 ∨ M.pubsX (AxisChipJ9.pubAXp + 1) ≠ 0) :
    ¬ AcceptsJ9A δ b Pb Rg c χ M tr r g := fun hacc => by
  rcases hacc.hAXk with ⟨hon, -⟩ | ⟨-, h1, h2, h3, h4⟩
  · rw [hoff] at hon; exact Bool.false_ne_true hon
  · rcases hf with h | h | h | h <;> contradiction

/-- **R1 (d), split flag off with a forged split public**: rejected. -/
theorem spOff_forged_rejected {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} (hoff : Pb.spOn = false)
    (hf : M.pubsS SplitChipJ9.pubSPs ≠ 0 ∨ M.pubsS (SplitChipJ9.pubSPs + 1) ≠ 0) :
    ¬ AcceptsJ9A δ b Pb Rg c χ M tr r g := fun hacc => by
  rcases hacc.hSPk with ⟨hon, -⟩ | ⟨-, h1, h2⟩
  · rw [hoff] at hon; exact Bool.false_ne_true hon
  · rcases hf with h | h <;> contradiction

/-- **R1 (d), axis flag on**: the axis chip's RAP (whose terminal gates define `pubAXs` / `pubAXp`) is satisfied and
bound, its nodes injective and `ω`-adjacent, `nX < p` — forged publics are a chip-level rejection. -/
theorem axOn_forces_chip {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} (hacc : AcceptsJ9A δ b Pb Rg c χ M tr r g) (hon : Pb.axOn = true) :
    (AxisChipJ9.axisChipJ9 δ b Pb.hnX Pb.nodesX Pb.orbitX (VerJ8.chalsMJ8 δ χ) M.pubsX).rap.Satisfies
      (qAX δ b Pb tr (VerJ8.chalsMJ8 δ χ) M.pubsX) ∧
    (AxisChipJ9.axisChipJ9 δ b Pb.hnX Pb.nodesX Pb.orbitX (VerJ8.chalsMJ8 δ χ) M.pubsX).BindsPreprocessing
      (qAX δ b Pb tr (VerJ8.chalsMJ8 δ χ) M.pubsX) ∧ Function.Injective Pb.nodesX ∧ Pb.nX < p := by
  rcases hacc.hAXk with ⟨-, hs, hb, hi, -, hn⟩ | ⟨hoff, -⟩
  · exact ⟨hs, hb, hi, hn⟩
  · rw [hon] at hoff; exact absurd hoff (by decide)

/-- **R1 (d), split flag on**: the split chip's RAP is satisfied and bound, `nS < p`. -/
theorem spOn_forces_chip {Pb : PubJ9A p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9A' p K δ} {tr : TrJ9A (ZMod p)} (hacc : AcceptsJ9A δ b Pb Rg c χ M tr r g) (hon : Pb.spOn = true) :
    (SplitChipJ9.splitChipJ9 δ Pb.nA b Pb.hnS Pb.nodesS Pb.orbitS (VerJ8.chalsMJ8 δ χ) M.pubsS).rap.Satisfies
      (qSP δ b Pb tr (VerJ8.chalsMJ8 δ χ) M.pubsS) ∧
    (SplitChipJ9.splitChipJ9 δ Pb.nA b Pb.hnS Pb.nodesS Pb.orbitS (VerJ8.chalsMJ8 δ χ) M.pubsS).BindsPreprocessing
      (qSP δ b Pb tr (VerJ8.chalsMJ8 δ χ) M.pubsS) ∧ Function.Injective Pb.nodesS ∧ Pb.nS < p := by
  rcases hacc.hSPk with ⟨-, hs, hb, hi, -, hn⟩ | ⟨hoff, -⟩
  · exact ⟨hs, hb, hi, hn⟩
  · rw [hon] at hoff; exact absurd hoff (by decide)

end Generic

end Nock.RedTeam.Batch4881

section Axioms
open Nock.RedTeam.Batch4881
#print axioms trA_toJ8
#print axioms nvA_goldilocks
#print axioms nvA_in_regime
#print axioms probJ9A_nonvacuous_demo
#print axioms nvA_hyps_final_clean
#print axioms false_claim_rejected
#print axioms labelJ9_cTrue_cFalse
#print axioms cFalse_rejected
#print axioms msgJ9A_ext
#print axioms inpred_claim_len
#print axioms bus_len_lt_p
#print axioms postcoin_lists
#print axioms nAS_out_rejected
#print axioms rows_out_rejected
#print axioms axOff_forged_rejected
#print axioms spOff_forged_rejected
#print axioms axOn_forces_chip
#print axioms spOn_forces_chip
-- the soundness steps that reject each forged case
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.AxisSoundX9.served_limb_cons
#print axioms Nock.J9A.NounAx.slot_combL_atom
#print axioms Nock.J9A.NounAx.wrap62
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9.tagAx9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.SubJ9A.notJ7_of_tag
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.FinalJ9AX9.axTag_entry7
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9A.mb_fp_ne
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9A.hostile_mb_rejected
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.DenJ9A.denOK9_split
#print axioms Nock.J9A.NounAx.valId_split
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.DenJ9A.hden2_valReader
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.s10B_row
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9.arithGatesX9_allowlist_xId
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9.sem_s10B
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9.s10S_limb
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9.sem_s10S
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ServedXJ9A.served9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.CompWalkJ9A.hrealA
end Axioms
