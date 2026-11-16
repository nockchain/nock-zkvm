/-
  Nock/RedTeam/Batch4922Thm54J9ALPredNC.lean

  **J-9 AL predicate witnesses, part 1: the four classic R1 witnesses at `AcceptsJ9AL`** (the J-9 A
  precedent is `Batch4881Thm54J9APredNC`).  NOT here: the demos and the with-prims non-vacuity
  witness (they wait for the completeness capstone).

  Everything below is KERNEL-CHECKED (std3 `#print axioms` at the end).  Scope labels:
  * "rejected" for a FALSE claim means the soundness bound `probJ9AL_final_clean`: `Pr_χ[(∃ M, AcceptsJ9AL …) ∧ ¬ HoldsN c]
    < 2^-155` at every in-regime verifier datum (`RegimeAL`).  It is a probability bound, as the bound of the
    soundness theorem is; it is not a "no trace exists" statement (a false claim's trace exists at a measure-zero
    set of coins).
  * "rejected" for the structural out-of-regime items is `¬ AcceptsJ9AL …` outright (a projection of the predicate).

  ## The four classic witnesses
  * label-equal false claim: `labelJ9_cTrue_cFalse`, `cFalse_rejected_AL`; and the atom wrap `v` vs `v + p`
    (`labelJ9_wrap_ne`: the labels differ at J-9, kind 0 vs kind 2; `wrap_claim_rejected_AL`).
  * padding by `p` copies: `msgJ9AL_ext` (no record list in a message), `inpred_claim_len`, `pinRecsP_length`
    (prim pin list is verifier-computed, length `|prims|`), `prims_len_le` (`|prims| ≤ nL`), `bus_len_lt_p` (the
    J-9 AL bus lists of an accepted trace are shorter than `p`, via `IOAL.hcountAL`).
  * post-coin record lists: `postcoin_lists_AL` (every J-9 AL list, ALU lists included, is `ReadsOnC frameJ8 ∅`
    along `StJ9AL`), and `aluFp_staged` / `valAL_staged`: the ALU validity list, the one coin-dependent list, is `ReadsOnC frameJ8 (coinsBelow frameJ8 1)` (legal staging).
  * out-of-regime inhabitant: `nAS_out_rejected`, `rows_out_rejected`, `axOff/spOff_forged_rejected`,
    `aluOff_forged_rejected`, `aluOff_prims_rejected`, `aluOn_forces_chip`, `nL_out_rejected`, `nLAL_out_rejected`,
    `primId_out_rejected`, `lenCP_out_rejected`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ProbJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.IOAL
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.CountAL
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch4922

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun ClaimMsgVS)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe c2 c3)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (claimBigs labelJ9 claimRecsJ9 claimRecsJ9_length isBigN claimKH claimHJ9)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
open Nock.Atoms (lenL)

noncomputable section

section Generic
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ9AL} {g : ℕ}

open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q3 (cTrue cFalse holdsN_cTrue not_holdsN_cFalse)

/-- **The in-regime numeric binders of `probJ9AL_final_clean`**, as one proposition (a definition, not a hypothesis of
a `variable` line): every binder of that theorem other than the prover `Q`, `hQ`, `hRg` and the `CharP` instances. -/
structure RegimeAL (K : Type) [Field K] [Algebra (ZMod p) K] [Fintype K] (Pb : PubJ9AL p) (c : P8PublicClaim)
    (r : RowsJ9AL) (g : ℕ) : Prop where
  hpG : p = Nock.Atoms.p
  hcK : Fintype.card K = VclL.Events.cK
  hr : RowsLe r.toRowsJ8 EncInjJ8.cornerC
  hAX : r.AX ≤ 2 ^ 31
  hSP : r.SP ≤ 2 ^ 31
  hAL : r.AL ≤ 2 ^ 31
  hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen
  hk : 2 * fuelChip ≤ r.leaves
  hmax : Pb.nA + 2 ≤ r.maxlen
  hg : g ≤ 2 ^ 31
  hLC : Pb.n ≤ r.N
  hLM : Pb.nC ≤ r.D
  hLW : Pb.nW ≤ r.W
  hLA : Pb.nA ≤ r.A
  hLV : Pb.nV ≤ r.AW
  hnM : Pb.nC ≤ 2 ^ 31
  hreg9P : (censusG Pb.toPubJ8 c ++ censusP Pb).length + 6 ≤ 2 ^ 31

open Classical in
/-- **`false_claim_rejected_AL`: a false claim is accepted with probability below `2^-155`.**
For a faithful jet registry `Rg`, a claim `c` that does not hold (`¬ HoldsN c`), any staged trace family `Q`, and
public data `Pb` in the J-9 AL regime (Goldilocks prime, `|K| = cK`, all table sizes within `2^31` and the public
sizes, length and census bounds), the fraction of coins `χ` for which some message `M` makes `AcceptsJ9AL` accept
is `< 1 / 2^155`.  This is `probJ9AL_final_clean` with the redundant `¬ HoldsN c` conjunct dropped from the
filter. -/
theorem false_claim_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (c : P8PublicClaim) (hc : ¬ Nock.Jet.HoldsN c)
    (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q) (hreg : RegimeAL K Pb c r g) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        ∃ M : MsgJ9AL' p K δ, AcceptsJ9AL δ b Pb Rg c χ M (Q χ) r g).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have h := ProbJ9AL.probJ9AL_final_clean δ b Pb hRg c Q hQ hreg.hpG hreg.hcK hreg.hr hreg.hAX hreg.hSP hreg.hAL
    hreg.hqM hreg.hk hreg.hmax hreg.hg hreg.hLC hreg.hLM hreg.hLW hreg.hLA hreg.hLV hreg.hnM hreg.hreg9P
  have he : (Finset.univ.filter fun χ : Coins frameJ8 K =>
        ∃ M : MsgJ9AL' p K δ, AcceptsJ9AL δ b Pb Rg c χ M (Q χ) r g) =
      Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ9AL' p K δ, AcceptsJ9AL δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c :=
    Finset.filter_congr fun χ _ => ⟨fun h => ⟨h, hc⟩, fun h => h.1⟩
  rw [he]; exact h


/-! ## 1. Classic (a): label-equal false claims -/

/-- **R1 (a), label-equal claims**: `cTrue` (true) and `cFalse` (false) have the SAME J-9 claim label at every
message (all six nouns are cells or equal); the compute chip's claim publics cannot tell them apart. -/
theorem labelJ9_cTrue_cFalse (m : ClaimMsgVS) : labelJ9 p cTrue m = labelJ9 p cFalse m := rfl

open Classical in
/-- **R1 (a), the label-equal false claim is rejected at J-9 AL**: `Pr_χ[∃ M, AcceptsJ9AL … cFalse …] < 2^-155`. -/
theorem cFalse_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb cFalse r g) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        ∃ M : MsgJ9AL' p K δ, AcceptsJ9AL δ b Pb Rg cFalse χ M (Q χ) r g).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  false_claim_rejected_AL δ b Pb hRg cFalse not_holdsN_cFalse Q hQ hreg

/-- The identity formula `[0 1]` returns the subject: a claim with a different result is false. -/
theorem not_holdsN_id (v w : ℕ) (h : v ≠ w) :
    ¬ Nock.Jet.HoldsN ⟨.atom v, .cell (.atom 0) (.atom 1), .atom w⟩ := by
  rintro ⟨fuel, hf⟩
  cases fuel with
  | zero => simp [Nock.evalN] at hf
  | succ n => simp [Nock.evalN, Nock.Noun.slot] at hf; exact h hf

/-- **Atom wrap**: the J-9 labels of the atoms `v < p` (kind 0) and `v + p` (kind 2, big) DIFFER (contrast J-8's
`labelF_atom_wrap`: there `v` and `v + p` had the same label). -/
theorem labelJ9_wrap_ne (hp : 2 < p) (v : ℕ) (hv : v < p) (f e : Noun) (m : ClaimMsgVS) :
    labelJ9 p ⟨.atom v, f, e⟩ m ≠ labelJ9 p ⟨.atom (v + p), f, e⟩ m := by
  intro h
  have h0 := congrArg (fun l => l.head?) h
  simp [labelJ9, claimHJ9, claimNoun, claimKH, Nat.not_le.mpr hv] at h0
  have h1 : ((0 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) := by simpa using h0
  have h2 := (ZMod.natCast_eq_natCast_iff' 0 2 p).mp h1
  rw [Nat.zero_mod, Nat.mod_eq_of_lt hp] at h2
  omega

open Classical in
/-- **`wrap_claim_rejected_AL`: the atom-wrap false claim is accepted with probability below `2^-155`.**
For the claim `*[v [0 1]] = w` with `w ≠ v` (in particular the claim that the atom `v + p` evaluates to `v`,
equal modulo `p`), a faithful registry, any staged trace family `Q` and public data in the J-9 AL regime, the
fraction of coins for which some message makes `AcceptsJ9AL` accept is `< 1 / 2^155`. -/
theorem wrap_claim_rejected_AL [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ9AL p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) (v w : ℕ) (hvw : v ≠ w)
    (Q : Coins frameJ8 K → TrJ9AL (ZMod p)) (hQ : StJ9AL Q)
    (hreg : RegimeAL K Pb ⟨.atom v, .cell (.atom 0) (.atom 1), .atom w⟩ r g) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        ∃ M : MsgJ9AL' p K δ, AcceptsJ9AL δ b Pb Rg ⟨.atom v, .cell (.atom 0) (.atom 1), .atom w⟩ χ M (Q χ) r g).card
        : ℚ) / Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  false_claim_rejected_AL δ b Pb hRg _ (not_holdsN_id v w hvw) Q hQ hreg

/-! ## 2. Classic (b): padding by `p` copies -/

/-- **R1 (b), no message list to pad**: a J-9 AL message is determined by its eleven scalar / function fields (no
field of `MsgJ9AL'` is a record list). -/
theorem msgJ9AL_ext {M M' : MsgJ9AL' p K δ} (hm : M.m = M'.m) (hρ : M.ρ = M'.ρ) (hρS : M.ρS = M'.ρS)
    (hC : M.pubsC = M'.pubsC) (hW : M.pubsW = M'.pubsW) (hJ : M.pubsJ = M'.pubsJ) (hA : M.pubsA = M'.pubsA)
    (hV : M.pubsV = M'.pubsV) (hX : M.pubsX = M'.pubsX) (hS : M.pubsS = M'.pubsS) (hL : M.pubsL = M'.pubsL) :
    M = M' := by
  obtain ⟨⟨⟨m, ρ, ρS, pC, pW, pJ, pA, pV⟩, pX, pS⟩, pL⟩ := M
  obtain ⟨⟨⟨m', ρ', ρS', pC', pW', pJ', pA', pV'⟩, pX', pS'⟩, pL'⟩ := M'
  simp only at hm hρ hρS hC hW hJ hA hV hX hS hL
  subst hm hρ hρS hC hW hJ hA hV hX hS hL
  rfl

/-- **R1 (b), the predicate's own claim list has at most three records** (verifier-computed from the claim and
`M.m`). -/
theorem inpred_claim_len (χ : Coins frameJ8 K) (c : P8PublicClaim) (M : MsgJ9AL' p K δ) :
    (claimRecsJ9 δ χ c M.m).length ≤ 3 := claimRecsJ9_length δ χ c M.m

/-- **R1 (b), the primitive pin list has exactly `|prims|` records** (verifier-computed from `Pb.prims`). -/
theorem pinRecsP_length (Pb : PubJ9AL p) (χ : Coins frameJ8 K) : (pinRecsP δ Pb χ).length = Pb.prims.length := by
  simp [pinRecsP]

/-- **R1 (b), the primitive census list has exactly `|prims|` nouns.** -/
theorem censusP_length (Pb : PubJ9AL p) : (censusP Pb).length = Pb.prims.length := by
  simp [censusP]

/-- **R1 (b), the verifier's primitive-pin lists in the service balance have exactly `|prims|` records each.** -/
theorem pinRgP_pinOpP_length (Pb : PubJ9AL p) :
    (pinRgP (p := p) (K := K) Pb).length = Pb.prims.length ∧ (pinOpP (p := p) (K := K) Pb).length = Pb.prims.length := by
  simp [pinRgP, pinOpP]

/-- **R1 (b), an accepted predicate has `|prims| ≤ nL`** (ALU rows: one `preg` row per primitive; ALU absent: no
primitive). -/
theorem prims_len_le {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) :
    Pb.prims.length ≤ Pb.nL := by
  rcases hacc.hALk with ⟨-, -, -, -, -, -, hpre⟩ | ⟨-, hp, -⟩
  · exact hpre.1
  · rw [hp]; exact Nat.zero_le _

/-- **R1 (b), the bus lists of an accepted trace are shorter than `p`**: all three J-9 AL request lists
(`RR49AL.reqsAL`, ALU lists included) at an accepted trace, from `IOAL.hcountAL` (budget + the ALU counts
`CountAL.aluSL_pins_le`); appending `p` copies of a record would break the budget. -/
theorem bus_len_lt_p {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g)
    (hpG : p = Nock.Atoms.p)
    (hcap : 3 * (RR49AL.rowsBL r).N + (RR49AL.rowsBL r).W + (RR49AL.rowsBL r).rd < p ∧
      2 * (RR49AL.rowsBL r).N < p ∧ (RR49AL.rowsBL r).N + 2 * (RR49AL.rowsBL r).J + RR49AL.gL r g < p)
    (bl : ChipHX.Bal) : (RR49AL.reqsAL δ b Pb tr bl).length < p := by
  have hp : 20 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hSL : (RR49AL.aluSL δ b Pb tr).length + 2 * Pb.prims.length ≤ 2 * Pb.nL := by
    subst hpG; exact CountAL.aluSL_pins_le δ b hacc.hALk
  exact IOAL.hcountAL δ b hp hacc.hbud hSL _ _ hacc.hsatX hcap bl

/-! ## 3. Classic (c): post-coin record lists -/

/-- **R1 (c), post-coin lists: none.**  Along any staged prover `StJ9AL Q`, every J-9 AL record list is
`ReadsOnC frameJ8 ∅` (a function of round-0 trace columns only): the assembled requests / providers of every
balance, and the four ALU lists (`aluRegReqsOf` = `hdr` consumes, `aluRegProvsOf` = `preg` provides, `aluJetProvsOf`,
`aluExportReqsOf`).  The one other ALU list, the validity list `aluFpL`, is NOT coin-free; it is closed by
`aluFp_staged` / `valAL_staged` below (legal staging: reads only `z` and rounds `<= 1`). -/
theorem postcoin_lists_AL (Pb : PubJ9AL p) {Q : Coins frameJ8 K → TrJ9AL (ZMod p)} (hQ : StJ9AL Q) :
    (∀ bl, ReadsOnC frameJ8 ∅ (fun χ => RR49AL.reqsAL δ b Pb (Q χ) bl) ∧
      ReadsOnC frameJ8 ∅ (fun χ => RR49AL.provsAL δ b Pb (Q χ) bl)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => aluRegReqsOf δ b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => aluRegProvsOf δ b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => aluJetProvsOf δ b Pb (Q χ)) ∧
    ReadsOnC frameJ8 ∅ (fun χ => aluExportReqsOf δ b Pb (Q χ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := lists_readsL δ b Pb hQ
  exact ⟨fun bl => ⟨fun χ χ' _ => (RR49AL.listsAL_const δ b Pb hQ χ χ' bl).1,
    fun χ χ' _ => (RR49AL.listsAL_const δ b Pb hQ χ χ' bl).2⟩, h1, h2, h3, h4⟩

/-- **The ALU validity list is legally staged (closes the one non-`ReadsOnC ∅` list).**
(a) The coin is the fingerprint seed `z = (χ c2, χ c3)`, read through `chalsALJ8` leaves `37 / 38`
(`AluSZChipJ9.chalsALJ8_zAt`); both are sampled after round 0 (`frameJ8_y_round0`: `sampledAfter c2 = c3 = 0`).
The records are `[z, 0, L, 0, sv]` (`AluSZChipJ9.valKey`) on rows with `aV ≠ 0`; they read the round-1 column `L` and
the round-0 columns `aV`, `sv`.
(b) LEGAL STAGING, not a free choice: `StJ9AL Q` includes `StagedCols frameJ8 crAL (L of Q)`, which forces column `j`
of round `r` to be a function of the coins sampled after rounds `< r` (`TraceJ8.staged_eq`); `L` (round 1) is a
function of `z` and round-0 data, committed after `z`, as in the J-9 A atom validity reads.  Hence the list is
`ReadsOnC frameJ8 (coinsBelow frameJ8 1)`: it depends only on coins sampled after round 0 (those below round 1) and
the staged columns of rounds `<= 1`; the prover cannot pick it after seeing anything later.
(Proof: `RR49AL.aluFp_congr`, as in `RR49AL.valAL_reads`.) -/
theorem aluFp_staged [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K] (Pb : PubJ9AL p) {Q : Coins frameJ8 K → TrJ9AL (ZMod p)} (hQ : StJ9AL Q) :
    ReadsOnC frameJ8 (coinsBelow frameJ8 1) (fun χ => RR49AL.aluFpL δ b Pb (Q χ) χ) := by
  intro χ χ' hχ
  have hm : ∀ i : Fin frameJ8.n, frameJ8.sampledAfter i = 0 → i ∈ coinsBelow frameJ8 1 := fun i hi => by
    simp only [coinsBelow, Finset.mem_filter, Finset.mem_univ, true_and, hi]; norm_num
  unfold RR49AL.aluFpL
  split_ifs
  · refine RR49AL.aluFp_congr δ b Pb _ _ _ _
      (fun j hj => TraceJ8.staged_eq hQ.2 (r := 1) (TraceJ8.below_of_mem hχ) j hj) ?_ ?_
    · rw [AluSZChipJ9.chalsALJ8_of_lt δ χ (by norm_num), AluSZChipJ9.chalsALJ8_of_lt δ χ' (by norm_num)]
      simp only [ChalsAZJ8.chalsAJ8Z, if_pos rfl]; exact hχ c2 (hm _ (by decide))
    · rw [AluSZChipJ9.chalsALJ8_of_lt δ χ (by norm_num), AluSZChipJ9.chalsALJ8_of_lt δ χ' (by norm_num)]
      simp only [ChalsAZJ8.chalsAJ8Z, if_neg (show (38 : ℕ) ≠ 37 by decide), if_pos rfl]
      exact hχ c3 (hm _ (by decide))
  · rfl

/-- The whole validity readout of the ALU-bearing cell balance (#2's consumers and providers) reads below round 1. -/
theorem valAL_staged [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K] (Pb : PubJ9AL p) (c : P8PublicClaim) {Q : Coins frameJ8 K → TrJ9AL (ZMod p)} (hQ : StJ9AL Q) :
    ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ =>
      (RR49AL.valReqsAL δ b Pb c (Q χ) χ, RealVJ8.valProvsJ8 δ b Pb.toPubJ8 (Q χ).toJ8 χ) :=
  RR49AL.valAL_reads δ b Pb c Q hQ

/-- `z = (c2, c3)` is sampled after round 0. -/
theorem z_round0 : frameJ8.sampledAfter c2 = 0 ∧ frameJ8.sampledAfter c3 = 0 :=
  ⟨(frameJ8_y_round0).2.2.1, (frameJ8_y_round0).2.2.2⟩

/-! ## 4. Classic (d): out-of-regime inhabitants -/

/-- **R1 (d), `2^57 ≤ nA + nS` is rejected.** -/
theorem nAS_out_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (h : 2 ^ 57 ≤ Pb.nA + Pb.nS) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by have := hacc.hnAS; omega

/-- **R1 (d), rows beyond the field** (`nX + n ≥ p` or `2 nS ≥ p`) are rejected. -/
theorem rows_out_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (h : p ≤ Pb.nX + Pb.n ∨ p ≤ 2 * Pb.nS) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by
  have := hacc.hlenX; rcases h with h | h <;> omega

/-- **R1 (d), ALU rows beyond the field** (`nL + n ≥ p`) or beyond the row budget (`AL < nL`) are rejected. -/
theorem nL_out_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (h : p ≤ Pb.nL + Pb.n ∨ r.AL < Pb.nL) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by
  have := hacc.hlenL; rcases h with h | h <;> omega

/-- **R1 (d), a primitive id or pin index beyond the field is rejected.** -/
theorem primId_out_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {q : ℕ × Nock.Jet.Prim.PrimOp} (hq : q ∈ Pb.prims)
    (h : p ≤ q.1 ∨ p ≤ Pb.idxP q.1) : ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by
  have := hacc.hlenL.2.2 q hq; rcases h with h | h <;> omega

/-- **R1 (d), the cell-validity consumer count beyond the field** is rejected. -/
theorem lenCP_out_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)}
    (h : p ≤ 3 + Pb.regs.length + Pb.prims.length + Pb.nL + 2 * Pb.nC) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by have := hacc.hlenCP; omega

/-- **R1 (d), axis flag off with a forged axis public**: rejected. -/
theorem axOff_forged_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (hoff : Pb.axOn = false)
    (hf : M.pubsX AxisChipJ9.pubAXs ≠ 0 ∨ M.pubsX (AxisChipJ9.pubAXs + 1) ≠ 0 ∨
      M.pubsX AxisChipJ9.pubAXp ≠ 0 ∨ M.pubsX (AxisChipJ9.pubAXp + 1) ≠ 0) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by
  rcases hacc.hAXk with ⟨hon, -⟩ | ⟨-, h1, h2, h3, h4⟩
  · rw [hoff] at hon; exact Bool.false_ne_true hon
  · rcases hf with h | h | h | h <;> contradiction

/-- **R1 (d), split flag off with a forged split public**: rejected. -/
theorem spOff_forged_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (hoff : Pb.spOn = false)
    (hf : M.pubsS SplitChipJ9.pubSPs ≠ 0 ∨ M.pubsS (SplitChipJ9.pubSPs + 1) ≠ 0) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by
  rcases hacc.hSPk with ⟨hon, -⟩ | ⟨-, h1, h2⟩
  · rw [hoff] at hon; exact Bool.false_ne_true hon
  · rcases hf with h | h <;> contradiction

/-- **R1 (d), ALU flag off with a forged ALU public** (`pubALv`, `pubALs`, `pubALx`, either half): rejected
(R8: absence = flag + zero publics). -/
theorem aluOff_forged_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (hoff : Pb.aluOn = false)
    (hf : M.pubsL AluSZChipJ9.pubALv ≠ 0 ∨ M.pubsL (AluSZChipJ9.pubALv + 1) ≠ 0 ∨
      M.pubsL AluSZChipJ9.pubALs ≠ 0 ∨ M.pubsL (AluSZChipJ9.pubALs + 1) ≠ 0 ∨
      M.pubsL AluSZChipJ9.pubALx ≠ 0 ∨ M.pubsL (AluSZChipJ9.pubALx + 1) ≠ 0) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by
  rcases hacc.hALk with ⟨hon, -⟩ | ⟨-, -, h1, h2, h3, h4, h5, h6⟩
  · rw [hoff] at hon; exact Bool.false_ne_true hon
  · rcases hf with h | h | h | h | h | h <;> contradiction

/-- **R1 (d), ALU flag off with a non-empty primitive table**: rejected (primitives need the ALU). -/
theorem aluOff_prims_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (hoff : Pb.aluOn = false) (hne : Pb.prims ≠ []) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by
  rcases hacc.hALk with ⟨hon, -⟩ | ⟨-, hp, -⟩
  · rw [hoff] at hon; exact Bool.false_ne_true hon
  · exact hne hp

/-- **R1 (d), ALU flag on**: the ALU's RAP (whose terminal gates define the three ALU publics) is satisfied and bound,
its nodes injective and `ω`-adjacent, `nL < p`, and the `preg` layout holds: forged publics or a forged table are a
chip-level rejection (Batch4920 and the ALU lemmas). -/
theorem aluOn_forces_chip {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (hacc : AcceptsJ9AL δ b Pb Rg c χ M tr r g) (hon : Pb.aluOn = true) :
    (AluSZChipJ9.aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL (AluSZChipJ9.chalsALJ8 δ χ) M.pubsL Pb.preL).rap.Satisfies
      (RealIOJ9AL.qAL δ b Pb tr (AluSZChipJ9.chalsALJ8 δ χ) M.pubsL) ∧
    (AluSZChipJ9.aluSZChipJ9 δ b Pb.hnL Pb.nodesL Pb.orbitL (AluSZChipJ9.chalsALJ8 δ χ) M.pubsL Pb.preL).BindsPreprocessing
      (RealIOJ9AL.qAL δ b Pb tr (AluSZChipJ9.chalsALJ8 δ χ) M.pubsL) ∧ Function.Injective Pb.nodesL ∧ Pb.nL < p ∧
    PregOK Pb.nodesL Pb.prims Pb.preL := by
  rcases hacc.hALk with ⟨-, hs, hb, hi, -, hn, hpre⟩ | ⟨hoff, -⟩
  · exact ⟨hs, hb, hi, hn, hpre⟩
  · rw [hon] at hoff; exact absurd hoff (by decide)

/-- **R1 (d), an unregistered primitive** (`Rg id ≠ some (primSpec op)`) is rejected (`hPrim`). -/
theorem primUnreg_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {q : ℕ × Nock.Jet.Prim.PrimOp} (hq : q ∈ Pb.prims)
    (h : Rg q.1 ≠ some (Nock.Jet.Prim.primSpec q.2)) : ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g :=
  fun hacc => h (hacc.hPrim q hq)

/-- **R1 (d), a primitive id that is also a J-chip registry id** is rejected (`hdisjP`). -/
theorem primId_in_regs_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {q : ℕ × Nock.Jet.Prim.PrimOp} (hq : q ∈ Pb.prims)
    (h : q.1 ∈ Pb.regs) : ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => hacc.hdisjP q hq h

/-- **R1 (d), a repeated primitive id** is rejected (`hndP`). -/
theorem primId_dup_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (h : ¬ (Pb.prims.map Prod.fst).Nodup) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => h hacc.hndP

/-- **R1 (d), a primitive with rank `(0, 0)`** (the atom-root rank) is rejected (`hrkP`). -/
theorem primRank_zero_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {q : ℕ × Nock.Jet.Prim.PrimOp} (hq : q ∈ Pb.prims)
    (h : Pb.rkP q.1 = (0, 0)) : ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => hacc.hrkP q hq h

/-- **R1 (d), a claim handle for a cell / big claim noun with index `≥ p`** is rejected (`hclI`). -/
theorem claimIdx_out_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (k : Fin 3)
    (hk : FrameVS.isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) (h : p ≤ (M.m k).1) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by have := hacc.hclI k hk; omega

/-- **R1 (d), a claim whose formula is an atom** is rejected (`hcellF`). -/
theorem formulaAtom_rejected {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} (h : FrameVS.isCellN c.formula = false) :
    ¬ AcceptsJ9AL δ b Pb Rg c χ M tr r g := fun hacc => by have := hacc.hcellF; rw [h] at this; exact Bool.false_ne_true this

end Generic

end

end Nock.RedTeam.Batch4922

section Axioms
open Nock.RedTeam.Batch4922
#print axioms false_claim_rejected_AL
#print axioms labelJ9_cTrue_cFalse
#print axioms cFalse_rejected_AL
#print axioms not_holdsN_id
#print axioms labelJ9_wrap_ne
#print axioms wrap_claim_rejected_AL
#print axioms msgJ9AL_ext
#print axioms inpred_claim_len
#print axioms pinRecsP_length
#print axioms censusP_length
#print axioms pinRgP_pinOpP_length
#print axioms prims_len_le
#print axioms bus_len_lt_p
#print axioms postcoin_lists_AL
#print axioms aluFp_staged
#print axioms valAL_staged
#print axioms z_round0
#print axioms nAS_out_rejected
#print axioms rows_out_rejected
#print axioms nL_out_rejected
#print axioms primId_out_rejected
#print axioms lenCP_out_rejected
#print axioms axOff_forged_rejected
#print axioms spOff_forged_rejected
#print axioms aluOff_forged_rejected
#print axioms aluOff_prims_rejected
#print axioms aluOn_forces_chip
#print axioms primUnreg_rejected
#print axioms primId_in_regs_rejected
#print axioms primId_dup_rejected
#print axioms primRank_zero_rejected
#print axioms claimIdx_out_rejected
#print axioms formulaAtom_rejected
end Axioms
