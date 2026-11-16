/-
  Nock/NockVMROM/Thm54/VclL/Handle/FrameVS.lean

  Additive: no existing module changed.

  * `frameVS` — `frameVCL`'s eleven coins plus four `𝕂` coins sampled after round 0:
    `γH = χ₁₁`, `ρH = χ₁₂` (the handle LogUp: export AND path records, keys are round-0 handle
    columns) and `αW = χ₁₃`, `γW = χ₁₄` (the compute walk over handle labels, also round-0 data).
  * the memory challenge vector `chalsVS` (`chalsVCL` at the first eleven coins, leaves `33 / 34`
    = `CellH.hGam / hRho` the handle coins); the compute challenge vector `chalVH` (`𝔽`-limbs
    `0..2 γH`, `3..5 ρH`, `6..8 αW`, `9..11 γW`, as `ChipH.chalGammaL / chalRhoL / chalAlphaW /
    chalGammaW` read them through `mixedCompile … col0Id`).
  * accumulators `nAcc = 5` at `Kio = Quad δ`: `0` validity, `1` fingerprint export, `2`
    fingerprint path (DEAD at VS, terminal free, see below), `3` handle export, `4` handle path.
    The compute publics (`pubVH`): `0..5` the claim handles `(kind, value)` of `s f e`
    (`claimHandle`, serials from `Msg0 = ClaimMsgVS`); `6..8 IC = αW`; `9..11` the walk seed
    `αW · RLC^{γW}(claim label)`; `12..14` walk terminal `0`; `15..17 / 18..20 = Re ρ₃ / Re ρ₄`.
  * the memory chips: table `0` `cellChipH` (pub `4 = Re ρ₃ + yH`), table `1` `walkChipH`
    (pub `4 = yH`, `5 = Re ρ₄`), `Msg2 = Quad × 𝕂` (fingerprint export terminal `y`, handle
    export terminal `yH`), each gated by `GoodM` / `GoodW` (else rejecting).
  * tables: compute `tableVS` (width `70`, rounds `0 | 1` at `43`); memory `shapeVS`
    (`232 / 151`, rounds of the twins: the appended base columns `mh` / `kL vL kR vR` in round
    `0`, the appended `𝕂`-roles in round `2`).
  * **`compCoreVS` / `memCoreVS`** — the `CompCore` / `MemCore` at those chips; the summand lists are
    PARAMETERS (`sumC`, `sumM`): F4/F5 fix them with the soundness proof.
  * `acceptsVS_facts` — `AcceptsG` at the cores unpacks to `GoodCVS ∧ computeChipVCLH` acceptance
    and `GoodM ∧ cellChipH` / `GoodW ∧ walkChipH` acceptance at the fixed coin/public maps.

  So VS leaves accumulator `2`'s
  terminal FREE (`ρ₂` unchecked); no VS soundness step reads the fingerprint path lookup.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipH
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimH
import Nock.NockVMROM.Thm54.VclL.Handle.WalkH
import Nock.NockVMROM.Thm54.VclL.Chips.MemFamilyVCLW
import Nock.NockVMROM.Thm54.P8Core.SVFrameG.StandaloneG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The frame and the coin maps -/

/-- **The VS frame**: `frameVCL`'s eleven coins, then `γH ρH αW γW`, all four sampled after round 0. -/
def frameVS : CoinFrame where
  n := 15
  sampledAfter := fun i => ![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0] i

def cGamH : Fin frameVS.n := ⟨11, by decide⟩
def cRhoH : Fin frameVS.n := ⟨12, by decide⟩
def cAlphaW : Fin frameVS.n := ⟨13, by decide⟩
def cGamW : Fin frameVS.n := ⟨14, by decide⟩

/-- The four VS coins are sampled after round 0 (handle keys and walk labels are round-0 data). -/
theorem frameVS_new_round0 :
    frameVS.sampledAfter cGamH = 0 ∧ frameVS.sampledAfter cRhoH = 0 ∧
      frameVS.sampledAfter cAlphaW = 0 ∧ frameVS.sampledAfter cGamW = 0 := by decide

theorem lt_frameVS (i : Fin frameVCL.n) : (i : ℕ) < frameVS.n := by
  have := i.isLt; change (i : ℕ) < 11 at this; change (i : ℕ) < 15; omega

/-- The first eleven coins (`frameVCL`'s). -/
def toVCL {K : Type} (χ : Coins frameVS K) : Coins frameVCL K := fun i => χ ⟨i, lt_frameVS i⟩

/-- `frameVCL`'s round map is `frameVS`'s on the first eleven coins. -/
theorem toVCL_sampled (i : Fin frameVCL.n) :
    frameVCL.sampledAfter i = frameVS.sampledAfter ⟨i, lt_frameVS i⟩ := by
  fin_cases i <;> rfl

section Coins
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **The memory challenge vector at VS**: leaves `33 / 34` (`CellH.hGam / hRho`, read by both
twins' handle gates) are `γH / ρH`; every other leaf is `chalsVCL` at the first eleven coins. -/
def chalsVS [Fintype K] (χ : Coins frameVS K) (j : ℕ) : K :=
  if j = CellH.hGam then χ cGamH else if j = CellH.hRho then χ cRhoH
  else chalsVCL δF (toVCL χ) j

theorem chalsVS_hGam [Fintype K] (χ : Coins frameVS K) : chalsVS δF χ CellH.hGam = χ cGamH := by
  simp [chalsVS]

theorem chalsVS_hRho [Fintype K] (χ : Coins frameVS K) : chalsVS δF χ CellH.hRho = χ cRhoH := by
  simp [chalsVS, CellH.hGam, CellH.hRho]

theorem chalsVS_old [Fintype K] (χ : Coins frameVS K) (j : ℕ) (hj : j < 33) :
    chalsVS δF χ j = chalsVCL δF (toVCL χ) j := by
  have h1 : j ≠ CellH.hGam := by simp only [CellH.hGam]; omega
  have h2 : j ≠ CellH.hRho := by simp only [CellH.hRho]; omega
  simp [chalsVS, h1, h2]

/-- The compute's `𝕂` coins by slot: `0 γH`, `1 ρH`, `2 αW`, `3 γW`. -/
def coinH (χ : Coins frameVS K) (q : ℕ) : K :=
  if q = 0 then χ cGamH else if q = 1 then χ cRhoH else if q = 2 then χ cAlphaW else χ cGamW

/-- **The compute challenge vector** (`𝔽`-limbs `3q.. 3q+2` of `coinH q`, `q < 4`). -/
def chalVH (b : Basis (Fin 3) F K) (χ : Coins frameVS K) : ℕ → F :=
  fun j => if j < 12 then coord b (coinH χ (j / 3)) ⟨j % 3, Nat.mod_lt j (by decide)⟩ else 0

end Coins

/-! ## 2. The claim message, the claim handles and the verifier-computed claim records -/

/-- **The compute's pre-coin message**: per claim noun (`s f e`) the serial `idx` and the rank halves
`(hi, lo)` of its validity key (read only when the noun is a cell). -/
abbrev ClaimMsgVS := Fin 3 → ℕ × ℕ × ℕ

def claimNoun (c : P8PublicClaim) : Fin 3 → Noun := ![c.subject, c.formula, c.result]

/-- The public handle of claim noun `k` (`claimHandle`: atom ↦ `(0, v)`, cell ↦ `(1, idx)`). -/
def claimH (c : P8PublicClaim) (m : ClaimMsgVS) (k : Fin 3) : VHandle :=
  claimHandle (claimNoun c k) (m k).1

def isCellN : Noun → Bool
  | .atom _ => false
  | .cell _ _ => true

section Claim
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- A handle's two `𝔽` entries `(kind, value)`. -/
def hvalF (h : VHandle) : List F := [if h.1 then 1 else 0, (h.2 : F)]

/-- The claim label `[s.k, s.v, f.k, f.v, e.k, e.v]` (`ChipH.labelCols`' order). -/
def labelF (c : P8PublicClaim) (m : ClaimMsgVS) : List F :=
  hvalF (claimH c m 0) ++ hvalF (claimH c m 1) ++ hvalF (claimH c m 2)

theorem labelF_length (c : P8PublicClaim) (m : ClaimMsgVS) : (labelF (F := F) c m).length = 6 := by
  simp [labelF, hvalF]

/-- **The compute walk seed** `αW · Σ_k γW^k · lift(label_k)` (the root counted as the first child of
a virtual parent, `ChipH.walkGates`' first-row form). -/
def seedVS (c : P8PublicClaim) (m : ClaimMsgVS) (χ : Coins frameVS K) : K :=
  χ cAlphaW * ((labelF (F := F) c m).zipIdx.map fun p => χ cGamW ^ p.2 * algebraMap F K p.1).sum

/-- **The compute publics at VS.** -/
def pubVH (b : Basis (Fin 3) F K) (c : P8PublicClaim) (m : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) : ℕ → F :=
  fun j =>
    if j < 6 then (labelF c m).getD j 0
    else if h1 : j < 9 then coord b (χ cAlphaW) ⟨j - 6, by omega⟩
    else if h2 : j < 12 then coord b (seedVS (F := F) c m χ) ⟨j - 9, by omega⟩
    else if j < 15 then 0
    else if h4 : j < 18 then coord b (Quad.re _ (ρ 3)) ⟨j - 15, by omega⟩
    else if h5 : j < 21 then coord b (Quad.re _ (ρ 4)) ⟨j - 18, by omega⟩
    else 0

/-- The fingerprint seed `z′ = (χ₂, χ₃)` (as `chalsVCL`'s leaves `2 / 3`). -/
def zVS (χ : Coins frameVS K) : Quad (algebraMap F K δF) := Quad.mk _ (χ ⟨2, by decide⟩) (χ ⟨3, by decide⟩)

/-- **The claim validity record** of noun `x` with message `(idx, hi, lo)`:
`(enc z x).size,.dyck,.leaf, lo + hi·√δ, idx` (`Cell.vKeyP`'s order, `QE.mk2 lo hi`), the
fingerprint computed by the VERIFIER from the public claim. -/
def claimKey (χ : Coins frameVS K) (x : Noun) (r : ℕ × ℕ × ℕ) : Fin 5 → Quad (algebraMap F K δF) :=
  let e := GlobalCarryRecognizer.enc (zVS δF χ) x
  ![e.size, e.dyck, e.leaf,
    Quad.mk _ (algebraMap F K (r.2.2 : F)) (algebraMap F K (r.2.1 : F)),
    Quad.mk _ (algebraMap F K (r.1 : F)) 0]

/-- The validity IO coins `γ′ = χ₄ + χ₆√δ`, `ρ′ = χ₅ + χ₇√δ` (`chalsVCL_ok`). -/
def ioCoinsVS (χ : Coins frameVS K) : FiniteIO.IOCoins (Quad (algebraMap F K δF)) :=
  ⟨Quad.mk _ (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩), Quad.mk _ (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)⟩

/-- **The claim validity records**: one per CELL claim noun. -/
def claimRecs (c : P8PublicClaim) (m : ClaimMsgVS) (χ : Coins frameVS K) :
    List (Fin 5 → Quad (algebraMap F K δF)) :=
  ((List.finRange 3).filter fun k => isCellN (claimNoun c k)).map fun k =>
    claimKey δF χ (claimNoun c k) (m k)

/-- **The verifier-computed claim validity sum** `Σ (ρ′ + RLC^{γ′} r)⁻¹` over `claimRecs`. -/
def claimValSum (c : P8PublicClaim) (m : ClaimMsgVS) (χ : Coins frameVS K) : Quad (algebraMap F K δF) :=
  ((claimRecs δF c m χ).map fun r => (FiniteIO.compress (ioCoinsVS δF χ) r)⁻¹).sum

theorem claimRecs_length_le (c : P8PublicClaim) (m : ClaimMsgVS) (χ : Coins frameVS K) :
    (claimRecs δF c m χ).length ≤ 3 := by
  unfold claimRecs
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

end Claim

/-! ## 3. Tables and the memory shape -/

/-- The VS compute table: width `70`, the `43` handle/control columns in round 0, the rest in 1. -/
def tableVS (hC : ℕ) : TableSpec where
  width := ChipH.widthH
  colRound := fun j => if (j : ℕ) < ChipH.round0W then 0 else 1
  height := hC

/-- The cell twin's rounds: base `0..129` (`mh` at `129`) in 0, the shifted round-1 roles in 1, the
shifted round-2 roles and the appended `invH accH` in 2. -/
def colRoundCH (j : Fin 232) : ℕ := if (j : ℕ) < 130 then 0 else if (j : ℕ) < 184 then 1 else 2

/-- The walk twin's rounds: base `0..24` (`kL vL kR vR` at `21..24`) in 0, then `+4`-shifted. -/
def colRoundWH (j : Fin 151) : ℕ := if (j : ℕ) < 25 then 0 else if (j : ℕ) < 97 then 1 else 2

/-- `colRoundCH` is `Cell.colRoundT` on the unshifted base columns and through the `+1` shift. -/
theorem colRoundCH_shift (j : Fin 225) :
    colRoundCH ⟨shiftCol 129 130 j, by unfold shiftCol; split_ifs <;> omega⟩ =
      Chips.Cell.colRoundT (Fin.cast Chips.Cell.widthT_eq.symm j) := by
  rcases j with ⟨j, hj⟩
  have h0 : Chips.Cell.b0CountS = 129 := by decide
  have h1 : Chips.Cell.b1Count = 54 := by decide
  simp only [colRoundCH, shiftCol, Chips.Cell.colRoundT, Fin.val_cast, h0, h1]
  split_ifs <;> omega

/-- `colRoundWH` is `colRoundW` through the `+4` shift. -/
theorem colRoundWH_shift (j : Fin 132) :
    colRoundWH ⟨shiftCol 21 25 j, by unfold shiftCol; split_ifs <;> omega⟩ = colRoundW j := by
  rcases j with ⟨j, hj⟩
  simp only [colRoundWH, shiftCol, colRoundW]
  split_ifs <;> omega

/-- **The VS memory shape**: cell twin `232`, walk twin `151`. -/
abbrev shapeVS (hT hP : ℕ) : MemShape := shapeVCL hT hP 232 151 colRoundCH colRoundWH

def tCS (hT hP : ℕ) : Fin (shapeVS hT hP).k := ⟨0, by show 0 < 2; omega⟩
def tWS (hT hP : ℕ) : Fin (shapeVS hT hP).k := ⟨1, by show 1 < 2; omega⟩

/-! ## 4. The rejecting chip at any width -/

section Reject
variable {F : Type} [Field F]

/-- One gate `1 = 0`, one round, width `w`. -/
def rejectRAPW (w : ℕ) {h : ℕ} (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 1
    wRAP := ![w]
    w := w
    w_eq := by simp
    h := h
    d := 4
    s := 1
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun _ => coeffToMv (fun _ => (0 : F)) (fun _ => 0) (CoeffExpr.const 1)
    C_vars := fun _ => coeffToMv_vars _ _ _
    C_deg := fun _ => (coeffToMv_totalDegree_le _ _ _).trans (by simp [CoeffExpr.degree])
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- The rejecting chip (no preprocessing). -/
def rejectChipW (w : ℕ) {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) :
    FixedPreprocessingRAP F where
  rap := rejectRAPW w orbit (rowNodeSet nodes)
  rounds_pos := Nat.one_pos
  fixedCount := 0
  preprocessingIndex := ⟨Fin.elim0, fun a => Fin.elim0 a⟩
  preprocessing := Fin.elim0

theorem rejectChipW_w (w : ℕ) {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) :
    (rejectChipW w nodes orbit).rap.w = w := rfl

/-- **The rejecting chip accepts nothing.** -/
theorem rejectChipW_unsat (w : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) (P : Fin (rejectChipW w nodes orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (rejectChipW w nodes orbit) P) : False := by
  have hx : nodes ⟨0, hn⟩ ∈ rowNodeSet nodes := by simp [rowNodeSet]
  have hz := hP.1 ⟨0, by change 0 < 1; norm_num⟩ _ hx
  have key : ((rejectChipW w nodes orbit).rap.compose P ⟨0, by change 0 < 1; norm_num⟩).eval
      (nodes ⟨0, hn⟩) = (CoeffExpr.const (1 : F)).eval
        (Reify.envOfTrace P orbit.ω (nodes ⟨0, hn⟩) (fun _ => 0) (fun _ => 0)) := by
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω (nodes ⟨0, hn⟩) (fun _ => 0) (fun _ => 0) _
  rw [key] at hz
  simp [CoeffExpr.eval] at hz

/-- Acceptance of a chip equal to a rejecting one is impossible (transport through the cast). -/
theorem not_sat_of_eq_reject (w : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (orbit : StrictOrbitDomain F 3 h) {W : ℕ} (c : FixedPreprocessingRAP F)
    (hc : c = rejectChipW w nodes orbit) (hw : c.rap.w = W) (Q : Fin W → F[X])
    (hP : RAP.SatisfiesWithPreprocessing c (fun j => Q (Fin.cast hw j))) : False := by
  subst hc
  exact rejectChipW_unsat w hn nodes orbit _ hP

end Reject

/-! ## 5. The chips -/

section Chips
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr : ℕ) {hC : ℕ}

/-- **What the VS compute chip enforces.** -/
def GoodCVS {S : MemShape} (V : VerifierData F K hC S) (x : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) : Prop :=
  V.AdjacentC ∧ Function.Injective V.computeNodes ∧ 2 ^ 63 < ringChar F ∧
    ρ 0 = claimValSum δF V.claim x χ ∧ ρ 1 = 0 ∧ Quad.im _ (ρ 3) = 0 ∧ Quad.im _ (ρ 4) = 0

open Classical in
/-- **The VS compute chip**: `computeChipVCLH` at `chalVH` / `pubVH` under `GoodCVS`, else rejecting. -/
def chipCVS {S : MemShape} (V : VerifierData F K hC S) (x : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) : FixedPreprocessingRAP F :=
  if GoodCVS δF V x ρ χ then
    ChipH.computeChipVCLH V.hN V.computeNodes V.basis (chalVH V.basis χ)
      (pubVH δF V.basis V.claim x ρ χ) V.orbitC
  else rejectChipW ChipH.widthH V.computeNodes V.orbitC

theorem chipCVS_width {S : MemShape} (V : VerifierData F K hC S) (x : ClaimMsgVS)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (χ : Coins frameVS K) :
    (chipCVS δF V x ρ χ).rap.w = (tableVS hC).width := by
  unfold chipCVS; split_ifs <;> rfl

/-- The three fingerprint accumulators of `ρ` (as `pubsC` / `pubsP` read them). -/
def rho3 (ρ : Fin 5 → Quad (algebraMap F K δF)) : Fin 3 → Quad (algebraMap F K δF) :=
  fun a => ρ ⟨a, by omega⟩

/-- The cell twin's publics: `pubsC` at the fingerprint terminals, `4 = Re ρ₃ + yH`. -/
def pubsCH (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (yH : K) (i : ℕ) : K :=
  if i = CellH.pubH then Quad.re _ (ρ 3) + yH else pubsC δF (rho3 δF ρ) y i

/-- The walk twin's publics: `pubsP` at the fingerprint terminals, `4 = yH`, `5 = Re ρ₄`. -/
def pubsWH (ρ : Fin 5 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (yH : K) (i : ℕ) : K :=
  if i = WalkHC.pubX then yH else if i = WalkHC.pubP then Quad.re _ (ρ 4)
  else pubsP δF (rho3 δF ρ) y i

open Classical in
/-- **The VS memory chips**: table `0` the cell twin under `GoodM`, table `1` the walk twin under
`GoodW kr`, each rejecting otherwise. -/
def chipMVS (V : VerifierData F K hC (shapeVS hT hP)) (t : Fin (shapeVS hT hP).k)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (yy : Quad (algebraMap F K δF) × K)
    (χ : Coins frameVS K) : FixedPreprocessingRAP F :=
  if (t : ℕ) = 0 then
    (if GoodM V t then
      cellChipH δF V.basis (V.hM t) (V.memNodes t) (V.orbitM t) (chalsVS δF χ) (pubsCH δF ρ yy.1 yy.2)
    else rejectChipW 232 (V.memNodes t) (V.orbitM t))
  else
    (if GoodW V t kr then
      walkChipH δF kr V.basis (V.hM t) (V.memNodes t) (V.orbitM t) (chalsVS δF χ) (pubsWH δF ρ yy.1 yy.2)
    else rejectChipW 151 (V.memNodes t) (V.orbitM t))

theorem chipMVS_width (V : VerifierData F K hC (shapeVS hT hP)) (t : Fin (shapeVS hT hP).k)
    (ρ : Fin 5 → Quad (algebraMap F K δF)) (yy : Quad (algebraMap F K δF) × K) (χ : Coins frameVS K) :
    (chipMVS δF hT hP kr V t ρ yy χ).rap.w = ((shapeVS hT hP).table t).width := by
  unfold chipMVS
  split_ifs with ht h1 h2
  · rw [cellChipH_width]; change _ = (if (t : ℕ) = 0 then (⟨232, colRoundCH, hT⟩ : TableSpec) else ⟨151, colRoundWH, hP⟩).width; rw [if_pos ht]
  · rw [rejectChipW_w]; change _ = (if (t : ℕ) = 0 then (⟨232, colRoundCH, hT⟩ : TableSpec) else ⟨151, colRoundWH, hP⟩).width; rw [if_pos ht]
  · rw [walkChipH_width]; change _ = (if (t : ℕ) = 0 then (⟨232, colRoundCH, hT⟩ : TableSpec) else ⟨151, colRoundWH, hP⟩).width; rw [if_neg ht]
  · rw [rejectChipW_w]; change _ = (if (t : ℕ) = 0 then (⟨232, colRoundCH, hT⟩ : TableSpec) else ⟨151, colRoundWH, hP⟩).width; rw [if_neg ht]

end Chips

/-! ## 6. The cores -/

section Cores
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)

/-- The summand-list type of the VS instance. -/
abbrev SummandsVS := List (BadSummand frameVS K (Traces F (tableVS hC) (shapeVS hT hP))
  (TracesStaged frameVS (tableVS hC) (shapeVS hT hP)))

def reqBoundVS (V : VerifierData F K hC (shapeVS hT hP)) : Fin 5 → ℕ :=
  ![3, 0, 0, 3 * V.N, 2 * V.N]

def internalBoundVS (V : VerifierData F K hC (shapeVS hT hP)) : Fin 5 → ℕ :=
  ![2 * V.memRows (tCS hT hP), V.memRows (tWS hT hP), 0, V.memRows (tWS hT hP), 0]

/-- **`CompCoreVS`**: the compute core at `chipCVS` (`70`); summands a parameter. -/
def compCoreVS (sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC) :
    CompCore F K (Quad (algebraMap F K δF)) frameVS hC (shapeVS hT hP) (tableVS hC) 5 where
  Msg0 := ClaimMsgVS
  chip := fun V x ρ χ => chipCVS δF V x ρ χ
  chip_width := fun V x ρ χ => chipCVS_width δF V x ρ χ
  reqBound := reqBoundVS hT hP hC
  summands := sumC
  Honest := Empty
  honestV := fun H => H.elim
  honestQ := fun H => H.elim
  honestReq := fun H => H.elim
  honest_staged := fun H => H.elim
  honestBad := fun H => H.elim

/-- **`MemCoreVS`**: the memory core at `chipMVS` (`232 / 151`); summands a parameter. -/
def memCoreVS (sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC) :
    MemCore F K (Quad (algebraMap F K δF)) frameVS hC (shapeVS hT hP) (tableVS hC) 5 where
  Msg0 := Unit
  Msg2 := Quad (algebraMap F K δF) × K
  chip := fun V t _ ρ yy χ => chipMVS δF hT hP kr V t ρ yy χ
  chip_width := fun V t _ ρ yy χ => chipMVS_width δF hT hP kr V t ρ yy χ
  internalBound := internalBoundVS hT hP hC
  summands := sumM
  Honest := Empty
  honestV := fun H => H.elim
  honestQ := fun H => H.elim
  honestReq := fun H => H.elim
  honest_staged := fun H => H.elim
  honestBad := fun H => H.elim

/-! ## 7. Acceptance at the cores unpacks to the three chips -/

variable {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

theorem sat_cast_eq {c c' : FixedPreprocessingRAP F} (hcc : c = c') {W : ℕ} (hw : c.rap.w = W)
    (hw' : c'.rap.w = W) (Q : Fin W → F[X])
    (hP : RAP.SatisfiesWithPreprocessing c (fun j => Q (Fin.cast hw j))) :
    RAP.SatisfiesWithPreprocessing c' (fun j => Q (Fin.cast hw' j)) := by
  subst hcc; exact hP

/-- **The compute side of `AcceptsG` at VS**: `GoodCVS` and `computeChipVCLH` acceptance. -/
theorem compute_facts (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ) :
    GoodCVS δF V msg.msg0C (msg.requests χ) χ ∧
      RAP.SatisfiesWithPreprocessing
        (ChipH.computeChipVCLH V.hN V.computeNodes V.basis (chalVH V.basis χ)
          (pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC)
        (fun j => msg.Qc χ (Fin.cast rfl j)) := by
  classical
  have hc := h.compute
  change RAP.SatisfiesWithPreprocessing (chipCVS δF V msg.msg0C (msg.requests χ) χ)
    (fun j => msg.Qc χ (Fin.cast (chipCVS_width δF V msg.msg0C (msg.requests χ) χ) j)) at hc
  by_cases hg : GoodCVS δF V msg.msg0C (msg.requests χ) χ
  · refine ⟨hg, ?_⟩
    have he : chipCVS δF V msg.msg0C (msg.requests χ) χ =
        ChipH.computeChipVCLH V.hN V.computeNodes V.basis (chalVH V.basis χ)
          (pubVH δF V.basis V.claim msg.msg0C (msg.requests χ) χ) V.orbitC := by
      unfold chipCVS; exact if_pos hg
    exact sat_cast_eq he _ rfl _ hc
  · exfalso
    have he : chipCVS δF V msg.msg0C (msg.requests χ) χ =
        rejectChipW ChipH.widthH V.computeNodes V.orbitC := by
      unfold chipCVS; exact if_neg hg
    exact not_sat_of_eq_reject _ V.hN V.computeNodes V.orbitC _ he _ _ hc

/-- **The cell side of `AcceptsG` at VS**: `GoodM` and `cellChipH` acceptance. -/
theorem cell_facts (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ) :
    GoodM V (tCS hT hP) ∧ ∃ hw : (cellChipH δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
        (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVS hT hP).table (tCS hT hP)).width,
      RAP.SatisfiesWithPreprocessing
        (cellChipH δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
          (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2))
        (fun j => msg.Qm χ (tCS hT hP) (Fin.cast hw j)) := by
  classical
  have hc := h.memory (tCS hT hP)
  change RAP.SatisfiesWithPreprocessing (chipMVS δF hT hP kr V (tCS hT hP) (msg.requests χ) (msg.msg2M χ) χ)
    (fun j => msg.Qm χ (tCS hT hP)
      (Fin.cast (chipMVS_width δF hT hP kr V (tCS hT hP) (msg.requests χ) (msg.msg2M χ) χ) j)) at hc
  have h0 : ((tCS hT hP : Fin (shapeVS hT hP).k) : ℕ) = 0 := rfl
  by_cases hg : GoodM V (tCS hT hP)
  · have he : chipMVS δF hT hP kr V (tCS hT hP) (msg.requests χ) (msg.msg2M χ) χ =
        cellChipH δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
          (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) := by
      unfold chipMVS; rw [if_pos h0, if_pos hg]
    have hw : (cellChipH δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
        (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVS hT hP).table (tCS hT hP)).width := by
      rw [← he]; exact chipMVS_width δF hT hP kr V _ _ _ _
    exact ⟨hg, hw, sat_cast_eq he _ hw _ hc⟩
  · exfalso
    have he : chipMVS δF hT hP kr V (tCS hT hP) (msg.requests χ) (msg.msg2M χ) χ =
        rejectChipW 232 (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) := by
      unfold chipMVS; rw [if_pos h0, if_neg hg]
    exact not_sat_of_eq_reject _ (V.hM _) (V.memNodes _) (V.orbitM _) _ he _ _ hc

/-- **The walk side of `AcceptsG` at VS**: `GoodW kr` and `walkChipH` acceptance. -/
theorem walk_facts (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ) :
    GoodW V (tWS hT hP) kr ∧ ∃ hw : (walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
        (V.orbitM (tWS hT hP)) (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVS hT hP).table (tWS hT hP)).width,
      RAP.SatisfiesWithPreprocessing
        (walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
          (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2))
        (fun j => msg.Qm χ (tWS hT hP) (Fin.cast hw j)) := by
  classical
  have hc := h.memory (tWS hT hP)
  change RAP.SatisfiesWithPreprocessing (chipMVS δF hT hP kr V (tWS hT hP) (msg.requests χ) (msg.msg2M χ) χ)
    (fun j => msg.Qm χ (tWS hT hP)
      (Fin.cast (chipMVS_width δF hT hP kr V (tWS hT hP) (msg.requests χ) (msg.msg2M χ) χ) j)) at hc
  have h1 : ¬ ((tWS hT hP : Fin (shapeVS hT hP).k) : ℕ) = 0 := Nat.one_ne_zero
  by_cases hg : GoodW V (tWS hT hP) kr
  · have he : chipMVS δF hT hP kr V (tWS hT hP) (msg.requests χ) (msg.msg2M χ) χ =
        walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP))
          (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) := by
      unfold chipMVS; rw [if_neg h1, if_pos hg]
    have hw : (walkChipH δF kr V.basis (V.hM (tWS hT hP)) (V.memNodes (tWS hT hP))
        (V.orbitM (tWS hT hP)) (chalsVS δF χ) (pubsWH δF (msg.requests χ) (msg.msg2M χ).1
          (msg.msg2M χ).2)).rap.w = ((shapeVS hT hP).table (tWS hT hP)).width := by
      rw [← he]; exact chipMVS_width δF hT hP kr V _ _ _ _
    exact ⟨hg, hw, sat_cast_eq he _ hw _ hc⟩
  · exfalso
    have he : chipMVS δF hT hP kr V (tWS hT hP) (msg.requests χ) (msg.msg2M χ) χ =
        rejectChipW 151 (V.memNodes (tWS hT hP)) (V.orbitM (tWS hT hP)) := by
      unfold chipMVS; rw [if_neg h1, if_neg hg]
    exact not_sat_of_eq_reject _ (V.hM _) (V.memNodes _) (V.orbitM _) _ he _ _ hc

end Cores

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
