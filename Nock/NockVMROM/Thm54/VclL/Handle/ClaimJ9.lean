/-
  Nock/NockVMROM/Thm54/VclL/Handle/ClaimJ9.lean

* `claimKH`: the J-9 public handle of a claim noun, as a wire handle `(kind, value)`: a small atom `v < p` is
    `(0, v)`, a BIG atom `v ≥ p` is `(2, idx)` (the atom table's serial, the third arm), a cell is `(1, idx)`.
  * `labelJ9`, `seedJ9`, **`pubVJ9`**: `pubVJ8` with the claim label (publics `0..5`) and the walk seed (`9..11`) taken
    from `claimKH`; every other public (`6..8`, `≥ 12`) is `pubVJ8`'s (`pubVJ9_hi`, `pubVJ9_six`).
  * **`claimRecsJ9`** `:= claimRecsJ8 ++` one record `claimVec (E (atom n)) idx 0 0` per big claim leaf (rank `(0, 0)`,
    bound to the atom table's g5 terminal through `hsumC'`).
  * **`censusGJ9`** `:= censusG ++` the claim's big atoms.
  * `rhoX_congr12`: the balance terminals read publics `≥ 12` only.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9

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
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe realize40 realizeJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (rowsMJ8 rowsB0 crA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (censusList2)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z atomTZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_of_ne chalsAJ8Z_ok chalsAJ8Z_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4 (RR4 LL4 hHXV_ofZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun claimH isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crA crM crW crC staged_eq below_of_mem shV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (mbXs claimCells claimRecsJ8 pinRecsJ8 rkC MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_zAt)
open Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP (toMsgJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 St40 sum40 fpx_out v4 v5 v6 v7)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (extY_below shV_round)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8

noncomputable section

/-! ## 1. The J-9 claim handle -/

/-- A big atom (`≥ p`). -/
def isBigN (p : ℕ) : Noun → Bool
  | .atom v => decide (p ≤ v)
  | .cell _ _ => false

/-- **The J-9 public handle of a claim noun** (wire form `(kind, value)`): small atom `(0, v)`, big atom `(2, idx)`,
cell `(1, idx)`; `idx` is the prover's serial. -/
def claimKH (p : ℕ) (x : Noun) (idx : ℕ) : ℕ × ℕ :=
  match x with
  | .atom v => if p ≤ v then (2, idx) else (0, v)
  | .cell _ _ => (1, idx)

/-- The J-9 handle of claim noun `k`. -/
def claimHJ9 (p : ℕ) (c : P8PublicClaim) (m : ClaimMsgVS) (k : Fin 3) : ℕ × ℕ := claimKH p (claimNoun c k) (m k).1

/-- **The J-9 claim label** `[s.k, s.v, f.k, f.v, e.k, e.v]` as field elements. -/
def labelJ9 (p : ℕ) (c : P8PublicClaim) (m : ClaimMsgVS) : List (ZMod p) :=
  [((claimHJ9 p c m 0).1 : ZMod p), ((claimHJ9 p c m 0).2 : ZMod p),
   ((claimHJ9 p c m 1).1 : ZMod p), ((claimHJ9 p c m 1).2 : ZMod p),
   ((claimHJ9 p c m 2).1 : ZMod p), ((claimHJ9 p c m 2).2 : ZMod p)]

theorem labelJ9_length (p : ℕ) (c : P8PublicClaim) (m : ClaimMsgVS) : (labelJ9 p c m).length = 6 := rfl

/-- The claim's big-atom positions. -/
def claimBigs (p : ℕ) (c : P8PublicClaim) : List (Fin 3) := (List.finRange 3).filter fun k => isBigN p (claimNoun c k)

theorem isCellN_isBigN {p : ℕ} {x : Noun} (h : isCellN x = true) : isBigN p x = false := by
  cases x with
  | atom v => simp [isCellN] at h
  | cell a b => rfl

theorem length_filter_disj {α : Type} (P Q : α → Bool) (h : ∀ x, ¬ (P x = true ∧ Q x = true)) :
    ∀ l : List α, (l.filter P).length + (l.filter Q).length ≤ l.length
  | [] => by simp
  | a :: l => by
    have ih := length_filter_disj P Q h l
    have ha := h a
    cases hP : P a <;> cases hQ : Q a <;> simp_all <;> omega

/-- **Cells and big atoms are at most three positions**: the claim records stay `≤ 3`. -/
theorem claimCells_bigs_length (p : ℕ) (c : P8PublicClaim) :
    (claimCells c).length + (claimBigs p c).length ≤ 3 := by
  have := length_filter_disj (fun k : Fin 3 => isCellN (claimNoun c k)) (fun k => isBigN p (claimNoun c k))
    (fun x hx => by rw [isCellN_isBigN hx.1] at hx; exact Bool.false_ne_true hx.2) (List.finRange 3)
  simpa [claimCells, claimBigs] using this


/-- **Conservativity**: with no big claim atom the J-9 label is the J-8 label. -/
theorem labelJ9_eq_labelF {p : ℕ} [Fact p.Prime] (c : P8PublicClaim) (m : ClaimMsgVS)
    (h : ∀ k, isBigN p (claimNoun c k) = false) : labelJ9 p c m = labelF (F := ZMod p) c m := by
  have hk : ∀ k, ((claimHJ9 p c m k).1 : ZMod p) = (if (claimH c m k).1 then 1 else 0) ∧
      ((claimHJ9 p c m k).2 : ZMod p) = ((claimH c m k).2 : ZMod p) := by
    intro k
    have hb := h k
    unfold claimHJ9 claimH
    cases hx : claimNoun c k with
    | atom v =>
      rw [hx] at hb
      have hv : ¬ p ≤ v := by simpa [isBigN] using hb
      simp [claimKH, claimHandle, hv]
    | cell a b' => simp [claimKH, claimHandle]
  simp only [labelJ9, labelF, hvalF, (hk 0).1, (hk 0).2, (hk 1).1, (hk 1).2, (hk 2).1, (hk 2).2,
    List.cons_append, List.nil_append]

section Pubs
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The J-9 compute walk seed** `αW · Σ_k γW^k · lift(labelJ9_k)` (`seedVS` at `labelJ9`). -/
def seedJ9 (c : P8PublicClaim) (m : ClaimMsgVS) (χ : Coins frameVS K) : K :=
  χ cAlphaW * ((labelJ9 p c m).zipIdx.map fun q => χ cGamW ^ q.2 * algebraMap (ZMod p) K q.1).sum

/-- **`pubVJ9`, the J-9 compute publics**: the label `labelJ9` at `0..5`, the seed `seedJ9` at `9..11`, `pubVJ8`
elsewhere. -/
def pubVJ9 (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′) (χ : Coins frameJ8 K) : ℕ → ZMod p :=
  fun j =>
    if j < 6 then (labelJ9 p c m).getD j 0
    else if h : 9 ≤ j ∧ j < 12 then coord b (seedJ9 (p := p) c m (toVS (toVSQ χ))) ⟨j - 9, by omega⟩
    else pubVJ8 δ b c m ρ ρS χ j

variable (c : P8PublicClaim) (m : ClaimMsgVS) (rr : Fin 5 → Quad (algebraMap (ZMod p) K δ)) (rS : Quad (algebraMap (ZMod p) K δ)) (χ : Coins frameJ8 K)

theorem pubVJ9_label (j : ℕ) (hj : j < 6) : pubVJ9 δ b c m rr rS χ j = (labelJ9 p c m).getD j 0 := by
  simp only [pubVJ9, if_pos hj]

theorem pubVJ9_hi (j : ℕ) (hj : 12 ≤ j) : pubVJ9 δ b c m rr rS χ j = pubVJ8 δ b c m rr rS χ j := by
  simp only [pubVJ9, if_neg (show ¬ j < 6 by omega), dif_neg (show ¬ (9 ≤ j ∧ j < 12) by omega)]

theorem pubVJ9_six (j : ℕ) (h1 : 6 ≤ j) (h2 : j < 9) : pubVJ9 δ b c m rr rS χ j = pubVJ8 δ b c m rr rS χ j := by
  simp only [pubVJ9, if_neg (show ¬ j < 6 by omega), dif_neg (show ¬ (9 ≤ j ∧ j < 12) by omega)]

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal limbVal_eq_of_coords)

/-- `limbVal` reads three consecutive entries. -/
theorem limbVal_congr3 {f g : ℕ → ZMod p} {k : ℕ} (h : ∀ i < 3, f (k + i) = g (k + i)) :
    limbVal b f k = limbVal b g k := by
  unfold limbVal
  exact Finset.sum_congr rfl fun i _ => by rw [h i i.isLt]

/-- **The balance terminals read publics `≥ 12` only.** -/
theorem rhoX_congr12 [DecidableEq K] {pv pv' : ℕ → ZMod p} (h : ∀ j, 12 ≤ j → pv j = pv' j) (bl : Bal) :
    ServedJ8.rhoX (K := K) (b := b) (δ := δ) (pubVal := pv) bl =
      ServedJ8.rhoX (K := K) (b := b) (δ := δ) (pubVal := pv') bl := by
  have e : ∀ k, 12 ≤ k → limbVal b pv k = limbVal b pv' k := fun k hk =>
    limbVal_congr3 b fun i _ => h _ (by omega)
  cases bl <;> simp only [ServedJ8.rhoX, TeleCQX.balCols] <;> rw [e _ (by decide), e _ (by decide)]

theorem rhoX_pubVJ9 [DecidableEq K] (bl : Bal) :
    ServedJ8.rhoX (K := K) (b := b) (δ := δ) (pubVal := pubVJ9 δ b c m rr rS χ) bl =
      ServedJ8.rhoX (K := K) (b := b) (δ := δ) (pubVal := pubVJ8 δ b c m rr rS χ) bl :=
  rhoX_congr12 δ b (fun j hj => pubVJ9_hi δ b c m rr rS χ j hj) bl

/-- `XCtx.hIC` at `pubVJ9`. -/
theorem pubVJ9_IC [DecidableEq K] : limbVal b (pubVJ9 δ b c m rr rS χ) pubIC = limbVal b (chalVJ8 b χ) chalAlphaW := by
  rw [← pubVJ8_IC δ b c m rr rS χ]
  exact limbVal_congr3 b fun i hi => pubVJ9_six δ b c m rr rS χ _ (by simp [pubIC]) (by simp [pubIC]; omega)

/-- `XCtx.hOut` at `pubVJ9`. -/
theorem pubVJ9_out [DecidableEq K] : limbVal b (pubVJ9 δ b c m rr rS χ) pubOut = 0 := by
  rw [← pubVJ8_out δ b c m rr rS χ]
  exact limbVal_congr3 b fun i hi => pubVJ9_hi δ b c m rr rS χ _ (by simp [pubOut])

/-- The seed public at `pubVJ9` is `seedJ9`. -/
theorem limb_pubVJ9_seed : limbVal b (pubVJ9 δ b c m rr rS χ) pubSeed = seedJ9 (p := p) c m (toVS (toVSQ χ)) := by
  refine limbVal_eq_of_coords b _ _ _ fun k => ?_
  have hk := k.isLt
  simp only [pubVJ9, pubSeed]
  erw [if_neg (by omega), dif_pos (by omega)]
  congr 1; apply Fin.ext; simp

/-- **Conservativity**: with no big claim atom, `pubVJ9 = pubVJ8`. -/
theorem pubVJ9_eq_pubVJ8 [DecidableEq K] (h : ∀ k, isBigN p (claimNoun c k) = false) :
    pubVJ9 δ b c m rr rS χ = pubVJ8 δ b c m rr rS χ := by
  have hl := labelJ9_eq_labelF c m h
  funext j
  by_cases h6 : j < 6
  · simp only [pubVJ9, if_pos h6, pubVJ8, pubVHQ, pubVH, if_pos (show j < 27 by omega),
      if_pos (show j < 21 by omega), hl]
  · by_cases h9 : 9 ≤ j ∧ j < 12
    · simp only [pubVJ9, if_neg h6, dif_pos h9, pubVJ8, pubVHQ, pubVH,
        if_pos (show j < 27 by omega), if_pos (show j < 21 by omega), if_neg h6,
        dif_neg (show ¬ j < 9 by omega), dif_pos (show j < 12 by omega)]
      congr 2
      simp only [seedJ9, seedVS, hl]
    · simp only [pubVJ9, if_neg h6, dif_neg h9]

end Pubs

/-! ## 2. The verifier-computed claim records and census -/

section Msg
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The big-leaf claim records**: `claimVec (E (atom n)) idx 0 0` per big claim atom (rank `(0, 0)`: the atom table's
`mb` export record, the g5 terminal). -/
def claimBigRecs (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) : List (Fin 5 → 𝕂′) :=
  (claimBigs p c).map fun k => ClaimVS.claimVec δ (encJ8 δ χ (claimNoun c k)) ((m k).1 : ZMod p) 0 0

/-- **`claimRecsJ9`** `= claimRecsJ8 ++ claimBigRecs`. -/
def claimRecsJ9 (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) : List (Fin 5 → 𝕂′) :=
  claimRecsJ8 δ χ c m ++ claimBigRecs δ χ c m

theorem claimRecsJ9_length (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) :
    (claimRecsJ9 δ χ c m).length ≤ 3 := by
  simp only [claimRecsJ9, claimBigRecs, claimRecsJ8, List.length_append, List.length_map]
  exact claimCells_bigs_length p c

end Msg

/-- **`censusGJ9`**: the J-8 census nouns and the claim's big atoms. -/
def censusGJ9 {p : ℕ} [Fact p.Prime] (Pb : PubJ8 p) (c : P8PublicClaim) : List Noun :=
  censusG Pb c ++ (claimBigs p c).map (claimNoun c)

theorem censusGJ9_length {p : ℕ} [Fact p.Prime] (Pb : PubJ8 p) (c : P8PublicClaim) :
    (censusGJ9 Pb c).length ≤ (censusG Pb c).length + 3 := by
  simp only [censusGJ9, List.length_append, List.length_map]
  have := claimCells_bigs_length p c
  omega

end

end Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
