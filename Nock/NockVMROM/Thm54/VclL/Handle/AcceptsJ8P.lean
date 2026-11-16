/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8P.lean

  * §1 the atom table's exported keys READ from its committed `mb` rows (`mbXs`, `mbVp`), their weighted sum is
    the g5 terminal `pubsA 6/7` (`mbXs_sum`), their denominators are nonzero (`mbXs_den`), and they are claim-shaped
    (`mbXs_claimVec`).  **FINDING (kernel-checked, `chalsAJ8_zAt`)**: the size entry `zAt` of the g5 key reads the
    atom vector's leaves `37 / 38`, which `frameJ8` fills with `γ′^13` (validity coins `χ₄ χ₆`), not `z`.
  * §3 **`AcceptsJ8'`**: `AcceptsJ8`'s chip / layout / J / pin checks, with the list equations replaced by PUBLIC
    equations (`hsumC'`: claim + pin records against `pubsC 0/1 + pubsA 6/7`; `hbalA'`: `pubsA 4/5 = pubsA 10/11 +
    pubsV 4/5`), plus `hvalA0` (`pubsA 0/1 = 0`, Q2 S3), `hfxC` (`pubsC 2/3 = pubsW 0/1`, Q1), `hfxA`
    (`pubsA 2/3 = pubsV 0/1`, Q1), the claim checks (atoms `< p`, cell serials `< p`, rank limb `< p`), the census
    size check on the registered and claim cell nouns, and the public length checks.  **`acceptsJ8_of'`**:
    `AcceptsJ8'` ⇒ `AcceptsJ8` at `toMsgJ8`.
  * §4 the derived `LinkJ8` fields: `hcountC`, `hcountA` (public lengths), `hseed`, `hreal` (cell formula), and the
    claim binding `hs / hf / he` (`claim_den`: the claim records are served, `regClaims_provided`, then
    `claimK_genuine_cell` under the census at the claim nouns, Q2's `hinjE_of_outside` at
    `G = registered ++ claim cells`); `hinjE` from the same census.
  * §5 **`LinkJ8'`** (the residue) and **`hsoundJ8'`**, **`probJ8_final'`** (`hlink` over `LinkJ8'` only).  The old
    witnesses: `cFalse` is rejected (`acceptsJ8'_cFalse_rejected`); `padM` / `padX` are not expressible (the lists
    are `toMsgJ8`'s, `toMsgJ8_reqsC`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q3
import Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R2V

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P

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

noncomputable section

/-! ## 1. The atom table's exported keys, read from the committed `mb` rows -/

section MB
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)
  (Q : Fin (AtomChipHQ.atomChipHQ δ b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "AF" => AtomServedQ.aEF b nodes orbit chals pubs
local notation "AK" => AtomServedQ.aEK δ b nodes orbit chals pubs

/-- The exported fingerprint of row `i`: `(zAt, 0, leaf_y)`. -/
def mbFP {w : ℕ} (Q' : Fin w → (ZMod p)[X]) (i : Fin n) : FP 𝕂′ :=
  ⟨(AtomChipHQ.zAt : QE (ZMod p)).ev δ (AK Q' i) (AF Q' i), 0,
    (QE.var (Cell.pR + 4) : QE (ZMod p)).ev δ (AK Q' i) (AF Q' i)⟩

/-- **The external validity provides read from the atom table**: every row with `mb ≠ 0`, its g5 key and weight. -/
def mbXs {w : ℕ} (Q' : Fin w → (ZMod p)[X]) : List ((Fin 5 → 𝕂′) × 𝕂′) :=
  (List.finRange n).flatMap fun i =>
    if (AF Q' i).trace AtomChipHQ.mb = 0 then [] else
      [(keyVec δ 5 AtomChipHQ.mbKey (AK Q' i) (AF Q' i), liftQ δ ((AF Q' i).trace AtomChipHQ.mb))]

/-- **The external keys read from the atom table** (`(fp, 0, 0, idx)` per exported row). -/
def mbVp {w : ℕ} (Q' : Fin w → (ZMod p)[X]) : List (VKey 𝕂′) :=
  (List.finRange n).flatMap fun i =>
    if (AF Q' i).trace AtomChipHQ.mb = 0 then [] else
      [(mbFP δ b nodes orbit chals pubs Q' i, 0, 0, ((AF Q' i).trace Cell.idx).val)]

theorem gate_inv_mb : QE.sub (QE.mul δ (QE.var AtomChipHQ.mbInv) (den δ AtomChipHQ.mbKey)) QE.one ∈
    AtomServedQ.qList δ := by
  simp [AtomServedQ.qList, AtomChipHQ.atomQ]

/-- The g5 inverse at row `i`: `den ≠ 0`, `inv = den⁻¹`, `den = compress ⟨γ′, ρ′⟩ (key)`. -/
theorem mb_inv (hsat : (AtomChipHQ.atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies Q)
    (γ ρ : 𝕂′) (hok : ChalsOK δ chals γ ρ 11) (i : Fin n) :
    FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (keyVec δ 5 AtomChipHQ.mbKey (AK Q i) (AF Q i)) ≠ 0 ∧
      AtomServedQ.rq δ b nodes orbit chals pubs Q AtomChipHQ.mbInv i =
        (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ (keyVec δ 5 AtomChipHQ.mbKey (AK Q i) (AF Q i)))⁻¹ := by
  have g := AtomServedQ.atom_qgates δ b hn nodes orbit chals pubs Q hsat i _ (gate_inv_mb δ)
  have hch : (AK Q i).chal = chals := funext fun j => AtomServedQ.aEK_chal δ b hn nodes orbit chals pubs Q i j
  have hok' : ChalsOK δ (AK Q i).chal γ ρ 5 := by rw [hch]; exact chalsOK_mono δ (by norm_num) hok
  rw [ev_sub, ev_mul, ev_var, ev_one, sub_eq_zero,
    den_ev_compress' δ AtomChipHQ.mbKey (by rfl) _ _ γ ρ hok'] at g
  exact ⟨right_ne_zero_of_mul_eq_one g, eq_inv_of_mul_eq_one_left g⟩

/-- **The external provides read from the `mb` rows sum to the g5 terminal `pubsA 6/7`.** -/
theorem mbXs_sum (hsat : (AtomChipHQ.atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (AtomChipHQ.atomChipHQ δ b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : 𝕂′) (hok : ChalsOK δ chals γ ρ 11) :
    ((mbXs δ b nodes orbit chals pubs Q).map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1)⁻¹).sum =
      Quad.mk _ (pubs AtomChipHQ.pubMB) (pubs (AtomChipHQ.pubMB + 1)) := by
  rw [← AtomServedQ.atom_tele δ b hn nodes orbit chals pubs Q hsat hbind hinj hadj AtomChipHQ.mb
    AtomChipHQ.mbInv AtomChipHQ.mbAcc AtomChipHQ.pubMB (by simp [AtomServedQ.qList, AtomChipHQ.atomQ])
    (by simp [AtomServedQ.qList, AtomChipHQ.atomQ]) (by simp [AtomServedQ.qList, AtomChipHQ.atomQ])]
  rw [mbXs, map_flatMap_sum, sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(mb_inv δ b hn nodes orbit chals pubs Q hsat γ ρ hok i).2]
  split_ifs with h0
  · simp [h0, liftQ]
  · simp

theorem mbXs_den (hsat : (AtomChipHQ.atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies Q)
    (γ ρ : 𝕂′) (hok : ChalsOK δ chals γ ρ 11) :
    ∀ x ∈ mbXs δ b nodes orbit chals pubs Q, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ x.1 ≠ 0 := by
  intro x hx
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hx
  split_ifs at hi with h0
  · simp at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact (mb_inv δ b hn nodes orbit chals pubs Q hsat γ ρ hok i).1

/-- Each read key is claim-shaped at its row's external key. -/
theorem keyVec_mbKey (i : Fin n) :
    keyVec δ 5 AtomChipHQ.mbKey (AK Q i) (AF Q i) =
      ClaimVS.claimVec δ (mbFP δ b nodes orbit chals pubs Q i)
        ((((AF Q i).trace Cell.idx).val : ℕ) : ZMod p) ((0 : ℕ) : ZMod p) ((0 : ℕ) : ZMod p) := by
  funext c
  fin_cases c <;>
    simp [keyVec, AtomChipHQ.mbKey, ClaimVS.claimVec, mbFP, ev_zero, ev_base, liftQ, Quad.mk_zero',
      ← Quad.mk_base, cv, CoeffExpr.eval]
  rw [Quad.mk_base]; rfl

theorem mbXs_claimVec :
    ∀ x ∈ mbXs δ b nodes orbit chals pubs Q, ∃ k ∈ mbVp δ b nodes orbit chals pubs Q,
      x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p) := by
  intro x hx
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hx
  split_ifs at hi with h0
  · simp at hi
  · rw [List.mem_singleton] at hi
    subst hi
    refine ⟨_, List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by rw [if_neg h0]; exact List.mem_singleton_self _⟩, ?_⟩
    exact keyVec_mbKey δ b hn nodes orbit chals pubs Q i

theorem mbVp_small : ∀ k ∈ mbVp δ b nodes orbit chals pubs Q, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < p := by
  intro k hk
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hk
  split_ifs at hi with h0
  · simp at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact ⟨rfl, rfl, ZMod.val_lt _⟩

/-- Every read key names an exported (`mb ≠ 0`) row (the shape of `atomLeaves_extB_of_mb`'s `hvpRow`, at
`mb ≠ 0`). -/
theorem mbVp_row : ∀ k ∈ mbVp δ b nodes orbit chals pubs Q,
    ∃ i : Fin n, (AF Q i).trace AtomChipHQ.mb ≠ 0 ∧ k.2.2.2 = ((AF Q i).trace Cell.idx).val := by
  intro k hk
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hk
  split_ifs at hi with h0
  · simp at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact ⟨i, h0, rfl⟩

theorem length_flatMap_ite_le {α β : Type*} (l : List α) (P : α → Prop) [DecidablePred P] (f : α → β) :
    (l.flatMap fun a => if P a then [] else [f a]).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    split_ifs <;> simp only [List.length_nil, List.length_singleton] <;> omega

end MB

/-! ### The finding: `zAt` is `γ′^13` at `frameJ8` -/

section ZAt
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

/-- **FINDING (wiring)**: the atom vector's leaves `37 / 38`, which the g5 key's size entry `zAt` reads, are
`Re / Im γ′^13` (`γ′ = χ₄ + χ₆√δ`, a round-1 validity coin), not the fingerprint seed `z = (χ₂, χ₃)`. -/
theorem chalsAJ8_zAt (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 37) (chalsAJ8 δ χ 38) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6) ^ 13 := by
  have e : ∀ j, 4 ≤ j → chalsAJ8 δ χ j = chalsMJ8 δ χ j := fun j hj => by
    simp only [chalsAJ8, if_neg (show j ≠ 2 by omega), if_neg (show j ≠ 3 by omega)]
  rw [e 37 (by norm_num), e 38 (by norm_num)]
  simp only [chalsMJ8, chalsVSQ, chalsVS, Chips.ChipRAP.chalsVCL, CellH.hGam, CellH.hRho]
  norm_num
  exact Quad.mk_re_im _ _

end ZAt

/-! ## 2. `MsgJ8'`, the verifier-computed lists, `toMsgJ8` -/

section Msg
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The prover's public messages under `AcceptsJ8'`**: the claim message (serials), the balance publics, the chip
publics.  No list. -/
structure MsgJ8' (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] (δ : ZMod p) where
  m : ClaimMsgVS
  ρ : Fin 5 → Quad (algebraMap (ZMod p) K δ)
  ρS : Quad (algebraMap (ZMod p) K δ)
  pubsC : ℕ → K
  pubsW : ℕ → K
  pubsJ : ℕ → K
  pubsA : ℕ → K
  pubsV : ℕ → K

/-- The rank limbs of a noun (`rankOf = internal`, `(rank / 2^62, rank % 2^62)`), computed by the verifier. -/
def rkC (x : Noun) : ℕ × ℕ := (x.internal / 2 ^ 62, x.internal % 2 ^ 62)

/-- The claim's cell positions. -/
def claimCells (c : P8PublicClaim) : List (Fin 3) := (List.finRange 3).filter fun k => isCellN (claimNoun c k)

def claimRecsJ8 (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) : List (Fin 5 → 𝕂′) :=
  (claimCells c).map fun k => ClaimVS.claimVec δ (encJ8 δ χ (claimNoun c k)) ((m k).1 : ZMod p)
    ((rkC (claimNoun c k)).1 : ZMod p) ((rkC (claimNoun c k)).2 : ZMod p)

def pinRecsJ8 (Pb : PubJ8 p) (χ : Coins frameJ8 K) : List (Fin 5 → 𝕂′) :=
  Pb.regs.map fun id => ClaimVS.claimVec δ (encJ8 δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id))) (Pb.idx id : ZMod p)
    ((Pb.rk id).1 : ZMod p) ((Pb.rk id).2 : ZMod p)

/-- The census nouns beyond the decoded table: the registered formulas and the claim's cell nouns. -/
def censusG (Pb : PubJ8 p) (c : P8PublicClaim) : List Noun :=
  Pb.regs.map (fun id => Nock.Jet.Autogen.compile p (Pb.Rt id)) ++ (claimCells c).map (claimNoun c)

/-- **`toMsgJ8`**: the old message with every list computed — `reqsC` by the verifier (claim + pins), `xsC` / `vp`
read from the atom table's committed `mb` rows, `wreqs` the atom walk's handle reads. -/
def toMsgJ8 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) :
    MsgJ8 p K δ where
  m := M.m
  ρ := M.ρ
  ρS := M.ρS
  pubsC := M.pubsC
  pubsW := M.pubsW
  pubsJ := M.pubsJ
  pubsA := M.pubsA
  pubsV := M.pubsV
  reqsC := claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ
  xsC := mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)
  vp := mbVp δ b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)
  wreqs := ServeH.walkXReqs b Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)

/-- The cell validity's external requests are the verifier's (no prover choice: `padM` / `padX` are not
expressible). -/
theorem toMsgJ8_reqsC (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ)
    (tr : TrJ8 (ZMod p)) : (toMsgJ8 δ b Pb c χ M tr).reqsC = claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ := rfl

end Msg

/-! ## 3. `AcceptsJ8'` -/

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`AcceptsJ8'`: THE verifier's checks** — `AcceptsJ8`'s chip, layout, balance (`hGx hGp hGS`), J and pin checks,
with every list equation replaced by a PUBLIC equation over verifier-computed lists, plus the claim binding, the
terminal links of Q1 / Q2, the census size check and the public length checks. -/
structure AcceptsJ8' (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) : Prop where
  -- compute
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
  hinjX : Function.Injective Pb.nodes
  hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  -- the cell table
  hsatC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hbindC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hinjC : Function.Injective Pb.nodesC
  hadjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  hnpC : Pb.nC < ringChar (ZMod p)
  -- the J-8 walk
  hsatW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).rap.Satisfies
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hbindW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).BindsPreprocessing
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hinjW : Function.Injective Pb.nodesW
  hadjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  hkW : 1 ≤ Pb.kroots
  hknW : Pb.kroots ≤ Pb.nW
  hkpW : Pb.kroots + Pb.nW < ringChar (ZMod p)
  -- the J chip
  hsatJ : (jetChipJ8 δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay).rap.Satisfies
    (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
  hbindJ : (jetChipJ8 δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay).BindsPreprocessing
    (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
  hinjJ : Function.Injective Pb.nodesJ
  hnJ : 0 < Pb.nJ
  hadjJ : ∀ (i : Fin Pb.nJ) (hi : (i : ℕ) + 1 < Pb.nJ), Pb.nodesJ ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesJ i * Pb.orbitJ.ω
  -- the atom table
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < p
  -- the atom walk
  hsatV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV).rap.Satisfies
    (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)
  hbindV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV).BindsPreprocessing
    (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)
  hinjV : Function.Injective Pb.nodesV
  hadjV : ∀ (i : Fin Pb.nV) (hi : (i : ℕ) + 1 < Pb.nV), Pb.nodesV ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesV i * Pb.orbitV.ω
  hkV : 1 ≤ Pb.krootsV
  hknV : Pb.krootsV ≤ Pb.nV
  hkpV : Pb.krootsV + Pb.nV < ringChar (ZMod p)
  -- the public balance equations
  hGx : M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
  hGp : M.ρ 4 = Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
  hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1))
  -- the J chip's public checks and the registry pin
  hlay : List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids
  hsmall : ∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p
  huniq : ((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup
  hTpl : ∀ i ∈ Pb.regs, Rg i = some ⟨(Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Pb.Rt i)⟩ ∧
    axPosB (Pb.Rt i) = true ∧ (Pb.Rt i).WellTyped p
  hnd : Pb.regs.Nodup
  hidx : ∀ id ∈ Pb.regs, Pb.idx id < p
  hrk : ∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)
  hlt : ∀ id ∈ Pb.regs, (Pb.rk id).1 < ringChar (ZMod p) ∧ (Pb.rk id).2 < ringChar (ZMod p) ∧
    Pb.idx id < ringChar (ZMod p)
  -- the cell validity: verifier-computed requests against the cell terminal and the atom g5 terminal (Q2 S2)
  hsumC' : ((claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ).map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 0) (M.pubsC 1) + Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1))
  -- the atom export: provides = old-export consumes + the atom walk's handle reads (Q1, `pubsV 4/5`)
  hbalA' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1))
  -- the atom table's validity terminal (Q2 S3)
  hvalA0 : M.pubsA 0 = 0 ∧ M.pubsA 1 = 0
  -- the fingerprint-export links (Q1): cell ↔ J-8 walk, atom table ↔ atom walk
  hfxC : M.pubsC 2 = M.pubsW 0 ∧ M.pubsC 3 = M.pubsW 1
  hfxA : M.pubsA 2 = M.pubsV 0 ∧ M.pubsA 3 = M.pubsV 1
  hclA : ∀ k : Fin 3, ∀ v, claimNoun c k = .atom v → v < p
  hclI : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (M.m k).1 < p
  hclR : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p
  -- the census size check on the registered and claim cell nouns
  hcen : ∀ x ∈ censusG Pb c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < p
  -- public lengths
  hlenC : 3 + Pb.regs.length + 2 * Pb.nC < p
  hlenA : Pb.nA + Pb.nV < p

/-- **`AcceptsJ8'` ⇒ `AcceptsJ8` at `toMsgJ8`**: every former list equation follows from the public equations
and the chips (the g5 telescope `mbXs_sum`, the walk telescope `walkHQK_reqs_sumQ`). -/
theorem acceptsJ8_of' {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} (h : AcceptsJ8' δ b Pb Rg c χ M tr) :
    AcceptsJ8 δ b Pb Rg c χ (toMsgJ8 δ b Pb c χ M tr) tr where
  hsatX := h.hsatX
  hinjX := h.hinjX
  hadjX := h.hadjX
  hsatC := h.hsatC
  hbindC := h.hbindC
  hinjC := h.hinjC
  hadjC := h.hadjC
  hnpC := h.hnpC
  hsatW := h.hsatW
  hbindW := h.hbindW
  hinjW := h.hinjW
  hadjW := h.hadjW
  hkW := h.hkW
  hknW := h.hknW
  hkpW := h.hkpW
  hsatJ := h.hsatJ
  hbindJ := h.hbindJ
  hinjJ := h.hinjJ
  hnJ := h.hnJ
  hadjJ := h.hadjJ
  hsatA := h.hsatA
  hbindA := h.hbindA
  hinjA := h.hinjA
  hadjA := h.hadjA
  hnpA := h.hnpA
  hsatV := h.hsatV
  hbindV := h.hbindV
  hinjV := h.hinjV
  hadjV := h.hadjV
  hkV := h.hkV
  hknV := h.hknV
  hkpV := h.hkpV
  hGx := h.hGx
  hGp := h.hGp
  hGS := h.hGS
  hlay := h.hlay
  hsmall := h.hsmall
  huniq := h.huniq
  hTpl := h.hTpl
  hnd := h.hnd
  hidx := h.hidx
  hrk := h.hrk
  hlt := h.hlt
  hsumC := by
    show _ = _ + ((mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA _).map _).sum
    rw [mbXs_sum δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA _ h.hsatA h.hbindA h.hinjA h.hadjA _ _
      (chalsAJ8_ok δ χ)]
    exact h.hsumC'
  hxneC := mbXs_den δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA _ h.hsatA _ _ (chalsAJ8_ok δ χ)
  hbalA := by
    show _ = _ + (((ServeH.walkXReqs b Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV _).map _).map _).sum
    rw [List.map_map]
    refine h.hbalA'.trans ?_
    congr 1
    exact (WalkTeleJ8.walkHQK_reqs_sumQ δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV _
      h.hsatV h.hbindV h.hinjV h.hadjV).symm
  hxC := mbXs_claimVec δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA _
  hvp0 := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := mbVp_small δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA _ k hk
    exact ⟨h1, h2, by rw [ZMod.ringChar_zmod_n]; exact h3⟩
  hpinC := fun id hid => List.mem_append_right _ (List.mem_map.mpr ⟨id, hid, rfl⟩)

end Accept

/-! ## 4. The derived `LinkJ8` fields -/

section Derived
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (k : ℕ) (hf : ∀ a, (f a).length ≤ k) :
    (l.flatMap f).length ≤ k * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have := hf a
    omega

theorem claimRecs_length_le (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) :
    (claimRecsJ8 δ χ c m).length ≤ 3 := by
  simp only [claimRecsJ8, claimCells, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- **L1 `hcountC`, derived** from the public length check `3 + |regs| + 2·nC < p`. -/
theorem hcountC_of' (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ)
    (tr : TrJ8 (ZMod p)) (hlen : 3 + Pb.regs.length + 2 * Pb.nC < p) :
    ((toMsgJ8 δ b Pb c χ M tr).reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ)
      (toMsgJ8 δ b Pb c χ M tr).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ8 δ b Pb c χ M tr).pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) (toMsgJ8 δ b Pb c χ M tr).pubsC))).length < p := by
  have h1 := claimRecs_length_le δ χ c M.m
  have h2 : (cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ8 δ b Pb c χ M tr).pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) (toMsgJ8 δ b Pb c χ M tr).pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) (toMsgJ8 δ b Pb c χ M tr).pubsC))).length ≤ 2 * Pb.nC := by
    unfold cellVInternal
    refine (length_flatMap_le _ _ 2 fun i => ?_).trans (by simp)
    rw [List.length_append]
    split_ifs <;> simp
  rw [toMsgJ8_reqsC, List.length_append, List.length_append, pinRecsJ8, List.length_map]
  exact lt_of_le_of_lt (by omega) hlen

/-- **L5 `hcountA`, derived** from the public length check `nA + nV < p`. -/
theorem hcountA_of' (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ)
    (tr : TrJ8 (ZMod p)) (hlen : Pb.nA + Pb.nV < p) :
    (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) (toMsgJ8 δ b Pb c χ M tr).pubsA
      (qA δ b Pb tr (chalsAJ8 δ χ) (toMsgJ8 δ b Pb c χ M tr).pubsA) ++ (toMsgJ8 δ b Pb c χ M tr).wreqs).length < p := by
  have h1 : (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) (toMsgJ8 δ b Pb c χ M tr).pubsA
      (qA δ b Pb tr (chalsAJ8 δ χ) (toMsgJ8 δ b Pb c χ M tr).pubsA)).length ≤ Pb.nA := by
    unfold AtomServedQ.atomCReqs
    refine (length_flatMap_le _ _ 1 fun i => ?_).trans (by simp)
    split_ifs <;> simp
  have h2 : (toMsgJ8 δ b Pb c χ M tr).wreqs.length = Pb.nV := by simp [toMsgJ8, ServeH.walkXReqs]
  rw [List.length_append, h2]
  omega

theorem rkC_ne {x : Noun} (hx : isCellN x = true) : rkC x ≠ (0, 0) := by
  cases x with
  | atom v => simp [isCellN] at hx
  | cell a b' =>
    intro h
    simp only [rkC, Prod.mk.injEq] at h
    have := Nat.div_add_mod (Noun.cell a b').internal (2 ^ 62)
    rw [h.1, h.2] at this
    simp [Noun.internal] at this
    omega

/-- The claim publics `0..5` are the claim label. -/
theorem pubVJ8_label (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′) (χ : Coins frameJ8 K)
    (j : ℕ) (hj : j < 6) : pubVJ8 δ b c m ρ ρS χ j = (labelF (F := ZMod p) c m).getD j 0 := by
  simp only [pubVJ8, pubVHQ, pubVH, if_pos (show j < 27 by omega), if_pos (show j < 21 by omega),
    if_pos hj]

/-- **Row 0's claim handles, as handles**: kind and value of claim noun `k` (`hdV` of `xS / xF / xE`). -/
theorem row0_hd (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) (hp : 17 < p) (hacc : AcceptsJ8 δ b Pb Rg c χ M tr) :
    ∀ k : Fin 3, hdV (envX δ b Pb c χ M tr 0) (![xS, xF, xE] k) =
      (((if (claimH c M.m k).1 then 1 else 0 : ZMod p)).val, (((claimH c M.m k).2 : ℕ) : ZMod p).val) := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := LinkJ8Q3.row0_claim δ b Pb Rg c χ M tr hp hacc
  intro k
  have L := fun j (hj : j < 6) => pubVJ8_label δ b c M.m M.ρ M.ρS χ j hj
  fin_cases k
  · simp [hdV]; rw [p0, p1, L 0 (by norm_num), L 1 (by norm_num)]; simp [labelF, hvalF]; try rfl
  · simp [hdV]; rw [p2, p3, L 2 (by norm_num), L 3 (by norm_num)]; simp [labelF, hvalF]; try rfl
  · simp [hdV]; rw [p4, p5, L 4 (by norm_num), L 5 (by norm_num)]; simp [labelF, hvalF]; try rfl

/-- **The claim noun's handle denotes it**: atoms by value (`< p`), cells by the served claim record. -/
theorem den_claim {q : ℕ} (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) (c : P8PublicClaim) (m : ClaimMsgVS)
    (k : Fin 3) (hA : ∀ v, claimNoun c k = .atom v → v < p) (hI : isCellN (claimNoun c k) = true → (m k).1 < p)
    (hcell : isCellN (claimNoun c k) = true → denK t ext (1, (m k).1) = some (claimNoun c k)) :
    denK t ext (((if (claimH c m k).1 then 1 else 0 : ZMod p)).val, (((claimH c m k).2 : ℕ) : ZMod p).val) =
      some (claimNoun c k) := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  unfold claimH
  cases hx : claimNoun c k with
  | atom v =>
    have hv := hA v hx
    simp only [claimHandle, Bool.false_eq_true, if_false, ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hv]
    rfl
  | cell a b' =>
    have hc : isCellN (claimNoun c k) = true := by rw [hx]; rfl
    simp only [claimHandle, if_true, ZMod.val_one, ZMod.val_natCast, Nat.mod_eq_of_lt (hI hc)]
    rw [← hx]; exact hcell hc

end Derived

/-! ## 5. `LinkJ8'`, `hsoundJ8'`, `probJ8_final'` -/

section Sound
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- **`LinkJ8'`: the residue** — `LinkJ8` minus the fields derived from `AcceptsJ8'` (`hcountC`, `hcountA`,
`hinjE`, `hseed`, `hreal` at a cell formula, `hs`, `hf`, `he`), plus the census readout at the registered and
claim cell nouns (`hprsG`) and `hreal` at an atom formula (`hrealA`). -/
structure LinkJ8' (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (rA : ℕ → ARow) : Prop where
  -- L1: the IO-list readouts of `R` / `L` at the trace, their budgets, the counts
  rdX : R.D.cxReqs tr χ = reqsOf δ b Pb c χ M tr .x ∧ R.D.cxProvs tr χ = liftP (provsJ8 δ b Pb χ M tr .x)
  budX : (R.D.cxReqs tr χ).length ≤ 3 * r.N + r.W + r.rd ∧ (R.D.cxProvs tr χ).length ≤ r.D
  rdP : L.pReqs tr (toVSQ χ) = reqsOf δ b Pb c χ M tr .p ∧
    L.pProvs tr (toVSQ χ) = liftP (provsJ8 δ b Pb χ M tr .p)
  budP : (L.pReqs tr (toVSQ χ)).length ≤ 2 * r.N ∧ (L.pProvs tr (toVSQ χ)).length ≤ 2 * r.W
  rdS : R.D.svReqs tr χ = reqsOf δ b Pb c χ M tr .s ∧
    R.D.svProvs tr χ = effP (liftP (provsJ8 δ b Pb χ M tr .s))
  budS : (R.D.svReqs tr χ).length ≤ r.N + 2 * r.J + g ∧
    (R.D.svProvs tr χ).length ≤ r.calls + r.heads + r.blocks + r.J
  hcount : ∀ bl, (reqsOf δ b Pb c χ M tr bl).length < p
  rdV : R.D.valReqs tr χ = M.reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) ∧
    R.D.valProvs tr χ = SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) ++ M.xsC
  budV : (R.D.valReqs tr χ).length ≤ 3 + 2 * r.D + g ∧ (R.D.valProvs tr χ).length ≤ r.D + r.mb
  -- L2: the three walk-data readouts
  rdWC : L.cRows tr = rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
    L.cH tr = Pb.n
  rdWW : L.wdW tr (toVSQ χ) = walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
    (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))
  -- L3: `EncInj2`'s census / atom-leaf premises
  hext : ∀ j m, extB p rA j = some m → ∃ v, m = .atom v ∧ lenL v ≤ r.maxlen
  hprs : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M tr).map (·.b0)) (extB p rA)),
    pr ∈ R.D.prs tr
  hvp : AtomLeaves (encJ8 δ χ) M.vp (extB p rA)
  -- L4: the J-8 walk's export premises
  hXW : KeysExported (cellT δ b Pb χ M tr)
    (walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).X
  hHXW : ∀ j < Pb.nW, ∃ c' ∈ cellT δ b Pb χ M tr,
    (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j).trace WChip.idx),
      WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) false,
      WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) true) = exportRecK c'.b0
  -- L5: the atom table's row reader and its facts, its export event
  hRA : ∀ k : Fin Pb.nA, Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
    (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) k) (rA k)
  hsA : ∀ k : Fin Pb.nA, (rA k).Small
  hidxA : ∀ k : Fin Pb.nA, (rA k).idx = k
  hrn : ∀ k, Pb.nA ≤ k → (rA k).inc = 0
  hB : AtomChipHQ.LimbsBounded rA
  hwRA : ∀ j, (rA j).wR ≤ 1
  hok : ∀ j, (rA j).inc = 1 → AtomChipHQ.ChainOK rA j
  houtA : ((AtomServedQ.acoins δ (chalsAJ8 δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8 δ χ)).pole) ∉
    IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
        (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) ++ M.wreqs).map (liftRec (K := K) (L := 𝕂′)))
      (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
        (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)))
  hservedA : ValidityServed (atomT δ b Pb χ M tr)
  -- L6: the atom walk's export premises
  hseedsV : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 2) (chalsAJ8 δ χ 3)) (atomT δ b Pb χ M tr)
  hXV : KeysExported (atomT δ b Pb χ M tr)
    (walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV))).X
  hHXV : ∀ j < Pb.nV, ∃ c' ∈ atomT δ b Pb χ M tr,
    (natOf ((walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j).trace WChip.idx),
      childHOf (walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j) false,
      childHOf (walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j) true) = exportRec c'.b0
  -- L7: the registered nouns' injectivity against the decoded nouns
  -- L8: the compute root binding
  -- the census readout covers the registered and claim cell nouns too (Q2 `hinjE_of_outside`)
  hprsG : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M tr).map (·.b0)) (extB p rA) ++
    censusG Pb c), pr ∈ R.D.prs tr
  -- `hreal` at an atom formula (a false claim; not derived)
  hrealA : isCellN c.formula = false → (stX (envX δ b Pb c χ M tr 0)).isChain = false

/-- **`hsoundJ8'`**: accepted by `AcceptsJ8'`, outside every summand of `allJ8C (withLiftC R L)`, at the statement
binders and under the residue `LinkJ8'` (at the computed message `toMsgJ8`), the claim holds.  Derived inside:
`hcountC`, `hcountA` (public lengths), `hinjE` and the claim census (Q2's `hinjE_of_outside` at
`censusG = registered ++ claim cells`), `hseed`, `hreal` (cell formula), and the claim binding `hs / hf / he`
(the claim records are served, `regClaims_provided`; atom-root keys are excluded by the public rank `≠ (0, 0)`;
`claimK_genuine_cell`). -/
theorem hsoundJ8' [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hacc' : AcceptsJ8' δ b Pb Rg c χ M tr)
    (hout : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    (hWV : R.wdC tr χ = walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)))
    {rA : ℕ → ARow} (hl : LinkJ8' δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr R L rA) :
    Nock.Jet.HoldsN c := by
  have hacc := acceptsJ8_of' δ b hacc'
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  have O := outJ8_of_outside R L b hout
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hcountC := hcountC_of' δ b Pb c χ M tr hacc'.hlenC
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) _ _ hacc.hsumC houtC
    hacc.hxneC hcountC _ hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  -- the census at the registered and claim cell nouns (Q2)
  have hG := LinkQ2J8.hinjE_of_outside (withLiftC R L) hout hq' O.z_ne hE htabC hl.hvp hl.hext hqM hk
    (G := censusG Pb c)
    (fun x hx => ⟨(hacc'.hcen x hx).1, fun v hv => hqM v (by rw [hrc]; exact (hacc'.hcen x hx).2 v hv)⟩) hl.hprsG
  have hinjE : ∀ id ∈ Pb.regs, ∀ d ∈ decodedNouns2 ((cellT δ b Pb χ (toMsgJ8 δ b Pb c χ M tr) tr).map (·.b0))
      (extB p rA), encJ8 δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)) = encJ8 δ χ d →
        Nock.Jet.Autogen.compile p (Pb.Rt id) = d :=
    fun id hid d hd he => hG _ (List.mem_append_left _ (List.mem_map_of_mem hid)) d hd he
  -- the claim's cell records are served
  have hvpr : ∀ k ∈ (toMsgJ8 δ b Pb c χ M tr).vp,
      k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧ k.2.2.2 < ringChar (ZMod p) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hacc.hvp0 k hk
    exact ⟨by omega, by omega, h3⟩
  have hcell : ∀ k : Fin 3, isCellN (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
        (1, (M.m k).1) = some (claimNoun c k) := by
    intro k hkc
    have hprov := Nock.Jet.PinJ8.regClaims_provided δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) hF' hsatC0 hbindC0 hacc.hinjC hacc.hadjC _ _ (chalsOK_J8 (δ := δ) χ)
      _ _ hacc.hsumC houtC hacc.hxneC hcountC _ hacc.hxC hvpr (regs := [0])
      (Ef := fun _ => encJ8 δ χ (claimNoun c k)) (rk := fun _ => rkC (claimNoun c k)) (idx := fun _ => (M.m k).1)
      (fun _ _ => List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩, rfl⟩))
      (fun _ _ => by
        have h62 : (rkC (claimNoun c k)).2 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
        rw [hrc]
        exact ⟨hacc'.hclR k hkc, by omega, hacc'.hclI k hkc⟩) 0 (List.mem_singleton_self 0)
    rcases hprov with hc | hv
    · exact claimK_genuine_cell hq' (fun a b' => rfl) hE htabC hl.hvp
        (fun d hd he => hG _ (List.mem_append_right _ (List.mem_map_of_mem
          (List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩))) d hd he) hc
    · exfalso
      obtain ⟨h1, h2, -⟩ := hl.hvp _ hv
      exact rkC_ne hkc (Prod.ext h1 h2)
  have hden : ∀ k : Fin 3, denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
      (hdV (envX δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr 0) (![xS, xF, xE] k)) = some (claimNoun c k) := by
    intro k
    rw [row0_hd δ b Pb Rg c χ _ tr (by omega) hacc k]
    exact den_claim _ _ c M.m k (hacc'.hclA k) (hacc'.hclI k) (hcell k)
  have hreal : (stX (envX δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr 0)).isChain = false := by
    cases hfc : isCellN c.formula
    · exact hl.hrealA hfc
    · exact LinkJ8Q3.hrealJ8 δ b Pb Rg c χ _ tr (by omega) hacc hfc
  exact hsoundJ8 δ b Pb hRg c χ (toMsgJ8 δ b Pb c χ M tr) tr R L hpG hqM hk hacc hout hWV
    { rdX := hl.rdX, budX := hl.budX, rdP := hl.rdP, budP := hl.budP, rdS := hl.rdS, budS := hl.budS, hcount := hl.hcount, rdV := hl.rdV, budV := hl.budV, rdWC := hl.rdWC, rdWW := hl.rdWW, hext := hl.hext, hprs := hl.hprs, hvp := hl.hvp, hXW := hl.hXW, hHXW := hl.hHXW, hRA := hl.hRA, hsA := hl.hsA, hidxA := hl.hidxA, hrn := hl.hrn, hB := hl.hB, hwRA := hl.hwRA, hok := hl.hok, houtA := hl.houtA, hservedA := hl.hservedA, hseedsV := hl.hseedsV, hXV := hl.hXV, hHXV := hl.hHXV,
      hcountC := hcountC, hcountA := hcountA_of' δ b Pb c χ M tr hacc'.hlenA, hinjE := hinjE,
      hseed := LinkJ8Q3.hseedJ8 δ b Pb Rg c χ _ tr (by omega) hacc, hreal := hreal,
      hs := hden 0, hf := hden 1, he := hden 2 }

/-- **The old L8 witness is rejected**: `cFalse = *[[1 1] [0 1]] = [0 0]` is accepted by `AcceptsJ8'` at no coin
outside `allJ8C` under the residue `LinkJ8'`. -/
theorem acceptsJ8'_cFalse_rejected [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry}
    (hRg : Rg.Faithful) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hout : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    (hWV : R.wdC tr χ = walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)))
    (rA : ℕ → ARow) (hl : LinkJ8' δ b Pb LinkJ8Q3.cFalse χ (toMsgJ8 δ b Pb LinkJ8Q3.cFalse χ M tr) tr R L rA) :
    ¬ AcceptsJ8' δ b Pb Rg LinkJ8Q3.cFalse χ M tr := fun hacc =>
  LinkJ8Q3.not_holdsN_cFalse (hsoundJ8' δ b Pb hRg _ χ M tr R L hpG hqM hk hacc hout hWV hl)

open Classical in
/-- **The J-8 figure at `AcceptsJ8'`**: for every staged `Q`, `Pr[(∃ M', AcceptsJ8') ∧ ¬ HoldsN c] < 2^-155`
(census corner), at the statement binders, conditional on the residue `LinkJ8'` at the computed message
`toMsgJ8` (the fields derived from `AcceptsJ8'` are not assumed). -/
theorem probJ8_final' [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (hAW : Pb.nV ≤ r.AW)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hcK : Fintype.card K = VclL.Events.cK) (hr : RowsLe r EncInjJ8.cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31)
    (hlink : ∀ χ (M : MsgJ8' p K δ), AcceptsJ8' δ b Pb Rg c χ M (Q χ) →
      ∃ rA, LinkJ8' δ b Pb c χ (toMsgJ8 δ b Pb c χ M (Q χ)) (Q χ)
        (TraceJ8.withWalkV (g := g) δ b R0 Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV hAW) L rA) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ8' δ b Pb Rg c χ M (Q χ)) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  BundleJ8.probJ8C_lt_155_census
    (withLiftC (TraceJ8.withWalkV (g := g) δ b R0 Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV hAW) L) Q hQ _ _
    (fun χ hacc hout => by
      obtain ⟨M, hM⟩ := hacc
      obtain ⟨rA, hl⟩ := hlink χ M hM
      exact hsoundJ8' δ b Pb hRg c χ M (Q χ) _ L hpG hqM hk hM hout (wdV_view δ b Pb (Q χ) _ _) hl)
    hcK hr hP hg

/-! ## 6. -/

structure LinkJ8X' (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (rA : ℕ → ARow) : Prop where
  -- L1: the IO-list readouts of `R` / `L` at the trace, their budgets, the counts
  rdX : R.D.cxReqs tr χ = reqsOf δ b Pb c χ M tr .x ∧ R.D.cxProvs tr χ = liftP (provsJ8 δ b Pb χ M tr .x)
  budX : (R.D.cxReqs tr χ).length ≤ 3 * r.N + r.W + r.rd ∧ (R.D.cxProvs tr χ).length ≤ r.D
  rdP : L.pReqs tr (toVSQ χ) = reqsOf δ b Pb c χ M tr .p ∧
    L.pProvs tr (toVSQ χ) = liftP (provsJ8 δ b Pb χ M tr .p)
  budP : (L.pReqs tr (toVSQ χ)).length ≤ 2 * r.N ∧ (L.pProvs tr (toVSQ χ)).length ≤ 2 * r.W
  rdS : R.D.svReqs tr χ = reqsOf δ b Pb c χ M tr .s ∧
    R.D.svProvs tr χ = effP (liftP (provsJ8 δ b Pb χ M tr .s))
  budS : (R.D.svReqs tr χ).length ≤ r.N + 2 * r.J + g ∧
    (R.D.svProvs tr χ).length ≤ r.calls + r.heads + r.blocks + r.J
  hcount : ∀ bl, (reqsOf δ b Pb c χ M tr bl).length < p
  rdV : R.D.valReqs tr χ = M.reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) ∧
    R.D.valProvs tr χ = SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) ++ M.xsC
  budV : (R.D.valReqs tr χ).length ≤ 3 + 2 * r.D + g ∧ (R.D.valProvs tr χ).length ≤ r.D + r.mb
  -- L2: the three walk-data readouts
  rdWC : L.cRows tr = rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
    L.cH tr = Pb.n
  rdWW : L.wdW tr (toVSQ χ) = walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
    (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))
  -- L3: `EncInj2`'s census / atom-leaf premises
  hext : ∀ j m, extB p rA j = some m → ∃ v, m = .atom v ∧ lenL v ≤ r.maxlen
  hprs : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M tr).map (·.b0)) (extB p rA)),
    pr ∈ R.D.prs tr
  hvp : AtomLeaves (encJ8 δ χ) M.vp (extB p rA)
  -- L4: the J-8 walk's export premises
  hXW : KeysExported (cellT δ b Pb χ M tr)
    (walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).X
  hHXW : ∀ j < Pb.nW, ∃ c' ∈ cellT δ b Pb χ M tr,
    (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j).trace WChip.idx),
      WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) false,
      WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) true) = exportRecK c'.b0
  -- L5: the atom table's row reader and its facts, its export event
  hRA : ∀ k : Fin Pb.nA, Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
    (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) k) (rA k)
  hsA : ∀ k : Fin Pb.nA, (rA k).Small
  hidxA : ∀ k : Fin Pb.nA, (rA k).idx = k
  hrn : ∀ k, Pb.nA ≤ k → (rA k).inc = 0
  hB : AtomChipHQ.LimbsBounded rA
  hwRA : ∀ j, (rA j).wR ≤ 1
  hok : ∀ j, (rA j).inc = 1 → AtomChipHQ.ChainOK rA j
  houtA : ((AtomServedQ.acoins δ (chalsAJ8 δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8 δ χ)).pole) ∉
    IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
        (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) ++ M.wreqs).map (liftRec (K := K) (L := 𝕂′)))
      (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
        (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)))
  hservedA : ValidityServed (atomT δ b Pb χ M tr)
  -- L6: the atom walk's export premises
  hseedsV : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 2) (chalsAJ8 δ χ 3)) (atomT δ b Pb χ M tr)
  hHXV : ∀ j < Pb.nV, ∃ c' ∈ atomT δ b Pb χ M tr,
    (natOf ((walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j).trace WChip.idx),
      childHOf (walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j) false,
      childHOf (walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j) true) = exportRec c'.b0
  -- L7: the registered nouns' injectivity against the decoded nouns
  -- L8: the compute root binding
  -- the census readout covers the registered and claim cell nouns too (Q2 `hinjE_of_outside`)
  hprsG : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M tr).map (·.b0)) (extB p rA) ++
    censusG Pb c), pr ∈ R.D.prs tr
  -- `hreal` at an atom formula (a false claim; not derived)
  hrealA : isCellN c.formula = false → (stX (envX δ b Pb c χ M tr 0)).isChain = false

theorem hsoundJ8X' [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hbV : Pb.nV ≤ r.AW) (hbA : Pb.nA ≤ r.A)
    (hacc' : AcceptsJ8' δ b Pb Rg c χ M tr)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b (withLiftC R L) Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV
      Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    (hWV : R.wdC tr χ = walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)))
    {rA : ℕ → ARow} (hl : LinkJ8X' δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr R L rA) :
    Nock.Jet.HoldsN c := by
  have hacc := acceptsJ8_of' δ b hacc'
  have hAV : Quad.mk (algebraMap (ZMod p) K δ) ((toMsgJ8 δ b Pb c χ M tr).pubsA 2) ((toMsgJ8 δ b Pb c χ M tr).pubsA 3) =
      Quad.mk (algebraMap (ZMod p) K δ) ((toMsgJ8 δ b Pb c χ M tr).pubsV 0) ((toMsgJ8 δ b Pb c χ M tr).pubsV 1) := by
    show Quad.mk _ (M.pubsA 2) (M.pubsA 3) = Quad.mk _ (M.pubsV 0) (M.pubsV 1)
    rw [hacc'.hfxA.1, hacc'.hfxA.2]
  have hXV := LinkJ8R2V.hXV_withFpxV δ b Pb c χ (toMsgJ8 δ b Pb c χ M tr) tr hacc (withLiftC R L) hout hbV hbA hAV
  exact hsoundJ8' δ b Pb hRg c χ M tr R L hpG hqM hk hacc' (AtomFpxJ8.outsideC_of_outsideX _ hout) hWV
    { rdX := hl.rdX, budX := hl.budX, rdP := hl.rdP, budP := hl.budP, rdS := hl.rdS, budS := hl.budS, hcount := hl.hcount, rdV := hl.rdV, budV := hl.budV, rdWC := hl.rdWC, rdWW := hl.rdWW, hext := hl.hext, hprs := hl.hprs, hvp := hl.hvp, hXW := hl.hXW, hHXW := hl.hHXW, hRA := hl.hRA, hsA := hl.hsA, hidxA := hl.hidxA, hrn := hl.hrn, hB := hl.hB, hwRA := hl.hwRA, hok := hl.hok, houtA := hl.houtA, hservedA := hl.hservedA, hseedsV := hl.hseedsV, hHXV := hl.hHXV, hprsG := hl.hprsG, hrealA := hl.hrealA, hXV := hXV }

open Classical in
theorem probJ8X_final' [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (hAW : Pb.nV ≤ r.AW) (hbA : Pb.nA ≤ r.A)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hcK : Fintype.card K = VclL.Events.cK) (hr : RowsLe r EncInjJ8.cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31)
    (hlink : ∀ χ (M : MsgJ8' p K δ), AcceptsJ8' δ b Pb Rg c χ M (Q χ) →
      ∃ rA, LinkJ8X' δ b Pb c χ (toMsgJ8 δ b Pb c χ M (Q χ)) (Q χ)
        (TraceJ8.withWalkV (g := g) δ b R0 Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV hAW) L rA) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ8' δ b Pb Rg c χ M (Q χ)) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  AtomFpxJ8.probJ8X_lt_155_census
    (AtomFpxJ8.withFpxV δ b (withLiftC (TraceJ8.withWalkV (g := g) δ b R0 Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV hAW) L)
      Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV Pb.nodesA Pb.orbitA) Q hQ _ _
    (fun χ hacc hout => by
      obtain ⟨M, hM⟩ := hacc
      obtain ⟨rA, hl⟩ := hlink χ M hM
      exact hsoundJ8X' δ b Pb hRg c χ M (Q χ) _ L hpG hqM hk hAW hbA hM hout (wdV_view δ b Pb (Q χ) _ _) hl)
    hcK hr hP hg

end Sound

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
