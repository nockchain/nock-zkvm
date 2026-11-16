/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/Out40J9A.lean

* §1 `stX9_congr`, `rowW9_congr`, `envs9_agree`: the twin's walk decoding reads RAP round-0 columns only
    (`Agree0`); `cRows9 Pb tr` (coin- and public-free) and `cRows9_eq` (= S8's `rowsWX9 (envsN9 … chalV pv P)` at any
    coins / publics).
  * §2 `cw9A Pb hN : CW9` (rows `cRows9 Pb`, count `Pb.n`, constant along `St40 StJ9A`).
  * §3 **`OutJ9A`**, the twin of `BundleJ8.OutJ8` at `withLiftCA R L C` with `hw` / `hα` at `cwEvent9` / `foOf9`;
    **`outJ9A_of_outside`**.
  * §4 **`XA9`**: `RR49A.XA` re-based on `withLiftCA … (cw9A …)`; its `ε` is `boundJ8X` by `epsilon_allJ8X` (the 40th's
    summand slot is `boundVCLHQ''` by `Lift40J9A.epsilon_sum40A`), so `RR49A.probJ8X_lt_155_optB` applies verbatim.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.RR49A
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.Lift40J9A
import Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.WalkBridgeX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.Out40J9A

open Nock Nock.Reified Nock.Framework Nock.Edit Module Polynomial
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComapJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 staged_eq LayLe)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 (CSt)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (rowOfX9 csIdx)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX (rowOfX)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 (RowVSX9)
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9 (stX9)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeX9 (rowW9 rowsWX9)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeX9 (cwEvent9 foOf9)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX (tileSet)
open Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9 (Agree0 r0 envsN9)
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.ComputeTable (FP)
open Nock.Atoms (lenL)

noncomputable section

/-! ## 1. The twin walk decoding reads round-0 columns only -/

section Congr
variable {p : ℕ} [Fact p.Prime]

theorem r0_true {c : ℕ} (h : c < 69 ∨ (123 ≤ c ∧ c < 137)) : r0 c = true := by
  unfold r0 permX9
  rw [decide_eq_true_eq]
  split_ifs <;> omega

theorem agree_lt69 {e e' : Env (ZMod p)} (h : Agree0 e e') : ∀ j < 69, e.trace j = e'.trace j :=
  fun j hj => h j (r0_true (Or.inl hj))

theorem rowOfX_congr {e e' : Env (ZMod p)} (h : ∀ j < 69, e.trace j = e'.trace j) (st : StateX) :
    rowOfX e st = rowOfX e' st := by
  have hd : ∀ hh : Hd, hh.k < 69 → hh.v < 69 → hdV e hh = hdV e' hh := by
    intro hh hk hv; simp only [hdV, h _ hk, h _ hv]
  simp only [rowOfX, hd xS (by decide) (by decide), hd xF (by decide) (by decide), hd xE (by decide) (by decide),
    hd xSf1 (by decide) (by decide), hd xSf2 (by decide) (by decide), hd xFh (by decide) (by decide),
    hd xFt (by decide) (by decide), hd xFth (by decide) (by decide), hd xFtt (by decide) (by decide),
    hd xFtth (by decide) (by decide), hd xFttt (by decide) (by decide), hd xM (by decide) (by decide)]

theorem stX9_congr {e e' : Env (ZMod p)} (h : Agree0 e e') : stX9 e = stX9 e' := by
  have hOH : OneHotAt9 e = OneHotAt9 e' := by
    funext j
    apply propext
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    have hr : r0 i = true := by
      simp only [statesX9, newStates, nStates, List.mem_append, List.mem_range, List.mem_cons, sS0B, sS10B, sS10S,
        List.not_mem_nil, or_false] at hi
      exact r0_true (by omega)
    rw [h i hr]
  unfold stX9
  rw [hOH]

theorem rowW9_congr {e e' : Env (ZMod p)} (h : Agree0 e e') (cs : CSt) : rowW9 e cs = rowW9 e' cs := by
  have h69 := agree_lt69 h
  have hL : hdV e ⟨kLabX, vLabX⟩ = hdV e' ⟨kLabX, vLabX⟩ := by
    simp only [hdV]
    rw [h kLabX (by decide), h vLabX (by decide)]
  have hE : hdV e xE = hdV e' xE := by
    simp only [hdV]; rw [h69 _ (by decide), h69 _ (by decide)]
  have hv : e.trace vX = e'.trace vX := h69 _ (by decide)
  cases cs with
  | old st =>
    cases st <;> simp only [rowW9, rowOfX9, rowOfX_congr h69, hL, hE, hv]
  | s0B => simp only [rowW9, rowOfX9, rowOfX_congr h69, hL]
  | s10B => simp only [rowW9, rowOfX9, rowOfX_congr h69, hL]
  | s10S => simp only [rowW9, rowOfX9, rowOfX_congr h69, hL]

variable {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (orbit : StrictOrbitDomain (ZMod p) 3 h)

/-- The twin row environments agree on round-0 columns whenever the traces agree on RAP columns `< 83`. -/
theorem envs9_agree {chalV pubVal chalV' pubVal' : ℕ → ZMod p} {w w' : ℕ}
    (Q : Fin w → (ZMod p)[X]) (Q' : Fin w' → (ZMod p)[X]) (hw : 83 ≤ w) (hw' : 83 ≤ w')
    (hQ : ∀ (j : ℕ) (h1 : j < w) (h2 : j < w'), j < 83 → Q ⟨j, h1⟩ = Q' ⟨j, h2⟩) (i : ℕ) :
    Agree0 (envsN9 hn nodes orbit chalV pubVal Q i) (envsN9 hn nodes orbit chalV' pubVal' Q' i) := by
  intro c hc
  have hc' : permX9 c < 83 := by simpa [r0] using hc
  simp only [envsN9, Env.viaPerm, TeleC.envsN, TeleC.rEF]
  split_ifs <;>
    exact DescentVSQ.envOfTrace_congrW 83 Q Q' hw hw' hQ _ _ _ _ _ _ _ _ hc'

/-- The twin compute walk rows at any coins / publics depend only on the round-0 RAP columns. -/
theorem rowsWX9_congr {chalV pubVal chalV' pubVal' : ℕ → ZMod p} {w w' : ℕ}
    (Q : Fin w → (ZMod p)[X]) (Q' : Fin w' → (ZMod p)[X]) (hw : 83 ≤ w) (hw' : 83 ≤ w')
    (hQ : ∀ (j : ℕ) (h1 : j < w) (h2 : j < w'), j < 83 → Q ⟨j, h1⟩ = Q' ⟨j, h2⟩) :
    rowsWX9 (fun r => envsN9 hn nodes orbit chalV pubVal Q r)
        (fun r => stX9 (envsN9 hn nodes orbit chalV pubVal Q r)) =
      rowsWX9 (fun r => envsN9 hn nodes orbit chalV' pubVal' Q' r)
        (fun r => stX9 (envsN9 hn nodes orbit chalV' pubVal' Q' r)) := by
  funext i
  have hA := envs9_agree hn nodes orbit (chalV := chalV) (pubVal := pubVal) (chalV' := chalV') (pubVal' := pubVal')
    Q Q' hw hw' hQ (i - 1)
  simp only [rowsWX9]
  rw [stX9_congr hA, rowW9_congr hA]

end Congr

/-! ## 2. The coin-free rows and the `CW9` datum -/

section Rows
variable {p : ℕ} [Fact p.Prime]

/-- **The J-9 A compute walk rows of a trace** (coin- and public-free). -/
def cRows9 (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) : ℕ → RowVSX9 :=
  rowsWX9 (fun r => envsN9 Pb.hn Pb.nodes Pb.orbit (fun _ => 0) (fun _ => 0) tr.C r)
    (fun r => stX9 (envsN9 Pb.hn Pb.nodes Pb.orbit (fun _ => 0) (fun _ => 0) tr.C r))

/-- S8's rows at any coins / publics are `cRows9`. -/
theorem cRows9_eq (Pb : PubJ9A p) (tr : TrJ9A (ZMod p)) (chalV pubVal : ℕ → ZMod p) :
    rowsWX9 (fun r => envsN9 Pb.hn Pb.nodes Pb.orbit chalV pubVal tr.C r)
        (fun r => stX9 (envsN9 Pb.hn Pb.nodes Pb.orbit chalV pubVal tr.C r)) = cRows9 Pb tr :=
  rowsWX9_congr Pb.hn Pb.nodes Pb.orbit tr.C tr.C (by norm_num) (by norm_num) (fun _ _ _ _ => rfl)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Along `St40 StJ9A`, the rows are constant in the coins. -/
theorem cRows9_const (Pb : PubJ9A p) (Q : Coins frameVSQ K → TrJ9A (ZMod p)) (hQ : St40 StJ9A Q)
    (ψ ψ' : Coins frameVSQ K) : cRows9 Pb (Q ψ) = cRows9 Pb (Q ψ') := by
  obtain ⟨Q', hQ', y₁, y₂, rfl⟩ := hQ
  refine rowsWX9_congr Pb.hn Pb.nodes Pb.orbit _ _ (by norm_num) (by norm_num) fun j h1 h2 hj => ?_
  exact staged_eq hQ'.1 (r := 0) (fun i hi => absurd hi (by omega)) ⟨j, h1⟩ (by simp [crC9, hj])

/-- **The `CW9` datum of J-9 A**: rows `cRows9 Pb`, count `Pb.n`. -/
def cw9A {r : RowsJ8} (Pb : PubJ9A p) (hN : Pb.n ≤ r.N) : CW9 (K := K) (TrJ9A (ZMod p)) StJ9A r where
  rows := cRows9 Pb
  h := fun _ => Pb.n
  h_le := fun _ => hN
  const := fun Q hQ ψ ψ' => ⟨cRows9_const Pb Q hQ ψ ψ', rfl⟩

end Rows

/-! ## 3. The bundle at `withLiftCA` -/

section Bundle
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 chalsMJ8 coinsCV_J8)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

theorem zero_outA (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (C : CW9 (K := K) Tr St r)
    {tr : Tr} {ψ : Coins frameVSQ K} (h : ∀ s ∈ sum40A L C, ¬ s.mem tr ψ) :
    Quad.mk (algebraMap (ZMod p) K δ) (ψ v2) (ψ v3) ≠ 0 := by
  have := h (zeroL L) (by simp [sum40A])
  rw [zeroL, towerSeedSummand_mem_iff, Finset.mem_singleton] at this
  exact this

theorem hp_outA (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (C : CW9 (K := K) Tr St r)
    {tr : Tr} {ψ : Coins frameVSQ K} (h : ∀ s ∈ sum40A L C, ¬ s.mem tr ψ) (h1 : (L.pReqs tr ψ).length ≤ 2 * r.N)
    (h2 : (L.pProvs tr ψ).length ≤ 2 * r.W) :
    (Quad.mk (algebraMap (ZMod p) K δ) (ψ v11) (ψ cGamHi), Quad.mk (algebraMap (ZMod p) K δ) (ψ v12) (ψ cRhoHi)) ∉
      IOFailureEventW (L.pReqs tr ψ) (L.pProvs tr ψ) := by
  have := h (hpL L) (by simp [sum40A])
  rw [hpL, mem_ioSummandF, evIO_of_guard h1 h2] at this
  exact this

/-- **The exclusion ingredients of `hsound` at `(tr, χ)`, J-9 A** (`OutJ8` with `hw` / `hα` at the twin rows). -/
structure OutJ9A (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (C : CW9 (K := K) Tr St r)
    (b : Module.Basis (Fin 3) (ZMod p) K) (tr : Tr) (χ : Coins frameJ8 K) : Prop where
  atom_hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 2) (chalsAJ8 δ χ 3) ≠ 0
  z_ne : Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) ≠ 0
  valid : (R.D.valReqs tr χ).length ≤ 3 + 2 * r.D + g → (R.D.valProvs tr χ).length ≤ r.D + r.mb →
    (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ)
  /-- #1 at J-9 A: the twin compute walk event. -/
  hw : ∀ {α γ : K}, limbVal b (chalVJ8 b χ) ChipH.chalAlphaW = α → limbVal b (chalVJ8 b χ) ChipH.chalGammaW = γ →
    (α, γ) ∉ cwEvent9 (K := K) (C.rows tr) (C.h tr)
  /-- #1 at J-9 A: the twin compute tiling. -/
  hα : ∀ {α : K}, limbVal b (chalVJ8 b χ) ChipH.chalAlphaW = α → α ∉ tileSet (K := K) (foOf9 (C.rows tr)) (C.h tr)
  hout_x : (R.D.cxReqs tr χ).length ≤ 3 * r.N + r.W + r.rd → (R.D.cxProvs tr χ).length ≤ r.D →
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.cxReqs tr χ) (R.D.cxProvs tr χ)
  hout_s : (R.D.svReqs tr χ).length ≤ r.N + 2 * r.J + g →
    (R.D.svProvs tr χ).length ≤ r.calls + r.heads + r.blocks + r.J →
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.svReqs tr χ) (R.D.svProvs tr χ)
  hout_p : (L.pReqs tr (toVSQ χ)).length ≤ 2 * r.N → (L.pProvs tr (toVSQ χ)).length ≤ 2 * r.W →
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (L.pReqs tr (toVSQ χ)) (L.pProvs tr (toVSQ χ))
  houtV : (chalsVJ8 δ χ 0, chalsVJ8 δ χ 1) ∉ WalkVCL.walkEvent (algebraMap (ZMod p) K δ) (R.wdC tr χ)
  biv : ∀ pr ∈ R.D.prs tr, pr.1.length = pr.2.length → pr.1 ≠ pr.2 → pr.1.length ≤ r.leaves →
    (∀ a ∈ pr.1, lenL a ≤ r.maxlen) → (∀ a ∈ pr.2, lenL a ≤ r.maxlen) →
    Nock.Atoms.leafSum (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
        (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) pr.1 ≠
      Nock.Atoms.leafSum (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
        (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) pr.2
  encInj : ∀ {t : List (CellRow Nock.Atoms.p 𝕂′)} {vp : List (VKey 𝕂′)}
    {ext : ℕ → Option Noun},
    TableAccepts2 (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) t vp →
    AtomLeaves (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3))
      (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))) vp ext →
    (∀ j m, ext j = some m → ∃ v, m = .atom v ∧ lenL v ≤ r.maxlen) →
    (∀ x < Nock.Atoms.p, lenL x ≤ r.maxlen) → 2 * fuelChip ≤ r.leaves →
    (∀ pr ∈ censusPairs (censusList2 (t.map (·.b0)) ext), pr ∈ R.D.prs tr) →
    EncInj2 (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3))
      (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))) t ext

/-- **The J-9 A bundle**: outside `allJ8C (withLiftCA R L C)`, every exclusion ingredient holds. -/
theorem outJ9A_of_outside (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (C : CW9 (K := K) Tr St r)
    (b : Module.Basis (Fin 3) (ZMod p) K)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C (withLiftCA R L C), ¬ s.mem tr χ) :
    OutJ9A (withLiftCA R L C) L C b tr χ := by
  have h40 := outside40CA R L C h
  have hz : Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) ≠ 0 := by
    have := zero_outA L C h40
    exact this
  have h10 := outside_sumJ8_D (withLiftCA R L C) h .bivariateCensus (by decide) (by decide) (by decide)
  refine ⟨atom_hz_of_outsideC _ h, hz, fun h1 h2 => valid_out_of_outsideC _ h h1 h2,
    fun hα hγ => ?_, fun hα => ?_,
    fun h1 h2 => hout_x_of_outsideC _ b h _ _ rfl rfl h1 h2,
    fun h1 h2 => hout_s_of_outsideC _ b h _ _ rfl rfl h1 h2,
    fun h1 h2 => ?_,
    houtV_of_outsideC _ h,
    fun _pr hpr hlen hne hk hM1 hM2 => biv_out_of_outsideC _ h hpr hlen hne hk hM1 hM2, ?_⟩
  · rw [← hα, ← hγ, limb_alphaW_J8, limb_gammaW_J8]
    exact cw9_out L C h40
  · rw [← hα, limb_alphaW_J8]
    exact tile9_out L C h40
  · rw [coinsCV_J8 δ b χ]
    exact hp_outA L C h40 h1 h2
  · intro t vp ext htab hvp hext hqM hk hprs
    have hq : 2 ^ 63 < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
    exact encInj2_of_outside (withLiftCA R L C).D h10 hq hz
      (inlineAtoms_encZY rfl _ _) htab hvp hext hqM hk hprs

end Bundle

/-! ## 4. `XA9`: the full J-9 A datum at the twin compute walk -/

section Real
open Nock.NockVMROM.Thm54.VclL.Handle.RR49A
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

/-- **`XA9`**: `RR49A.XA` with #1's compute walk at the J-9 A rows (`cw9A`). -/
def XA9 (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Pb : PubJ9A p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3)
    (hL : LayLe (LinkJ8Q1.layPb Pb.toPubJ8 skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (LinkJ8Q1.layPb Pb.toPubJ8 skel hs).nM ≤ 2 ^ 31)
    (hreg9 : (AcceptsJ8P.censusG Pb.toPubJ8 c).length + 6 ≤ 2 ^ 31) (gA gS : Bool) (hN : Pb.n ≤ r.N) :
    DataJ8X (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ9A (ZMod p)) StJ9A r P g :=
  { XA δ b (g := g) R0 L0 Pb c skel hs hL hP hnM hreg9 gA gS with
    C := withLiftCA (RR49A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg9 gA gS) (LL4A δ b L0 Pb skel hs hL gA gS)
      (cw9A (K := K) Pb hN) }


theorem XA9_C (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Pb : PubJ9A p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3)
    (hL : LayLe (LinkJ8Q1.layPb Pb.toPubJ8 skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (LinkJ8Q1.layPb Pb.toPubJ8 skel hs).nM ≤ 2 ^ 31)
    (hreg9 : (AcceptsJ8P.censusG Pb.toPubJ8 c).length + 6 ≤ 2 ^ 31) (gA gS : Bool) (hN : Pb.n ≤ r.N) :
    (XA9 δ b (g := g) R0 L0 Pb c skel hs hL hP hnM hreg9 gA gS hN).C =
      withLiftCA (RR49A δ b (g := g) R0 Pb c skel hs hL hP hnM hreg9 gA gS) (LL4A δ b L0 Pb skel hs hL gA gS)
        (cw9A (K := K) Pb hN) := rfl

/-- **The ε equality**: `XA9`'s list has `ε = boundJ8X` (so `probJ8X_lt_155_optB` applies to `XA9` as is). -/
theorem epsilon_XA9 (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Pb : PubJ9A p) (c : P8PublicClaim) (skel : List Noun) (hs : skel.length ≤ 3)
    (hL : LayLe (LinkJ8Q1.layPb Pb.toPubJ8 skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (LinkJ8Q1.layPb Pb.toPubJ8 skel hs).nM ≤ 2 ^ 31)
    (hreg9 : (AcceptsJ8P.censusG Pb.toPubJ8 c).length + 6 ≤ 2 ^ 31) (gA gS : Bool) (hN : Pb.n ≤ r.N) :
    epsilonOf (allJ8X (XA9 δ b (g := g) R0 L0 Pb c skel hs hL hP hnM hreg9 gA gS hN)) =
      boundJ8X (Fintype.card K) (Fintype.card (Quad (algebraMap (ZMod p) K δ))) r P g :=
  epsilon_allJ8X _

end Real

end

end Nock.NockVMROM.Thm54.VclL.Handle.Out40J9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.Out40J9A
#print axioms stX9_congr
#print axioms rowW9_congr
#print axioms rowsWX9_congr
#print axioms cRows9_eq
#print axioms cw9A
#print axioms outJ9A_of_outside
#print axioms XA9
#print axioms epsilon_XA9
end Axioms
