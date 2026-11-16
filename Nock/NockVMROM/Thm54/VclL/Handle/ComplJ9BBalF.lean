/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BBalF.lean

* root rows: `idx = rIAP p acs node`, every row `ridx = rIAP p acs root` (`ComplJ9BAWR.walkRow0R` at `rIA D`);
  * child handles: the walk column 24 `vRV9` reads the pointer `ptrP` at a cell child (J9BC5A), the weight `WA9` reads
    `chPP`; other children are `hdl acs` (the generator's `HA`), never `hdlP cs acs`;
  * everything else as J-8's `ComplJ8Of` atom-walk part.

  * §1 the J-9 atom-walk part of a run (`vR9 … trVOf9`, `pubsVOf9`), its staging (`stV_run9`), its two pole families
    (`famAWV9`, `famAWH9`), and **`awOK_D9`** (absent / present under `hwalkA`).
  * §2 `balF` at general limbs: the atom-walk reads (`preads_shape9`: comb roots of big atoms of ANY limb count,
    a defined slot of axis `≥ 2`), the exec/spec walk bridge on `(node, side-bit count)` pairs
    (`walkGen_nodeLen_perm`), `mxA_spec9` (the generator's `mxA` at `rIAP` counts the variant rows at `idxRW`),
    **`axT_eq_vxT9`**, and **`balF2_run9`** (the atom / atom-walk clause of `balF`, every coin, binders `hpG`,
    `h31`, `hwalkA` only; no `bigBound_single`, no `hclA`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAWR
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList quadPole ReadsOff)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAWR (idxRW walkRow0R wRowsBR wValsBR wColBR)

noncomputable section

/-! ## 1. The J-9 atom-walk part of a run -/

section AW9
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The J-9 atom-walk root serial** (the generator's `rIAP`: `p`'s comb at its LAST row). -/
abbrev rIA (D : J8Data p Rg fuel s f r) : Noun → ℕ := ComplJ8Data.rIAP p D.acs

/-- The atom-walk fingerprint encoder (J-8's: the plain encoder at the limb coin `zA`). -/
abbrev encA (χ : Coins frameJ8 K) : Noun → Nock.ComputeTable.FP 𝕂′ := GlobalCarryRecognizer.enc (zA δ χ)

/-- **The J-9 honest atom-walk rows at the coin** (`walkRow0R` at `rIA D`). -/
abbrev vR9 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → WalkVals (ZMod p) K 𝕂′ :=
  wRowsBR δ (ChalsAZJ8.chalsAJ8Z δ χ) (encA δ χ) D.acs (rIA D) D.preads

def vxT9 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ k ∈ Finset.range (nVOf D), (walkFillInv δ (γV δ χ) (ρV δ χ) (vR9 δ D χ k)).xInv
def vpT9 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ k ∈ Finset.range (nVOf D), wpTermV δ (walkFillInv δ (γV δ χ) (ρV δ χ) (vR9 δ D χ k))

def pubsV09 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → K := fun i =>
  if D.preads = [] then 0 else if i < 2 then pub2 δ (vxT9 δ D χ) i else if i < 4 then pub2 δ (vpT9 δ D χ) i else 0

abbrev vCol9 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : ℕ → Fin (nVOf D) → ZMod p :=
  wColBR δ b (ChalsAZJ8.chalsAJ8Z δ χ) (encA δ χ) (γV δ χ) (ρV δ χ) D.acs (rIA D) D.preads

/-- **The J-9 child handles**: the generator's `hdl acs` (GLC's finding), not `hdlP cs acs`. -/
abbrev HA (D : J8Data p Rg fuel s f r) : Noun → ℕ × ℕ := Nock.V1J8.Gen.hdl D.acs

def kLV9 (D : J8Data p Rg fuel s f r) : Fin (nVOf D) → ZMod p := fun i => ((HA D (VclL.hdN (vNode D i))).1 : ZMod p)
def vLV9 (D : J8Data p Rg fuel s f r) : Fin (nVOf D) → ZMod p := fun i => ((HA D (VclL.hdN (vNode D i))).2 : ZMod p)
def kRV9 (D : J8Data p Rg fuel s f r) : Fin (nVOf D) → ZMod p := fun i => ((HA D (VclL.tlN (vNode D i))).1 : ZMod p)
/-- **The J-9 walk's right value at the pointer** (J9BC5A, one pointer): a cell tail is keyed by the row's tail pointer
`ptrP p acs rows` (the atom table's `idR`, `colAH_fields`), an atom tail by its value (`hdl`). -/
def vRV9 (D : J8Data p Rg fuel s f r) : Fin (nVOf D) → ZMod p := fun i =>
  if (VclL.tlN (vNode D i)).isCell then ((ComplJ8Data.ptrP p D.acs D.rows (vNode D i) : ℕ) : ZMod p)
  else ((HA D (VclL.tlN (vNode D i))).2 : ZMod p)

abbrev vdN9 (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K)
    (l : List (CoeffExpr (ZMod p))) (j : ℕ) : 𝕂′ :=
  WalkTraceHQ.dN δ (krVOf D) b (nV_pos D) (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsV09 δ D χ) (vCol9 δ b D χ)
    (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D) l j

def vhX9 (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ j ∈ Finset.range (nVOf D), (vdN9 δ b D o χ WalkHC.xKeyH j)⁻¹
def vhP9 (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) : 𝕂′ :=
  ∑ j ∈ Finset.range (nVOf D),
    (liftQ δ (WalkTraceH.cN j (vCol9 δ b D χ WChip.mL)) * (vdN9 δ b D o χ WalkHC.recLH j)⁻¹ +
      liftQ δ (WalkTraceH.cN j (vCol9 δ b D χ WChip.mR)) * (vdN9 δ b D o χ WalkHC.recRH j)⁻¹)

/-- **The J-9 atom walk's publics** (all `0` when absent). -/
def pubsVOf9 (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    ℕ → K := fun i =>
  if D.preads = [] then 0 else
  if i < 4 then pubsV09 δ D χ i else if i < 6 then pub2 δ (vhX9 δ b D o χ) i
  else if i < 8 then pub2 δ (vhP9 δ b D o χ) i else 0

/-- **The J-9 honest atom-walk trace at the coin** (for `BRun9`'s `tr.V`). -/
def trVOf9 (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    Fin 166 → (ZMod p)[X] := fun j =>
  WalkTraceHQ.walkTraceHQ δ (krVOf D) b (nV_pos D) (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsVOf9 δ b D o χ)
    (vCol9 δ b D χ) (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D)
    (Fin.cast (WalkTraceHQ.walkTemplateHQ_width δ (krVOf D)).symm j)

/-- **The J-9 atom part of the run**: the atom table of any `AVPart` with the J-9 atom walk. -/
def avOf9 (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (AV : AVPart p K) : AVPart p K where
  trA := AV.trA
  trV := trVOf9 δ b D (orbJ8 D hF)
  pubsA := AV.pubsA
  pubsV := pubsVOf9 δ b D (orbJ8 D hF)

/-- **The J-9 honest atom-walk trace is staged** (`StJ8`'s `V`). -/
theorem stV_run9 (D : J8Data p Rg fuel s f r) (hF : DvdOK D) :
    StagedCols frameJ8 TraceJ8.crW (fun χ => trVOf9 δ b D (orbJ8 D hF) (K := K) χ) :=
  ComplJ8AW.stV_gen δ b (krVOf D) (nV_pos D) _ (orbJ8 D hF) (fun χ => ChalsAZJ8.chalsAJ8Z δ χ)
    (fun χ => pubsVOf9 δ b D (orbJ8 D hF) χ) (fun χ => vCol9 δ b D χ) (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D)
    (fun χ χ' k hk => ComplJ9BAWR.wColBR_cong δ b _ _ _ _ _ _ _ _ D.acs (rIA D) D.preads k (by omega)
      (fun h => absurd h (by omega)))
    (fun χ χ' hχ k hk => ComplJ9BAWR.wColBR_cong δ b _ _ _ _ _ _ _ _ D.acs (rIA D) D.preads k hk
      (fun _ => by simp only [encA]; rw [zA_round0 δ χ χ' hχ]))

theorem stV_run9' (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (AV : AVPart p K) :
    StagedCols frameJ8 TraceJ8.crW (fun χ => (avOf9 δ b D hF AV).trV χ) :=
  stV_run9 δ b D hF

end AW9

/-! ### The two pole families and `awOK` -/

section AWPoles9
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom (chalsAZ_0 chalsAZ_1 zA_eq)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The J-9 honest atom-walk rows with the walk coins read as coordinates `χ₀ χ₁`. -/
abbrev vRow9 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    ℕ → WalkVals (ZMod p) K (Quad (algebraMap (ZMod p) K δ)) :=
  walkRow0R δ (GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2))) D.acs (rIA D) D.preads
    (χ ⟨0, by decide⟩) (χ ⟨1, by decide⟩)

theorem vR9_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) : vR9 δ D χ = vRow9 δ D χ := by
  simp only [vR9, wRowsBR, encA, chalsAZ_0, chalsAZ_1, zA_eq]

/-- The three J-9 atom-walk validity pole-free parts of row `j`. -/
def awVx9 (D : J8Data p Rg fuel s f r) (j : ℕ) : List (Coins frameJ8 K → Quad (algebraMap (ZMod p) K δ)) :=
  [fun χ => FiniteIO.compress (m := 11) ⟨γV δ χ, 0⟩ (wxKeyV δ (vRow9 δ D χ j)),
   fun χ => FiniteIO.compress (m := 8) ⟨γV δ χ, 0⟩ (wrecLV δ (vRow9 δ D χ j)),
   fun χ => FiniteIO.compress (m := 8) ⟨γV δ χ, 0⟩ (wrecRV δ (vRow9 δ D χ j))]

/-- **The J-9 atom-walk validity pole family.** -/
def famAWV9 (D : J8Data p Rg fuel s f r) : List (BadSpec K) :=
  (List.range (nVOf D)).flatMap fun j => (awVx9 δ D j).map (quadPole δ WeightsJ8.c5)

theorem famAWV9_OK (D : J8Data p Rg fuel s f r) : ∀ e ∈ famAWV9 δ D (K := K), e.OK := by
  intro e he
  obtain ⟨j, -, he⟩ := List.mem_flatMap.mp he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ ?_
  simp only [awVx9, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · intro χ χ' h
    simp only [γV, vRow9, h WeightsJ8.c4 (by decide), h WeightsJ8.c6 (by decide), h cY1 (by decide),
      h cY2 (by decide), h ⟨0, by decide⟩ (by decide), h ⟨1, by decide⟩ (by decide)]

theorem famAWV9_good (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K)
    (hg : ∀ e ∈ famAWV9 δ D (K := K), χ ∉ e.ev) : ∀ j < nVOf D,
      FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (vRow9 δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecLV δ (vRow9 δ D χ j)) ≠ 0 ∧
      FiniteIO.compress (m := 8) ⟨γV δ χ, ρV δ χ⟩ (wrecRV δ (vRow9 δ D χ j)) ≠ 0 := by
  intro j hj
  have hx : ∀ x ∈ awVx9 δ D j (K := K), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7) + x χ ≠ 0 := by
    intro x hx
    refine ComplJ8Bad.quadPole_ne_mk δ _ x χ _ (hg _ ?_)
    exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  simp only [awVx9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [InhabJ8Good.compress_split]; exact h1
  · rw [InhabJ8Good.compress_split]; exact h2
  · rw [InhabJ8Good.compress_split]; exact h3

/-- The J-9 honest atom-walk values with coordinate coins. -/
abbrev vValsC9 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    Fin (nVOf D) → WalkVals (ZMod p) K (Quad (algebraMap (ZMod p) K δ)) :=
  fun i => walkFill δ (γV δ χ) (ρV δ χ) (vRow9 δ D χ) i

/-- The three J-9 atom-walk handle pole-free parts of row `j`. -/
def awHx9 (D : J8Data p Rg fuel s f r) (j : ℕ) : List (Coins frameJ8 K → Quad (algebraMap (ZMod p) K δ)) :=
  if hj : j < nVOf D then
    [fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ ⟨j, hj⟩).idx, (kLV9 D ⟨j, hj⟩, vLV9 D ⟨j, hj⟩),
        (kRV9 D ⟨j, hj⟩, vRV9 D ⟨j, hj⟩)),
     fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ ⟨j, hj⟩).ridx, 2 * (vValsC9 δ D χ ⟨j, hj⟩).pre,
        (kLV9 D ⟨j, hj⟩, vLV9 D ⟨j, hj⟩)),
     fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ ⟨j, hj⟩).ridx, 2 * (vValsC9 δ D χ ⟨j, hj⟩).pre + 1,
        (kRV9 D ⟨j, hj⟩, vRV9 D ⟨j, hj⟩))]
  else []

/-- **The J-9 atom-walk handle pole family.** -/
def famAWH9 (D : J8Data p Rg fuel s f r) : List (BadSpec K) :=
  (List.range (nVOf D)).flatMap fun j => (awHx9 δ D j).map (quadPole δ InhabJ8Good.c12)

theorem famAWH9_OK (D : J8Data p Rg fuel s f r) : ∀ e ∈ famAWH9 δ D (K := K), e.OK := by
  intro e he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  refine ComplJ8Bad.quadPole_OK δ _ _ ?_
  have hj' := List.mem_range.mp hj
  simp only [awHx9, dif_pos hj', List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · intro χ χ' h
    have hγ : ComplJ8Bad.γH δ χ = ComplJ8Bad.γH δ χ' := ComplJ8Bad.γH_readsOff δ χ χ' h
    simp only [hγ, vValsC9, γV, ρV, vRow9, h WeightsJ8.c4 (by decide), h WeightsJ8.c5 (by decide),
      h WeightsJ8.c6 (by decide), h WeightsJ8.c7 (by decide), h cY1 (by decide), h cY2 (by decide),
      h ⟨0, by decide⟩ (by decide), h ⟨1, by decide⟩ (by decide)]

theorem vVals9_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    wValsBR (n := nVOf D) δ (chalsAJ8Z δ χ) (encA δ χ) (γV δ χ) (ρV δ χ) D.acs (rIA D) D.preads =
      vValsC9 δ D χ := by
  unfold wValsBR
  rw [show wRowsBR δ (chalsAJ8Z δ χ) (encA δ χ) D.acs (rIA D) D.preads = vR9 δ D χ from rfl, vR9_eq]

variable (b : Basis (Fin 3) (ZMod p) K)

/-- **The three J-9 atom-walk handle denominators split** as `ρH + (pole-free part)` at any publics. -/
theorem aw_dRow_split9 (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) (χ : Coins frameJ8 K) (pubs : ℕ → K) (i : Fin (nVOf D)) :
    WalkTraceHQ.dRow δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o (chalsAJ8Z δ χ) pubs
        WalkHC.xKeyH (vCol9 δ b D χ) (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D) i =
      ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ i).idx, (kLV9 D i, vLV9 D i),
        (kRV9 D i, vRV9 D i)) ∧
    WalkTraceHQ.dRow δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o (chalsAJ8Z δ χ) pubs
        WalkHC.recLH (vCol9 δ b D χ) (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D) i =
      ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ i).ridx, 2 * (vValsC9 δ D χ i).pre,
        (kLV9 D i, vLV9 D i)) ∧
    WalkTraceHQ.dRow δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o (chalsAJ8Z δ χ) pubs
        WalkHC.recRH (vCol9 δ b D χ) (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D) i =
      ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ i).ridx, 2 * (vValsC9 δ D χ i).pre + 1,
        (kRV9 D i, vRV9 D i)) := by
  obtain ⟨e1, e2, e3⟩ := FrameVSQ.walk_dRowQ_vals δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o
    (chalsAJ8Z δ χ) pubs (wValsBR δ (chalsAJ8Z δ χ) (encA δ χ) (γV δ χ) (ρV δ χ) D.acs (rIA D) D.preads)
    (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D) hinj i
  have hρ : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 34) (chalsAJ8Z δ χ 36) = ComplJ8Bad.ρH δ χ := by
    rw [ChalsAZJ8.chalsAJ8Z_agree δ χ 34 (by norm_num) (by norm_num),
      ChalsAZJ8.chalsAJ8Z_agree δ χ 36 (by norm_num) (by norm_num), chals_34, chals_36]; rfl
  have hγ : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 33) (chalsAJ8Z δ χ 35) = ComplJ8Bad.γH δ χ := by
    rw [ChalsAZJ8.chalsAJ8Z_agree δ χ 33 (by norm_num) (by norm_num),
      ChalsAZJ8.chalsAJ8Z_agree δ χ 35 (by norm_num) (by norm_num), chals_33, chals_35]; rfl
  rw [hρ, hγ, vVals9_eq] at e1 e2 e3
  exact ⟨e1.trans (recDen_split δ _ _ _), e2.trans (recDenP_split δ _ _ _), e3.trans (recDenP_split δ _ _ _)⟩

theorem aw_dN_pubs9 (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) (χ : Coins frameJ8 K)
    (pubs pubs' : ℕ → K) (l : List (CoeffExpr (ZMod p))) (hl : l = WalkHC.xKeyH ∨ l = WalkHC.recLH ∨ l = WalkHC.recRH)
    (j : ℕ) :
    WalkTraceHQ.dN δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o (chalsAJ8Z δ χ) pubs
      (vCol9 δ b D χ) (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D) l j =
    WalkTraceHQ.dN δ (krW D.acs D.preads) b (nV_pos D) (powN o _) o (chalsAJ8Z δ χ) pubs'
      (vCol9 δ b D χ) (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D) l j := by
  unfold WalkTraceHQ.dN
  split_ifs with hj
  · have e := aw_dRow_split9 δ b D o hinj χ pubs ⟨j, hj⟩
    have e' := aw_dRow_split9 δ b D o hinj χ pubs' ⟨j, hj⟩
    rcases hl with rfl | rfl | rfl
    · rw [e.1, e'.1]
    · rw [e.2.1, e'.2.1]
    · rw [e.2.2, e'.2.2]
  · rfl

/-- The generator's child-handle kinds are in `{0, 1, 2}`. -/
theorem hdlA_kind (cs : List Noun) (x : Noun) :
    ((Nock.V1J8.Gen.hdl cs x).1 : ZMod p) = 0 ∨ ((Nock.V1J8.Gen.hdl cs x).1 : ZMod p) = 1 ∨
      ((Nock.V1J8.Gen.hdl cs x).1 : ZMod p) = 2 := by
  cases x with
  | atom v => by_cases hv : v < Nock.Field.p <;> simp [Nock.V1J8.Gen.hdl, hv]
  | cell a c => simp [Nock.V1J8.Gen.hdl]

/-- `rIAP` is at most the atom-cell count. -/
theorem rIA_le (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) : ∀ n, rIA D n ≤ D.acs.length := by
  intro n
  have hne : D.acs ≠ [] := List.ne_nil_of_length_pos hA
  simp only [rIA, ComplJ8Data.rIAP]
  split_ifs
  · exact (ComplJ8Data.lastIdxOf_lt _ _ hne).le
  · unfold Nock.V1J8.Gen.idxN
    split
    · exact (ComplJ8Data.idxOf_lt_of_ne _ _ hne).le
    · exact le_rfl

end AWPoles9


section AWRun9
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom (chalsAZ_0 chalsAZ_1 zA_eq)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **The J-9 atom walk at a coin outside its two pole families** (`awOK` for `BRun9`), for any run data `D`: absent (`preads = []`) by `awOK_absent`, present by `awOK_list` under `hwalkA`. -/
theorem awOK_D9 (D : J8Data p Rg fuel s f r) (hF : DvdOK D) (hp63 : 2 ^ 63 < p)
    (h31 : ∀ x ∈ sizesJ8 D, x ≤ 2 ^ 31) (hwalkA : ComplJ8Walk.WalkDepthOK D.preads)
    (hA : 0 < D.acs.length)
    (χ : Coins frameJ8 K) (hgV : ∀ e ∈ famAWV9 δ D (K := K), χ ∉ e.ev)
    (hgH : ∀ e ∈ famAWH9 δ D (K := K), χ ∉ e.ev) :
    AWChipOK δ b (krVOf D) (nV_pos D) (powN (orbJ8 D hF) (nVOf D)) (orbJ8 D hF) (chalsAJ8Z δ χ)
      (pubsVOf9 δ b D (orbJ8 D hF) χ)
      (fun j => trVOf9 δ b D (orbJ8 D hF) χ
        (Fin.cast (CellTwinK.walkChipHQK_width δ (krVOf D) b (nV_pos D) _ _ _ _) j)) := by
  by_cases h0 : D.preads = []
  · refine ComplJ8AW.awOK_absent δ b (krVOf D) (nV_pos D) _ _ _ _ (by simp [krVOf, h0]) _ ?_
    simp [pubsVOf9, h0]
  have hk : krVOf D = krW D.acs D.preads := by simp [krVOf, h0]
  have hN : nVOf D = (walkRows D.acs D.preads).length := by simp [nVOf, h0]
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 D hF) (le_two_pow_ht D hmV)
  have hcells : D.acs.length < ringChar (ZMod p) := by
    have := h31 _ hmA; have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; omega
  have hkp : krW D.acs D.preads + (walkRows D.acs D.preads).length < ringChar (ZMod p) := by
    have h1 := h31 _ hmV
    have h2 := krW_le_rows D.acs D.preads
    have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; rw [hN] at h1; omega
  have hrows := famAWV9_good δ D χ hgV
  have hpoleH : ∀ (i : Fin (nVOf D)), ∀ x ∈ awHx9 δ D i (K := K), ComplJ8Bad.ρH δ χ + x χ ≠ 0 := by
    intro i x hx
    refine ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 x χ _ (ComplJ8Bad.ρH_re δ χ) (hgH _ ?_)
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hsplit := aw_dRow_split9 δ b D (orbJ8 D hF) hinj χ (pubsVOf9 δ b D (orbJ8 D hF) χ)
  have hP : ∀ i, pubsVOf9 δ b D (orbJ8 D hF) χ i =
      if i < 4 then pubsV09 δ D χ i else if i < 6 then pub2 δ (vhX9 δ b D (orbJ8 D hF) χ) i
      else if i < 8 then pub2 δ (vhP9 δ b D (orbJ8 D hF) χ) i else 0 := by
    intro i; simp only [pubsVOf9, if_neg h0]
  have hP0 : ∀ i, pubsV09 δ D χ i =
      if i < 2 then pub2 δ (vxT9 δ D χ) i else if i < 4 then pub2 δ (vpT9 δ D χ) i else 0 := by
    intro i; simp only [pubsV09, if_neg h0]
  have qx : ∀ i, i < 2 → pubsVOf9 δ b D (orbJ8 D hF) χ i = pub2 δ (vxT9 δ D χ) i := by
    intro i hi; rw [hP, if_pos (show i < 4 by omega), hP0, if_pos hi]
  have qp : ∀ i, 2 ≤ i → i < 4 → pubsVOf9 δ b D (orbJ8 D hF) χ i = pub2 δ (vpT9 δ D χ) i := by
    intro i h1 h2; rw [hP, if_pos h2, hP0, if_neg (show ¬ i < 2 by omega), if_pos h2]
  have qhx : ∀ i, 4 ≤ i → i < 6 → pubsVOf9 δ b D (orbJ8 D hF) χ i = pub2 δ (vhX9 δ b D (orbJ8 D hF) χ) i := by
    intro i h1 h2; rw [hP, if_neg (show ¬ i < 4 by omega), if_pos h2]
  have qhp : ∀ i, 6 ≤ i → i < 8 → pubsVOf9 δ b D (orbJ8 D hF) χ i = pub2 δ (vhP9 δ b D (orbJ8 D hF) χ) i := by
    intro i h1 h2; rw [hP, if_neg (show ¬ i < 4 by omega), if_neg (show ¬ i < 6 by omega), if_pos h2]
  have hres := ComplJ9BAWR.awOK_listR δ b (nV_pos D) (powN (orbJ8 D hF) (nVOf D)) (orbJ8 D hF) (chalsAJ8Z δ χ)
    (pubsVOf9 δ b D (orbJ8 D hF) χ) (encA δ χ) (γV δ χ) (ρV δ χ) D.acs (rIA D) D.preads (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D)
    (by rw [hrc]; exact hp63) hcells (rIA_le D hA) hwalkA hkp hN hinj hadj (ChalsAZJ8.chalsAJ8Z_ok δ χ)
    (fun j hj => by rw [show wRowsBR δ (chalsAJ8Z δ χ) (encA δ χ) D.acs (rIA D) D.preads = vR9 δ D χ from rfl, vR9_eq]; exact (hrows j hj).1) (fun j hj => by rw [show wRowsBR δ (chalsAJ8Z δ χ) (encA δ χ) D.acs (rIA D) D.preads = vR9 δ D χ from rfl, vR9_eq]; exact (hrows j hj).2.1)
    (fun j hj => by rw [show wRowsBR δ (chalsAJ8Z δ χ) (encA δ χ) D.acs (rIA D) D.preads = vR9 δ D χ from rfl, vR9_eq]; exact (hrows j hj).2.2)
    (by
      rw [qx 0 (by norm_num), qx 1 (by norm_num), pub2_mk2 δ _ 0 rfl]
      rfl)
    (by
      rw [qp 2 (by norm_num) (by norm_num), qp 3 (by norm_num) (by norm_num), pub2_mk2 δ _ 2 rfl]
      rfl)
    (fun i => hdlA_kind _ _) (fun i => hdlA_kind _ _)
    (fun i => by
      rw [(hsplit i).1]
      exact hpoleH i (fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ i).idx, (kLV9 D i, vLV9 D i),
        (kRV9 D i, vRV9 D i))) (by simp only [awHx9, dif_pos i.isLt]; exact List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.1]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ i).ridx, 2 * (vValsC9 δ D χ i).pre,
        (kLV9 D i, vLV9 D i))) (by simp only [awHx9, dif_pos i.isLt]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.2]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((vValsC9 δ D χ i).ridx, 2 * (vValsC9 δ D χ i).pre + 1,
        (kRV9 D i, vRV9 D i))) (by
          simp only [awHx9, dif_pos i.isLt]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (by
      show Quad.mk _ (pubsVOf9 δ b D (orbJ8 D hF) χ 4) (pubsVOf9 δ b D (orbJ8 D hF) χ 5) = _
      rw [qhx 4 (by norm_num) (by norm_num), qhx 5 (by norm_num) (by norm_num), pub2_mk2 δ _ 4 rfl]
      unfold vhX9
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold vdN9
      rw [hk, aw_dN_pubs9 δ b D (orbJ8 D hF) hinj χ (pubsV09 δ D χ) (pubsVOf9 δ b D (orbJ8 D hF) χ) _ (Or.inl rfl)])
    (by
      show Quad.mk _ (pubsVOf9 δ b D (orbJ8 D hF) χ 6) (pubsVOf9 δ b D (orbJ8 D hF) χ 7) = _
      rw [qhp 6 (by norm_num) (by norm_num), qhp 7 (by norm_num) (by norm_num), pub2_mk2 δ _ 6 rfl]
      unfold vhP9
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold vdN9
      rw [hk, aw_dN_pubs9 δ b D (orbJ8 D hF) hinj χ (pubsV09 δ D χ) (pubsVOf9 δ b D (orbJ8 D hF) χ) _
          (Or.inr (Or.inl rfl)),
        aw_dN_pubs9 δ b D (orbJ8 D hF) hinj χ (pubsV09 δ D χ) (pubsVOf9 δ b D (orbJ8 D hF) χ) _ (Or.inr (Or.inr rfl))])
  unfold trVOf9
  rw [hk]
  exact hres

end AWRun9

/-! ## 2. `balF` at general limbs -/

section CombFD
open Nock.GlobalCarryAxis (headOpt tailOpt slot_double slot_double_succ)
open Nock.V1J8.Gen (combOf)

theorem combOf_cons3 (x x1 x2 : ℕ) (xs : List ℕ) :
    combOf (x :: x1 :: x2 :: xs) = .cell (.atom x) (combOf (x1 :: x2 :: xs)) := rfl

/-- **The first-difference axis of two combs is a defined slot of both** (any limb counts `≥ 2`), and `≥ 2`. -/
theorem combFD_slot (sxa sxb : ℕ → ℕ) : ∀ (xs ys : List ℕ) (d ax : ℕ) (n n' : Noun), 1 ≤ ax →
    2 ≤ xs.length → 2 ≤ ys.length → Noun.slot ax n = some (combOf xs) → Noun.slot ax n' = some (combOf ys) →
    2 ≤ (HonestPairX.combFD sxa sxb d ax xs ys).1 ∧
      (Noun.slot (HonestPairX.combFD sxa sxb d ax xs ys).1 n).isSome ∧
      (Noun.slot (HonestPairX.combFD sxa sxb d ax xs ys).1 n').isSome
  | [x, x'], [y, y'], d, ax, n, n', hax, _, _, hn, hn' => by
    simp only [HonestPairX.combFD]
    split_ifs <;> refine ⟨by omega, ?_, ?_⟩ <;>
      simp [slot_double, slot_double_succ, hax, hn, hn', combOf, headOpt, tailOpt]
  | [x, x'], y :: y1 :: y2 :: ys, d, ax, n, n', hax, _, _, hn, hn' => by
    simp only [HonestPairX.combFD]
    split_ifs <;> refine ⟨by omega, ?_, ?_⟩ <;>
      simp [slot_double, slot_double_succ, hax, hn, hn', combOf, combOf_cons3, headOpt, tailOpt]
  | x :: x1 :: x2 :: xs, [y, y'], d, ax, n, n', hax, _, _, hn, hn' => by
    simp only [HonestPairX.combFD]
    split_ifs <;> refine ⟨by omega, ?_, ?_⟩ <;>
      simp [slot_double, slot_double_succ, hax, hn, hn', combOf, combOf_cons3, headOpt, tailOpt]
  | x :: x1 :: x2 :: xs, y :: y1 :: y2 :: ys, d, ax, n, n', hax, _, _, hn, hn' => by
    simp only [HonestPairX.combFD]
    split_ifs with h
    · have h1 : Noun.slot (2 * ax + 1) n = some (combOf (x1 :: x2 :: xs)) := by
        rw [slot_double_succ _ hax, hn, combOf_cons3]; rfl
      have h2 : Noun.slot (2 * ax + 1) n' = some (combOf (y1 :: y2 :: ys)) := by
        rw [slot_double_succ _ hax, hn', combOf_cons3]; rfl
      exact combFD_slot sxa sxb (x1 :: x2 :: xs) (y1 :: y2 :: ys) (d + 1) (2 * ax + 1) n n' (by omega)
        (by simp) (by simp) h1 h2
    · refine ⟨by omega, ?_, ?_⟩ <;>
        simp [slot_double, slot_double_succ, hax, hn, hn', combOf_cons3, headOpt]
  | [], _, _, _, _, _, _, h, _, _, _ => by simp at h
  | [_], _, _, _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _ :: _, [], _, _, _, _, _, _, h, _, _ => by simp at h
  | _ :: _ :: _, [_], _, _, _, _, _, _, h, _, _ => by simp at h

end CombFD

section Reads9
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
variable {p : ℕ} [Fact p.Prime] [Fact (ringChar (ZMod p)).Prime] {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **The atom-walk reads at general limbs**: the comb of a big atom of the run (any limb count), at an axis `≥ 2`
that is a defined slot of the comb. -/
theorem preads_shape9 (hpG : p = Nock.Atoms.p) :
    ∀ x ∈ (j8DataOf p Rg Rt hgen).preads, ∃ a ∈ (j8DataOf p Rg Rt hgen).bigs,
      x.1 = Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) ∧ 2 ≤ x.2 ∧ (Noun.slot x.2 x.1).isSome := by
  set D := j8DataOf p Rg Rt hgen with hD
  intro x hx
  have hx' : x ∈ ComplJ8Data.pairReadsP D.H D.pd D.rows := hx
  unfold ComplJ8Data.pairReadsP at hx'
  obtain ⟨row, hrow, hx'⟩ := List.mem_flatMap.mp hx'
  split_ifs at hx' with hpair
  swap
  · simp at hx'
  simp only [Nock.V1J8.FillX.isPairB, Bool.and_eq_true, decide_eq_true_eq] at hpair
  obtain ⟨⟨⟨-, -⟩, h1⟩, h2⟩ := hpair
  have hkind : ∀ n : Noun, n ∈ rowHandleNounsX row → (D.H n).1 = 2 →
      ∃ a, n = .atom a ∧ a ∈ D.bigs ∧ p ≤ a := by
    intro n hn hk
    have hH : D.H = ComplJ8Data.hdlP p D.cells D.acs := rfl
    rw [hH] at hk
    cases n with
    | cell l r' => simp [ComplJ8Data.hdlP] at hk
    | atom a =>
      have hpa : p ≤ a := by
        by_contra hlt
        simp [ComplJ8Data.hdlP, show a < p by omega] at hk
      refine ⟨a, rfl, ?_, hpa⟩
      show a ∈ ComplJ8Data.bigsP p D.roots D.rows
      refine (ComplJ8Atom.mem_bigsP p _ _ a).mpr ⟨?_, hpa⟩
      refine List.mem_flatMap.mpr ⟨.atom a, List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, hrow, hn⟩), ?_⟩
      simp [leavesOf]
  obtain ⟨a, ha', ha, hpa⟩ := hkind row.ftth (by simp [rowHandleNounsX]) h1
  obtain ⟨c, hc', hc, hpc⟩ := hkind row.fttt (by simp [rowHandleNounsX]) h2
  have hBp : Nock.Atoms.B ≤ p := by rw [hpG]; exact Nock.Atoms.B_lt_p.le
  have hla := HonestPairX.two_le_length_limbs (a := a) (by omega)
  have hlc := HonestPairX.two_le_length_limbs (a := c) (by omega)
  have hpd : (D.pd row).1 = (HonestPairX.combFD (ComplJ8Data.sxPP p D.acs D.rows a) (ComplJ8Data.sxPP p D.acs D.rows c) 0 1
      (Nock.Atoms.limbs a) (Nock.Atoms.limbs c)).1 := by
    have e : D.pd row = HonestPairX.pdX (ComplJ8Data.sxPP p D.acs D.rows) row := rfl
    rw [e]; unfold HonestPairX.pdX; rw [ha', hc']
  obtain ⟨hge, hsa, hsc⟩ := combFD_slot (ComplJ8Data.sxPP p D.acs D.rows a) (ComplJ8Data.sxPP p D.acs D.rows c)
    (Nock.Atoms.limbs a) (Nock.Atoms.limbs c) 0 1 (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a))
    (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c)) le_rfl hla hlc
    (by simp [Noun.slot]) (by simp [Noun.slot])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl
  · refine ⟨a, ha, by rw [ha']; rfl, ?_, ?_⟩
    · show 2 ≤ (D.pd row).1; rw [hpd]; exact hge
    · show (Noun.slot (D.pd row).1 (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV row.ftth)))).isSome
      rw [hpd, ha']; exact hsa
  · refine ⟨c, hc, by rw [hc']; rfl, ?_, ?_⟩
    · show 2 ≤ (D.pd row).1; rw [hpd]; exact hge
    · show (Noun.slot (D.pd row).1 (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV row.fttt)))).isSome
      rw [hpd, hc']; exact hsc

/-- **Every J-9 spec atom-walk node is an atom cell** (general limbs; binder `hpG` only). -/
theorem awNodes_mem9 (hpG : p = Nock.Atoms.p) :
    ∀ u ∈ walkRows (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).preads,
      u.label.node ∈ (j8DataOf p Rg Rt hgen).acs := by
  have hsh := preads_shape9 Rt hgen hpG
  refine walkRows_nodes_mem _ _ (List.ne_nil_of_length_pos (acs_pos (p := p) Rt hgen))
    (acs_closed_run Rt hgen hpG) ?_
  intro x hx _
  obtain ⟨a, ha, h1, -, h3⟩ := hsh x hx
  have hBp : Nock.Atoms.B ≤ p := by rw [hpG]; exact Nock.Atoms.B_lt_p.le
  have hpa : p ≤ a := by
    have : a ∈ ComplJ8Data.bigsP p (j8DataOf p Rg Rt hgen).roots (j8DataOf p Rg Rt hgen).rows := ha
    exact ((ComplJ8Atom.mem_bigsP p _ _ a).mp this).2
  exact ⟨h1 ▸ comb_mem_acs Rt hgen hpG ha (HonestPairX.two_le_length_limbs (by omega)), h3⟩

end Reads9


/-! ### The exec / spec walk bridge on `(node, side-bit count)` pairs -/

section WalkBridge9
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal

theorem nodeLen_eq {k : ℕ} {u : Nock.V1J8.Gen.TN} {t : NTree WN} (h : CorrK k u t) :
    (u.label.node, u.label.len) = (t.label.node, t.label.bits.length) := by
  obtain ⟨R, n, pre, bs, T, rfl, rfl, -⟩ := h
  cases n <;> rfl

theorem forall₂_map_nodeLen {k : ℕ} : ∀ {l : List Nock.V1J8.Gen.TN} {l' : List (NTree WN)},
    List.Forall₂ (CorrK k) l l' →
      (l.map fun u => (u.label.node, u.label.len)) = l'.map fun t => (t.label.node, t.label.bits.length)
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [List.map_cons, nodeLen_eq h, forall₂_map_nodeLen hs]

/-- **The executable BFS is the spec BFS on nodes** once the fuel exceeds the target depth. -/
theorem bfsTN_nodeLen : ∀ (k m : ℕ), k + 1 ≤ m → ∀ (l : List Nock.V1J8.Gen.TN) (l' : List (NTree WN)),
    List.Forall₂ (CorrK k) l l' →
    ((Nock.V1J8.Gen.bfsTN m l).map fun w => (w.node, w.len)) = (bfsForest l').map fun t => (t.label.node, t.label.bits.length)
  | k, 0, hm, _, _, _ => by omega
  | k, m + 1, hm, [], l', h => by
    cases h; simp [Nock.V1J8.Gen.bfsTN, bfsForest]
  | k, m + 1, hm, u :: us, l', h => by
    cases h with
    | cons hu hus =>
      rename_i t ts
      rw [bfsForest]
      simp only [Nock.V1J8.Gen.bfsTN, List.map_append, List.map_map]
      have hnodes := forall₂_map_nodeLen (List.Forall₂.cons hu hus)
      have e1 : ((u :: us).map fun x => ((Nock.V1J8.Gen.TN.label x).node, (Nock.V1J8.Gen.TN.label x).len)) =
          (List.map ((fun w => (w.node, w.len)) ∘ Nock.V1J8.Gen.TN.label) (u :: us)) := rfl
      rw [← e1, hnodes]
      congr 1
      cases k with
      | zero =>
        have hk : ((u :: us).flatMap Nock.V1J8.Gen.TN.kids) = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro x hx
          obtain ⟨y, hy⟩ := f2_left (List.Forall₂.cons hu hus) x hx
          exact (kids_nil0 hy).1
        have hk' : ((t :: ts).flatMap NTree.children) = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro x hx
          obtain ⟨y, hy⟩ := f2_right (List.Forall₂.cons hu hus) x hx
          exact (kids_nil0 hy).2
        rw [hk, hk']
        cases m <;> simp [Nock.V1J8.Gen.bfsTN, bfsForest]
      | succ k =>
        exact bfsTN_nodeLen k m (by omega) _ _
          (forall₂_flatMap (fun a b hab => kids_corr hab) (List.Forall₂.cons hu hus))

/-- **The executable and the spec walk rows have the same `(node, side-bit count)` pairs, up to order** (all reads path-kind,
depth `≤ 62`). -/
theorem walkGen_nodeLen_perm (cells : List Noun) (rs : List (Noun × ℕ))
    (hall : ∀ x ∈ rs, VclL.isPathAx x.2 = true) (h62 : ∀ r ∈ VclL.pathReads rs, VclL.depthOf r.2 ≤ 62) :
    ((Nock.V1J8.Gen.walkGen (cells.headD (.atom 0)) rs).1.map fun w => (w.node, w.len)).Perm
      ((walkRows cells rs).map fun t => (t.label.node, t.label.bits.length)) := by
  set dummy := cells.headD (.atom 0)
  set roots := rs.foldl (fun acc p => if p.1 ∈ acc then acc else acc ++ [p.1]) [] with hroots
  have hgs : Nock.V1J8.Gen.groupReads rs =
      roots.map fun r => (r, (rs.filter fun p => p.1 = r).map fun p => Nock.V1J8.Gen.axisBits p.2) := rfl
  have hperm := groupRoots_perm rs
  rw [← hroots] at hperm
  have hwr : walkRoots rs = (rs.map Prod.fst).dedup := by unfold walkRoots; rw [pathKind_of_all hall]
  -- the spec forest built from the exec roots
  let fs : List (NTree WN) := if roots = [] then [GenWalk.trie dummy dummy [] []]
    else roots.map fun r => GenWalk.trie r r [] (targetsOf rs r)
  have hfe : List.Forall₂ (CorrK 62)
      (if (Nock.V1J8.Gen.groupReads rs).isEmpty then [Nock.V1J8.Gen.trie dummy dummy 1 0 []]
        else (Nock.V1J8.Gen.groupReads rs).map fun g => Nock.V1J8.Gen.trie g.1 g.1 1 0 g.2) fs := by
    rw [hgs]
    by_cases h0 : roots = []
    · simp only [fs, h0, List.map_nil, List.isEmpty_nil, if_true]
      exact List.Forall₂.cons ⟨dummy, dummy, 1, [], [], rfl, rfl, by simp⟩ List.Forall₂.nil
    · have he : (roots.map fun r => (r, (rs.filter fun p => p.1 = r).map fun p => Nock.V1J8.Gen.axisBits p.2)).isEmpty
          = false := by simpa using h0
      simp only [fs, h0, he, if_false, Bool.false_eq_true, List.map_map]
      clear he hperm hroots h0
      induction roots with
      | nil => exact List.Forall₂.nil
      | cons r rt ih =>
        refine List.Forall₂.cons ⟨r, r, 1, [], targetsOf rs r, ?_, rfl, ?_⟩ ?_
        · simp only [List.map_cons, Function.comp_apply, targets_eq hall]; rfl
        · intro s hs
          have := (targetsOf_depth h62 r).2 s hs
          simp at this; omega
        · exact ih
  have hlist := bfsTN_nodeLen 62 70 (by norm_num) _ _ hfe
  have hws : (Nock.V1J8.Gen.walkGen dummy rs).1 = Nock.V1J8.Gen.bfsTN 70
      (if (Nock.V1J8.Gen.groupReads rs).isEmpty then [Nock.V1J8.Gen.trie dummy dummy 1 0 []]
        else (Nock.V1J8.Gen.groupReads rs).map fun g => Nock.V1J8.Gen.trie g.1 g.1 1 0 g.2) := rfl
  rw [hws, hlist]
  refine List.Perm.map _ (bfsForest_perm_of_perm ?_)
  unfold walkForest
  rw [hwr]
  by_cases h0 : roots = []
  · have : (rs.map Prod.fst).dedup = [] := List.Perm.eq_nil (hperm.symm.trans (by rw [h0]))
    simp only [fs, h0, this, if_true]; exact List.Perm.refl _
  · have h1 : (rs.map Prod.fst).dedup ≠ [] := fun e => h0 (List.Perm.eq_nil (hperm.trans (by rw [e])))
    simp only [fs, h0, h1, if_false]
    exact hperm.map _


end WalkBridge9


/-! ### The atom export terminal against the J-9 atom-walk import terminal -/

section SumAtW
/-- The generator's walk-row serial on a `(node, side-bit count)` pair (`GenAtom.wIdx`). -/
def gI (rI : Noun → ℕ) (cs : List Noun) (q : Noun × ℕ) : ℕ :=
  if q.2 = 0 then rI q.1 else Nock.V1J8.Gen.idxN cs q.1

theorem sumAt_wPairs (rI : Noun → ℕ) (cs : List Noun) (j : ℕ) : ∀ ws : List Nock.V1J8.Gen.WRow,
    ComplJ8Data.sumAt (ComplJ8Data.wPairs rI cs ws) j =
      ((ws.map fun w => (w.node, w.len)).filter fun q => q.1.isCell && decide (gI rI cs q = j)).length
  | [] => rfl
  | w :: ws => by
    have ih := sumAt_wPairs rI cs j ws
    have hwi : Nock.V1J8.Gen.wIdx rI cs w = gI rI cs (w.node, w.len) := rfl
    rcases hw : w.node with v | ⟨a, c⟩
    · simp only [ComplJ8Data.wPairs, List.filterMap_cons, hw, List.map_cons, List.filter_cons, Noun.isCell,
        Bool.false_and, Bool.false_eq_true, if_false] at ih ⊢
      exact ih
    · simp only [ComplJ8Data.wPairs, List.filterMap_cons, hw, List.map_cons, List.filter_cons, Noun.isCell,
        Bool.true_and] at ih ⊢
      rw [hwi, hw]
      rw [ComplJ8Data.sumAt, List.filter_cons] at *
      by_cases h : gI rI cs (.cell a c, w.len) = j
      · simp [h] at ih ⊢; omega
      · simp [h] at ih ⊢; exact ih
end SumAtW

section BalF9
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The atom export multiplicity counts the J-9 spec atom-walk rows at the generator's serial** (`rIAP` on root
rows, `idxN` elsewhere; no `rIAP = idxN`, no limb count). -/
theorem mxA_spec9 (hne : (j8DataOf p Rg Rt hgen).preads ≠ [])
    (hall : ∀ x ∈ (j8DataOf p Rg Rt hgen).preads, VclL.isPathAx x.2 = true)
    (h62 : ∀ r ∈ VclL.pathReads (j8DataOf p Rg Rt hgen).preads, VclL.depthOf r.2 ≤ 62) (j : ℕ)
    (hj : j < (j8DataOf p Rg Rt hgen).acs.length) :
    (j8DataOf p Rg Rt hgen).mxA.getD j 0 =
      ((walkRows (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).preads).filter fun t =>
        t.label.node.isCell &&
          decide (gI (rIA (j8DataOf p Rg Rt hgen)) (j8DataOf p Rg Rt hgen).acs
            (t.label.node, t.label.bits.length) = j)).length := by
  rw [ComplJ8Data.mxA_eq_cnt p Rg Rt hgen j hj, ComplJ8Data.cnt_eq_sumAt]
  simp only [ComplJ8Data.awRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [sumAt_wPairs, vs_eq Rt hgen hne]
  have hperm := walkGen_nodeLen_perm (j8DataOf p Rg Rt hgen).acs _ hall h62
  rw [(hperm.filter _).length_eq, List.filter_map, List.length_map]
  rfl

omit [Fact p.Prime] in
theorem getD_lastIdxOf (l : List Noun) (n : Noun) (h : n ∈ l) :
    l.getD (Nock.V1J8.Gen.lastIdxOf l n) (.atom 0) = n := by
  rw [List.getD_eq_getElem?_getD, ComplJ8Atom.lastIdxOf_mem l n h]; rfl

/-- The J-9 row serial of an atom-cell node of the spec walk reads that node back, and is in range. -/
theorem idxRW_facts (D : J8Data p Rg fuel s f r) (u : NTree WN) (hm : u.label.node ∈ D.acs)
    (hc : u.label.node.isCell = true) :
    D.acs.getD (idxRW D.acs (rIA D) u) (.atom 0) = u.label.node ∧ idxRW D.acs (rIA D) u < D.acs.length ∧
      gI (rIA D) D.acs (u.label.node, u.label.bits.length) = idxRW D.acs (rIA D) u := by
  have hidxN : Nock.V1J8.Gen.idxN D.acs u.label.node = D.acs.idxOf u.label.node := by
    obtain ⟨a, c, e⟩ : ∃ a c, u.label.node = .cell a c := by
      cases h : u.label.node with
      | atom v => rw [h] at hc; simp [Noun.isCell] at hc
      | cell a c => exact ⟨a, c, rfl⟩
    rw [e] at hm ⊢
    exact genIdxOf_eq _ _ hm
  have hne : D.acs ≠ [] := List.ne_nil_of_mem hm
  refine ⟨?_, ?_, ?_⟩
  · unfold idxRW
    split_ifs
    · simp only [rIA, ComplJ8Data.rIAP]
      split_ifs with he
      · rw [he] at hm ⊢; exact getD_lastIdxOf _ _ hm
      · rw [hidxN]; exact getD_idxOf _ _ hm
    · exact getD_idxOf _ _ hm
  · unfold idxRW
    split_ifs
    · simp only [rIA, ComplJ8Data.rIAP]
      split_ifs
      · exact ComplJ8Data.lastIdxOf_lt _ _ hne
      · rw [hidxN]; exact List.idxOf_lt_length_of_mem hm
    · exact List.idxOf_lt_length_of_mem hm
  · unfold gI idxRW
    by_cases hb : u.label.bits = []
    · simp [hb]
    · have : u.label.bits.length ≠ 0 := fun h => hb (List.length_eq_zero_iff.mp h)
      simp only [if_neg this, if_neg hb, hidxN]

/-- The J-9 walk row's export key is the atom cell row's export key at the row's serial. -/
theorem wxKey_eqR (z : 𝕂′) (big : Noun → Option ℕ) (cells : List Noun) (rI : Noun → ℕ) (reads : List (Noun × ℕ))
    (mv mx mx1 : ℕ → ℕ) (α γ : K) (k : ℕ)
    (hg : cells.getD (idxRW cells rI (wTrie cells reads k)) (.atom 0) = (wTrie cells reads k).label.node) :
    wxKeyV δ (walkRow0R δ (GlobalCarryRecognizer.enc z) cells rI reads α γ k) =
      xKeyOf δ (ComplJ8Cell.cellRowsB δ z big cells mv mx mx1 (idxRW cells rI (wTrie cells reads k))) 0 := by
  rw [rowsB_eq δ z big cells mv mx mx1 _ hg]
  funext i
  fin_cases i <;> simp [wxKeyV, xKeyOf, walkRow0R, ComplJ8Cell.cellRowB, cellRow0]

/-- **The atom export terminal equals the J-9 atom-walk import terminal** (atom walk present; general limbs;
binders `hpG`, `hwalkA`). -/
theorem axT_eq_vxT9 (hpG : p = Nock.Atoms.p) (hne : (j8DataOf p Rg Rt hgen).preads ≠ [])
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads) (χ : Coins frameJ8 K) :
    axT δ (j8DataOf p Rg Rt hgen) χ = vxT9 δ (j8DataOf p Rg Rt hgen) χ := by
  have hsh := preads_shape9 Rt hgen hpG
  have hall : ∀ x ∈ (j8DataOf p Rg Rt hgen).preads, VclL.isPathAx x.2 = true := by
    intro x hx; obtain ⟨-, -, -, h2, -⟩ := hsh x hx; exact isPathAx_of_two_le h2
  have h62 := ComplJ8Walk.walkDepth62 hwalkA
  have hwcell := awNodes_mem9 Rt hgen hpG
  have hcellsC := acs_cell Rt hgen hpG
  have hspec := mxA_spec9 Rt hgen hne hall h62
  set D := j8DataOf p Rg Rt hgen with hD
  set n := D.acs.length
  set XG : ℕ → 𝕂′ := fun j => (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩
    (xKeyOf δ (aRows δ D χ j) 0))⁻¹ with hXG
  have hF : ∀ u ∈ walkRows D.acs D.preads, _ := fun u hu => idxRW_facts D u (hwcell u hu) (hcellsC _ (hwcell u hu))
  have hnV : nVOf D = (walkRows D.acs D.preads).length := by unfold nVOf; rw [if_neg hne]
  have hW : vxT9 δ D χ = ((walkRows D.acs D.preads).map fun u => XG (idxRW D.acs (rIA D) u)).sum := by
    unfold vxT9
    rw [hnV, ← sum_range_getD' (trie (.atom 0) (.atom 0) [] []) _ (walkRows D.acs D.preads)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmem := wTrie_mem D.acs D.preads (Finset.mem_range.mp hk)
    show (FiniteIO.compress (m := 11) ⟨γV δ χ, ρV δ χ⟩ (wxKeyV δ (vR9 δ D χ k)))⁻¹ = _
    rw [show vR9 δ D χ k = walkRow0R δ (GlobalCarryRecognizer.enc (zA δ χ)) D.acs (rIA D) D.preads
        (ChalsAZJ8.chalsAJ8Z δ χ 0) (ChalsAZJ8.chalsAJ8Z δ χ 1) k from rfl,
      wxKey_eqR δ (zA δ χ) (fun _ => none) D.acs (rIA D) D.preads (mvA D) (mxAF D) (fun _ => 0) _ _ k
        (hF _ hmem).1]
    rfl
  have hS := sum_serial n (fun u : NTree WN => idxRW D.acs (rIA D) u) XG (walkRows D.acs D.preads)
    (fun u hu => (hF u hu).2.1)
  have hC : axT δ D χ = ∑ j ∈ Finset.range n, ((mxAF D j : ℕ) : 𝕂′) * XG j := by
    unfold axT
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [xTermOf, cellFillInv, hXG, ComplJ8Cell.cellRowsBP, ComplJ8Cell.cellRowBP, ComplJ8Cell.cellRowsB,
      ComplJ8Cell.cellRowB, liftQ, map_natCast,
      Nat.cast_zero, map_zero, zero_mul, add_zero]
  rw [hC, hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  show D.mxA.getD j 0 = _
  rw [hspec j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  rw [hcellsC _ (hwcell u hu), (hF u hu).2.2]
  simp

/-- The atom table's export publics `2 / 3` are the atom export terminal (any data record). -/
theorem pubsAOf_23 (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) :
    pubsAOf δ b D hA o χ 2 = pub2 δ (axT δ D χ) 2 ∧ pubsAOf δ b D hA o χ 3 = pub2 δ (axT δ D χ) 3 := by
  simp [pubsAOf, pubsA1, pubsA0]

/-- `axT` reads only the atom cells and `mxA` (so GLA's `D9 = {j8DataOf with mb := mb9}` has J-8's). -/
theorem axT_congr (D D' : J8Data p Rg fuel s f r) (ha : D'.acs = D.acs) (hm : D'.mxA = D.mxA)
    (hr : D'.rows = D.rows) (χ : Coins frameJ8 K) :
    axT δ D' χ = axT δ D χ := by
  unfold axT aRows mvA mxAF ptA
  rw [ha, hm, hr]

/-- **`balF`'s atom / atom-walk clause at general limbs** (every coin, any orbit): the atom export publics `2/3`
equal the J-9 atom-walk import publics `0/1`.  Binders: `hpG`, `hwalkA` only. -/
theorem balF2_run9 (hpG : p = Nock.Atoms.p) (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) o χ 2 = pubsVOf9 δ b (j8DataOf p Rg Rt hgen) o χ 0 ∧
    pubsAOf δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) o χ 3 = pubsVOf9 δ b (j8DataOf p Rg Rt hgen) o χ 1 := by
  have hz : (0 : Quad (algebraMap (ZMod p) K δ)) = Quad.mk _ 0 0 :=
    ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
  obtain ⟨e2, e3⟩ := pubsAOf_23 δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) o χ
  rw [e2, e3]
  by_cases h0 : (j8DataOf p Rg Rt hgen).preads = []
  · rw [axT_zero δ Rt hgen h0 χ]
    refine ⟨?_, ?_⟩
    · simp [pubsVOf9, pub2, h0, hz, Quad.re_mk]
    · simp [pubsVOf9, pub2, h0, hz, Quad.im_mk]
  · rw [axT_eq_vxT9 δ Rt hgen hpG h0 hwalkA χ]
    refine ⟨?_, ?_⟩
    · simp [pubsVOf9, pubsV09, pub2, h0]
    · simp [pubsVOf9, pubsV09, pub2, h0]

end BalF9


/-! ### The J-9 atom walk's handle provide as a total over the pair reads (GLC's `hA` provide half) -/

section Provide9
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The J-9 atom-walk read weight** `WA9 x = 1 / (ρH + recDenP(rIAP x.1, x.2, chPP acs rows x))` (J9BC5A: the child
handle at the pointer; a cell at an odd axis is keyed by its parent's `ptrP`). -/
def WA9 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (x : Noun × ℕ) : 𝕂′ :=
  (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (((rIA D x.1 : ℕ) : ZMod p), ((x.2 : ℕ) : ZMod p),
    ((((ComplJ8Data.chPP p D.acs D.rows x).1 : ℕ) : ZMod p),
     (((ComplJ8Data.chPP p D.acs D.rows x).2 : ℕ) : ZMod p))))⁻¹

/-- The record-indexed form of `WA9` (first-occurrence root serial in, `rIAP` of that row's noun out). -/
def W9 (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (k : ZMod p × ZMod p × (ZMod p × ZMod p)) : 𝕂′ :=
  WA9 δ D χ (D.acs.getD k.1.val (.atom 0), k.2.1.val)

theorem W9_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (root : Noun) (a : ℕ)
    (hroot : root ∈ D.acs) (hlen : D.acs.length < p) (ha : a < p) (c : ZMod p × ZMod p) :
    W9 δ D χ (((D.acs.idxOf root : ℕ) : ZMod p), ((a : ℕ) : ZMod p), c) = WA9 δ D χ (root, a) := by
  have hil : D.acs.idxOf root < D.acs.length := List.idxOf_lt_length_of_mem hroot
  have hv1 : ((D.acs.idxOf root : ℕ) : ZMod p).val = D.acs.idxOf root := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hil.trans hlen)]
  have hv2 : ((a : ℕ) : ZMod p).val = a := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
  simp only [W9, hv1, hv2, getD_idxOf _ _ hroot]

set_option maxHeartbeats 1000000 in
/-- **The J-9 atom walk's handle provide is its rows' provided total at `W9`** (a read present). -/
theorem vhP9_eq (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hne : D.preads ≠ [])
    (hinjV : Function.Injective (powN o (nVOf D)))
    (χ : Coins frameJ8 K) (hlen : D.acs.length < p)
    (hwn : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs)
    (hcl : ∀ c ∈ D.acs, c.isCell = true)
    (hpre : ∀ u ∈ walkRows D.acs D.preads, 2 * axisFold u.label.bits + 1 < p) :
    vhP9 δ b D o χ = ((walkRows D.acs D.preads).map fun u => provH (W9 δ D χ) D.acs u.label).sum := by
  have hn : nVOf D = (walkRows D.acs D.preads).length := by simp [nVOf, hne]
  unfold vhP9
  rw [show Finset.range (nVOf D) = Finset.range (walkRows D.acs D.preads).length by rw [hn],
    ← sum_range_getD' (trie (.atom 0) (.atom 0) [] []) (fun u => provH (W9 δ D χ) D.acs u.label)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hkV : k < nVOf D := hn ▸ hk'
  rw [show (walkRows D.acs D.preads).getD k (trie (.atom 0) (.atom 0) [] []) = wTrie D.acs D.preads k from rfl]
  obtain ⟨-, eL, eR⟩ := aw_dRow_split9 δ b D o hinjV χ (pubsV09 δ D χ) ⟨k, hkV⟩
  simp only [vdN9, WalkTraceHQ.dN, WalkTraceH.cN, dif_pos hkV]
  rw [show krVOf D = krW D.acs D.preads by simp [krVOf, hne], eL, eR]
  have hu : wTrie D.acs D.preads k ∈ walkRows D.acs D.preads := wTrie_mem _ _ hk'
  obtain ⟨hch, hroot⟩ := walk_row_chain D.acs D.preads hwn _ hu
  have hc := hcl _ (hwn _ hu)
  obtain ⟨l, rr, hlr⟩ : ∃ l rr, (wTrie D.acs D.preads k).label.node = .cell l rr := by
    cases h : (wTrie D.acs D.preads k).label.node with
    | atom v => rw [h] at hc; simp [Noun.isCell] at hc
    | cell l rr => exact ⟨l, rr, rfl⟩
  have hp2 := hpre _ hu
  set w := (wTrie D.acs D.preads k).label with hw
  have hmL : vCol9 δ b D χ WChip.mL ⟨k, hkV⟩ = ((w.mL : ℕ) : ZMod p) := rfl
  have hmR : vCol9 δ b D χ WChip.mR ⟨k, hkV⟩ = ((w.mR : ℕ) : ZMod p) := rfl
  rw [hmL, hmR]
  have hsL : Noun.slot (2 * axisFold w.bits) w.root = some l := by
    rw [show 2 * axisFold w.bits = axisFold (w.bits ++ [false]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have hsR : Noun.slot (2 * axisFold w.bits + 1) w.root = some rr := by
    rw [show 2 * axisFold w.bits + 1 = axisFold (w.bits ++ [true]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have eWL := W9_eq δ D χ w.root (2 * axisFold w.bits) hroot hlen (by omega) (hdl D.acs (hdN w.node))
  have eWR := W9_eq δ D χ w.root (2 * axisFold w.bits + 1) hroot hlen hp2 (hdl D.acs (tlN w.node))
  rw [provH, nsmul_eq_mul, nsmul_eq_mul, recLH, recRH, eWL, eWR]
  have hsA : Noun.slot (axisFold w.bits) w.root = some w.node := by rw [chain_slot]; exact hch
  have hA1 : 1 ≤ axisFold w.bits := by
    rcases Nat.eq_zero_or_pos (axisFold w.bits) with h0 | h0
    · rw [h0] at hsA; simp [Noun.slot] at hsA
    · exact h0
  have hodd : (2 * axisFold w.bits + 1) % 2 = 1 ∧ 2 ≤ 2 * axisFold w.bits + 1 := ⟨by omega, by omega⟩
  have hdiv : (2 * axisFold w.bits + 1) / 2 = axisFold w.bits := by omega
  have hnode : vNode D k = w.node := rfl
  have hkl : kLV9 D ⟨k, hkV⟩ = (((ComplJ8Data.chPP p D.acs D.rows (w.root, 2 * axisFold w.bits)).1 : ℕ) : ZMod p) ∧
      vLV9 D ⟨k, hkV⟩ = (((ComplJ8Data.chPP p D.acs D.rows (w.root, 2 * axisFold w.bits)).2 : ℕ) : ZMod p) ∧
      kRV9 D ⟨k, hkV⟩ = (((ComplJ8Data.chPP p D.acs D.rows (w.root, 2 * axisFold w.bits + 1)).1 : ℕ) : ZMod p) ∧
      vRV9 D ⟨k, hkV⟩ = (((ComplJ8Data.chPP p D.acs D.rows (w.root, 2 * axisFold w.bits + 1)).2 : ℕ) : ZMod p) := by
    have hev : ¬ ((2 * axisFold w.bits) % 2 = 1 ∧ 2 ≤ 2 * axisFold w.bits) := fun h => by omega
    have htl : VclL.tlN (vNode D k) = rr := by rw [hnode, hlr]; rfl
    have hhd : VclL.hdN (vNode D k) = l := by rw [hnode, hlr]; rfl
    simp only [kLV9, vLV9, kRV9, vRV9, htl, hhd, ComplJ8Data.chPP, hsL, hsR, Option.getD_some, hdiv, hsA, hnode]
    simp only [hlr, VclL.hdN, VclL.tlN]
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases l <;> simp [hev, HA]
    · cases l <;> simp [hev, HA]
    · cases rr <;> simp [hodd, HA, Nock.V1J8.Gen.hdl]
    · cases rr <;> simp [hodd, HA, Noun.isCell]
  rw [hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2]
  have hri : (vValsC9 δ D χ ⟨k, hkV⟩).ridx = ((rIA D w.root : ℕ) : ZMod p) := rfl
  have hpr : (vValsC9 δ D χ ⟨k, hkV⟩).pre = ((axisFold w.bits : ℕ) : ZMod p) := rfl
  rw [hri, hpr]
  simp only [WA9]
  push_cast
  simp [liftQ, map_natCast]

variable (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **GLC's `hA` provide half at general limbs**: the J-9 atom walk's handle-provide publics are the total of
`WA9` over the run's pair reads (every coin; binders `hpG`, `h31`, `hwalkA`). -/
theorem vhP9_total (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads) (χ : Coins frameJ8 K) :
    Quad.mk _ (pubsVOf9 δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ WalkHQ.pubPQ)
        (pubsVOf9 δ b (j8DataOf p Rg Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ (WalkHQ.pubPQ + 1)) =
      ((j8DataOf p Rg Rt hgen).preads.map (WA9 δ (j8DataOf p Rg Rt hgen) χ)).sum := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hlenA : (j8DataOf p Rg Rt hgen).acs.length < p := size_lt_p Rt hgen hp63 h31 (by simp [sizesJ8])
  have hsh := preads_shape9 Rt hgen hpG
  have hwn := awNodes_mem9 Rt hgen hpG
  have hcl := acs_cell Rt hgen hpG
  set D := j8DataOf p Rg Rt hgen with hD
  set o := orbJ8 _ (dvdOK_of_rows hpG D h31)
  by_cases h0 : D.preads = []
  · have h0' : (j8DataOf p Rg Rt hgen).preads = [] := h0
    have hz : (0 : 𝕂′) = Quad.mk _ 0 0 := ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
    simp [pubsVOf9, h0, h0', hz]
  have h6 : pubsVOf9 δ b D o χ WalkHQ.pubPQ = pub2 δ (vhP9 δ b D o χ) 6 := by simp [pubsVOf9, h0, WalkHQ.pubPQ]
  have h7 : pubsVOf9 δ b D o χ (WalkHQ.pubPQ + 1) = pub2 δ (vhP9 δ b D o χ) 7 := by
    simp [pubsVOf9, h0, WalkHQ.pubPQ]
  rw [h6, h7, pub2_mk2 δ _ 6 rfl]
  have hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true := by
    intro x hx; obtain ⟨-, -, -, h2, -⟩ := hsh x hx; exact isPathAx_of_two_le h2
  have hmem : ∀ x ∈ VclL.pathReads D.preads, x ∈ D.preads := fun x hx =>
    (List.mem_filter.mp (List.mem_dedup.mp hx)).1
  have hslot : ∀ x ∈ VclL.pathReads D.preads, (Noun.slot x.2 x.1).isSome := by
    intro x hx; obtain ⟨-, -, -, -, h3⟩ := hsh x (hmem x hx); exact h3
  have hpre : ∀ u ∈ walkRows D.acs D.preads, 2 * axisFold u.label.bits + 1 < p := by
    intro u hu
    have h60 := ComplJ8Walk.walkRows_len_le60 hwalkA hu
    have h1 := axisFold_lt u.label.bits
    have h2 : 2 ^ (u.label.bits.length + 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 63 = 4 * 2 ^ 61 := by norm_num
    omega
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjV := (powN_ok o (le_two_pow_ht D hmV)).1
  rw [vhP9_eq δ b D o h0 hinjV χ hlenA hwn hcl hpre,
    walk_provide_total (W9 δ D χ) D.acs D.preads hslot (fun _ => rfl), pathKind_of_all hall]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨a, ha, h1, h2, -⟩ := hsh x hx
  have hBp : Nock.Atoms.B ≤ p := by rw [hpG]; exact Nock.Atoms.B_lt_p.le
  have hpa : p ≤ a := by
    have : a ∈ ComplJ8Data.bigsP p D.roots D.rows := ha
    exact ((ComplJ8Atom.mem_bigsP p _ _ a).mp this).2
  have hroot : x.1 ∈ D.acs := h1 ▸ comb_mem_acs Rt hgen hpG ha (HonestPairX.two_le_length_limbs (by omega))
  have hx2 : x.2 < p := by
    have hd := hwalkA x (List.mem_dedup.mpr (List.mem_filter.mpr ⟨hx, hall x hx⟩))
    have := ax_lt_of_depth (by omega) hd
    have : (2 : ℕ) ^ 62 < 2 ^ 63 := by norm_num
    omega
  exact W9_eq δ D χ x.1 x.2 hroot hlenA hx2 _

end Provide9


/-! ## 3. Sanity: under J-8's binders the J-9 atom walk IS J-8's

The variant changes the root serial (`rIAP` in place of `idxOf`) and the child handles (`hdl acs` in place of
`hdlP cs acs`).  Under `complJ8`'s claim binder `hclA` both changes are
invisible: `vR9 = vR`, `vCol9 = vCol`, `kLV9 … = kLV …`, `pubsVOf9 = pubsVOf`, `trVOf9 = trVOf`.  So the variant
is a correction of the honest record, not a change of scope. -/

section SanityGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAWR (wNodeValR lblWR dtWR)

theorem inTree_child {c t x : NTree WN} (h : InTree c t) (hx : x ∈ t.children) : InTree c x := by
  induction h with
  | here c => exact InTree.sub hx (InTree.here x)
  | sub hs _ ih => exact InTree.sub hs (ih hx)

theorem walkRows_child {cells : List Noun} {preads : List (Noun × ℕ)} {t x : NTree WN}
    (ht : t ∈ walkRows cells preads) (hx : x ∈ t.children) : x ∈ walkRows cells preads := by
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp ht
  exact (mem_bfsForest _ _).mpr ⟨c, hc, inTree_child hin hx⟩

theorem curCol_congr {L : Type} [Field L] (f g : NTree WN → L) (W : List (NTree WN))
    (h : ∀ t ∈ W, f t = g t) : curCol f W = curCol g W := by
  funext i
  unfold curCol
  cases hw : W[i - 1]? with
  | none => rfl
  | some t => simp only [Option.map_some, Option.getD_some]; exact h t (List.mem_of_getElem? hw)

theorem chldCol_congr {L : Type} [Field L] (f g : NTree WN → L) (W : List (NTree WN))
    (h : ∀ t ∈ W, ∀ x ∈ t.children, f x = g x) : chldCol f W = chldCol g W := by
  funext i l
  unfold chldCol
  cases hw : W[i - 1]? with
  | none => rfl
  | some t =>
    simp only [Option.bind_some]
    cases hx : t.children[l - 1]? with
    | none => rfl
    | some x =>
      simp only [Option.map_some, Option.getD_some]
      exact h t (List.mem_of_getElem? hw) x (List.mem_of_getElem? hx)

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **The variant rows depend on `rI` only at the walk's nodes and roots** (and the out-of-range dummy `atom 0`). -/
theorem walkRow0R_congr (E : Noun → Nock.ComputeTable.FP (Quad (algebraMap F K δF))) (cells : List Noun)
    (rI rI' : Noun → ℕ) (preads : List (Noun × ℕ)) (α γ : K)
    (hrow : ∀ t ∈ walkRows cells preads, rI t.label.root = rI' t.label.root ∧ rI t.label.node = rI' t.label.node)
    (hd : rI (.atom 0) = rI' (.atom 0)) :
    walkRow0R δF E cells rI preads α γ = walkRow0R δF E cells rI' preads α γ := by
  have hv : ∀ t ∈ walkRows cells preads, wNodeValR δF E rI γ t = wNodeValR δF E rI' γ t := by
    intro t ht
    simp only [wNodeValR, lblWR, dtWR, (hrow t ht).1]
  have hc := curCol_congr _ _ _ hv
  have hch := chldCol_congr _ _ (walkRows cells preads) (fun t ht x hx => hv x (walkRows_child ht hx))
  have hw : ∀ j, rI (wTrie cells preads j).label.root = rI' (wTrie cells preads j).label.root ∧
      rI (wTrie cells preads j).label.node = rI' (wTrie cells preads j).label.node := by
    intro j
    by_cases hj : j < (walkRows cells preads).length
    · exact hrow _ (wTrie_mem cells preads hj)
    · have e : wTrie cells preads j = trie (.atom 0) (.atom 0) [] [] := by
        unfold wTrie; rw [List.getD_eq_default _ _ (by omega)]
      rw [e, (trie_label _ _ _ _).1, (trie_label _ _ _ _).2.2]
      exact ⟨hd, hd⟩
  funext j
  have hi : idxRW cells rI (wTrie cells preads j) = idxRW cells rI' (wTrie cells preads j) := by
    unfold idxRW; rw [(hw j).2]
  unfold walkRow0R
  rw [hi, (hw j).1, hc, hch]

end SanityGen

section SanityRun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (walk_row_chain)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))


theorem j8_facts (hpG : p = Nock.Atoms.p)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hop5 : ComplJ8.ProgOp5OK p t) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    ComplJ8Data.rIAP p (j8DataOf p Rg Rt hgen).acs = Nock.V1J8.Gen.idxN (j8DataOf p Rg Rt hgen).acs ∧
    ∀ y ∈ (j8DataOf p Rg Rt hgen).acs, ∃ x z, y = Noun.cell (.atom x) (.atom z) ∧ x < p ∧ z < p := by
  have hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataOf p Rg Rt hgen).t]).length (by simp [sizesJ8])
    rw [ComplJ8BigBound.data_rows hgen]
    simpa [ComplJ8Data.rowsOfT, j8DataOf] using h
  obtain ⟨hb, -, -, -, -, -, hrI, -, -⟩ := ComplJ8BigBound.bigBound_single hgen hpG (hclA 0) (hclA 1) hRt hop5 hN
  exact ⟨hrI, acs_two Rt hgen hpG fun a ha => ⟨(hb a ha).1, by have := (hb a ha).2.1; omega⟩⟩

variable {Rt hgen}

/-- At `rIAP = idxN`, `rIA` is the first occurrence on the atom cells and on `atom 0`. -/
theorem rIA_idxOf (hpG : p = Nock.Atoms.p)
    (hrI : ComplJ8Data.rIAP p (j8DataOf p Rg Rt hgen).acs = Nock.V1J8.Gen.idxN (j8DataOf p Rg Rt hgen).acs) :
    (∀ n ∈ (j8DataOf p Rg Rt hgen).acs, rIA (j8DataOf p Rg Rt hgen) n = (j8DataOf p Rg Rt hgen).acs.idxOf n) ∧
    rIA (j8DataOf p Rg Rt hgen) (.atom 0) = (j8DataOf p Rg Rt hgen).acs.idxOf (.atom 0) := by
  have hcl := acs_cell Rt hgen hpG
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨a, c, rfl⟩ : ∃ a c, n = .cell a c := by
      have := hcl n hn
      cases n with
      | atom v => simp [Noun.isCell] at this
      | cell a c => exact ⟨a, c, rfl⟩
    show ComplJ8Data.rIAP p _ _ = _
    rw [hrI]
    exact genIdxOf_eq _ _ hn
  · show ComplJ8Data.rIAP p _ _ = _
    rw [hrI]
    show (j8DataOf p Rg Rt hgen).acs.length = _
    refine (List.idxOf_eq_length fun h => ?_).symm
    have := hcl _ h
    simp [Noun.isCell] at this

/-- **`vR9 = vR`** at `rIAP = idxN`. -/
theorem vR9_eq_vR (hpG : p = Nock.Atoms.p)
    (hrI : ComplJ8Data.rIAP p (j8DataOf p Rg Rt hgen).acs = Nock.V1J8.Gen.idxN (j8DataOf p Rg Rt hgen).acs)
    (χ : Coins frameJ8 K) : vR9 δ (j8DataOf p Rg Rt hgen) χ = vR δ (j8DataOf p Rg Rt hgen) χ := by
  have hwn := awNodes_mem9 Rt hgen hpG
  obtain ⟨hkey, hd⟩ := rIA_idxOf hpG hrI
  set D := j8DataOf p Rg Rt hgen
  have hrow : ∀ u ∈ walkRows D.acs D.preads, rIA D u.label.root = D.acs.idxOf u.label.root ∧
      rIA D u.label.node = D.acs.idxOf u.label.node := fun u hu =>
    ⟨hkey _ (walk_row_chain D.acs D.preads hwn u hu).2, hkey _ (hwn u hu)⟩
  show walkRow0R δ (GlobalCarryRecognizer.enc (zA δ χ)) D.acs (rIA D) D.preads _ _ =
    walkRow0 δ (zA δ χ) D.acs D.preads _ _
  rw [walkRow0R_congr δ _ D.acs (rIA D) (fun n => D.acs.idxOf n) D.preads _ _ hrow hd,
    ComplJ9BAWR.walkRow0R_idxOf, ComplJ9BAWR.walkRow0E_enc]

theorem vCol9_eq_vCol (hpG : p = Nock.Atoms.p)
    (hrI : ComplJ8Data.rIAP p (j8DataOf p Rg Rt hgen).acs = Nock.V1J8.Gen.idxN (j8DataOf p Rg Rt hgen).acs)
    (χ : Coins frameJ8 K) : vCol9 δ b (j8DataOf p Rg Rt hgen) χ = vCol δ b (j8DataOf p Rg Rt hgen) χ := by
  have e := vR9_eq_vR δ hpG hrI χ
  unfold vCol9 vCol wColBR ComplJ8Walk.wColB wValsBR ComplJ8Walk.wValsB
  rw [show wRowsBR δ (ChalsAZJ8.chalsAJ8Z δ χ) (encA δ χ) (j8DataOf p Rg Rt hgen).acs (rIA _)
      (j8DataOf p Rg Rt hgen).preads = vR9 δ (j8DataOf p Rg Rt hgen) χ from rfl, e]

/-- **The child handles agree** when every atom cell is a two-small-atom cell (`hdl acs = hdlP cs acs` on its
children). -/
theorem kLV9_eq (hpG : p = Nock.Atoms.p)
    (h2 : ∀ y ∈ (j8DataOf p Rg Rt hgen).acs, ∃ x z, y = Noun.cell (.atom x) (.atom z) ∧ x < p ∧ z < p) :
    kLV9 (j8DataOf p Rg Rt hgen) = kLV (j8DataOf p Rg Rt hgen) ∧
    vLV9 (j8DataOf p Rg Rt hgen) = vLV (j8DataOf p Rg Rt hgen) ∧
    kRV9 (j8DataOf p Rg Rt hgen) = kRV (j8DataOf p Rg Rt hgen) ∧
    vRV9 (j8DataOf p Rg Rt hgen) = vRV (j8DataOf p Rg Rt hgen) := by
  have hwn := awNodes_mem9 Rt hgen hpG
  set D := j8DataOf p Rg Rt hgen
  have hpP : p = Nock.Field.p := by rw [hpG]
  have hat : ∀ v, v < p → HA D (.atom v) = D.H (.atom v) := by
    intro v hv
    show Nock.V1J8.Gen.hdl D.acs (.atom v) = ComplJ8Data.hdlP p D.cells D.acs (.atom v)
    simp [Nock.V1J8.Gen.hdl, ComplJ8Data.hdlP, hv, show v < Nock.Field.p by omega]
  have hnode : ∀ i : Fin (nVOf D), ∃ x z, vNode D i = Noun.cell (.atom x) (.atom z) ∧ x < p ∧ z < p := by
    intro i
    have hi : (i : ℕ) < (walkRows D.acs D.preads).length := by
      have := i.isLt
      unfold nVOf at this
      split_ifs at this
      · have := walk_pos D.acs D.preads; omega
      · exact this
    exact h2 _ (hwn _ (wTrie_mem _ _ hi))
  refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩ <;>
  · obtain ⟨x, z, hxz, hx, hz⟩ := hnode i
    simp only [kLV9, vLV9, kRV9, vRV9, kLV, vLV, kRV, vRV, hxz, VclL.hdN, VclL.tlN, hat x hx, hat z hz,
      Noun.isCell, Bool.false_eq_true, if_false]


theorem pubsVOf9_eq (hpG : p = Nock.Atoms.p)
    (hrI : ComplJ8Data.rIAP p (j8DataOf p Rg Rt hgen).acs = Nock.V1J8.Gen.idxN (j8DataOf p Rg Rt hgen).acs)
    (h2 : ∀ y ∈ (j8DataOf p Rg Rt hgen).acs, ∃ x z, y = Noun.cell (.atom x) (.atom z) ∧ x < p ∧ z < p)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    pubsVOf9 δ b (j8DataOf p Rg Rt hgen) o χ = pubsVOf δ b (j8DataOf p Rg Rt hgen) o χ ∧
    trVOf9 δ b (j8DataOf p Rg Rt hgen) o χ = trVOf δ b (j8DataOf p Rg Rt hgen) o χ := by
  have e1 := vR9_eq_vR δ hpG hrI χ
  have e2 := vCol9_eq_vCol δ b hpG hrI χ
  obtain ⟨k1, k2, k3, k4⟩ := kLV9_eq hpG h2
  have h0 : pubsV09 δ (j8DataOf p Rg Rt hgen) χ = pubsV0 δ (j8DataOf p Rg Rt hgen) χ := by
    unfold pubsV09 pubsV0 vxT9 vpT9 vxT vpT
    rw [e1]
  have hp : pubsVOf9 δ b (j8DataOf p Rg Rt hgen) o χ = pubsVOf δ b (j8DataOf p Rg Rt hgen) o χ := by
    unfold pubsVOf9 pubsVOf vhX9 vhP9 vhX vhP vdN9 vdN
    rw [h0, e2, k1, k2, k3, k4]
  refine ⟨hp, ?_⟩
  unfold trVOf9 trVOf
  rw [hp, e2, k1, k2, k3, k4]

/-- **The sanity statement at `complJ8`'s binders**: the J-9 atom walk is J-8's (`hclA` used here only). -/
theorem aw9_eq_j8 (hpG : p = Nock.Atoms.p)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hop5 : ComplJ8.ProgOp5OK p t) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    vR9 δ (j8DataOf p Rg Rt hgen) χ = vR δ (j8DataOf p Rg Rt hgen) χ ∧
    vCol9 δ b (j8DataOf p Rg Rt hgen) χ = vCol δ b (j8DataOf p Rg Rt hgen) χ ∧
    (kLV9 (j8DataOf p Rg Rt hgen) = kLV (j8DataOf p Rg Rt hgen) ∧
      vLV9 (j8DataOf p Rg Rt hgen) = vLV (j8DataOf p Rg Rt hgen) ∧
      kRV9 (j8DataOf p Rg Rt hgen) = kRV (j8DataOf p Rg Rt hgen) ∧
      vRV9 (j8DataOf p Rg Rt hgen) = vRV (j8DataOf p Rg Rt hgen)) ∧
    pubsVOf9 δ b (j8DataOf p Rg Rt hgen) o χ = pubsVOf δ b (j8DataOf p Rg Rt hgen) o χ ∧
    trVOf9 δ b (j8DataOf p Rg Rt hgen) o χ = trVOf δ b (j8DataOf p Rg Rt hgen) o χ := by
  obtain ⟨hrI, h2⟩ := j8_facts Rt hgen hpG hclA hRt hop5 h31
  exact ⟨vR9_eq_vR δ hpG hrI χ, vCol9_eq_vCol δ b hpG hrI χ, kLV9_eq hpG h2, pubsVOf9_eq δ b hpG hrI h2 o χ⟩

end SanityRun

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
