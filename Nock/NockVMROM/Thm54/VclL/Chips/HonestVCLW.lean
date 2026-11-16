/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestVCLW.lean

* `HonestVCLW kr`: a verifier datum on `shapeVW` whose cell table is the generator's `d.cells` and
    whose walk table is `GenWalk.walkRows d.cells d.preads` (`krW = kr`), with the numeric facts
    `GoodW` reads (`kr + |walk| < p` is the `hmemW` content).
  * The cell rows' side-0 export multiplicity counts the WALK consumers: `xs0W = walkRows.map node ++`
    the depth-1 side-0 lookups (one export consume per walk row, `ExportTelescopeW`), `xs1W` the
    depth-1 side-1 lookups.
  * `col` / `trace`: the cell fill (unchanged) and the walk fill `walkFill (γ′, ρ′)` of
    `walkRow0 z α γ` at `(α, γ) = (χ₀, χ₁)`; `trace_stagedW` (B0 coin-free, B1 the seed only, B2 every
    coin is sampled before round 2).
  * `bad`: the zero seed and three pole summands — validity keys `3·nC`, export keys `2·nC + nW`
    (cell sides 0 / 1 and every walk row's consume key), path records **`2·nW`: `recL` AND `recR` of
    every walk row** (the unconditional `pInvL` / `pInvR`, W2's flagged pole case).
  * `acceptedW`: outside `bad` both `ok`-gated chips accept the honest traces at `req` / `msg2`.
  * `epsilon_badW`: `ε = (1 + 5·nC + 3·nW) / |𝕂|²`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestWalkGen
import Nock.NockVMROM.Thm54.VclL.Chips.HonestWalkAccept
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemHonest

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The honest datum -/

section Honest
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]

/-- **The honest datum of the walk memory family.** -/
structure HonestVCLW (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (hT hP hC kr : ℕ) where
  V : VerifierData F K hC (shapeVW hT hP)
  d : Demand
  hF : GeneratedField.PrimeFieldElems F
  hq : 2 ^ 63 < ringChar F
  hrows : ∀ t, V.memRows t + 1 < ringChar F
  hadj : ∀ t, V.AdjacentM t
  hinj : ∀ t, Function.Injective (V.memNodes t)
  hrank : ∀ n ∈ d.cells, rankOf n < 2 ^ 110
  h62 : ∀ r ∈ pathReads d.preads, depthOf r.2 ≤ 62
  hC0 : V.memRows (tCW hT hP) = d.cells.length
  hW0 : V.memRows (tWW hT hP) = (walkRows d.cells d.preads).length
  hkr : krW d.cells d.preads = kr
  hkp : kr + V.memRows (tWW hT hP) < ringChar F

/-- Side-0 export consumers: every walk row's node (one consume per row) and the depth-1 side-0 lookups. -/
def xs0W (d : Demand) : List Noun :=
  (walkRows d.cells d.preads).map (fun t => t.label.node) ++
    ((shallowSided d.reads).filter fun c => !c.2).map Prod.fst

/-- Side-1 export consumers: the depth-1 side-1 lookups. -/
def xs1W (d : Demand) : List Noun := ((shallowSided d.reads).filter fun c => c.2).map Prod.fst

variable {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}

namespace HonestVCLW
variable (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- The generated cell rows at the seed `z`. -/
def cellRows (z : Quad (algebraMap F K δF)) : ℕ → CellVals F (Quad (algebraMap F K δF)) :=
  cellRows0 δF z H.d.cells (vcsOf H.d.cells []) (xs0W H.d) (xs1W H.d)

/-- The honest walk rows at the coins (seed `z = zC`, walk coins `χ₀, χ₁`), before the fill. -/
def wRows (χ : Coins frameVCL K) : ℕ → WalkVals F K (Quad (algebraMap F K δF)) :=
  walkRow0 δF (zC χ) H.d.cells H.d.preads (chalsVCL δF χ 0) (chalsVCL δF χ 1)

/-- The honest filled walk rows. -/
def wVals (χ : Coins frameVCL K) : ℕ → WalkVals F K (Quad (algebraMap F K δF)) :=
  walkFill δF (γC χ) (ρC χ) (H.wRows χ)

def vTot (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  ∑ k ∈ Finset.range (H.V.memRows (tCW hT hP)),
    vTermOf δF (cellFillInv δF (γC χ) (ρC χ) (H.cellRows (zC χ) k))
def xTot (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  ∑ k ∈ Finset.range (H.V.memRows (tCW hT hP)),
    xTermOf δF (cellFillInv δF (γC χ) (ρC χ) (H.cellRows (zC χ) k))
/-- The walk's export-consume total `y`. -/
def yTot (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  ∑ k ∈ Finset.range (H.V.memRows (tWW hT hP)), (walkFillInv δF (γC χ) (ρC χ) (H.wRows χ k)).xInv
/-- The walk's path-provide total `Σ mL·invL + mR·invR`. -/
def pTot (χ : Coins frameVCL K) : Quad (algebraMap F K δF) :=
  ∑ k ∈ Finset.range (H.V.memRows (tWW hT hP)), wpTermV δF (walkFillInv δF (γC χ) (ρC χ) (H.wRows χ k))

/-- **`honestReq`**. -/
def req (χ : Coins frameVCL K) : Fin 3 → Quad (algebraMap F K δF)
  | 0 => H.vTot χ
  | 1 => H.xTot χ - H.yTot χ
  | 2 => H.pTot χ

/-- **`honestMsg2`**. -/
def msg2 (χ : Coins frameVCL K) : Quad (algebraMap F K δF) := H.yTot χ

/-- The honest column function of table `t`. -/
def col (χ : Coins frameVCL K) (t : Fin (shapeVW hT hP).k) : ℕ → Fin (H.V.memRows t) → F :=
  fun j i =>
    if (t : ℕ) = 0 then
      cellCol δF H.V.basis (fun i' : Fin (H.V.memRows t) =>
        cellFill δF (γC χ) (ρC χ) (H.cellRows (zC χ)) i') j i
    else walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows t) => H.wVals χ i') j i

/-- **`honestQ`**. -/
def trace (χ : Coins frameVCL K) (t : Fin (shapeVW hT hP).k) :
    Fin ((shapeVW hT hP).table t).width → F[X] :=
  honestQ (H.V.hM t) (H.V.memNodes t) (H.col χ t) ((shapeVW hT hP).table t).width

end HonestVCLW

end Honest

/-! ## 2. Stagedness -/

section Staged
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ}

theorem frameVCL_sampled_le_one (i : Fin frameVCL.n) : frameVCL.sampledAfter i ≤ 1 := by
  revert i; decide

theorem fpSlot_congr {Q : Type} (v v' : WalkVals F K Q) (hp : v.p = v'.p) (hl : v.l = v'.l)
    (hr : v.r = v'.r) (hroot : v.root = v'.root) (s : ℕ) : v.fpSlot s = v'.fpSlot s := by
  cases v; cases v'
  simp only at hp hl hr hroot
  subst hp hl hr hroot
  rfl

theorem walkTable_round_lower (j : Fin 132) :
    (21 ≤ (j : ℕ) → 1 ≤ colRoundW j) ∧ (93 ≤ (j : ℕ) → 2 ≤ colRoundW j) := by
  simp only [colRoundW]
  split_ifs <;> omega

theorem table_zero_roundW (t : Fin (shapeVW hT hP).k) (ht : (t : ℕ) = 0)
    (j : Fin ((shapeVW hT hP).table t).width) :
    ∃ hj : (j : ℕ) < 225, ((shapeVW hT hP).table t).colRound j = Chips.Cell.colRoundT ⟨j, hj⟩ := by
  obtain rfl : t = tCW hT hP := Fin.ext ht
  exact ⟨j.2, rfl⟩

theorem table_one_roundW (t : Fin (shapeVW hT hP).k) (ht : (t : ℕ) ≠ 0)
    (j : Fin ((shapeVW hT hP).table t).width) :
    ∃ hj : (j : ℕ) < 132, ((shapeVW hT hP).table t).colRound j = colRoundW ⟨j, hj⟩ := by
  have h2 : (t : ℕ) < 2 := t.2
  obtain rfl : t = tWW hT hP := Fin.ext (show (t : ℕ) = 1 by omega)
  exact ⟨j.2, rfl⟩

variable (H : HonestVCLW (K := K) δF hT hP hC kr)

/-- **`honest_staged`.** -/
theorem trace_stagedW (t : Fin (shapeVW hT hP).k) :
    StagedCols frameVCL ((shapeVW hT hP).table t).colRound (fun χ => H.trace χ t) := by
  intro j χ χ' h
  unfold HonestVCLW.trace
  refine honestQ_congr (H.V.hM t) (H.V.memNodes t) (H.col χ t) (H.col χ' t) _ j ?_
  funext i
  by_cases h2 : 2 ≤ ((shapeVW hT hP).table t).colRound j
  · have : χ = χ' := funext fun c => h c (by have := frameVCL_sampled_le_one c; omega)
    subst this; rfl
  by_cases ht : (t : ℕ) = 0
  · obtain ⟨hj, hr⟩ := table_zero_roundW t ht j
    have hlow := cell_round_lower ⟨j, hj⟩
    simp only [HonestVCLW.col, ht, if_true]
    refine cellCol_round1 H.V.basis _ _ _ _ _ _ j (fun i k => cellRows0_base_indep _ _ _ _ _ _ i k)
      (fun h1 i s _ => ?_) i (by by_contra hc; exact h2 (by rw [hr]; exact hlow.2 (by simp; omega)))
    have hz := zC_congr (δF := δF) χ χ' (r := ((shapeVW hT hP).table t).colRound j)
      (by rw [hr]; exact hlow.1 (by simpa using h1)) h
    show (H.cellRows (zC χ) i).qslot s = (H.cellRows (zC χ') i).qslot s
    rw [hz]
  · obtain ⟨hj, hr⟩ := table_one_roundW t ht j
    have hlow := walkTable_round_lower ⟨j, hj⟩
    simp only [HonestVCLW.col, ht, if_false]
    have hj93 : (j : ℕ) < 93 := by by_contra hc; exact h2 (by rw [hr]; exact hlow.2 (by simp; omega))
    unfold walkCol
    by_cases hb : (j : ℕ) < 21
    · simp only [hb, if_true]; rfl
    · simp only [hb, if_false]
      have hz := zC_congr (δF := δF) χ χ' (r := ((shapeVW hT hP).table t).colRound j)
        (by rw [hr]; exact hlow.1 (by simp; omega)) h
      congr 1
      unfold wroleVal
      have hρ : ((j : ℕ) - 21) / 3 < 24 := by omega
      simp only [hρ, if_true]
      have e : ∀ s, (H.wVals χ i).fpSlot s = (H.wVals χ' i).fpSlot s := by
        intro s
        apply fpSlot_congr <;>
          simp only [HonestVCLW.wVals, HonestVCLW.wRows, walkFill, walkFillInv, walkRow0, hz]
      rw [e]

end Staged

/-! ## 3. The honest bad summands -/

section Bad
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ} {C : TableSpec}
  (H : HonestVCLW (K := K) δF hT hP hC kr)

namespace HonestVCLW

/-- The walk rows' records read only the seed (the walk coins enter B2 only). -/
def wRec (z : Quad (algebraMap F K δF)) (j : ℕ) : WalkVals F K (Quad (algebraMap F K δF)) :=
  walkRow0 δF z H.d.cells H.d.preads 0 0 j

def keys0 (χ : Coins frameVCL K) : List (Fin 5 → Quad (algebraMap F K δF)) :=
  (List.range (H.V.memRows (tCW hT hP))).map (fun j => vKeyOf δF (H.cellRows (zC χ) j)) ++
  (List.range (H.V.memRows (tCW hT hP))).map (fun j => lKeyOf δF (H.cellRows (zC χ) j)) ++
  (List.range (H.V.memRows (tCW hT hP))).map (fun j => rKeyOf δF (H.cellRows (zC χ) j))

def keys1 (χ : Coins frameVCL K) : List (Fin 11 → Quad (algebraMap F K δF)) :=
  (List.range (H.V.memRows (tCW hT hP))).map (fun j => xKeyOf δF (H.cellRows (zC χ) j) 0) ++
  (List.range (H.V.memRows (tCW hT hP))).map (fun j => xKeyOf δF (H.cellRows (zC χ) j) 1) ++
  (List.range (H.V.memRows (tWW hT hP))).map (fun j => wxKeyV δF (H.wRec (zC χ) j))

/-- **Both path records of EVERY walk row** (the unconditional path-provide inverses). -/
def keys2 (χ : Coins frameVCL K) : List (Fin 8 → Quad (algebraMap F K δF)) :=
  (List.range (H.V.memRows (tWW hT hP))).map (fun j => wrecLV δF (H.wRec (zC χ) j)) ++
  (List.range (H.V.memRows (tWW hT hP))).map (fun j => wrecRV δF (H.wRec (zC χ) j))

def zeroSW : BadSummand frameVCL K (Traces F C (shapeVW hT hP)) (TracesStaged frameVCL C (shapeVW hT hP)) :=
  seedSummand (seedSpecVCL (algebraMap F K δF)) (fun _ => ({0} : Finset (Quad (algebraMap F K δF)))) 1
    (fun _ => by simp)

def poleS0 : BadSummand frameVCL K (Traces F C (shapeVW hT hP)) (TracesStaged frameVCL C (shapeVW hT hP)) :=
  poleSummand (ioSpecVCLQuad (algebraMap F K δF)) _ HonestVCL.disj_io_seed (3 * H.V.memRows (tCW hT hP))
    (fun χ => H.keys0 χ) (fun χ => by simp [keys0]; omega)
    (HonestVCL.reads_seed (fun z =>
      (List.range (H.V.memRows (tCW hT hP))).map (fun j => vKeyOf δF (H.cellRows z j)) ++
      (List.range (H.V.memRows (tCW hT hP))).map (fun j => lKeyOf δF (H.cellRows z j)) ++
      (List.range (H.V.memRows (tCW hT hP))).map (fun j => rKeyOf δF (H.cellRows z j))))

def poleS1 : BadSummand frameVCL K (Traces F C (shapeVW hT hP)) (TracesStaged frameVCL C (shapeVW hT hP)) :=
  poleSummand (ioSpecVCLQuad (algebraMap F K δF)) _ HonestVCL.disj_io_seed
    (2 * H.V.memRows (tCW hT hP) + H.V.memRows (tWW hT hP))
    (fun χ => H.keys1 χ) (fun χ => by simp [keys1]; omega)
    (HonestVCL.reads_seed (fun z =>
      (List.range (H.V.memRows (tCW hT hP))).map (fun j => xKeyOf δF (H.cellRows z j) 0) ++
      (List.range (H.V.memRows (tCW hT hP))).map (fun j => xKeyOf δF (H.cellRows z j) 1) ++
      (List.range (H.V.memRows (tWW hT hP))).map (fun j => wxKeyV δF (H.wRec z j))))

def poleS2 : BadSummand frameVCL K (Traces F C (shapeVW hT hP)) (TracesStaged frameVCL C (shapeVW hT hP)) :=
  poleSummand (ioSpecVCLQuad (algebraMap F K δF)) _ HonestVCL.disj_io_seed (2 * H.V.memRows (tWW hT hP))
    (fun χ => H.keys2 χ) (fun χ => by simp [keys2]; omega)
    (HonestVCL.reads_seed (fun z =>
      (List.range (H.V.memRows (tWW hT hP))).map (fun j => wrecLV δF (H.wRec z j)) ++
      (List.range (H.V.memRows (tWW hT hP))).map (fun j => wrecRV δF (H.wRec z j))))

/-- **`honestBad`**: the zero seed and the three pole events. -/
def bad : List (BadSummand frameVCL K (Traces F C (shapeVW hT hP)) (TracesStaged frameVCL C (shapeVW hT hP))) :=
  [zeroSW (δF := δF), H.poleS0, H.poleS1, H.poleS2]

end HonestVCLW

theorem bad_decodeW (χ : Coins frameVCL K) (Qc : Fin C.width → F[X])
    (hbad : ∀ s ∈ H.bad (C := C), ¬ s.mem (Qc, fun t => H.trace χ t) χ) :
    zC (δF := δF) χ ≠ 0 ∧
    (∀ v ∈ H.keys0 χ, FiniteIO.compress (m := 5) ⟨γC χ, ρC χ⟩ v ≠ 0) ∧
    (∀ v ∈ H.keys1 χ, FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ v ≠ 0) ∧
    (∀ v ∈ H.keys2 χ, FiniteIO.compress (m := 8) ⟨γC χ, ρC χ⟩ v ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hbad (HonestVCLW.zeroSW (K := K) (δF := δF) (hT := hT) (hP := hP) (C := C))
      (by simp [HonestVCLW.bad])
    intro hz
    apply h
    unfold HonestVCLW.zeroSW
    rw [seedSummand_mem]
    simp [HonestVCL.zC_eq_seed] at hz ⊢
    exact hz
  · have h := hbad H.poleS0 (by simp [HonestVCLW.bad])
    unfold HonestVCLW.poleS0 at h
    erw [poleSummand_mem] at h
    exact pole_ne _ χ h
  · have h := hbad H.poleS1 (by simp [HonestVCLW.bad])
    unfold HonestVCLW.poleS1 at h
    erw [poleSummand_mem] at h
    exact pole_ne _ χ h
  · have h := hbad H.poleS2 (by simp [HonestVCLW.bad])
    unfold HonestVCLW.poleS2 at h
    erw [poleSummand_mem] at h
    exact pole_ne _ χ h

/-- **The honest bad set's mass**: `ε = (1 + 5·nC + 3·nW) / |𝕂|²`. -/
theorem epsilon_badW :
    epsilonOf (H.bad (C := C)) =
      (1 + 5 * (H.V.memRows (tCW hT hP) : ℚ) + 3 * (H.V.memRows (tWW hT hP) : ℚ)) / (Fintype.card K : ℚ) ^ 2 := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  have hdep : (seedSpecVCL (algebraMap F K δF)).dep.card = 2 := by
    show ({c2, c3} : Finset (Fin frameVCL.n)).card = 2
    decide
  have hio : (ioSpecVCLQuad (algebraMap F K δF)).dep.card = 4 := ioSpecVCLQuad_dep_card _
  have hq : Fintype.card (Quad (algebraMap F K δF)) = Fintype.card K ^ 2 := ioSpecVCLQuad_card _
  unfold epsilonOf HonestVCLW.bad
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have e0 : ((HonestVCLW.zeroSW (K := K) (δF := δF) (hT := hT) (hP := hP) (C := C)).weight : ℚ) /
      (Fintype.card K : ℚ) ^ (HonestVCLW.zeroSW (K := K) (δF := δF) (hT := hT) (hP := hP) (C := C)).coins.card
      = 1 / (Fintype.card K : ℚ) ^ 2 := by
    show ((1 : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ (seedSpecVCL (algebraMap F K δF)).dep.card = _
    rw [hdep]; simp
  have ep : ∀ (len : ℕ), ((len * Fintype.card (Quad (algebraMap F K δF)) : ℕ) : ℚ) /
      (Fintype.card K : ℚ) ^ (ioSpecVCLQuad (algebraMap F K δF)).dep.card = len / (Fintype.card K : ℚ) ^ 2 := by
    intro len
    rw [hio, hq]; push_cast; field_simp
  have p0 : ((H.poleS0 (C := C)).weight : ℚ) / (Fintype.card K : ℚ) ^ (H.poleS0 (C := C)).coins.card =
      ((3 * H.V.memRows (tCW hT hP) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 := ep _
  have p1 : ((H.poleS1 (C := C)).weight : ℚ) / (Fintype.card K : ℚ) ^ (H.poleS1 (C := C)).coins.card =
      ((2 * H.V.memRows (tCW hT hP) + H.V.memRows (tWW hT hP) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 := ep _
  have p2 : ((H.poleS2 (C := C)).weight : ℚ) / (Fintype.card K : ℚ) ^ (H.poleS2 (C := C)).coins.card =
      ((2 * H.V.memRows (tWW hT hP) : ℕ) : ℚ) / (Fintype.card K : ℚ) ^ 2 := ep _
  rw [e0, p0, p1, p2]
  push_cast
  field_simp
  ring

end Bad

/-! ## 4. Acceptance -/

section Accepted
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] {hT hP hC kr : ℕ} {C : TableSpec}
  (H : HonestVCLW (K := K) δF hT hP hC kr)

theorem cell_acceptedW (χ : Coins frameVCL K)
    (hz : zC (δF := δF) χ ≠ 0)
    (h0 : ∀ v ∈ H.keys0 χ, FiniteIO.compress (m := 5) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (h1 : ∀ v ∈ H.keys1 χ, FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (hρ0 : ρ 0 = H.vTot χ) (hρ1 : ρ 1 + y = H.xTot χ) :
    RAP.SatisfiesWithPreprocessing
      (cellChipOk δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
        (chalsVCL δF χ) (pubsC δF ρ y) true)
      (fun j => honestQ (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
        (cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
          cellFill δF (γC χ) (ρC χ) (H.cellRows (zC χ)) i')) 225
        (Fin.cast (cellChipOk_w δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP))
          (H.V.orbitM (tCW hT hP)) (chalsVCL δF χ) (pubsC δF ρ y) true) j)) := by
  have hN : H.V.memRows (tCW hT hP) = H.d.cells.length := H.hC0
  have hnd := closureOf_nodup H.d.roots
  have hcell : ∀ n ∈ H.d.cells, n.isCell = true := fun n hn => closureOf_isCell hn
  refine cellOk_sat δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
    (chalsVCL δF χ) (pubsC δF ρ y) _ (H.hinj _) (H.hadj _) (γC χ) (ρC χ) (zC χ)
    (chalsVCL_ok δF χ 11) rfl (fun i => ?_) (fun i => ?_)
  · exact cellBaseFacts_fill δF _ _ (H.cellRows (zC χ)) i
      (cellRows0_baseFacts (δF := δF) (zC χ) H.d.cells (vcsOf H.d.cells []) (xs0W H.d) (xs1W H.d)
        hcell hnd H.hrank hN i)
  · have hlt : ∀ j < H.V.memRows (tCW hT hP), j < H.d.cells.length := fun j hj => hN ▸ hj
    refine cellFill_facts (γC χ) (ρC χ) (H.cellRows (zC χ)) (zC χ) (pubsC δF ρ y) i hz
      (fun j hj => cellRows0_cons (δF := δF) (zC χ) H.d.cells _ _ _ hcell hz (hlt j hj))
      (fun j hj => cellRows0_atomL (δF := δF) (zC χ) H.d.cells _ _ _ hcell (hlt j hj))
      (fun j hj => cellRows0_atomR (δF := δF) (zC χ) H.d.cells _ _ _ hcell (hlt j hj))
      (fun j hj => h0 _ ?_) (fun j hj _ => h0 _ ?_) (fun j hj _ => h0 _ ?_)
      (fun j hj => h1 _ ?_) (fun j hj => h1 _ ?_) ?_ ?_
    · simp only [HonestVCLW.keys0, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl ⟨j, hj, rfl⟩)
    · simp only [HonestVCLW.keys0, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
    · simp only [HonestVCLW.keys0, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩
    · simp only [HonestVCLW.keys1, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl ⟨j, hj, rfl⟩)
    · simp only [HonestVCLW.keys1, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
    · rw [pubsC_01, hρ0]; rfl
    · rw [pubsC_23, hρ1]; rfl

theorem wRows_root (χ : Coins frameVCL K) {j : ℕ} (hj : j < (walkRows H.d.cells H.d.preads).length)
    (hk : j < krW H.d.cells H.d.preads) : (H.wRows χ j).root = (H.wRows χ j).p := by
  obtain ⟨t, ht, -, hn⟩ := walkRows_root H.d.cells H.d.preads j hk
  have : wTrie H.d.cells H.d.preads j = t := by
    unfold wTrie; rw [List.getD_eq_getElem _ _ hj]
    exact Option.some_injective _ ((List.getElem?_eq_getElem hj).symm.trans ht)
  show GlobalCarryRecognizer.enc (zC χ) (wTrie H.d.cells H.d.preads j).label.root =
    GlobalCarryRecognizer.enc (zC χ) (wTrie H.d.cells H.d.preads j).label.node
  rw [this, hn]

theorem walk_acceptedW (χ : Coins frameVCL K)
    (h1 : ∀ v ∈ H.keys1 χ, FiniteIO.compress (m := 11) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (h2 : ∀ v ∈ H.keys2 χ, FiniteIO.compress (m := 8) ⟨γC χ, ρC χ⟩ v ≠ 0)
    (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (hy : y = H.yTot χ) (hρ2 : ρ 2 = H.pTot χ) :
    RAP.SatisfiesWithPreprocessing
      (walkChipOk δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
        (chalsVCL δF χ) (pubsP δF ρ y) true)
      (fun j => honestQ (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
        (walkCol δF H.V.basis kr (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals χ i')) 132
        (Fin.cast (walkChipOk_w δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP))
          (H.V.orbitM (tWW hT hP)) (chalsVCL δF χ) (pubsP δF ρ y) true) j)) := by
  have hN := H.hW0
  have hkp : krW H.d.cells H.d.preads + (walkRows H.d.cells H.d.preads).length < ringChar F := by
    rw [H.hkr, ← hN]; exact H.hkp
  have hcells : H.d.cells.length < ringChar F := by
    have := H.hrows (tCW hT hP); rw [H.hC0] at this; omega
  refine walkOk_sat δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
    (chalsVCL δF χ) (pubsP δF ρ y) _ H.hF (H.hinj _) (H.hadj _) (γC χ) (ρC χ)
    (chalsVCL_ok δF χ 11) (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · have hb := walkRow0_base δF (zC χ) H.d.cells H.d.preads (chalsVCL δF χ 0) (chalsVCL δF χ 1) H.h62 hkp hN i
    rw [H.hkr] at hb
    exact walkBaseFacts_fill δF (γC χ) (ρC χ) (H.wRows χ) kr i hb
  · have hk := walkRow0_K δF (zC χ) H.d.cells H.d.preads (chalsVCL δF χ 0) (chalsVCL δF χ 1) H.hF H.hq hcells
      H.h62 hN i
    rw [H.hkr] at hk
    exact walkKFacts_fill δF (γC χ) (ρC χ) (H.wRows χ) kr _ _ i hk
  · refine walkFill_mixed δF (γC χ) (ρC χ) (H.wRows χ) kr (pubsP δF ρ y) i
      (fun j hj hk => wRows_root H χ (hN ▸ hj) (by rw [H.hkr]; exact hk))
      (fun j hj => h1 _ ?_) (fun j hj => h2 _ ?_) (fun j hj => h2 _ ?_) ?_ ?_
    · simp only [HonestVCLW.keys1, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩
    · simp only [HonestVCLW.keys2, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨j, hj, rfl⟩
    · simp only [HonestVCLW.keys2, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩
    · rw [pubsP_01, hy]; rfl
    · rw [pubsP_23, hρ2]; rfl

/-- **`honest_accepted`**: outside the honest bad set both `ok`-gated chips accept the honest traces at
the honest requests / message. -/
theorem acceptedW (χ : Coins frameVCL K) (Qc : Fin C.width → F[X])
    (hbad : ∀ s ∈ H.bad (C := C), ¬ s.mem (Qc, fun t => H.trace χ t) χ) (t : Fin (shapeVW hT hP).k) :
    RAP.SatisfiesWithPreprocessing (vclChipW δF hT hP kr (H.req χ) (H.msg2 χ) H.V χ t)
      (fun j => H.trace χ t (Fin.cast (vclChipW_width δF hT hP kr (H.req χ) (H.msg2 χ) H.V χ t) j)) := by
  obtain ⟨hz, h0, h1, h2⟩ := bad_decodeW H χ Qc hbad
  have hok : ∀ t, okOf H.V t = true := fun t =>
    ok_of_goodM ⟨H.hadj t, H.hinj t, H.hF, H.hq, H.hrows t⟩
  have hokW : okW H.V (tWW hT hP) kr = true := by
    refine okW_of_goodW ⟨⟨H.hadj _, H.hinj _, H.hF, H.hq, H.hrows _⟩, ?_, ?_, H.hkp⟩
    · have := one_le_krW H.d.cells H.d.preads; rw [H.hkr] at this; exact this
    · have := krW_le_rows H.d.cells H.d.preads; rw [H.hkr, ← H.hW0] at this; exact this
  by_cases ht : (t : ℕ) = 0
  · obtain rfl : t = tCW hT hP := Fin.ext ht
    have hch : vclChipW δF hT hP kr (H.req χ) (H.msg2 χ) H.V χ (tCW hT hP) =
        cellChipOk δF H.V.basis (H.V.hM (tCW hT hP)) (H.V.memNodes (tCW hT hP)) (H.V.orbitM (tCW hT hP))
          (chalsVCL δF χ) (pubsC δF (H.req χ) (H.msg2 χ)) true := by
      unfold vclChipW
      rw [if_pos (by rfl), hok]
    have hcol : H.col χ (tCW hT hP) = cellCol δF H.V.basis (fun i' : Fin (H.V.memRows (tCW hT hP)) =>
        cellFill δF (γC χ) (ρC χ) (H.cellRows (zC χ)) i') := by
      funext j i; unfold HonestVCLW.col; rw [if_pos ht]
    refine sat_transportW hch.symm _ _ ?_
      (cell_acceptedW H χ hz h0 h1 (H.req χ) (H.msg2 χ) rfl (sub_add_cancel _ _))
    intro j hj hj'
    simp only [HonestVCLW.trace, hcol]
    rfl
  · have ht1 : t = tWW hT hP := Fin.ext (by have h2 : (t : ℕ) < 2 := t.2; show (t : ℕ) = 1; omega)
    subst ht1
    have hch : vclChipW δF hT hP kr (H.req χ) (H.msg2 χ) H.V χ (tWW hT hP) =
        walkChipOk δF kr H.V.basis (H.V.hM (tWW hT hP)) (H.V.memNodes (tWW hT hP)) (H.V.orbitM (tWW hT hP))
          (chalsVCL δF χ) (pubsP δF (H.req χ) (H.msg2 χ)) true := by
      unfold vclChipW
      rw [if_neg (by show (1 : ℕ) ≠ 0; exact one_ne_zero), hokW]
    have hcol : H.col χ (tWW hT hP) = walkCol δF H.V.basis kr
        (fun i' : Fin (H.V.memRows (tWW hT hP)) => H.wVals χ i') := by
      funext j i; unfold HonestVCLW.col; rw [if_neg (by show (1 : ℕ) ≠ 0; exact one_ne_zero)]
    refine sat_transportW hch.symm _ _ ?_
      (walk_acceptedW H χ h1 h2 (H.req χ) (H.msg2 χ) rfl rfl)
    intro j hj hj'
    simp only [HonestVCLW.trace, hcol]
    rfl

end Accepted

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
