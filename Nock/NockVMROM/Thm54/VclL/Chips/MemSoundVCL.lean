/-
  Nock/NockVMROM/Thm54/VclL/Chips/MemSoundVCL.lean

  **1829): the soundness fields of `vclMemFamily`
  that read the B0 columns and the summands.**  Coordinates as in `MemFamilyVCL.lean` (`shapeV hT hP`, `frameVCL`,
  `ioSpecVCLQuad δ`, `Kio = Kfp = Quad δ`, `RV.recordViewVCL`, `Msg0 := Unit`).

  * §1 **the B0 decode**: `b0Trace` (a `B0Cols` message as a full-width trace, non-B0 columns `0`),
    `cellRowsB0` (the cell table's round-0 rows, read from the B0 message only), `decodedNoun`
    (`preZNounOfTable` capped at the window `2^110`).
  * §2 the served-noun fields: `vclServedKeys` (the keys of the providers decoded from the B0 message
    — the keys read B0 entries only), `vclServedRoot` / `vclServed` (validity: the decoded noun;
    export `(i, s)`: the decoded cell and its side child; path `(rootIdx, ax)`: the decoded root and
    `Noun.slot ax`), `vclServedKeys_length` (`≤ D + 2D + P`), `vclWindow := 2^110` (trace-free),
    `vclServed_leaves_le` (holds at EVERY B0 message, by the cap).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemFamilyVCL
import Nock.NockVMROM.Thm54.P8Core.VclL.Census
import Nock.NockVMROM.Thm54.P8Core.VclL.DyckRoot
import Nock.NockVMROM.Thm54.P8Core.RootGoodF

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.PathModel
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The B0 decode -/

/-- A B0 message as a full-width trace: the B0 columns, every other column `0`. -/
def b0Trace {F : Type} [Field F] {T : TableSpec} (bm : B0Cols F T) : Fin T.width → F[X] :=
  fun j => if h : T.colRound j = 0 then bm ⟨j, h⟩ else 0

theorem b0Trace_b0 {F : Type} [Field F] {T : TableSpec} (Q : Fin T.width → F[X]) (j : Fin T.width)
    (h : T.colRound j = 0) : b0Trace (b0 Q) j = Q j := by
  simp [b0Trace, b0, h]

/-- The window: `Λ_chip = 2^110` (`Table.fuelChip`). -/
def capN (n : Noun) : Noun := if n.leaves ≤ fuelChip then n else .atom 0

theorem capN_leaves (n : Noun) : (capN n).leaves ≤ fuelChip := by
  unfold capN; split_ifs with h
  · exact h
  · simp [Noun.leaves, fuelChip]

theorem capN_of_le {n : Noun} (h : n.leaves ≤ fuelChip) : capN n = n := if_pos h

section Family
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP : ℕ) {hC : ℕ}

variable (V : VerifierData F K hC (shapeV hT hP)) (x : Unit)
  (b : ∀ t : Fin (shapeV hT hP).k, B0Cols F ((shapeV hT hP).table t))

/-- The B0 message of both tables as traces. -/
def bTr : ∀ t : Fin (shapeV hT hP).k, Fin ((shapeV hT hP).table t).width → F[X] :=
  fun t => b0Trace (b t)

/-- **The cell table's round-0 rows, from the B0 message alone.** -/
def cellRowsB0 : List (CellRowB0 (ringChar F)) :=
  List.ofFn fun i : Fin (V.memRows (tC hT hP)) =>
    cellB0Of (cellEnvF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) 0 0 (b0Trace (b (tC hT hP))) i)

/-- **The noun at serial `i`**: the B0 decode `preZNounOfTable`, capped at the window. -/
def decodedNoun (i : ℕ) : Noun :=
  match preZNounOfTable (cellRowsB0 hT hP V b) i with
  | some n => capN n
  | none => .atom 0

theorem decodedNoun_leaves (i : ℕ) : (decodedNoun hT hP V b i).leaves ≤ fuelChip := by
  unfold decodedNoun; split
  · exact capN_leaves _
  · simp [Noun.leaves, fuelChip]

/-! ## 2. The served-noun fields -/

/-- **`servedKeys`**: the keys of the providers at the B0 message (validity `D`, export `2D`, path
`≤ P`); a key reads only B0 entries of its record. -/
def vclServedKeys : List RV.KeyVCL :=
  ((vclResp δF hT hP V (bTr hT hP b) 0).map fun r => RV.keyVCL 0 r.1) ++
  ((vclResp δF hT hP V (bTr hT hP b) 1).map fun r => RV.keyVCL 1 r.1) ++
  ((vclResp δF hT hP V (bTr hT hP b) 2).map fun r => RV.keyVCL 2 r.1)

theorem vclServedKeys_length :
    (vclServedKeys δF hT hP V b).length ≤ ∑ a, vclRespBound hT hP V a := by
  rw [Fin.sum_univ_three]
  simp only [vclServedKeys, List.length_append, List.length_map]
  have h0 := vclResp_length δF hT hP V (bTr hT hP b) 0
  have h1 := vclResp_length δF hT hP V (bTr hT hP b) 1
  have h2 := vclResp_length δF hT hP V (bTr hT hP b) 2
  omega

/-- **`servedRoot`**: the decoded noun at the key's serial (validity / export) or root serial (path). -/
def vclServedRoot : RV.KeyVCL → Noun
  | .valid i => decodedNoun hT hP V b i
  | .export i _ => decodedNoun hT hP V b i
  | .path ri _ => decodedNoun hT hP V b ri

/-- The side child of a cell (`true` = right, axis `3`). -/
def sideChild (s : Bool) : Noun → Noun
  | .cell L R => if s then R else L
  | n => n

/-- **`served`**: validity — the decoded noun; export `(i, s)` — its side child; path
`(rootIdx, ax)` — `Noun.slot ax` of the decoded root. -/
def vclServed : RV.KeyVCL → Noun
  | .valid i => decodedNoun hT hP V b i
  | .export i s => sideChild s (decodedNoun hT hP V b i)
  | .path ri ax => (Noun.slot ax (decodedNoun hT hP V b ri)).getD (.atom 0)

theorem sideChild_leaves (s : Bool) (n : Noun) : (sideChild s n).leaves ≤ n.leaves := by
  cases n with
  | atom _ => exact le_refl _
  | cell L R => simp only [sideChild, Noun.leaves]; split_ifs <;> omega

/-- **The window** `2^110`, trace-free. -/
def vclWindow : ℕ := fuelChip

/-- **`served_leaves_le`** at every B0 message and every key (the cap). -/
theorem vclServed_leaves_le (κ : RV.KeyVCL) :
    (vclServedRoot hT hP V b κ).leaves ≤ vclWindow ∧ (vclServed hT hP V b κ).leaves ≤ vclWindow := by
  cases κ with
  | valid i => exact ⟨decodedNoun_leaves hT hP V b i, decodedNoun_leaves hT hP V b i⟩
  | «export» i s =>
    exact ⟨decodedNoun_leaves hT hP V b i,
      (sideChild_leaves s _).trans (decodedNoun_leaves hT hP V b i)⟩
  | path ri ax =>
    refine ⟨decodedNoun_leaves hT hP V b ri, ?_⟩
    show ((Noun.slot ax (decodedNoun hT hP V b ri)).getD (.atom 0)).leaves ≤ fuelChip
    cases hs : Noun.slot ax (decodedNoun hT hP V b ri) with
    | none => simp [Noun.leaves, fuelChip]
    | some n =>
      exact (RootGoodF.slot_leaves_le' ax _ hs).trans (decodedNoun_leaves hT hP V b ri)

end Family

/-! ## 3. Receipt: the validity axis -/

theorem validity_axis_one_serves {F K Kio : Type} [Field F] [Field K] [Algebra F K] [Field Kio]
    [DecidableEq Kio] {C : TableSpec} {S : MemShape} {hC : ℕ} (V : VerifierData F K hC S)
    (bc : B0Cols F C) (bm : ∀ t, B0Cols F (S.table t)) (r : Fin (RV.mVCL 0) → Kio) (n : Noun) :
    Noun.slot ((RV.recordViewVCL F K Kio C S hC).axis 0 V bc bm r) n = some n := by
  show Noun.slot 1 n = some n
  simp [Noun.slot]

/-! ## 4. The seed, the summands, `reqCond` -/

/-- Frame coin `2` (`z₁`). -/
def c2 : Fin frameVCL.n := ⟨2, by decide⟩
/-- Frame coin `3` (`z₂`). -/
def c3 : Fin frameVCL.n := ⟨3, by decide⟩

/-- **The VCL-L seed** `z′ = χ₂ + χ₃√δ` (frame coins `2, 3`, both M1). -/
def seedSpecVCL {K : Type} [Field K] (δ : K) [Fact (¬ IsSquare δ)] : SeedSpec frameVCL K (Quad δ) where
  seed χ := Quad.mk δ (χ c2) (χ c3)
  dep := ({c2, c3} : Finset (Fin frameVCL.n))
  readsOn χ χ' h := by
    show Quad.mk δ _ _ = Quad.mk δ _ _
    rw [h c2 (Finset.mem_insert_self _ _), h c3 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
  round0 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> decide
  inj χ χ' h := by
    obtain ⟨h1, h2⟩ := (Quad.mk_eq_mk_iff δ _ _ _ _).mp h
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact h1
    · exact h2

section Summands
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP : ℕ) {hC : ℕ} {C : TableSpec}
  (V : VerifierData F K hC (shapeV hT hP))

/-- The cell table's round-0 rows of a trace pair (its B0 columns only). -/
def rowsOfTr (tr : Traces F C (shapeV hT hP)) : List (CellRowB0 (ringChar F)) :=
  cellRowsB0 hT hP V (fun t => b0 (tr.2 t))

theorem rowsOfTr_length (tr : Traces F C (shapeV hT hP)) :
    (rowsOfTr hT hP V tr).length = V.memRows (tC hT hP) := by
  simp [rowsOfTr, cellRowsB0]

/-- Along a staged strategy the round-0 rows are coin-independent. -/
theorem rowsOfTr_const (Q : Coins frameVCL K → Traces F C (shapeV hT hP))
    (hQ : TracesStaged frameVCL C (shapeV hT hP) Q) (χ χ' : Coins frameVCL K) :
    rowsOfTr hT hP V (Q χ) = rowsOfTr hT hP V (Q χ') := by
  have e : (fun t => b0 ((Q χ).2 t)) = (fun t => b0 ((Q χ').2 t)) := by
    funext t j
    show (Q χ).2 t j.1 = (Q χ').2 t j.1
    exact hQ.2 t j.1 χ χ' (fun i hi => absurd hi (by rw [j.2]; omega))
  simp only [rowsOfTr, e]

/-- The census (T2, `skel := []`, priced at the skeleton majorant `3 + 19N`). -/
def vclCensus : BadSummand frameVCL K (Traces F C (shapeV hT hP)) (TracesStaged frameVCL C (shapeV hT hP)) :=
  vclCensusSummand (algebraMap F K δF) (TracesStaged frameVCL C (shapeV hT hP)) (rowsOfTr hT hP V)
    (fun _ => []) (V.memRows (tC hT hP)) V.N (fun tr => (rowsOfTr_length hT hP V tr).le)
    (fun _ => by simp) (fun Q hQ χ χ' => ⟨rowsOfTr_const hT hP V Q hQ χ χ', rfl⟩)

/-- The dyck-root event. -/
def vclDyck : BadSummand frameVCL K (Traces F C (shapeV hT hP)) (TracesStaged frameVCL C (shapeV hT hP)) :=
  vclCellDyckRootSummand (algebraMap F K δF) (TracesStaged frameVCL C (shapeV hT hP)) (rowsOfTr hT hP V)
    (V.memRows (tC hT hP)) (fun tr => (rowsOfTr_length hT hP V tr).le)
    (fun Q hQ χ χ' => rowsOfTr_const hT hP V Q hQ χ χ')

/-- **`summands`**: the zero seed (`SVFrame.zeroSummand` at `seedSpecVCL`, the joint list's own
object), the census, the dyck-root event — all seed events at coins `2, 3`, B0-const. -/
def vclSummands (_x : Unit) :
    List (BadSummand frameVCL K (Traces F C (shapeV hT hP)) (TracesStaged frameVCL C (shapeV hT hP))) :=
  [zeroSummand (F := F) (C := C) (S := shapeV hT hP) (Z := seedSpecVCL (algebraMap F K δF)),
    vclCensus δF hT hP V, vclDyck δF hT hP V]

/-- **Outside the summands**: the seed is nonzero, outside the census and outside the dyck-root
event, at the trace pair's round-0 rows. -/
theorem vclSummands_good (x : Unit) (tr : Traces F C (shapeV hT hP)) (χ : Coins frameVCL K)
    (h : ∀ s ∈ vclSummands δF hT hP V x, ¬ s.mem tr χ) :
    (seedSpecVCL (algebraMap F K δF)).seed χ ≠ 0 ∧
    (seedSpecVCL (algebraMap F K δF)).seed χ ∉
      tableBadSeeds (Kfp := Quad (algebraMap F K δF)) fuelChip (rowsOfTr hT hP V tr) [] ∧
    (seedSpecVCL (algebraMap F K δF)).seed χ ∉
      cellDyckRootSeeds (Kfp := Quad (algebraMap F K δF)) fuelChip (rowsOfTr hT hP V tr) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply h _ (List.mem_cons_self ..)
    unfold zeroSummand
    rw [seedSummand_mem]
    simp [h0]
  · intro hm
    apply h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    unfold vclCensus vclCensusSummand
    rw [tableCensusSummand_mem_iff]
    convert hm using 2
    rfl
  · intro hm
    apply h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    unfold vclDyck
    rw [vclCellDyckRootSummand_mem_iff]
    convert hm using 2
    rfl

/-- The summands read no coin and price `|𝕂|²` each. -/
theorem vclSummands_shape (x : Unit) :
    ∀ s ∈ vclSummands δF hT hP V (C := C) x, s.dep = ∅ ∨ s.dep ⊆ (seedSpecVCL (algebraMap F K δF)).dep := by
  intro s hs
  simp only [vclSummands, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · left; rfl
  · left; rfl
  · left; rfl

end Summands


/-! ## 5. The B0 rows of an accepted trace are the chip's cell table's round-0 rows -/

section Bridge
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP : ℕ) {hC : ℕ} {C : TableSpec}
  (V : VerifierData F K hC (shapeV hT hP))

/-- `cellB0Of` reads only the B0 columns `< 129`. -/
theorem cellB0Of_congr {e e' : Env F} (h : ∀ j < 129, e.trace j = e'.trace j) :
    cellB0Of e = cellB0Of e' := by
  simp only [cellB0Of, h Cell.idx (by decide), h Cell.idL (by decide), h Cell.idR (by decide),
    h Cell.wL (by decide), h Cell.wR (by decide), h Cell.aL (by decide), h Cell.aR (by decide),
    h Cell.lo (by decide), h Cell.hi (by decide), h Cell.loL (by decide), h Cell.hiL (by decide),
    h Cell.loR (by decide), h Cell.hiR (by decide), h Cell.carry (by decide), h Cell.mv (by decide),
    h Cell.mx (by decide)]

theorem round_cell0 (j : ℕ) (hj : j < 129) :
    ((shapeV hT hP).table (tC hT hP)).colRound ⟨j, by show j < 225; omega⟩ = 0 := by
  show Chips.Cell.colRoundT ⟨j, _⟩ = 0
  simp only [Chips.Cell.colRoundT, show Chips.Cell.b0CountS = 129 from rfl]
  rw [if_pos hj]

/-- **The bridge**: the round-0 rows the summands and the served nouns read (`rowsOfTr`, from the
B0 columns only) are the round-0 rows of the chip's cell table `cellTableOf` at the trace, at any
coins and publics. -/
theorem rowsOfTr_eq (Qc : Fin C.width → F[X])
    (Q : ∀ t : Fin (shapeV hT hP).k, Fin ((shapeV hT hP).table t).width → F[X])
    (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (χ : Coins frameVCL K) :
    rowsOfTr hT hP V (Qc, Q) =
      (cellTableOf δF V.basis (V.memNodes (tC hT hP)) (V.orbitM (tC hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y) (QC δF hT hP ρ y V χ Q)).map (·.b0) := by
  unfold rowsOfTr cellRowsB0 cellTableOf
  rw [List.map_ofFn]
  -- closes by unfolding: `cellB0Of` reads concrete B0 columns, whose `colRoundT` reduces to `0`
  congr 1

end Bridge

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
