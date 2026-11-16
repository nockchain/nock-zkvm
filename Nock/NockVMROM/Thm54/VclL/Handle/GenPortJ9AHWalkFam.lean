import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRowPerm

/-!

`famWalkV`/`famWalkH` entries read only the trie label of the row (`p l r root idx pre ridx` and,
for `walkHx`, the handles of the row's node), so they are invariant under a permutation of
`walkRows` (generic records `D D'` with the same cells and handle map). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkFam

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec quadPole)

noncomputable section Fam
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The walk row read by the families, built from the trie `t` alone (other fields are junk). -/
def rowT (cells : List Noun) (χ : Coins frameJ8 K) (t : NTree WN) : WalkVals (ZMod p) K 𝕂′ :=
  { ComplJ8Enc.walkRow0E δ (encR δ χ) cells ([] : List (Noun × ℕ)) (χ ⟨0, by decide⟩) (χ ⟨1, by decide⟩) 0 with
    idx := ((cells.idxOf t.label.node : ℕ) : ZMod p)
    pre := ((axisFold t.label.bits : ℕ) : ZMod p)
    ridx := ((cells.idxOf t.label.root : ℕ) : ZMod p)
    p := encR δ χ t.label.node
    l := encR δ χ (hdN t.label.node)
    r := encR δ χ (tlN t.label.node)
    root := encR δ χ t.label.root }

/-- The entries of `walkVx` built from the trie `t`. -/
def gV (cells : List Noun) (t : NTree WN) : List (Coins frameJ8 K → 𝕂′) :=
  [fun χ => FiniteIO.compress (m := 11) ⟨γV δ χ, 0⟩ (wxKeyV δ (rowT δ cells χ t)),
   fun χ => FiniteIO.compress (m := 8) ⟨γV δ χ, 0⟩ (wrecLV δ (rowT δ cells χ t)),
   fun χ => FiniteIO.compress (m := 8) ⟨γV δ χ, 0⟩ (wrecRV δ (rowT δ cells χ t))]

/-- The entries of `walkHx` built from the trie `t` and the handle map `H`. -/
def gH (cells : List Noun) (H : Noun → ℕ × ℕ) (t : NTree WN) : List (Coins frameJ8 K → 𝕂′) :=
  [fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((rowT δ cells χ t).idx,
      ((((H (hdN t.label.node)).1 : ℕ) : ZMod p), (((H (hdN t.label.node)).2 : ℕ) : ZMod p)),
      ((((H (tlN t.label.node)).1 : ℕ) : ZMod p), (((H (tlN t.label.node)).2 : ℕ) : ZMod p))),
   fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((rowT δ cells χ t).ridx, 2 * (rowT δ cells χ t).pre,
      ((((H (hdN t.label.node)).1 : ℕ) : ZMod p), (((H (hdN t.label.node)).2 : ℕ) : ZMod p))),
   fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((rowT δ cells χ t).ridx, 2 * (rowT δ cells χ t).pre + 1,
      ((((H (tlN t.label.node)).1 : ℕ) : ZMod p), (((H (tlN t.label.node)).2 : ℕ) : ZMod p)))]

theorem walkVx_label (D : J8Data p Rg fuel s f r) (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) :
    walkVx δ D j (K := K) = gV δ D.cells (wTrie D.cells D.reads j) := rfl

theorem walkHx_label (D : J8Data p Rg fuel s f r) (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) :
    walkHx δ D j (K := K) = gH δ D.cells D.H (wTrie D.cells D.reads j) := by
  simp only [walkHx, dif_pos hj]
  rfl

theorem range_map_wTrie (cells : List Noun) (reads : List (Noun × ℕ)) :
    (List.range (walkRows cells reads).length).map (wTrie cells reads) = walkRows cells reads := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, wTrie]
    rw [List.getD_eq_getElem _ _ h2]

theorem famWalkV_eq_flatMap (D : J8Data p Rg fuel s f r) :
    famWalkV δ D (K := K) = (walkRows D.cells D.reads).flatMap fun t =>
      (gV δ D.cells t (K := K)).map (quadPole δ WeightsJ8.c5) := by
  rw [← range_map_wTrie D.cells D.reads, List.flatMap_map]
  unfold famWalkV
  refine List.flatMap_congr ?_
  intro j hj
  rw [walkVx_label δ D j (List.mem_range.mp hj)]

theorem famWalkH_eq_flatMap (D : J8Data p Rg fuel s f r) :
    famWalkH δ D (K := K) = (walkRows D.cells D.reads).flatMap fun t =>
      (gH δ D.cells D.H t (K := K)).map (quadPole δ InhabJ8Good.c12) := by
  rw [← range_map_wTrie D.cells D.reads, List.flatMap_map]
  unfold famWalkH
  refine List.flatMap_congr ?_
  intro j hj
  rw [walkHx_label δ D j (List.mem_range.mp hj)]

theorem famWalkV_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.cells = D.cells)
    (hp : (walkRows D'.cells D'.reads).Perm (walkRows D.cells D.reads)) :
    (famWalkV δ D' (K := K)).Perm (famWalkV δ D) := by
  rw [hc] at hp
  exact GenPortJ9AHRowPerm.fam_perm_of_flatMap (famWalkV_eq_flatMap δ D)
    (by rw [famWalkV_eq_flatMap δ D', hc]) hp

theorem famWalkH_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.cells = D.cells) (hH : D'.H = D.H)
    (hp : (walkRows D'.cells D'.reads).Perm (walkRows D.cells D.reads)) :
    (famWalkH δ D' (K := K)).Perm (famWalkH δ D) := by
  rw [hc] at hp
  exact GenPortJ9AHRowPerm.fam_perm_of_flatMap (famWalkH_eq_flatMap δ D)
    (by rw [famWalkH_eq_flatMap δ D', hc, hH]) hp

theorem famWalkV_good_of_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.cells = D.cells)
    (hp : (walkRows D'.cells D'.reads).Perm (walkRows D.cells D.reads)) (χ : Coins frameJ8 K)
    (h : ∀ e ∈ famWalkV δ D (K := K), χ ∉ e.ev) : ∀ e ∈ famWalkV δ D' (K := K), χ ∉ e.ev :=
  GenPortJ9AHRowPerm.good_of_fam_perm (fun e => ((e.ev : Finset (Coins frameJ8 K)) : Set (Coins frameJ8 K))) (famWalkV_perm δ D D' hc hp) χ h

theorem famWalkH_good_of_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.cells = D.cells) (hH : D'.H = D.H)
    (hp : (walkRows D'.cells D'.reads).Perm (walkRows D.cells D.reads)) (χ : Coins frameJ8 K)
    (h : ∀ e ∈ famWalkH δ D (K := K), χ ∉ e.ev) : ∀ e ∈ famWalkH δ D' (K := K), χ ∉ e.ev :=
  GenPortJ9AHRowPerm.good_of_fam_perm (fun e => ((e.ev : Finset (Coins frameJ8 K)) : Set (Coins frameJ8 K))) (famWalkH_perm δ D D' hc hH hp) χ h

#print axioms walkVx_label
#print axioms walkHx_label
#print axioms range_map_wTrie
#print axioms famWalkV_eq_flatMap
#print axioms famWalkH_eq_flatMap
#print axioms famWalkV_perm
#print axioms famWalkH_perm
#print axioms famWalkV_good_of_perm
#print axioms famWalkH_good_of_perm

end Fam

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkFam
