import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRowPerm

/-!

`famAWV9`/`famAWH9` entries read only the trie label of the row (`p l r root idx pre ridx`) and, for `awHx9`,
the handles of the row's node (`hdl acs`) and the pointer `ptrP p acs rows`. So they are invariant under a
permutation of `walkRows` (generic records `D D'` with the same cells and rows). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec quadPole)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAWR (idxRW walkRow0R)
open Nock.V1J8.Gen (P)

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWFam

noncomputable section Fam
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The atom-walk row read by the families, built from the trie `t` alone (other fields are junk). -/
def rowTA (acs : List Noun) (rI : Noun → ℕ) (χ : Coins frameJ8 K) (t : NTree WN) : WalkVals (ZMod p) K 𝕂′ :=
  { walkRow0R δ (GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2))) acs rI ([] : List (Noun × ℕ))
      (χ ⟨0, by decide⟩) (χ ⟨1, by decide⟩) 0 with
    idx := ((idxRW acs rI t : ℕ) : ZMod p)
    pre := ((VclL.axisFold t.label.bits : ℕ) : ZMod p)
    ridx := ((rI t.label.root : ℕ) : ZMod p)
    p := GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2)) t.label.node
    l := GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2)) (VclL.hdN t.label.node)
    r := GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2)) (VclL.tlN t.label.node)
    root := GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2)) t.label.root
    mL := (((t.label.mL : ℕ)) : ZMod p)
    mR := (((t.label.mR : ℕ)) : ZMod p) }

/-- The entries of `awVx9` built from the trie `t`. -/
def gVA (acs : List Noun) (rI : Noun → ℕ) (t : NTree WN) : List (Coins frameJ8 K → 𝕂′) :=
  [fun χ => FiniteIO.compress (m := 11) ⟨γV δ χ, 0⟩ (wxKeyV δ (rowTA δ acs rI χ t)),
   fun χ => FiniteIO.compress (m := 8) ⟨γV δ χ, 0⟩ (wrecLV δ (rowTA δ acs rI χ t)),
   fun χ => FiniteIO.compress (m := 8) ⟨γV δ χ, 0⟩ (wrecRV δ (rowTA δ acs rI χ t))]

/-- The entries of `awHx9` built from the trie `t`, the handle map `H` and the pointer map `ptr`. -/
def gHA (acs : List Noun) (rI : Noun → ℕ) (ptr : Noun → ℕ) (H : Noun → ℕ × ℕ) (t : NTree WN) :
    List (Coins frameJ8 K → 𝕂′) :=
  [fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((rowTA δ acs rI χ t).idx,
      ((((H (VclL.hdN t.label.node)).1 : ℕ) : ZMod p), (((H (VclL.hdN t.label.node)).2 : ℕ) : ZMod p)),
      ((((H (VclL.tlN t.label.node)).1 : ℕ) : ZMod p),
        (if (VclL.tlN t.label.node).isCell then ((ptr t.label.node : ℕ) : ZMod p)
         else (((H (VclL.tlN t.label.node)).2 : ℕ) : ZMod p)))),
   fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((rowTA δ acs rI χ t).ridx, 2 * (rowTA δ acs rI χ t).pre,
      ((((H (VclL.hdN t.label.node)).1 : ℕ) : ZMod p), (((H (VclL.hdN t.label.node)).2 : ℕ) : ZMod p))),
   fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((rowTA δ acs rI χ t).ridx, 2 * (rowTA δ acs rI χ t).pre + 1,
      ((((H (VclL.tlN t.label.node)).1 : ℕ) : ZMod p),
        (if (VclL.tlN t.label.node).isCell then ((ptr t.label.node : ℕ) : ZMod p)
         else (((H (VclL.tlN t.label.node)).2 : ℕ) : ZMod p))))]

theorem awVx9_label (D : J8Data p Rg fuel s f r) (j : ℕ) :
    awVx9 δ D j (K := K) = gVA δ D.acs (ComplJ8Data.rIAP p D.acs) (wTrie D.acs D.preads j) := rfl

theorem awHx9_label (D : J8Data p Rg fuel s f r) (j : ℕ) (hj : j < nVOf D) :
    awHx9 δ D j (K := K) = gHA δ D.acs (ComplJ8Data.rIAP p D.acs) (ComplJ8Data.ptrP p D.acs D.rows)
      (Nock.V1J8.Gen.hdl D.acs) (wTrie D.acs D.preads j) := by
  simp only [awHx9, dif_pos hj]
  rfl

theorem range_map_wTrieA (cells : List Noun) (reads : List (Noun × ℕ)) :
    (List.range (walkRows cells reads).length).map (wTrie cells reads) = walkRows cells reads := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, wTrie]
    rw [List.getD_eq_getElem _ _ h2]

theorem flatMap_wTrie {α : Type} (cells : List Noun) (reads : List (Noun × ℕ)) (g : NTree WN → List α) :
    (List.range (walkRows cells reads).length).flatMap (fun j => g (wTrie cells reads j)) =
      (walkRows cells reads).flatMap g := by
  conv_rhs => rw [← range_map_wTrieA cells reads]
  rw [List.flatMap_map]

theorem walkRows_length_pos(cells : List Noun) (reads : List (Noun × ℕ)) : 0 < (walkRows cells reads).length :=
  lt_of_lt_of_le (one_le_krW cells reads) (krW_le_rows cells reads)

theorem nVOf_eq_length (D : J8Data p Rg fuel s f r) (hne : D.preads ≠ []) :
    nVOf D = (walkRows D.acs D.preads).length := by
  simp [nVOf, hne]

theorem nVOf_perm (D D' : J8Data p Rg fuel s f r) (hnil : D'.preads = [] ↔ D.preads = [])
    (hp : (walkRows D'.acs D'.preads).Perm (walkRows D.acs D.preads)) : nVOf D' = nVOf D := by
  by_cases h : D.preads = []
  · simp [nVOf, h, hnil.mpr h]
  · have h' : D'.preads ≠ [] := fun e => h (hnil.mp e)
    simp only [nVOf, h, h', if_false]
    exact hp.length_eq

theorem famAWV9_eq_range (D : J8Data p Rg fuel s f r) :
    famAWV9 δ D (K := K) = (List.range (nVOf D)).flatMap fun j =>
      (gVA δ D.acs (ComplJ8Data.rIAP p D.acs) (wTrie D.acs D.preads j) (K := K)).map
        (quadPole δ WeightsJ8.c5) := by
  unfold famAWV9
  refine List.flatMap_congr ?_
  intro j hj
  rw [awVx9_label δ D j]

theorem famAWH9_eq_range (D : J8Data p Rg fuel s f r) :
    famAWH9 δ D (K := K) = (List.range (nVOf D)).flatMap fun j =>
      (gHA δ D.acs (ComplJ8Data.rIAP p D.acs) (ComplJ8Data.ptrP p D.acs D.rows) (Nock.V1J8.Gen.hdl D.acs)
        (wTrie D.acs D.preads j) (K := K)).map (quadPole δ InhabJ8Good.c12) := by
  unfold famAWH9
  refine List.flatMap_congr ?_
  intro j hj
  rw [awHx9_label δ D j (List.mem_range.mp hj)]

theorem famAWV9_eq_flatMap (D : J8Data p Rg fuel s f r) (hne : D.preads ≠ []) :
    famAWV9 δ D (K := K) = (walkRows D.acs D.preads).flatMap fun t =>
      (gVA δ D.acs (ComplJ8Data.rIAP p D.acs) t (K := K)).map (quadPole δ WeightsJ8.c5) := by
  rw [famAWV9_eq_range, nVOf_eq_length D hne]
  exact flatMap_wTrie D.acs D.preads (fun t => (gVA δ D.acs (ComplJ8Data.rIAP p D.acs) t (K := K)).map
    (quadPole δ WeightsJ8.c5))

theorem famAWH9_eq_flatMap (D : J8Data p Rg fuel s f r) (hne : D.preads ≠ []) :
    famAWH9 δ D (K := K) = (walkRows D.acs D.preads).flatMap fun t =>
      (gHA δ D.acs (ComplJ8Data.rIAP p D.acs) (ComplJ8Data.ptrP p D.acs D.rows) (Nock.V1J8.Gen.hdl D.acs) t
        (K := K)).map (quadPole δ InhabJ8Good.c12) := by
  rw [famAWH9_eq_range, nVOf_eq_length D hne]
  exact flatMap_wTrie D.acs D.preads (fun t => (gHA δ D.acs (ComplJ8Data.rIAP p D.acs)
    (ComplJ8Data.ptrP p D.acs D.rows) (Nock.V1J8.Gen.hdl D.acs) t (K := K)).map (quadPole δ InhabJ8Good.c12))

theorem famAWV9_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.acs = D.acs)
    (hnil : D'.preads = [] ↔ D.preads = [])
    (hp : (walkRows D'.acs D'.preads).Perm (walkRows D.acs D.preads)) :
    (famAWV9 δ D' (K := K)).Perm (famAWV9 δ D) := by
  by_cases hn : D.preads = []
  · have hn' : D'.preads = D.preads := by rw [hn, hnil.mpr hn]
    rw [famAWV9_eq_range, famAWV9_eq_range, nVOf_perm D D' hnil hp, hc, hn']
  · have hn' : D'.preads ≠ [] := fun e => hn (hnil.mp e)
    rw [hc] at hp
    exact GenPortJ9AHRowPerm.fam_perm_of_flatMap (famAWV9_eq_flatMap δ D hn)
      (by rw [famAWV9_eq_flatMap δ D' hn', hc]) hp

theorem famAWH9_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.acs = D.acs) (hr : D'.rows = D.rows)
    (hnil : D'.preads = [] ↔ D.preads = [])
    (hp : (walkRows D'.acs D'.preads).Perm (walkRows D.acs D.preads)) :
    (famAWH9 δ D' (K := K)).Perm (famAWH9 δ D) := by
  by_cases hn : D.preads = []
  · have hn' : D'.preads = D.preads := by rw [hn, hnil.mpr hn]
    rw [famAWH9_eq_range, famAWH9_eq_range, nVOf_perm D D' hnil hp, hc, hr, hn']
  · have hn' : D'.preads ≠ [] := fun e => hn (hnil.mp e)
    rw [hc] at hp
    exact GenPortJ9AHRowPerm.fam_perm_of_flatMap (famAWH9_eq_flatMap δ D hn)
      (by rw [famAWH9_eq_flatMap δ D' hn', hc, hr]) hp

theorem famAWV9_good_of_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.acs = D.acs)
    (hnil : D'.preads = [] ↔ D.preads = [])
    (hp : (walkRows D'.acs D'.preads).Perm (walkRows D.acs D.preads)) (χ : Coins frameJ8 K)
    (h : ∀ e ∈ famAWV9 δ D (K := K), χ ∉ e.ev) : ∀ e ∈ famAWV9 δ D' (K := K), χ ∉ e.ev :=
  GenPortJ9AHRowPerm.good_of_fam_perm (fun e => ((e.ev : Finset (Coins frameJ8 K)) : Set (Coins frameJ8 K))) (famAWV9_perm δ D D' hc hnil hp) χ h

theorem famAWH9_good_of_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.acs = D.acs) (hr : D'.rows = D.rows)
    (hnil : D'.preads = [] ↔ D.preads = [])
    (hp : (walkRows D'.acs D'.preads).Perm (walkRows D.acs D.preads)) (χ : Coins frameJ8 K)
    (h : ∀ e ∈ famAWH9 δ D (K := K), χ ∉ e.ev) : ∀ e ∈ famAWH9 δ D' (K := K), χ ∉ e.ev :=
  GenPortJ9AHRowPerm.good_of_fam_perm (fun e => ((e.ev : Finset (Coins frameJ8 K)) : Set (Coins frameJ8 K))) (famAWH9_perm δ D D' hc hr hnil hp) χ h

#print axioms awVx9_label
#print axioms awHx9_label
#print axioms range_map_wTrieA
#print axioms walkRows_length_pos
#print axioms nVOf_eq_length
#print axioms nVOf_perm
#print axioms famAWV9_eq_range
#print axioms famAWH9_eq_range
#print axioms famAWV9_eq_flatMap
#print axioms famAWH9_eq_flatMap
#print axioms famAWV9_perm
#print axioms famAWH9_perm
#print axioms famAWV9_good_of_perm
#print axioms famAWH9_good_of_perm

end Fam

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWFam
