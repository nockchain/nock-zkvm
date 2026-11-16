import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRowPerm

/-!

For `D D'` with the same atom cells, the same rows and permuted `walkRows`, `vxT9 vpT9 vhX9 vhP9` and hence
`pubsVOf9` agree (each public is a sum over the rows of a function of the row's trie label only). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPub

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
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAWR (idxRW walkRow0R)

noncomputable section Pub
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem sum_range_list {M : Type} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.range n, g k = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem range_map_wTrie9 (cells : List Noun) (reads : List (Noun × ℕ)) :
    (List.range (walkRows cells reads).length).map (wTrie cells reads) = walkRows cells reads := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, wTrie]
    rw [List.getD_eq_getElem _ _ h2]

theorem sum_range_wTrie9 {M : Type} [AddCommMonoid M] (cells : List Noun) (reads : List (Noun × ℕ))
    (F : NTree WN → M) :
    ∑ k ∈ Finset.range (walkRows cells reads).length, F (wTrie cells reads k) =
      ((walkRows cells reads).map F).sum := by
  rw [sum_range_list]
  conv_rhs => rw [← range_map_wTrie9 cells reads, List.map_map]
  rfl

theorem nVOf_eq (D : J8Data p Rg fuel s f r) (hne : D.preads ≠ []) :
    nVOf D = (walkRows D.acs D.preads).length := by
  simp only [nVOf, if_neg hne]

theorem krVOf_eq (D : J8Data p Rg fuel s f r) (hne : D.preads ≠ []) :
    krVOf D = krW D.acs D.preads := by
  simp only [krVOf, if_neg hne]

/-- The walk row read by the publics, built from the trie `t` alone (other fields are junk). -/
def rowA (acs : List Noun) (rI : Noun → ℕ) (χ : Coins frameJ8 K) (t : NTree WN) : WalkVals (ZMod p) K 𝕂′ :=
  { walkRow0R δ (GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2))) acs rI ([] : List (Noun × ℕ))
      (χ ⟨0, by decide⟩) (χ ⟨1, by decide⟩) 0 with
    idx := ((idxRW acs rI t : ℕ) : ZMod p)
    pre := ((axisFold t.label.bits : ℕ) : ZMod p)
    ridx := ((rI t.label.root : ℕ) : ZMod p)
    mL := ((t.label.mL : ℕ) : ZMod p)
    mR := ((t.label.mR : ℕ) : ZMod p)
    p := GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2)) t.label.node
    l := GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2)) (hdN t.label.node)
    r := GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2)) (tlN t.label.node)
    root := GlobalCarryRecognizer.enc (Quad.mk _ (χ cY1) (χ cY2)) t.label.root }

/-- Row term of `vxT9`. -/
def tX (acs : List Noun) (rI : Noun → ℕ) (χ : Coins frameJ8 K) (t : NTree WN) : 𝕂′ :=
  (walkFillInv δ (γV δ χ) (ρV δ χ) (rowA δ acs rI χ t)).xInv

/-- Row term of `vpT9`. -/
def tP (acs : List Noun) (rI : Noun → ℕ) (χ : Coins frameJ8 K) (t : NTree WN) : 𝕂′ :=
  wpTermV δ (walkFillInv δ (γV δ χ) (ρV δ χ) (rowA δ acs rI χ t))

/-- The right child value at the pointer, from the trie label. -/
def vRt (acs : List Noun) (rows : Array RowNX) (t : NTree WN) : ZMod p :=
  if (VclL.tlN t.label.node).isCell then ((ComplJ8Data.ptrP p acs rows t.label.node : ℕ) : ZMod p)
  else ((Nock.V1J8.Gen.hdl acs (VclL.tlN t.label.node)).2 : ZMod p)

/-- Row term of `vhX9` (the denominator before inversion). -/
def hXd (acs : List Noun) (rows : Array RowNX) (rI : Noun → ℕ) (χ : Coins frameJ8 K) (t : NTree WN) : 𝕂′ :=
  ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ) ((rowA δ acs rI χ t).idx,
    ((((Nock.V1J8.Gen.hdl acs (VclL.hdN t.label.node)).1 : ℕ) : ZMod p),
      (((Nock.V1J8.Gen.hdl acs (VclL.hdN t.label.node)).2 : ℕ) : ZMod p)),
    ((((Nock.V1J8.Gen.hdl acs (VclL.tlN t.label.node)).1 : ℕ) : ZMod p), vRt acs rows t))

/-- Row term of `vhP9`. -/
def hPt (acs : List Noun) (rows : Array RowNX) (rI : Noun → ℕ) (χ : Coins frameJ8 K) (t : NTree WN) : 𝕂′ :=
  liftQ δ ((t.label.mL : ℕ) : ZMod p) *
      (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((rowA δ acs rI χ t).ridx, 2 * (rowA δ acs rI χ t).pre,
        ((((Nock.V1J8.Gen.hdl acs (VclL.hdN t.label.node)).1 : ℕ) : ZMod p),
          (((Nock.V1J8.Gen.hdl acs (VclL.hdN t.label.node)).2 : ℕ) : ZMod p))))⁻¹ +
    liftQ δ ((t.label.mR : ℕ) : ZMod p) *
      (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((rowA δ acs rI χ t).ridx, 2 * (rowA δ acs rI χ t).pre + 1,
        ((((Nock.V1J8.Gen.hdl acs (VclL.tlN t.label.node)).1 : ℕ) : ZMod p), vRt acs rows t)))⁻¹

section Eq
variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

theorem vxT9_eq (D : J8Data p Rg fuel s f r) (hne : D.preads ≠ []) (χ : Coins frameJ8 K) :
    vxT9 δ D χ = ((walkRows D.acs D.preads).map fun t => tX δ D.acs (rIA D) χ t).sum := by
  rw [← sum_range_wTrie9, ← nVOf_eq D hne]
  unfold vxT9
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vR9_eq]
  rfl

theorem vpT9_eq (D : J8Data p Rg fuel s f r) (hne : D.preads ≠ []) (χ : Coins frameJ8 K) :
    vpT9 δ D χ = ((walkRows D.acs D.preads).map fun t => tP δ D.acs (rIA D) χ t).sum := by
  rw [← sum_range_wTrie9, ← nVOf_eq D hne]
  unfold vpT9
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vR9_eq]
  rfl

theorem vhX9_eq (D : J8Data p Rg fuel s f r) (hne : D.preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) (χ : Coins frameJ8 K) :
    vhX9 δ b D o χ = ((walkRows D.acs D.preads).map fun t => (hXd δ D.acs D.rows (rIA D) χ t)⁻¹).sum := by
  rw [← sum_range_wTrie9, ← nVOf_eq D hne]
  unfold vhX9
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < nVOf D := Finset.mem_range.mp hj
  unfold vdN9 WalkTraceHQ.dN
  rw [krVOf_eq D hne, dif_pos hj', (aw_dRow_split9 δ b D o hinj χ _ ⟨j, hj'⟩).1]
  rfl

theorem vhP9_eq (D : J8Data p Rg fuel s f r) (hne : D.preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) (χ : Coins frameJ8 K) :
    vhP9 δ b D o χ = ((walkRows D.acs D.preads).map fun t => hPt δ D.acs D.rows (rIA D) χ t).sum := by
  rw [← sum_range_wTrie9, ← nVOf_eq D hne]
  unfold vhP9
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < nVOf D := Finset.mem_range.mp hj
  unfold vdN9 WalkTraceHQ.dN
  have hs := aw_dRow_split9 δ b D o hinj χ (pubsV09 δ D χ) ⟨j, hj'⟩
  rw [krVOf_eq D hne, dif_pos hj', dif_pos hj', hs.2.1, hs.2.2]
  unfold WalkTraceH.cN
  simp only [dif_pos hj']
  rfl

variable {D D' : J8Data p Rg fuel s f r}

theorem rIA_eq (hc : D'.acs = D.acs) : rIA D' = rIA D := by
  simp only [rIA, hc]

theorem vxT9_perm (hc : D'.acs = D.acs) (hnil : D'.preads = [] ↔ D.preads = [])
    (hp : (walkRows D'.acs D'.preads).Perm (walkRows D.acs D.preads)) (χ : Coins frameJ8 K) :
    vxT9 δ D' χ = vxT9 δ D χ := by
  by_cases hn : D.preads = []
  · have hn' := hnil.mpr hn
    have he : D'.preads = D.preads := hn'.trans hn.symm
    simp only [vxT9, nVOf, vR9, rIA, hc, he]
  · have hn' : D'.preads ≠ [] := fun h => hn (hnil.mp h)
    rw [vxT9_eq δ D' hn', vxT9_eq δ D hn, rIA_eq hc, hc]
    rw [hc] at hp
    exact GenPortJ9AHRowPerm.sum_perm_of_map _ hp

theorem vpT9_perm (hc : D'.acs = D.acs) (hnil : D'.preads = [] ↔ D.preads = [])
    (hp : (walkRows D'.acs D'.preads).Perm (walkRows D.acs D.preads)) (χ : Coins frameJ8 K) :
    vpT9 δ D' χ = vpT9 δ D χ := by
  by_cases hn : D.preads = []
  · have hn' := hnil.mpr hn
    have he : D'.preads = D.preads := hn'.trans hn.symm
    simp only [vpT9, nVOf, vR9, rIA, hc, he]
  · have hn' : D'.preads ≠ [] := fun h => hn (hnil.mp h)
    rw [vpT9_eq δ D' hn', vpT9_eq δ D hn, rIA_eq hc, hc]
    rw [hc] at hp
    exact GenPortJ9AHRowPerm.sum_perm_of_map _ hp

theorem vhX9_perm (hc : D'.acs = D.acs) (hr : D'.rows = D.rows) (hnil : D'.preads = [] ↔ D.preads = [])
    (hp : (walkRows D'.acs D'.preads).Perm (walkRows D.acs D.preads))
    (hne : D.preads ≠ [])
    {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (nVOf D))) (hinj' : Function.Injective (powN o' (nVOf D')))
    (χ : Coins frameJ8 K) :
    vhX9 δ b D' o' χ = vhX9 δ b D o χ := by
  have hn' : D'.preads ≠ [] := fun h => hne (hnil.mp h)
  rw [vhX9_eq δ b D' hn' o' hinj', vhX9_eq δ b D hne o hinj, rIA_eq hc, hc, hr]
  rw [hc] at hp
  exact GenPortJ9AHRowPerm.sum_perm_of_map _ hp

theorem vhP9_perm (hc : D'.acs = D.acs) (hr : D'.rows = D.rows) (hnil : D'.preads = [] ↔ D.preads = [])
    (hp : (walkRows D'.acs D'.preads).Perm (walkRows D.acs D.preads))
    (hne : D.preads ≠ [])
    {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (nVOf D))) (hinj' : Function.Injective (powN o' (nVOf D')))
    (χ : Coins frameJ8 K) :
    vhP9 δ b D' o' χ = vhP9 δ b D o χ := by
  have hn' : D'.preads ≠ [] := fun h => hne (hnil.mp h)
  rw [vhP9_eq δ b D' hn' o' hinj', vhP9_eq δ b D hne o hinj, rIA_eq hc, hc, hr]
  rw [hc] at hp
  exact GenPortJ9AHRowPerm.sum_perm_of_map _ hp

theorem pubsVOf9_perm (hc : D'.acs = D.acs) (hr : D'.rows = D.rows) (hnil : D'.preads = [] ↔ D.preads = [])
    (hp : (walkRows D'.acs D'.preads).Perm (walkRows D.acs D.preads))
    {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (nVOf D))) (hinj' : Function.Injective (powN o' (nVOf D')))
    (χ : Coins frameJ8 K) :
    pubsVOf9 δ b D' o' χ = pubsVOf9 δ b D o χ := by
  funext i
  by_cases hn : D.preads = []
  · have hn' := hnil.mpr hn
    simp only [pubsVOf9, hn, hn', if_true]
  · have hn' : D'.preads ≠ [] := fun h => hn (hnil.mp h)
    simp only [pubsVOf9, pubsV09, if_neg hn, if_neg hn']
    rw [vxT9_perm δ hc hnil hp, vpT9_perm δ hc hnil hp, vhX9_perm δ b hc hr hnil hp hn o o' hinj hinj',
      vhP9_perm δ b hc hr hnil hp hn o o' hinj hinj']

end Eq

end Pub

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPub

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPub.vxT9_perm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPub.vpT9_perm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPub.vhX9_perm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPub.vhP9_perm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWPub.pubsVOf9_perm
