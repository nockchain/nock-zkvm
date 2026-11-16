import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkFam
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRowPerm

/-!

* `pubsWOf_perm`: for `D D'` with the same cells and handle map and permuted `walkRows`, `pubsWOf` agrees
  (each public is a sum over the rows of a function of the row's trie label only).
* `walkOK_at`: D1a's `walkOK_run_at` at a generic record `D` (`hcl`, `hkp` as hypotheses). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkPub

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkFam
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

noncomputable section Pub
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem sum_range_list {M : Type} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.range n, g k = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem sum_range_wTrie {M : Type} [AddCommMonoid M] (cells : List Noun) (reads : List (Noun × ℕ))
    (F : NTree WN → M) :
    ∑ k ∈ Finset.range (walkRows cells reads).length, F (wTrie cells reads k) =
      ((walkRows cells reads).map F).sum := by
  rw [sum_range_list]
  conv_rhs => rw [← range_map_wTrie cells reads, List.map_map]
  rfl

/-- The walk row read by the publics, built from the trie `t` alone (adds `mL mR` to `rowT`). -/
def rowM (cells : List Noun) (χ : Coins frameJ8 K) (t : NTree WN) : WalkVals (ZMod p) K 𝕂′ :=
  { rowT δ cells χ t with mL := ((t.label.mL : ℕ) : ZMod p), mR := ((t.label.mR : ℕ) : ZMod p) }

/-- Row term of `wxT`. -/
def tX (cells : List Noun) (t : NTree WN) (χ : Coins frameJ8 K) : 𝕂′ :=
  (walkFillInv δ (γV δ χ) (ρV δ χ) (rowM δ cells χ t)).xInv

/-- Row term of `wpT`. -/
def tP (cells : List Noun) (t : NTree WN) (χ : Coins frameJ8 K) : 𝕂′ :=
  wpTermV δ (walkFillInv δ (γV δ χ) (ρV δ χ) (rowM δ cells χ t))

/-- Row term of `whX`. -/
def hX (cells : List Noun) (H : Noun → ℕ × ℕ) (t : NTree WN) (χ : Coins frameJ8 K) : 𝕂′ :=
  (ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ) ((rowT δ cells χ t).idx,
      ((((H (hdN t.label.node)).1 : ℕ) : ZMod p), (((H (hdN t.label.node)).2 : ℕ) : ZMod p)),
      ((((H (tlN t.label.node)).1 : ℕ) : ZMod p), (((H (tlN t.label.node)).2 : ℕ) : ZMod p))))⁻¹

/-- Row term of `whP`. -/
def hP (cells : List Noun) (H : Noun → ℕ × ℕ) (t : NTree WN) (χ : Coins frameJ8 K) : 𝕂′ :=
  liftQ δ ((t.label.mL : ℕ) : ZMod p) *
      (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((rowT δ cells χ t).ridx, 2 * (rowT δ cells χ t).pre,
        ((((H (hdN t.label.node)).1 : ℕ) : ZMod p), (((H (hdN t.label.node)).2 : ℕ) : ZMod p))))⁻¹ +
    liftQ δ ((t.label.mR : ℕ) : ZMod p) *
      (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((rowT δ cells χ t).ridx, 2 * (rowT δ cells χ t).pre + 1,
        ((((H (tlN t.label.node)).1 : ℕ) : ZMod p), (((H (tlN t.label.node)).2 : ℕ) : ZMod p))))⁻¹

theorem wxT_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    wxT δ D χ = ((walkRows D.cells D.reads).map fun t => tX δ D.cells t χ).sum := by
  rw [← sum_range_wTrie]
  rfl

theorem wpT_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) :
    wpT δ D χ = ((walkRows D.cells D.reads).map fun t => tP δ D.cells t χ).sum := by
  rw [← sum_range_wTrie]
  rfl

theorem whX_eq (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (walkRows D.cells D.reads).length)) (χ : Coins frameJ8 K) :
    whX δ b D o χ = ((walkRows D.cells D.reads).map fun t => hX δ D.cells D.H t χ).sum := by
  rw [← sum_range_wTrie]
  unfold whX
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  unfold wdN WalkTraceHQ.dN
  rw [dif_pos hj', (walk_dRow_split δ b D o hinj χ (pubsW0 δ D χ) ⟨j, hj'⟩).1]
  rfl

theorem whP_eq (D : J8Data p Rg fuel s f r) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (walkRows D.cells D.reads).length)) (χ : Coins frameJ8 K) :
    whP δ b D o χ = ((walkRows D.cells D.reads).map fun t => hP δ D.cells D.H t χ).sum := by
  rw [← sum_range_wTrie]
  unfold whP
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  unfold wdN WalkTraceHQ.dN
  have hs := walk_dRow_split δ b D o hinj χ (pubsW0 δ D χ) ⟨j, hj'⟩
  rw [dif_pos hj', dif_pos hj', hs.2.1, hs.2.2]
  unfold WalkTraceH.cN
  simp only [dif_pos hj']
  rfl

theorem wxT_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.cells = D.cells)
    (hp : (walkRows D'.cells D'.reads).Perm (walkRows D.cells D.reads)) (χ : Coins frameJ8 K) :
    wxT δ D' χ = wxT δ D χ := by
  rw [wxT_eq, wxT_eq, hc]
  rw [hc] at hp
  exact GenPortJ9AHRowPerm.sum_perm_of_map _ hp

theorem wpT_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.cells = D.cells)
    (hp : (walkRows D'.cells D'.reads).Perm (walkRows D.cells D.reads)) (χ : Coins frameJ8 K) :
    wpT δ D' χ = wpT δ D χ := by
  rw [wpT_eq, wpT_eq, hc]
  rw [hc] at hp
  exact GenPortJ9AHRowPerm.sum_perm_of_map _ hp

theorem whX_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.cells = D.cells) (hH : D'.H = D.H)
    (hp : (walkRows D'.cells D'.reads).Perm (walkRows D.cells D.reads))
    {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (walkRows D.cells D.reads).length))
    (hinj' : Function.Injective (powN o' (walkRows D'.cells D'.reads).length)) (χ : Coins frameJ8 K) :
    whX δ b D' o' χ = whX δ b D o χ := by
  rw [whX_eq δ b D' o' hinj', whX_eq δ b D o hinj, hc, hH]
  rw [hc] at hp
  exact GenPortJ9AHRowPerm.sum_perm_of_map _ hp

theorem whP_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.cells = D.cells) (hH : D'.H = D.H)
    (hp : (walkRows D'.cells D'.reads).Perm (walkRows D.cells D.reads))
    {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (walkRows D.cells D.reads).length))
    (hinj' : Function.Injective (powN o' (walkRows D'.cells D'.reads).length)) (χ : Coins frameJ8 K) :
    whP δ b D' o' χ = whP δ b D o χ := by
  rw [whP_eq δ b D' o' hinj', whP_eq δ b D o hinj, hc, hH]
  rw [hc] at hp
  exact GenPortJ9AHRowPerm.sum_perm_of_map _ hp

theorem pubsWOf_perm (D D' : J8Data p Rg fuel s f r) (hc : D'.cells = D.cells) (hH : D'.H = D.H)
    (hp : (walkRows D'.cells D'.reads).Perm (walkRows D.cells D.reads))
    {h h' : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (o' : StrictOrbitDomain (ZMod p) 3 h')
    (hinj : Function.Injective (powN o (walkRows D.cells D.reads).length))
    (hinj' : Function.Injective (powN o' (walkRows D'.cells D'.reads).length))
    (χ : Coins frameJ8 K) :
    pubsWOf δ b D' o' χ = pubsWOf δ b D o χ := by
  funext i
  unfold pubsWOf pubsW0
  rw [wxT_perm δ D D' hc hp, wpT_perm δ D D' hc hp, whX_perm δ b D D' hc hH hp o o' hinj hinj',
    whP_perm δ b D D' hc hH hp o o' hinj hinj']

end Pub

section Obl
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **`walkOK_run_at` at a generic record `D`** (`hcl`, `hkp` as hypotheses instead of `Rows31`/`lt31`). -/
theorem walkOK_at (D : J8Data p Rg fuel s f r) (hp63 : 2 ^ 63 < p) (hcl : D.cells.length < p)
    (hkp : krW D.cells D.reads + (walkRows D.cells D.reads).length < p)
    (hwalk : ComplJ8Walk.WalkDepthOK D.reads)
    (hHk : ∀ x : Noun, ((D.H x).1 : ZMod p) = 0 ∨ ((D.H x).1 : ZMod p) = 1 ∨ ((D.H x).1 : ZMod p) = 2)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (walkRows D.cells D.reads).length))
    (hadj : ∀ (i : Fin (walkRows D.cells D.reads).length)
      (hi : (i : ℕ) + 1 < (walkRows D.cells D.reads).length),
      powN o (walkRows D.cells D.reads).length ⟨(i : ℕ) + 1, hi⟩ =
        powN o (walkRows D.cells D.reads).length i * o.ω)
    (χ : Coins frameJ8 K)
    (hV : ∀ e ∈ famWalkV δ D (K := K), χ ∉ e.ev)
    (hH : ∀ e ∈ famWalkH δ D (K := K), χ ∉ e.ev) :
    (WalkJ8.walkChipJ8 δ (krW D.cells D.reads) b (walk_pos D.cells D.reads)
        (powN o (walkRows D.cells D.reads).length) o (chalsMJ8 δ χ) (pubsWOf δ b D o χ)).rap.Satisfies
      (fun j => ComplJ8Enc.walkTrWE δ b (walk_pos D.cells D.reads)
        (powN o (walkRows D.cells D.reads).length) o (chalsMJ8 δ) (pubsWOf δ b D o) (γV δ) (ρV δ)
        (encR δ) D.cells D.reads (kLW D) (vLW D) (kRW D) (vRW D) χ
        (Fin.cast (WalkJ8.walkChipJ8_width δ (krW D.cells D.reads) b (walk_pos D.cells D.reads)
          (powN o (walkRows D.cells D.reads).length) o (chalsMJ8 δ χ) (pubsWOf δ b D o χ)) j)) ∧
    (WalkJ8.walkChipJ8 δ (krW D.cells D.reads) b (walk_pos D.cells D.reads)
        (powN o (walkRows D.cells D.reads).length) o (chalsMJ8 δ χ) (pubsWOf δ b D o χ)).BindsPreprocessing
      (fun j => ComplJ8Enc.walkTrWE δ b (walk_pos D.cells D.reads)
        (powN o (walkRows D.cells D.reads).length) o (chalsMJ8 δ) (pubsWOf δ b D o) (γV δ) (ρV δ)
        (encR δ) D.cells D.reads (kLW D) (vLW D) (kRW D) (vRW D) χ
        (Fin.cast (WalkJ8.walkChipJ8_width δ (krW D.cells D.reads) b (walk_pos D.cells D.reads)
          (powN o (walkRows D.cells D.reads).length) o (chalsMJ8 δ χ) (pubsWOf δ b D o χ)) j)) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hrows := famWalkV_good δ D χ hV
  have hcl' : D.cells.length < ringChar (ZMod p) := by rw [hrc]; exact hcl
  have hkp' : krW D.cells D.reads + (walkRows D.cells D.reads).length < ringChar (ZMod p) := by
    rw [hrc]; exact hkp
  have hpoleH : ∀ (i : Fin (walkRows D.cells D.reads).length),
      ∀ x ∈ walkHx δ D i (K := K), ComplJ8Bad.ρH δ χ + x χ ≠ 0 := by
    intro i x hx
    refine ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 x χ _ (ComplJ8Bad.ρH_re δ χ) (hH _ ?_)
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hsplit := walk_dRow_split δ b D o hinj χ
    (pubsWOf δ b D o χ)
  have hwalk' := ComplJ8Enc.walkChipJ8_honest_listE δ b (walk_pos _ _) (powN o _) o
    (chalsMJ8 δ χ) (pubsWOf δ b D o χ) (encR δ χ) (γV δ χ) (ρV δ χ) _ _ (kLW _) (vLW _) (kRW _) (vRW _)
    (GeneratedField.primeFieldElems_zmod p) (by rw [hrc]; exact hp63) hcl' hwalk hkp' rfl hinj hadj
    (ProbJ8.chalsOK_J8 δ χ) (fun j hj => (hrows j hj).1) (fun j hj => (hrows j hj).2.1)
    (fun j hj => (hrows j hj).2.2) (pub2_mk2 δ (wxT δ D χ) 0 rfl).symm (pub2_mk2 δ (wpT δ D χ) 2 rfl).symm
    (fun i => hHk _) (fun i => hHk _)
    (fun i => by
      rw [(hsplit i).1]
      exact hpoleH i (fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).idx, (kLW _ i, vLW _ i),
        (kRW _ i, vRW _ i))) (by simp only [walkHx, dif_pos i.isLt]; exact List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.1]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).ridx, 2 * (wValsC δ _ χ i).pre,
        (kLW _ i, vLW _ i))) (by simp only [walkHx, dif_pos i.isLt]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.2]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).ridx, 2 * (wValsC δ _ χ i).pre + 1,
        (kRW _ i, vRW _ i))) (by
          simp only [walkHx, dif_pos i.isLt]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    ?_ ?_
  · exact hwalk'
  · show Quad.mk _ (pub2 δ (whX δ b D o χ) 4) (pub2 δ (whX δ b D o χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b D o hinj χ (pubsW0 δ D χ) (pubsWOf δ b D o χ) _ (Or.inl rfl)]
  · show Quad.mk _ (pub2 δ (whP δ b D o χ) 6) (pub2 δ (whP δ b D o χ) 7) = _
    rw [pub2_mk2 δ _ 6 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b D o hinj χ (pubsW0 δ D χ) (pubsWOf δ b D o χ) _ (Or.inr (Or.inl rfl)),
      dN_pubs δ b D o hinj χ (pubsW0 δ D χ) (pubsWOf δ b D o χ) _ (Or.inr (Or.inr rfl))]

end Obl

#print axioms sum_range_list
#print axioms sum_range_wTrie
#print axioms wxT_eq
#print axioms wpT_eq
#print axioms whX_eq
#print axioms whP_eq
#print axioms wxT_perm
#print axioms wpT_perm
#print axioms whX_perm
#print axioms whP_perm
#print axioms pubsWOf_perm
#print axioms walkOK_at

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkPub
