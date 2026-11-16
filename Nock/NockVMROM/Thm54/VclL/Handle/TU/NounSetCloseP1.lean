/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/NounSetCloseP1.lean

 **Closing the noun-set hypotheses of `NounSetP1.r0M_auxM_final` (trace uniqueness, P1 fragment).**

 * §1 the cell-table decoder against the row decoder: on a `TableM` table with `RowServed`, every row that the
 two-provider decoder `denK` decodes is the row noun `nounOf` (a weighted child names a row of positive rank,
 so the rank-`(0, 0)` external branch never fires on it). **`hDN_of_rows`** (table level) and
 **`hDN_of_accepts`** (at an accepted trace, `D = denK (cellTable.map b0) ext`, `ext` atoms only;
 `extB_atoms` for the atom table's `extB`).
 * §2 the honest roots: on the six fragment states every row's `m` is an atom, and `sf1`, `sf2` are `atom 0`,
 a child evaluation, or the row's own subject / evaluation. With the positional bridge (`RowBridgeP1`) every
 honest root that is a cell is denoted by a chip handle: **`hrowsC_of_agree`**, **`hrowsC_of_bridge`**,
 **`hrowsC_of_twin`** (from the extraction twins' `RowsAccXI ∧ ForestReconGoal` and the root denotations).
 * §3 the multiplicities: `mv mx mx1 mh` are the consumer counts `cntOf` (`CountsP1.*_eq_count` read through
 the side row values), **`mulCounts_of_balances`**; equal consumer lists and equal row keys give equal counts,
 **`hcnt_of_lists`**.
 * §4 **`r0M_auxM_closed`**: `r0M_auxM_final` with §1–§3 plugged in.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CountsP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1
import Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1

noncomputable section

open Nock Nock.Reified Nock.Framework Polynomial Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)

/-! ## 1. The cell-table decoder is the row decoder -/

section Decode
variable {p : ℕ} [Fact p.Prime] {q : ℕ}

/-- **The B0 rows `tB` read the row values `v`** on the child columns: weight, serial, inline atom and rank
limbs of both sides, row by row. -/
def RowsRead (tB : List (CellRowB0 q)) (v : ℕ → ℕ → ZMod p) (n : ℕ) : Prop :=
  tB.length = n ∧ ∀ i (hi : i < tB.length),
    tB[i].wL = decide (v i Cell.wL = 1) ∧ tB[i].idL = (v i Cell.idL).val ∧ tB[i].aL.val = (v i Cell.aL).val ∧
    tB[i].loL = (v i Cell.loL).val ∧ tB[i].hiL = (v i Cell.hiL).val ∧
    tB[i].wR = decide (v i Cell.wR = 1) ∧ tB[i].idR = (v i Cell.idR).val ∧ tB[i].aR.val = (v i Cell.aR).val ∧
    tB[i].loR = (v i Cell.loR).val ∧ tB[i].hiR = (v i Cell.hiR).val

variable {v : ℕ → ℕ → ZMod p} {n : ℕ}

/-- One side of a decoded row: a weighted side of nonzero rank is followed to the row noun of its serial, an
unweighted side is its inline atom. -/
theorem side_eq {tB : List (CellRowB0 q)} {ext : ℕ → Option Noun} {f : ℕ}
    (ih : ∀ i X, decodeTree tB (leaf2 q ext) f i = some X → i < n ∧ X = nounOf v i)
    {c : CellRowB0 q} {s : Side} {i w sid a lo hi : ℕ} {A : Noun}
    (hw : c.wS s = decide (v i w = 1)) (hid : c.idS s = (v i sid).val) (ha : (c.aS s).val = (v i a).val)
    (hlo : c.loS s = (v i lo).val) (hhi : c.hiS s = (v i hi).val)
    (hrk : v i w = 1 → (v i hi).val * 2 ^ 62 + (v i lo).val ≠ 0)
    (hch : VclL.childT tB (leaf2 q ext) f c s = some A) :
    A = if v i w = 1 then nounOf v (v i sid).val else .atom (v i a).val := by
  unfold VclL.childT leaf2 at hch
  by_cases h1 : v i w = 1
  · simp only [h1, ↓reduceIte]
    have hwt : c.wS s = true := by rw [hw]; exact decide_eq_true h1
    have h0 : ¬ (c.hiS s = 0 ∧ c.loS s = 0) := by
      rw [hhi, hlo]; rintro ⟨e1, e2⟩; exact hrk h1 (by rw [e1, e2]; rfl)
    simp only [hwt, h0, ite_true, ite_false] at hch
    rw [← hid]; exact (ih _ _ hch).2
  · simp only [h1, ↓reduceIte]
    have hwf : c.wS s = false := by rw [hw]; exact decide_eq_false h1
    simp only [hwf, Bool.false_eq_true, ite_false, Option.some.injEq] at hch
    rw [← hch, ha]

/-- **The decoder at any fuel decodes a row to its row noun.** -/
theorem decode_eq_nounOf (T : TableM v n) (S : RowServed v n) (hp : 2 ^ 63 < p) (hnp : n ≤ p)
    {tB : List (CellRowB0 q)} (hR : RowsRead tB v n) (ext : ℕ → Option Noun) :
    ∀ f i X, decodeTree tB (leaf2 q ext) f i = some X → i < n ∧ X = nounOf v i := by
  intro f
  induction f with
  | zero => intro i X h; simp [decodeTree] at h
  | succ f ih =>
    intro i X h
    rw [decodeTree_succ] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, a, ha, b', hb, hX⟩ := h
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
    have hin : i < n := hR.1 ▸ hi
    obtain ⟨hwL, hidL, haL, hloL, hhiL, hwR, hidR, haR, hloR, hhiR⟩ := hR.2 i hi
    have hsplit := rank_split T S hp hnp hin
    obtain ⟨-, -, -, lw⟩ := side_facts (sid := Cell.idL) T hp hnp hin (atomL T hin) (T.cell hin).wL (S i hin).1
    obtain ⟨-, -, -, rw'⟩ := side_facts (sid := Cell.idR) T hp hnp hin (atomR T hin) (T.cell hin).wR (S i hin).2
    have posL : v i Cell.wL = 1 → (v i Cell.hiL).val * 2 ^ 62 + (v i Cell.loL).val ≠ 0 := fun h1 => by
      obtain ⟨hj, -, -, -, hr⟩ := lw h1
      have := rank_split T S hp hnp hj
      omega
    have posR : v i Cell.wR = 1 → (v i Cell.hiR).val * 2 ^ 62 + (v i Cell.loR).val ≠ 0 := fun h1 => by
      obtain ⟨hj, -, -, -, hr⟩ := rw' h1
      have := rank_split T S hp hnp hj
      omega
    have eA := side_eq (s := .L) ih hwL hidL haL hloL hhiL posL ha
    have eB := side_eq (s := .R) ih hwR hidR haR hloR hhiR posR hb
    refine ⟨hin, ?_⟩
    obtain rfl : Noun.cell a b' = X := Option.some.inj hX
    rw [nounOf, decN_succ, eA, eB]
    refine congrArg₂ Noun.cell ?_ ?_
    · split_ifs with h1
      · obtain ⟨hj, -, -, -, hr⟩ := lw h1
        exact (child_noun T S hp hnp hin hj (by omega)).symm
      · rfl
    · split_ifs with h1
      · obtain ⟨hj, -, -, -, hr⟩ := rw' h1
        exact (child_noun T S hp hnp hin hj (by omega)).symm
      · rfl

/-- **`hDN_of_rows`**: the two-provider handle decoder of B0 rows that read a served `TableM` table, with an
external provider that names atoms only, decodes every handle denoting a cell to some row noun. -/
theorem hDN_of_rows (T : TableM v n) (S : RowServed v n) (hp : 2 ^ 63 < p) (hnp : n ≤ p)
    {tB : List (CellRowB0 q)} (hR : RowsRead tB v n) {ext : ℕ → Option Noun}
    (hext : ∀ j X, ext j = some X → ∃ a, X = .atom a) :
    ∀ hd A B, denK tB ext hd = some (.cell A B) → ∃ i < n, nounOf v i = .cell A B := by
  rintro ⟨k, j⟩ A B h
  rcases k with _ | _ | _ | k
  · simp [denK] at h
  · obtain ⟨hj, e⟩ := decode_eq_nounOf T S hp hnp hR ext _ _ _ h
    exact ⟨j, hj, e.symm⟩
  · obtain ⟨a, ha⟩ := hext j _ h
    exact absurd ha (by simp)
  · simp [denK] at h

/-- The atom table's external provider names atoms only. -/
theorem extB_atoms (q' : ℕ) (rA : ℕ → AtomChipHQ.ARow) :
    ∀ j X, AtomBigJ8.extB q' rA j = some X → ∃ a, X = .atom a := by
  intro j X h
  unfold AtomBigJ8.extB at h
  split_ifs at h with he
  exact ⟨_, (Option.some.inj h).symm⟩

end Decode

/-! ### At an accepted trace -/

section DecodeAccepts
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- `natOf` on `ZMod p` is `val`. -/
theorem natOf_zmod (x : ZMod p) : natOf x = x.val := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hx : x.val < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact ZMod.val_lt x
  have := natOf_natCast hF hx
  rwa [ZMod.natCast_zmod_val] at this

/-- **The accepted cell table's B0 rows read the side row values `vM`.** -/
theorem rowsRead_of_accepts {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    {ax : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) :
    RowsRead ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))).map (·.b0)) (vM tr ax Pb.orbitC.ω) Pb.nC := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hPb := h.2.hPb
  subst hPb
  refine ⟨by simp [cellTableOf], fun i hi => ?_⟩
  have hi' : i < (canonPb hpG sz c).nC := by simpa [cellTableOf] using hi
  have e : ∀ j, j < 129 → (cellEnvF b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC
        (chalsMJ8 δ χ) M.pubsC (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC)) ⟨i, hi'⟩).trace j =
      vM tr ax (canonPb hpG sz c).orbitC.ω i j := fun j hj => cellEnvF_vM δ b tr ax i hi' hj
  have hrow : ((cellTableOf δ b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC
        (chalsMJ8 δ χ) M.pubsC (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC))).map (·.b0))[i] =
      cellB0Of (cellEnvF b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC
        (chalsMJ8 δ χ) M.pubsC (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC)) ⟨i, hi'⟩) := by
    simp [cellTableOf, cellRowOf]
  have hval : ∀ x : ZMod p, (((natOf x : ℕ) : ZMod (ringChar (ZMod p)))).val = x.val := fun x => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (natOf_lt hF x), natOf_zmod]
  rw [hrow]
  simp only [cellB0Of]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e _ (by decide)]
  · rw [e _ (by decide), natOf_zmod]
  · rw [hval, e _ (by decide)]
  · rw [e _ (by decide), natOf_zmod]
  · rw [e _ (by decide), natOf_zmod]
  · rw [e _ (by decide)]
  · rw [e _ (by decide), natOf_zmod]
  · rw [hval, e _ (by decide)]
  · rw [e _ (by decide), natOf_zmod]
  · rw [e _ (by decide), natOf_zmod]

/-- **`hDN_of_accepts`**: at an accepted trace whose restricted cell table is validity-served, the chip's handle
decoder `denK (cellTable.map b0) ext` (with an external provider naming atoms only, e.g. `extB`) decodes every
handle denoting a cell to some row noun `nounOf (vM …)`. This is `NounSetP1`'s `hDN`. -/
theorem hDN_of_accepts {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    {ax : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))))
    {ext : ℕ → Option Noun} (hext : ∀ j X, ext j = some X → ∃ a, X = .atom a) :
    ∀ hd A B, denK ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))).map (·.b0)) ext hd = some (.cell A B) →
      ∃ i < Pb.nC, nounOf (vM tr ax Pb.orbitC.ω) i = .cell A B := by
  obtain ⟨T, S, -⟩ := nounLink_of_accepts δ b h hS
  have hnp : Pb.nC ≤ p := by
    have := h.1.hnpC; rw [ZMod.ringChar_zmod_n] at this; omega
  exact hDN_of_rows T S (hp63_of hpG) hnp (rowsRead_of_accepts δ b h) hext

end DecodeAccepts

/-! ## 2. The honest roots are denoted -/

section Roots
open Nock.Edit Nock.Walk
open Nock.Edit.GenX (P1Frag genX genChainF genChain mkX SkelX RowNX rowOfSkelX kidE handleNounsX
  genComputeSkeletonX)
open Nock.V1J8.Gen (rootsOf)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX nd RowVSX kidsX)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1 (RowAgreeX KidsAgree rowBridge rowOfSkelX_core)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)

/-- The six states of the fragment `{0, 7, 10, autocons}`. -/
def FragSt (s : StateX) : Prop := s = .s0 ∨ s = .s7 ∨ s = .cons ∨ s = .s10 ∨ s = .s10L ∨ s = .s10T

theorem inTree_mkX {st : StateX} {s f e : Noun} {ks : List (NTree SkelX)} {u : NTree SkelX}
    (h : InTree (mkX st s f e ks) u) : u.label.state = st ∨ ∃ k ∈ ks, InTree k u := by
  cases h with
  | here => left; rfl
  | sub hs hu => right; exact ⟨_, hs, hu⟩

/-- Every node of an edit chain is an `s10L` or `s10T` node. -/
theorem chain_frag (old e : Noun) : ∀ k a u, InTree (genChainF old e k a) u → FragSt u.label.state := by
  intro k
  induction k with
  | zero =>
    intro a u h
    rw [genChainF] at h
    rcases inTree_mkX h with h | ⟨k, hk, -⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · simp at hk
  | succ k ih =>
    intro a u h
    rw [genChainF] at h
    split_ifs at h
    · rcases inTree_mkX h with h | ⟨k', hk, hu⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · rw [List.mem_singleton] at hk; subst hk; exact ih _ _ hu
    · rcases inTree_mkX h with h | ⟨k', hk, -⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · simp at hk

/-- **Every node of the generated tree of a fragment formula is in one of the six fragment states.** -/
theorem genX_frag {R : Nock.Jet.Registry} {f : Noun} (hfrag : P1Frag f) :
    ∀ {n : ℕ} {s r : Noun} {t : NTree SkelX}, genX R n s f = some (t, r) →
      ∀ u, InTree t u → FragSt u.label.state := by
  induction hfrag with
  | op0 ax =>
    intro n s r t h u hu
    rcases n with _ | n
    · simp [genComputeSkeletonX] at h
    cases hsl : Noun.slot ax s with
    | none => simp [genComputeSkeletonX, hsl] at h
    | some v =>
      simp only [genComputeSkeletonX, hsl, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases inTree_mkX hu with h | ⟨k, hk, -⟩
      · exact Or.inl h
      · simp at hk
  | @op7 b c _ _ ihb ihc =>
    intro n s r t h u hu
    rcases n with _ | n
    · simp [genComputeSkeletonX] at h
    cases hb : genX R n s b with
    | none => simp [genComputeSkeletonX, hb] at h
    | some p =>
      obtain ⟨tH, sb⟩ := p
      cases hc : genX R n sb c with
      | none => simp [genComputeSkeletonX, hb, hc] at h
      | some q =>
        obtain ⟨tM, r'⟩ := q
        simp only [genComputeSkeletonX, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases inTree_mkX hu with h | ⟨k, hk, hku⟩
        · exact Or.inr (Or.inl h)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl
          · exact ihc hc u hku
          · exact ihb hb u hku
  | @op10 ax c d _ _ ihc ihd =>
    intro n s r t h u hu
    rcases n with _ | n
    · simp [genComputeSkeletonX] at h
    cases hc : genX R n s c with
    | none => simp [genComputeSkeletonX, hc] at h
    | some p =>
      obtain ⟨tN, new⟩ := p
      cases hd : genX R n s d with
      | none => simp [genComputeSkeletonX, hc, hd] at h
      | some q =>
        obtain ⟨tO, old⟩ := q
        cases hed : Noun.edit ax new old with
        | none => simp [genComputeSkeletonX, hc, hd, hed] at h
        | some e =>
          simp only [genComputeSkeletonX, hc, hd, hed, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases inTree_mkX hu with h | ⟨k, hk, hku⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl
            · exact ihc hc u hku
            · exact ihd hd u hku
            · exact chain_frag _ _ _ _ u hku
  | @cons b c d _ _ ihbc ihd =>
    intro n s r t h u hu
    rcases n with _ | n
    · simp [genComputeSkeletonX] at h
    cases hbc : genX R n s (.cell b c) with
    | none => simp [genComputeSkeletonX, hbc] at h
    | some p =>
      obtain ⟨tl0, l⟩ := p
      cases hd : genX R n s d with
      | none => simp [genComputeSkeletonX, hbc, hd] at h
      | some q =>
        obtain ⟨tr0, r'⟩ := q
        simp only [genComputeSkeletonX, hbc, hd, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases inTree_mkX hu with h | ⟨k, hk, hku⟩
        · exact Or.inr (Or.inr (Or.inl h))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl
          · exact ihbc hbc u hku
          · exact ihd hd u hku

/-- On the fragment states the honest row's `m` is an atom (`atom 0`, or the `s10L` sibling axis). -/
theorem m_atom {sk : SkelX} (h : FragSt sk.state) : ∃ k, (rowOfSkelX sk).m = .atom k := by
  rcases h with h | h | h | h | h | h <;> simp [rowOfSkelX, h]

/-- `sf1` is `atom 0`, the first child's evaluation, or the row's subject (every state). -/
theorem sf1_cases (sk : SkelX) : (rowOfSkelX sk).sf1 = .atom 0 ∨ (rowOfSkelX sk).sf1 = kidE sk 0 ∨
    (rowOfSkelX sk).sf1 = sk.subject := by
  cases h : sk.state <;> simp [rowOfSkelX, h]

/-- `sf2` is `atom 0`, the second child's evaluation, or the row's evaluation (every state). -/
theorem sf2_cases (sk : SkelX) : (rowOfSkelX sk).sf2 = .atom 0 ∨ (rowOfSkelX sk).sf2 = kidE sk 1 ∨
    (rowOfSkelX sk).sf2 = sk.evaluation := by
  cases h : sk.state <;> simp [rowOfSkelX, h]

theorem kidE_cell {sk : SkelX} {i : ℕ} {A B : Noun} (h : kidE sk i = .cell A B) :
    ∃ hi : i < sk.kids.length, (sk.kids[i]).evaluation = .cell A B := by
  unfold kidE at h
  cases hk : sk.kids[i]? with
  | none => rw [hk] at h; simp at h
  | some k =>
    rw [hk] at h
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hk
    exact ⟨hi, by simpa using h⟩

theorem den_of_nd {D : HX → Option Noun} {h : HX} {X : Noun} {A B : Noun} (e : nd D h = X)
    (hc : X = .cell A B) : ∃ hd, D hd = some X := by
  refine ⟨h, ?_⟩
  subst hc
  unfold nd at e
  cases hD : D h with
  | none => rw [hD] at e; simp at e
  | some y => rw [hD] at e; simp at e; rw [e]

/-- A child evaluation that is a cell is denoted (through the decoded row's child triple). -/
theorem kid_den {D : HX → Option Noun} {d : RowVSX} {sk : SkelX} (hk : KidsAgree D d sk) {i : ℕ}
    {A B : Noun} (h : kidE sk i = .cell A B) : ∃ hd, D hd = some (kidE sk i) := by
  obtain ⟨hi, he⟩ := kidE_cell h
  have h1 : i < (kidsX d).length := by rw [hk.1]; exact hi
  rw [h]
  exact den_of_nd ((hk.2 i h1 hi).2.2.trans he) rfl

/-- **`hrowsC_of_agree`**: if every node of the honest tree agrees with some decoded row (`RowAgreeX`) and is in
a fragment state, and the claim's three nouns are denoted, then every honest root `rootsOf x (rowsOfT tg)` that
is a cell is denoted by some handle. The roots outside a row's active handles are `atom 0` or atoms (`m`). -/
theorem hrowsC_of_agree {D : HX → Option Noun} (x : P8PublicClaim) {tg : NTree SkelX}
    (hs : ∃ h, D h = some x.subject) (hf : ∃ h, D h = some x.formula) (he : ∃ h, D h = some x.result)
    (hag : ∀ u ∈ bfsForest [tg], (∃ d, RowAgreeX D d u.label) ∧ FragSt u.label.state) :
    ∀ X ∈ rootsOf x (rowsOfT tg), ∀ A B, X = .cell A B → ∃ hd, D hd = some X := by
  intro X hX A B hc
  simp only [rootsOf, rowsOfT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.toList_toArray, List.mem_map] at hX
  rcases hX with (rfl | rfl | rfl) | ⟨r, ⟨u, hu, rfl⟩, hX⟩
  · exact hs
  · exact hf
  · exact he
  obtain ⟨⟨d, hst, hsub, hfor, hev, hkid, -⟩, hfr⟩ := hag u hu
  obtain ⟨c1, c2, c3, c4⟩ := rowOfSkelX_core u.label
  simp only [handleNounsX, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [c2] at hc ⊢; exact den_of_nd hsub hc
  · rw [c3] at hc ⊢; exact den_of_nd hfor hc
  · rw [c4] at hc ⊢; exact den_of_nd hev hc
  · rcases sf1_cases u.label with e | e | e <;> rw [e] at hc ⊢
    · exact absurd hc (by simp)
    · exact kid_den hkid hc
    · exact den_of_nd hsub hc
  · rcases sf2_cases u.label with e | e | e <;> rw [e] at hc ⊢
    · exact absurd hc (by simp)
    · exact kid_den hkid hc
    · exact den_of_nd hev hc
  · obtain ⟨k, hk⟩ := m_atom hfr
    rw [hk] at hc; exact absurd hc (by simp)

/-- **`hrowsC_of_bridge`**: from the positional bridge's conclusion (`RowBridgeP1.rowBridge`: the BFS list of the
generated tree `tg` agrees node by node with the decoded rows), the fragment formula and the root denotations. -/
theorem hrowsC_of_bridge {D : HX → Option Noun} {R : Nock.Jet.Registry} (x : P8PublicClaim) {fuel : ℕ}
    {tg : NTree SkelX} {r : Noun} (hfrag : P1Frag x.formula) (hg : genX R fuel x.subject x.formula = some (tg, r))
    {n : ℕ} {d : ℕ → RowVSX}
    (hB : (bfsForest [tg]).length = n ∧ ∀ j (hj : j < (bfsForest [tg]).length),
      RowAgreeX D (d j) ((bfsForest [tg])[j]'hj).label)
    (hs : ∃ h, D h = some x.subject) (hf : ∃ h, D h = some x.formula) (he : ∃ h, D h = some x.result) :
    ∀ X ∈ rootsOf x (rowsOfT tg), ∀ A B, X = .cell A B → ∃ hd, D hd = some X := by
  refine hrowsC_of_agree x hs hf he fun u hu => ⟨?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hu
    exact ⟨_, hB.2 j hj⟩
  · obtain ⟨c0, hc0, hcu⟩ := (mem_bfsForest [tg] u).mp hu
    rw [List.mem_singleton] at hc0; subst hc0
    exact genX_frag hfrag hg u hcu

end Roots

section RootsTwin
open Nock.Edit Nock.Walk
open Nock.Edit.GenX (P1Frag genX SkelX)
open Nock.V1J8.Gen (rootsOf)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1 (rowBridge)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]

/-- **`hrowsC_of_twin`**: `hrowsC` at a chip decoder `D` from the extraction twins' conclusion (the compute walk's
row accumulator `RowsAccXI` and its forest goal, as returned by `TwinLinkJ8A.hsoundJ8XUA_ex` /
`TwinHokLJ8GA.acceptsJ8_holdsN_finalLGA_ex` at `D = denJ8 …`), the root row's three handle denotations, the
fragment formula and the generated tree. -/
theorem hrowsC_of_twin [CharP K p] (hp : 2 ^ 63 + 1 < p) {R : Nock.Jet.Registry} (hR : R.Faithful)
    {D : HX → Option Noun} (hD : DenOKX p D) {n : ℕ} (hn : 1 ≤ n) {E : ℕ → Env (ZMod p)} {st : ℕ → StateX}
    {comb : ℕ → Noun} (x : P8PublicClaim) (A : RowsAccXI n E st D R comb)
    (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n)
    (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (he : D (hdV (E 0) xE) = some x.result) (hfrag : P1Frag x.formula) {fuel : ℕ} {tg : NTree SkelX} {r : Noun}
    (hg : genX R fuel x.subject x.formula = some (tg, r)) :
    ∀ X ∈ rootsOf x (rowsOfT tg), ∀ A B, X = .cell A B → ∃ hd, D hd = some X :=
  hrowsC_of_bridge x hfrag hg (rowBridge (K := K) hp hR hD hn A hG x hs hf hfrag hg) ⟨_, hs⟩ ⟨_, hf⟩ ⟨_, he⟩

end RootsTwin

/-! ## 3. The multiplicities are consumer counts -/

section Counts

/-- **The consumer counts** of the four balances at row `i`: validity (`kV`), export side `0` / `1` (`kX0`,
`kX1`, one request list), handle export (`kH`). -/
def cntOf {αV αX αH : Type} [DecidableEq αV] [DecidableEq αX] [DecidableEq αH] (rV : List αV) (kV : ℕ → αV)
    (rX : List αX) (kX0 kX1 : ℕ → αX) (rH : List αH) (kH : ℕ → αH) : Fin 4 → ℕ → ℕ :=
  fun k i => ![rV.count (kV i), rX.count (kX0 i), rX.count (kX1 i), rH.count (kH i)] k

/-- **`hcnt_of_lists`**: equal consumer lists and equal row keys give equal consumer counts. -/
theorem hcnt_of_lists {αV αX αH : Type} [DecidableEq αV] [DecidableEq αX] [DecidableEq αH] {n : ℕ}
    {rV rV' : List αV} {kV kV' : ℕ → αV} {rX rX' : List αX} {kX0 kX0' kX1 kX1' : ℕ → αX}
    {rH rH' : List αH} {kH kH' : ℕ → αH} (hV : rV = rV') (hX : rX = rX') (hH : rH = rH')
    (hkV : ∀ i < n, kV i = kV' i) (hkX0 : ∀ i < n, kX0 i = kX0' i) (hkX1 : ∀ i < n, kX1 i = kX1' i)
    (hkH : ∀ i < n, kH i = kH' i) :
    ∀ k, ∀ i < n, cntOf rV kV rX kX0 kX1 rH kH k i = cntOf rV' kV' rX' kX0' kX1' rH' kH' k i := by
  intro k i hi
  subst hV hX hH
  fin_cases k <;> simp [cntOf, hkV i hi, hkX0 i hi, hkX1 i hi, hkH i hi]

end Counts

section CountsAccepts
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The restricted cell trace of an accepted message. -/
abbrev qCell (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) :=
  restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)

/-- Row `i`'s validity key (`0` off the table). -/
def keyVOf (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (i : ℕ) : Fin 5 → 𝕂′ :=
  if hi : i < Pb.nC then keyVec δ 5 Cell.vKeyP
    (cellEnvK δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr) ⟨i, hi⟩)
    (cellEnvF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr) ⟨i, hi⟩) else 0

/-- Row `i`'s export key on side `s` (`0` off the table). -/
def keyXOf (s : ZMod p) (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (i : ℕ) :
    Fin 11 → 𝕂′ :=
  if hi : i < Pb.nC then keyVec δ 11 (Cell.xKeyS s)
    (cellEnvK δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr) ⟨i, hi⟩)
    (cellEnvF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr) ⟨i, hi⟩) else 0

/-- Row `i`'s handle-export key (`0` off the table). -/
def keyHOf (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (i : ℕ) : Fin 5 → K :=
  if hi : i < Pb.nC then ServeH.keyVec5 (K := K) (TwoProviderQ.keyHK (F := ZMod p))
    (TwoProviderQ.hqkEF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) ⟨i, hi⟩)
    else 0

/-- **`mulCounts_of_balances`**: at an accepted trace, given each balance's per-record count form
(`fibre_counts`'s conclusion `hbal*` over a provider list `provs*` with pairwise distinct keys `hd*` containing the
cell table's own providers `hsub*`), the four multiplicity columns of the side row values are the consumer counts
`cntOf` at the row keys. -/
theorem mulCounts_of_balances {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    {ax : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g)
    (reqsV : List (Fin 5 → 𝕂′)) (provsV : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hbalV : ∀ r, (reqsV.count r : 𝕂′) = pw provsV r) (hdV : (provsV.map Prod.fst).Nodup)
    (hsubV : ∀ q ∈ liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)),
      q ∈ provsV)
    (reqsX : List (Fin 11 → 𝕂′)) (provsX : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbalX : ∀ r, (reqsX.count r : 𝕂′) = pw provsX r) (hdX : (provsX.map Prod.fst).Nodup)
    (hsubX : ∀ q ∈ liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)),
      q ∈ provsX)
    (reqsH : List (Fin 5 → K)) (provsH : List ((Fin 5 → K) × K))
    (hbalH : ∀ r, (reqsH.count r : K) = pw provsH r) (hdH : (provsH.map Prod.fst).Nodup)
    (hsubH : ∀ q ∈ cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC),
      q ∈ provsH) :
    MulCounts (vM tr ax Pb.orbitC.ω) Pb.nC
      (cntOf reqsV (keyVOf δ b Pb χ M tr) reqsX (keyXOf δ b 0 Pb χ M tr) (keyXOf δ b 1 Pb χ M tr)
        reqsH (keyHOf δ b Pb χ M tr)) := by
  have hPb := h.2.hPb
  subst hPb
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [← cellEnvF_vM δ b tr ax i hi (by decide),
      CountsP1.mv_eq_count (δF := δ) (b := b) (nodes := _) (orbit := _) (chals := _) (pubs := _)
        (Q := qCell δ b _ χ M tr) reqsV provsV hbalV hdV hsubV ⟨i, hi⟩]
    simp [cntOf, keyVOf, hi]
  · rw [← cellEnvF_vM δ b tr ax i hi (by decide),
      CountsP1.mx_eq_count (δF := δ) (b := b) (nodes := _) (orbit := _) (chals := _) (pubs := _)
        (Q := qCell δ b _ χ M tr) reqsX provsX hbalX hdX hsubX ⟨i, hi⟩]
    simp [cntOf, keyXOf, hi]
  · rw [← cellEnvF_vM δ b tr ax i hi (by decide),
      CountsP1.mx1_eq_count (δF := δ) (b := b) (nodes := _) (orbit := _) (chals := _) (pubs := _)
        (Q := qCell δ b _ χ M tr) reqsX provsX hbalX hdX hsubX ⟨i, hi⟩]
    simp [cntOf, keyXOf, hi]
  · rw [← hqkEF_vM δ b tr ax i hi (by decide),
      CountsP1.mh_eq_count (b := b) (nodes := _) (orbit := _) (chals := _) (pubs := _)
        (Q := qM δ b _ tr (chalsMJ8 δ χ) M.pubsC) reqsH provsH hbalH hdH hsubH ⟨i, hi⟩]
    simp [cntOf, keyHOf, hi]

/-- **The handle-export providers have pairwise distinct keys** (`hdH` when the provider list is
`cellProvsW`, as in the J-8 balance): the key's first entry is the row serial, injective on a `TableM` table
(`TableM.idx_inj`, the `records_nodup` argument). -/
theorem cellProvsW_nodup {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    {ax : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) :
    ((cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)).map Prod.fst).Nodup := by
  obtain ⟨T, -⟩ := tableM_of_accepts δ b h
  have hnp : Pb.nC ≤ p := by
    have := h.1.hnpC; rw [ZMod.ringChar_zmod_n] at this; omega
  have hPb := h.2.hPb
  subst hPb
  simp only [cellProvsW, List.map_map]
  refine (List.nodup_finRange _).map fun i j hij => Fin.ext ?_
  have h0 : algebraMap (ZMod p) K
        ((TwoProviderQ.hqkEF b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC
          (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC) i).trace Cell.idx) =
      algebraMap (ZMod p) K
        ((TwoProviderQ.hqkEF b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC
          (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC) j).trace Cell.idx) := congrFun hij 0
  have h1 := (algebraMap (ZMod p) K).injective h0
  have ea := hqkEF_vM δ b tr ax (c := c) (M := M) (χ := χ) (sz := sz) (hpG := hpG) i i.2 (j := Cell.idx) (by decide)
  have eb := hqkEF_vM δ b tr ax (c := c) (M := M) (χ := χ) (sz := sz) (hpG := hpG) j j.2 (j := Cell.idx) (by decide)
  exact T.idx_inj hnp i.2 j.2 (ea.symm.trans (h1.trans eb))

/-- The validity key's last entry is the row serial. -/
theorem keyVec_vKeyP_idx (eK : Env K) (eF : Env (ZMod p)) :
    keyVec δ 5 Cell.vKeyP eK eF 4 = liftQ δ (eF.trace Cell.idx) := by
  simp [keyVec, Cell.vKeyP, QFP.entries, QE.var, ev_base, cv, CoeffExpr.eval]

/-- The export key's serial entry (`9`). -/
theorem keyVec_xKeyS_idx (s : ZMod p) (eK : Env K) (eF : Env (ZMod p)) :
    keyVec δ 11 (Cell.xKeyS s) eK eF 9 = liftQ δ (eF.trace Cell.idx) := by
  simp [keyVec, Cell.xKeyS, Cell.xKey, QFP.entries, QE.var, ev_base, cv, CoeffExpr.eval]

/-- The export key's side entry (`10`). -/
theorem keyVec_xKeyS_side (s : ZMod p) (eK : Env K) (eF : Env (ZMod p)) :
    keyVec δ 11 (Cell.xKeyS s) eK eF 10 = liftQ δ s := by
  simp [keyVec, Cell.xKeyS, Cell.xKey, QFP.entries, QE.var, ev_base, cv, CoeffExpr.eval, cst]

theorem liftQ_inj : Function.Injective (liftQ (K := K) δ) := fun x y h =>
  (algebraMap (ZMod p) K).injective ((algebraMap K (Quad (algebraMap (ZMod p) K δ))).injective h)

/-- **The validity providers have pairwise distinct keys** (the key's last entry is the row serial). -/
theorem cVRec_nodup {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    {ax : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) :
    ((liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr))).map Prod.fst).Nodup := by
  obtain ⟨T, -⟩ := tableM_of_accepts δ b h
  have hnp : Pb.nC ≤ p := by
    have := h.1.hnpC; rw [ZMod.ringChar_zmod_n] at this; omega
  have hPb := h.2.hPb
  subst hPb
  rw [liftWts_fst]
  simp only [cVRec, List.map_map]
  refine (List.nodup_finRange _).map fun i j hij => Fin.ext ?_
  have h0 := congrFun hij 4
  simp only [Function.comp_apply, keyVec_vKeyP_idx] at h0
  have h1 := liftQ_inj δ h0
  have ea := cellEnvF_vM δ b tr ax (c := c) (M := M) (χ := χ) (sz := sz) (hpG := hpG) i i.2 (j := Cell.idx) (by decide)
  have eb := cellEnvF_vM δ b tr ax (c := c) (M := M) (χ := χ) (sz := sz) (hpG := hpG) j j.2 (j := Cell.idx) (by decide)
  exact T.idx_inj hnp i.2 j.2 (ea.symm.trans (h1.trans eb))

/-- **The export providers have pairwise distinct keys** (serial entry `9`, side entry `10`). -/
theorem cXRec_nodup {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)}
    {ax : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) :
    ((liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr))).map Prod.fst).Nodup := by
  obtain ⟨T, -⟩ := tableM_of_accepts δ b h
  have hnp : Pb.nC ≤ p := by
    have := h.1.hnpC; rw [ZMod.ringChar_zmod_n] at this; omega
  have hPb := h.2.hPb
  subst hPb
  rw [liftWts_fst]
  simp only [cXRec, List.map_flatMap, List.map_cons, List.map_nil]
  refine List.nodup_flatMap.mpr ⟨fun i _ => ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
      and_true]
    intro h0
    have h1 := congrFun h0 10
    rw [keyVec_xKeyS_side, keyVec_xKeyS_side] at h1
    have := liftQ_inj δ h1
    exact zero_ne_one this
  · have hk : ∀ (s s' : ZMod p) (i j : Fin (canonPb hpG sz c).nC),
        keyVec δ 11 (Cell.xKeyS s) (cellEnvK δ b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC
          (chalsMJ8 δ χ) M.pubsC (qCell δ b (canonPb hpG sz c) χ M tr) i)
          (cellEnvF b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC
            (qCell δ b (canonPb hpG sz c) χ M tr) i) =
        keyVec δ 11 (Cell.xKeyS s') (cellEnvK δ b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC
          (chalsMJ8 δ χ) M.pubsC (qCell δ b (canonPb hpG sz c) χ M tr) j)
          (cellEnvF b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC
            (qCell δ b (canonPb hpG sz c) χ M tr) j) → i = j := by
      intro s s' i j hij
      have h0 := congrFun hij 9
      rw [keyVec_xKeyS_idx, keyVec_xKeyS_idx] at h0
      have h1 := liftQ_inj δ h0
      have ea := cellEnvF_vM δ b tr ax (c := c) (M := M) (χ := χ) (sz := sz) (hpG := hpG) i i.2 (j := Cell.idx)
        (by decide)
      have eb := cellEnvF_vM δ b tr ax (c := c) (M := M) (χ := χ) (sz := sz) (hpG := hpG) j j.2 (j := Cell.idx)
        (by decide)
      exact Fin.ext (T.idx_inj hnp i.2 j.2 (ea.symm.trans (h1.trans eb)))
    refine (List.nodup_finRange _).imp fun {i j} hij => ?_
    intro a ha hb
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> exact hij (hk _ _ i j (ha.symm.trans hb))

end CountsAccepts

/-! ## 4. Assembly -/

section Final
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)
open Nock.Edit Nock.Walk
open Nock.Edit.GenX (P1Frag genX SkelX)
open Nock.V1J8.Gen (cellsOfRoots rootsOf)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (RowVSX)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1 (RowAgreeX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The chip's handle decoder of an accepted message: the two-provider decode of its restricted cell table. -/
abbrev denC (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (ext : ℕ → Option Noun) :
    LocalVSX.HX → Option Noun :=
  denK ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)).map (·.b0)) ext

/-- **`r0M_auxM_closed`: the cell table's round-0 and aux columns of two accepted traces agree**, with
`NounSetP1.r0M_auxM_final`'s noun-set hypotheses discharged: `hDN` by `hDN_of_accepts` (the chip decoder
`denC … ext`), `hrowsC` by `hrowsC_of_bridge` (the honest rows are `rowsOfT tg` of the generated tree of the
fragment claim), `C` by `mulCounts_of_balances` (passed in), `hcnt` by `hcnt_of_lists`. Remaining hypotheses:
the validity-served tables `hS`, `hS'`; the atom-only external providers `hext`, `hext'` (`extB_atoms`); the
positional bridges `hB`, `hB'` with the root denotations (`RowBridgeP1.rowBridge`, from the twins); the size
`hsz`; the multiplicity count forms `C`, `C'`; equal consumer lists `hreqs` (the compute and walk rows) and equal
row keys `hkey` (the cell round-1 fingerprints with serial and rank). -/
theorem r0M_auxM_closed {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)))
    (hS' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')))
    {ext ext' : ℕ → Option Noun} (hext : ∀ j X, ext j = some X → ∃ a, X = .atom a)
    (hext' : ∀ j X, ext' j = some X → ∃ a, X = .atom a)
    {R : Nock.Jet.Registry} {fuel : ℕ} {tg : NTree SkelX} {rr : Noun} (hfrag : P1Frag c.formula)
    (hg : genX R fuel c.subject c.formula = some (tg, rr))
    (hsz : Pb.nC = (cellsOfRoots (rootsOf c (rowsOfT tg))).length)
    {n n' : ℕ} {d d' : ℕ → RowVSX}
    (hB : (bfsForest [tg]).length = n ∧ ∀ j (hj : j < (bfsForest [tg]).length),
      RowAgreeX (denC δ b Pb χ M tr ext) (d j) ((bfsForest [tg])[j]'hj).label)
    (hB' : (bfsForest [tg]).length = n' ∧ ∀ j (hj : j < (bfsForest [tg]).length),
      RowAgreeX (denC δ b Pb χ M' tr' ext') (d' j) ((bfsForest [tg])[j]'hj).label)
    (hs : ∃ hd, denC δ b Pb χ M tr ext hd = some c.subject)
    (hf : ∃ hd, denC δ b Pb χ M tr ext hd = some c.formula)
    (he : ∃ hd, denC δ b Pb χ M tr ext hd = some c.result)
    (hs' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.subject)
    (hf' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.formula)
    (he' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.result)
    {reqsV reqsV' : List (Fin 5 → 𝕂′)} {reqsX reqsX' : List (Fin 11 → 𝕂′)} {reqsH reqsH' : List (Fin 5 → K)}
    (C : MulCounts (vM tr ax Pb.orbitC.ω) Pb.nC
      (cntOf reqsV (keyVOf δ b Pb χ M tr) reqsX (keyXOf δ b 0 Pb χ M tr) (keyXOf δ b 1 Pb χ M tr)
        reqsH (keyHOf δ b Pb χ M tr)))
    (C' : MulCounts (vM tr' ax' Pb.orbitC.ω) Pb.nC
      (cntOf reqsV' (keyVOf δ b Pb χ M' tr') reqsX' (keyXOf δ b 0 Pb χ M' tr') (keyXOf δ b 1 Pb χ M' tr')
        reqsH' (keyHOf δ b Pb χ M' tr')))
    (hreqs : reqsV = reqsV' ∧ reqsX = reqsX' ∧ reqsH = reqsH')
    (hkey : ∀ i < Pb.nC, keyVOf δ b Pb χ M tr i = keyVOf δ b Pb χ M' tr' i ∧
      keyXOf δ b 0 Pb χ M tr i = keyXOf δ b 0 Pb χ M' tr' i ∧
      keyXOf δ b 1 Pb χ M tr i = keyXOf δ b 1 Pb χ M' tr' i ∧ keyHOf δ b Pb χ M tr i = keyHOf δ b Pb χ M' tr' i) :
    (∀ j : Fin 242, (j : ℕ) < 134 → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) ∧
      (∀ j i, (ax.M j).eval (Pb.nodesC i) = (ax'.M j).eval (Pb.nodesC i)) :=
  r0M_auxM_final δ b h h' hS hS' (rowsOfT tg) hsz (hDN_of_accepts δ b h hS hext)
    (hDN_of_accepts δ b h' hS' hext') (hrowsC_of_bridge c hfrag hg hB hs hf he)
    (hrowsC_of_bridge c hfrag hg hB' hs' hf' he') C C'
    (hcnt_of_lists hreqs.1 hreqs.2.1 hreqs.2.2 (fun i hi => (hkey i hi).1) (fun i hi => (hkey i hi).2.1)
      (fun i hi => (hkey i hi).2.2.1) (fun i hi => (hkey i hi).2.2.2))

/-- **`r0M_auxM_closed'`**: `r0M_auxM_closed` with `C`, `C'` replaced by the balances' count forms (`fibre_counts`'s
conclusions): `hbal*` over provider lists with distinct keys `hd*` (V, X) containing the table's providers `hsub*`;
the handle side takes the provider list `cellProvsW` itself, so `hdH`/`hsubH` are discharged (`cellProvsW_nodup`). -/
theorem r0M_auxM_closed' {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)))
    (hS' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')))
    {ext ext' : ℕ → Option Noun} (hext : ∀ j X, ext j = some X → ∃ a, X = .atom a)
    (hext' : ∀ j X, ext' j = some X → ∃ a, X = .atom a)
    {R : Nock.Jet.Registry} {fuel : ℕ} {tg : NTree SkelX} {rr : Noun} (hfrag : P1Frag c.formula)
    (hg : genX R fuel c.subject c.formula = some (tg, rr))
    (hsz : Pb.nC = (cellsOfRoots (rootsOf c (rowsOfT tg))).length)
    {n n' : ℕ} {d d' : ℕ → RowVSX}
    (hB : (bfsForest [tg]).length = n ∧ ∀ j (hj : j < (bfsForest [tg]).length),
      RowAgreeX (denC δ b Pb χ M tr ext) (d j) ((bfsForest [tg])[j]'hj).label)
    (hB' : (bfsForest [tg]).length = n' ∧ ∀ j (hj : j < (bfsForest [tg]).length),
      RowAgreeX (denC δ b Pb χ M' tr' ext') (d' j) ((bfsForest [tg])[j]'hj).label)
    (hs : ∃ hd, denC δ b Pb χ M tr ext hd = some c.subject)
    (hf : ∃ hd, denC δ b Pb χ M tr ext hd = some c.formula)
    (he : ∃ hd, denC δ b Pb χ M tr ext hd = some c.result)
    (hs' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.subject)
    (hf' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.formula)
    (he' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.result)
    {reqsV reqsV' : List (Fin 5 → 𝕂′)} {reqsX reqsX' : List (Fin 11 → 𝕂′)} {reqsH reqsH' : List (Fin 5 → K)}
    (provsV : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hbalV : ∀ r, (reqsV.count r : 𝕂′) = pw provsV r) (hdV : (provsV.map Prod.fst).Nodup)
    (hsubV : ∀ q ∈ liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)),
      q ∈ provsV)
    (provsX : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbalX : ∀ r, (reqsX.count r : 𝕂′) = pw provsX r) (hdX : (provsX.map Prod.fst).Nodup)
    (hsubX : ∀ q ∈ liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)),
      q ∈ provsX)
    (hbalH : ∀ r, (reqsH.count r : K) = pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) r)
    (provsV' : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hbalV' : ∀ r, (reqsV'.count r : 𝕂′) = pw provsV' r) (hdV' : (provsV'.map Prod.fst).Nodup)
    (hsubV' : ∀ q ∈ liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')),
      q ∈ provsV')
    (provsX' : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbalX' : ∀ r, (reqsX'.count r : 𝕂′) = pw provsX' r) (hdX' : (provsX'.map Prod.fst).Nodup)
    (hsubX' : ∀ q ∈ liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')),
      q ∈ provsX')
    (hbalH' : ∀ r, (reqsH'.count r : K) = pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC)) r)
    (hreqs : reqsV = reqsV' ∧ reqsX = reqsX' ∧ reqsH = reqsH')
    (hkey : ∀ i < Pb.nC, keyVOf δ b Pb χ M tr i = keyVOf δ b Pb χ M' tr' i ∧
      keyXOf δ b 0 Pb χ M tr i = keyXOf δ b 0 Pb χ M' tr' i ∧
      keyXOf δ b 1 Pb χ M tr i = keyXOf δ b 1 Pb χ M' tr' i ∧ keyHOf δ b Pb χ M tr i = keyHOf δ b Pb χ M' tr' i) :
    (∀ j : Fin 242, (j : ℕ) < 134 → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) ∧
      (∀ j i, (ax.M j).eval (Pb.nodesC i) = (ax'.M j).eval (Pb.nodesC i)) :=
  r0M_auxM_closed δ b h h' hS hS' hext hext' hfrag hg hsz hB hB' hs hf he hs' hf' he'
    (mulCounts_of_balances δ b h reqsV provsV hbalV hdV hsubV reqsX provsX hbalX hdX hsubX reqsH
      (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) hbalH
      (cellProvsW_nodup δ b h) (fun _ hq => hq))
    (mulCounts_of_balances δ b h' reqsV' provsV' hbalV' hdV' hsubV' reqsX' provsX' hbalX' hdX' hsubX' reqsH'
      (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC)) hbalH'
      (cellProvsW_nodup δ b h') (fun _ hq => hq))
    hreqs hkey

/-- **`r0M_auxM_closed''`**: `r0M_auxM_closed'` with the V and X providers' distinctness and containment discharged
(`cVRec_nodup`, `cXRec_nodup`): the provider list is the cell table's own providers plus an `extra` list (the atom
table's exports) which is nodup and key-disjoint from the cell's. -/
theorem r0M_auxM_closed'' {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)))
    (hS' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')))
    {ext ext' : ℕ → Option Noun} (hext : ∀ j X, ext j = some X → ∃ a, X = .atom a)
    (hext' : ∀ j X, ext' j = some X → ∃ a, X = .atom a)
    {R : Nock.Jet.Registry} {fuel : ℕ} {tg : NTree SkelX} {rr : Noun} (hfrag : P1Frag c.formula)
    (hg : genX R fuel c.subject c.formula = some (tg, rr))
    (hsz : Pb.nC = (cellsOfRoots (rootsOf c (rowsOfT tg))).length)
    {n n' : ℕ} {d d' : ℕ → RowVSX}
    (hB : (bfsForest [tg]).length = n ∧ ∀ j (hj : j < (bfsForest [tg]).length),
      RowAgreeX (denC δ b Pb χ M tr ext) (d j) ((bfsForest [tg])[j]'hj).label)
    (hB' : (bfsForest [tg]).length = n' ∧ ∀ j (hj : j < (bfsForest [tg]).length),
      RowAgreeX (denC δ b Pb χ M' tr' ext') (d' j) ((bfsForest [tg])[j]'hj).label)
    (hs : ∃ hd, denC δ b Pb χ M tr ext hd = some c.subject)
    (hf : ∃ hd, denC δ b Pb χ M tr ext hd = some c.formula)
    (he : ∃ hd, denC δ b Pb χ M tr ext hd = some c.result)
    (hs' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.subject)
    (hf' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.formula)
    (he' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.result)
    {reqsV reqsV' : List (Fin 5 → 𝕂′)} {reqsX reqsX' : List (Fin 11 → 𝕂′)} {reqsH reqsH' : List (Fin 5 → K)}
    (extraV : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hbalV : ∀ r, (reqsV.count r : 𝕂′) =
      pw (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)) ++ extraV) r)
    (hdeV : (extraV.map Prod.fst).Nodup)
    (hdisV : ∀ a ∈ (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr))).map Prod.fst, ∀ e ∈ extraV.map Prod.fst, a ≠ e)
    (extraX : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbalX : ∀ r, (reqsX.count r : 𝕂′) =
      pw (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)) ++ extraX) r)
    (hdeX : (extraX.map Prod.fst).Nodup)
    (hdisX : ∀ a ∈ (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr))).map Prod.fst, ∀ e ∈ extraX.map Prod.fst, a ≠ e)
    (hbalH : ∀ r, (reqsH.count r : K) = pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) r)
    (extraV' : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hbalV' : ∀ r, (reqsV'.count r : 𝕂′) =
      pw (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')) ++ extraV') r)
    (hdeV' : (extraV'.map Prod.fst).Nodup)
    (hdisV' : ∀ a ∈ (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr'))).map Prod.fst, ∀ e ∈ extraV'.map Prod.fst, a ≠ e)
    (extraX' : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbalX' : ∀ r, (reqsX'.count r : 𝕂′) =
      pw (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')) ++ extraX') r)
    (hdeX' : (extraX'.map Prod.fst).Nodup)
    (hdisX' : ∀ a ∈ (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr'))).map Prod.fst, ∀ e ∈ extraX'.map Prod.fst, a ≠ e)
    (hbalH' : ∀ r, (reqsH'.count r : K) = pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC)) r)
    (hreqs : reqsV = reqsV' ∧ reqsX = reqsX' ∧ reqsH = reqsH')
    (hkey : ∀ i < Pb.nC, keyVOf δ b Pb χ M tr i = keyVOf δ b Pb χ M' tr' i ∧
      keyXOf δ b 0 Pb χ M tr i = keyXOf δ b 0 Pb χ M' tr' i ∧
      keyXOf δ b 1 Pb χ M tr i = keyXOf δ b 1 Pb χ M' tr' i ∧ keyHOf δ b Pb χ M tr i = keyHOf δ b Pb χ M' tr' i) :
    (∀ j : Fin 242, (j : ℕ) < 134 → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) ∧
      (∀ j i, (ax.M j).eval (Pb.nodesC i) = (ax'.M j).eval (Pb.nodesC i)) :=
  r0M_auxM_closed' δ b h h' hS hS' hext hext' hfrag hg hsz hB hB' hs hf he hs' hf' he'
    _ hbalV (by rw [List.map_append]; exact List.nodup_append.mpr ⟨cVRec_nodup δ b h, hdeV, hdisV⟩) (fun q hq => List.mem_append_left _ hq)
    _ hbalX (by rw [List.map_append]; exact List.nodup_append.mpr ⟨cXRec_nodup δ b h, hdeX, hdisX⟩) (fun q hq => List.mem_append_left _ hq)
    hbalH
    _ hbalV' (by rw [List.map_append]; exact List.nodup_append.mpr ⟨cVRec_nodup δ b h', hdeV', hdisV'⟩) (fun q hq => List.mem_append_left _ hq)
    _ hbalX' (by rw [List.map_append]; exact List.nodup_append.mpr ⟨cXRec_nodup δ b h', hdeX', hdisX'⟩) (fun q hq => List.mem_append_left _ hq)
    hbalH' hreqs hkey

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.decode_eq_nounOf
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.hDN_of_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.extB_atoms
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.rowsRead_of_accepts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.hDN_of_accepts
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.genX_frag
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.hrowsC_of_agree
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.hrowsC_of_bridge
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.hrowsC_of_twin
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.hcnt_of_lists
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.mulCounts_of_balances
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.cellProvsW_nodup
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.r0M_auxM_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.r0M_auxM_closed'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.r0M_auxM_closed''
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.cVRec_nodup
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1.cXRec_nodup
