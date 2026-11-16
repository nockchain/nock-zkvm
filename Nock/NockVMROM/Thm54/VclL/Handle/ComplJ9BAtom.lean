/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BAtom.lean

  Everything is stated over an ARBITRARY extra big-atom noun list `L` (J-9 B: the claim's nouns) so
  that J9BC's `BRun9` instantiates it.

  * §1 `mbX D L`: `D.mb` plus one bump at `bigIdOfP p D.acs n` per `n ∈ L` (`mbX_getD`: the count is the cell
    children's plus `L`'s); `genHyp_mb` (L3's `GenHyp` at any `mb` whose nonzero entries are big roots, no
    two-limb fact), `mbX_roots` (that fact for `mbX` when `L`'s big leaves are big atoms of the run).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9B

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf bumpAll bumpAll_getD bumpAll_size bigIdOfP
  rootIdxP sumAt)

noncomputable section

/-! ## 1. The bumped `mb` -/

section MbX
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The atom-root pairs of an extra noun list (`(root, 1)` per big atom of `L`). -/
def extraPairs (p : ℕ) (acs : List Noun) (L : List Noun) : List (ℕ × ℕ) :=
  L.filterMap fun n => (bigIdOfP p acs n).map fun i => (i, 1)

/-- **`mb` bumped at the atom roots of `L`** (J-9 B: `L` = the claim's nouns; `bigIdOfP` is `none` off big atoms). -/
def mbX (D : J8Data p Rg fuel s f r) (L : List Noun) : Array ℕ := bumpAll D.mb (extraPairs p D.acs L)

theorem mbX_getD (D : J8Data p Rg fuel s f r) (L : List Noun) (j : ℕ) (hj : j < D.mb.size) :
    (mbX D L).getD j 0 = D.mb.getD j 0 + sumAt (extraPairs p D.acs L) j :=
  bumpAll_getD _ _ _ hj

theorem mbX_size (D : J8Data p Rg fuel s f r) (L : List Noun) : (mbX D L).size = D.mb.size := bumpAll_size _ _

end MbX

section RunMb
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

theorem foldl_bumpOpt_size (acs : List Noun) : ∀ (l : List Noun) (a : Array ℕ),
    (l.foldl (fun a n => match bigIdOfP p acs n with
      | some i => Nock.V1J8.Gen.bump a i 1
      | none => a) a).size = a.size
  | [], a => rfl
  | n :: l, a => by
    simp only [List.foldl_cons]
    rw [foldl_bumpOpt_size acs l]
    rcases bigIdOfP p acs n with _ | i
    · rfl
    · exact ComplJ8Data.bump_size _ _ _

/-- **The generator's optional-bump fold is `bumpAll` of `extraPairs`** (J9BC's `mbCountsP9 p acs cs c` is
`mbX (j8DataOf …) ((claimBigs p c).map (claimNoun c))` by this lemma at `a := mbCountsP p acs cs`). -/
theorem foldl_bumpOpt_eq (acs : List Noun) : ∀ (l : List Noun) (a : Array ℕ),
    l.foldl (fun a n => match bigIdOfP p acs n with
      | some i => Nock.V1J8.Gen.bump a i 1
      | none => a) a = bumpAll a (extraPairs p acs l)
  | [], a => rfl
  | n :: l, a => by
    simp only [List.foldl_cons, extraPairs, List.filterMap_cons]
    rcases h : bigIdOfP p acs n with _ | i
    · exact foldl_bumpOpt_eq acs l a
    · exact foldl_bumpOpt_eq acs l _

/-- `bigIdOfP` is `none` off big atoms. -/
theorem bigIdOfP_of_not_big (acs : List Noun) (n : Noun) (h : ClaimJ9.isBigN p n = false) :
    bigIdOfP p acs n = none := by
  cases n with
  | atom v => simp only [ClaimJ9.isBigN, decide_eq_false_iff_not] at h; simp [bigIdOfP]; omega
  | cell a b => rfl

/-- `extraPairs` ignores the non-big nouns. -/
theorem extraPairs_filter (acs : List Noun) : ∀ L : List Noun,
    extraPairs p acs (L.filter (ClaimJ9.isBigN p)) = extraPairs p acs L
  | [] => rfl
  | n :: L => by
    have ih := extraPairs_filter acs L
    by_cases h : ClaimJ9.isBigN p n = true
    · simp only [List.filter_cons, h, if_true, extraPairs, List.filterMap_cons] at ih ⊢; rw [ih]
    · have h' : ClaimJ9.isBigN p n = false := by simpa using h
      simp only [List.filter_cons, h', Bool.false_eq_true, if_false, extraPairs, List.filterMap_cons,
        bigIdOfP_of_not_big p acs n h', Option.map_none] at ih ⊢
      exact ih

/-- **The claim's big positions bump exactly the big atoms among `[s, f, r]`** (for J9BC: `genJ9A`'s
`mbCounts9 acs cs c` at `p` is `mbX (j8DataOf …) [s, f, r]`, by `foldl_bumpOpt_eq` and this). -/
theorem extraPairs_claimBigs (acs : List Noun) (c : P8PublicClaim) :
    extraPairs p acs ((ClaimJ9.claimBigs p c).map (FrameVS.claimNoun c)) =
      extraPairs p acs [c.subject, c.formula, c.result] := by
  rw [← extraPairs_filter p acs [c.subject, c.formula, c.result]]
  unfold ClaimJ9.claimBigs
  have h3 : List.finRange 3 = [0, 1, 2] := by decide
  rw [h3]
  simp only [List.filter_cons, List.filter_nil, FrameVS.claimNoun]
  split_ifs <;> simp_all

/-- `mbX` at the claim's big positions is `mbX` at `[s, f, r]`. -/
theorem mbX_claimBigs (D : J8Data p Rg fuel s f r) (c : P8PublicClaim) :
    mbX D ((ClaimJ9.claimBigs p c).map (FrameVS.claimNoun c)) = mbX D [c.subject, c.formula, c.result] := by
  unfold mbX; rw [extraPairs_claimBigs p]

/-- The run's `mb` has one entry per atom row. -/
theorem mb_size : (j8DataOf p Rg Rt hgen).mb.size = (j8DataOf p Rg Rt hgen).acs.length := by
  show (ComplJ8Data.mbCountsP p _ _).size = _
  unfold ComplJ8Data.mbCountsP
  exact (foldl_bumpOpt_size p _ _ _).trans (Array.size_replicate ..)

/-- A big leaf of the claim is a big atom of the run. -/
theorem claim_leaf_big {n : Noun} (hn : n ∈ [s, f, r]) (a : ℕ) (ha : a ∈ leavesOf n) (hp : p ≤ a) :
    a ∈ (j8DataOf p Rg Rt hgen).bigs := by
  show a ∈ ComplJ8Data.bigsP p (j8DataOf p Rg Rt hgen).roots (j8DataOf p Rg Rt hgen).rows
  refine (ComplJ8Atom.mem_bigsP p _ _ a).mpr ⟨?_, hp⟩
  refine List.mem_flatMap.mpr ⟨n, ?_, ha⟩
  refine List.mem_append_left _ ?_
  show n ∈ Nock.V1J8.Gen.rootsOf ⟨s, f, r⟩ (ComplJ8Data.rowsOfT t) ++ _
  exact List.mem_append_left _ (List.mem_append_left _ hn)

/-- **The nonzero entries of `mbX` are big roots** (the `mb` clause of `GenHyp`), when every big atom of `L` is a
big atom of the run. -/
theorem mbX_roots (L : List Noun)
    (hL : ∀ a, Noun.atom a ∈ L → p ≤ a → a ∈ (j8DataOf p Rg Rt hgen).bigs)
    (hmb : ∀ j < (j8DataOf p Rg Rt hgen).acs.length, (j8DataOf p Rg Rt hgen).mb.getD j 0 ≠ 0 →
      ∃ a ∈ (j8DataOf p Rg Rt hgen).bigs, j = rootIdxP p (j8DataOf p Rg Rt hgen).acs a) :
    ∀ j < (j8DataOf p Rg Rt hgen).acs.length, (mbX (j8DataOf p Rg Rt hgen) L).getD j 0 ≠ 0 →
      ∃ a ∈ (j8DataOf p Rg Rt hgen).bigs, j = rootIdxP p (j8DataOf p Rg Rt hgen).acs a := by
  intro j hj h0
  rw [mbX_getD _ _ _ (by rw [mb_size]; exact hj)] at h0
  by_cases h1 : (j8DataOf p Rg Rt hgen).mb.getD j 0 = 0
  · rw [h1, zero_add] at h0
    obtain ⟨q, hq, hq0⟩ : ∃ q ∈ (extraPairs p (j8DataOf p Rg Rt hgen).acs L).filter (fun q => q.1 = j), q.2 ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_and, ne_eq, not_not] at hc
      apply h0
      unfold sumAt
      exact List.sum_eq_zero fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact hc q hq
    simp only [List.mem_filter, decide_eq_true_eq] at hq
    obtain ⟨hq, rfl⟩ := hq
    simp only [extraPairs, List.mem_filterMap, Option.map_eq_some_iff] at hq
    obtain ⟨n, hn, i, hi, rfl⟩ := hq
    cases n with
    | cell u w => simp [bigIdOfP] at hi
    | atom a =>
      simp only [bigIdOfP] at hi
      split_ifs at hi with hlt
      cases hi
      exact ⟨a, hL a hn (by omega), rfl⟩
  · exact hmb j hj h1

/-- **`GenHyp` at any `mb`** whose nonzero entries are big roots (L3's `genHyp_j8` with `mb` generic; no limb
count is used). -/
theorem genHyp_mb (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hN : (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31) (mb : Array ℕ)
    (hmb : ∀ j < (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length, mb.getD j 0 ≠ 0 →
      ∃ a ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs, j = rootIdxP Nock.Atoms.p (j8DataOf Nock.Atoms.p Rg Rt hgen).acs a) :
    ComplJ8Atom.GenHyp (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs (j8DataOf Nock.Atoms.p Rg Rt hgen).dupP
      (j8DataOf Nock.Atoms.p Rg Rt hgen).rows mb :=
  have hg := ComplJ8Atom.genHyp_j8 Rg Rt hgen hax hop5 hN
  ⟨hg.big, hg.ops, hg.dup, hmb, hg.rows31⟩

/-- `GenHyp` at the claim-bumped `mb` (`L ⊆ [s, f, r]`). -/
theorem genHyp_mbX (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hN : (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31)
    (L : List Noun) (hLs : ∀ n ∈ L, n ∈ [s, f, r]) :
    ComplJ8Atom.GenHyp (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs (j8DataOf Nock.Atoms.p Rg Rt hgen).dupP
      (j8DataOf Nock.Atoms.p Rg Rt hgen).rows (mbX (j8DataOf Nock.Atoms.p Rg Rt hgen) L) :=
  genHyp_mb Rg Rt hgen hax hop5 hN _ (mbX_roots Nock.Atoms.p Rg Rt hgen L
    (fun a ha hp => claim_leaf_big Nock.Atoms.p Rg Rt hgen (hLs _ ha) a (by simp [leavesOf]) hp)
    (ComplJ8Atom.genHyp_j8 Rg Rt hgen hax hop5 hN).mb)

end RunMb

/-! ## 2. The atom table at a generic `mb` -/

section AtomMb
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (atomChipHQ pubMB pubC pubMI mb inc mi)

variable {K : Type} [Field K] [Algebra (ZMod Nock.Atoms.p) K] [FiniteDimensional (ZMod Nock.Atoms.p) K]
  [Fintype K] (δ : ZMod Nock.Atoms.p) [Fact (¬ IsSquare (algebraMap (ZMod Nock.Atoms.p) K δ))]
  (b : Basis (Fin 3) (ZMod Nock.Atoms.p) K)
  (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  {hA : ℕ} (hn : 0 < (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length)
  (nodes : Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length → ZMod Nock.Atoms.p)
  (orbit : StrictOrbitDomain (ZMod Nock.Atoms.p) 3 hA) (chals pubs : ℕ → K)
  (col : ℕ → Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length → ZMod Nock.Atoms.p) (mbA : Array ℕ)

/-- The honest atom rows at a generic `mb`. -/
abbrev rowsMb : ℕ → NRow :=
  (tabOf (j8DataOf Nock.Atoms.p Rg Rt hgen).acs (j8DataOf Nock.Atoms.p Rg Rt hgen).info mbA
    (j8DataOf Nock.Atoms.p Rg Rt hgen).rows).row

/-- **L3's `atomOK_j8` at a generic `mb`** whose nonzero entries are big roots (`hmb`; the J-9 B claim-bumped
`mbX` meets it, `genHyp_mbX`).  No limb count is assumed anywhere (`valid_gen` covers every big atom). -/
theorem atomOK_mb (hax : ComplJ8.ProgAxOK Nock.Atoms.p t) (hop5 : ComplJ8.ProgOp5OK Nock.Atoms.p t)
    (hmb : ComplJ8Atom.GenHyp (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs (j8DataOf Nock.Atoms.p Rg Rt hgen).dupP
      (j8DataOf Nock.Atoms.p Rg Rt hgen).rows mbA)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin _) (hi : (i : ℕ) + 1 < (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length),
      nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hcol : ∀ i : Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      let y := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs[(i : ℕ)]
      col Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      col Cell.idR i = (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j8DataOf Nock.Atoms.p Rg Rt hgen).acs
          (j8DataOf Nock.Atoms.p Rg Rt hgen).rows y else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      col Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p))
    (hsat0 : (cellChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hz1 : ∀ i, HonestA8.dMB δ b hn nodes orbit chals pubs col (newOf (rowsMb Rg Rt hgen mbA)) i ≠ 0)
    (hz2 : ∀ i, HonestA8.dC δ b hn nodes orbit chals pubs col (newOf (rowsMb Rg Rt hgen mbA)) i ≠ 0)
    (hz3 : ∀ i, HonestA8.dMI δ b hn nodes orbit chals pubs col (newOf (rowsMb Rg Rt hgen mbA)) i ≠ 0)
    (hpMB : Quad.mk _ (pubs pubMB) (pubs (pubMB + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (rowsMb Rg Rt hgen mbA) mb)) *
        (HonestA8.dNat δ (HonestA8.dMB δ b hn nodes orbit chals pubs col (newOf (rowsMb Rg Rt hgen mbA))) j)⁻¹)
    (hpC : Quad.mk _ (pubs pubC) (pubs (pubC + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (rowsMb Rg Rt hgen mbA) inc)) *
        (HonestA8.dNat δ (HonestA8.dC δ b hn nodes orbit chals pubs col (newOf (rowsMb Rg Rt hgen mbA))) j)⁻¹)
    (hpMI : Quad.mk _ (pubs pubMI) (pubs (pubMI + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (rowsMb Rg Rt hgen mbA) mi)) *
        (HonestA8.dNat δ (HonestA8.dMI δ b hn nodes orbit chals pubs col (newOf (rowsMb Rg Rt hgen mbA))) j)⁻¹) :
    (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies
        (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsMb Rg Rt hgen mbA))) ∧
      (atomChipHQ δ b hn nodes orbit chals pubs).BindsPreprocessing
        (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsMb Rg Rt hgen mbA))) ∧
      (AtomChipHQL.atomChipHQL δ b hn nodes orbit chals pubs).rap.Satisfies
        (AtomChipHQL.ofHQ δ b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsMb Rg Rt hgen mbA)))) ∧
      (AtomChipHQL.atomChipHQL δ b hn nodes orbit chals pubs).BindsPreprocessing
        (AtomChipHQL.ofHQ δ b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (rowsMb Rg Rt hgen mbA)))) := by
  have hv : (tabOf (j8DataOf Nock.Atoms.p Rg Rt hgen).acs (j8DataOf Nock.Atoms.p Rg Rt hgen).info mbA
      (j8DataOf Nock.Atoms.p Rg Rt hgen).rows).Valid :=
    valid_gen _ _ _ _ hmb
  obtain ⟨hok, hlast⟩ := AtomTab.rows_ok hv (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) rfl
  have hB : Nock.Atoms.B < ringChar (ZMod Nock.Atoms.p) := by
    rw [ZMod.ringChar_zmod_n]; exact Nock.Atoms.B_lt_p
  refine atomOK_of_rows δ b hn nodes orbit chals pubs col hinj hadj hB (rowsMb Rg Rt hgen mbA) (fun i => ?_) hok hlast
    hsat0 hz1 hz2 hz3 hpMB hpC hpMI
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcol i
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := row_cell _ _ _ _ hmb (j8DataOf Nock.Atoms.p Rg Rt hgen).info i i.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c1]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e1.symm
  · rw [c2]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e6.symm
  · rw [c3]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e4.symm
  · rw [c4]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e5.symm
  · rw [c5]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e2.symm
  · rw [c6]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e3.symm

end AtomMb

/-! ## 3. `atomOK` at the claim-bumped data `D9` -/

section AtomRun9
open Nock.V1J8.Gen (hdN' tlN' atomV)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **The J-9 B data**: the run's data with `mb` bumped at the atom roots of `L` (J9BC's `D9` at `L` = the claim's
nouns). -/
abbrev D9 (L : List Noun) : J8Data p Rg fuel s f r := { j8DataOf p Rg Rt hgen with mb := mbX (j8DataOf p Rg Rt hgen) L }

/-- **`atomOK` at `D9`**: at a coin outside the six atom pole
families of `D9`, the honest atom trace at `D9` (`avOf (D9 L)`'s `trA`, publics `pubsAOf (D9 L)`) is accepted and
bound by `atomChipHQ` and `atomChipHQL`.  Binders: `hpG hax hop5 h31`, `hcor : NoIncCornerP` (GLA fix (B));
`L ⊆ [s, f, r]`. -/
theorem atomOK_run9 (hpG : p = Nock.Atoms.p) (L : List Noun) (hLs : ∀ n ∈ L, n ∈ [s, f, r])
    (hF : DvdOK (D9 Rt hgen L)) (hA : 0 < (D9 Rt hgen L).acs.length)
    (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (χ : Coins frameJ8 K)
    (gZ : ∀ e ∈ famAZ (K := K), χ ∉ e.ev) (gV : ∀ e ∈ famAV δ (D9 Rt hgen L) (K := K), χ ∉ e.ev)
    (gH : ∀ e ∈ famAH δ b (D9 Rt hgen L) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev)
    (gMB : ∀ e ∈ famMB δ b (D9 Rt hgen L) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev)
    (gC : ∀ e ∈ famC δ b (D9 Rt hgen L) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev)
    (gMI : ∀ e ∈ famMI δ b (D9 Rt hgen L) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev) :
    let o := orbJ8 (D9 Rt hgen L) hF
    let P := pubsAOf δ b (D9 Rt hgen L) hA o χ
    let tr := HonestA8.atomTraceHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b (D9 Rt hgen L) hA o χ P)
      (newBA (D9 Rt hgen L))
    (AtomChipHQ.atomChipHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P).rap.Satisfies tr ∧
    (AtomChipHQ.atomChipHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P).BindsPreprocessing tr ∧
    (atomChipHQL δ b hA (powN o _) o (chalsAJ8Z δ χ) P).rap.Satisfies
      (AtomChipHQL.ofHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P tr) ∧
    (atomChipHQL δ b hA (powN o _) o (chalsAJ8Z δ χ) P).BindsPreprocessing
      (AtomChipHQL.ofHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P tr) := by
  intro o P tr
  subst hpG
  have hz := famAZ_good δ χ gZ
  have hv := famAV_good δ (D9 (p := Nock.Atoms.p) Rt hgen L) χ gV
  obtain ⟨hpH, hpMB, hpC, hpMI⟩ := atomPoles_good δ b (D9 (p := Nock.Atoms.p) Rt hgen L) hA o χ gH gMB gC gMI P
  have hmA : (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length ∈ sizesJ8 (j8DataOf Nock.Atoms.p Rg Rt hgen) := by
    simp [sizesJ8]
  have hmA9 : (D9 (p := Nock.Atoms.p) Rt hgen L).acs.length ∈ sizesJ8 (D9 (p := Nock.Atoms.p) Rt hgen L) := by simp [sizesJ8]
  obtain ⟨hcell, hrank, htl⟩ := acs_ok Rg Rt hgen hax hop5 h31
  have hN := rows_le_of_rows31 Rt hgen h31
  obtain ⟨hinj, hadj⟩ := powN_ok o (le_two_pow_ht _ hmA9)
  obtain ⟨tV, tX, tH, tMB, tC, tMI⟩ := atomTerms δ b (D9 (p := Nock.Atoms.p) Rt hgen L) hA o χ
  have hsat0 := ComplJ8Cell.cellChipHQ_honest_listP δ b hA (powN o _) o (chalsAJ8Z δ χ) P (γV δ χ) (ρV δ χ)
    (zA δ χ) (fun _ => none) (D9 (p := Nock.Atoms.p) Rt hgen L).acs (mvA _) (mxAF _) (fun _ => 0) (ptA _) (mhvA _) hcell hrank rfl hinj hadj
    (ChalsAZJ8.chalsAJ8Z_ok δ χ) rfl hz (fun j hj => (hv j hj).1) (fun j hj _ => (hv j hj).2.1)
    (fun j hj _ => (hv j hj).2.2.1) (fun j hj => (hv j hj).2.2.2.1) (fun j hj => (hv j hj).2.2.2.2)
    tV tX hpH tH
  have hcol : ∀ i : Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      let y := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs[(i : ℕ)]
      colAH δ b _ hA o χ P Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.idR i =
        (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j8DataOf Nock.Atoms.p Rg Rt hgen).acs
            (j8DataOf Nock.Atoms.p Rg Rt hgen).rows y else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p) := by
    intro i y
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := colAH_fields δ b (D9 (p := Nock.Atoms.p) Rt hgen L) hA o χ P i
    refine ⟨c1, ?_, c3, c4, c5, c6⟩
    rw [c2]
    by_cases hc : (tlN' y).isCell = true
    · rw [if_pos hc, if_pos hc]
      -- one pointer: `colAH`'s `idR` reads `ptrP p acs rows` (`ComplJ8Cell.cellRowsBP`, `ComplJ8Of.ptA`)
    · rw [if_neg hc, if_neg hc]; simp
  exact atomOK_mb δ b Rg Rt hgen hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b (D9 (p := Nock.Atoms.p) Rt hgen L) hA o χ P)
    (mbX (j8DataOf Nock.Atoms.p Rg Rt hgen) L) hax hop5 (genHyp_mbX Rg Rt hgen hax hop5 hN L hLs) hinj hadj hcol hsat0
    hpMB hpC hpMI tMB tC tMI

end AtomRun9

/-! ## 4. The big-atom key at general limbs -/

section EncComb
variable {L : Type} [Field L]

theorem leafList_combOf : ∀ l : List ℕ, l ≠ [] → (Nock.V1J8.Gen.combOf l).leafList = l
  | [], h => absurd rfl h
  | [x], _ => by simp [Nock.V1J8.Gen.combOf, Noun.leafList]
  | [x, y], _ => by simp [Nock.V1J8.Gen.combOf, Noun.leafList]
  | x :: y :: z :: t, _ => by
    have ih := leafList_combOf (y :: z :: t) (by simp)
    show (Noun.cell (.atom x) (Nock.V1J8.Gen.combOf (y :: z :: t))).leafList = _
    simp [Noun.leafList, ih]

theorem eval_listPoly_horner (z : L) : ∀ l : List ℕ,
    (NPR.listPoly (l.map fun k : ℕ => (k : L))).eval z = G5J8.horner z l
  | [] => by simp [NPR.listPoly, NPR.cpoly, G5J8.horner]
  | a :: l => by
    have ih := eval_listPoly_horner z l
    simp only [NPR.listPoly, NPR.cpoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, List.length_map, List.length_cons] at ih ⊢
    rw [Finset.sum_range_succ', G5J8.horner, ← ih, Finset.mul_sum]
    simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **The leaf coordinate of a comb's fingerprint is its limb polynomial** (any limb count). -/
theorem enc_leaf_comb (z : L) (l : List ℕ) (hl : l ≠ []) :
    (GlobalCarryRecognizer.enc z (Nock.V1J8.Gen.combOf l)).leaf = G5J8.horner z l := by
  rw [GlobalCarryRecognizer.enc_leaf, NPR.leafF, leafList_combOf l hl]
  exact eval_listPoly_horner z l

end EncComb

section BigKeyG
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal (gOf keyVec_mb newBA_mb ekA_leaf)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- **The big-atom key identity at general limbs**: at any data
record and any atom row `j` holding a copy of `comb (limbs a)` (`a ≥ p`), the validity consumer key of `atom a` at
serial `j` is the atom table's `mb` provider key of row `j` (`leaf = horner zA (limbs a) = leafVal zY a`). -/
theorem big_keyG (hpG : p = Nock.Atoms.p) (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K)
    (pubs : ℕ → K) (a : ℕ) (hbig : p ≤ a) (j : ℕ) (hj : j < D.acs.length)
    (hget : D.acs[j]'hj = Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) :
    gOf δ (γV δ χ) (ρV δ χ) (encR δ χ) (.atom a) ((j : ℕ) : ZMod p) =
      (HonestA8.dNat δ (HonestA8.dMB δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs)
        (newBA D)) j)⁻¹ := by
  have hl2 : 2 ≤ (Nock.Atoms.limbs a).length := ComplJ8Atom.limbs_big_len (by rw [← hpG]; exact hbig)
  have hne : Nock.Atoms.limbs a ≠ [] := by intro e; rw [e] at hl2; simp at hl2
  set i : Fin D.acs.length := ⟨j, hj⟩ with hi
  have hleaf := ekA_leaf δ b D hA o hinj χ pubs i
  have hidx : (ComplJ8OfAtom.ezA δ b D hA o χ pubs i).trace 2 = ((j : ℕ) : ZMod p) := by
    rw [ComplJ8Atom.EZ_trace (δF := δ) (b := b) (hinj := hinj) (i := i) (j := 2) (h2 := le_rfl) (h3 := by norm_num),
      if_pos (by norm_num)]
    exact (ComplJ8OfAtom.colAH_fields δ b D hA o χ pubs i).1
  have hchal := ComplJ8OfAtom.ekA_chal δ b D hA o χ pubs i
  have hlimbs : ∀ x ∈ Nock.Atoms.limbs a, x < Nock.Atoms.B := fun x hx => (Nock.Atoms.limbs_canonical a).1 x hx
  have hlv := G5J8.leafVal_val (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) hlimbs
    (by rw [Nock.Atoms.val_limbs, ← hpG]; exact hbig)
  rw [Nock.Atoms.val_limbs] at hlv
  have hget' : D.acs[(i : ℕ)] = Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) := hget
  rw [hget', enc_leaf_comb _ _ hne, ComplJ8OfAtom.zA_eq] at hleaf
  unfold gOf
  rw [HonestA8.dNat, dif_pos hj, ComplJ8OfAtom.dMB_eq, InhabJ8Good.compress_split, keyVec_mb, hchal,
    ChalsAZJ8.chalsAJ8Z_zAt, hleaf, hidx]
  refine congrArg (fun x => (ρV δ χ + FiniteIO.compress ⟨γV δ χ, 0⟩ x)⁻¹) ?_
  funext c
  fin_cases c
  · rfl
  · rfl
  · show Nock.Atoms.leafVal (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) a = _
    rw [hlv]
    rfl
  · show Quad.mk _ (algebraMap (ZMod p) K ((0 % 2 ^ 62 : ℕ) : ZMod p))
      (algebraMap (ZMod p) K ((0 / 2 ^ 62 : ℕ) : ZMod p)) = 0
    simp only [Nat.zero_mod, Nat.zero_div, Nat.cast_zero, map_zero]
    exact (Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩
  · rfl

variable (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **A big atom's root serial holds a copy of its comb** (any limb count; for `p`, the LAST copy of `comb p`). -/
theorem root_get (hpG : p = Nock.Atoms.p) (a : ℕ) (ha : a ∈ (j8DataOf p Rg Rt hgen).bigs) :
    (j8DataOf p Rg Rt hgen).acs[ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a]? =
      some (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) := by
  have hpa : p ≤ a := ((ComplJ8Atom.mem_bigsP p _ _ a).mp ha).2
  have hl : 2 ≤ (Nock.Atoms.limbs a).length := ComplJ8Atom.limbs_big_len (by rw [← hpG]; exact hpa)
  have hmem := ComplJ8OfBal.comb_mem_acs Rt hgen hpG ha hl
  unfold ComplJ8Data.rootIdxP
  split_ifs with h
  · rw [h] at hmem ⊢; exact ComplJ8Atom.lastIdxOf_mem _ _ hmem
  · rw [ComplJ8Atom.idxOf_eq _ _ hmem]; exact ComplJ8Atom.getElem?_idxD _ _ hmem

end BigKeyG

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom
