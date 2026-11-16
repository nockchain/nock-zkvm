/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ9BBalV.lean

* §1 `balV1_run9`: clause 1 over `claimRecsJ9` (claim cell records, claim big-leaf records, pin records) at the cell
    table at `DD = j8DataOf` and the atom table at `D9 = {DD with mb := mbX DD [s, f, r]}`.
  * §2 clause 2 and clause 3 at `D9` / the J-9 atom walk (`vhX9`).
  * §3 `balV_run9`: `OpenJ9B.balV`'s statement over the components (`pubsCOf` at `DD`, `pubsAOf` at `D9`, `pubsVOf9` at
    `DD`), the shape `BRun9` unfolds to.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9B
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom (D9 mbX extraPairs)
open Nock.V1J8.Gen (hdN' tlN')
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF (vValsC9 kLV9 vLV9 kRV9 vRV9)

noncomputable section

section Clause1
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The orbit of the claim-bumped atom data. -/
abbrev o9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    StrictOrbitDomain (ZMod p) 3 (htJ8 (D9 (p := p) Rt hgen [s, f, r])) :=
  orbJ8 (D9 (p := p) Rt hgen [s, f, r]) (dvdOK_of_rows hpG _ h31)

/-- The atom-root provider inverse of atom row `j` at `D9`. -/
abbrev HB9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) (j : ℕ) : 𝕂′ :=
  (HonestA8.dNat δ (HonestA8.dMB δ b (acs_pos (p := p) Rt hgen) (powN (o9 Rt hgen hpG h31) _) (o9 Rt hgen hpG h31)
    (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ)
    (colAH δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ
      (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ))
    (newBA (D9 (p := p) Rt hgen [s, f, r]))) j)⁻¹

/-- A noun's atom-root terminal term at `D9`. -/
abbrev bh9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) (n : Noun) : 𝕂′ :=
  ((ComplJ8Data.bigIdOfP p (j8DataOf p Rg Rt hgen).acs n).map (HB9 δ b Rt hgen hpG h31 χ)).getD 0

/-- **The big-atom key identity at `D9`, general limbs**: the validity consumer key of a big atom of the run at its
root serial is the atom table's `mb` provider inverse of that root row. -/
theorem key9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) (a : ℕ)
    (ha : a ∈ (j8DataOf p Rg Rt hgen).bigs) :
    gOf δ (γV δ χ) (ρV δ χ) (encR δ χ) (.atom a)
        ((ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a : ℕ) : ZMod p) =
      HB9 δ b Rt hgen hpG h31 χ (ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a) := by
  have hpa : p ≤ a := ((ComplJ8Atom.mem_bigsP p _ _ a).mp ha).2
  have hg := ComplJ9BAtom.root_get Rt hgen hpG a ha
  have hj : ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a < (j8DataOf p Rg Rt hgen).acs.length :=
    (List.getElem?_eq_some_iff.mp hg).1
  have hmA : (D9 (p := p) Rt hgen [s, f, r]).acs.length ∈ sizesJ8 (D9 (p := p) Rt hgen [s, f, r]) := by
    simp [sizesJ8]
  have hinj := (powN_ok (o9 Rt hgen hpG h31) (le_two_pow_ht (D9 (p := p) Rt hgen [s, f, r]) hmA)).1
  exact ComplJ9BAtom.big_keyG δ b hpG (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen)
    (o9 Rt hgen hpG h31) hinj χ _ a hpa _ hj (Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans hg))

/-- **A child's big-atom consumer term is its atom-root provider term** (at `D9`). -/
theorem bt_bh9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) (n : Noun)
    (hn : ∀ a, n = .atom a → p ≤ a → a ∈ (j8DataOf p Rg Rt hgen).bigs) :
    btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataOf p Rg Rt hgen)) n = bh9 δ b Rt hgen hpG h31 χ n := by
  cases n with
  | cell u v => simp [btT, bh9, ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP]
  | atom v =>
    by_cases hv : v < p
    · simp [btT, bh9, ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hv]
    · have hb : ComplJ8Cell.isBig (bigOf (j8DataOf p Rg Rt hgen)) (.atom v) = true := by
        simp [ComplJ8Cell.isBig, Noun.isCell, ComplJ8Data.bigIdOfP, hv]
      simp only [btT, hb, if_true, bh9, bigOf, ComplJ8Data.bigIdOfP, hv, if_false, Option.getD_some,
        Option.map_some]
      exact key9 δ b Rt hgen hpG h31 χ v (hn v rfl (by omega))

/-- **The atom table's `mb` terminal at `D9`** is the sum of the cell children's atom-root terms and the claim's
(`[s, f, r]`'s) atom-root terms. -/
theorem mbT9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
        (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ AtomChipHQ.pubMB)
        (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ (AtomChipHQ.pubMB + 1)) =
      ((j8DataOf p Rg Rt hgen).cells.map fun y =>
        bh9 δ b Rt hgen hpG h31 χ (hdN' y) + bh9 δ b Rt hgen hpG h31 χ (tlN' y)).sum +
      ([s, f, r].map fun n => bh9 δ b Rt hgen hpG h31 χ n).sum := by
  refine ((ComplJ8OfAtom.atomTerms δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen)
    (o9 Rt hgen hpG h31) χ).2.2.2.1).trans ?_
  obtain ⟨LB, hLB⟩ : ∃ LB, LB = ((j8DataOf p Rg Rt hgen).cells.flatMap fun n => [hdN' n, tlN' n]).filterMap
      fun n => (ComplJ8Data.bigIdOfP p (j8DataOf p Rg Rt hgen).acs n).map fun i => (i, 1) := ⟨_, rfl⟩
  have hne : (j8DataOf p Rg Rt hgen).acs ≠ [] := List.ne_nil_of_length_pos (acs_pos (p := p) Rt hgen)
  have hrange : ∀ q ∈ LB ++ extraPairs p (j8DataOf p Rg Rt hgen).acs [s, f, r], 0 < q.2 →
      q.1 < (j8DataOf p Rg Rt hgen).acs.length := by
    intro q hq _
    rcases List.mem_append.mp hq with hq | hq
    · exact ComplJ8Data.mbRecs_range p Rg Rt hgen q (by
        simp only [ComplJ8Data.mbRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil]; rw [← hLB]; exact hq) ‹_›
    · obtain ⟨n, -, hn⟩ := List.mem_filterMap.mp hq
      cases n with
      | cell u v => simp [ComplJ8Data.bigIdOfP] at hn
      | atom v =>
        by_cases hv : v < p
        · simp [ComplJ8Data.bigIdOfP, hv] at hn
        · simp only [ComplJ8Data.bigIdOfP, hv, if_false, Option.map_some, Option.some.injEq] at hn
          rw [← hn]
          exact ComplJ8Data.rootIdxP_lt p _ hne v
  have hcnt : ∀ j ∈ Finset.range (j8DataOf p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newBA (D9 (p := p) Rt hgen [s, f, r]) AtomChipHQ.mb)) *
        (HonestA8.dNat δ (HonestA8.dMB δ b (acs_pos (p := p) Rt hgen) (powN (o9 Rt hgen hpG h31) _)
          (o9 Rt hgen hpG h31) (ChalsAZJ8.chalsAJ8Z δ χ)
          (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ)
          (colAH δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ
            (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ))
          (newBA (D9 (p := p) Rt hgen [s, f, r]))) j)⁻¹ =
      ((ComplJ8Data.sumAt (LB ++ extraPairs p (j8DataOf p Rg Rt hgen).acs [s, f, r]) j : ℕ) : 𝕂′) *
        HB9 δ b Rt hgen hpG h31 χ j := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e : HonestA8.cNat j (newBA (D9 (p := p) Rt hgen [s, f, r]) AtomChipHQ.mb) =
        ((ComplJ8Data.sumAt (LB ++ extraPairs p (j8DataOf p Rg Rt hgen).acs [s, f, r]) j : ℕ) : ZMod p) := by
      rw [HonestA8.cNat, dif_pos hj', newBA_mb]
      show (((mbX (j8DataOf p Rg Rt hgen) [s, f, r]).getD j 0 : ℕ) : ZMod p) = _
      rw [ComplJ9BAtom.mbX_getD _ _ _ (by rw [ComplJ9BAtom.mb_size p Rg Rt hgen]; exact hj'),
        ComplJ8Data.mb_eq_cnt p Rg Rt hgen j hj', ComplJ8Data.cnt_eq_sumAt, ComplJ8Data.sumAt_append]
      simp only [ComplJ8Data.mbRecs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hLB]
    rw [e]
    simp only [liftQ, map_natCast]
  refine (Finset.sum_congr rfl hcnt).trans ?_
  rw [sum_sumAt _ _ (LB ++ extraPairs p (j8DataOf p Rg Rt hgen).acs [s, f, r]) hrange, List.map_append,
    List.sum_append]
  unfold extraPairs
  rw [bigPairs_sum (ComplJ8Data.bigIdOfP p (j8DataOf p Rg Rt hgen).acs) (HB9 δ b Rt hgen hpG h31 χ) [s, f, r]]
  rw [hLB, bigPairs_sum (ComplJ8Data.bigIdOfP p (j8DataOf p Rg Rt hgen).acs) (HB9 δ b Rt hgen hpG h31 χ), sum_flatMap_two]

/-- **The claim's big-leaf records' inverse sum** is the claim's atom-root terms. -/
theorem claimBig_sum (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K)
    (hbig : ∀ n ∈ [s, f, r], ∀ a, n = .atom a → p ≤ a → a ∈ (j8DataOf p Rg Rt hgen).bigs) :
    ((ClaimJ9.claimBigRecs δ χ (ComplJ8.cJ s f r) (ComplJ8Comp.mCOf (j8DataOf p Rg Rt hgen).H (ComplJ8.cJ s f r))).map
      fun x => (FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6),
        Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      ([s, f, r].map fun n => bh9 δ b Rt hgen hpG h31 χ n).sum := by
  have hterm : ∀ x ∈ [s, f, r], (if ClaimJ9.isBigN p x = true then
      (FiniteIO.compress (m := 5) ⟨γV δ χ, ρV δ χ⟩ (ClaimVS.claimVec δ (AcceptsJ8.encJ8 δ χ x)
        (((j8DataOf p Rg Rt hgen).H x).2 : ZMod p) 0 0))⁻¹ else 0) = bh9 δ b Rt hgen hpG h31 χ x := by
    intro x hx
    cases x with
    | cell u v => simp [ClaimJ9.isBigN, bh9, ComplJ8Data.bigIdOfP]
    | atom a =>
      by_cases ha : p ≤ a
      · have hmem := hbig _ hx a rfl ha
        have hH : ((j8DataOf p Rg Rt hgen).H (.atom a)).2 = ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a := by
          show (ComplJ8Data.hdlP p (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).acs (.atom a)).2 = _
          simp [ComplJ8Data.hdlP, show ¬ a < p by omega]
        have hk := claimVec_kOf δ (AcceptsJ8.encJ8 δ χ) (.atom a)
          ((ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a : ℕ) : ZMod p)
        simp only [Noun.internal, Nat.zero_div, Nat.zero_mod, Nat.cast_zero] at hk
        have hb : bh9 δ b Rt hgen hpG h31 χ (.atom a) =
            HB9 δ b Rt hgen hpG h31 χ (ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a) := by
          simp [bh9, ComplJ8Data.bigIdOfP, show ¬ a < p by omega]
        rw [hb, ← key9 δ b Rt hgen hpG h31 χ a hmem, if_pos (by simp [ClaimJ9.isBigN, ha]), hH, hk]
      · simp [ClaimJ9.isBigN, ha, bh9, ComplJ8Data.bigIdOfP, show a < p by omega]
  unfold ClaimJ9.claimBigRecs ClaimJ9.claimBigs
  rw [List.map_map, sum_map_ite']
  have h3 : List.finRange 3 = [0, 1, 2] := by decide
  rw [h3]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def]
  rw [← hterm s (by simp), ← hterm f (by simp), ← hterm r (by simp)]
  rfl

/-- **`balV`'s first clause at `D9`** (every coin; no claim-leaf binder, no limb count): the claim (cell and big-leaf)
and registry pin records' validity inverses sum to the cell validity terminal (`pubsCOf` at `DD`) plus the atom
table's `mb` terminal (`pubsAOf` at `D9`). -/
theorem balV1_run9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    ((ClaimJ9.claimRecsJ9 δ χ (ComplJ8.cJ s f r)
        (ComplJ8Comp.mCOf (j8DataOf p Rg Rt hgen).H (ComplJ8.cJ s f r)) ++
        AcceptsJ8P.pinRecsJ8 δ (BRun δ b Rt hgen hpG h31).Pb χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ)
          (pubsCOf δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ 0)
          (pubsCOf δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ 1) +
        Quad.mk (algebraMap (ZMod p) K δ)
          (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ AtomChipHQ.pubMB)
          (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ
            (AtomChipHQ.pubMB + 1)) := by
  have hbigC : ∀ n ∈ [s, f, r], ∀ a, n = .atom a → p ≤ a → a ∈ (j8DataOf p Rg Rt hgen).bigs :=
    fun n hn a h hp => ComplJ9BAtom.claim_leaf_big p Rg Rt hgen hn a (by subst h; simp [leavesOf]) hp
  have hcv : Quad.mk (algebraMap (ZMod p) K δ)
      (pubsCOf δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ 0)
      (pubsCOf δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ 1) =
      cvT δ (j8DataOf p Rg Rt hgen) χ := by
    have e0 : pubsCOf δ b _ (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ 0 = pub2 δ (cvT δ (j8DataOf p Rg Rt hgen) χ) 0 := by
      simp [pubsCOf, pubsC0]
    have e1 : pubsCOf δ b _ (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ 1 = pub2 δ (cvT δ (j8DataOf p Rg Rt hgen) χ) 1 := by
      simp [pubsCOf, pubsC0]
    rw [e0, e1]
    exact pub2_mk2 δ _ 0 rfl
  have hbb : ((j8DataOf p Rg Rt hgen).cells.map fun y =>
      btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataOf p Rg Rt hgen)) (hdN y) +
        btT δ (γV δ χ) (ρV δ χ) (encR δ χ) (bigOf (j8DataOf p Rg Rt hgen)) (tlN y)).sum =
      ((j8DataOf p Rg Rt hgen).cells.map fun y =>
        bh9 δ b Rt hgen hpG h31 χ (hdN' y) + bh9 δ b Rt hgen hpG h31 χ (tlN' y)).sum := by
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    rw [bt_bh9 δ b Rt hgen hpG h31 χ _ fun a ha hp => child_big Rt hgen y hy _ (Or.inl rfl) a ha hp,
      bt_bh9 δ b Rt hgen hpG h31 χ _ fun a ha hp => child_big Rt hgen y hy _ (Or.inr rfl) a ha hp,
      hdN_eq, tlN_eq]
  unfold ClaimJ9.claimRecsJ9
  rw [List.append_assoc, List.map_append, List.sum_append, List.map_append, List.sum_append,
    claim_sum δ Rt hgen χ, claimBig_sum δ b Rt hgen hpG h31 χ hbigC, pin_sum δ b Rt hgen hpG h31 χ, hcv,
    cvT_run δ Rt hgen χ, mbT9 δ b Rt hgen hpG h31 χ, hbb]
  ring

/-- **Every atom cell is a comb of canonical limbs** (any limb count). -/
theorem acs_shape (hpG : p = Nock.Atoms.p) : ∀ y ∈ (j8DataOf p Rg Rt hgen).acs,
    ∃ l, 2 ≤ l.length ∧ Nock.Atoms.Canonical l ∧ y = Nock.V1J8.Gen.combOf l := by
  subst hpG
  intro y hy
  obtain ⟨l, h2, hc, rfl, -⟩ := ComplJ8Atom.shape_acsP _ _
    (fun a ha => ((ComplJ8Atom.mem_bigsP _ _ _ a).mp ha).2) y hy
  exact ⟨l, h2, hc, rfl⟩

/-- The generator's child handle of a small atom. -/
theorem hdl_small (hpG : p = Nock.Atoms.p) (cs : List Noun) (v : ℕ) (hv : v < p) :
    Nock.V1J8.Gen.hdl cs (.atom v) = (0, v) := by
  have hpP : p = Nock.Field.p := by rw [hpG]
  simp [Nock.V1J8.Gen.hdl, hv, ← hpP]

/-- **The atom-walk handle key of a spec row is the atom cell handle key of its row** (general limbs). -/
theorem awKey9 (hpG : p = Nock.Atoms.p) (hne : (j8DataOf p Rg Rt hgen).preads ≠ [])
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjA : Function.Injective (powN o (j8DataOf p Rg Rt hgen).acs.length))
    (hinjV : Function.Injective (powN o (nVOf (j8DataOf p Rg Rt hgen)))) (χ : Coins frameJ8 K) (k : ℕ)
    (hk : k < nVOf (j8DataOf p Rg Rt hgen)) :
    (ComplJ9BBalF.vdN9 δ b (j8DataOf p Rg Rt hgen) o χ WalkHC.xKeyH k)⁻¹ =
      (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (j8DataOf p Rg Rt hgen) (acs_pos (p := p) Rt hgen) o
        (ComplJ9BAWR.idxRW (j8DataOf p Rg Rt hgen).acs (ComplJ9BBalF.rIA (j8DataOf p Rg Rt hgen))
          (wTrie (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).preads k)) χ)⁻¹ := by
  set D := j8DataOf p Rg Rt hgen with hD
  have hA : 0 < D.acs.length := acs_pos (p := p) Rt hgen
  have hnV : nVOf D = (walkRows D.acs D.preads).length := by unfold nVOf; rw [if_neg hne]
  have hmem := wTrie_mem D.acs D.preads (hnV ▸ hk)
  have hwn := ComplJ9BBalF.awNodes_mem9 Rt hgen hpG _ hmem
  have hcl := acs_cell Rt hgen hpG _ hwn
  obtain ⟨hget, hjlt, -⟩ := ComplJ9BBalF.idxRW_facts D _ hwn hcl
  set j := ComplJ9BAWR.idxRW D.acs (ComplJ9BBalF.rIA D) (wTrie D.acs D.preads k) with hj
  have hgetE : D.acs[j]'hjlt = (wTrie D.acs D.preads k).label.node := by
    rw [List.getD_eq_getElem _ _ hjlt] at hget; exact hget
  obtain ⟨l, h2, hcan, hl⟩ := acs_shape Rt hgen hpG _ hwn
  have hBp : Nock.Atoms.B ≤ p := by rw [hpG]; exact Nock.Atoms.B_lt_p.le
  have hlimb : ∀ x ∈ l, x < p := fun x hx => lt_of_lt_of_le (hcan.1 x hx) hBp
  have hhd : Nock.V1J8.Gen.hdN' D.acs[j] = .atom (l.headD 0) := by
    rw [hgetE, hl, ComplJ8Atom.hd_combOf l h2]
  have hd : ComplJ9BBalF.vdN9 δ b D o χ WalkHC.xKeyH k = ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ)
      ((vValsC9 δ D χ ⟨k, hk⟩).idx, (kLV9 D ⟨k, hk⟩, vLV9 D ⟨k, hk⟩), (kRV9 D ⟨k, hk⟩, vRV9 D ⟨k, hk⟩)) := by
    simp only [ComplJ9BBalF.vdN9, WalkTraceHQ.dN, dif_pos hk]
    exact (ComplJ9BBalF.aw_dRow_split9 δ b D o hinjV χ (ComplJ9BBalF.pubsV09 δ D χ) ⟨k, hk⟩).1
  rw [hd, aHx_gen δ b D hA o hinjA χ j hjlt (by rw [hhd]; rfl), hhd]
  have ehd : VclL.hdN (vNode D k) = .atom (l.headD 0) := by
    rw [ComplJ8OfBal.hdN_eq]; show hdN' (wTrie D.acs D.preads k).label.node = _
    rw [hl, ComplJ8Atom.hd_combOf l h2]
  have etl : VclL.tlN (vNode D k) = tlN' D.acs[j] := by
    rw [ComplJ8OfBal.tlN_eq, hgetE]
  have hx0 : l.headD 0 < p := by
    cases l with
    | nil => simp at h2
    | cons x l' => exact hlimb x (by simp)
  have hk0 : ((ComplJ9BBalF.HA D (VclL.hdN (vNode D k))).1 : ZMod p) = 0 ∧
      ((ComplJ9BBalF.HA D (VclL.hdN (vNode D k))).2 : ZMod p) = ((l.headD 0 : ℕ) : ZMod p) := by
    rw [ehd]; simp only [ComplJ9BBalF.HA, hdl_small hpG _ _ hx0]; simp
  have hcell : (tlN' D.acs[j]).isCell = true → tlN' D.acs[j] ∈ D.acs := fun hc => by
    have := (acs_closed_run Rt hgen hpG _ (hgetE ▸ hwn)).2
    rw [ComplJ8OfBal.tlN_eq] at this
    exact this hc
  have hR : ((ComplJ9BBalF.HA D (tlN' D.acs[j])).1 : ZMod p) =
        ((if (tlN' D.acs[j]).isCell = true then 1 else 0 : ℕ) : ZMod p) ∧
      ((ComplJ9BBalF.HA D (tlN' D.acs[j])).2 : ZMod p) =
        (if (tlN' D.acs[j]).isCell = true then ((List.idxOf (tlN' D.acs[j]) D.acs : ℕ) : ZMod p)
          else ((V1J8.Gen.atomV (tlN' D.acs[j]) : ℕ) : ZMod p)) := by
    have htl : tlN' D.acs[j] = if 3 ≤ l.length then V1J8.Gen.combOf l.tail else .atom (l.getD 1 0) := by
      rw [hgetE, hl, ComplJ8Atom.tl_combOf l h2]
    by_cases h3 : 3 ≤ l.length
    · have hc : (tlN' D.acs[j]).isCell = true := by
        rw [htl, if_pos h3]; exact ComplJ8Atom.combOf_isCell _ (by rw [List.length_tail]; omega)
      have hm := hcell hc
      rw [if_pos hc, if_pos hc]
      cases hy : tlN' D.acs[j] with
      | atom v => rw [hy] at hc; simp [Noun.isCell] at hc
      | cell a c =>
        rw [hy] at hm
        simp only [ComplJ9BBalF.HA, V1J8.Gen.hdl, genIdxOf_eq _ _ hm]
        simp
    · have ha : tlN' D.acs[j] = .atom (l.getD 1 0) := by rw [htl, if_neg h3]
      have hv : l.getD 1 0 < p := by
        by_cases h : 1 < l.length
        · rw [List.getD_eq_getElem _ _ h]; exact hlimb _ (List.getElem_mem _)
        · omega
      rw [ha]
      simp only [Noun.isCell, Bool.false_eq_true, if_false, ComplJ9BBalF.HA, hdl_small hpG _ _ hv,
        V1J8.Gen.atomV]
      simp
  have hidx : (vValsC9 δ D χ ⟨k, hk⟩).idx = ((j : ℕ) : ZMod p) := rfl
  have eR1 : kRV9 D ⟨k, hk⟩ = ((if (tlN' D.acs[j]).isCell = true then 1 else 0 : ℕ) : ZMod p) := by
    show ((ComplJ9BBalF.HA D (VclL.tlN (vNode D k))).1 : ZMod p) = _
    rw [etl]; exact hR.1
  have eR2 : vRV9 D ⟨k, hk⟩ = (if (tlN' D.acs[j]).isCell = true then ((ComplJ8Data.ptrP p D.acs D.rows D.acs[j] : ℕ) : ZMod p)
          else ((V1J8.Gen.atomV (tlN' D.acs[j]) : ℕ) : ZMod p)) := by
    have hvn : vNode D k = D.acs[j] := hgetE.symm
    show (if (VclL.tlN (vNode D k)).isCell then ((ComplJ8Data.ptrP p D.acs D.rows (vNode D k) : ℕ) : ZMod p)
      else ((ComplJ9BBalF.HA D (VclL.tlN (vNode D k))).2 : ZMod p)) = _
    rw [etl, hvn]
    by_cases hc : (tlN' D.acs[j]).isCell = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, hR.2, if_neg hc]
  rw [hidx, eR1, eR2, show kLV9 D ⟨k, hk⟩ = 0 from hk0.1, show vLV9 D ⟨k, hk⟩ = ((l.headD 0 : ℕ) : ZMod p) from hk0.2]
  rfl

/-- **The J-9 atom-walk handle import is the atom-walk-weighted atom cell handle sum** (atom walk present; general
limbs; binders `hpG`, `hwalkA`). -/
theorem vhX9_eq (hpG : p = Nock.Atoms.p) (hne : (j8DataOf p Rg Rt hgen).preads ≠ [])
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjA : Function.Injective (powN o (j8DataOf p Rg Rt hgen).acs.length))
    (hinjV : Function.Injective (powN o (nVOf (j8DataOf p Rg Rt hgen)))) (χ : Coins frameJ8 K) :
    ComplJ9BBalF.vhX9 δ b (j8DataOf p Rg Rt hgen) o χ =
      ∑ j ∈ Finset.range (j8DataOf p Rg Rt hgen).acs.length,
        (((j8DataOf p Rg Rt hgen).mhA.getD j 0 : ℕ) : 𝕂′) *
          (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (j8DataOf p Rg Rt hgen) (acs_pos (p := p) Rt hgen) o j χ)⁻¹ := by
  have hsh := ComplJ9BBalF.preads_shape9 Rt hgen hpG
  have hall : ∀ x ∈ (j8DataOf p Rg Rt hgen).preads, VclL.isPathAx x.2 = true := by
    intro x hx; obtain ⟨-, -, -, h2, -⟩ := hsh x hx; exact isPathAx_of_two_le h2
  have h62 := ComplJ8Walk.walkDepth62 hwalkA
  have hwcell := ComplJ9BBalF.awNodes_mem9 Rt hgen hpG
  have hcellsC := acs_cell Rt hgen hpG
  have hspec := ComplJ9BBalF.mxA_spec9 Rt hgen hne hall h62
  set D := j8DataOf p Rg Rt hgen with hD
  set n := D.acs.length
  set G : ℕ → 𝕂′ := fun j => (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D (acs_pos (p := p) Rt hgen) o j χ)⁻¹ with hG
  have hF : ∀ u ∈ walkRows D.acs D.preads, _ := fun u hu =>
    ComplJ9BBalF.idxRW_facts D u (hwcell u hu) (hcellsC _ (hwcell u hu))
  have hnV : nVOf D = (walkRows D.acs D.preads).length := by unfold nVOf; rw [if_neg hne]
  have hW : ComplJ9BBalF.vhX9 δ b D o χ =
      ((walkRows D.acs D.preads).map fun u => G (ComplJ9BAWR.idxRW D.acs (ComplJ9BBalF.rIA D) u)).sum := by
    unfold ComplJ9BBalF.vhX9
    rw [hnV, ← sum_range_getD' (trie (.atom 0) (.atom 0) [] []) _ (walkRows D.acs D.preads)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have e := awKey9 δ b Rt hgen hpG hne o hinjA hinjV χ k (hnV ▸ hk')
    rw [e]
    have hm := wTrie_mem D.acs D.preads hk'
    rw [show (walkRows D.acs D.preads).getD k (trie (.atom 0) (.atom 0) [] []) = wTrie D.acs D.preads k from rfl]
  have hS := sum_serial n (fun u : NTree WN => ComplJ9BAWR.idxRW D.acs (ComplJ9BBalF.rIA D) u) G (walkRows D.acs D.preads)
    (fun u hu => (hF u hu).2.1)
  rw [hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  show _ = D.mxA.getD j 0
  rw [hspec j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  rw [hcellsC _ (hwcell u hu), (hF u hu).2.2]
  simp

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal in
/-- **The atom inc terminal at `D9`** (`incT_gen` at the claim-bumped data: the inc column and old keys do not read `mb`). -/
theorem incT9 (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
    (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
      ∑ j ∈ Finset.range (D9 (p := p) Rt hgen [s, f, r]).acs.length,
        liftQ δ (HonestA8.cNat j (newBA (D9 (p := p) Rt hgen [s, f, r]) AtomChipHQ.inc)) *
          (HonestA8.dNat δ (HonestA8.dC δ b (acs_pos (p := p) Rt hgen) (powN (o9 Rt hgen hpG h31) _)
            (o9 Rt hgen hpG h31) (ChalsAZJ8.chalsAJ8Z δ χ)
            (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ)
            (colAH δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ
              (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ))
            (newBA (D9 (p := p) Rt hgen [s, f, r]))) j)⁻¹ =
        ∑ j ∈ Finset.range (D9 (p := p) Rt hgen [s, f, r]).acs.length,
          ((((D9 (p := p) Rt hgen [s, f, r]).info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) *
            (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen)
              (o9 Rt hgen hpG h31) j χ)⁻¹ := by
  subst hpG
  set D := D9 (p := Nock.Atoms.p) Rt hgen [s, f, r] with hD
  set hF := dvdOK_of_rows rfl D h31
  set o := orbJ8 D hF
  have hA : 0 < D.acs.length := acs_pos (p := Nock.Atoms.p) Rt hgen
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjA := (powN_ok o (le_two_pow_ht D hmA)).1
  have hg := ComplJ9BAtom.genHyp_mbX Rg Rt hgen hax hop5 (ComplJ8OfAtom.rows_le_of_rows31 Rt hgen h31) [s, f, r] (fun n hn => hn)
  obtain ⟨-, -, htl⟩ := ComplJ8OfAtom.acs_ok Rg Rt hgen hax hop5 h31
  set T := ComplJ8Atom.tabOf D.acs D.info D.mb D.rows with hT
  set G : ℕ → Quad (algebraMap (ZMod Nock.Atoms.p) K δ) := fun j =>
    (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ with hG
  set J : ℕ → ℕ := fun m => (T.row m).idxO with hJ
  set C := (List.range D.acs.length).filter fun m => T.inc m with hCdef
  have hlt : ∀ c ∈ D.acs, Nock.V1J8.Gen.idxOf D.acs c < D.acs.length := by
    intro c hc; rw [genIdxOf_eq _ _ hc]; exact List.idxOf_lt_length_of_mem hc
  -- an inc row's old index and fields
  have hold : ∀ m, T.inc m = true → D.acs[J m]? = some (Nock.V1J8.Gen.combOf (T.lo m)) ∧
      J m < D.acs.length ∧ 2 ≤ (T.lo m).length ∧ Nock.V1J8.Gen.combOf (T.lo m) ∈ D.acs := by
    intro m hm
    obtain ⟨-, h2, hmem⟩ := ComplJ8Atom.inc_old _ _ _ _ hg m hm
    obtain ⟨hl, he⟩ := ComplJ8Atom.idxO_copy _ _ _ _ hg m hm
    exact ⟨he, hl, h2, hmem⟩
  -- the inc rows' terms
  have hterm : ∀ j ∈ Finset.range D.acs.length,
      liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.inc)) *
        (HonestA8.dNat δ (HonestA8.dC δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ)
          (colAH δ b D hA o χ (pubsAOf δ b D hA o χ)) (newBA D)) j)⁻¹ =
      if T.inc j = true then G (J j) else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [HonestA8.cNat, HonestA8.dNat, dif_pos hj']
    rw [newBA_inc]
    by_cases hi : T.inc j = true
    · have hi' : (D.info.getD j Nock.V1J8.Gen.AInfo.z).inc = true := hi
      rw [if_pos hi', if_pos hi]
      obtain ⟨eJ, hJn, h2, hmem⟩ := hold j hi
      set l := T.lo j with hl
      rw [dC_key δ b D hA o hinjA χ _ ⟨j, hj'⟩]
      simp only [Fin.val_mk, liftQ, map_one, one_mul, hG]
      have hget : D.acs[J j]'hJn = Nock.V1J8.Gen.combOf l := by
        rw [List.getElem?_eq_getElem hJn] at eJ; exact Option.some.inj eJ
      have hhd : Nock.V1J8.Gen.hdN' D.acs[J j] = .atom (l.headD 0) := by rw [hget, ComplJ8Atom.hd_combOf l h2]
      rw [aHx_gen δ b D hA o hinjA χ (J j) hJn (by rw [hhd]; rfl), hhd]
      have hrow : (T.row j).idxO = J j ∧ (T.row j).lO = l.headD 0 ∧
          (T.row j).kRO = (if 3 ≤ l.length then 1 else 0) ∧
          (T.row j).vRO = (if 3 ≤ l.length then T.ip l else l.getD 1 0) := by
        refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [ComplJ8Atom.AtomTab.row, hi, hl]
      rw [hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2]
      have htl' := ComplJ8Atom.tl_combOf l h2
      by_cases h3 : 3 ≤ l.length
      · have e2 : Nock.V1J8.Gen.tlN' D.acs[J j] = Nock.V1J8.Gen.combOf l.tail := by rw [hget, htl', if_pos h3]
        have hc : (Nock.V1J8.Gen.tlN' D.acs[J j]).isCell = true := by
          rw [e2]; exact ComplJ8Atom.combOf_isCell _ (by rw [List.length_tail]; omega)
        have hm2 : Nock.V1J8.Gen.combOf l.tail ∈ D.acs := e2 ▸ htl _ (List.getElem_mem _) hc
        -- one pointer: `aHx_gen` reads `ptrP p acs rows` (via `colAH_fields`), the same as `T.ip`
        have hix : T.ip l = ComplJ8Data.ptrP Nock.Atoms.p D.acs D.rows D.acs[J j] := by
          show ComplJ8Data.ptrP Nock.Atoms.p D.acs D.rows (Nock.V1J8.Gen.combOf l) = _
          rw [hget]
        have hc' : (Nock.V1J8.Gen.combOf l.tail).isCell = true := e2 ▸ hc
        simp only [if_pos h3, hc', if_true, hix, e2, Nock.V1J8.Gen.atomV]
      · have e2 : Nock.V1J8.Gen.tlN' D.acs[J j] = .atom (l.getD 1 0) := by rw [hget, htl', if_neg h3]
        simp only [if_neg h3, e2, Noun.isCell, Bool.false_eq_true, if_false, Nock.V1J8.Gen.atomV]
    · have hi' : ¬ (D.info.getD j Nock.V1J8.Gen.AInfo.z).inc = true := hi
      rw [if_neg hi', if_neg hi]
      simp only [liftQ, map_zero, zero_mul]
  rw [Finset.sum_congr rfl hterm, sum_range_ite_list (fun m => T.inc m) (fun m => G (J m)) D.acs.length]
  have hss := sum_serial D.acs.length J G C (fun m hm => (hold m (List.mem_filter.mp hm).2).2.1)
  rw [hss]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  congr 1
  -- the recounted mhx is the number of inc rows whose old row is `j`
  set Fd := ComplJ8Atom.infoFold Nock.Atoms.p D.acs D.rows with hFd
  have hinfo : D.info = Nock.V1J8.Gen.recountMhx Fd := ComplJ8Atom.infoOfP_eq _ _ _
  have hsz : Fd.size = D.acs.length := by
    have := ComplJ8Atom.recountMhx_size Fd
    rw [← hinfo] at this
    rw [← this]
    exact (ComplJ8Atom.stInv_gen _ _ _ _ hg).size
  have hm : (D.info.getD j Nock.V1J8.Gen.AInfo.z).mhx = Nock.V1J8.Gen.mhxOf Fd j := by
    rw [hinfo, ComplJ8Atom.getD_recountMhx, if_pos (by rw [hsz]; exact hj')]
  rw [hm]
  unfold Nock.V1J8.Gen.mhxOf
  rw [toList_eq_range, hsz, List.filter_map, List.length_map, hCdef, List.filter_filter]
  congr 2
  refine List.filter_congr fun m hmr => ?_
  have hR := ComplJ8Atom.recountMhx_fields Fd m
  have e1 : (Fd.getD m Nock.V1J8.Gen.AInfo.z).inc = T.inc m := by
    show _ = (D.info.getD m Nock.V1J8.Gen.AInfo.z).inc; rw [hinfo, hR.1]
  have e2 : (Fd.getD m Nock.V1J8.Gen.AInfo.z).idxO = (D.info.getD m Nock.V1J8.Gen.AInfo.z).idxO := by
    rw [hinfo, hR.2.2.2.1]
  have e3 : (T.row m).idxO = (D.info.getD m Nock.V1J8.Gen.AInfo.z).idxO :=
    (ComplJ8Atom.row_info _ _ _ _ hg m).2.2.2.1
  simp only [Function.comp, e1, e2, hJ, e3]
  cases T.inc m <;> simp <;> exact Bool.eq_iff_iff.mpr (by simp)


/-- **`balV`'s second clause at `D9` and the J-9 atom walk** (every coin; general limbs): the atom table's handle
export plus the J-9 atom walk's handle import balance the atom inc terminal.  Binders `hpG hax hop5 h31 hwalkA`. -/
theorem balV2_run9 (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
        (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ CellHQ.pubHQ)
        (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ)
          (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ AtomChipHQ.pubC)
          (pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ
            (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ)
          (ComplJ9BBalF.pubsVOf9 δ b (j8DataOf p Rg Rt hgen) (oR Rt hgen hpG h31) χ WalkHQ.pubXQ)
          (ComplJ9BBalF.pubsVOf9 δ b (j8DataOf p Rg Rt hgen) (oR Rt hgen hpG h31) χ (WalkHQ.pubXQ + 1)) := by
  set D := D9 (p := p) Rt hgen [s, f, r] with hD
  set DD := j8DataOf p Rg Rt hgen with hDD
  have hA : 0 < D.acs.length := acs_pos (p := p) Rt hgen
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hmAD : DD.acs.length ∈ sizesJ8 DD := by simp [sizesJ8]
  have hmV : nVOf DD ∈ sizesJ8 DD := by simp [sizesJ8]
  have hinjA := (powN_ok (o9 Rt hgen hpG h31) (le_two_pow_ht D hmA)).1
  have hinjAD := (powN_ok (oR Rt hgen hpG h31) (le_two_pow_ht DD hmAD)).1
  have hinjV := (powN_ok (oR Rt hgen hpG h31) (le_two_pow_ht DD hmV)).1
  set G : ℕ → 𝕂′ := fun j => (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA (o9 Rt hgen hpG h31) j χ)⁻¹ with hG
  obtain ⟨-, -, tHQ, -, tC, -⟩ := ComplJ8OfAtom.atomTerms δ b D hA (o9 Rt hgen hpG h31) χ
  show Quad.mk _ (pubsAOf δ b D hA (o9 Rt hgen hpG h31) χ CellHQ.pubHQ) (pubsAOf δ b D hA (o9 Rt hgen hpG h31) χ (CellHQ.pubHQ + 1)) =
    Quad.mk _ (pubsAOf δ b D hA (o9 Rt hgen hpG h31) χ AtomChipHQ.pubC) (pubsAOf δ b D hA (o9 Rt hgen hpG h31) χ (AtomChipHQ.pubC + 1)) +
      Quad.mk _ (ComplJ9BBalF.pubsVOf9 δ b DD (oR Rt hgen hpG h31) χ WalkHQ.pubXQ)
        (ComplJ9BBalF.pubsVOf9 δ b DD (oR Rt hgen hpG h31) χ (WalkHQ.pubXQ + 1))
  rw [tHQ, tC, incT9 δ b Rt hgen hpG hax hop5 h31 χ]
  have hL : ∑ j ∈ Finset.range D.acs.length, liftQ δ (CellTraceH.mN (mhvA D) j) *
      (CellTraceHQ.dN δ b hA (powN (o9 Rt hgen hpG h31) _) (o9 Rt hgen hpG h31) (ChalsAZJ8.chalsAJ8Z δ χ)
        (pubsAOf δ b D hA (o9 Rt hgen hpG h31) χ) (aCol δ b D χ) (mhvA D) j)⁻¹ =
      ∑ j ∈ Finset.range D.acs.length, (((D.info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) * G j +
      ∑ j ∈ Finset.range D.acs.length, ((D.mhA.getD j 0 : ℕ) : 𝕂′) * G j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    simp only [CellTraceH.mN, CellTraceHQ.dN, dif_pos hj', hG]
    rw [ComplJ8OfAtom.aRow_split δ b D hA (o9 Rt hgen hpG h31) χ _ ⟨j, hj'⟩]
    simp only [mhvA, mhAF, liftQ, Nat.cast_add, map_add, map_natCast]
    ring
  rw [hL]
  congr 1
  by_cases h0 : DD.preads = []
  · have hz : (0 : 𝕂′) = Quad.mk _ 0 0 := ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
    have hv : ∀ i, ComplJ9BBalF.pubsVOf9 δ b DD (oR Rt hgen hpG h31) χ i = 0 := fun i => by
      simp [ComplJ9BBalF.pubsVOf9, h0]
    rw [hv, hv, ← hz]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hm : D.mhA.getD j 0 = 0 := by
      show DD.mxA.getD j 0 = 0
      rw [ComplJ8Data.mxA_eq_cnt p Rg Rt hgen j (Finset.mem_range.mp hj), ComplJ8Data.cnt_eq_sumAt]
      simp [ComplJ8Data.awRecs, vs_nil Rt hgen h0, ComplJ8Data.wPairs, ComplJ8Data.sumAt]
    simp [hm]
  · have h4 : ComplJ9BBalF.pubsVOf9 δ b DD (oR Rt hgen hpG h31) χ WalkHQ.pubXQ =
        pub2 δ (ComplJ9BBalF.vhX9 δ b DD (oR Rt hgen hpG h31) χ) 4 := by
      simp [ComplJ9BBalF.pubsVOf9, h0, WalkHQ.pubXQ]
    have h5 : ComplJ9BBalF.pubsVOf9 δ b DD (oR Rt hgen hpG h31) χ (WalkHQ.pubXQ + 1) =
        pub2 δ (ComplJ9BBalF.vhX9 δ b DD (oR Rt hgen hpG h31) χ) 5 := by
      simp [ComplJ9BBalF.pubsVOf9, h0, WalkHQ.pubXQ]
    rw [h4, h5, pub2_mk2 δ _ 4 rfl, vhX9_eq δ b Rt hgen hpG h0 hwalkA (oR Rt hgen hpG h31) hinjAD hinjV χ]
    refine Finset.sum_congr rfl fun j hj => ?_
    rfl

/-- **`balV`'s third clause at `D9`**: the atom table's validity publics are zero. -/
theorem balV3_run9 (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ 0 = 0 ∧
    pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ 1 = 0 := by
  have h0 := avT_zero_of δ (D9 (p := p) Rt hgen [s, f, r]) (acs_closed_run Rt hgen hpG) χ
  have hz : (0 : Quad (algebraMap (ZMod p) K δ)) = Quad.mk _ 0 0 :=
    ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
  refine ⟨?_, ?_⟩
  · simp [pubsAOf, pubsA1, pubsA0, pub2, h0, hz, Quad.re_mk, Quad.im_mk]
  · simp [pubsAOf, pubsA1, pubsA0, pub2, h0, hz, Quad.re_mk, Quad.im_mk]

/-- **`OpenJ9B.balV` at `BRun9`, over its components** (every coin).  `BRun9`'s `M.m` is `mCOf DD.H (cJ s f r)`, its
`Pb` is `BRun`'s (`pinRecsJ8`), its cell-table publics are `pubsCOf` at `DD` (`oR`), its atom-table publics are
`pubsAOf` at `D9 = j9DataOf` (`o9`) and its atom-walk publics are `pubsVOf9` at `DD` (`oR`), so J9BC closes
`BalV9` by `fun χ _ => balV_run9 … χ` (up to `show`).  Binders `hpG hax hop5 h31 hwalkA` (no claim-leaf binder). -/
theorem balV_run9 (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (χ : Coins frameJ8 K) :
    let A := pubsAOf δ b (D9 (p := p) Rt hgen [s, f, r]) (acs_pos (p := p) Rt hgen) (o9 Rt hgen hpG h31) χ
    let C := pubsCOf δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (oR Rt hgen hpG h31) χ
    let V := ComplJ9BBalF.pubsVOf9 δ b (j8DataOf p Rg Rt hgen) (oR Rt hgen hpG h31) χ
    ((ClaimJ9.claimRecsJ9 δ χ (ComplJ8.cJ s f r)
        (ComplJ8Comp.mCOf (j8DataOf p Rg Rt hgen).H (ComplJ8.cJ s f r)) ++
        AcceptsJ8P.pinRecsJ8 δ (BRun δ b Rt hgen hpG h31).Pb χ).map fun x => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ WeightsJ8.c4) (χ WeightsJ8.c6), Quad.mk _ (χ WeightsJ8.c5) (χ WeightsJ8.c7)⟩ x)⁻¹).sum =
      Quad.mk (algebraMap (ZMod p) K δ) (C 0) (C 1) +
        Quad.mk (algebraMap (ZMod p) K δ) (A AtomChipHQ.pubMB) (A (AtomChipHQ.pubMB + 1)) ∧
    Quad.mk (algebraMap (ZMod p) K δ) (A CellHQ.pubHQ) (A (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ) (A AtomChipHQ.pubC) (A (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ) (V WalkHQ.pubXQ) (V (WalkHQ.pubXQ + 1)) ∧
    (A 0 = 0 ∧ A 1 = 0) :=
  ⟨balV1_run9 δ b Rt hgen hpG h31 χ, balV2_run9 δ b Rt hgen hpG hax hop5 h31 hwalkA χ,
    balV3_run9 δ b Rt hgen hpG h31 χ⟩

end Clause1

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV
