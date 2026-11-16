/-
  Nock/RedTeam/Batch4851Thm54J9BComplGLA.lean

Generator fix (A) (`GenAtom.recountMhx`, mirrored in `ComplJ8Data.infoOfP`): `mhx` recounted from the final inc rows;
  `incT_gen` (`balV` clause 2's inc terminal at GENERAL limbs); `complJ8_closed` unchanged in statement.

  **Generator fix (B).**  `GenAtom.fixOld` / `ComplJ8Data.fixOldP`: a post-pass after the inc fold
  (before the `mhx` recount) sets the old index of `p`'s depth-0 inc row (row `comb (p + 1)`, when `p` is a slow-OP4
  operand) to `rootIdx p` (the LAST copy of `comb p`, the key of the compute's inc record `(2, rootIdx p)`); for
  `v ≠ p` the fold already wrote `rootIdx v = idxOf (comb v)`; depth `≥ 1` rows keep `idxOf` (link1). New
  `AtomTab.io` (old index; `ix` is the tail pointer, unchanged), `AtomTab.Valid.ioLink`; `idxO_gen` / `idxO_copy` /
  `idxO_nodup` / `idxO_root`; GLC's `IdxOOK` at the run by `ComplJ9BBalG.idxOOK_run` (no corner binder; GLC's
  TEMPORARY `HincDup` and `idxOOK_tab` retired). Negative control `noIncCorner_neg` below (the corner run's data violates it); J-8 sanity
  `ComplJ8OfAtom.noIncCorner_of_j8` (it holds under `complJ8`'s binders `hpG hop5 hclA hRt h31`).

* `ComplJ8Atom.valid_j8`: `hax hop5` → `hax hop5 hclA hRt h31` (moved to `ComplJ8OfAtom.lean`, same name);
  * `ComplJ8AW.atomOK_j8`: `hax hop5 …` → `hax hop5 hclA hRt h31 …` (moved to `ComplJ8OfAtom.lean`, same name);
  * `ComplJ8OfAtom.atomOK_run`: `hpG … hax hop5 h31 …` → `hpG … hax hop5 h31 hclA hRt …`. Each is re-derived from its `_gen` version by `noIncCorner_of_j8`.

  Corner data: `incOps = [(p, 1), (u, 1), (p − 1, 1)]`,
  `acs = [[0 [1 B−1]], [1 B−1], [0 [2 B−1]], [2 B−1], [B−1 [1 B−1]], [1 B−1], [0 1]]`, `idxOf comb p = 1`,
  `lastIdxOf comb p = 5`.  `noIncCorner_neg` is stated at that data (the run → data step is the `#eval`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalG
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV

set_option autoImplicit false

namespace Nock.RedTeam.Batch4851

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BAtom

#print axioms mbX_getD
#print axioms mb_size
#print axioms claim_leaf_big
#print axioms mbX_roots
#print axioms genHyp_mb
#print axioms genHyp_mbX
#print axioms atomOK_mb
#print axioms atomOK_run9
#print axioms foldl_bumpOpt_eq

-- generator fix (A): the `mhx` recount, and `balV` clause 2's inc terminal at general limbs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.getD_recountMhx
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.recountMhx_fields
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.stInv_infoOfP
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.inc_old
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal.aHx_gen
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal.incT_gen
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal.incT_run
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal.balV_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG.incSum_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Closed.complJ8_closed

-- generator fix (B) (GLA2): the depth-0 old index of `p`, the corner binder
namespace FixB
open Nock Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock.V1J8.Gen (combOf)
open Nock.Atoms (B val limbs)

/-- `u = [B − 1, 1, B − 1]` (as limbs). -/
def uC : ℕ := (B - 1) + 1 * B + (B - 1) * B * B

/-- The corner run's atom cell list (`#eval`, see the module docstring). -/
def acsC : List Noun :=
  [.cell (.atom 0) (.cell (.atom 1) (.atom (B - 1))), .cell (.atom 1) (.atom (B - 1)),
   .cell (.atom 0) (.cell (.atom 2) (.atom (B - 1))), .cell (.atom 2) (.atom (B - 1)),
   .cell (.atom (B - 1)) (.cell (.atom 1) (.atom (B - 1))), .cell (.atom 1) (.atom (B - 1)),
   .cell (.atom 0) (.atom 1)]

/-- The corner run's slow-OP4 operands (`#eval`). -/
def opsC : List (ℕ × ℕ) := [(Nock.Atoms.p, 1), (uC, 1), (Nock.Atoms.p - 1, 1)]

theorem canon3 (a b c : ℕ) (ha : a < B) (hb : b < B) (hc : 0 < c) (hc' : c < B) : Nock.Atoms.Canonical [a, b, c] :=
  ⟨fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl <;> assumption, fun _ => by simp; omega⟩

theorem canon2 (a c : ℕ) (ha : a < B) (hc : 0 < c) (hc' : c < B) : Nock.Atoms.Canonical [a, c] :=
  ⟨fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption, fun _ => by simp; omega⟩

theorem limbs_uC : limbs uC = [B - 1, 1, B - 1] := by
  have : val [B - 1, 1, B - 1] = uC := by simp [uC]; ring
  rw [← this, Nock.Atoms.limbs_val (canon3 _ _ _ (by simp [B]) (by simp [B]) (by simp [B]) (by simp [B]))]

theorem limbs_uC1 : limbs (uC + 1) = [0, 2, B - 1] := by
  have hB : 1 ≤ B := by simp [B]
  have : val [0, 2, B - 1] = uC + 1 := by
    simp only [Nock.Atoms.val_cons, Nock.Atoms.val_nil, uC]
    zify [hB]; ring
  rw [← this, Nock.Atoms.limbs_val (canon3 _ _ _ (by simp [B]) (by simp [B]) (by simp [B]) (by simp [B]))]

theorem limbs_p1 : limbs (Nock.Atoms.p + 1) = [2, B - 1] := by
  have : val [2, B - 1] = Nock.Atoms.p + 1 := by
    have := Nock.Atoms.val_limbs Nock.Atoms.p
    rw [Nock.Atoms.limbs_p] at this
    simp only [Nock.Atoms.val_cons, Nock.Atoms.val_nil] at this ⊢
    omega
  rw [← this, Nock.Atoms.limbs_val (canon2 _ _ (by simp [B]) (by simp [B]) (by simp [B]))]

/-- **Negative control**: the corner run's data VIOLATES `NoIncCornerP` (`p` is an operand, `u`'s carry chain
reaches the row `comb (p + 1) = [2 B−1]` at depth 1, and `comb p = [1 B−1]` is duplicated at rows 1 and 5). -/
theorem noIncCorner_neg : ¬ NoIncCornerP Nock.Atoms.p acsC opsC := by
  intro h
  have hne : uC + 1 ≠ Nock.Atoms.p := by
    intro e
    have := congrArg limbs e
    rw [limbs_uC1, Nock.Atoms.limbs_p] at this
    simp at this
  have hreach : Reach (fuelOf uC) (limbs (uC + 1)) (limbs uC) (0 + 1) := by
    rw [limbs_uC, limbs_uC1]
    refine ⟨?_, by simp, by simp, fun i hi => ?_⟩
    · unfold fuelOf; rw [limbs_uC]; simp [Nock.V1J8.Gen.spineOf]
    · have : i = 0 := by omega
      subst this
      refine ⟨by simp, by simp⟩
  have key := h ⟨(Nock.Atoms.p, 1), by simp [opsC], rfl⟩
    ⟨(uC, 1), by simp [opsC], hne, 0, hreach, by rw [limbs_uC1, limbs_p1]; rfl⟩
  rw [combPP_eq] at key
  have h1 : Nock.V1J8.Gen.lastIdxOf acsC (combOf [1, B - 1]) = 5 := by decide
  have h2 : Nock.V1J8.Gen.idxOf acsC (combOf [1, B - 1]) = 1 := by decide
  omega

end FixB

#print axioms FixB.noIncCorner_neg
-- item 2: the big-atom key at general limbs
#print axioms leafList_combOf
#print axioms eval_listPoly_horner
#print axioms enc_leaf_comb
#print axioms big_keyG
#print axioms root_get
#print axioms bigIdOfP_of_not_big
#print axioms extraPairs_filter
#print axioms extraPairs_claimBigs
#print axioms mbX_claimBigs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom.noIncCorner_of_j8
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.noIncCorner_of_last
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.info_fields
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.info_idxO
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.stInv_infoFold
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.AtomTab.rowOK_of_valid
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.valid_gen
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.valid_j8_gen
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.valid_j8
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.row_info
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.idxO_gen
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.idxO_copy
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.idxO_nodup
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom.idxO_root
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8AW.atomOK_j8_gen
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8AW.atomOK_j8
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom.atomOK_run_gen
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom.atomOK_run
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG.hI_run
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalG.idxOOK_run
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalG.incInfoOK_infoOfP
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalG.hI9_mb

-- GLA3: balV at D9, general limbs
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.key9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.bt_bh9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.mbT9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.claimBig_sum
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.balV1_run9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.acs_shape
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.hdl_small
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.awKey9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.vhX9_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.incT9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.balV2_run9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.balV3_run9
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV.balV_run9

end Nock.RedTeam.Batch4851
