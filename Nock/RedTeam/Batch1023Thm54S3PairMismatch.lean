/-
  Nock/RedTeam/Batch1023Thm54S3PairMismatch.lean

  At an opcode row of the C2 skeleton (`StrategyOfTracesR0AC2.c2SkeletonRow`, structural
  decompositions `nounHead f` / `nounTail f` of the passed-down formula `f`, as `builtJoin`), the
  chip facts are: `f` binds the row's `f` fingerprint (the induction hypothesis from the parent),
  `V_comp`'s `f = cons(f_h, f_t)` with `f_h = atomFP op` (`SVhead`), and the served tail
  `f_t = enc ft` (route B, (i)+(ii)).  From these the one fingerprint identity derivable is
  `enc f = enc (cell (atom op) ft)` (§A, `headCollision_enc`).  The structural decomposition binds
  (`enc (nounHead f) = f_h`, `enc (nounTail f) = f_t`) iff `f = cell (atom op) ft` — which
  `SepSeed z f (cell (atom op) ft)` gives and nothing weaker does.

  `S3PairEvent.rowS3Pairs` prices `formulaCons = (f, cell (nounHead f) ft)` instead.  §B: for
  `f = cell a x` that pair collides iff `enc x = enc ft` (`cons` is cancellative in each argument
  once sizes are nonzero, §A), so its separation says `enc x = enc ft → x = ft` — it never speaks
  to the head.  §C is the compiled instance at `ZMod 31`, `z = 2`: the hostile head
  `enc 2 [1 2] = enc 2 [0 18]` (an OP0 row whose structural formula is `[1 2]` and whose served
  tail is `18`) while S3's pair `([1 2], [1 18])` does NOT collide at `z = 2`, so `2 ∉ pairBadSeeds`
  of that pair at every window and the induction still has no separation of `([1 2], [0 18])`.

  So the S3 event as defined does not price what the induction consumes at opcode rows (nor, by the
  same algebra, at `tailCons` / `branchTailCons`: the derivable right-hand sides carry the served or
  child nouns where the event's carry the structural tails).
-/
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
import Nock.RedTeam.Batch758Thm54HbindComputeCancel
import Nock.NockVMROM.Thm54.P8Core.Batch1023Thm54S3PairMismatch

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1023

open Nock
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.GlobalCarryRecognizer

variable {K : Type} [Field K] [DecidableEq K]

/-! ## §A  The fingerprint algebra the induction has -/

/-- **The one identity the chips give at an opcode row.**  With the formula bound from above, the
opcode head and the served tail, the row's formula fingerprint is `enc` of `cell (atom op) ft`. -/
theorem headCollision_enc {z : K} (hz : z ≠ 0) (f ft : Noun) (op : ℕ) {f_fp f_t : FP K}
    (hf : bindFP z f f_fp) (hV : f_fp = FP.cons z (FP.atomFP z (op : K)) f_t)
    (ht : bindFP z ft f_t) :
    enc z f = enc z (Noun.cell (Noun.atom op) ft) := by
  rw [enc_cons hz, enc_atom, ← ht, ← hV]
  exact hf.symm

/-- **The separation the structural decomposition needs** is `SepSeed` of exactly that pair: it
turns the derivable identity into field-level equality of `f` and `cell (atom op) ft` (noun
equality under the window, `PreSeedCensus.natCast_inj_of_lt`-shaped, as in `PairFaithful`). -/
theorem structural_decomposition_of_sepSeed {z : K} (hz : z ≠ 0) (f ft : Noun) (op : ℕ)
    {f_fp f_t : FP K}
    (hf : bindFP z f f_fp) (hV : f_fp = FP.cons z (FP.atomFP z (op : K)) f_t)
    (ht : bindFP z ft f_t)
    (hsep : SepSeed z f (Noun.cell (Noun.atom op) ft)) :
    (NPR.leafF (K := K) f, NPR.dyckBits (K := K) f) =
      (NPR.leafF (K := K) (Noun.cell (Noun.atom op) ft),
        NPR.dyckBits (K := K) (Noun.cell (Noun.atom op) ft)) := by
  by_contra hne
  exact hsep hne (enc_eq_imp_fn_eq z _ _ (headCollision_enc hz f ft op hf hV ht))

/-! ## §B  What S3's `formulaCons` separates -/

/-- **S3's pair collides iff the tails collide.**  For a cell formula `f = cell a x`,
`enc f = enc (cell (nounHead f) ft) ↔ enc x = enc ft` — the pair carries no information about the
head `a` against the row's opcode. -/
theorem formulaCons_collides_iff_tails {z : K} (hz : z ≠ 0) (a x ft : Noun) :
    enc z (Noun.cell a x) = enc z (Noun.cell (nounHead (Noun.cell a x)) ft) ↔
      enc z x = enc z ft := by
  simp only [nounHead, enc_cons hz]
  constructor
  · intro h
    exact Batch758.cons_right_cancel (by rw [enc_size]; exact pow_ne_zero _ hz) h
  · intro h; rw [h]

/-! ## §C  The compiled instance at `ZMod 31`, `z = 2` -/

/-- The hostile head: the structural formula `[1 2]` and the served reconstruction `[0 18]` of an
OP0 row collide at `z = 2`. -/
theorem hostile_head_collides :
    enc (2 : ZMod 31) (Noun.cell (.atom 1) (.atom 2)) =
      enc (2 : ZMod 31) (Noun.cell (.atom 0) (.atom 18)) := by
  simp only [enc_cons (show (2 : ZMod 31) ≠ 0 by decide), enc_atom]
  apply FP.ext <;> simp [FP.cons, FP.atomFP] <;> decide

/-- S3's `formulaCons` pair at that row, `([1 2], cell (head [1 2]) 18) = ([1 2], [1 18])`, does
NOT collide at `z = 2`. -/
theorem s3_pair_separates :
    enc (2 : ZMod 31) (Noun.cell (.atom 1) (.atom 2)) ≠
      enc (2 : ZMod 31) (Noun.cell (nounHead (Noun.cell (.atom 1) (.atom 2))) (.atom 18)) := by
  simp only [nounHead, enc_cons (show (2 : ZMod 31) ≠ 0 by decide), enc_atom]
  intro h
  have := congrArg FP.leaf h
  simp [FP.cons, FP.atomFP] at this
  revert this; decide

/-- Hence `z = 2` is outside the S3 bad-seed set of that pair at EVERY window: `SepSeed` of S3's
pair holds there. -/
theorem s3_pair_sepSeed :
    SepSeed (2 : ZMod 31) (Noun.cell (.atom 1) (.atom 2))
      (Noun.cell (nounHead (Noun.cell (.atom 1) (.atom 2))) (.atom 18)) := by
  intro _ hfn
  apply s3_pair_separates
  rw [enc_eq_fn, enc_eq_fn, hfn]

theorem two_not_mem_s3_pairBadSeeds (Λ : ℕ) :
    (2 : ZMod 31) ∉ Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds (K := ZMod 31) Λ
      [(Noun.cell (.atom 1) (.atom 2),
        Noun.cell (nounHead (Noun.cell (.atom 1) (.atom 2))) (.atom 18))] := by
  intro hmem
  rw [Nock.NockVMROM.Thm54.PreSeedCensus.mem_pairBadSeeds_iff] at hmem
  obtain ⟨p, hp, _, _, hsep⟩ := hmem
  simp only [List.mem_singleton] at hp
  subst hp
  exact hsep s3_pair_sepSeed

/-- … while the pair the induction needs, `([1 2], [0 18])`, is NOT separated at `z = 2`: two
field-distinct nouns, one fingerprint.  The S3 event does not price this seed; the binding of the
structural decomposition (`enc (nounHead [1 2]) = atomFP 0`) fails there. -/
theorem needed_pair_not_sepSeed :
    ¬ SepSeed (2 : ZMod 31) (Noun.cell (.atom 1) (.atom 2)) (Noun.cell (.atom 0) (.atom 18)) := by
  intro hsep
  refine hsep ?_ (enc_eq_imp_fn_eq _ _ _ hostile_head_collides)
  intro h
  exact absurd (congrArg Prod.fst h) (by simp [NPR.leafF, Noun.leafList] <;> decide)

end Nock.RedTeam.Batch1023

#print axioms Nock.RedTeam.Batch1023.cons_left_cancel
#print axioms Nock.RedTeam.Batch1023.headCollision_enc
#print axioms Nock.RedTeam.Batch1023.structural_decomposition_of_sepSeed
#print axioms Nock.RedTeam.Batch1023.formulaCons_collides_iff_tails
#print axioms Nock.RedTeam.Batch1023.hostile_head_collides
#print axioms Nock.RedTeam.Batch1023.two_not_mem_s3_pairBadSeeds
#print axioms Nock.RedTeam.Batch1023.needed_pair_not_sepSeed
