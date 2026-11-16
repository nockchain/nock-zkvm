/-
  Nock/RedTeam/Batch600Thm54PreseedAtomDomainStop.lean

  Notes-only.

  Those rows are **not** atom rows: Nock's
  `[1 b]` returns `b` for every noun `b`, and an honest OP1 row whose literal is a cell carries a result leaf
  `leaf(enc z [x y]) = x + z^{λ_x} · leaf(y)` that is not
  in `𝔽`.  The proposed gate therefore REJECTS the honest trace of `[1 [1 a]]`
  at every seed outside an `|𝔽|`-element set — completeness fails, so the honest
  fill `enc_atom` (item 4) does not exist on those rows.  OP0 results have the
  same shape (a slot of the subject is an arbitrary noun; the table's `e` row
  `:1939` leaves `OP_0`/`OP_1` results unconstrained `⊥`).  The compute chip has
  no round-0 "is-atom" selector and no subject/formula *leaf* rows (leaves of
  nouns are memory-forest `halt` rows), so the compute half of the design does
  not fit the merged code.  The memory half (`halt` rows are atoms,
  `Batch579.halt_is_atom_shape`) does fit; it is not built here.

  Compiled:
  * `honest_op1_cell_row_valid` — the honest OP1 row of `[1 [1 a]]` satisfies
    `Vcomp` (same row shape as `Batch578.child_valid`).
  * `honest_op1_result_eq_enc` — its result is `enc z [1 a]` (the honest noun).
  * `honest_op1_result_leaf` — that leaf is `1 + z·a`.
  * `atom_gates_iff` — the three coordinate gates hold iff `leaf = atom • b 0`.
  * `atom_gate_honest_seeds_card_le` — the seeds at which the honest `[1 [1 1]]`
    OP1 row can pass the gates (for ANY atom fill) number at most `|𝔽|`.
  * `atom_gate_rejects_honest_op1_cell` — at `K = GaloisField 31 3`, `|𝕂| = 31³`,
    some seed rejects the honest row under every atom fill.
  * `deployed_codec_carries_e_leaf` — the deployed normalized codec stores the
    gated coordinate as an extension role (`OptimizedComputeCodec.encodeExtension`
    at `(2, 2)` = `pub.e.leaf`), so the rejection is at the codec, not only at `Vcomp`.
-/
import Nock.RedTeam.Batch578Thm54AdaptiveAtomForgery
import Nock.RedTeam.Batch579Thm54PreseedAtomGates
import Nock.NockVMROM.Thm54.OptimizedComputeCodec
import Mathlib.FieldTheory.Finite.GaloisField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch600

open Nock
open Nock.ComputeTable
open Nock.GlobalCarryRecognizer
open Nock.NockVMROM.Thm54
open Nock.RedTeam.Batch578
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K]

/-! ## The honest OP1 row of `[1 [1 a]]` (a cell literal) -/

/-- Result of `[1 [1 a]]`: the cell `[1 a]`. -/
noncomputable def honestOp1Result (z a : K) : FP K := pair z (aFP z 1) (aFP z a)

/-- The formula `[1 [1 a]]`. -/
noncomputable def honestOp1Formula (z a : K) : FP K := pair z (aFP z 1) (honestOp1Result z a)

/-- Honest OP1 row (row shape of `Batch578.row`). -/
noncomputable def honestOp1Row (z alpha a : K) : ComputeTable.Pub K :=
  row z alpha .s1 (honestOp1Formula z a) (honestOp1Result z a) (honestOp1Result z a) alpha

theorem honest_op1_cell_row_valid (z alpha a : K) :
    Vcomp (⟨alpha, z, 0, 0, 0⟩ : ComputeTable.Inputs K) (honestOp1Row z alpha a)
      (decOf z 1 (honestOp1Result z a)) := by
  simp [Vcomp, honestOp1Row, row, honestOp1Formula, pair, decOf, SVhead, headAtom, memBlk,
    evalV, sfz1, sfz2, sfz3, aFP, FP.atomFP, State.toNat]

/-- The row's result is the honest fingerprint of the noun `[1 a]`. -/
theorem honest_op1_result_eq_enc (z : K) (hz : z ≠ 0) (a : ℕ) :
    honestOp1Result z (a : K) = enc z (.cell (.atom 1) (.atom a)) := by
  rw [enc_cons hz, enc_atom, enc_atom]
  simp [honestOp1Result, pair, aFP]

theorem honest_op1_result_leaf (z a : K) :
    (honestOp1Result z a).leaf = 1 + z * a := by
  simp [honestOp1Result, pair, aFP, FP.cons, FP.atomFP]

theorem honest_op1_row_e (z alpha a : K) :
    (honestOp1Row z alpha a).e = honestOp1Result z a := rfl

theorem honest_op1_row_state (z alpha a : K) :
    (honestOp1Row z alpha a).state = .s1 := rfl

/-! ## The three proposed coordinate gates -/

section Gates

variable {F : Type*} [Field F] [Algebra F K]

/-- The design's three gates on a `𝕂` leaf, as coordinates in a basis `b`:
`leaf₀ − atom = 0`, `leaf₁ = 0`, `leaf₂ = 0`. -/
def AtomGates (b : Module.Basis (Fin 3) F K) (leaf : K) (atom : F) : Prop :=
  b.repr leaf 0 = atom ∧ b.repr leaf 1 = 0 ∧ b.repr leaf 2 = 0

theorem atom_gates_iff (b : Module.Basis (Fin 3) F K) (leaf : K) (atom : F) :
    AtomGates b leaf atom ↔ leaf = atom • b 0 := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    apply b.ext_elem
    intro i
    fin_cases i <;> simp [h0, h1, h2]
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩ <;> simp

/-- The seeds at which the honest `[1 [1 1]]` OP1 row can pass the three gates, for ANY
atom fill, form a set of at most `|𝔽|` elements. -/
theorem atom_gate_honest_seeds_card_le [Fintype F] [Fintype K] [DecidableEq K]
    (b : Module.Basis (Fin 3) F K) :
    (Finset.univ.filter fun z : K =>
      ∃ atom : F, AtomGates b (honestOp1Result z 1).leaf atom).card ≤ Fintype.card F := by
  classical
  have hsub :
      (Finset.univ.filter fun z : K =>
        ∃ atom : F, AtomGates b (honestOp1Result z 1).leaf atom) ⊆
        Finset.univ.image (fun atom : F => atom • b 0 - 1) := by
    intro z hz
    obtain ⟨atom, hg⟩ := (Finset.mem_filter.mp hz).2
    rw [atom_gates_iff, honest_op1_result_leaf, mul_one] at hg
    exact Finset.mem_image.mpr ⟨atom, Finset.mem_univ _, by rw [← hg]; ring⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end Gates

/-! ## Concrete: `p = 31`, `K = GaloisField 31 3` -/

/-- At `|𝕂| = 31³`, some seed rejects the honest `[1 [1 1]]` OP1 row under every atom fill. -/
theorem atom_gate_rejects_honest_op1_cell (b : Module.Basis (Fin 3) F31 K31) :
    ∃ z : K31, ∀ atom : F31, ¬ AtomGates b (honestOp1Result z 1).leaf atom := by
  classical
  letI : Fintype K31 := Fintype.ofFinite K31
  by_contra hall
  push Not at hall
  have hfull :
      (Finset.univ.filter fun z : K31 =>
        ∃ atom : F31, AtomGates b (honestOp1Result z 1).leaf atom) = Finset.univ := by
    ext z
    simp [hall z]
  have hle := atom_gate_honest_seeds_card_le b
  rw [hfull, Finset.card_univ] at hle
  have hK : Fintype.card K31 = 31 ^ 3 := by
    rw [@Module.card_eq_pow_finrank (K := F31) (V := K31), ZMod.card,
      GaloisField.finrank 31 (by norm_num : (3 : ℕ) ≠ 0)]
  rw [hK, ZMod.card] at hle
  norm_num at hle

/-! ## At the deployed codec -/

/-- The deployed normalized compute codec stores `pub.e.leaf` as extension role `(2, 2)`;
the proposed compute gate would read exactly this coordinate. -/
theorem deployed_codec_carries_e_leaf {F : Type*} [Field F]
    (pub : ComputeTable.Pub K) (dec : Dec K) (ex : Extra K) :
    (OptimizedComputeCodec.encode (F := F) pub dec ex).extension (.inl (2, 2)) = pub.e.leaf :=
  rfl

/-- Same row through the deployed codec: the honest OP1 cell-literal row encodes the leaf
`1 + z·a` at role `(2, 2)`, under selector `stateIndex.s1`. -/
theorem deployed_honest_op1_cell_leaf {F : Type*} [Field F] (z alpha a : K) (ex : Extra K) :
    (OptimizedComputeCodec.encode (F := F) (honestOp1Row z alpha a)
        (decOf z 1 (honestOp1Result z a)) ex).extension (.inl (2, 2)) = 1 + z * a ∧
      (OptimizedComputeCodec.encode (F := F) (honestOp1Row z alpha a)
        (decOf z 1 (honestOp1Result z a)) ex).base
          (.inl (OptimizedComputeCodec.stateIndex .s1)) = 1 := by
  refine ⟨honest_op1_result_leaf z a, ?_⟩
  simp [OptimizedComputeCodec.encode, OptimizedComputeCodec.encodeBase, honestOp1Row, row]

end Nock.RedTeam.Batch600

#print axioms Nock.RedTeam.Batch600.honest_op1_cell_row_valid
#print axioms Nock.RedTeam.Batch600.honest_op1_result_eq_enc
#print axioms Nock.RedTeam.Batch600.atom_gates_iff
#print axioms Nock.RedTeam.Batch600.atom_gate_honest_seeds_card_le
#print axioms Nock.RedTeam.Batch600.atom_gate_rejects_honest_op1_cell
#print axioms Nock.RedTeam.Batch600.deployed_honest_op1_cell_leaf
