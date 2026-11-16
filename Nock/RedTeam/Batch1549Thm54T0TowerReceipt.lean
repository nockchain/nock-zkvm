/-
  Nock/RedTeam/Batch1549Thm54T0TowerReceipt.lean

  **Receipts for the quadratic-tower fingerprint objects.**

  Production modules (all additive, under `P8Core/`, none imported by the statement):
  * `Batch1540Thm54T0IOExt` — `IOFailureEventExt`, `IOFailureEventExt_card_le`: **the ioFUB twin**.
    Records over an extension `L` of the coin field `K`, coins `γ, pole ∈ K`; the failure set has
    at most `ioFailureUnionBound m k₁ k₂ |K|` elements, the same numeral as at records over `K`.
  * `Batch1541Thm54T0Tower` — `Quad δ = 𝕂[X]/(X²−δ)` with its `Field` instance under
    `Fact (¬ IsSquare δ)`, `quad_card`, `nonsquare_lift`, `tower_irreducible`, coordinates
    `Quad.mk`, `mk_mul`, `mk_inv`, `mk_bijective`, `tower_pair_collision_prob`,
    `tower_beats_two_seeds`, `tower_window_card_le`.
  * `Batch1542Thm54T0TowerFP` — `FP2`, `fn2`, `FP2.cons`, `fn2_cons` / `fn2_atom`, the Re/Im gates
    (`qmul`, `consSize`, `consLeaf`, `consDyck`, `atomTest`), `qmul_val`, `cons_gates_iff`,
    `cons_gates_of_enc`, the compiler link (`gate_zero_iff_compiled`,
    `cons_gates_compiled_degrees`) and the exact degrees.

  This artifact: (1) `#print axioms`; (2) the NEGATIVE CONTROL — `qmulBad` drops the sign of the
  `Im` part's cross term (`ad − bc` for `ad + bc`): `qmul_val` then FAILS at an explicit
  `𝔽 = 𝕂 = ZMod 7`, `δ = 3` witness, while the genuine `qmul` agrees; (3) `|𝕂′| = |𝕂|²` at
  `ZMod 7`; (4) the gate degrees.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1540Thm54T0IOExt
import Nock.NockVMROM.Thm54.P8Core.Batch1541Thm54T0Tower
import Nock.NockVMROM.Thm54.P8Core.Batch1542Thm54T0TowerFP

namespace Nock.RedTeam.Batch1549T0

open Nock.NockVMROM.Thm54.T0TowerFP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.Reified

instance fact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## Negative control: drop the sign of the `Im` cross term -/

/-- `qmul` with `Im = ad − bc`. -/
def qmulBad (δ : F) (a b : Q F) : Q F :=
  (.Add (.Mul a.1 b.1) (.Scale (.const δ) (.Mul a.2 b.2)), .Sub (.Mul a.1 b.2) (.Mul a.2 b.1))

theorem not_square_three : ¬ IsSquare (3 : ZMod 7) := by decide

/-- `a = 0 + 1·√δ`, `b = 1 + 0·√δ` as environment columns `0..3`. -/
def env7 : Env (ZMod 7) where
  trace := fun i => if i = 1 then 1 else if i = 2 then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

def aQ : Q (ZMod 7) := (.Var .traceCur 0, .Var .traceCur 1)
def bQ : Q (ZMod 7) := (.Var .traceCur 2, .Var .traceCur 3)

/-- The genuine `qmul` agrees with the product at the witness (`√δ · 1 = √δ`). -/
theorem control_good :
    Q.val (3 : ZMod 7) (qmul (ZMod 7) 3 aQ bQ) env7 env7 =
      Q.val 3 aQ env7 env7 * Q.val 3 bQ env7 env7 :=
  qmul_val (3 : ZMod 7) env7 env7 aQ bQ

/-- The sign-dropped gate has `Im = −1` where the product has `Im = 1`. -/
theorem control_bad_im :
    (qmulBad (3 : ZMod 7) aQ bQ).2.eval env7 env7 = -1 ∧
      (qmul (ZMod 7) 3 aQ bQ).2.eval env7 env7 = 1 := by
  refine ⟨?_, ?_⟩ <;> simp [qmulBad, qmul, aQ, bQ, MixedExpr.eval, env7]

/-- **The identity fails without the sign**: `qmulBad` is not multiplication in `𝕂′`. -/
theorem control_bad_fails :
    Q.val (3 : ZMod 7) (qmulBad (3 : ZMod 7) aQ bQ) env7 env7 ≠
      Q.val 3 aQ env7 env7 * Q.val 3 bQ env7 env7 := by
  haveI : Fact (¬ IsSquare (algebraMap (ZMod 7) (ZMod 7) 3)) := ⟨by simpa using not_square_three⟩
  rw [← control_good]
  intro h
  simp only [Q.val] at h
  have h2 := ((Quad.mk_eq_mk_iff _ _ _ _ _).mp h).2
  have := control_bad_im
  rw [this.1, this.2] at h2
  revert h2
  decide

/-- `|𝕂′| = |𝕂|²` at `ZMod 7`. -/
example : Fintype.card (Quad (3 : ZMod 7)) = 49 := by rw [quad_card, ZMod.card]; norm_num

/-! ## Gate degrees (exact), all `≤ 4` -/

example (F : Type) (δ : F) : qdeg F (consSize F δ (ptQ F) (lcQ F) (rcQ F)) = 2 :=
  consSize_degree F δ
example (F : Type) (δ : F) : qdeg F (consLeaf F δ (ptQ F) (lcQ F) (rcQ F)) = 2 :=
  consLeaf_degree F δ
example (F : Type) (δ : F) : qdeg F (consDyck F δ (zq F) (ptQ F) (lcQ F) (rcQ F)) = 3 :=
  consDyck_degree F δ
example (F : Type) (δ : F) :
    qdeg F (qsmul F (provCol F) (consDyck F δ (zq F) (ptQ F) (lcQ F) (rcQ F))) = 4 :=
  prov_consDyck_degree F δ
example (F : Type) : qdeg F (atomTest F (.var .traceCur 3) (ptQ F)) = 2 := atomTest_degree F

#check @Nock.NockVMROM.Thm54.T0IOExt.IOFailureEventExt_card_le

end Nock.RedTeam.Batch1549T0

#print axioms Nock.NockVMROM.Thm54.T0IOExt.IOFailureEventExt_card_le
#print axioms Nock.NockVMROM.Thm54.T0Tower.nonsquare_lift
#print axioms Nock.NockVMROM.Thm54.T0Tower.tower_irreducible
#print axioms Nock.NockVMROM.Thm54.T0Tower.quad_card
#print axioms Nock.NockVMROM.Thm54.T0Tower.tower_pair_collision_prob
#print axioms Nock.NockVMROM.Thm54.T0Tower.tower_beats_two_seeds
#print axioms Nock.NockVMROM.Thm54.T0Tower.tower_window_card_le
#print axioms Nock.NockVMROM.Thm54.T0Tower.Quad.mk_inv
#print axioms Nock.NockVMROM.Thm54.T0Tower.Quad.mk_bijective
#print axioms Nock.NockVMROM.Thm54.T0TowerFP.fn2_cons
#print axioms Nock.NockVMROM.Thm54.T0TowerFP.fn2_atom
#print axioms Nock.NockVMROM.Thm54.T0TowerFP.qmul_val
#print axioms Nock.NockVMROM.Thm54.T0TowerFP.cons_gates_iff
#print axioms Nock.NockVMROM.Thm54.T0TowerFP.cons_gates_of_enc
#print axioms Nock.NockVMROM.Thm54.T0TowerFP.cons_gates_compiled_degrees
#print axioms Nock.NockVMROM.Thm54.T0TowerFP.gate_zero_iff_compiled
#print axioms Nock.NockVMROM.Thm54.T0TowerFP.consDyck_degree
#print axioms Nock.RedTeam.Batch1549T0.control_good
#print axioms Nock.RedTeam.Batch1549T0.control_bad_fails
