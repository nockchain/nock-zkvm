/-
  NockvmE2E/Exec/SoundLocal.lean   (proof-only)

  L5: the agreeing in-the-clear path `q0` built from the openings (generic in the mask; instantiated on a toy below),
  and (L7, `check_of_flat`).
-/
import NockvmE2E.Merkle.Opening
import NockvmE2E.Deep.UDLink

open BinaryTree InductiveMerkleTree OracleComp OracleSpec
open Interaction.Oracle Interaction.Oracle.Security.StateRestoration

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.SL

open NockvmE2E.Merkle

/-! ## L5: `q0` from the openings -/

section Fill

variable {F : Type}

/-- Leaf data carrying the selected values at the selected leaves and `d` elsewhere. -/
def fillLeaf (d : F) : {s : Skeleton} → (sel : LeafData Bool s) → SelectedValues F sel → LeafData F s
  | _, .leaf true, v => .leaf v
  | _, .leaf false, _ => .leaf d
  | _, .internal l r, v => .internal (fillLeaf d l v.1) (fillLeaf d r v.2)

theorem selectedValues_fillLeaf (d : F) : {s : Skeleton} → (sel : LeafData Bool s) →
    (v : SelectedValues F sel) → selectedValues (fillLeaf d sel v) sel = v
  | _, .leaf true, v => rfl
  | _, .leaf false, v => rfl
  | _, .internal l r, v => by
      simp only [fillLeaf, selectedValues]
      rw [selectedValues_fillLeaf d l v.1, selectedValues_fillLeaf d r v.2]
      rfl

end Fill

section Q0

variable {Dg : Type} [Finite Dg] [DecidableEq Dg] {Op : Type} [Finite Op] [DecidableEq Op]

/-- **`q0`**: the clear messages and challenges of the compiled path `p`; at a merkle round the word is
`words.symm` of the leaf data holding the decoded opened values at the selected leaves (and a fixed element elsewhere). -/
noncomputable def q0Of : (ms : MRounds Dg) → OpenAll Dg (merkleSkels ms) →
    (protocol (compiledRoundsK Dg Op ms)).tree.ExecutionPath →
    (protocol (baseRounds Dg ms)).tree.ExecutionPath
  | [], _, _ => PUnit.unit
  | ⟨_, .clear⟩ :: ms, os, p => ⟨p.1, p.2.1, q0Of ms os p.2.2⟩
  | ⟨_, .merkle _ _ ne enc words⟩ :: ms, (o, os), p =>
      ⟨words.symm (fillLeaf (Classical.choice ne) o.selector (o.values.map (codecDec ne enc))), p.2.1,
        q0Of ms os p.2.2⟩

/-- **L5 (`agree_q0`)**: `q0Of` agrees with the openings, for EVERY mask, openings and compiled path. -/
theorem agree_q0 : (ms : MRounds Dg) → (os : OpenAll Dg (merkleSkels ms)) →
    (p : (protocol (compiledRoundsK Dg Op ms)).tree.ExecutionPath) → Agrees ms os p (q0Of ms os p)
  | [], _, _ => trivial
  | ⟨_, .clear⟩ :: ms, os, p => ⟨rfl, rfl, agree_q0 ms os p.2.2⟩
  | ⟨_, .merkle _ _ ne enc words⟩ :: ms, (o, os), p =>
      ⟨rfl, by
        simp only [q0Of, Equiv.apply_symm_apply]
        exact (selectedValues_fillLeaf _ _ _).symm, agree_q0 ms os p.2.2⟩

end Q0

/-! ## Toy instantiation: one merkle round over `ZMod 17` leaves on the 2-leaf perfect skeleton, then a clear round -/

namespace Toy

abbrev F17 : Type := ZMod 17
abbrev Sk : Skeleton := Skeleton.internal .leaf .leaf

/-- the merkle round: message = a 2-leaf word, challenge `Unit` -/
def wRound : Round where
  Message := LeafData F17 Sk
  Challenge := Unit
  interface := OracleInterface.instDefault
  decEqMessage := inferInstance
  finiteMessage := finite_leafData Sk
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstanceAs (SampleableType Unit)

/-- a clear round: message `Unit` -/
def cRound : Round where
  Message := Unit
  Challenge := Unit
  interface := OracleInterface.instDefault
  decEqMessage := inferInstance
  finiteMessage := inferInstance
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstanceAs (SampleableType Unit)

def toyMs : MRounds F17 :=
  [⟨cRound, .clear⟩,
   ⟨wRound, .merkle Sk F17 ⟨0⟩ (Function.Embedding.refl F17) (Equiv.refl _)⟩]

/-- an opening selecting leaf 0 with value 3 (leaf 1's hash 5 on the frontier) -/
def toyOpening : BatchOpening F17 Sk where
  selector := .internal (.leaf true) (.leaf false)
  values := ((3 : F17), PUnit.unit)
  proof := .pruneRight rfl 5 .leaf

def toyOs : OpenAll F17 (merkleSkels toyMs) := (toyOpening, PUnit.unit)

/-- the compiled path: clear message, challenge, root, challenge, terminal opening message -/
def toyP : (protocol (compiledRoundsK F17 (BatchOpening F17 Sk × Unit) toyMs)).tree.ExecutionPath :=
  ⟨(), (), (11 : F17), (), (toyOpening, ()), (), PUnit.unit⟩

theorem toy_agree : ∃ q0, Agrees (Op := BatchOpening F17 Sk × Unit) toyMs toyOs toyP q0 :=
  ⟨_, agree_q0 toyMs toyOs toyP⟩

/-- the toy `q0` writes the opened value 3 at leaf 0 -/
theorem toy_q0_leaf0 : ∃ r : LeafData F17 (Skeleton.leaf),
    (q0Of (Op := BatchOpening F17 Sk × Unit) toyMs toyOs toyP).2.2.1 = .internal (.leaf 3) r := by
  have h : codecDec ⟨(0 : F17)⟩ (Function.Embedding.refl F17) 3 = 3 := codecDec_enc _ _ 3
  refine ⟨.leaf (Classical.choice ⟨(0 : F17)⟩), ?_⟩
  show LeafData.internal (.leaf (codecDec ⟨(0 : F17)⟩ (Function.Embedding.refl F17) 3)) (.leaf (Classical.choice ⟨(0 : F17)⟩)) = _
  rw [h]

end Toy

/-! ## L7: `DeepCheck` from the verifier's evaluated check, modulo a ring-hom realization of the verifier's arithmetic

The verifier computes `lhs = Σ α^i C_i` (a fold over the DAG values), `zh = Z_H(ζ)`, `qsum = Σ_j cw_j (ζ^hN)^(j/3) vQ_j`, and tests
`lhs = zh * qsum`.  Here the fold is written as the `List.foldl` it must be rewritten to (the `for … in` over an `Array` and the
`while`-based `K3.pow` cannot be unfolded by the kernel), and the arithmetic is abstracted by `VHom`: a map `φ` from the
verifier's value type to the field `K` commuting with `+`, `*`, `0`, `1`, `pow`.  The instance-level hypotheses (`hdag`, `hZ`, …) are
exactly the ones the interface puts in `ExecInst`. -/

section L7

open NockvmE2E.Deep NockvmE2E.Rap Polynomial

structure VHom (V K : Type) [Field K] where
  add : V → V → V
  mul : V → V → V
  zero : V
  one : V
  pow : V → ℕ → V
  φ : V → K
  φ_add : ∀ a b, φ (add a b) = φ a + φ b
  φ_mul : ∀ a b, φ (mul a b) = φ a * φ b
  φ_zero : φ zero = 0
  φ_one : φ one = 1
  φ_pow : ∀ a n, φ (pow a n) = φ a ^ n

variable {V K : Type} [Field K] (H : VHom V K)

/-- `Σ α^i cv_i` as the verifier folds it -/
def deepLhs (α : V) (cv : List V) : V :=
  (cv.foldl (fun (p : V × V) v => (H.add p.1 (H.mul p.2 v), H.mul p.2 α)) (H.zero, H.one)).1

theorem foldl_deep (α : V) : ∀ (cv : List V) (acc ap : V),
    H.φ (cv.foldl (fun (p : V × V) v => (H.add p.1 (H.mul p.2 v), H.mul p.2 α)) (acc, ap)).1 =
      H.φ acc + H.φ ap * ∑ i : Fin cv.length, H.φ α ^ i.1 * H.φ (cv.get i)
  | [], acc, ap => by simp
  | v :: cv, acc, ap => by
      simp only [List.foldl_cons]
      rw [foldl_deep α cv]
      erw [Fin.sum_univ_succ]
      simp only [H.φ_add, H.φ_mul, List.get_eq_getElem, Fin.val_zero, pow_zero, one_mul, Fin.val_succ,
        List.getElem_cons_succ, List.getElem_cons_zero, pow_succ]
      have : ∑ x : Fin cv.length, H.φ α ^ x.1 * H.φ α * H.φ cv[x.1] =
          H.φ α * ∑ x : Fin cv.length, H.φ α ^ x.1 * H.φ cv[x.1] := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
      rw [this]; ring

/-- `Σ_j cw_j (ζ^hN)^(j/3) vQ_j` as the verifier folds it (index carried in the state) -/
def qsumV (cw : ℕ → V) (zN : V) (vQ : List V) : V :=
  (vQ.foldl (fun (p : V × ℕ) v => (H.add p.1 (H.mul (H.mul (cw p.2) (H.pow zN (p.2 / 3))) v), p.2 + 1))
    (H.zero, 0)).1

theorem foldl_qsum (cw : ℕ → V) (zN : V) : ∀ (vQ : List V) (acc : V) (j0 : ℕ),
    H.φ (vQ.foldl (fun (p : V × ℕ) v => (H.add p.1 (H.mul (H.mul (cw p.2) (H.pow zN (p.2 / 3))) v), p.2 + 1))
      (acc, j0)).1 =
      H.φ acc + ∑ i : Fin vQ.length, H.φ (cw (j0 + i.1)) * H.φ zN ^ ((j0 + i.1) / 3) * H.φ (vQ.get i)
  | [], acc, j0 => by simp
  | v :: vQ, acc, j0 => by
      simp only [List.foldl_cons]
      rw [foldl_qsum cw zN vQ]
      erw [Fin.sum_univ_succ]
      simp only [H.φ_add, H.φ_mul, H.φ_pow, List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
        List.getElem_cons_succ, List.getElem_cons_zero, add_zero]
      have : ∀ x : Fin vQ.length, j0 + (x.1 + 1) = j0 + 1 + x.1 := fun x => by omega
      simp only [this]
      ring

variable {Φ : CoinFrame} {ι β : Type} [Fintype K] [DecidableEq K] {colRound : ι → ℕ}

/-- **L7 (`check_of_flat`, core).**  If the verifier's evaluated test `lhs = zh * qsum` holds, and its arithmetic is realized in `K`
by `φ` with the instance hypotheses (`hdag`: the DAG values are `A.Cv`; `hZ`: `zh = Z_H(ζ)`; `he`: three chunks per power; …), then
`DeepCheck` holds. -/
theorem deepCheck_of_flat (P : DeepParams Φ K ι β colRound) {r : ℕ} (A : AirShape P r) (χ : Coins Φ K) (α ζ : K)
    (vT : ι × Fin r → K) (vQ : Fin P.nq → K)
    (αV zhV zNV : V) (cv : List V) (cwV : ℕ → V) (vQV : List V)
    (hα : H.φ αV = α) (hlen : cv.length = P.ns)
    (hdag : ∀ i : Fin cv.length, H.φ (cv.get i) = A.Cv χ ζ (Fin.cast hlen i) vT)
    (hZ : H.φ zhV = eval ζ P.Zpoly) (he : P.e = 3) (hzN : H.φ zNV = ζ ^ P.H.card)
    (hqlen : vQV.length = P.nq) (hcw : ∀ j : Fin vQV.length, H.φ (cwV j.1) = P.cw (Fin.cast hqlen j))
    (hQ : ∀ j : Fin vQV.length, H.φ (vQV.get j) = vQ (Fin.cast hqlen j))
    (h : deepLhs H αV cv = H.mul zhV (qsumV H cwV zNV vQV)) : DeepCheck P A χ α ζ vT vQ := by
  have h1 := congrArg H.φ h
  have hl : H.φ (deepLhs H αV cv) = ∑ i : Fin P.ns, α ^ i.1 * A.Cv χ ζ i vT := by
    unfold deepLhs
    rw [foldl_deep H αV cv H.zero H.one, H.φ_zero, H.φ_one, zero_add, one_mul, hα]
    refine Fintype.sum_equiv (finCongr hlen) _ _ fun i => ?_
    rw [hdag i]; rfl
  have hr : H.φ (qsumV H cwV zNV vQV) = ∑ j : Fin P.nq, P.cw j * ζ ^ (j.1 / P.e * P.H.card) * vQ j := by
    unfold qsumV
    rw [foldl_qsum H cwV zNV vQV H.zero 0, H.φ_zero, zero_add]
    refine Fintype.sum_equiv (finCongr hqlen) _ _ fun j => ?_
    rw [zero_add, hcw j, hQ j, hzN, he, ← pow_mul, mul_comm P.H.card]
    rfl
  rw [hl, H.φ_mul, hZ, hr] at h1
  exact h1

/-- **`OffDom` from the verifier's power test.** If every domain point `y` satisfies `y^N = c^N` (the domain is the coset `c·μ_N`, `N = 2^n`)
and every opening point `pt_j` has `pt_j^N ≠ c^N` (the verifier's check (v)), then no opening point lies on the domain. -/
theorem offDom_of_pow {F J : Type} [Field F] (N : ℕ) (c : F) {D : Type} (ω : D → F) (hω : ∀ i, ω i ^ N = c ^ N)
    (pts : J → F) (hpt : ∀ j, pts j ^ N ≠ c ^ N) : ∀ j i, ω i ≠ pts j := by
  intro j i h
  exact hpt j (h ▸ hω i)

end L7

end NockvmE2E.Exec.SL

#print axioms NockvmE2E.Exec.SL.agree_q0
#print axioms NockvmE2E.Exec.SL.Toy.toy_agree
#print axioms NockvmE2E.Exec.SL.Toy.toy_q0_leaf0
#print axioms NockvmE2E.Exec.SL.deepCheck_of_flat
#print axioms NockvmE2E.Exec.SL.offDom_of_pow
