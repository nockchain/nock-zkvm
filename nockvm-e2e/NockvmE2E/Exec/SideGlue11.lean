/-
 conjunct 5, word0 link, step 1: `initialOracle_side`, the initial oracle of the batched side statement `stmtOf` at a domain
point is the verifier's batched word `φ (deepWordS ..)` (the side analogue of `E2EFri.initialOracle_combined`, with `stmtOf`'s honest words in place
of the main DEEP statement).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue11` is complete.
-/
import NockvmE2E.Exec.SideGlue10
import NockvmE2E.Exec.HFixFri

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue11
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri
  NockvmE2E.FriPort NockvmE2E.FriPort.Batched NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriDeep

variable {k m : ℕ} (s : Fin (k + 1) → ℕ+)

/-- **`initialOracle_side`** -/
theorem initialOracle_side (C : SideCfg m) (hn : C.XI.nD ≤ 32) (st : SideStmt)
    {S : Type} (G : CoreDefinitions.Generator S (Fin (m + 1)) KC) (csS : S) (cs : KC)
    (hG : ∀ i : Fin (m + 1), G csS i = cs ^ (i : ℕ))
    (pts : Array VF.K3) (ops : List (ℕ × ℕ × VF.K3 × VF.K3)) (baseAt : ℕ → ℕ → VF.G)
    (idx : Fin (2 ^ C.XI.nD)) (y : ((smoothDomain C.XI.nD hn).subdomain 0).toFinset) (hy : y.val = smoothDomain C.XI.nD hn idx)
    (hω : smoothDomain C.XI.nD hn idx = homV.ψ C.XI.dShift * homV.ψ C.XI.dGen ^ (idx : ℕ))
    (hops : List.Forall₂ (fun (o : ℕ × ℕ × VF.K3 × VF.K3) (j : Fin (m + 1)) =>
      o.2.1 < C.XI.r + 2 ∧ homV.φ o.2.2.1 = cs ^ (j : ℕ) ∧ homV.φ pts[o.2.1]! = C.pt st j ∧
      homV.φ o.2.2.2 = C.val st j ∧ homV.ψ (baseAt o.1 idx) = honestWord C.XI (C.col j) idx)
      ops (List.finRange (m + 1)))
    (hops_can : ∀ o ∈ ops, homV.C o.2.2.1 ∧ homV.C o.2.2.2 ∧ homV.Cg (baseAt o.1 idx))
    (hpts_can : ∀ p, p < C.XI.r + 2 → homV.C pts[p]!)
    (s : Fin (k + 1) → ℕ+) (hs0 : (∑ j' ∈ finRangeTo (k + 1) (0 : Fin 1).1, (s j').1) = 0) :
    initialOracle (ω := smoothDomain C.XI.nD hn) s (combinedStmt s m G csS (stmtOf C hn st)) y
      = homV.φ (deepWordS C.XI pts ops baseAt idx) := by
  rw [(deepWordS_hom homV C.XI pts ops baseAt idx hops_can hpts_can).2, opSum]
  have hy' : y.val ∈ (((smoothDomain C.XI.nD hn)).subdomain (∑ j' ∈ finRangeTo (k + 1) (0 : Fin 1).1, (s j').1)).toFinset := by
    rw [hs0]; exact y.2
  unfold initialOracle combinedStmt
  erw [cast_fun_apply (e := (by simp [finRangeTo] : (∑ j' ∈ finRangeTo (k + 1) (0 : Fin 1).1, (s j').1) = 0))]
  unfold combinedOracle
  dsimp only
  have hv : initialDomainPoint (s := s) (0 : Fin 1) ⟨y.val, hy'⟩ = (smoothDomain C.XI.nD hn).equivToFinset idx := Subtype.ext hy
  have key : ∀ j : Fin (m + 1), (stmtOf C hn st).2 j (initialDomainPoint (s := s) (0 : Fin 1) ⟨y.val, hy'⟩) =
      NockvmE2E.Deep.deepWord (⇑(smoothDomain C.XI.nD hn)) (honestWord C.XI (C.col j)) (C.pt st j) (C.val st j) idx := fun j => by
    rw [hv]; exact stmtOf_words C hn st j idx
  refine Eq.trans (congrArg List.sum (List.map_congr_left (fun j _ => congrArg (G csS j * ·) (key j)))) ?_
  refine (forall2_sum _ (fun o : ℕ × ℕ × VF.K3 × VF.K3 => if o.2.1 < C.XI.r + 2 then
      homV.φ o.2.2.1 * (homV.ψ (baseAt o.1 ↑idx) - homV.φ o.2.2.2) *
        (homV.ψ C.XI.dShift * homV.ψ C.XI.dGen ^ (idx : ℕ) - homV.φ pts[o.2.1]!)⁻¹ else 0)
    (fun j : Fin (m + 1) => G csS j * NockvmE2E.Deep.deepWord (⇑(smoothDomain C.XI.nD hn)) (honestWord C.XI (C.col j)) (C.pt st j) (C.val st j) idx)
    ?_ ops _ hops).symm
  rintro o j ⟨hp, hc, hpt, hval, hb⟩
  simp only [if_pos hp]
  unfold NockvmE2E.Deep.deepWord
  rw [hc, hpt, hval, hb, ← hω, hG, div_eq_mul_inv]
  ring

open NockvmE2E.Exec.V in
/-- **`baseAt_honest`**: when every selected tree-0 leaf is the honest leaf (the `¬VKcoll` situation), the verifier's base read at (column `c`, domain index `idx`)
is the honest spec word.  `idx % half` must be a (reduced) query position, `c < F`. -/
theorem baseAt_honest (X0 XV : ExecInst) (hnd : XV.nD = X0.nD) (hn1 : 1 ≤ XV.nD) (F : ℕ) (hF : 0 < F) (pos : Array ℕ) (vals0 : Array ℕ)
    (hhon : ∀ r, r < (treeSel XV F 0 pos).size →
      vals0[r]! = honestLeaf X0 F (2 ^ (XV.nD - 1)) (treeSel XV F 0 pos)[r]!)
    (c idx : ℕ) (hc : c < F) (hidx : idx < 2 ^ XV.nD) (q : ℕ) (hq : q ∈ pos.toList) (hqi : q % 2 ^ (XV.nD - 1) = idx % 2 ^ (XV.nD - 1)) :
    UInt64.ofNat vals0[lb (treeSel XV F 0 pos) ((idx % 2 ^ (XV.nD - 1)) * 2 * F + (idx / 2 ^ (XV.nD - 1)) * F + c)]! =
      specWord X0 (fixCols X0)[c]! idx := by
  have hhalf : 0 < 2 ^ (XV.nD - 1) := Nat.two_pow_pos _
  have h2 : 2 ^ XV.nD = 2 * 2 ^ (XV.nD - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hs2 : idx / 2 ^ (XV.nD - 1) < 2 := by
    apply Nat.div_lt_of_lt_mul; omega
  have hp : (idx % 2 ^ (XV.nD - 1)) * 2 * F + (idx / 2 ^ (XV.nD - 1)) * F + c ∈ (treeSel XV F 0 pos).toList := by
    have := leafPos_mem_treeSel XV F 0 pos (by omega) q c hq hc (idx / 2 ^ (XV.nD - 1)) hs2
    rw [Nat.mod_mod, hqi] at this
    exact this
  have hlb := (mem_iff_lb (treeSel XV F 0 pos) (treeSel_pw XV F 0 pos) _).mpr hp
  have hr : lb (treeSel XV F 0 pos) ((idx % 2 ^ (XV.nD - 1)) * 2 * F + (idx / 2 ^ (XV.nD - 1)) * F + c) < (treeSel XV F 0 pos).size := by
    by_contra hcn
    rw [Array.getElem?_eq_none (by omega)] at hlb
    simp at hlb
  rw [Array.getElem?_eq_getElem hr] at hlb
  have hsp : (treeSel XV F 0 pos)[lb (treeSel XV F 0 pos) ((idx % 2 ^ (XV.nD - 1)) * 2 * F + (idx / 2 ^ (XV.nD - 1)) * F + c)]! =
      (idx % 2 ^ (XV.nD - 1)) * 2 * F + (idx / 2 ^ (XV.nD - 1)) * F + c := by
    rw [getElem!_pos (treeSel XV F 0 pos) _ hr]; exact Option.some.inj hlb
  rw [hhon _ hr, hsp]
  unfold honestLeaf
  have e1 : ((idx % 2 ^ (XV.nD - 1)) * 2 * F + (idx / 2 ^ (XV.nD - 1)) * F + c) % (2 * F) = (idx / 2 ^ (XV.nD - 1)) * F + c := by
    have : (idx % 2 ^ (XV.nD - 1)) * 2 * F + (idx / 2 ^ (XV.nD - 1)) * F + c =
        ((idx / 2 ^ (XV.nD - 1)) * F + c) + (2 * F) * (idx % 2 ^ (XV.nD - 1)) := by ring
    rw [this, Nat.add_mul_mod_self_left]
    apply Nat.mod_eq_of_lt
    have : (idx / 2 ^ (XV.nD - 1)) * F + c < 2 * F := by nlinarith
    exact this
  have e2 : ((idx / 2 ^ (XV.nD - 1)) * F + c) % F = c := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hc
  have e3 : ((idx / 2 ^ (XV.nD - 1)) * F + c) / F = idx / 2 ^ (XV.nD - 1) := by
    rw [Nat.mul_comm, Nat.mul_add_div hF, Nat.div_eq_of_lt hc]; simp
  have e4 : ((idx % 2 ^ (XV.nD - 1)) * 2 * F + (idx / 2 ^ (XV.nD - 1)) * F + c) / (2 * F) = idx % 2 ^ (XV.nD - 1) := by
    have : (idx % 2 ^ (XV.nD - 1)) * 2 * F + (idx / 2 ^ (XV.nD - 1)) * F + c =
        ((idx / 2 ^ (XV.nD - 1)) * F + c) + (2 * F) * (idx % 2 ^ (XV.nD - 1)) := by ring
    rw [this, Nat.add_mul_div_left _ _ (by omega)]
    rw [Nat.div_eq_of_lt (by nlinarith), zero_add]
  rw [e1, e2, e3, e4]
  have : idx % 2 ^ (XV.nD - 1) + idx / 2 ^ (XV.nD - 1) * 2 ^ (XV.nD - 1) = idx := by
    rw [mul_comm]; exact Nat.mod_add_div _ _
  rw [this]
  exact UInt64.ofNat_toNat

end NockvmE2E.Exec.SideGlue11

#print axioms NockvmE2E.Exec.SideGlue11.initialOracle_side
#print axioms NockvmE2E.Exec.SideGlue11.baseAt_honest
