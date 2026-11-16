/-
  NockvmE2E/Exec/SoundFlatFri.lean   (proof-only)

  The verifier's FRI part of `FlatOk` read as the flat model `FlatFri` of SoundFri (in the field `KC`, through `VL.homV`), with every
  canonicity side condition read off `FlatOk`.  Verifier-side half of L9; the audited-side half is `SF.friAccepts_of_flat` (hypothesis `Link`).
-/
import NockvmE2E.Exec.Sound

set_option autoImplicit false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec NockvmE2E.Exec.VL

section FriPart
variable (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof)

/-- the batching challenge `cs` -/
def csOf : VF.K3 := VF.K3.ofLimbs (chalsOf XI FS z π)[6]!
/-- the FRI folding challenges `α_0 .. α_k` -/
def alphasOf : Array VF.K3 := (Array.range (XI.k + 1)).map fun w => VF.K3.ofLimbs (chalsOf XI FS z π)[7 + w]!
/-- the opened base value of column `c` at domain index `idx` (leaf `idx%half·2W + (idx/half)·W + rank c` of its RAP block) -/
def baseAtOf (c idx : Nat) : VF.G :=
  let b := XI.blockOf[c]!
  let half0 := 2 ^ (XI.nD - 1)
  UInt64.ofNat (π.vals[b]!)[lb (selsOf XI π)[b]!
    ((idx % half0) * 2 * (blockLayout XI).1[b]! + (idx / half0) * (blockLayout XI).1[b]! + (blockLayout XI).2[c]!)]!
/-- the verifier's FRI input word -/
def word0Of : Nat → VF.K3 :=
  deepWord XI (openPts XI (zetaOf XI FS z π)) (openingList XI (csOf XI FS z π) π.vT π.vQ) (baseAtOf XI π)

theorem flatOk_fri_walk (H : HFn) (hok : FlatOk XI H FS z π) :
    ∀ q ∈ π.pos.toList, SF.walkK XI (word0Of XI FS z π) (faV π.vals (selsOf XI π)) (fbV π.vals (selsOf XI π))
      (alphasOf XI FS z π) π.pfinal q = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hf⟩ := hok
  intro q hq
  exact (fri_query_iff_walkK XI π.vals (selsOf XI π) (alphasOf XI FS z π) π.pfinal q (word0Of XI FS z π)).mp (hf q hq)

/-- `nD ≥ k + 1`, from the parameter check -/
theorem flatOk_nD (H : HFn) (hok : FlatOk XI H FS z π) : XI.k + 1 ≤ XI.nD := by
  obtain ⟨_, _, h, _⟩ := hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

/-- the flat FRI model for every query, in `KC` (`W w i` = the opened word `w` at index `i`, `αN`, the final polynomial) -/
theorem flatOk_flatFri (H : HFn) (hok : FlatOk XI H FS z π) :
    ∀ q ∈ π.pos.toList,
      SF.FlatFri (homV.ψ XI.dShift) (homV.ψ XI.dGen) XI.nD XI.k
        (fun w i => homV.φ (SF.Wf XI (word0Of XI FS z π) (faV π.vals (selsOf XI π)) (fbV π.vals (selsOf XI π)) w i))
        (fun i => homV.φ (alphasOf XI FS z π)[i]!)
        (SF.hornerF (fun j => homV.φ π.pfinal[j]!) π.pfinal.size) q := by
  intro q hq
  obtain ⟨hvT, hvQ, hpf, hvals⟩ := flatOk_limbs XI H FS z π hok
  exact SF.flat_of_walk (flatOk_nD XI FS z π H hok) _ _ _ _
    (walkK_sound_V XI (word0Of XI FS z π) π.vals (selsOf XI π) (alphasOf XI FS z π) π.pfinal q hvals hpf
      (fun i => canon3_deepWord _ _ _ _ _) (flatOk_fri_walk XI FS z π H hok q hq))

end FriPart

/-! ### verifier-side L6: every leaf the verifier reads is a selected leaf (membership in `treeSel`) -/
section Cover

theorem mem_foldl_insertD : ∀ (l acc : List Nat), acc.Pairwise (· < ·) →
    ∀ y, y ∈ l.foldl (fun acc x => insertD x acc) acc ↔ y ∈ l ∨ y ∈ acc := by
  intro l
  induction l with
  | nil => intro acc _ y; simp
  | cons x l ih =>
    intro acc hacc y
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := insertD_pw x acc hacc
    rw [ih _ h1, h2]
    simp only [List.mem_cons]; tauto

theorem mem_sortedDistinct (a : Array Nat) (y : Nat) : y ∈ (sortedDistinct a).toList ↔ y ∈ a.toList := by
  unfold sortedDistinct
  simp only [List.toList_toArray]
  rw [mem_foldl_insertD _ _ List.Pairwise.nil]
  simp

/-- a RAP-block leaf of the group of position `q` is selected -/
theorem mem_treeSel_rap (XI : ExecInst) (Wb j : Nat) (pos : Array Nat) (hj : j < 4) (hW : Wb ≠ 0) (q : Nat) (hq : q ∈ pos.toList)
    (t : Nat) (ht : t < 2 * Wb) : (q % 2 ^ (XI.nD - 1)) * 2 * Wb + t ∈ (treeSel XI Wb j pos).toList := by
  unfold treeSel
  simp only [hj, if_true, hW, beq_iff_eq, if_false]
  simp only [Array.toList_flatMap, List.mem_flatMap, Array.toList_map, List.mem_map, Array.toList_range, List.mem_range]
  refine ⟨q % 2 ^ (XI.nD - 1), ?_, t, ht, rfl⟩
  rw [mem_sortedDistinct]
  simp only [Array.toList_map, List.mem_map]
  exact ⟨q, hq, rfl⟩

/-- both leaves `2g, 2g+1` of the FRI-word fold pair of position `q` are selected -/
theorem mem_treeSel_fri (XI : ExecInst) (j : Nat) (pos : Array Nat) (hj : ¬ j < 4) (q : Nat) (hq : q ∈ pos.toList) (e : Nat) (he : e < 2) :
    2 * (q % 2 ^ (XI.nD - (j - 3) - 1)) + e ∈ (treeSel XI 0 j pos).toList := by
  unfold treeSel
  simp only [hj, if_false]
  simp only [Array.toList_flatMap, List.mem_flatMap]
  refine ⟨q % 2 ^ (XI.nD - (j - 3) - 1), ?_, ?_⟩
  · rw [mem_sortedDistinct]
    simp only [Array.toList_map, List.mem_map]
    exact ⟨q, hq, rfl⟩
  · interval_cases e <;> simp

/-- the verifier's base read of column `c` at index `idx ∈ {g0, g0 + half}` (leaf `(idx%half)·2W + (idx/half)·W + rank`) is a selected leaf,
given `rank < W` (a property of `blockLayout`, not proved here) -/
theorem leafPos_mem_treeSel (XI : ExecInst) (Wb j : Nat) (pos : Array Nat) (hj : j < 4) (q rk : Nat) (hq : q ∈ pos.toList)
    (hrk : rk < Wb) (s : Nat) (hs : s < 2) :
    ((q % 2 ^ (XI.nD - 1)) % 2 ^ (XI.nD - 1)) * 2 * Wb + s * Wb + rk ∈ (treeSel XI Wb j pos).toList := by
  have hW : Wb ≠ 0 := by omega
  have := mem_treeSel_rap XI Wb j pos hj hW q hq (s * Wb + rk) (by nlinarith)
  rw [Nat.mod_mod, ← add_assoc] at *
  simpa [add_assoc] using this

end Cover

/-! ### non-vacuity (kernel): the new hypotheses are satisfiable.  `FlatOk` itself is NOT kernel-instantiated (its Merkle/FS conjuncts hold only for
real prover output; `toyProve2` runs in the exe), nor `DeepLink`/`SF.Link` (they need a concrete `DeepParams` / ArkLib oracle history). -/
section NonVac

/-- `tabs_fold` on one table with constraint value `1` and multiplier `1`: all its canonicity hypotheses hold -/
example (t : TabInst) :
    toKV ([t].foldl (tabStep VF.K3.one (fun _ => #[VF.K3.one]) (fun _ => VF.K3.one)) (VF.K3.zero, VF.K3.one)).1 =
      toKV VF.K3.zero + toKV VF.K3.one *
        hornerA (toKV VF.K3.one) (termsK VF.K3.one (fun _ => #[VF.K3.one]) (fun _ => VF.K3.one) [t]) :=
  (tabs_fold VF.K3.one (fun _ => #[VF.K3.one]) (fun _ => VF.K3.one) [t] VF.K3.zero VF.K3.one canon3_zero canon3_one
    (fun _ _ v hv => by simp at hv; rw [hv]; exact canon3_one) (fun _ _ => canon3_one)).2.2.1

/-- the public-side hypothesis shape is satisfiable (`PubRel := True`) -/
example (XI : ExecInst) (FS : FSFn) (z : List Nat) (π : FlatProof) :
    XI.pubCheck (slotsOf XI FS z π) (pubOfProof XI π) = true → (fun (_ : Array VF.K3) (_ : Array VF.G) => True) (slotsOf XI FS z π) (pubOfProof XI π) :=
  fun _ => trivial

/-- FRI selection coverage on the trivial instance -/
example : 2 * (0 % 2 ^ (toyInst.nD - (4 - 3) - 1)) + 0 ∈ (treeSel toyInst 0 4 #[0]).toList :=
  mem_treeSel_fri toyInst 4 #[0] (by decide) 0 (by simp) 0 (by decide)

example : 0 * 2 * 1 + 1 ∈ (treeSel toyInst 1 0 #[0]).toList := by
  have := mem_treeSel_rap toyInst 1 0 #[0] (by decide) (by decide) 0 (by simp) 1 (by decide)
  simpa using this

end NonVac
end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.flatOk_flatFri
#print axioms NockvmE2E.Exec.V.mem_treeSel_rap
#print axioms NockvmE2E.Exec.V.mem_treeSel_fri
#print axioms NockvmE2E.Exec.V.leafPos_mem_treeSel
