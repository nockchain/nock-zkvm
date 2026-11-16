/-
  Nock/RedTeam/Batch4833Thm54J8ComplL2.lean
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Cell
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8

namespace Nock.RedTeam.Batch4833

open Nock.NockVMROM.Thm54.VclL.Handle

#check @ComplJ8Cell.cellRowsB
#print axioms ComplJ8Cell.cellRowsB_baseFacts
#print axioms ComplJ8Cell.cellRowsB_cons
#print axioms ComplJ8Cell.cellRowsB_atomL
#print axioms ComplJ8Cell.cellRowsB_atomR
#print axioms ComplJ8Cell.cellChip_honest_list
#print axioms ComplJ8Cell.cellChip_honest_list_bind
#print axioms ComplJ8Cell.cellChipHQ_honest_list
#print axioms ComplJ8Cell.limbs_ne_zero
#print axioms ComplJ8Cell.sideOK_child
#print axioms ComplJ8Cell.sideOK_rowsB_L
#print axioms ComplJ8Cell.sideOK_rowsB_R
#print axioms ComplJ8Cell.cellChipHQKW_honest_list
#print axioms ComplJ8Cell.cellChipHQKW_honest_list_bind

-- the J-8 walk (`Handle/ComplJ8Walk`): binder `WalkDepthOK` (every read of depth `≤ 61`), `len ≤ 60`, three chips
#check @ComplJ8Walk.WalkDepthOK
#print axioms ComplJ8Walk.walkRows_len_le60
#print axioms ComplJ8Walk.wRowsB_root
#print axioms ComplJ8Walk.walkOk_honest_list
#print axioms ComplJ8Walk.walkChip_honest_list
#print axioms ComplJ8Walk.walkChipHQK_honest_list
#print axioms ComplJ8Walk.walkChipJ8_honest_list

-- staging of the honest cell / J-8 walk traces (`StJ8`'s `M`, `W`), the `hleaf` binder and the J-8 instance
#print axioms ComplJ8Walk.cellTrM_staged
#print axioms ComplJ8Walk.walkTrW_staged
#check @ComplJ8Walk.RootsLeafOK
#print axioms ComplJ8Walk.cellsOfRoots_mem
#print axioms ComplJ8Walk.cells_ok_of_leaf
#print axioms ComplJ8Walk.j8_cells_ok

end Nock.RedTeam.Batch4833

/-! * **NC 1** (`hleaf_not_implied`): `*[0 F 110]` with `F (k+1) = [7 (F k) [[0 1] [0 1]]]` doubles the subject 110 times;
  every atom `< 8`, `hax`, `hop5`, `hwalk` hold on its generated tree; the result has `2^110` leaves, so `hleaf`
  (phase-A `ProgLeafOK` and the demand-root `RootsLeafOK`) fails.
* **NC 2** (`hwalk_not_implied`): `*[sW [0 2^62]]` with `sW` the left spine of depth 62; every atom `< p`, `hax`,
  `hop5`, `hleaf` hold; `WalkDepthOK` fails on its reads (depth 62).
-/

namespace Nock.RedTeam.Batch4833NC
open Nock Nock.Walk Nock.Edit.GenX Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle

/-! ## NC 2: `hwalk` is not implied (an op-0 read of depth 62 at a small axis `2^62 < p`) -/

/-- The left spine of depth `k` (all atoms `0`). -/
def deep : ℕ → Noun
  | 0 => .atom 0
  | k + 1 => .cell (deep k) (.atom 0)

theorem slot_deep : ∀ k m : ℕ, Noun.slot (2 ^ k) (deep (k + m)) = some (deep m)
  | 0, m => by simp [Noun.slot]
  | k + 1, m => by
    have h2 : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : 2 ^ (k + 1) = (2 ^ (k + 1) - 2) + 2 := by omega
    have hd : ((2 ^ (k + 1) - 2) + 2) / 2 = 2 ^ k := by rw [← e, pow_succ]; omega
    have hm : ((2 ^ (k + 1) - 2) + 2) % 2 = 0 := by rw [← e, pow_succ]; omega
    rw [e, Noun.slot, hd, hm, show k + 1 + m = k + (m + 1) by omega, slot_deep k (m + 1)]
    simp [deep]

theorem depthOf_pow (k : ℕ) : depthOf (2 ^ k) = k := by
  induction k with
  | zero => simp [depthOf, axisBits_of_lt_two]
  | succ k ih =>
    have h2 : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [depthOf] at ih ⊢
    rw [axisBits_of_two_le h2, List.length_append, show 2 ^ (k + 1) / 2 = 2 ^ k by rw [pow_succ]; omega, ih]
    rfl

def sW : Noun := deep 62
def fW : Noun := .cell (.atom 0) (.atom (2 ^ 62))
def tW : NTree SkelX := mkX .s0 sW fW (.atom 0) []

theorem slotW : Noun.slot 4611686018427387904 sW = some (Noun.atom 0) := by
  have h := slot_deep 62 0
  norm_num at h
  exact h

theorem runW : evalN 1 sW fW = some (Noun.atom 0) := by
  simp only [evalN, fW]
  exact slotW

theorem genW (R : Nock.Jet.Registry) : genX R 1 sW fW = some (tW, Noun.atom 0) := by
  simp only [genX, genComputeSkeletonX, fW, tW]
  norm_num
  rw [slotW]

theorem inTree_tW {u : NTree SkelX} (h : InTree tW u) : u = tW := by
  cases h with
  | here => rfl
  | sub hs _ => simp [tW] at hs

theorem leaves_deep : ∀ k, (deep k).leaves = k + 1
  | 0 => rfl
  | k + 1 => by simp [deep, Noun.leaves, leaves_deep k]

/-- `hax` holds (the only formula atom is the op-0 axis `2^62 < p`). -/
theorem axW {p : ℕ} (hp : 2 ^ 62 < p) : ComplJ8.ProgAxOK p tW := by
  intro u hu
  rw [inTree_tW hu]
  simp [ComplJ8.AxRowX, rowOfSkelX, tW, fW, tlN]
  norm_num at hp ⊢
  exact hp

/-- `hop5` holds (no op-5 row). -/
theorem op5W (p : ℕ) : ComplJ8.ProgOp5OK p tW := by
  intro u hu
  rw [inTree_tW hu]
  simp [ComplJ8.Op5RowX, rowOfSkelX, tW]

/-- `hleaf` (phase A form) holds: every handle noun has at most `63` leaves. -/
theorem leafW : ComplJ8.ProgLeafOK tW := by
  intro u hu k hk
  rw [inTree_tW hu]
  have h63 : (deep 62).leaves = 63 := leaves_deep 62
  interval_cases k <;> simp [HonestCompX.hN, rowOfSkelX, tW, sW, fW, tlN, hdN, h63, Noun.leaves]

/-- The claim nouns have at most `63` leaves (the demand-root form of `hleaf` on the claim). -/
theorem claimLeafW : ComplJ8Walk.RootsLeafOK [sW, fW, Noun.atom 0] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp [sW, fW, leaves_deep, Noun.leaves]

/-- **`hwalk` FAILS**: the run's only path read `(sW, 2^62)` has depth `62 > 61`. -/
theorem not_walkW : ¬ ComplJ8Walk.WalkDepthOK (Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT tW)) := by
  intro h
  have hmem : (sW, 2 ^ 62) ∈ pathReads (Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT tW)) := by
    have hr : ComplJ8Data.rowsOfT tW = #[rowOfSkelX tW.label] := by
      simp [ComplJ8Data.rowsOfT, tW, bfsForest]
    rw [hr]
    have hp : isPathAx 4611686018427387904 = true := by
      have h62 := depthOf_pow 62
      norm_num at h62
      simp [isPathAx, h62]
    simp [Nock.V1J8.Gen.pathReads, consEntriesX, rowOfSkelX, tW, fW, tlN, atomVal, pathReads, hp]
  have := h _ hmem
  rw [depthOf_pow] at this
  omega

/-! ## NC 1: `hleaf` is not implied (a formula of size `O(k)` doubling the subject `k` times) -/

/-- The doubling formula `[[0 1] [0 1]]`. -/
def dD : Noun := .cell (.cell (.atom 0) (.atom 1)) (.cell (.atom 0) (.atom 1))

/-- `F 0 = [0 1]`, `F (k+1) = [7 (F k) dD]`. -/
def fD : ℕ → Noun
  | 0 => .cell (.atom 0) (.atom 1)
  | k + 1 => .cell (.atom 7) (.cell (fD k) dD)

/-- `k`-fold doubling. -/
def dbl : ℕ → Noun → Noun
  | 0, x => x
  | k + 1, x => .cell (dbl k x) (dbl k x)

theorem leaves_dbl (x : Noun) : ∀ k, (dbl k x).leaves = 2 ^ k * x.leaves
  | 0 => by simp [dbl]
  | k + 1 => by simp only [dbl, Noun.leaves, leaves_dbl x k]; ring

/-- Every atom of a noun is `< B`. -/
def AtomsLt (B : ℕ) : Noun → Prop
  | .atom v => v < B
  | .cell a b => AtomsLt B a ∧ AtomsLt B b

theorem atoms_fD : ∀ k, AtomsLt 8 (fD k)
  | 0 => by simp [fD, AtomsLt]
  | k + 1 => ⟨by simp [AtomsLt], atoms_fD k, by simp [dD, AtomsLt]⟩

theorem atoms_dbl (B : ℕ) (x : Noun) (hx : AtomsLt B x) : ∀ k, AtomsLt B (dbl k x)
  | 0 => hx
  | k + 1 => ⟨atoms_dbl B x hx k, atoms_dbl B x hx k⟩

theorem eval_fD (x : Noun) : ∀ k fuel, k + 2 ≤ fuel → evalN fuel x (fD k) = some (dbl k x)
  | 0, fuel, h => by
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    simp [evalN, fD, dbl, Noun.slot]
  | k + 1, fuel, h => by
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [evalN, fD]
    rw [show evalN (m' + 1) x (fD k) = some (dbl k x) from eval_fD x k (m' + 1) (by omega)]
    obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
    simp [evalN, dD, dbl, Noun.slot]

/-- The generated tree of `F k`. -/
def tD0 (x : Noun) : NTree SkelX := mkX .s0 x (.cell (.atom 0) (.atom 1)) x []
def tDD (x : Noun) : NTree SkelX := mkX .cons x dD (.cell x x) [tD0 x, tD0 x]
def tF (x : Noun) : ℕ → NTree SkelX
  | 0 => tD0 x
  | k + 1 => mkX .s7 x (fD (k + 1)) (dbl (k + 1) x) [tDD (dbl k x), tF x k]

theorem gen_fD (R : Nock.Jet.Registry) (x : Noun) : ∀ k fuel, k + 2 ≤ fuel →
    genX R fuel x (fD k) = some (tF x k, dbl k x)
  | 0, fuel, h => by
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    simp [genX, genComputeSkeletonX, fD, tF, tD0, dbl, Noun.slot]
  | k + 1, fuel, h => by
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have ih := gen_fD R x k (m' + 1) (by omega)
    simp only [genX] at ih ⊢
    simp only [genComputeSkeletonX, fD]
    rw [ih]
    obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
    simp [genComputeSkeletonX, dD, tF, tDD, tD0, dbl, Noun.slot, fD]

/-- Every row of `tF x k` is an op-0 row at axis `1`, a `cons` row or an op-7 row. -/
def RowKind (sk : SkelX) : Prop :=
  (sk.state = .s0 ∧ sk.formula = .cell (.atom 0) (.atom 1)) ∨ sk.state = .cons ∨ sk.state = .s7

theorem inTree_mkX {st : Nock.Edit.StateX} {s f e : Noun} {ks : List (NTree SkelX)} {u : NTree SkelX}
    (h : InTree (mkX st s f e ks) u) : u = mkX st s f e ks ∨ ∃ c ∈ ks, InTree c u := by
  cases h with
  | here => exact Or.inl rfl
  | sub hs h' => exact Or.inr ⟨_, by simpa using hs, h'⟩

theorem rowKind_tD0 (x : Noun) {u : NTree SkelX} (h : InTree (tD0 x) u) : RowKind u.label := by
  rcases inTree_mkX h with rfl | ⟨c, hc, -⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · simp at hc

theorem rowKind_tDD (x : Noun) {u : NTree SkelX} (h : InTree (tDD x) u) : RowKind u.label := by
  rcases inTree_mkX h with rfl | ⟨c, hc, hu⟩
  · exact Or.inr (Or.inl rfl)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact rowKind_tD0 x hu

theorem rowKind_tF (x : Noun) : ∀ k {u : NTree SkelX}, InTree (tF x k) u → RowKind u.label
  | 0, u, h => rowKind_tD0 x h
  | k + 1, u, h => by
    rcases inTree_mkX h with rfl | ⟨c, hc, hu⟩
    · exact Or.inr (Or.inr rfl)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact rowKind_tDD _ hu
      · exact rowKind_tF x k hu

/-- `hax` holds on the doubling run (its only formula atom at an op-0 row is the axis `1`). -/
theorem axD {p : ℕ} (hp : 2 ≤ p) (x : Noun) (k : ℕ) : ComplJ8.ProgAxOK p (tF x k) := by
  intro u hu
  rcases rowKind_tF x k hu with ⟨h1, h2⟩ | h1 | h1
  · simp [ComplJ8.AxRowX, rowOfSkelX, h1, h2, tlN]; omega
  · simp [ComplJ8.AxRowX, rowOfSkelX, h1]
  · simp [ComplJ8.AxRowX, rowOfSkelX, h1]

/-- `hop5` holds (no op-5 row). -/
theorem op5D (p : ℕ) (x : Noun) (k : ℕ) : ComplJ8.ProgOp5OK p (tF x k) := by
  intro u hu
  rcases rowKind_tF x k hu with ⟨h1, -⟩ | h1 | h1 <;> simp [ComplJ8.Op5RowX, rowOfSkelX, h1]

/-- `hwalk` holds (no path read: every op-0 axis is `1`). -/
theorem walkD (x : Noun) (k : ℕ) :
    ComplJ8Walk.WalkDepthOK (Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT (tF x k))) := by
  have hnil : Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT (tF x k)) = [] := by
    simp only [Nock.V1J8.Gen.pathReads, List.filter_eq_nil_iff]
    intro r hr
    simp only [ComplJ8Data.rowsOfT, List.toList_toArray, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨row, ⟨u, hu, rfl⟩, he⟩ := hr
    obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ u).mp hu
    simp only [List.mem_singleton] at hc
    subst hc
    rcases rowKind_tF x k hcu with ⟨h1, h2⟩ | h1 | h1
    · simp [consEntriesX, rowOfSkelX, h1, h2, tlN] at he
    · simp [consEntriesX, rowOfSkelX, h1] at he
    · simp [consEntriesX, rowOfSkelX, h1] at he
  rw [hnil]
  intro r hr
  simp [pathReads] at hr

theorem hN_tF (x : Noun) (k : ℕ) : HonestCompX.hN (rowOfSkelX (tF x (k + 1)).label) 2 = dbl (k + 1) x := rfl

/-- **NC 1: `hleaf` is not implied.**  The run `*[0 F 110] = dbl 110 0` (fuel `112`): every atom is `< 8`,
`hax`, `hop5` and `hwalk` hold on its generated tree, and the result (a claim noun, row `0`'s evaluation) has
`2^110 > 2^109` leaves, so both the phase-A `ProgLeafOK` and `RootsLeafOK` on the claim fail. -/
theorem hleaf_not_implied :
    evalN 112 (.atom 0) (fD 110) = some (dbl 110 (.atom 0)) ∧
    genX Nock.Jet.VerifiedRegistry.empty.R 112 (.atom 0) (fD 110) = some (tF (.atom 0) 110, dbl 110 (.atom 0)) ∧
    AtomsLt 8 (.atom 0) ∧ AtomsLt 8 (fD 110) ∧ AtomsLt 8 (dbl 110 (.atom 0)) ∧
    ComplJ8.ProgAxOK Nock.Atoms.p (tF (.atom 0) 110) ∧ ComplJ8.ProgOp5OK Nock.Atoms.p (tF (.atom 0) 110) ∧
    ComplJ8Walk.WalkDepthOK (Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT (tF (.atom 0) 110))) ∧
    (dbl 110 (.atom 0)).leaves = 2 ^ 110 ∧
    ¬ ComplJ8.ProgLeafOK (tF (.atom 0) 110) ∧
    ¬ ComplJ8Walk.RootsLeafOK [.atom 0, fD 110, dbl 110 (.atom 0)] := by
  have hl : (dbl 110 (.atom 0)).leaves = 2 ^ 110 := by rw [leaves_dbl]; simp [Noun.leaves]
  have hp2 : 2 ≤ Nock.Atoms.p := by simp [Nock.Atoms.p, Nock.Field.p]
  refine ⟨eval_fD _ 110 112 (by omega), gen_fD _ _ 110 112 (by omega), by simp [AtomsLt], atoms_fD 110,
    atoms_dbl 8 _ (by simp [AtomsLt]) 110, axD hp2 _ 110, op5D _ _ 110,
    walkD _ 110, hl, ?_, ?_⟩
  · intro h
    have := h (tF (.atom 0) 110) (InTree.here _) 2 (by norm_num)
    rw [hN_tF (.atom 0) 109, hl] at this
    norm_num at this
  · intro h
    have := h (dbl 110 (.atom 0)) (by simp)
    rw [hl] at this
    norm_num at this

/-- **NC 2: `hwalk` is not implied.**  The run `*[sW [0 2^62]] = 0` (`sW` the left spine of depth `62`, fuel `1`):
every atom is `< p` (Goldilocks), `hax` (axis `2^62 < p`), `hop5` and `hleaf` (both forms) hold on its generated
tree, and `WalkDepthOK` fails on its reads (the read `(sW, 2^62)` has depth `62 > 61`). -/
theorem hwalk_not_implied :
    evalN 1 sW fW = some (Noun.atom 0) ∧
    genX Nock.Jet.VerifiedRegistry.empty.R 1 sW fW = some (tW, Noun.atom 0) ∧
    AtomsLt Nock.Atoms.p sW ∧ AtomsLt Nock.Atoms.p fW ∧ AtomsLt Nock.Atoms.p (Noun.atom 0) ∧
    ComplJ8.ProgAxOK Nock.Atoms.p tW ∧ ComplJ8.ProgOp5OK Nock.Atoms.p tW ∧ ComplJ8.ProgLeafOK tW ∧
    ComplJ8Walk.RootsLeafOK [sW, fW, Noun.atom 0] ∧
    ¬ ComplJ8Walk.WalkDepthOK (Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT tW)) := by
  have hp : 2 ^ 62 < Nock.Atoms.p := by simp [Nock.Atoms.p, Nock.Field.p]
  have hdeep : ∀ k, AtomsLt Nock.Atoms.p (deep k) := by
    intro k; induction k with
    | zero => simp [deep, AtomsLt]; omega
    | succ k ih => exact ⟨ih, by simp [AtomsLt]; omega⟩
  exact ⟨runW, genW _, hdeep 62, ⟨by simp [AtomsLt]; omega, hp⟩, by simp [AtomsLt]; omega, axW hp, op5W _,
    leafW, claimLeafW, not_walkW⟩

#print axioms hwalk_not_implied
#print axioms hleaf_not_implied
end Nock.RedTeam.Batch4833NC
