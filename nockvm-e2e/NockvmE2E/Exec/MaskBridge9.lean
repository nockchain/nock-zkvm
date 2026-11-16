/-
the J-9 A twin of `Exec/MaskBridge.lean`.  For the seven non-jet tables of `preJ9`
(`J9A/InstJ9A.lean`) incl. the three new chips (compute9: masks at columns 17/18, axis and split: columns 0/1, endpoint masks
only, numeral 0), the fixed columns `preJ9 d (colI9 s c)` are `Msk pos nodes hn kr` at the `preIdx9` positions (`preJ9_s*`),
and a passing executed `maskCol` check identifies the loaded column with it (`lagr9_*`: `preJ9 d (colI9 s c) = some (polyOfArr arr)`,
equivalently the monomial sum by `MaskBridge.polyOfArr_sum`).  The executed shape facts (node injectivity, canon columns) are
hypotheses here, discharged by the generic `ExecInst` shape lemmas at the instance; the jet's registry columns stay TCB.
-/
import NockvmE2E.Exec.MaskBridge
import NockvmE2E.Exec.J9AChipsFam
import NockvmE2E.J9A.TieJ9A

set_option autoImplicit false

namespace NockvmE2E.Exec.MaskBridge9
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VF NockvmE2E.Exec.VL NockvmE2E.Exec.MaskOk NockvmE2E.Exec.MaskOkK
open NockvmE2E.Exec.MaskBridge Polynomial
open Nock.Framework Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open NockvmE2E.J8.InstJ8 (preOf preOf_col ω0)
open NockvmE2E.J9A.InstJ9A
open NockvmE2E.J9A.TieJ9A (colI9)

/-- the new chips' fixed-column positions (the executed `preIdx9`) -/
theorem preIdx9_compute : NockvmE2E.Exec.J9AChips.preIdx9 "computeChipVCLHX9" = #[17, 18] := by decide +kernel
theorem preIdx9_axis : NockvmE2E.Exec.J9AChips.preIdx9 "axisChipJ9" = #[0, 1] := by decide +kernel
theorem preIdx9_split : NockvmE2E.Exec.J9AChips.preIdx9 "splitChipJ9" = #[0, 1] := by decide +kernel

/-- a passing mask column is the mask over the instance's nodes (injectivity of the node powers as a hypothesis) -/
theorem polyOfArr_Msk9 (XI : ExecInst) (n : ℕ) (hinj : Function.Injective (fun i : Fin n => zv XI.hGen ^ (i : ℕ)))
    (arr : Array G) (harr : ∀ c ∈ arr.toList, canon c) (pos : ℕ) (nodes : Fin n → ZMod NockvmE2E.J8.InstJ8.P) (hn0 : 0 < n)
    (hnodes : ∀ i, nodes i = ω0 XI ^ (i : ℕ)) (kr k : ℕ) (hm : maskCol XI n pos arr = some k)
    (hk : 2 ≤ pos → kr = k) : polyOfArr arr = Msk pos nodes hn0 kr := by
  have hnodes' : nodes = fun i : Fin n => zv XI.hGen ^ (i : ℕ) := funext hnodes
  subst hnodes'
  obtain ⟨h0, h1, h2⟩ := maskCol_sound' XI n pos hn0 hinj arr harr k hm
  unfold Msk
  by_cases p0 : pos = 0
  · rw [if_pos p0]; exact h0 p0
  by_cases p1 : pos = 1
  · rw [if_neg p0, if_pos p1]; exact h1 p1
  rw [if_neg p0, if_neg p1, hk (by omega)]
  exact (h2 (by omega)).2

theorem preJ9_s0 (d : Datum9A) (c pos : ℕ) (h : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "computeChipVCLHX9").toList.zipIdx) :
    preJ9 d (colI9 0 c) = some (Msk pos d.Pb.nodes d.Pb.hn 0) := by
  simp [preIdx9_compute] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 2; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 2; omega⟩ rfl]; simp [Msk]; rfl

/-- the loaded mask column of table 0 (comp) is its fixed column -/
theorem lagr9_comp (d : Datum9A) (XI : ExecInst) (c pos : ℕ) (hpos : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "computeChipVCLHX9").toList.zipIdx)
    (hinj : Function.Injective (fun i : Fin d.Pb.n => zv XI.hGen ^ (i : ℕ))) (hn0 : 0 < d.Pb.n)
    (hnodes : ∀ i, d.Pb.nodes i = ω0 XI ^ (i : ℕ)) (arr : Array G) (harr : ∀ x ∈ arr.toList, canon x) (k : ℕ)
    (hm : maskCol XI d.Pb.n pos arr = some k) (hk : 2 ≤ pos → 0 = k) :
    preJ9 d (colI9 0 c) = some (polyOfArr arr) := by
  rw [preJ9_s0 d c pos hpos]
  congr 1
  exact (polyOfArr_Msk9 XI _ hinj arr harr pos _ hn0 hnodes _ k hm hk).symm

theorem preJ9_s1 (d : Datum9A) (c pos : ℕ) (h : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "cellChipHQKW").toList.zipIdx) :
    preJ9 d (colI9 1 c) = some (Msk pos d.Pb.nodesC d.Pb.hnC 0) := by
  simp [NockvmE2E.Exec.J9AChips.preIdx9, J8Shape.preIdxJ8] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 2; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 2; omega⟩ rfl]; simp [Msk]; rfl

/-- the loaded mask column of table 1 (cell) is its fixed column -/
theorem lagr9_cell (d : Datum9A) (XI : ExecInst) (c pos : ℕ) (hpos : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "cellChipHQKW").toList.zipIdx)
    (hinj : Function.Injective (fun i : Fin d.Pb.nC => zv XI.hGen ^ (i : ℕ))) (hn0 : 0 < d.Pb.nC)
    (hnodes : ∀ i, d.Pb.nodesC i = ω0 XI ^ (i : ℕ)) (arr : Array G) (harr : ∀ x ∈ arr.toList, canon x) (k : ℕ)
    (hm : maskCol XI d.Pb.nC pos arr = some k) (hk : 2 ≤ pos → 0 = k) :
    preJ9 d (colI9 1 c) = some (polyOfArr arr) := by
  rw [preJ9_s1 d c pos hpos]
  congr 1
  exact (polyOfArr_Msk9 XI _ hinj arr harr pos _ hn0 hnodes _ k hm hk).symm

theorem preJ9_s2 (d : Datum9A) (c pos : ℕ) (h : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "walkChipJ8").toList.zipIdx) :
    preJ9 d (colI9 2 c) = some (Msk pos d.Pb.nodesW d.Pb.hnW d.Pb.kroots) := by
  simp [NockvmE2E.Exec.J9AChips.preIdx9, J8Shape.preIdxJ8] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 3; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 3; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨2, by show 2 < 3; omega⟩ rfl]; simp [Msk]; rfl

/-- the loaded mask column of table 2 (walk) is its fixed column -/
theorem lagr9_walk (d : Datum9A) (XI : ExecInst) (c pos : ℕ) (hpos : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "walkChipJ8").toList.zipIdx)
    (hinj : Function.Injective (fun i : Fin d.Pb.nW => zv XI.hGen ^ (i : ℕ))) (hn0 : 0 < d.Pb.nW)
    (hnodes : ∀ i, d.Pb.nodesW i = ω0 XI ^ (i : ℕ)) (arr : Array G) (harr : ∀ x ∈ arr.toList, canon x) (k : ℕ)
    (hm : maskCol XI d.Pb.nW pos arr = some k) (hk : 2 ≤ pos → d.Pb.kroots = k) :
    preJ9 d (colI9 2 c) = some (polyOfArr arr) := by
  rw [preJ9_s2 d c pos hpos]
  congr 1
  exact (polyOfArr_Msk9 XI _ hinj arr harr pos _ hn0 hnodes _ k hm hk).symm

theorem preJ9_s4 (d : Datum9A) (c pos : ℕ) (h : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "atomChipHQL").toList.zipIdx) :
    preJ9 d (colI9 4 c) = some (Msk pos d.Pb.nodesA d.Pb.hnA 0) := by
  simp [NockvmE2E.Exec.J9AChips.preIdx9, J8Shape.preIdxJ8] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 2; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 2; omega⟩ rfl]; simp [Msk]; rfl

/-- the loaded mask column of table 4 (atom) is its fixed column -/
theorem lagr9_atom (d : Datum9A) (XI : ExecInst) (c pos : ℕ) (hpos : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "atomChipHQL").toList.zipIdx)
    (hinj : Function.Injective (fun i : Fin d.Pb.nA => zv XI.hGen ^ (i : ℕ))) (hn0 : 0 < d.Pb.nA)
    (hnodes : ∀ i, d.Pb.nodesA i = ω0 XI ^ (i : ℕ)) (arr : Array G) (harr : ∀ x ∈ arr.toList, canon x) (k : ℕ)
    (hm : maskCol XI d.Pb.nA pos arr = some k) (hk : 2 ≤ pos → 0 = k) :
    preJ9 d (colI9 4 c) = some (polyOfArr arr) := by
  rw [preJ9_s4 d c pos hpos]
  congr 1
  exact (polyOfArr_Msk9 XI _ hinj arr harr pos _ hn0 hnodes _ k hm hk).symm

theorem preJ9_s5 (d : Datum9A) (c pos : ℕ) (h : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "walkChipHQK").toList.zipIdx) :
    preJ9 d (colI9 5 c) = some (Msk pos d.Pb.nodesV d.Pb.hnV d.Pb.krootsV) := by
  simp [NockvmE2E.Exec.J9AChips.preIdx9, J8Shape.preIdxJ8] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 3; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 3; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨2, by show 2 < 3; omega⟩ rfl]; simp [Msk]; rfl

/-- the loaded mask column of table 5 (walkV) is its fixed column -/
theorem lagr9_walkV (d : Datum9A) (XI : ExecInst) (c pos : ℕ) (hpos : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "walkChipHQK").toList.zipIdx)
    (hinj : Function.Injective (fun i : Fin d.Pb.nV => zv XI.hGen ^ (i : ℕ))) (hn0 : 0 < d.Pb.nV)
    (hnodes : ∀ i, d.Pb.nodesV i = ω0 XI ^ (i : ℕ)) (arr : Array G) (harr : ∀ x ∈ arr.toList, canon x) (k : ℕ)
    (hm : maskCol XI d.Pb.nV pos arr = some k) (hk : 2 ≤ pos → d.Pb.krootsV = k) :
    preJ9 d (colI9 5 c) = some (polyOfArr arr) := by
  rw [preJ9_s5 d c pos hpos]
  congr 1
  exact (polyOfArr_Msk9 XI _ hinj arr harr pos _ hn0 hnodes _ k hm hk).symm

theorem preJ9_s6 (d : Datum9A) (c pos : ℕ) (h : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "axisChipJ9").toList.zipIdx) :
    preJ9 d (colI9 6 c) = some (Msk pos d.Pb.nodesX d.Pb.hnX 0) := by
  simp [preIdx9_axis] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 2; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 2; omega⟩ rfl]; simp [Msk]; rfl

/-- the loaded mask column of table 6 (axis) is its fixed column -/
theorem lagr9_axis (d : Datum9A) (XI : ExecInst) (c pos : ℕ) (hpos : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "axisChipJ9").toList.zipIdx)
    (hinj : Function.Injective (fun i : Fin d.Pb.nX => zv XI.hGen ^ (i : ℕ))) (hn0 : 0 < d.Pb.nX)
    (hnodes : ∀ i, d.Pb.nodesX i = ω0 XI ^ (i : ℕ)) (arr : Array G) (harr : ∀ x ∈ arr.toList, canon x) (k : ℕ)
    (hm : maskCol XI d.Pb.nX pos arr = some k) (hk : 2 ≤ pos → 0 = k) :
    preJ9 d (colI9 6 c) = some (polyOfArr arr) := by
  rw [preJ9_s6 d c pos hpos]
  congr 1
  exact (polyOfArr_Msk9 XI _ hinj arr harr pos _ hn0 hnodes _ k hm hk).symm

theorem preJ9_s7 (d : Datum9A) (c pos : ℕ) (h : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "splitChipJ9").toList.zipIdx) :
    preJ9 d (colI9 7 c) = some (Msk pos d.Pb.nodesS d.Pb.hnS 0) := by
  simp [preIdx9_split] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨0, by show 0 < 2; omega⟩ rfl]; simp [Msk]; rfl
  · show preOf _ _ = _
    rw [preOf_of_idx _ _ ⟨1, by show 1 < 2; omega⟩ rfl]; simp [Msk]; rfl

/-- the loaded mask column of table 7 (split) is its fixed column -/
theorem lagr9_split (d : Datum9A) (XI : ExecInst) (c pos : ℕ) (hpos : (c, pos) ∈ (NockvmE2E.Exec.J9AChips.preIdx9 "splitChipJ9").toList.zipIdx)
    (hinj : Function.Injective (fun i : Fin d.Pb.nS => zv XI.hGen ^ (i : ℕ))) (hn0 : 0 < d.Pb.nS)
    (hnodes : ∀ i, d.Pb.nodesS i = ω0 XI ^ (i : ℕ)) (arr : Array G) (harr : ∀ x ∈ arr.toList, canon x) (k : ℕ)
    (hm : maskCol XI d.Pb.nS pos arr = some k) (hk : 2 ≤ pos → 0 = k) :
    preJ9 d (colI9 7 c) = some (polyOfArr arr) := by
  rw [preJ9_s7 d c pos hpos]
  congr 1
  exact (polyOfArr_Msk9 XI _ hinj arr harr pos _ hn0 hnodes _ k hm hk).symm

end NockvmE2E.Exec.MaskBridge9

#print axioms NockvmE2E.Exec.MaskBridge9.polyOfArr_Msk9
#print axioms NockvmE2E.Exec.MaskBridge9.preJ9_s0
#print axioms NockvmE2E.Exec.MaskBridge9.preJ9_s6
#print axioms NockvmE2E.Exec.MaskBridge9.preJ9_s7
#print axioms NockvmE2E.Exec.MaskBridge9.lagr9_comp
#print axioms NockvmE2E.Exec.MaskBridge9.lagr9_axis
#print axioms NockvmE2E.Exec.MaskBridge9.lagr9_split
