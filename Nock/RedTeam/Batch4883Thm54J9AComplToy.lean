/-
  Nock/RedTeam/Batch4883Thm54J9AComplToy.lean

  **J-9 A general completeness (L7 C8): non-vacuity of `complJ9A_closed` with BOTH new chips on.**  The run
  `*[sA [[0 AB] [0 AF]]]` (Goldilocks, `K = KC`, `δ = deltaF`, `b = powerBasis3`, the empty registry) with
  `sA = rsp 63` the right spine of depth 63, the BIG axis `AB = 2^64 - 1` (two limbs, `≥ p`, served by the axis
  chip through the atom table) and the FIELD axis `AF = 2^63 - 1` (`2^62 ≤ AF < p`, served by the split chip).
  Every binder of `complJ9A_closed` (`hpG hax9 hop5 hleaf hwalk9 hwalkA hRt hregAx h31A` and the run `hgen`) is a
  closed lemma below; `complJ9A_toy` concludes `axOnA t = true ∧ spOnA p t = true ∧ ε_c < 2^-120 ∧ ∃ χ, AcceptsJ9A …`.

  Design (no kernel evaluation of `Noun.slot`, `Nat.digits` or `Nat.log` on the deep / big data):
  * `slot_rsp`: `slot (2^(k+1) - 1) (rsp n) = rsp (n - k)` by induction (`slot_double_succ`); the run `genA` is
    `genX`'s equations plus the two slot facts.
  * limbs / `top` of the two axes by `Nat.digits_def'` / `Nat.log_eq_of_pow_le_of_lt_pow`.
  * the row sizes are bounds (`cellsOfRoots` by a cell count, the walk rows by `walkRows_length_le` with every read
    axis `< 2^62`), never the exact tables.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AClosed
import Nock.RedTeam.Batch4856Thm54J9BComplToy

set_option autoImplicit false

namespace Nock.RedTeam.Batch4883

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.RedTeam.Batch4842 (RtT factRC charPKC algRC card_KC)

/-! ## 1. The subject and the slot facts -/

/-- The right spine of depth `n`. -/
def rsp : ℕ → Noun
  | 0 => .atom 0
  | n + 1 => .cell (.atom 0) (rsp n)

theorem slot_rsp : ∀ (k n : ℕ), k ≤ n → Noun.slot (2 ^ (k + 1) - 1) (rsp n) = some (rsp (n - k))
  | 0, n, _ => by simp [Noun.slot]
  | k + 1, n, h => by
    have he : 2 ^ (k + 1 + 1) - 1 = 2 * (2 ^ (k + 1) - 1) + 1 := by
      have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      rw [pow_succ]; omega
    rw [he, Nock.GlobalCarryAxis.slot_double_succ _ (Nat.one_le_iff_ne_zero.mpr (by
      have : 2 ≤ 2 ^ (k + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)), slot_rsp k n (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
    rw [hm]
    simp [rsp, Nock.GlobalCarryAxis.tailOpt]
    congr 1; omega

/-- The subject. -/
def sA : Noun := rsp 63
/-- The big axis (two limbs, `≥ p`). -/
def AB : ℕ := 2 ^ 64 - 1
/-- The field axis (`2^62 ≤ AF < p`). -/
def AF : ℕ := 2 ^ 63 - 1
/-- The formula `[[0 AB] [0 AF]]`. -/
def fA : Noun := .cell (.cell (.atom 0) (.atom AB)) (.cell (.atom 0) (.atom AF))
/-- The result. -/
def rA : Noun := .cell (rsp 0) (rsp 1)

theorem slotB : Noun.slot AB sA = some (rsp 0) := by
  have := slot_rsp 63 63 le_rfl
  simpa [AB, sA] using this

theorem slotF : Noun.slot AF sA = some (rsp 1) := by
  have := slot_rsp 62 63 (by norm_num)
  simpa [AF, sA] using this

/-! ## 2. The run -/

/-- The two op-0 children and the tree. -/
def kB : NTree SkelX := mkX .s0 sA (.cell (.atom 0) (.atom AB)) (rsp 0) []
def kF : NTree SkelX := mkX .s0 sA (.cell (.atom 0) (.atom AF)) (rsp 1) []
def tA : NTree SkelX := mkX .cons sA fA rA [kB, kF]

theorem genA : genX Nock.Jet.VerifiedRegistry.empty.R 2 sA fA = some (tA, rA) := by
  simp only [genX, fA, genComputeSkeletonX, slotB, slotF]
  rfl


/-! ## 3. Limbs and `top` of the two axes -/

theorem limbsB : Nock.Atoms.limbs AB = [2 ^ 32 - 1, 2 ^ 32 - 1] := by
  unfold Nock.Atoms.limbs Nock.Atoms.B AB
  rw [Nat.digits_def' (by norm_num) (by norm_num), Nat.digits_def' (by norm_num) (by norm_num)]
  norm_num

theorem limbsF : Nock.Atoms.limbs AF = [2 ^ 32 - 1, 2 ^ 31 - 1] := by
  unfold Nock.Atoms.limbs Nock.Atoms.B AF
  rw [Nat.digits_def' (by norm_num) (by norm_num), Nat.digits_def' (by norm_num) (by norm_num)]
  norm_num

theorem topB : Nock.J9A.NounAx.top AB = 1 := by
  have h := Nock.J9A.NounAx.top_eq_length AB (by simp [AB])
  rw [limbsB] at h; simp at h; omega

theorem topF : Nock.J9A.NounAx.top AF = 1 := by
  have h := Nock.J9A.NounAx.top_eq_length AF (by simp [AF])
  rw [limbsF] at h; simp at h; omega

theorem capB : ComplJ9ABinders.AxCap AB := by
  unfold ComplJ9ABinders.AxCap; rw [limbsB]; simp

theorem pB : Nock.Field.p ≤ AB := by simp [AB, Nock.Field.p]
theorem pF : AF < Nock.Field.p := by simp [AF, Nock.Field.p]

/-! ## 4. The rows (J-8 and J-9 A) -/

theorem bfsA : bfsForest [tA] = [tA, kB, kF] := by simp [bfsForest, tA, kB, kF, mkX]

theorem rowsA : ComplJ8Data.rowsOfT tA =
    #[rowOfSkelX tA.label, rowOfSkelX kB.label, rowOfSkelX kF.label] := by
  simp only [ComplJ8Data.rowsOfT, bfsA]; rfl

theorem inTree_tA (u : NTree SkelX) (h : InTree tA u) : u = tA ∨ u = kB ∨ u = kF := by
  have : u ∈ bfsForest [tA] := (mem_bfsForest [tA] u).2 ⟨tA, by simp, h⟩
  rw [bfsA] at this; simpa using this

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 genX9T rowsOfT9 rowX9) in
/-- The J-9 A tree: the cons row stays `old`, both op-0 rows are `s0B` at their axes. -/
def gT9 : NTree LX9 :=
  .node ⟨rowX9 tA.label, .old, 0, 0, rowOfSkelX tA.label⟩
    [.node ⟨rowX9 kB.label, .s0B, AB, 0, rowOfSkelX kB.label⟩ [],
     .node ⟨rowX9 kF.label, .s0B, AF, 0, rowOfSkelX kF.label⟩ []]

theorem chipB : ComplJ9AGen.chipOf kB.label = (.s0B, AB) := by decide
theorem chipF : ComplJ9AGen.chipOf kF.label = (.s0B, AF) := by decide
theorem chipC : ComplJ9AGen.chipOf tA.label = (.old, 0) := rfl

theorem genX9T_A : ComplJ9AGen.genX9T tA = gT9 := by
  have hB : ComplJ9AGen.genX9T kB = .node ⟨ComplJ9AGen.rowX9 kB.label, .s0B, AB, 0, rowOfSkelX kB.label⟩ [] := by
    show ComplJ9AGen.genX9T (.node kB.label []) = _
    rw [ComplJ9AGen.genX9T_node, chipB]; rfl
  have hF : ComplJ9AGen.genX9T kF = .node ⟨ComplJ9AGen.rowX9 kF.label, .s0B, AF, 0, rowOfSkelX kF.label⟩ [] := by
    show ComplJ9AGen.genX9T (.node kF.label []) = _
    rw [ComplJ9AGen.genX9T_node, chipF]; rfl
  show ComplJ9AGen.genX9T (.node tA.label [kB, kF]) = _
  rw [ComplJ9AGen.genX9T_node, chipC]
  simp only [List.map_cons, List.map_nil, hB, hF, ComplJ9AGen.kid9, chipC, gT9]
  simp

theorem bfs9A : bfsForest [gT9] = [gT9, .node ⟨ComplJ9AGen.rowX9 kB.label, .s0B, AB, 0, rowOfSkelX kB.label⟩ [],
    .node ⟨ComplJ9AGen.rowX9 kF.label, .s0B, AF, 0, rowOfSkelX kF.label⟩ []] := by
  simp [bfsForest, gT9]

theorem rows9A : ComplJ9AGen.rowsOfT9 tA =
    #[⟨ComplJ9AGen.rowX9 tA.label, .old, 0, 0, rowOfSkelX tA.label⟩,
      ⟨ComplJ9AGen.rowX9 kB.label, .s0B, AB, 0, rowOfSkelX kB.label⟩,
      ⟨ComplJ9AGen.rowX9 kF.label, .s0B, AF, 0, rowOfSkelX kF.label⟩] := by
  simp only [ComplJ9AGen.rowsOfT9, genX9T_A, bfs9A]; rfl

theorem keys9A : ComplJ9AChainsRun.axKeys9 (ComplJ9AGen.rowsOfT9 tA) = [(sA, AB), (sA, AF)] := by
  rw [rows9A]; decide

theorem axAtoms9A : ComplJ9AData.axAtoms9 (ComplJ9AGen.rowsOfT9 tA) = [AB, AF] := by
  rw [rows9A]; decide

theorem fieldAx9A : ComplJ9AData.fieldAx9 Nock.Field.p (ComplJ9AGen.rowsOfT9 tA) = [AF] := by
  unfold ComplJ9AData.fieldAx9; rw [axAtoms9A]; simp [pF, Nat.not_lt.mpr pB]

theorem axOnA_tA : ComplJ9ARun.axOnA tA = true := by
  simp [ComplJ9ARun.axOnA, keys9A]

theorem spOnA_tA : ComplJ9ARun.spOnA Nock.Field.p tA = true := by
  simp [ComplJ9ARun.spOnA, fieldAx9A]


/-! ## 5. The data and the binders -/

noncomputable section

abbrev DD := j8DataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty RtT genA
abbrev DA := ComplJ9ADataRec.j9aDataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty RtT genA

abbrev rowsL : Array RowNX := #[rowOfSkelX tA.label, rowOfSkelX kB.label, rowOfSkelX kF.label]

theorem hcallsA : Nock.V1J8.Gen.callsOf rowsL = [] := by decide

theorem callsA : DD.calls = [] := by
  show Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT tA) = []
  rw [rowsA]; exact hcallsA

theorem rootsA : DD.roots = Nock.V1J8.Gen.rootsOf ⟨sA, fA, rA⟩ rowsL := by
  show Nock.V1J8.Gen.rootsOf _ (ComplJ8Data.rowsOfT tA) ++ _ = _
  rw [rowsA]
  simp only [ComplJ8Data.jNounsP, hcallsA]
  simp

theorem hleafA : ComplJ8Walk.RootsLeafOK DD.roots := by
  rw [rootsA]
  show ∀ x ∈ Nock.V1J8.Gen.rootsOf ⟨sA, fA, rA⟩ rowsL, x.leaves ≤ 2 ^ 109
  decide

theorem walkReads9A : ComplJ9ABinders.walkReads9 rowsL = [] := by decide

theorem hwalk9A : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT tA) := by
  show ComplJ8Walk.WalkDepthOK (ComplJ9ABinders.walkReads9 _)
  rw [rowsA, walkReads9A]; intro r hr; simp [VclL.pathReads] at hr

theorem preadsA : DD.preads = [] := by
  show ComplJ8Data.pairReadsP _ _ (ComplJ8Data.rowsOfT tA) = []
  rw [rowsA]
  simp [ComplJ8Data.pairReadsP, Nock.V1J8.FillX.isPairB, rowOfSkelX, tA, kB, kF, mkX]

theorem hwalkAA : ComplJ8Walk.WalkDepthOK DD.preads := by
  rw [preadsA]; intro r hr; simp [VclL.pathReads] at hr

theorem jrowsA : DD.jrows = [] := by
  show ComplJ8Data.mvFixP _ (Nock.Jet.ChipJ8.honestJ8G _ _ (List.map Prod.fst DD.calls).dedup DD.calls) _ = []
  rw [callsA]; rfl

theorem hax9A : ComplJ9ABinders.ProgAxOK9A Nock.Field.p tA := by
  intro u hu
  rcases inTree_tA u hu with rfl | rfl | rfl
  · simp [ComplJ9ABinders.AxRowX9A, rowOfSkelX, tA, mkX]
  · simp only [ComplJ9ABinders.AxRowX9A, rowOfSkelX, kB, mkX]
    intro ax h
    simp [VclL.tlN] at h; subst h; exact Or.inr capB
  · simp only [ComplJ9ABinders.AxRowX9A, rowOfSkelX, kF, mkX]
    intro ax h
    simp [VclL.tlN] at h; subst h; exact Or.inl pF

theorem hop5A : ComplJ8.ProgOp5OK Nock.Field.p tA := by
  intro u hu
  rcases inTree_tA u hu with rfl | rfl | rfl <;> intro h <;> simp [rowOfSkelX, tA, kB, kF, mkX] at h

theorem calledA : ∀ id, id ∉ ComplJ8Jet.CalledIds tA := by
  rintro id ⟨u, hu, hst, -⟩
  rcases inTree_tA u hu with rfl | rfl | rfl <;> simp [rowOfSkelX, tA, kB, kF, mkX] at hst

/-! ## 6. The sizes (bounds) -/

/-- The number of cell nodes of a noun. -/
def ncell : Noun → ℕ
  | .atom _ => 0
  | .cell a b => ncell a + ncell b + 1

theorem addCells_len : ∀ (n : Noun) (acc : List Noun),
    (Nock.V1J8.Gen.addCells n acc).length ≤ acc.length + ncell n
  | .atom _, acc => by simp [Nock.V1J8.Gen.addCells, ncell]
  | .cell a b, acc => by
    unfold Nock.V1J8.Gen.addCells
    split_ifs
    · simp [ncell]
    · have h1 := addCells_len a (acc ++ [.cell a b])
      have h2 := addCells_len b (Nock.V1J8.Gen.addCells a (acc ++ [.cell a b]))
      simp only [List.length_append, List.length_singleton] at h1
      simp only [ncell]; omega

theorem foldl_addCells_len : ∀ (roots acc : List Noun),
    (roots.foldl (fun acc n => Nock.V1J8.Gen.addCells n acc) acc).length ≤ acc.length + (roots.map ncell).sum
  | [], acc => by simp
  | n :: rs, acc => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have h1 := foldl_addCells_len rs (Nock.V1J8.Gen.addCells n acc)
    have h2 := addCells_len n acc
    omega

/-- Generic (so no concrete unfolding): the J-8 cell list is `cellsOfRoots` of the roots. -/
theorem cells_gen {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {Rt : ℕ → Nock.Jet.Autogen.Tpl}
    {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r)) :
    (j8DataOf p Rg Rt hgen).cells = Nock.V1J8.Gen.cellsOfRoots (j8DataOf p Rg Rt hgen).roots := rfl

theorem cellsDD : DD.cells = Nock.V1J8.Gen.cellsOfRoots DD.roots := cells_gen genA

theorem cellsA_len : DA.cells.length ≤ 2 ^ 31 := by
  rw [ComplJ9ADataRec.j9aDataOf_cells, cellsDD]
  have h := foldl_addCells_len DD.roots []
  have h2 : (DD.roots.map ncell).sum ≤ 2 ^ 31 := by
    rw [rootsA]; decide
  simp only [List.length_nil, zero_add] at h
  exact le_trans h h2

theorem walk_bound (cs : List Noun) (L : List (Noun × ℕ)) (h : ∀ x ∈ L, x.2 < 2 ^ 62) :
    (VclL.GenWalk.walkRows cs L).length ≤ 61 * L.length + 1 := by
  have hw := VclL.GenWalk.walkRows_length_le cs L
  have hsub : ∀ r ∈ VclL.pathReads L, r ∈ L := by
    intro r hr
    simp only [VclL.pathReads, List.mem_dedup, List.mem_filter] at hr
    exact hr.1
  have hsum : ((VclL.pathReads L).map fun r => VclL.depthOf r.2).sum ≤ (VclL.pathReads L).length * 61 := by
    have := List.sum_le_length_nsmul ((VclL.pathReads L).map fun r => VclL.depthOf r.2) 61 (by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact ComplJ9AReads.depthOf_le61 (h r (hsub r hr)))
    simpa using this
  have hlen : (VclL.pathReads L).length ≤ L.length :=
    ((List.dedup_sublist _).trans List.filter_sublist).length_le
  split_ifs at hw <;> nlinarith

theorem segReads_length (n : ℕ) : ∀ (m : ℕ) (s : Noun), (ComplJ9AData.segReads n m s).length = m + 1
  | 0, s => by simp [ComplJ9AData.segReads]
  | m + 1, s => by simp [ComplJ9AData.segReads, segReads_length n m]

theorem walkReadsX9A : ComplJ9AReads.walkReadsX9 (ComplJ9AGen.rowsOfT9 tA) = [] := by
  rw [rows9A]; decide

theorem readsA_lt : ∀ x ∈ DA.reads, x.2 < 2 ^ 62 := by
  intro x hx
  change x ∈ ComplJ9AReads.walkReadsX9 _ ++ ComplJ9AChainsRun.axChainReadsK9 _ at hx
  rw [walkReadsX9A, List.nil_append] at hx
  simp only [ComplJ9AChainsRun.axChainReadsK9, List.mem_filter, List.mem_flatMap] at hx
  obtain ⟨⟨k, -, hl⟩, -⟩ := hx
  have h33 : (2 : ℕ) ^ 33 < 2 ^ 62 := by norm_num
  exact lt_trans (ComplJ9AData.segReads_lt _ _ _ x hl) h33

theorem readsA_len : DA.reads.length ≤ 4 := by
  change (ComplJ9AReads.walkReadsX9 _ ++ ComplJ9AChainsRun.axChainReadsK9 _).length ≤ 4
  rw [walkReadsX9A, List.nil_append]
  unfold ComplJ9AChainsRun.axChainReadsK9
  refine le_trans (List.length_filter_le _ _) ?_
  rw [keys9A]
  simp [segReads_length, topB, topF]

theorem filterKeysA : ((ComplJ9AChainsRun.axKeys9 (ComplJ9AGen.rowsOfT9 tA)).filter
    fun k => decide (Nock.Field.p ≤ k.2)) = [(sA, AB)] := by
  rw [keys9A]; simp [pB, Nat.not_le.mpr pF]

theorem filterRowsA : ((ComplJ9AGen.rowsOfT9 tA).toList.filter
    fun l => decide (l.chip = .s10B ∧ Nock.Field.p ≤ l.n)) = [] := by
  rw [rows9A]; decide

theorem preadsDA : DA.preads = ComplJ9AData.limbReads AB := by
  rw [ComplJ9ADataRec.j9aDataOf_preads, preadsA, List.nil_append]
  unfold ComplJ9AChainsRun.axReadsK9
  rw [filterKeysA, filterRowsA]
  simp

theorem nVA : nVOf DA ≤ 2 ^ 31 := by
  unfold nVOf
  split_ifs
  · norm_num
  · refine le_trans (walk_bound _ _ ?_) ?_
    · intro x hx
      rw [preadsDA] at hx
      simp only [ComplJ9AData.limbReads, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ComplJ9AData.limbAxes_lt (by rw [limbsB]; simp) y hy
    · rw [preadsDA]; simp [ComplJ9AData.limbReads, ComplJ9AData.limbAxes, limbsB]

theorem bigsA : DD.bigs = [AB] := by
  show ComplJ8Data.bigsP _ DD.roots (ComplJ8Data.rowsOfT tA) = _
  rw [rootsA, rowsA]
  unfold ComplJ8Data.bigsP
  rw [show (List.filter _ _).dedup = [AB] by decide]
  simp

theorem acsA_len : DA.acs.length ≤ 3 := by
  show (ComplJ8Data.acsP _ DD.bigs _).length ≤ 3
  rw [bigsA]
  unfold ComplJ8Data.acsP
  simp only [List.foldl_cons, List.foldl_nil, limbsB]
  have hsp : Nock.V1J8.Gen.spineOf [2 ^ 32 - 1, 2 ^ 32 - 1] = [Nock.V1J8.Gen.combOf [2 ^ 32 - 1, 2 ^ 32 - 1]] := rfl
  rw [hsp]
  have hL : Nock.V1J8.Gen.addNew [] [Nock.V1J8.Gen.combOf [2 ^ 32 - 1, 2 ^ 32 - 1]] =
      [Nock.V1J8.Gen.combOf [2 ^ 32 - 1, 2 ^ 32 - 1]] := by simp [Nock.V1J8.Gen.addNew]
  rw [hL]
  have hcell : ∀ x ∈ [Nock.V1J8.Gen.combOf [2 ^ 32 - 1, 2 ^ 32 - 1]], x.isCell = true := by
    intro x hx; simp at hx; subst hx; rfl
  have hlo := ComplJ8Atom.len_le_of_sub (ComplJ8Atom.linkOrder_spec _ hcell).1
    (fun x hx => ((ComplJ8Atom.linkOrder_spec _ hcell).2.1 x).mp hx)
  simp only [List.length_append, List.length_singleton]
  split_ifs <;> simp at hlo ⊢ <;> omega

theorem N9A : ComplJ9ARun.N9 tA = 3 := by
  rw [ComplJ9ARun.N9_def, ComplJ9ARun.W9, genX9T_A, bfs9A]; rfl

theorem nXA : ComplJ9ARun.nXOf Nock.Field.p DA.acs.length DA.H tA = 4 := by
  rw [ComplJ9ARun.nXOf_eq axOnA_tA, ComplJ9AChainsRun.axChains9_table_length, keys9A]
  simp [limbsB, limbsF]

theorem nSA : ComplJ9ARun.nSOf Nock.Field.p tA = 1 := by
  rw [ComplJ9ARun.nSOf_eq spOnA_tA]
  simp [ComplJ9AChainsRun.splitVals9, fieldAx9A]

theorem h31A : ComplJ9ARun.Rows31A DA := by
  intro x hx
  simp only [ComplJ9ARun.sizesA, sizesJ8, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hB : (bfsForest [DA.t]).length = 3 := by
    show (bfsForest [tA]).length = 3
    rw [bfsA]; rfl
  have hC := cellsA_len
  have hW : (VclL.GenWalk.walkRows DA.cells DA.reads).length ≤ 2 ^ 31 := by
    have := walk_bound DA.cells DA.reads readsA_lt
    have := readsA_len
    omega
  have hJ : DA.jrows.length = 0 := by
    show DD.jrows.length = 0
    rw [jrowsA]; rfl
  have hA := acsA_len
  have hV := nVA
  have hN : ComplJ9ARun.N9 DA.t = 3 := N9A
  have hX : ComplJ9ARun.nXOf Nock.Field.p DA.acs.length DA.H DA.t = 4 := nXA
  have hS : ComplJ9ARun.nSOf Nock.Field.p DA.t = 1 := nSA
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega

/-! ## 7. `complJ9A_closed` at the toy -/

/-- The toy's J-9 A honest record. -/
abbrev BA := ComplJ9ARun.BRun9A deltaF powerBasis3 RtT genA rfl h31A

open Classical in
/-- **`complJ9A_closed` at `*[sA [[0 AB] [0 AF]]]`**, every binder discharged, nothing carried. -/
theorem complJ9A_toy :
    (∀ χ, BA.Good χ → AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 BA.Pb Nock.Jet.VerifiedRegistry.empty.R
      (ComplJ8.cJ sA fA rA) χ (BA.M χ) (BA.tr χ) BA.rows BA.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ BA.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 KC) ≤ BA.epsC) ∧
    RealIOJ9A.StJ9A BA.tr ∧ Nock.Jet.HoldsN (ComplJ8.cJ sA fA rA) ∧
    (Fintype.card KC = VclL.Events.cK →
      BA.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 BA.Pb Nock.Jet.VerifiedRegistry.empty.R
        (ComplJ8.cJ sA fA rA) χ (BA.M χ) (BA.tr χ) BA.rows BA.g) :=
  ComplJ9AClosed.complJ9A_closed deltaF powerBasis3 RtT genA rfl hax9A hop5A hleafA hwalk9A hwalkAA
    (fun id h => absurd h (calledA id)) (fun id h => absurd h (calledA id)) h31A

/-- **The toy, both chips ON, hypothesis-free**: the axis chip and the split chip are present, `ε_c < 2^-120`,
and an accepting coin. -/
theorem complJ9A_toy_figure :
    ComplJ9ARun.axOnA tA = true ∧ ComplJ9ARun.spOnA Nock.Field.p tA = true ∧
      BA.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 BA.Pb Nock.Jet.VerifiedRegistry.empty.R
        (ComplJ8.cJ sA fA rA) χ (BA.M χ) (BA.tr χ) BA.rows BA.g :=
  ⟨axOnA_tA, spOnA_tA, complJ9A_toy.2.2.2.2 card_KC⟩

end

end Nock.RedTeam.Batch4883

#print axioms Nock.RedTeam.Batch4883.slot_rsp
#print axioms Nock.RedTeam.Batch4883.genA
#print axioms Nock.RedTeam.Batch4883.h31A
#print axioms Nock.RedTeam.Batch4883.complJ9A_toy
#print axioms Nock.RedTeam.Batch4883.complJ9A_toy_figure
