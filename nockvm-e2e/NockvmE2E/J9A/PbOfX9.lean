/-
J9A-LINK: `PbOfX9`, the uniform `PubJ9A` of a loaded J-9 A instance (twin of
`InstJ8.PbOfX` of `J8/InstJ8.lean` §6), its geometry (`geom_PbOfX9`), `hHt` (`hHt_PbOfX9`) and the datum link (`link9_PbOfX9`).
-/
import NockvmE2E.J9A.GenJ9A
import NockvmE2E.J8.InstJ8W

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J9A.PbOfX9

open Nock.NockVMROM.Thm54.StrictExtension
open Nock.Framework (rowNodeSet)
open NockvmE2E.Exec NockvmE2E.Exec.E2EGen NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A
open NockvmE2E.J8.InstJ8 (P tabOf hNof ω0 fold_pos fold_mono hNof_pos_of_isSome tabOf_isSome_of_mem)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (PubJ9A)
open Nock.Jet.ChipJ8 (PRow)

/-! ## 1. shape facts at the J-9 A family -/

/-- every table of a family-shaped instance has a row (`tabsOk`) -/
theorem hN_pos_of_shapeF {XI : ExecInst} {F : Fam} (h : shapeOkF F XI = true) : ∀ t ∈ XI.tabs.toList, 1 ≤ t.hN := by
  have h1 := tabsOk_of_shapeF h
  unfold NockvmE2E.Exec.V.tabsOk at h1
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.1.1.2
  rw [← Array.foldl_toList] at h2
  refine fold_pos _ ?_ XI.tabs.toList _ h2
  intro st t hst
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hst
  exact ⟨by tauto, by tauto⟩

theorem hNof_le9 (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (id : String) : hNof XI id ≤ XI.hN := by
  unfold hNof tabOf
  cases hf : XI.tabs.toList.find? (fun t => t.chip.id == id) with
  | none => simp
  | some t => simpa using hle_of_shapeF h t (List.mem_of_find?_eq_some hf)

theorem k_le_25_9 {XI : ExecInst} (h : shapeOkF famJ9A XI = true) : XI.k ≤ 25 := by
  have := hn32_of_shapeF h
  have h2 : XI.nD = XI.k + 7 := by
    have := h
    unfold shapeOkF at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    tauto
  omega

theorem hN_le_9 {XI : ExecInst} (h : shapeOkF famJ9A XI = true) : XI.hN ≤ 2 ^ 26 := by
  rw [hN_of_shapeF h]
  exact Nat.pow_le_pow_right (by norm_num) (by have := k_le_25_9 h; omega)

theorem hN_lt_p_9 {XI : ExecInst} (h : shapeOkF famJ9A XI = true) : XI.hN < P := by
  have := hN_le_9 h
  have h2 : 2 ^ 26 < P := by norm_num [P, Nock.Field.p]
  omega

theorem hN_one_9 {XI : ExecInst} (h : shapeOkF famJ9A XI = true) : 1 ≤ XI.hN := by
  rw [hN_of_shapeF h]; exact Nat.one_le_two_pow

/-! ## 2. `PosX9`, `orbX9`, `PbOfX9` -/

/-- the positivity side conditions: the four mandatory tables have rows; an optional table that is present has rows -/
def PosX9 (XI : ExecInst) : Prop :=
  0 < hNof XI "computeChipVCLHX9" ∧ 0 < hNof XI "cellChipHQKW" ∧ 0 < hNof XI "walkChipJ8" ∧ 0 < hNof XI "atomChipHQL" ∧
  ((tabOf XI "walkChipHQK").isSome → 0 < hNof XI "walkChipHQK") ∧
  ((tabOf XI "axisChipJ9").isSome → 0 < hNof XI "axisChipJ9") ∧
  ((tabOf XI "splitChipJ9").isSome → 0 < hNof XI "splitChipJ9")

theorem mand_mem9 {XI : ExecInst} (h : shapeOkF famJ9A XI = true) :
    ∀ id ∈ famJ9A.mandatory, id ∈ XI.tabs.toList.map (·.chip.id) := by
  have hm := mandatoryOk_of_shapeF h
  unfold mandatoryOkF at hm
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hm
  exact hm.2

theorem posX9_of_shapeF {XI : ExecInst} (h : shapeOkF famJ9A XI = true) : PosX9 XI := by
  have hp := hN_pos_of_shapeF h
  have hm := mand_mem9 h
  refine ⟨hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm _ (by simp [famJ9A, idsJ9A]))),
    hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm _ (by simp [famJ9A]))),
    hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm _ (by simp [famJ9A]))),
    hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm _ (by simp [famJ9A]))),
    fun hs => hNof_pos_of_isSome hp _ hs, fun hs => hNof_pos_of_isSome hp _ hs, fun hs => hNof_pos_of_isSome hp _ hs⟩

/-- the single trace-domain orbit of every table (`ω = zv hGen`, `β = 1`, exact order `3·2^(k+1)`) -/
def orbX9 (XI : ExecInst) (h : shapeOkF famJ9A XI = true) : StrictOrbitDomain (ZMod P) 3 (XI.k + 1) :=
  ⟨zv XI.hGen, 1, by omega, by omega, orbit_order_of_shapeF h, one_ne_zero⟩

/-- the row count of an optional table: `hNof` if present, `1` if absent (absent-table convention of `PbOfX`: `nV = 1`) -/
def nOpt (XI : ExecInst) (id : String) : ℕ := if (tabOf XI id).isSome then hNof XI id else 1

theorem nOpt_pos {XI : ExecInst} (hpos : PosX9 XI) (id : String)
    (h : (tabOf XI id).isSome → 0 < hNof XI id) : 0 < nOpt XI id := by
  unfold nOpt
  by_cases hs : (tabOf XI id).isSome = true
  · simp only [hs, ite_true]; exact h hs
  · simp only [hs]; exact Nat.one_pos

theorem nOpt_le {XI : ExecInst} (h : shapeOkF famJ9A XI = true) (id : String) : nOpt XI id ≤ XI.hN := by
  unfold nOpt
  split_ifs
  · exact hNof_le9 XI h _
  · exact hN_one_9 h

/-- **`PbOfX9`**: every table gets `h := k+1`, the orbit `orbX9`, `n_t := hN_t`, `nodes_t i := ω^i`. An absent jet has `nJ = 0`;
an absent atom walk / axis / split has `n = 1`, `nodes 0 = 1` (and `krootsV = 0`, `axOn`/`spOn = false`). -/
def PbOfX9 (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (kroots krootsV : ℕ) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ) (lay : Fin (hNof XI "jetChipJ8") → PRow) : PubJ9A P where
  h := XI.k + 1
  n := hNof XI "computeChipVCLHX9"
  hn := (posX9_of_shapeF h).1
  nodes i := zv XI.hGen ^ (i : ℕ)
  orbit := orbX9 XI h
  hC := XI.k + 1
  nC := hNof XI "cellChipHQKW"
  hnC := (posX9_of_shapeF h).2.1
  nodesC i := zv XI.hGen ^ (i : ℕ)
  orbitC := orbX9 XI h
  kroots := kroots
  hW := XI.k + 1
  nW := hNof XI "walkChipJ8"
  hnW := (posX9_of_shapeF h).2.2.1
  nodesW i := zv XI.hGen ^ (i : ℕ)
  orbitW := orbX9 XI h
  hJ := XI.k + 1
  nJ := hNof XI "jetChipJ8"
  nodesJ i := zv XI.hGen ^ (i : ℕ)
  orbitJ := orbX9 XI h
  lay := lay
  hA := XI.k + 1
  nA := hNof XI "atomChipHQL"
  hnA := (posX9_of_shapeF h).2.2.2.1
  nodesA i := zv XI.hGen ^ (i : ℕ)
  orbitA := orbX9 XI h
  krootsV := if (tabOf XI "walkChipHQK").isSome then krootsV else 0
  hV := XI.k + 1
  nV := nOpt XI "walkChipHQK"
  hnV := nOpt_pos (posX9_of_shapeF h) _ (posX9_of_shapeF h).2.2.2.2.1
  nodesV i := zv XI.hGen ^ (i : ℕ)
  orbitV := orbX9 XI h
  Rt := Rt
  regs := regs
  ids := ids
  idx := idx
  rk := rk
  hX := XI.k + 1
  nX := nOpt XI "axisChipJ9"
  hnX := nOpt_pos (posX9_of_shapeF h) _ (posX9_of_shapeF h).2.2.2.2.2.1
  nodesX i := zv XI.hGen ^ (i : ℕ)
  orbitX := orbX9 XI h
  hS := XI.k + 1
  nS := nOpt XI "splitChipJ9"
  hnS := nOpt_pos (posX9_of_shapeF h) _ (posX9_of_shapeF h).2.2.2.2.2.2
  nodesS i := zv XI.hGen ^ (i : ℕ)
  orbitS := orbX9 XI h
  axOn := (tabOf XI "axisChipJ9").isSome
  spOn := (tabOf XI "splitChipJ9").isSome

/-! ## 3. geometry -/

/-- injectivity of the nodes `ω^i`, `i < n ≤ hN` -/
theorem inj_pows_9 {XI : ExecInst} (h : shapeOkF famJ9A XI = true) {n : ℕ} (hn : n ≤ XI.hN) :
    Function.Injective (fun i : Fin n => ω0 XI ^ (i : ℕ)) :=
  inj_pows9 h hn

theorem adj_pows_9 {XI : ExecInst} (h : shapeOkF famJ9A XI = true) {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    ω0 XI ^ ((⟨(i : ℕ) + 1, hi⟩ : Fin n) : ℕ) = ω0 XI ^ (i : ℕ) * (orbX9 XI h).ω := by
  show ω0 XI ^ ((i : ℕ) + 1) = _
  rw [pow_succ]; rfl

/-- the geometric conjuncts of `StmtP9A` (injectivity and adjacency of the nodes of every table, the size bounds): the lemma for `PbOfX9` -/
structure Geom9 (Pb : PubJ9A P) : Prop where
  hinjX : Function.Injective Pb.nodes
  hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  hinjC : Function.Injective Pb.nodesC
  hadjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  hnpC : Pb.nC < ringChar (ZMod P)
  hinjW : Function.Injective Pb.nodesW
  hadjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  hJgeom : Pb.nJ ≠ 0 → Function.Injective Pb.nodesJ ∧
    ∀ (i : Fin Pb.nJ) (hi : (i : ℕ) + 1 < Pb.nJ), Pb.nodesJ ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesJ i * Pb.orbitJ.ω
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < P
  hVgeom : Pb.krootsV ≠ 0 → Function.Injective Pb.nodesV ∧
    ∀ (i : Fin Pb.nV) (hi : (i : ℕ) + 1 < Pb.nV), Pb.nodesV ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesV i * Pb.orbitV.ω
  hXgeom : Pb.axOn = true → Function.Injective Pb.nodesX ∧
    (∀ (i : Fin Pb.nX) (hi : (i : ℕ) + 1 < Pb.nX), Pb.nodesX ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesX i * Pb.orbitX.ω) ∧ Pb.nX < P
  hSgeom : Pb.spOn = true → Function.Injective Pb.nodesS ∧
    (∀ (i : Fin Pb.nS) (hi : (i : ℕ) + 1 < Pb.nS), Pb.nodesS ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesS i * Pb.orbitS.ω) ∧ Pb.nS < P
  hlenA : Pb.nA + Pb.nV < P
  hnAS : Pb.nA + Pb.nS < 2 ^ 57
  hlenX : Pb.nX + Pb.n < P ∧ 2 * Pb.nS < P
  hlenAN : Pb.nV ≤ 2 ^ 26 ∧ Pb.nJ ≤ 2 ^ 26

theorem geom_PbOfX9 (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) :
    Geom9 (PbOfX9 XI h kroots krootsV Rt regs ids idx rk lay) := by
  have hlt := hN_lt_p_9 h
  have hle := hN_le_9 h
  have hrc : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n P
  have hV := nOpt_le h "walkChipHQK"
  have hX := nOpt_le h "axisChipJ9"
  have hS := nOpt_le h "splitChipJ9"
  have h2 : (2 : ℕ) * 2 ^ 26 < P := by norm_num [P, Nock.Field.p]
  have h3 : (2 : ℕ) * 2 ^ 26 < 2 ^ 57 := by norm_num
  have hC := hNof_le9 XI h "computeChipVCLHX9"
  have hA := hNof_le9 XI h "atomChipHQL"
  refine ⟨inj_pows_9 h (hNof_le9 XI h _), fun i hi => adj_pows_9 h i hi, inj_pows_9 h (hNof_le9 XI h _),
    fun i hi => adj_pows_9 h i hi, ?_, inj_pows_9 h (hNof_le9 XI h _), fun i hi => adj_pows_9 h i hi,
    fun _ => ⟨inj_pows_9 h (hNof_le9 XI h _), fun i hi => adj_pows_9 h i hi⟩, inj_pows_9 h (hNof_le9 XI h _),
    fun i hi => adj_pows_9 h i hi, ?_, fun _ => ⟨inj_pows_9 h hV, fun i hi => adj_pows_9 h i hi⟩,
    fun _ => ⟨inj_pows_9 h hX, fun i hi => adj_pows_9 h i hi, ?_⟩,
    fun _ => ⟨inj_pows_9 h hS, fun i hi => adj_pows_9 h i hi, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show hNof XI "cellChipHQKW" < ringChar (ZMod P)
    rw [hrc]; exact lt_of_le_of_lt (hNof_le9 XI h _) hlt
  · show hNof XI "atomChipHQL" < P
    exact lt_of_le_of_lt hA hlt
  · show nOpt XI "axisChipJ9" < P
    omega
  · show nOpt XI "splitChipJ9" < P
    omega
  · show hNof XI "atomChipHQL" + nOpt XI "walkChipHQK" < P
    omega
  · show hNof XI "atomChipHQL" + nOpt XI "splitChipJ9" < 2 ^ 57
    omega
  · show nOpt XI "axisChipJ9" + hNof XI "computeChipVCLHX9" < P
    omega
  · show 2 * nOpt XI "splitChipJ9" < P
    omega
  · show nOpt XI "walkChipHQK" ≤ 2 ^ 26
    omega
  · show hNof XI "jetChipJ8" ≤ 2 ^ 26
    have := hNof_le9 XI h "jetChipJ8"
    omega

/-! ## 4. `hHt` and the datum link -/

/-- `hHt` for `PbOfX9`: every row set lies in the union domain `{ω^i : i < hN}` (`n_t ≤ hN`) -/
theorem hHt_PbOfX9 (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum9A) (hd : d.Pb = PbOfX9 XI h kroots krootsV Rt regs ids idx rk lay)
    (hN : d.hN = XI.hN) (hω : d.ω = ω0 XI) : ∀ t, HtOf9 d t ⊆ HdomOf9 d := by
  have hV := nOpt_le h "walkChipHQK"
  have hX := nOpt_le h "axisChipJ9"
  have hS := nOpt_le h "splitChipJ9"
  obtain ⟨Pb, Rg, c, r, g, hN', ω'⟩ := d
  simp only at hd hN hω
  subst hd hN hω
  intro t x hxt
  have key : ∀ {n : ℕ} (nodes : Fin n → ZMod P), (∀ i, nodes i = ω0 XI ^ (i : ℕ)) → n ≤ XI.hN →
      x ∈ rowNodeSet nodes → x ∈ HdomOf9 ⟨PbOfX9 XI h kroots krootsV Rt regs ids idx rk lay, Rg, c, r, g, XI.hN, ω0 XI⟩ := by
    intro n nodes hn hle hxm
    unfold rowNodeSet at hxm
    obtain ⟨i, -, rfl⟩ := (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) nodes Finset.univ x).mp hxm
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le i.2 hle), (hn i).symm⟩
  fin_cases t
  · exact key _ (fun i => rfl) (hNof_le9 XI h _) hxt
  · exact key _ (fun i => rfl) (hNof_le9 XI h _) hxt
  · exact key _ (fun i => rfl) (hNof_le9 XI h _) hxt
  · exact key _ (fun i => rfl) (hNof_le9 XI h _) hxt
  · exact key _ (fun i => rfl) (hNof_le9 XI h _) hxt
  · exact key _ (fun i => rfl) hV hxt
  · exact key _ (fun i => rfl) hX hxt
  · exact key _ (fun i => rfl) hS hxt

/-- the `hN` of a table of the instance is `hNof` of its chip id (the chip ids are pairwise distinct) -/
theorem hNof_tab (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (t : Fin XI.tabs.size) :
    hNof XI XI.tabs[t].chip.id = XI.tabs[t].hN := by
  obtain ⟨hnd, -⟩ := ids_of_shapeF h
  have hmem : XI.tabs[t] ∈ XI.tabs.toList := Array.getElem_mem_toList t.2
  unfold hNof tabOf
  cases hf : XI.tabs.toList.find? (fun t' => t'.chip.id == XI.tabs[t].chip.id) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf _ hmem
    simp at this
  | some t0 =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp only [beq_iff_eq] at h2
    have := List.inj_on_of_nodup_map hnd h1 hmem h2
    simp [this]

theorem isSome_tab (XI : ExecInst) (t : Fin XI.tabs.size) : (tabOf XI XI.tabs[t].chip.id).isSome = true :=
  tabOf_isSome_of_mem XI _ (List.mem_map.mpr ⟨XI.tabs[t], Array.getElem_mem_toList t.2, rfl⟩)

/-- **`link9_PbOfX9`**: a datum over `PbOfX9` with `hN = XI.hN`, `ω = zv hGen` is linked to the instance -/
theorem link9_PbOfX9 (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum9A) (hd : d.Pb = PbOfX9 XI h kroots krootsV Rt regs ids idx rk lay)
    (hN : d.hN = XI.hN) (hω : d.ω = zv XI.hGen) : Link9 XI d := by
  have hV := nOpt_le h "walkChipHQK"
  have hX := nOpt_le h "axisChipJ9"
  have hS := nOpt_le h "splitChipJ9"
  obtain ⟨Pb, Rg, c, r, g, hN', ω'⟩ := d
  simp only at hd hN hω
  subst hd hN hω
  refine ⟨rfl, rfl, ?_, fun i => rfl, fun i => rfl, fun i => rfl, fun i => rfl, fun i => rfl, fun i => rfl, fun i => rfl,
    fun i => rfl, ?_, ?_⟩
  · intro t
    fin_cases t <;> rfl
  · intro t
    fin_cases t
    · exact hNof_le9 XI h _
    · exact hNof_le9 XI h _
    · exact hNof_le9 XI h _
    · exact hNof_le9 XI h _
    · exact hNof_le9 XI h _
    · exact hV
    · exact hX
    · exact hS
  · intro t
    have hid := (ids_of_shapeF h).2 _ (Array.getElem_mem_toList t.2)
    have hnt := hNof_tab XI h t
    have hs := isSome_tab XI t
    have hid' : XI.tabs[t].chip.id ∈ idsJ9A := hid
    unfold sigma9
    generalize XI.tabs[t].chip.id = id at hid' hnt hs
    simp only [idsJ9A, List.mem_cons, List.not_mem_nil, or_false] at hid'
    rcases hid' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [tabIdx9, Nof9, PbOfX9, nOpt, hs, hnt]

end NockvmE2E.J9A.PbOfX9

#print axioms NockvmE2E.J9A.PbOfX9.posX9_of_shapeF
#print axioms NockvmE2E.J9A.PbOfX9.orbX9
#print axioms NockvmE2E.J9A.PbOfX9.PbOfX9
#print axioms NockvmE2E.J9A.PbOfX9.geom_PbOfX9
#print axioms NockvmE2E.J9A.PbOfX9.hHt_PbOfX9
#print axioms NockvmE2E.J9A.PbOfX9.link9_PbOfX9
