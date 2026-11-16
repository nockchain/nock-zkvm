/-
`PbOfX9L`, the uniform `PubJ9AL` of a loaded J-9 AL instance (twin of `J9A/PbOfX9.lean`):
the eight J-9 A tables as at J-9 A (at `famJ9AL`), plus the ALU (`hL := k+1`, `nL := nOpt XI "aluChipJ9"`, `nodesL i := zv hGen ^ i`, `prims` read from
`XI.pubIn.prims`, `preL k` the loaded preprocessed columns `2+k` of the ALU table), its geometry (`geom_PbOfX9L`), `hHt` (`hHt_PbOfX9L`) and the
datum link (`link9L_PbOfX9L`).  Not zero-knowledge.
-/
import NockvmE2E.J9AL.GenJ9AL
import NockvmE2E.J9A.PbOfX9
import NockvmE2E.J9A.RunGate9L
import NockvmE2E.Exec.MaskOkK

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

open Polynomial

namespace NockvmE2E.J9AL.PbOfX9L

open Nock.NockVMROM.Thm54.StrictExtension
open Nock.Framework (rowNodeSet)
open NockvmE2E.Exec NockvmE2E.Exec.E2EGen NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.ShapeF NockvmE2E.Exec.J9AChips
  NockvmE2E.Exec.J9ALChips
open NockvmE2E.J9A.InstJ9A NockvmE2E.J9A.GenJ9A NockvmE2E.J9A.PbOfX9
open NockvmE2E.J9AL.InstJ9AL NockvmE2E.J9AL.GenJ9AL
open NockvmE2E.J8.InstJ8 (P tabOf hNof ω0 fold_pos fold_mono hNof_pos_of_isSome tabOf_isSome_of_mem)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A (PubJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.Jet.ChipJ8 (PRow)

/-! ## 1. shape facts at the J-9 AL family -/

theorem hNof_leL (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (id : String) : hNof XI id ≤ XI.hN := by
  unfold hNof tabOf
  cases hf : XI.tabs.toList.find? (fun t => t.chip.id == id) with
  | none => simp
  | some t => simpa using hle_of_shapeF h t (List.mem_of_find?_eq_some hf)

theorem k_le_25L {XI : ExecInst} (h : shapeOkF famJ9AL XI = true) : XI.k ≤ 25 := by
  have := hn32_of_shapeF h
  have h2 : XI.nD = XI.k + 7 := by
    have := h
    unfold shapeOkF at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    tauto
  omega

theorem hN_leL {XI : ExecInst} (h : shapeOkF famJ9AL XI = true) : XI.hN ≤ 2 ^ 26 := by
  rw [hN_of_shapeF h]
  exact Nat.pow_le_pow_right (by norm_num) (by have := k_le_25L h; omega)

theorem hN_ltPL {XI : ExecInst} (h : shapeOkF famJ9AL XI = true) : XI.hN < P := by
  have := hN_leL h
  have h2 : 2 ^ 26 < P := by norm_num [P, Nock.Field.p]
  omega

theorem hN_oneL {XI : ExecInst} (h : shapeOkF famJ9AL XI = true) : 1 ≤ XI.hN := by
  rw [hN_of_shapeF h]; exact Nat.one_le_two_pow

/-- the positivity side conditions at the AL family: as `PosX9`, plus the optional ALU -/
def PosX9L (XI : ExecInst) : Prop :=
  PosX9 XI ∧ ((tabOf XI "aluChipJ9").isSome → 0 < hNof XI "aluChipJ9")

theorem mand_memL {XI : ExecInst} (h : shapeOkF famJ9AL XI = true) :
    ∀ id ∈ famJ9AL.mandatory, id ∈ XI.tabs.toList.map (·.chip.id) := by
  have hm := mandatoryOk_of_shapeF h
  unfold mandatoryOkF at hm
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hm
  exact hm.2

theorem posX9L_of_shapeF {XI : ExecInst} (h : shapeOkF famJ9AL XI = true) : PosX9L XI := by
  have hp := hN_pos_of_shapeF h
  have hm := mand_memL h
  refine ⟨⟨hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm _ (by simp [famJ9AL]))),
    hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm _ (by simp [famJ9AL]))),
    hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm _ (by simp [famJ9AL]))),
    hNof_pos_of_isSome hp _ (tabOf_isSome_of_mem _ _ (hm _ (by simp [famJ9AL]))),
    fun hs => hNof_pos_of_isSome hp _ hs, fun hs => hNof_pos_of_isSome hp _ hs, fun hs => hNof_pos_of_isSome hp _ hs⟩,
    fun hs => hNof_pos_of_isSome hp _ hs⟩

/-- the single trace-domain orbit of every table (`ω = zv hGen`, `β = 1`, exact order `3·2^(k+1)`) -/
def orbX9L (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) : StrictOrbitDomain (ZMod P) 3 (XI.k + 1) :=
  ⟨zv XI.hGen, 1, by omega, by omega, orbit_order_of_shapeF h, one_ne_zero⟩

theorem nOpt_leL {XI : ExecInst} (h : shapeOkF famJ9AL XI = true) (id : String) : nOpt XI id ≤ XI.hN := by
  unfold nOpt
  split_ifs
  · exact hNof_leL XI h _
  · exact hN_oneL h

/-! ## 2. `PbOfX9L` -/

/-- the primitive table of the instance's public input as nock's `prims` (`[]` on an unknown code) -/
def primsOf (XI : ExecInst) : List (ℕ × Nock.Jet.Prim.PrimOp) :=
  (NockvmE2E.J9A.RunGate9L.primsOfPub XI.pubIn.prims).getD []

/-- the pin index of a primitive id: its `idx` in the public input's `prims` (`0` if absent) -/
def idxPOf (XI : ExecInst) (id : ℕ) : ℕ := ((XI.pubIn.prims.find? (fun q => q.id == id)).map (·.idx)).getD 0

/-- the public rank limbs of a primitive id: its `(hi, lo)` in the public input's `prims` (`(0, 0)` if absent) -/
def rkPOf (XI : ExecInst) (id : ℕ) : ℕ × ℕ := ((XI.pubIn.prims.find? (fun q => q.id == id)).map (fun q => (q.hi, q.lo))).getD (0, 0)

/-- the first ALU table's column `0` -/
def aluCol0 (XI : ExecInst) : ℕ := ((tabOf XI "aluChipJ9").map (·.col0)).getD 0

/-- the loaded preprocessed column `2 + k` of the ALU as a polynomial (`0` if the ALU is absent) -/
noncomputable def preLOfX (XI : ExecInst) (k : Fin 3) : (ZMod P)[X] :=
  if (tabOf XI "aluChipJ9").isSome then NockvmE2E.Exec.MaskOkK.polyOfArr (XI.pre[aluCol0 XI + 2 + (k : ℕ)]!) else 0

/-- **`PbOfX9L`**: every table gets `h := k+1`, the orbit `orbX9L`, `n_t := hN_t`, `nodes_t i := ω^i`.  An absent jet has `nJ = 0`; an absent atom walk / axis /
split / ALU has `n = 1`, `nodes 0 = 1`. -/
noncomputable def PbOfX9L (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (kroots krootsV : ℕ) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ) (lay : Fin (hNof XI "jetChipJ8") → PRow) : PubJ9AL P where
  h := XI.k + 1
  n := hNof XI "computeChipVCLHX9"
  hn := (posX9L_of_shapeF h).1.1
  nodes i := zv XI.hGen ^ (i : ℕ)
  orbit := orbX9L XI h
  hC := XI.k + 1
  nC := hNof XI "cellChipHQKW"
  hnC := (posX9L_of_shapeF h).1.2.1
  nodesC i := zv XI.hGen ^ (i : ℕ)
  orbitC := orbX9L XI h
  kroots := kroots
  hW := XI.k + 1
  nW := hNof XI "walkChipJ8"
  hnW := (posX9L_of_shapeF h).1.2.2.1
  nodesW i := zv XI.hGen ^ (i : ℕ)
  orbitW := orbX9L XI h
  hJ := XI.k + 1
  nJ := hNof XI "jetChipJ8"
  nodesJ i := zv XI.hGen ^ (i : ℕ)
  orbitJ := orbX9L XI h
  lay := lay
  hA := XI.k + 1
  nA := hNof XI "atomChipHQL"
  hnA := (posX9L_of_shapeF h).1.2.2.2.1
  nodesA i := zv XI.hGen ^ (i : ℕ)
  orbitA := orbX9L XI h
  krootsV := if (tabOf XI "walkChipHQK").isSome then krootsV else 0
  hV := XI.k + 1
  nV := nOpt XI "walkChipHQK"
  hnV := nOpt_pos (posX9L_of_shapeF h).1 _ (posX9L_of_shapeF h).1.2.2.2.2.1
  nodesV i := zv XI.hGen ^ (i : ℕ)
  orbitV := orbX9L XI h
  Rt := Rt
  regs := regs
  ids := ids
  idx := idx
  rk := rk
  hX := XI.k + 1
  nX := nOpt XI "axisChipJ9"
  hnX := nOpt_pos (posX9L_of_shapeF h).1 _ (posX9L_of_shapeF h).1.2.2.2.2.2.1
  nodesX i := zv XI.hGen ^ (i : ℕ)
  orbitX := orbX9L XI h
  hS := XI.k + 1
  nS := nOpt XI "splitChipJ9"
  hnS := nOpt_pos (posX9L_of_shapeF h).1 _ (posX9L_of_shapeF h).1.2.2.2.2.2.2
  nodesS i := zv XI.hGen ^ (i : ℕ)
  orbitS := orbX9L XI h
  axOn := (tabOf XI "axisChipJ9").isSome
  spOn := (tabOf XI "splitChipJ9").isSome
  hL := XI.k + 1
  nL := nOpt XI "aluChipJ9"
  hnL := nOpt_pos (posX9L_of_shapeF h).1 _ (posX9L_of_shapeF h).2
  nodesL i := zv XI.hGen ^ (i : ℕ)
  orbitL := orbX9L XI h
  aluOn := (tabOf XI "aluChipJ9").isSome
  prims := primsOf XI
  idxP := idxPOf XI
  rkP := rkPOf XI
  preL := preLOfX XI

/-! ## 3. geometry -/

theorem inj_pows_L {XI : ExecInst} (h : shapeOkF famJ9AL XI = true) {n : ℕ} (hn : n ≤ XI.hN) :
    Function.Injective (fun i : Fin n => ω0 XI ^ (i : ℕ)) :=
  inj_pows9L h hn

theorem adj_pows_L {XI : ExecInst} (h : shapeOkF famJ9AL XI = true) {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    ω0 XI ^ ((⟨(i : ℕ) + 1, hi⟩ : Fin n) : ℕ) = ω0 XI ^ (i : ℕ) * (orbX9L XI h).ω := by
  show ω0 XI ^ ((i : ℕ) + 1) = _
  rw [pow_succ]; rfl

/-- the geometric conjuncts of `StmtP9AL`: `Geom9` of the J-9 A part, and the ALU's injectivity, adjacency and size bounds (unconditionally) -/
structure Geom9L (Pb : PubJ9AL P) : Prop where
  geomA : Geom9 Pb.toPubJ9A
  hinjL : Function.Injective Pb.nodesL
  hadjL : ∀ (i : Fin Pb.nL) (hi : (i : ℕ) + 1 < Pb.nL), Pb.nodesL ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesL i * Pb.orbitL.ω
  hnpL : Pb.nL < P
  hlenL : Pb.nL + Pb.n < P

theorem geom_PbOfX9L (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) :
    Geom9L (PbOfX9L XI h kroots krootsV Rt regs ids idx rk lay) := by
  have hlt := hN_ltPL h
  have hle := hN_leL h
  have hrc : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n P
  have hV := nOpt_leL h "walkChipHQK"
  have hX := nOpt_leL h "axisChipJ9"
  have hS := nOpt_leL h "splitChipJ9"
  have hL := nOpt_leL h "aluChipJ9"
  have h2 : (2 : ℕ) * 2 ^ 26 < P := by norm_num [P, Nock.Field.p]
  have h3 : (2 : ℕ) * 2 ^ 26 < 2 ^ 57 := by norm_num
  have hC := hNof_leL XI h "computeChipVCLHX9"
  have hA := hNof_leL XI h "atomChipHQL"
  refine ⟨⟨inj_pows_L h (hNof_leL XI h _), fun i hi => adj_pows_L h i hi, inj_pows_L h (hNof_leL XI h _),
    fun i hi => adj_pows_L h i hi, ?_, inj_pows_L h (hNof_leL XI h _), fun i hi => adj_pows_L h i hi,
    fun _ => ⟨inj_pows_L h (hNof_leL XI h _), fun i hi => adj_pows_L h i hi⟩, inj_pows_L h (hNof_leL XI h _),
    fun i hi => adj_pows_L h i hi, ?_, fun _ => ⟨inj_pows_L h hV, fun i hi => adj_pows_L h i hi⟩,
    fun _ => ⟨inj_pows_L h hX, fun i hi => adj_pows_L h i hi, ?_⟩,
    fun _ => ⟨inj_pows_L h hS, fun i hi => adj_pows_L h i hi, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩,
    inj_pows_L h hL, fun i hi => adj_pows_L h i hi, ?_, ?_⟩
  · show hNof XI "cellChipHQKW" < ringChar (ZMod P)
    rw [hrc]; exact lt_of_le_of_lt (hNof_leL XI h _) hlt
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
    have := hNof_leL XI h "jetChipJ8"
    omega
  · show nOpt XI "aluChipJ9" < P
    omega
  · show nOpt XI "aluChipJ9" + hNof XI "computeChipVCLHX9" < P
    omega

/-! ## 4. `hHt` and the datum link -/

/-- `hHt` for `PbOfX9L`: every row set lies in the union domain `{ω^i : i < hN}` (`n_t ≤ hN`) -/
theorem hHt_PbOfX9L (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum9AL) (hd : d.Pb = PbOfX9L XI h kroots krootsV Rt regs ids idx rk lay)
    (hN : d.hN = XI.hN) (hω : d.ω = ω0 XI) : ∀ t, HtOf9L d t ⊆ HdomOf9L d := by
  have hV := nOpt_leL h "walkChipHQK"
  have hX := nOpt_leL h "axisChipJ9"
  have hS := nOpt_leL h "splitChipJ9"
  have hL := nOpt_leL h "aluChipJ9"
  obtain ⟨Pb, Rg, c, r, g, hN', ω'⟩ := d
  simp only at hd hN hω
  subst hd hN hω
  intro t x hxt
  have key : ∀ {n : ℕ} (nodes : Fin n → ZMod P), (∀ i, nodes i = ω0 XI ^ (i : ℕ)) → n ≤ XI.hN →
      x ∈ rowNodeSet nodes →
      x ∈ HdomOf9L ⟨PbOfX9L XI h kroots krootsV Rt regs ids idx rk lay, Rg, c, r, g, XI.hN, ω0 XI⟩ := by
    intro n nodes hn hle hxm
    unfold rowNodeSet at hxm
    obtain ⟨i, -, rfl⟩ := (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) nodes Finset.univ x).mp hxm
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le i.2 hle), (hn i).symm⟩
  fin_cases t
  · exact key _ (fun i => rfl) (hNof_leL XI h _) hxt
  · exact key _ (fun i => rfl) (hNof_leL XI h _) hxt
  · exact key _ (fun i => rfl) (hNof_leL XI h _) hxt
  · exact key _ (fun i => rfl) (hNof_leL XI h _) hxt
  · exact key _ (fun i => rfl) (hNof_leL XI h _) hxt
  · exact key _ (fun i => rfl) hV hxt
  · exact key _ (fun i => rfl) hX hxt
  · exact key _ (fun i => rfl) hS hxt
  · exact key _ (fun i => rfl) hL hxt

/-- the `hN` of a table of the instance is `hNof` of its chip id (the chip ids are pairwise distinct) -/
theorem hNof_tabL (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (t : Fin XI.tabs.size) :
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

/-- **`link9L_PbOfX9L`**: a datum over `PbOfX9L` with `hN = XI.hN`, `ω = zv hGen` is linked to the instance -/
theorem link9L_PbOfX9L (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (kroots krootsV : ℕ)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ)
    (lay : Fin (hNof XI "jetChipJ8") → PRow) (d : Datum9AL) (hd : d.Pb = PbOfX9L XI h kroots krootsV Rt regs ids idx rk lay)
    (hN : d.hN = XI.hN) (hω : d.ω = zv XI.hGen) : Link9L XI d := by
  have hV := nOpt_leL h "walkChipHQK"
  have hX := nOpt_leL h "axisChipJ9"
  have hS := nOpt_leL h "splitChipJ9"
  have hL := nOpt_leL h "aluChipJ9"
  obtain ⟨Pb, Rg, c, r, g, hN', ω'⟩ := d
  simp only at hd hN hω
  subst hd hN hω
  refine ⟨rfl, rfl, ?_, fun i => rfl, fun i => rfl, fun i => rfl, fun i => rfl, fun i => rfl, fun i => rfl, fun i => rfl,
    fun i => rfl, fun i => rfl, ?_, ?_⟩
  · intro t
    fin_cases t <;> rfl
  · intro t
    fin_cases t
    · exact hNof_leL XI h _
    · exact hNof_leL XI h _
    · exact hNof_leL XI h _
    · exact hNof_leL XI h _
    · exact hNof_leL XI h _
    · exact hV
    · exact hX
    · exact hS
    · exact hL
  · intro t
    have hid := (ids_of_shapeF h).2 _ (Array.getElem_mem_toList t.2)
    have hnt := hNof_tabL XI h t
    have hs : (tabOf XI XI.tabs[t].chip.id).isSome = true :=
      tabOf_isSome_of_mem XI _ (List.mem_map.mpr ⟨XI.tabs[t], Array.getElem_mem_toList t.2, rfl⟩)
    have hid' : XI.tabs[t].chip.id ∈ idsJ9AL := hid
    unfold sigma9L
    generalize XI.tabs[t].chip.id = id at hid' hnt hs
    simp only [idsJ9AL, idsJ9A, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hid'
    rcases hid' with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;>
      simp [tabIdx9L, tabIdx9, Nof9L, PbOfX9L, nOpt, hs, hnt]

/-- the table of a chip id is the unique table with that id -/
theorem tabOf_of_idF (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (t : Fin XI.tabs.size) :
    tabOf XI XI.tabs[t].chip.id = some XI.tabs[t] := by
  obtain ⟨hnd, -⟩ := ids_of_shapeF h
  have hmem : XI.tabs[t] ∈ XI.tabs.toList := Array.getElem_mem_toList t.2
  unfold tabOf
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
    rw [this]

/-- **the datum's ALU preprocessed columns are the loaded ones** (`PreLLink`'s body at `PbOfX9L`) -/
theorem preL_PbOfX9L (XI : ExecInst) (h : shapeOkF famJ9AL XI = true) (t : Fin XI.tabs.size)
    (hid : XI.tabs[t].chip.id = "aluChipJ9") (k : Fin 3) :
    preLOfX XI k = NockvmE2E.Exec.MaskOkK.polyOfArr (XI.pre[XI.tabs[t].col0 + 2 + (k : ℕ)]!) := by
  have ht := tabOf_of_idF XI h t
  rw [hid] at ht
  unfold preLOfX aluCol0
  rw [ht]
  rfl

end NockvmE2E.J9AL.PbOfX9L

#print axioms NockvmE2E.J9AL.PbOfX9L.posX9L_of_shapeF
#print axioms NockvmE2E.J9AL.PbOfX9L.orbX9L
#print axioms NockvmE2E.J9AL.PbOfX9L.PbOfX9L
#print axioms NockvmE2E.J9AL.PbOfX9L.geom_PbOfX9L
#print axioms NockvmE2E.J9AL.PbOfX9L.hHt_PbOfX9L
#print axioms NockvmE2E.J9AL.PbOfX9L.link9L_PbOfX9L
#print axioms NockvmE2E.J9AL.PbOfX9L.tabOf_of_idF
#print axioms NockvmE2E.J9AL.PbOfX9L.preL_PbOfX9L
