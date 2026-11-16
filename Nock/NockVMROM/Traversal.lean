import Nock.Framework
import Nock.NMRMEF
import Nock.NockVMROM.Language
import Nock.NockVMROM.Separation

/-!
# S4 — `nock_traversalModel` + `nock_isTraversable` : NockVMROM `(Fcomp, Fmem)`-traversability

The S4 Layer-1 surface for the NockVMROM tag.

* `nock_traversalModel` carries the *labeling data*: the compute label space `State × DTcomp K`
  with arity `n_comp = 3` and single root `k_comp = 1`, the memory label space `MState × DTmem K`
  with arity `n_mem = 2` and single root `k_mem = 1`, and the two algebraically-constrainable
  labeling relations — the genuine walk recognisers `ComputeTable.Fcomp` / `MemoryTable.Fmem`.  These are exactly the arities used by the existing
  `Nock.Framework.nock_traversable` (compute arity 3, memory arity 2).

* `nock_isTraversable` discharges the `IsTraversable` recognition of the compute/memory languages
  by the **exact arity-`n` `RVTWithArity` tree languages** `∏_{i<1} {t // RVTWithArity F_i t}`,
  via the recognition fields below — NOT via a free-field `φ`.

  This surface is
  **not** the paper's full `Def:traversable` bijection between the *whole accepted* compute/memory
  sublanguages and the RVT products.  It carries (a) the genuine **sound inclusion**
  `L_RVT^{F,n} ⊆ L` (via `computeAccepts`/`memoryAccepts`) and (b) a **walk-structured** `F`-row →
  RVT reconstruction — but the reconstruction quantifies over rows *assumed* to satisfy `F` with a
  valid BFS layout, **not** over arbitrary `computeAccepts`/`memoryAccepts` witnesses, and
  `computeReadout` is singleton-valued (so an accepted trace such as the empty one is outside its
  image — `b12_s4_accepted_not_in_readout`).  A genuine bijection would additionally require
  threading `computeAccepts` through the reconstruction under a walk-structure hypothesis and tying
  the root count — the remaining bridge (F4), disclosed not closed.

  **Honest exact-`RVTWithArity` form (fixes SC4's bare-`RVT` overshoot).**  Unlike the earlier
  `Framework.nock_traversable`, whose language object was `{t // RVT F t}` (bare `RVT`, which
  strictly overshoots the paper's arity-`n` `L_SLT^n` target — see the `ProperArity`/`RVTWithArity`
  docstrings), the recognised language here is the *exact*
  `Nock.Walk.RVTWithArity F t = RVT F t ∧ ProperArity n t`, i.e. the faithful `L_RVT^{F,n}` of

  The class no longer carries the self-chosen
  `ComputeLang`/`MemoryLang` types or the traversability isomorphisms `φ_comp`/`φ_mem` (which were
  an `Equiv.refl` over a free `Type` field, satisfiable by any VM and untied to Nock); those four
  fields are removed at the class level.  This instance discharges EXACTLY the `IsTraversable`
  *recognition* fields, which reference the VM's ACTUAL sub-verifiers via the S1 separation
  `nock_uniqueMES` (`computeAccepts`/`memoryAccepts`):

  * `recognizes_compute`/`recognizes_memory` — the **sound inclusion** `L_RVT^{Fcomp,3} ⊆ L_comp`
    (resp. `L_RVT^{Fmem,2} ⊆ L_mem`): every label the walk recogniser `ComputeTable.Fcomp`
    (resp. `MemoryTable.Fmem`) accepts is accepted by Nock's own `V_comp` (resp. `V_mem`) on its
    readout row.  This is immediate because `Fcomp`/`Fmem` *embed* `Vcomp`/`Vmem` (their second
    conjunct, `NockVM.lean:195`/`341`), and `computeAccepts`/`memoryAccepts` are exactly the
    per-row `Vcomp`/`Vmem` folds — the substantive direction of the paper's `L ≡ L_RVT`.
  * `compute_recognized`/`memory_recognized` — a **witnessed inhabitant**: `V_comp`/`V_mem`
    genuinely accept the readout of the concrete `Fcomp`/`Fmem`-recognised leaf supplied by
    `Fcomp_nonvacuous`/`Fmem_nonvacuous`.
  * `recognized_complete_compute`/`recognized_complete_memory` — a **walk-structured reconstruction**
    (NOT the reverse inclusion of the acceptance language): every *walk-structured* family of rows
    each satisfying `Fcomp`/`Fmem` (with a valid BFS layout) reconstructs to an `RVTWithArity`
    forest, discharged by `nockvmrom_compute_complete`/`nockvmrom_memory_complete` (below).  This
    does **not** quantify over `computeAccepts`/`memoryAccepts`, so it is not the paper's full
    acceptance↔RVT bijection (see the HONEST SCOPE note above, F4).

  Because these fields reference `computeAccepts`/`memoryAccepts`, the class is **no longer
  satisfiable for an arbitrary `VMSystem`** (it fails when the sub-verifier rejects everything or
  the labeling relation recognises an empty tree language) — so `b11_isTraversable_is_vacuous` is
  no longer provable.

  **Walk-structured reconstruction — PROVEN (but NOT the full acceptance bijection, F4).**  A
  walk-structured execution (row labeling `lbl`, fanout column `fo`, `kroots ≥ 1` roots,
  height `h`, with the aggregate-BFS tiling `kroots + Sf fo h = h` + queue-validity `BFSValidF` —
  both obtainable from a `Walk.QGate` via `bfsValidF_of_qgate`/`SfF_tiling_of_qgate`, exactly as the
  `V_NockVMROM_forest` capstone does — arity bound, and per-row `Fcomp`/`Fmem`) reconstructs, via
  the inverse-BFS `Walk.reconForest`, to a forest of `RVTWithArity`-trees whose aggregate BFS labels
  are the committed rows (`nockvmrom_compute_complete`/`nockvmrom_memory_complete`, pure ASSEMBLY of
  `Walk.reconForest_RVT`/`reconForest_properArity`/`reconForest_labels`).  This is a genuine
  reconstruction of *walk-structured `F`-rows*, and with `ComputeLang`/`MemoryLang`/`φ` removed the
  surface rests on NO free-field `Equiv.refl`.  **It is `1-1*`, not the paper's full bijection:** it
  does not take an arbitrary `computeAccepts`/`memoryAccepts` witness to an RVT (an accepted trace
  need not be walk-structured; `computeReadout` is singleton-valued — `b12_s4_accepted_not_in_readout`).
  So S4 carries the sound inclusion + a walk-structured reconstruction; the full acceptance↔RVT
  bijection of `Def:traversable` remains the disclosed remaining bridge (F4).
-/

namespace Nock.NockVMROM

open Nock Nock.Framework Nock.Walk Nock.ComputeTable Nock.MemoryTable

/-- **S4 traversal data.**  The compute label space
    `State × DTcomp K` (arity `n_comp = 3`, single root), the memory label space `MState × DTmem K`
    (arity `n_mem = 2`, single root), and the two genuine walk recognisers `ComputeTable.Fcomp` and `MemoryTable.Fmem` as the labeling relations `F_i`/`F*_i`.
    Arities match the existing `Nock.Framework.nock_traversable` (compute 3, memory 2). -/
noncomputable instance nock_traversalModel (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    TraversalModel (Tag F K α β Ksz) (nmrMEF F K) where
  ComputeLabel := State × DTcomp K
  MemoryLabel := MState × DTmem K
  compArity := 3
  memArity := 2
  compRoots := 1
  memRoots := 1
  Fcomp := fun _ => ComputeTable.Fcomp (K := K)
  Fmem := fun _ => MemoryTable.Fmem (K := K)

/-- **Arity-`n` fanout pinning.**  Two nat bounds `a, b ≤ n` that agree on the `Fin n`-cutoffs
    (`∀ i : Fin n, i < a ↔ i < b`) are equal.  Used to recover the fanout binding
    `fo k = fanout (row k).1` from the state-defined dynamic-labeling conjunct of `Fcomp`/`Fmem`
    (which pins `fanout` against the child-slot occupancy) plus the arity bound. -/
theorem nat_eq_of_lt_iff_fin {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n)
    (h : ∀ i : Fin n, ((i : ℕ) < a ↔ (i : ℕ) < b)) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have hb' := (h ⟨a, lt_of_lt_of_le hlt hb⟩).mpr hlt
    simp only [lt_irrefl] at hb'
  · exact heq
  · have ha' := (h ⟨b, lt_of_lt_of_le hgt ha⟩).mp hgt
    simp only [lt_irrefl] at ha'

/-- **S4 COMPUTE COMPLETENESS — reverse inclusion `L_comp ⊆ L_RVT^{Fcomp,3}`, the
    inverse-BFS reconstruction half.**  Given a *walk-structured accepting compute execution* — a
    row labeling `lbl`, fanout column `fo`, `kroots ≥ 1` roots, height `h`, with the aggregate-BFS
    tiling `kroots + Sf fo h = h`, queue-validity `BFSValidF`, arity bound `fo ≤ 3`, the fanout
    binding `fo = fanoutComp ∘ state`, and the per-row `Fcomp`-recognition of each row against its
    inverse-BFS child slots — the reconstructed forest `Walk.reconForest` is a forest of trees in
    the EXACT arity-3 language `L_RVT^{Fcomp,3}` (`Walk.RVTWithArity Fcomp = RVT ∧ ProperArity 3`)
    whose aggregate breadth-first labels reproduce the committed rows `[lbl 1,…,lbl h]`.

    Pure ASSEMBLY of the already-proven inverse-BFS infrastructure: `Walk.reconForest_RVT`
    (per-tree `RVT` via the per-node `Fcon`), `Walk.reconForest_properArity` (per-node child count
    `≤ 3`), and `Walk.reconForest_labels` (the inverse-BFS round-trip).  `hF` is exactly the
    per-row `Fcomp` the walk capstone `V_NockVMROM(_forest)` establishes from each row's `Vcomp` +
    structure. -/
theorem nockvmrom_compute_complete {K : Type} [Field K] (fo : ℕ → ℕ)
    (lbl : ℕ → State × DTcomp K) {kroots h : ℕ} (hk : 1 ≤ kroots)
    (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ 3)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = fanoutComp (lbl i).1)
    (hF : ∀ i, 1 ≤ i → i ≤ h → ComputeTable.Fcomp (lbl i)
      (fun j : Fin 3 => if (j : ℕ) < fo i then some (lbl (firstCF kroots fo i + j)) else none)) :
    (∀ t ∈ Walk.reconForest kroots fo lbl h, Walk.RVTWithArity (ComputeTable.Fcomp (K := K)) t)
      ∧ (Walk.bfsForest (Walk.reconForest kroots fo lbl h)).map NTree.label
          = (List.range' 1 h).map lbl :=
  ⟨fun t ht => RVTWithArity.mk'
      (reconForest_RVT (comp_stateSep (K := K)) kroots fo lbl h hk hSf hvalid harity hfo hF t ht)
      (reconForest_properArity kroots fo lbl h hk hSf hvalid harity t ht),
    reconForest_labels kroots fo lbl h hk hSf hvalid⟩

/-- **S4 MEMORY COMPLETENESS — reverse inclusion `L_mem ⊆ L_RVT^{Fmem,2}`.**  The
    memory analogue of `nockvmrom_compute_complete` (arity `2`, `mem_stateSep`, `fanoutMem`): a
    walk-structured accepting memory execution reconstructs to a forest in the exact arity-2 language
    `L_RVT^{Fmem,2}` whose aggregate BFS labels are the committed rows.  Assembly of the same
    `Walk.reconForest_RVT`/`reconForest_properArity`/`reconForest_labels` infrastructure. -/
theorem nockvmrom_memory_complete {K : Type} [Field K] (fo : ℕ → ℕ)
    (lbl : ℕ → MState × DTmem K) {kroots h : ℕ} (hk : 1 ≤ kroots)
    (hSf : kroots + Sf fo h = h) (hvalid : BFSValidF kroots fo h) (harity : ∀ i, fo i ≤ 2)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = fanoutMem (lbl i).1)
    (hF : ∀ i, 1 ≤ i → i ≤ h → MemoryTable.Fmem (lbl i)
      (fun j : Fin 2 => if (j : ℕ) < fo i then some (lbl (firstCF kroots fo i + j)) else none)) :
    (∀ t ∈ Walk.reconForest kroots fo lbl h, Walk.RVTWithArity (MemoryTable.Fmem (K := K)) t)
      ∧ (Walk.bfsForest (Walk.reconForest kroots fo lbl h)).map NTree.label
          = (List.range' 1 h).map lbl :=
  ⟨fun t ht => RVTWithArity.mk'
      (reconForest_RVT (mem_stateSep (K := K)) kroots fo lbl h hk hSf hvalid harity hfo hF t ht)
      (reconForest_properArity kroots fo lbl h hk hSf hvalid harity t ht),
    reconForest_labels kroots fo lbl h hk hSf hvalid⟩

/-- **S4 traversability — exact `RVTWithArity` form.**  The
    compute language is recognised by the exact arity-3 RVT tree language `∏_{i<1} {t // RVTWithArity
    Fcomp t}` and the memory language by the exact arity-2 `∏_{i<1} {t // RVTWithArity Fmem t}`.  With the class's `ComputeLang`/`MemoryLang`/`φ` fields
    removed, there is NO free-field `Equiv.refl`: the `V_comp`/`V_mem` ↔ `RVT` *recognition* is
    carried entirely in BOTH directions — `recognizes_compute`/`recognizes_memory` (the sound
    inclusion `L_RVT ⊆ L_comp/L_mem`, `Fcomp`/`Fmem` embedding `Vcomp`/`Vmem`) AND
    `recognized_complete_compute`/`recognized_complete_memory` (the reverse inclusion
    `L_comp/L_mem ⊆ L_RVT` via the inverse-BFS `Walk.reconForest`). -/
noncomputable instance nock_isTraversable (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    @IsTraversable (Tag F K α β Ksz) _ (nmrMEF F K)
      (nock_traversalModel F K α β Ksz) (nock_uniqueMES F K α β Ksz) where
  -- Readout of a compute label `(state, (inp, pub, dec))` into the S1 program `(stmt, wit, io)`:
  -- the single compute row `[(inp, pub)]` with decided columns `[dec]` and empty IO.
  computeReadout := fun lbl => ([(lbl.2.1, lbl.2.2.1)], ([lbl.2.2.2], []), [])
  -- Readout of a memory label `(state, (inp, pub))` into the single memory row `[(inp, pub)]`.
  memoryReadout := fun lbl => ([(lbl.2.1, lbl.2.2)], [], [])
  -- Sound inclusion `L_RVT^{Fcomp,3} ⊆ L_comp`: `Fcomp lbl xout` embeds `Vcomp lbl.2.1 lbl.2.2.1
  -- lbl.2.2.2` (2nd conjunct), which is exactly the compute-verifier of the readout row.
  recognizes_compute := by
    rintro _ lbl _ hF
    exact ⟨List.Forall₂.cons hF.2.1 List.Forall₂.nil, rfl⟩
  -- Sound inclusion `L_RVT^{Fmem,2} ⊆ L_mem`: `Fmem lbl xout` embeds `Vmem lbl.2.1 lbl.2.2`.
  recognizes_memory := by
    rintro _ lbl _ hF
    refine ⟨?_, rfl⟩
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact hF.2.1
  -- Witness: `V_comp` accepts the readout of the concrete `Fcomp`-recognised leaf.
  compute_recognized := by
    obtain ⟨lbl, hlbl⟩ := Fcomp_nonvacuous (K := K)
    exact ⟨0, lbl, hlbl, List.Forall₂.cons hlbl.2.1 List.Forall₂.nil, rfl⟩
  -- Witness: `V_mem` accepts the readout of the concrete `Fmem`-recognised leaf.
  memory_recognized := by
    obtain ⟨lbl, hlbl⟩ := Fmem_nonvacuous (K := K)
    refine ⟨0, lbl, hlbl, ?_, rfl⟩
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact hlbl.2.1
  -- Completeness (reverse inclusion `L_comp ⊆ L_RVT^{Fcomp,3}`): the inverse-BFS reconstruction.
  -- The fanout binding `fo k = fanoutComp (lbl k).1` is RECOVERED from the per-row `Fcomp`'s
  -- state-defined dynamic-labeling conjunct (`.2.2.1`) + the arity bound (`nat_eq_of_lt_iff_fin`),
  -- then the reconstruction is discharged by `nockvmrom_compute_complete`.
  recognized_complete_compute := by
    rintro _ fo lbl kroots h hk hSf hvalid harity hF
    have hfo : ∀ k, 1 ≤ k → k ≤ h → fo k = fanoutComp (lbl k).1 := by
      intro k hk1 hkh
      have hiff := (hF k hk1 hkh).2.2.1
      have key : ∀ j : Fin 3, ((j : ℕ) < fanoutComp (lbl k).1 ↔ (j : ℕ) < fo k) := by
        intro j
        rw [hiff j]
        by_cases hc : (j : ℕ) < fo k <;> simp [hc]
      have hle : fanoutComp (lbl k).1 ≤ 3 := by cases (lbl k).1 <;> decide
      exact (nat_eq_of_lt_iff_fin hle (harity k) key).symm
    obtain ⟨hrvt, hlab⟩ := nockvmrom_compute_complete fo lbl hk hSf hvalid harity hfo hF
    exact ⟨Walk.reconForest kroots fo lbl h, hrvt, hlab⟩
  -- Completeness (reverse inclusion `L_mem ⊆ L_RVT^{Fmem,2}`): the memory analogue.
  recognized_complete_memory := by
    rintro _ fo lbl kroots h hk hSf hvalid harity hF
    have hfo : ∀ k, 1 ≤ k → k ≤ h → fo k = fanoutMem (lbl k).1 := by
      intro k hk1 hkh
      have hiff := (hF k hk1 hkh).2.2.1
      have key : ∀ j : Fin 2, ((j : ℕ) < fanoutMem (lbl k).1 ↔ (j : ℕ) < fo k) := by
        intro j
        rw [hiff j]
        by_cases hc : (j : ℕ) < fo k <;> simp [hc]
      have hle : fanoutMem (lbl k).1 ≤ 2 := by cases (lbl k).1 <;> decide
      exact (nat_eq_of_lt_iff_fin hle (harity k) key).symm
    obtain ⟨hrvt, hlab⟩ := nockvmrom_memory_complete fo lbl hk hSf hvalid harity hfo hF
    exact ⟨Walk.reconForest kroots fo lbl h, hrvt, hlab⟩

end Nock.NockVMROM

#print axioms Nock.NockVMROM.nock_traversalModel
#print axioms Nock.NockVMROM.nock_isTraversable
#print axioms Nock.NockVMROM.nockvmrom_compute_complete
#print axioms Nock.NockVMROM.nockvmrom_memory_complete
