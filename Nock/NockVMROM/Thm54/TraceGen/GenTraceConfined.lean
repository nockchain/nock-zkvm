/-
  Nock/NockVMROM/Thm54/TraceGen/GenTraceConfined.lean

  **The Λ-confinement premise, decidable, and its projection to `RowLeafWindow`.**

  Lean already mirrors that shape — `Trace.FiniteΛ Λ F := Finite F ∧
  size F ≤ Λ` (`Trace.lean:352`), `FiniteTransitionΛ` (`:356`).

  So the object to build is not a growth invariant but the **generator-side image of that membership
  condition**.  It is `TraceConfined` below.

  **Why a derivation is not available, in one line.**  `cons` duplicates its subject, so a step can double, and the only
  uniform bound is `2^t · |t₀|`.  Confining a `t`-step run to `Λ` leaves by that route would need
  `t ≤ log₂(Λ / |t₀|)`; the matmul program runs 401 steps at `Λ = 2048`, where the worst case would
  demand `Λ ≥ 2^401`.  Real traces grow nowhere near worst case, which is exactly why the paper
  makes confinement a membership condition and not a theorem.

  **What this module buys.**  `TraceConfined` carries a `Decidable` instance, and discharging it at a
  concrete program is a mechanical measurement rather than a proof about the construction — which is
  precisely the program family the construction has: programs *measured* to fit in `Λ`, i.e. members
  of `NockVM^Λ`.

  **How the measurement is actually discharged, precisely.**  Not by `decide`.  `bfsForest` is
  defined by well-founded recursion and the released carriers are `GaloisField p 3`, whose `Field`
  instance is noncomputable, so the `Decidable` instance exists as a term but does **not** reduce at
  a live configuration.  The discharge is a precomputed row-list equation (`dot_air_bfsRows`) plus
  kernel `Nat.ble` reduction per row — see `Batch164.dot_traceConfined`.  Still mechanical, still a
  measurement, but `decide` is the wrong word and earlier drafts of this docstring used it.  The projection then upgrades it to
  the full `RowLeafWindow` (`CensusExtraClosure.lean:1306`), which additionally constrains all nine
  subformula slots, using the fact that a row's subformula slots **are** its children's nouns
  (`childrenMatchSf`, `GenAirOrder.lean:175`) together with the padding value beyond the fan-out.

  The premise is therefore strictly weaker than the conclusion, and the gap between them is where the
  structure of the generated tree does the work.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenLeafWindow
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderChildLink
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenTraceConfined

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.CensusExtraClosure
open ComputeTable

variable {K : Type} [Field K]

/-! ## The premise -/

instance (Λ : ℕ) (g : GenComputeRow K) : Decidable (RowNounsConfined Λ g) := by
  unfold RowNounsConfined; infer_instance

instance (Λ : ℕ) (t : NTree (GenComputeRow K)) : Decidable (TraceConfined Λ t) := by
  unfold TraceConfined; infer_instance

/-! ## The projection -/

/-- **`RowLeafWindow` at every node, from Λ-confinement.**

The row's own three nouns come straight from the premise.  Each subformula slot within the fan-out
is a child's noun (`childrenMatchSf`), so the premise applies to it *at that child*; beyond the
fan-out `skeletonSubformula` returns the padding `atom 0`, whose one leaf fits any `Λ ≥ 1`.

No growth arithmetic anywhere: the premise supplies every bound and the tree structure routes them. -/
theorem leafWindow_of_traceConfined {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {t : NTree (GenComputeRow K)}
    (hlink : AirLinked t)
    (hfan : ∀ u, InTree t u → u.children.length = fanoutComp u.label.skel.state)
    (hconf : TraceConfined Λ t) :
    ∀ u, InTree t u → RowLeafWindow Λ u.label.skel := by
  intro u hu
  obtain ⟨hs, hf, he⟩ := confined_inTree hconf hu
  refine ⟨hs, hf, he, ?_⟩
  intro i slot
  by_cases hi : (i : ℕ) < fanoutComp u.label.skel.state
  · -- inside the fan-out: the slot is a child's noun, and the child is confined too
    have hlen : (i : ℕ) < u.children.length := by rw [hfan u hu]; exact hi
    have hmatch := childrenMatchSf_of_AirLinked (AirLinked_of_inTree hlink hu) i hlen
    have hchild : InTree t (u.children[(i : ℕ)]'hlen) :=
      InTree_trans hu (InTree.sub (List.getElem_mem hlen) (InTree.here _))
    obtain ⟨cs, cf, ce⟩ := confined_inTree hconf hchild
    cases slot with
    | subject => rw [← hmatch.1]; exact cs
    | formula => rw [← hmatch.2.1]; exact cf
    | result => rw [← hmatch.2.2]; exact ce
  · -- beyond the fan-out: padding
    simp only [P8Census.skeletonSubformula, dif_neg hi]
    exact atom_leaves_le hΛ 0

/-! ## The generic instance

For any accepted program at the AIR ordering — the ordering every live configuration commits — both
structural side conditions come from the generator, leaving only the measured premise. -/

/-- **`RowLeafWindow` for any accepted program, given only Λ-confinement.**

`AirLinked` and the fan-out equality are supplied by the generator; the caller supplies the
measurement (a row-list equation plus `Nat.ble` reduction, not `decide` — see the module docstring). -/
theorem genComputeSkeleton_leafWindow_air {Λ : ℕ} (hΛ : 1 ≤ Λ)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hconf : TraceConfined Λ (airReorder t)) :
    ∀ u, InTree (airReorder t) u → RowLeafWindow Λ u.label.skel :=
  leafWindow_of_traceConfined hΛ
    (airLinked_airReorder_of_gen (p := (t, result)) h)
    (airReorder_inTree_fanout (fun v hv => genComputeSkeleton_inTree_fanout h v hv))
    hconf

/-! ## §1 `hΛ` is `TraceConfined`, not a sixth binder

That is a **membership**
measurement, not a growth
invariant: `cons` (`:1075`) doubles, and no lemma of the paper preserves
length.  The Lean image of the measurement is the max of the three
per-row noun leaf counts.  `traceConfined_of_leafBound` turns it into
`TraceConfined`; the converse is `leafBound_of_traceConfined`.  Neither
claims `∀ program, TraceConfined` without a window.  Proving the numeric
inequality at a concrete program still uses the opcode combinators
(`confined_gen_op0` / … / slam) — that is a spine, not a generic lift. -/

theorem foldl_sup_le_aux {α : Type} (l : List α) (f : α → ℕ)
    (acc Λ : ℕ) (hacc : acc ≤ Λ) (h : ∀ x ∈ l, f x ≤ Λ) :
    l.foldl (fun a x => a ⊔ f x) acc ≤ Λ := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons a rest ih =>
    exact ih (acc ⊔ f a) (max_le hacc (h a (List.mem_cons.mpr (Or.inl rfl))))
      (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

theorem foldl_sup_le {α : Type} (l : List α) (f : α → ℕ) {Λ : ℕ}
    (h : ∀ x ∈ l, f x ≤ Λ) :
    l.foldl (fun acc x => acc ⊔ f x) 0 ≤ Λ :=
  foldl_sup_le_aux l f 0 Λ (Nat.zero_le _) h

/-- Alias: the same fact under the §1 name. -/
theorem traceConfined_of_hΛ {Λ : ℕ} {t : NTree (GenComputeRow K)}
    (hΛ : programLeafBound t ≤ Λ) : TraceConfined Λ t :=
  traceConfined_of_leafBound hΛ

theorem leafBound_of_traceConfined {Λ : ℕ} {t : NTree (GenComputeRow K)}
    (h : TraceConfined Λ t) : programLeafBound t ≤ Λ :=
  foldl_sup_le (bfsRows t) rowNounsBound (fun g hg =>
    (rowNounsConfined_iff_bound.mp (h g hg)))

theorem traceConfined_iff_leafBound {Λ : ℕ} {t : NTree (GenComputeRow K)} :
    TraceConfined Λ t ↔ programLeafBound t ≤ Λ :=
  ⟨leafBound_of_traceConfined, traceConfined_of_leafBound⟩

/-- A nonempty tree's window numeral is at least 1, so `leafBound ≤ Λ`
gives the padding `1 ≤ Λ` that `RowLeafWindow` wants. -/
theorem one_le_of_leafBound {Λ : ℕ} {t : NTree (GenComputeRow K)}
    (hrows : 0 < (bfsRows t).length) (h : programLeafBound t ≤ Λ) :
    1 ≤ Λ := by
    have hg : (bfsRows t)[0] ∈ bfsRows t := List.getElem_mem hrows
    have hb := foldl_sup_le_of_le (bfsRows t) rowNounsBound h (bfsRows t)[0] hg
    have hpos : 1 ≤ rowNounsBound (bfsRows t)[0] :=
      le_trans (leaves_pos (bfsRows t)[0].skel.subject)
        (le_trans (le_max_left _ _) (le_max_left _ _))
    exact le_trans hpos hb

theorem one_le_of_traceConfined {Λ : ℕ} {t : NTree (GenComputeRow K)}
    (hrows : 0 < (bfsRows t).length) (h : TraceConfined Λ t) : 1 ≤ Λ :=
  one_le_of_leafBound hrows (leafBound_of_traceConfined h)

/-- Every tree has a BFS row (the root).  Same fact as
`GenSemanticLmIO.lean::bfsRows_length_pos` (F-6); kept as a thin alias so
this module does not import that file. -/
theorem bfsRows_pos (t : NTree (GenComputeRow K)) : 0 < (bfsRows t).length := by
  have h1 : 1 ≤ t.size := by cases t with | node _ _ => simp [NTree.size]
  rw [bfsRows_length, bfsForest_length,
    show totalSize [t] = t.size by simp [totalSize]]
  omega

/-- Padding `1 ≤ Λ` from the §1 window alone -/
theorem one_le_of_hΛ_conf {Λ : ℕ} {t : NTree (GenComputeRow K)}
    (h : TraceConfined Λ t) : 1 ≤ Λ :=
  one_le_of_traceConfined (bfsRows_pos t) h

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.confined_inTree
#print axioms Nock.NockVMROM.Thm54.TraceGen.leafWindow_of_traceConfined
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_leafWindow_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.traceConfined_of_leafBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.traceConfined_of_hΛ
#print axioms Nock.NockVMROM.Thm54.TraceGen.leafBound_of_traceConfined
#print axioms Nock.NockVMROM.Thm54.TraceGen.traceConfined_iff_leafBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.one_le_of_leafBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.one_le_of_traceConfined
#print axioms Nock.NockVMROM.Thm54.TraceGen.one_le_of_hΛ_conf
