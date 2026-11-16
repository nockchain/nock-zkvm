/-
  NockvmE2E/Exec/J8ChipsK.lean   (the kernel half of hop 0)

  For each literal `lit` of `Exec/J8Chips.lean` with emitter spec `s` (`Nock.Emit.{jet,atom,cellKW,compute}Spec`, `walkJ8SpecAt k`, `walkAtomSpecAt k`):
    `tieB s lit = true`  (by `decide +kernel`, one theorem per literal, each in its own module `J8ChipsK_<name>.lean`: the all-in-one module was OOM-killed at 20 GB),
  where `tieB` says: the emitted DAG of `s` parses to a chip `c0` (`chipOfDag`, = `toEx` of the shared table and of the six root buckets in the loader's order), and
  `(verifierChipT c0 jDers jMeta).1` has the same `shared` array, the same constraint expressions and the same `baseCols`/`width` as `lit`.
  `chipEqB_tie`: a loaded chip that the exe accepts against `lit` (`chipEqB`) therefore has `shared`/`cons.map e` equal to those of `verifierChipT (toEx (emitDag s))`.
  NOT tied (checked by the exe only against the literal): `kind`/`round`/`deg` of the constraints and `colRound` (the verifier never reads them).
-/
import NockvmE2E.Exec.J8Chips
import NockvmE2E.Emit.Tie
import NockvmE2E.Emit.ChipsWalk

set_option autoImplicit false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.J8ChipsK
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.VC NockvmE2E.Exec.J8Chips NockvmE2E.Emit Nock.Emit

/-- the chip a DAG document parses to: shared = `toEx` of the table, constraints = `toEx` of the six buckets in the emitter's (= the loader's) order -/
def chipOfDag (d : DagGates) : Option Chip := do
  let sh ← d.defs.mapM toEx
  let cs ← (d.base ++ d.ext ++ d.mixed ++ d.ext1 ++ d.ext3 ++ d.eqc).mapM toEx
  pure { id := "", shared := sh.toArray, cons := (cs.map fun e => ({ kind := 0, round := 0, deg := 0, e := e } : Con)).toArray,
         colRound := #[], sharedK := #[], consK := #[], baseCols := 0, width := 0 }

/-- the comparison, on LISTS (the kernel evaluates `Array.map`/`++` by well-founded recursion on indices, which is what OOM-killed the all-`Array` version for
cell/atom/compute; `tieB_spec` transfers the list equalities to `verifierChipT`'s arrays). -/
def tieB (s : TSpec) (lit : Chip) : Bool :=
  match chipOfDag (emitDag s) with
  | none => false
  | some c0 =>
    let dnS := dnSeen jDers jMeta
    let f := fOf (orderOf jMeta) (drefOf jDers dnS.2)
    let m := dnS.1.size
    exListEqB (dnS.1.toList ++ c0.shared.toList.map (mapExT f m)) lit.shared.toList &&
    exListEqB (c0.cons.toList.map (fun c => mapExT f m c.e)) (lit.cons.toList.map (·.e)) &&
    lit.baseCols == s.baseCols.sum && lit.width == s.baseCols.sum + 3 * s.extCols.sum

theorem exListEqB_iff : ∀ (a b : List Tr.Ex), exListEqB a b = true ↔ a = b
  | [], [] => by simp [exListEqB]
  | [], _ :: _ => by simp [exListEqB]
  | _ :: _, [] => by simp [exListEqB]
  | x :: xs, y :: ys => by
    simp only [exListEqB, Bool.and_eq_true, exEqB_iff, exListEqB_iff xs ys, List.cons.injEq]

theorem exArrEqB_iff (a b : Array Tr.Ex) : exArrEqB a b = true ↔ a = b := by
  unfold exArrEqB; rw [exListEqB_iff]; exact ⟨Array.ext', fun h => by rw [h]⟩

theorem conListEqB_map : ∀ (a b : List Con), conListEqB a b = true → a.map (·.e) = b.map (·.e)
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp [conListEqB] at h
  | _ :: _, [] => fun h => by simp [conListEqB] at h
  | x :: xs, y :: ys => fun h => by
    simp only [conListEqB, Bool.and_eq_true, conEqB] at h
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨(exEqB_iff _ _).1 h.1.2, conListEqB_map xs ys h.2⟩

theorem chipEqB_shared (a b : Chip) (h : chipEqB a b = true) : a.shared = b.shared := by
  unfold chipEqB at h
  simp only [Bool.and_eq_true] at h
  exact (exArrEqB_iff _ _).1 h.1.1.1.1.2

theorem chipEqB_cons_e (a b : Chip) (h : chipEqB a b = true) : a.cons.map (·.e) = b.cons.map (·.e) := by
  unfold chipEqB at h
  simp only [Bool.and_eq_true] at h
  have := conListEqB_map _ _ h.1.1.1.2
  apply Array.ext'
  simpa using this

theorem tieB_spec (s : TSpec) (lit : Chip) (h : tieB s lit = true) :
    ∃ c0, chipOfDag (emitDag s) = some c0 ∧ (verifierChipT c0 jDers jMeta).1.shared = lit.shared ∧
      (verifierChipT c0 jDers jMeta).1.cons.map (·.e) = lit.cons.map (·.e) ∧
      lit.baseCols = s.baseCols.sum ∧ lit.width = s.baseCols.sum + 3 * s.extCols.sum := by
  unfold tieB at h
  cases hc : chipOfDag (emitDag s) with
  | none => simp [hc] at h
  | some c0 =>
    simp only [hc, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have e1 := (exListEqB_iff _ _).1 h1
    have e2 := (exListEqB_iff _ _).1 h2
    refine ⟨c0, rfl, ?_, ?_, h3, h4⟩
    · apply Array.ext'
      simpa [verifierChipT, Array.toList_append, Array.toList_map] using e1
    · apply Array.ext'
      simpa [verifierChipT, Array.toList_map, List.map_map, Function.comp_def] using e2

/-- hop 0 for one table: a chip the exe accepts against the literal equals the verifier chip of the emitted DAG -/
theorem chipEqB_tie (s : TSpec) (lit c : Chip) (h1 : tieB s lit = true) (h2 : chipEqB c lit = true) :
    ∃ c0, chipOfDag (emitDag s) = some c0 ∧ c.shared = (verifierChipT c0 jDers jMeta).1.shared ∧
      c.cons.map (·.e) = (verifierChipT c0 jDers jMeta).1.cons.map (·.e) := by
  obtain ⟨c0, hc, hs, hcons, -, -⟩ := tieB_spec s lit h1
  exact ⟨c0, hc, by rw [chipEqB_shared c lit h2, hs], by rw [chipEqB_cons_e c lit h2, hcons]⟩

end NockvmE2E.Exec.J8ChipsK

#print axioms NockvmE2E.Exec.J8ChipsK.chipEqB_tie
#print axioms NockvmE2E.Exec.J8ChipsK.tieB_spec
