/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9.lean

Trunk J9B-CORNER keyed the proofs' honest atom-table data (`ComplJ8Data.j8DataOf`) by the
  per-component tail pointer `ComplJ8Data.ptrP` (`FirstC`, `StopE`).  `V1J8/GenAtom` §5b ports the executable
  generators (`genJ8A`, `V1J9/GenJ9.genJ9A`) to it; this module closes the transcription gap of the changed part:
  * `stopE_iff` / `firstC_iff`: the executable stop edges `Gen.stopEdges` and the decided `Gen.firstCE` are
    `StopE` / `FirstC` at Goldilocks;
  * **`ptrE_eq`**: `Gen.ptrE acsL (Gen.stopEdges rows) n = ComplJ8Data.ptrP P acsL rows n` (every `acsL`, `rows`, `n`);
  * **`infoOfE_eq`**: the generator's inc / conversion data `Gen.infoOfE` = `ComplJ8Data.infoOfP`;
  * `sxE_eq`, `mvE_getD`: the compute's pair spine serials and the atom cells' validity multiplicity;
  * **`genJ9A_pointer_data`**: on a jet-free run at Goldilocks, the pointer, `info` and `pd` that `genJ9A` / `genJ8A`
    build are `j8DataOf`'s (`ptrP` at its `acs` / `rows`, its `info`, its `pd`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.V1J8.Gen (P stopsOfL stopEdges firstCE ptrE keyE valROfE incChainE infoOfE sxE mvE incOps combP idxOf
  lastIdxOf hdN' tlN' atomV AInfo)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)

/-! ## 1. Stop edges and the FIRST component -/

theorem mem_stopsOfL {l : List ℕ} {x : ℕ} : x ∈ stopsOfL l ↔
    ∃ d, l.drop d = x :: Nock.Atoms.limbs P ∧ x ≠ Nock.Atoms.B - 1 ∧
      ∀ i < d, (l.drop i).headD 0 = Nock.Atoms.B - 1 := by
  unfold stopsOfL
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨d, -, h⟩
    revert h
    cases hd : l.drop d with
    | nil => intro h; cases h
    | cons y t =>
      intro h
      by_cases hc : t = Nock.Atoms.limbs P ∧ y ≠ Nock.Atoms.B - 1 ∧
          (List.range d).all (fun i => (l.drop i).headD 0 == Nock.Atoms.B - 1) = true
      · simp only [if_pos hc, Option.some.injEq] at h
        subst h
        obtain ⟨ht, hy, hall⟩ := hc
        refine ⟨d, by rw [hd, ht], hy, fun i hi => ?_⟩
        have := List.all_eq_true.mp hall i (List.mem_range.mpr hi)
        simpa using this
      · simp only [if_neg hc] at h; cases h
  · rintro ⟨d, hd, hx, hall⟩
    refine ⟨d, ?_, ?_⟩
    · rw [List.mem_range]
      have h1 : 0 < (l.drop d).length := by rw [hd]; simp
      rw [List.length_drop] at h1; omega
    · rw [hd]
      have hc : Nock.Atoms.limbs P = Nock.Atoms.limbs P ∧ x ≠ Nock.Atoms.B - 1 ∧
          (List.range d).all (fun i => (l.drop i).headD 0 == Nock.Atoms.B - 1) = true :=
        ⟨rfl, hx, List.all_eq_true.mpr fun i hi => by simpa using hall i (List.mem_range.mp hi)⟩
      exact if_pos hc

/-- **The executable stop edges are `StopE`** (Goldilocks). -/
theorem stopE_iff (rows : Array RowNX) (x : ℕ) : ComplJ8Data.StopE P rows x ↔ x ∈ stopEdges rows := by
  unfold ComplJ8Data.StopE stopEdges
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨vc, hvc, hne, hd⟩
    exact ⟨vc, hvc, by rw [if_neg hne]; exact mem_stopsOfL.mpr hd⟩
  · rintro ⟨vc, hvc, hx⟩
    by_cases hne : vc.1 + 1 = P
    · rw [if_pos hne] at hx; simp at hx
    · rw [if_neg hne] at hx; exact ⟨vc, hvc, hne, mem_stopsOfL.mp hx⟩

/-- `firstCE` decides "every edge below `x` is in `es`". -/
theorem firstCE_iff (es : List ℕ) (x : ℕ) : firstCE es x = true ↔ ∀ y < x, y ∈ es := by
  unfold firstCE
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨-, h⟩ y hy
    simpa using h y (List.mem_range.mpr hy)
  · intro h
    refine ⟨?_, fun y hy => by simpa using h y (List.mem_range.mp hy)⟩
    have hsub : (List.range x).toFinset ⊆ es.toFinset := by
      intro y hy
      rw [List.mem_toFinset, List.mem_range] at hy
      exact List.mem_toFinset.mpr (h y hy)
    have h1 := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range] at h1
    exact h1.trans (List.toFinset_card_le es)

/-- **`FirstC` decided** (Goldilocks). -/
theorem firstC_iff (rows : Array RowNX) (x : ℕ) :
    ComplJ8Data.FirstC P rows x ↔ firstCE (stopEdges rows) x = true := by
  rw [firstCE_iff]
  exact forall_congr' fun y => imp_congr_right fun _ => stopE_iff rows y

/-! ## 2. The pointer, the inc data, the pair serials, `mv` -/

/-- **The executable pointer is the proofs' pointer** (`ptrE` at the run's stop edges = `ComplJ8Data.ptrP`). -/
theorem ptrE_eq (acsL : List Noun) (rows : Array RowNX) (n : Noun) :
    ptrE acsL (stopEdges rows) n = ComplJ8Data.ptrP P acsL rows n := by
  have hiff : (tlN' n = combP ∧ firstCE (stopEdges rows) (atomV (hdN' n)) = false) ↔
      (tlN' n = ComplJ8Data.combPP P ∧ ¬ ComplJ8Data.FirstC P rows (atomV (hdN' n))) := by
    rw [firstC_iff, Bool.not_eq_true]; exact Iff.rfl
  unfold ptrE ComplJ8Data.ptrP
  by_cases h : tlN' n = combP ∧ firstCE (stopEdges rows) (atomV (hdN' n)) = false
  · rw [if_pos h, if_pos (hiff.mp h)]; rfl
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem ptrE_eq' (acsL : List Noun) (rows : Array RowNX) :
    ptrE acsL (stopEdges rows) = ComplJ8Data.ptrP P acsL rows := funext (ptrE_eq acsL rows)

theorem incChainE_eq (acsL : List Noun) (key ptr : Noun → ℕ) (f : ℕ) :
    ∀ (ns os : List Noun) (a : Array AInfo),
      incChainE acsL key ptr f ns os a = ComplJ8Data.incChainK acsL key ptr f ns os a := by
  induction f with
  | zero => intro ns os a; rfl
  | succ f ih =>
    intro ns os a
    cases ns with
    | nil => rfl
    | cons n ns =>
      cases os with
      | nil => rfl
      | cons o os =>
        have hv : valROfE ptr o = ComplJ8Data.valROfK ptr o := rfl
        simp only [incChainE, ComplJ8Data.incChainK, hv, ih]

/-- **The generator's inc / conversion data is the proofs'** (`infoOfE` at the pointer = `ComplJ8Data.infoOfP`). -/
theorem infoOfE_eq (acsL : List Noun) (rows : Array RowNX) :
    infoOfE acsL (ptrE acsL (stopEdges rows)) rows = ComplJ8Data.infoOfP P acsL rows := by
  have hk : keyE acsL = ComplJ8Data.keyP P acsL := rfl
  have hc : incChainE acsL (keyE acsL) (ComplJ8Data.ptrP P acsL rows) =
      ComplJ8Data.incChainK acsL (ComplJ8Data.keyP P acsL) (ComplJ8Data.ptrP P acsL rows) := by
    funext f ns os a; rw [hk]; exact incChainE_eq _ _ _ f ns os a
  unfold infoOfE ComplJ8Data.infoOfP
  rw [ptrE_eq', hc]
  rfl

/-- **The compute's pair spine serials are the proofs'** (`sxE` at the pointer = `ComplJ8Data.sxPP`). -/
theorem sxE_eq (acsL : List Noun) (rows : Array RowNX) (a e : ℕ) :
    sxE (ptrE acsL (stopEdges rows)) a e = ComplJ8Data.sxPP P acsL rows a e :=
  ptrE_eq acsL rows _

/-- **The atom cells' validity multiplicity** (`mvE`, read at a row) is `ComplJ8Of.mvA`'s count at the pointer. -/
theorem mvE_getD (acsL : List Noun) (rows : Array RowNX) {j : ℕ} (hj : j < acsL.length) :
    (mvE acsL (ptrE acsL (stopEdges rows))).getD j 0 =
      (acsL.filter fun y => (hdN' y).isCell && idxOf acsL (hdN' y) == j).length +
        (acsL.filter fun y => (tlN' y).isCell && ComplJ8Data.ptrP P acsL rows y == j).length := by
  rw [ptrE_eq']
  simp [mvE, Array.getD_eq_getD_getElem?, hj]

/-! ## 3. At the run: `genJ9A` / `genJ8A`'s pointer data is `j8DataOf`'s -/

section Run
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- The atom cell list `genJ9A` / `genJ8A` build from a run's rows. -/
def acsRun (s f r : Noun) (t : NTree SkelX) : List Noun :=
  Nock.V1J8.Gen.acsOfD (Nock.V1J8.Gen.bigsOf (Nock.V1J8.Gen.rootsOf ⟨s, f, r⟩ (ComplJ8Data.rowsOfT t))
    (ComplJ8Data.rowsOfT t)) ((incOps (ComplJ8Data.rowsOfT t)).any fun x => x.1 + 1 = P)

/-- **`genJ9A`'s pointer data is the run's** (Goldilocks, a jet-free run, as `genJ9A` requires): the pointer
`ptrE acsL (stopEdges rows)` that `genJ9A` / `genJ8A` route everywhere is `ptrP` at `j8DataOf`'s `acs` and `rows`, and
the inc / conversion data `infoOfE` and the compute's limb data `pdX (sxE …)` they build are `j8DataOf`'s `info` and
`pd`. -/
theorem genJ9A_pointer_data (hpG : p = P) (hnc : Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t) = []) :
    (∀ n, ptrE (acsRun s f r t) (stopEdges (ComplJ8Data.rowsOfT t)) n =
      ComplJ8Data.ptrP p (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).rows n) ∧
    infoOfE (acsRun s f r t) (ptrE (acsRun s f r t) (stopEdges (ComplJ8Data.rowsOfT t))) (ComplJ8Data.rowsOfT t) =
      (j8DataOf p Rg Rt hgen).info ∧
    HonestPairX.pdX (sxE (ptrE (acsRun s f r t) (stopEdges (ComplJ8Data.rowsOfT t)))) =
      (j8DataOf p Rg Rt hgen).pd := by
  subst hpG
  have hacs : acsRun s f r t = (j8DataOf P Rg Rt hgen).acs :=
    (ComplJ9BClosed.genJ9A_data Rt hgen rfl hnc).2.2
  have hrows : (j8DataOf P Rg Rt hgen).rows = ComplJ8Data.rowsOfT t := rfl
  have hinfo : (j8DataOf P Rg Rt hgen).info =
      ComplJ8Data.infoOfP P (j8DataOf P Rg Rt hgen).acs (ComplJ8Data.rowsOfT t) := rfl
  have hpd : (j8DataOf P Rg Rt hgen).pd =
      HonestPairX.pdX (ComplJ8Data.sxPP P (j8DataOf P Rg Rt hgen).acs (ComplJ8Data.rowsOfT t)) := rfl
  rw [hacs, hrows, hinfo, hpd]
  refine ⟨fun n => ptrE_eq _ _ n, infoOfE_eq _ _, ?_⟩
  congr 1
  funext a e
  exact sxE_eq _ _ a e

end Run

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.stopE_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.firstC_iff
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.ptrE_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.infoOfE_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.sxE_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.mvE_getD
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9.genJ9A_pointer_data
