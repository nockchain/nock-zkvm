/-
  Nock/NockVMROM/Thm54/ActiveFingerprintScan.lean

  The strict contract is a two-phase discipline:

  1. before `z`, the prover fixes `StrictCommitment.SkeletonCommitment` and it passes the
     seed-independent `CanonicalCommitmentCheck`;
  2. after `z`, *every active field fingerprint* of the committed arrays is checked to equal
     `GlobalCarryRecognizer.enc z` of the corresponding **pre-committed** noun.

  This module is phase 2.  It reuses the *same* address enumeration as phase 1
  (`StrictCommitment.activeComputeSlotAddresses` / `activeMemorySlotAddresses`), so "the scan covers
  exactly the active slots" is a fact about one enumeration, not a coincidence between two.

  Three things are proved:

  * **enumeration completeness** — every active address of every commonly-indexed row contributes a
    scanned `(committed noun, committed fingerprint)` pair (`mem_computeRowSlots`,
    `mem_activeComputeSlots_getElem`, `scan_covers_all_compute_rows`);
  * **inactive-slot exclusion** — a padding address is not scanned
    (`inactive_compute_slot_not_scanned`), at the level of *addresses*.  Value-level exclusion is
    deliberately **not** claimed: two distinct active slots may legitimately carry equal
    fingerprints, so "this field element is not in the scan" is not a true statement about a padding
    slot;
  * **reconstruction at the characteristic** — passing the scan with a canonical commitment makes
    every scanned fingerprint an `ActiveRealization` (Packet 2A), hence `FPRealized` and hence a
    passer of `BoundGates.LeafBoundGate`, with pair-local `SepSeed` uniqueness and **no** global
    bounded-domain injectivity premise (`scanned_activeRealization`, `scanned_noun_unique`).

  ## Honest scope, and the exactly-named residuals

  * The direction proved here is `BindsAt ⟹ scan passes` (`activeFingerprintChecksOn_of_bindsAt`)
    together with `scan passes + canonical commitment ⟹ per-slot realization`.  The **converse**,
    "raw acceptance forces the scan to pass", is *not* proved and *not* assumed.  Nothing in
    this module assumes acceptance.
  * The fingerprint payloads scanned here live in `R.exec` — the raw family's committed
    configuration/execution arrays — because that is where the current raw architecture stores the
    compute/memory `Pub`/`Dec` fingerprints; `RawMessage` itself carries the table/walk/IO auxiliary
    columns.  `ActiveFingerprintChecks … msg` is therefore defined as `ActiveFingerprintChecksOn` on
    `msg`'s own family, which is the honest reading of "the raw message's committed fingerprint".
  * Row pairing is by `List.zip`, which truncates.  Completeness is consequently stated for indices
    below both lengths, and `scan_covers_all_compute_rows` upgrades it to *all* committed rows under
    the row-count agreement that `List.Forall₂` (hence `BindsAt`) already supplies.
-/

import Nock.NockVMROM.Thm54.SkeletonCommitment
import Nock.NockVMROM.Thm54.RawVerifier
import Nock.NockVMROM.Thm54.StrictRawReconstruction
import Nock.NockVMROM.Thm54.FPDecoder

namespace Nock.NockVMROM.Thm54.ActiveFingerprintScan

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictCommitment

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## List plumbing for the zipped row pairing -/

private theorem rel_of_mem_zip {α β : Type} {Rel : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ Rel l₁ l₂ →
      ∀ {x : α} {y : β}, (x, y) ∈ List.zip l₁ l₂ → Rel x y := by
  intro l₁ l₂ h
  induction h with
  | nil => intro x y hxy; simp at hxy
  | cons hhead htail ih =>
      intro x y hxy
      rw [List.zip_cons_cons, List.mem_cons] at hxy
      rcases hxy with heq | hrest
      · rw [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact hhead
      · exact ih hrest

private theorem getElem_mem_zip {α β : Type} :
    ∀ (l₁ : List α) (l₂ : List β) (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
      (l₁[i], l₂[i]) ∈ List.zip l₁ l₂
  | [], _, _, h₁, _ => absurd h₁ (by simp)
  | _ :: _, [], _, _, h₂ => absurd h₂ (by simp)
  | _ :: _, _ :: _, 0, _, _ => by simp
  | _ :: as, _ :: bs, i + 1, h₁, h₂ => by
      simp only [List.zip_cons_cons, List.mem_cons, List.getElem_cons_succ]
      exact Or.inr (getElem_mem_zip as bs i (by simpa using h₁) (by simpa using h₂))

/-! ## Committed fingerprints at a slot address -/

/-- The committed compute fingerprint at one slot address.  These are precisely the fingerprint
positions related by `SemanticStrategy.BindComputeRow`. -/
def computeSlotFP (row : ComputeTable.State × ComputeTable.DTcomp K) :
    ComputeSlotAddress → ComputeTable.FP K
  | .subject => row.2.2.1.s
  | .formula => row.2.2.1.f
  | .evaluation => row.2.2.1.e
  | .dec slot => decFP row.2.2.2 slot
  | .sub i slot => tripleFP (computeSubformulaFPs row.2.2.1 i) slot
  | .memRec i slot => memRecFP (computeMemRec row.2.2.1 i) slot

/-- The committed memory fingerprint at one slot address, matching
`SemanticStrategy.BindMemoryRow`. -/
def memorySlotFP (row : MemoryTable.MState × MemoryTable.DTmem K) :
    MemorySlotAddress → ComputeTable.FP K
  | .parent => row.2.2.pt.noun
  | .child i => (memoryChildCell row.2.2 i).noun
  | .memRec slot => memRecFP row.2.2.mem slot

/-! ## The per-row scan -/

/-- Every `(pre-committed noun, committed fingerprint)` pair of one compute row, at exactly the
addresses the *committed* state makes active. -/
def computeRowSlots (s : ComputeRowSkeleton)
    (row : ComputeTable.State × ComputeTable.DTcomp K) :
    List (Noun × ComputeTable.FP K) :=
  (activeComputeSlotAddresses s.state).map
    (fun a => (computeSlotNoun s a, computeSlotFP row a))

/-- Memory analogue of `computeRowSlots`. -/
def memoryRowSlots (s : MemoryRowSkeleton)
    (row : MemoryTable.MState × MemoryTable.DTmem K) :
    List (Noun × ComputeTable.FP K) :=
  (activeMemorySlotAddresses s.state).map
    (fun a => (memorySlotNoun s a, memorySlotFP row a))

omit [Field K] in
/-- **Row-local enumeration completeness.**  Every active compute address is scanned. -/
theorem mem_computeRowSlots (s : ComputeRowSkeleton)
    (row : ComputeTable.State × ComputeTable.DTcomp K)
    {a : ComputeSlotAddress} (ha : computeSlotActive s.state a = true) :
    (computeSlotNoun s a, computeSlotFP row a) ∈ computeRowSlots s row :=
  List.mem_map_of_mem ((mem_activeComputeSlotAddresses_iff _ a).2 ha)

omit [Field K] in
/-- **Row-local enumeration completeness**, memory side. -/
theorem mem_memoryRowSlots (s : MemoryRowSkeleton)
    (row : MemoryTable.MState × MemoryTable.DTmem K)
    {a : MemorySlotAddress} (ha : memorySlotActive s.state a = true) :
    (memorySlotNoun s a, memorySlotFP row a) ∈ memoryRowSlots s row :=
  List.mem_map_of_mem ((mem_activeMemorySlotAddresses_iff _ a).2 ha)

omit [Field K] in
/-- **Inactive-slot exclusion (address level).**  A padding compute address contributes no scanned
pair: it is absent from the address list the scan maps over.  This is the exclusion statement that is
actually true — see the module header on why value-level exclusion is not claimed. -/
theorem inactive_compute_slot_not_scanned (s : ComputeRowSkeleton)
    (row : ComputeTable.State × ComputeTable.DTcomp K)
    {a : ComputeSlotAddress} (h : computeSlotActive s.state a = false) :
    a ∉ activeComputeSlotAddresses s.state ∧
      computeRowSlots s row =
        (activeComputeSlotAddresses s.state).map
          (fun b => (computeSlotNoun s b, computeSlotFP row b)) :=
  ⟨not_mem_activeComputeSlotAddresses h, rfl⟩

omit [Field K] in
/-- **Inactive-slot exclusion (address level)**, memory side. -/
theorem inactive_memory_slot_not_scanned (s : MemoryRowSkeleton)
    (row : MemoryTable.MState × MemoryTable.DTmem K)
    {a : MemorySlotAddress} (h : memorySlotActive s.state a = false) :
    a ∉ activeMemorySlotAddresses s.state ∧
      memoryRowSlots s row =
        (activeMemorySlotAddresses s.state).map
          (fun b => (memorySlotNoun s b, memorySlotFP row b)) :=
  ⟨not_mem_activeMemorySlotAddresses h, rfl⟩

omit [Field K] in
/-- The scanned pairs of a row are exactly as many as its active addresses: no slot is scanned twice
and no padding slot is added. -/
theorem computeRowSlots_length (s : ComputeRowSkeleton)
    (row : ComputeTable.State × ComputeTable.DTcomp K) :
    (computeRowSlots s row).length = (activeComputeSlotAddresses s.state).length :=
  List.length_map _

omit [Field K] in
theorem memoryRowSlots_length (s : MemoryRowSkeleton)
    (row : MemoryTable.MState × MemoryTable.DTmem K) :
    (memoryRowSlots s row).length = (activeMemorySlotAddresses s.state).length :=
  List.length_map _

omit [Field K] in
/-- The committed nouns of the scan are exactly the committed nouns of the commitment inventory for
that row. -/
theorem computeRowSlots_map_fst (s : ComputeRowSkeleton)
    (row : ComputeTable.State × ComputeTable.DTcomp K) :
    (computeRowSlots s row).map Prod.fst = commitmentComputeRowNouns s := by
  simp [computeRowSlots, commitmentComputeRowNouns, List.map_map, Function.comp_def]

omit [Field K] in
theorem memoryRowSlots_map_fst (s : MemoryRowSkeleton)
    (row : MemoryTable.MState × MemoryTable.DTmem K) :
    (memoryRowSlots s row).map Prod.fst = commitmentMemoryRowNouns s := by
  simp [memoryRowSlots, commitmentMemoryRowNouns, List.map_map, Function.comp_def]

/-! ## The whole-family scan -/

variable {p : ℕ}

/-- **The full active compute fingerprint scan.**  Canonical committed compute BFS rows are paired
with the family's canonical committed compute BFS rows, each contributing its active addresses. -/
def activeComputeSlotsOn (C : SkeletonCommitment) (R : RawPlusIOSegmentedFamily F K) :
    List (Noun × ComputeTable.FP K) :=
  (List.zip (computeSkeletonRows C.skeleton) R.exec.computeRows).flatMap
    (fun q => computeRowSlots q.1 q.2)

/-- **The full active memory fingerprint scan.** -/
def activeMemorySlotsOn (C : SkeletonCommitment) (R : RawPlusIOSegmentedFamily F K) :
    List (Noun × ComputeTable.FP K) :=
  (List.zip (memorySkeletonRows C.skeleton) R.exec.memoryRows).flatMap
    (fun q => memoryRowSlots q.1 q.2)

/-- The finite enumeration of active compute fingerprints (public `s`/`f`/`e`, private
decomposition, subformula triples, and memory-record root/child slots). -/
def activeComputeFingerprints (C : SkeletonCommitment) (R : RawPlusIOSegmentedFamily F K) :
    List (ComputeTable.FP K) :=
  (activeComputeSlotsOn C R).map Prod.snd

/-- The finite enumeration of active memory fingerprints (parent, active child cells, live memory
record root/child). -/
def activeMemoryFingerprints (C : SkeletonCommitment) (R : RawPlusIOSegmentedFamily F K) :
    List (ComputeTable.FP K) :=
  (activeMemorySlotsOn C R).map Prod.snd

/-- **The post-seed check, family form.**  Every scanned active slot's committed fingerprint is the
NPR encoding at `z` of the corresponding pre-committed skeleton noun. -/
def ActiveFingerprintChecksOn (z : K) (C : SkeletonCommitment)
    (R : RawPlusIOSegmentedFamily F K) : Prop :=
  (∀ e ∈ activeComputeSlotsOn C R, e.2 = GlobalCarryRecognizer.enc z e.1) ∧
    ∀ e ∈ activeMemorySlotsOn C R, e.2 = GlobalCarryRecognizer.enc z e.1

/-- **The post-seed check, raw-message form.**  `p` is the strict modular prime of the commitment
check; the scanned fingerprints are those of `msg`'s own committed family. -/
def ActiveFingerprintChecks (p : ℕ) (z : K) (C : SkeletonCommitment)
    {R : RawPlusIOSegmentedFamily F K} (_msg : RawMessage R p) : Prop :=
  ActiveFingerprintChecksOn z C R

@[simp] theorem activeFingerprintChecks_iff (p : ℕ) (z : K) (C : SkeletonCommitment)
    {R : RawPlusIOSegmentedFamily F K} (msg : RawMessage R p) :
    ActiveFingerprintChecks p z C msg ↔ ActiveFingerprintChecksOn z C R :=
  Iff.rfl

/-! ## Enumeration completeness of the whole scan -/

theorem mem_activeComputeSlotsOn_of_mem_zip
    {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    {s : ComputeRowSkeleton} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hzip : (s, row) ∈ List.zip (computeSkeletonRows C.skeleton) R.exec.computeRows)
    {e : Noun × ComputeTable.FP K} (he : e ∈ computeRowSlots s row) :
    e ∈ activeComputeSlotsOn C R :=
  List.mem_flatMap.2 ⟨(s, row), hzip, he⟩

theorem mem_activeMemorySlotsOn_of_mem_zip
    {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    {s : MemoryRowSkeleton} {row : MemoryTable.MState × MemoryTable.DTmem K}
    (hzip : (s, row) ∈ List.zip (memorySkeletonRows C.skeleton) R.exec.memoryRows)
    {e : Noun × ComputeTable.FP K} (he : e ∈ memoryRowSlots s row) :
    e ∈ activeMemorySlotsOn C R :=
  List.mem_flatMap.2 ⟨(s, row), hzip, he⟩

/-- **Enumeration completeness at a commonly indexed compute row.**  Every active address of the
`i`-th committed skeleton row appears in the scan, paired with the `i`-th committed execution row's
fingerprint at the same address. -/
theorem mem_activeComputeSlots_getElem
    (C : SkeletonCommitment) (R : RawPlusIOSegmentedFamily F K) (i : ℕ)
    (h₁ : i < (computeSkeletonRows C.skeleton).length)
    (h₂ : i < R.exec.computeRows.length)
    {a : ComputeSlotAddress}
    (ha : computeSlotActive ((computeSkeletonRows C.skeleton)[i]).state a = true) :
    (computeSlotNoun (computeSkeletonRows C.skeleton)[i] a,
        computeSlotFP R.exec.computeRows[i] a) ∈ activeComputeSlotsOn C R :=
  mem_activeComputeSlotsOn_of_mem_zip
    (getElem_mem_zip _ _ i h₁ h₂)
    (mem_computeRowSlots _ _ ha)

/-- Memory analogue of `mem_activeComputeSlots_getElem`. -/
theorem mem_activeMemorySlots_getElem
    (C : SkeletonCommitment) (R : RawPlusIOSegmentedFamily F K) (i : ℕ)
    (h₁ : i < (memorySkeletonRows C.skeleton).length)
    (h₂ : i < R.exec.memoryRows.length)
    {a : MemorySlotAddress}
    (ha : memorySlotActive ((memorySkeletonRows C.skeleton)[i]).state a = true) :
    (memorySlotNoun (memorySkeletonRows C.skeleton)[i] a,
        memorySlotFP R.exec.memoryRows[i] a) ∈ activeMemorySlotsOn C R :=
  mem_activeMemorySlotsOn_of_mem_zip
    (getElem_mem_zip _ _ i h₁ h₂)
    (mem_memoryRowSlots _ _ ha)

/-- **Full enumeration completeness under row-count agreement.**  With the committed row counts equal
— which is exactly what the `List.Forall₂` row bindings (hence `BindsAt`) supply — *every* active
address of *every* committed compute row is scanned. -/
theorem scan_covers_all_compute_rows
    (C : SkeletonCommitment) (R : RawPlusIOSegmentedFamily F K)
    (hlen : (computeSkeletonRows C.skeleton).length = R.exec.computeRows.length)
    (i : ℕ) (hi : i < (computeSkeletonRows C.skeleton).length)
    {a : ComputeSlotAddress}
    (ha : computeSlotActive ((computeSkeletonRows C.skeleton)[i]).state a = true) :
    (computeSlotNoun (computeSkeletonRows C.skeleton)[i] a,
        computeSlotFP R.exec.computeRows[i] a) ∈ activeComputeSlotsOn C R :=
  mem_activeComputeSlots_getElem C R i hi (hlen ▸ hi) ha

/-- Memory analogue of `scan_covers_all_compute_rows`. -/
theorem scan_covers_all_memory_rows
    (C : SkeletonCommitment) (R : RawPlusIOSegmentedFamily F K)
    (hlen : (memorySkeletonRows C.skeleton).length = R.exec.memoryRows.length)
    (i : ℕ) (hi : i < (memorySkeletonRows C.skeleton).length)
    {a : MemorySlotAddress}
    (ha : memorySlotActive ((memorySkeletonRows C.skeleton)[i]).state a = true) :
    (memorySlotNoun (memorySkeletonRows C.skeleton)[i] a,
        memorySlotFP R.exec.memoryRows[i] a) ∈ activeMemorySlotsOn C R :=
  mem_activeMemorySlots_getElem C R i hi (hlen ▸ hi) ha

/-! ## Coverage: every scanned noun is a committed noun -/

theorem scanned_compute_noun_mem_commitment
    {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    {e : Noun × ComputeTable.FP K} (he : e ∈ activeComputeSlotsOn C R) :
    e.1 ∈ commitmentNouns C := by
  obtain ⟨q, hq, hmem⟩ := List.mem_flatMap.1 he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hmem
  exact mem_commitmentNouns_compute (List.of_mem_zip hq).1 ha

theorem scanned_memory_noun_mem_commitment
    {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    {e : Noun × ComputeTable.FP K} (he : e ∈ activeMemorySlotsOn C R) :
    e.1 ∈ commitmentNouns C := by
  obtain ⟨q, hq, hmem⟩ := List.mem_flatMap.1 he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hmem
  exact mem_commitmentNouns_memory (List.of_mem_zip hq).1 ha

/-! ## The pre-seed bindings imply the post-seed checks

The converse (acceptance forces the
bindings) is the named residual of A2/B. -/

/-- Every scanned pair of a *bound* compute row satisfies the check. -/
theorem bindComputeRow_slots {z : K} {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (h : BindComputeRow z s row) :
    ∀ e ∈ computeRowSlots s row, e.2 = GlobalCarryRecognizer.enc z e.1 := by
  obtain ⟨_, _, _, hs, hf, he, hdec, hsf, hmr⟩ := h
  intro e hmem
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hmem
  rw [mem_activeComputeSlotAddresses_iff] at ha
  cases a with
  | subject => exact hs
  | formula => exact hf
  | evaluation => exact he
  | dec slot =>
      have hactive : decActive s.state slot = true := by
        simpa [computeSlotActive] using ha
      have hbind := hdec slot
      rw [dif_pos hactive] at hbind
      simpa [bindFP, computeSlotFP, computeSlotNoun_dec_of_active hactive] using hbind
  | sub i slot =>
      have hactive : (i : ℕ) < ComputeTable.fanoutComp s.state := by
        simpa [computeSlotActive] using ha
      have hbind := hsf i
      rw [dif_pos hactive] at hbind
      simpa [bindFP, computeSlotFP, computeSlotNoun_sub_of_active hactive slot] using hbind slot
  | memRec i slot =>
      have hactive : (i : ℕ) < Nock.Framework.recordCount s.state := by
        simpa [computeSlotActive] using ha
      have hbind := hmr i
      rw [dif_pos hactive] at hbind
      cases slot with
      | root =>
          simpa [bindFP, computeSlotFP, memRecFP, memRecSkeletonNoun,
            computeSlotNoun_memRec_of_active hactive] using hbind.1
      | child =>
          simpa [bindFP, computeSlotFP, memRecFP, memRecSkeletonNoun,
            computeSlotNoun_memRec_of_active hactive] using hbind.2.1

/-- Every scanned pair of a *bound* memory row satisfies the check. -/
theorem bindMemoryRow_slots {z : K} {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : BindMemoryRow z s row) :
    ∀ e ∈ memoryRowSlots s row, e.2 = GlobalCarryRecognizer.enc z e.1 := by
  obtain ⟨_, _, _, hpt, hchild, hmem, _hver⟩ := h
  intro e hmemE
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hmemE
  rw [mem_activeMemorySlotAddresses_iff] at ha
  cases a with
  | parent => exact hpt
  | child i =>
      have hactive : (i : ℕ) < MemoryTable.fanoutMem s.state := by
        simpa [memorySlotActive] using ha
      have hbind := hchild i
      rw [dif_pos hactive] at hbind
      simpa [bindFP, memorySlotFP, memorySlotNoun_child_of_active hactive] using hbind
  | memRec slot =>
      have hactive : memoryMemRecKind s.state = .active := by
        simpa [memorySlotActive] using ha
      rw [dif_pos hactive] at hmem
      cases slot with
      | root =>
          simpa [bindFP, memorySlotFP, memRecFP, memRecSkeletonNoun,
            memorySlotNoun_memRec_of_active hactive] using hmem.1
      | child =>
          simpa [bindFP, memorySlotFP, memRecFP, memRecSkeletonNoun,
            memorySlotNoun_memRec_of_active hactive] using hmem.2.1

/-- **The two canonical `Forall₂` row bindings are exactly what the scan consumes.** -/
theorem activeFingerprintChecksOn_of_forall₂
    {z : K} {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    (hc : List.Forall₂ (BindComputeRow z) (computeSkeletonRows C.skeleton) R.exec.computeRows)
    (hm : List.Forall₂ (BindMemoryRow z) (memorySkeletonRows C.skeleton) R.exec.memoryRows) :
    ActiveFingerprintChecksOn z C R := by
  constructor
  · intro e he
    obtain ⟨q, hq, hmem⟩ := List.mem_flatMap.1 he
    exact bindComputeRow_slots (rel_of_mem_zip hc (by simpa using hq)) e hmem
  · intro e he
    obtain ⟨q, hq, hmem⟩ := List.mem_flatMap.1 he
    exact bindMemoryRow_slots (rel_of_mem_zip hm (by simpa using hq)) e hmem

/-- **A genuine pre-seed binding passes the post-seed scan.**  This is the completeness half of the
strict contract: an honest prover is not rejected. -/
theorem activeFingerprintChecksOn_of_bindsAt
    {z : K} {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    (h : BindsAt z C.skeleton R.cfg R.exec) :
    ActiveFingerprintChecksOn z C R :=
  activeFingerprintChecksOn_of_forall₂ h.derived_computeRows h.derived_memoryRows

/-- Raw-message spelling of `activeFingerprintChecksOn_of_bindsAt`. -/
theorem activeFingerprintChecks_of_bindsAt
    {z : K} {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    (msg : RawMessage R p) (h : BindsAt z C.skeleton R.cfg R.exec) :
    ActiveFingerprintChecks p z C msg :=
  activeFingerprintChecksOn_of_bindsAt h

/-! ## Reconstruction at the characteristic

The key consequence: the post-seed check ties every active committed fingerprint back to a noun that
was fixed *before* `z`, and the canonical commitment check supplies its canonical-residue bound.
`ActiveRealization` (Packet 2A) is the data-carrying realization, so nothing here is a bare
existential. -/

/-- **Every scanned compute fingerprint is an `ActiveRealization` at `z`.**  The witness noun is the
pre-committed one; the bound comes from the seed-independent commitment check.

This is a `def`, not a `theorem`: `ActiveRealization` is deliberately *data* (Packet 2A), so the
realization is exhibited rather than asserted to exist. -/
def scanned_compute_activeRealization
    {z : K} {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    (hcanon : CanonicalCommitmentCheck p C)
    (hcheck : ActiveFingerprintChecksOn z C R)
    {e : Noun × ComputeTable.FP K} (he : e ∈ activeComputeSlotsOn C R) :
    StrictRawReconstruction.ActiveRealization z p e.2 where
  noun := e.1
  bounded := (hcanon _ (scanned_compute_noun_mem_commitment he)).1
  realizes := (hcheck.1 e he).symm

/-- Memory analogue of `scanned_compute_activeRealization`. -/
def scanned_memory_activeRealization
    {z : K} {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    (hcanon : CanonicalCommitmentCheck p C)
    (hcheck : ActiveFingerprintChecksOn z C R)
    {e : Noun × ComputeTable.FP K} (he : e ∈ activeMemorySlotsOn C R) :
    StrictRawReconstruction.ActiveRealization z p e.2 where
  noun := e.1
  bounded := (hcanon _ (scanned_memory_noun_mem_commitment he)).1
  realizes := (hcheck.2 e he).symm

/-- Every enumerated active compute fingerprint is `FPRealized` — the leaf/decode bound gate of
`BoundGates`, now discharged by the two deterministic checks rather than assumed. -/
theorem activeComputeFingerprints_realized
    {z : K} {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    (hcanon : CanonicalCommitmentCheck p C)
    (hcheck : ActiveFingerprintChecksOn z C R)
    {fp : ComputeTable.FP K} (hfp : fp ∈ activeComputeFingerprints C R) :
    FPRealized z p fp := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hfp
  exact (scanned_compute_activeRealization hcanon hcheck he).fpRealized

/-- Memory analogue of `activeComputeFingerprints_realized`. -/
theorem activeMemoryFingerprints_realized
    {z : K} {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    (hcanon : CanonicalCommitmentCheck p C)
    (hcheck : ActiveFingerprintChecksOn z C R)
    {fp : ComputeTable.FP K} (hfp : fp ∈ activeMemoryFingerprints C R) :
    FPRealized z p fp := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hfp
  exact (scanned_memory_activeRealization hcanon hcheck he).fpRealized

/-- **The scan discharges the leaf/decode bound gate** on every active compute fingerprint, so the
non-noun forgery class of `BoundGates` is excluded by a check the verifier can run. -/
theorem activeComputeFingerprints_leafBoundGate
    {z : K} {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    (hcanon : CanonicalCommitmentCheck p C)
    (hcheck : ActiveFingerprintChecksOn z C R)
    {fp : ComputeTable.FP K} (hfp : fp ∈ activeComputeFingerprints C R) :
    BoundGates.LeafBoundGate z p fp :=
  activeComputeFingerprints_realized hcanon hcheck hfp

/-- **Pair-local uniqueness at the characteristic, no global injectivity.**  Any other canonical
witness for a scanned fingerprint equals the pre-committed noun as soon as that one concrete pair is
NPR-separated at `z`.  The cast-injectivity premise is free at the characteristic
(`StrictRawReconstruction.charCast_injOn`). -/
theorem scanned_noun_unique [CharP K p]
    {z : K} {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    (hcanon : CanonicalCommitmentCheck p C)
    (hcheck : ActiveFingerprintChecksOn z C R)
    {e : Noun × ComputeTable.FP K} (he : e ∈ activeComputeSlotsOn C R)
    (n : Noun) (hn : FieldEmbedding.BoundedBy p n)
    (henc : GlobalCarryRecognizer.enc z n = e.2)
    (hsep : GlobalCarryRecognizer.SepSeed z n e.1) :
    n = e.1 :=
  GlobalCarryRecognizer.noun_eq_of_enc_eq z n e.1 hsep
    (StrictRawReconstruction.charCast_injOn p) hn
    (hcanon _ (scanned_compute_noun_mem_commitment he)).1
    (henc.trans (hcheck.1 e he))

/-- **The public root claim is realized by the pre-seed commitment.**  Specialization of the scan at
the canonical compute root: the three public fingerprints carry `ActiveRealization` data whose
witnesses are the committed root row's `subject`/`formula`/`evaluation` nouns, i.e. exactly
`SemanticSkeleton.publicClaim`. -/
def root_claim_activeRealization
    {z : K} {C : SkeletonCommitment} {R : RawPlusIOSegmentedFamily F K}
    (hcanon : CanonicalCommitmentCheck p C)
    (hcheck : ActiveFingerprintChecksOn z C R)
    (hlen : (computeSkeletonRows C.skeleton).length = R.exec.computeRows.length)
    (hpos : 0 < (computeSkeletonRows C.skeleton).length) :
    StrictRawReconstruction.ActiveRealization z p
        (computeSlotFP R.exec.computeRows[0] .subject) ×
      StrictRawReconstruction.ActiveRealization z p
        (computeSlotFP R.exec.computeRows[0] .formula) ×
      StrictRawReconstruction.ActiveRealization z p
        (computeSlotFP R.exec.computeRows[0] .evaluation) :=
  ⟨scanned_compute_activeRealization hcanon hcheck
      (scan_covers_all_compute_rows C R hlen 0 hpos (a := .subject) rfl),
    scanned_compute_activeRealization hcanon hcheck
      (scan_covers_all_compute_rows C R hlen 0 hpos (a := .formula) rfl),
    scanned_compute_activeRealization hcanon hcheck
      (scan_covers_all_compute_rows C R hlen 0 hpos (a := .evaluation) rfl)⟩

/-- The committed root-row nouns witnessing `root_claim_activeRealization` are literally the
commitment's public claim: no post-seed choice enters. -/
theorem root_claim_nouns_eq_publicClaim (C : SkeletonCommitment)
    (hpos : 0 < (computeSkeletonRows C.skeleton).length) :
    computeSlotNoun (computeSkeletonRows C.skeleton)[0] .subject =
        C.skeleton.publicClaim.subject ∧
      computeSlotNoun (computeSkeletonRows C.skeleton)[0] .formula =
        C.skeleton.publicClaim.formula ∧
      computeSlotNoun (computeSkeletonRows C.skeleton)[0] .evaluation =
        C.skeleton.publicClaim.result := by
  have hEq : computeSkeletonRows C.skeleton =
      C.skeleton.computeTree.label ::
        (bfsForest ([C.skeleton.computeTree].flatMap NTree.children)).map NTree.label := by
    unfold computeSkeletonRows
    rw [bfsForest_cons_eq _ (by simp)]
    simp
  have hroot : (computeSkeletonRows C.skeleton)[0] = C.skeleton.computeTree.label := by
    simp [hEq]
  rw [hroot]
  exact ⟨rfl, rfl, rfl⟩

end

end Nock.NockVMROM.Thm54.ActiveFingerprintScan

#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.mem_computeRowSlots
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.mem_memoryRowSlots
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.inactive_compute_slot_not_scanned
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.inactive_memory_slot_not_scanned
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.computeRowSlots_map_fst
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.memoryRowSlots_map_fst
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.mem_activeComputeSlots_getElem
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.mem_activeMemorySlots_getElem
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.scan_covers_all_compute_rows
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.scan_covers_all_memory_rows
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.scanned_compute_noun_mem_commitment
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.scanned_memory_noun_mem_commitment
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.bindComputeRow_slots
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.bindMemoryRow_slots
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.activeFingerprintChecksOn_of_forall₂
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.activeFingerprintChecksOn_of_bindsAt
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.activeFingerprintChecks_of_bindsAt
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.scanned_compute_activeRealization
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.scanned_memory_activeRealization
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.activeComputeFingerprints_realized
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.activeMemoryFingerprints_realized
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.activeComputeFingerprints_leafBoundGate
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.scanned_noun_unique
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.root_claim_activeRealization
#print axioms Nock.NockVMROM.Thm54.ActiveFingerprintScan.root_claim_nouns_eq_publicClaim
