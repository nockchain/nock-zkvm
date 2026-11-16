/-
  Nock/NockVMROM/Thm54/VclL/Handle/ClaimH.lean

  The compute twin `ChipH.computeChipVCLH` pins its first row's handles `s f e` to publics
  (`isFirst·(h − pub)`).  A public CELL handle `(1, idx)` is bound to the claim noun `x` by one
  external validity lookup `(enc z x, hi, lo, idx)` whose fingerprint the VERIFIER computes from the
  public claim (an element of the validity balance's external list `vl`); an ATOM handle `(0, v)` is
  the claim atom itself and needs no lookup.

  * `claim_census_inj` — outside T2 at the census with the claim nouns as skeleton
    (`tableBadSeeds fuelChip _ skel`, `x ∈ skel`), a claim noun in the window whose fingerprint
    equals a decoded noun's IS that noun;
  * **`claimH_genuine`** — a served claim record `(enc z x, hi, lo, idx)` gives
    `denH (1, idx) = x`, from `row_genuine` (T1) and `claim_census_inj`;
  * **`claim_handles_denote`** — every claim noun's public handle (`claimHandle`: atom ↦ `(0, v)`,
    cell ↦ `(1, idx)`) denotes the claim noun.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.Ground

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL
open Nock.ComputeTable (FP)

section Claim
variable {q : ℕ} {Kfp : Type} [Field Kfp]

/-- **The external validity lookup's existence form**: the record is some row's validity key. -/
def ValidityProvided (t : List (CellRow q Kfp)) (r : VKey Kfp) : Prop :=
  ∃ c ∈ t, r = (c.p, c.b0.hi, c.b0.lo, c.b0.idx)

theorem ValidityBalanced.provided {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)}
    (h : ValidityBalanced t vl) : ∀ r ∈ vl, ValidityProvided t r := by
  intro r hr
  have hmem : r ∈ expand (vCons t ++ vl.map (·, 1)) := by
    rw [mem_expand]
    exact ⟨(r, 1), List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩), one_ne_zero, rfl⟩
  have hp := h.mem_iff.mpr hmem
  rw [mem_expand] at hp
  obtain ⟨kc, hkc, -, hk⟩ := hp
  simp only [vProv, List.mem_map] at hkc
  obtain ⟨c, hc, rfl⟩ := hkc
  exact ⟨c, hc, hk⟩

variable [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp] [Fact q.Prime]

/-- **The claim census**: outside T2 with the claim nouns as skeleton, a window claim noun whose
fingerprint equals a decoded noun's is that noun. -/
theorem claim_census_inj (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)}
    {vl : List (VKey Kfp)} (h : TableAccepts z t vl) {skel : List Noun}
    (hT2 : z ∉ tableBadSeeds fuelChip (t.map (·.b0)) skel) {x d : Noun} (hx : x ∈ skel)
    (hxl : x.leaves ≤ fuelChip) (hxq : ∀ k ∈ x.leafList, k < q)
    (hd : d ∈ decodedNouns (t.map (·.b0)))
    (he : GlobalCarryRecognizer.enc z x = GlobalCarryRecognizer.enc z d) : x = d := by
  haveI : CharP Kfp q := charP_of_injective_algebraMap (algebraMap (ZMod q) Kfp).injective q
  have hchar : ringChar Kfp = q := ringChar.eq Kfp q
  obtain ⟨hld, hqd⟩ := decoded_window hq hz h hd
  by_contra hne
  have hmx : x ∈ censusNouns (t.map (·.b0)) skel := List.mem_append_right _ hx
  have hmd : d ∈ censusNouns (t.map (·.b0)) skel := List.mem_append_left _ hd
  have hfield : (NPR.leafF (K := Kfp) x, NPR.dyckBits (K := Kfp) x)
      = (NPR.leafF (K := Kfp) d, NPR.dyckBits (K := Kfp) d) := by
    rcases mem_allPairs_of_ne _ hmx hmd hne with hp | hp
    · exact PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds hT2 hp hxl hld he
    · exact (PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds hT2 hp hld hxl he.symm).symm
  exact hne (PreSeedCensus.noun_eq_of_fieldNoun_eq (K := Kfp)
    (fun k hk => hchar ▸ hxq k hk) (fun k hk => hchar ▸ hqd k hk) hfield)

/-- **`claimH_genuine`**: a served claim record `(enc z x, hi, lo, idx)`, fingerprint computed by
the verifier from the public claim noun `x`, gives `denH (1, idx) = x`. -/
theorem claimH_genuine (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)}
    {vl : List (VKey Kfp)} (h : TableAccepts z t vl) {skel : List Noun}
    (hT2 : z ∉ tableBadSeeds fuelChip (t.map (·.b0)) skel) {x : Noun} (hx : x ∈ skel)
    (hxl : x.leaves ≤ fuelChip) (hxq : ∀ k ∈ x.leafList, k < q) {hi lo idx : ℕ}
    (hprov : ValidityProvided t (GlobalCarryRecognizer.enc z x, hi, lo, idx)) :
    denH (t.map (·.b0)) (true, idx) = some x := by
  obtain ⟨c, hc, heq⟩ := hprov
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hfp, -, -, hidx⟩ := heq
  obtain ⟨L, R, hdec, hp, -⟩ := row_genuine hq hz h hc
  have hxd : x = .cell L R :=
    claim_census_inj hq hz h hT2 hx hxl hxq (mem_decodedNouns_of hdec) (by rw [hfp, hp])
  rw [denH_cell, hidx, hdec, hxd]

/-- The public handle of a claim noun: an atom is `(0, v)`; a cell is `(1, idx)` with the
prover-named serial `idx`. -/
def claimHandle (x : Noun) (idx : ℕ) : VHandle :=
  match x with
  | .atom v => (false, v)
  | .cell _ _ => (true, idx)

/-- **The claim's handles denote the claim's nouns** (`s f e`, or any claim list): atoms by the
handle's own value, cells through one served validity record each with the verifier-computed
fingerprint. -/
theorem claim_handles_denote (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)}
    {vl : List (VKey Kfp)} (h : TableAccepts z t vl) {claim : List Noun}
    (hT2 : z ∉ tableBadSeeds fuelChip (t.map (·.b0)) claim)
    (hwin : ∀ x ∈ claim, x.leaves ≤ fuelChip ∧ ∀ k ∈ x.leafList, k < q) (idxOf : Noun → ℕ)
    (hprov : ∀ x ∈ claim, ∀ L R, x = .cell L R →
      ∃ hi lo, ValidityProvided t (GlobalCarryRecognizer.enc z x, hi, lo, idxOf x)) :
    ∀ x ∈ claim, denH (t.map (·.b0)) (claimHandle x (idxOf x)) = some x := by
  intro x hx
  match x, hx with
  | .atom v, _ => rfl
  | .cell L R, hx =>
    obtain ⟨hi, lo, hp⟩ := hprov _ hx L R rfl
    exact claimH_genuine hq hz h hT2 hx (hwin _ hx).1 (hwin _ hx).2 hp

end Claim

end Nock.NockVMROM.Thm54.VclL.Handle
