/-
  Nock/NockVMROM/Thm54/VclL/Handle/ClaimDenVS.lean

  Additive.

  * `claim_census_injΛ` / `claimH_genuineΛ`: `ClaimH.claim_census_inj` / `claimH_genuine` at any census
    fuel `Λ ≥ fuelChip` (a claim noun's leaf count is public, NOT bounded by `fuelChip`; no check of
    the VS verifier bounds it, so the VS census runs at `claimFuel V = max fuelChip (claim leaves)`).
  * `zVS_chals`: `chalsVS`'s leaves `2 / 3` recombine to `zVS`.
  * **`claim_table_VS`**: at VS (`AcceptsG`, `V.Checks`), outside `valSummand`, with `zVS ≠ 0`, the
    decoded (restricted) cell table is `TableAccepts` (`cellTable_accepts_of_lookup`, `reqs = claimRecs`;
    `PrimeFieldElems F`, `2^63 < p`, `n < p` from the cell chip's `GoodM`).
  * **`claim_handles_VS`**: moreover outside the claim census `tableBadSeeds (claimFuel V) _ claimList`,
    every claim noun `k`'s public handle at the serial the chip SEES, `claimHandle x (natOf (idx : 𝔽))`,
    denotes `x` in the decoded table.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL.Handle.IOVS
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS Nock.NockVMROM.Thm54.VclL.Handle.ValIOVS
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The claim census at any fuel `Λ ≥ fuelChip` -/

section Census
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp]
  [Fact q.Prime]

theorem claim_census_injΛ (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)}
    {vl : List (VKey Kfp)} (h : TableAccepts z t vl) {Λ : ℕ} (hΛ : fuelChip ≤ Λ) {skel : List Noun}
    (hT2 : z ∉ tableBadSeeds Λ (t.map (·.b0)) skel) {x d : Noun} (hx : x ∈ skel)
    (hxl : x.leaves ≤ Λ) (hxq : ∀ k ∈ x.leafList, k < q)
    (hd : d ∈ decodedNouns (t.map (·.b0)))
    (he : GlobalCarryRecognizer.enc z x = GlobalCarryRecognizer.enc z d) : x = d := by
  haveI : CharP Kfp q := charP_of_injective_algebraMap (algebraMap (ZMod q) Kfp).injective q
  have hchar : ringChar Kfp = q := ringChar.eq Kfp q
  obtain ⟨hld, hqd⟩ := decoded_window hq hz h hd
  by_contra hne
  have hmx : x ∈ censusNouns (t.map (·.b0)) skel := List.mem_append_right _ hx
  have hmd : d ∈ censusNouns (t.map (·.b0)) skel := List.mem_append_left _ hd
  have hld' : d.leaves ≤ Λ := hld.trans hΛ
  have hfield : (NPR.leafF (K := Kfp) x, NPR.dyckBits (K := Kfp) x)
      = (NPR.leafF (K := Kfp) d, NPR.dyckBits (K := Kfp) d) := by
    rcases mem_allPairs_of_ne _ hmx hmd hne with hp | hp
    · exact PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds hT2 hp hxl hld' he
    · exact (PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds hT2 hp hld' hxl he.symm).symm
  exact hne (PreSeedCensus.noun_eq_of_fieldNoun_eq (K := Kfp)
    (fun k hk => hchar ▸ hxq k hk) (fun k hk => hchar ▸ hqd k hk) hfield)

theorem claimH_genuineΛ (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0) {t : List (CellRow q Kfp)}
    {vl : List (VKey Kfp)} (h : TableAccepts z t vl) {Λ : ℕ} (hΛ : fuelChip ≤ Λ) {skel : List Noun}
    (hT2 : z ∉ tableBadSeeds Λ (t.map (·.b0)) skel) {x : Noun} (hx : x ∈ skel)
    (hxl : x.leaves ≤ Λ) (hxq : ∀ k ∈ x.leafList, k < q) {hi lo idx : ℕ}
    (hprov : ValidityProvided t (GlobalCarryRecognizer.enc z x, hi, lo, idx)) :
    denH (t.map (·.b0)) (true, idx) = some x := by
  obtain ⟨c, hc, heq⟩ := hprov
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hfp, -, -, hidx⟩ := heq
  obtain ⟨L, R, hdec, hp, -⟩ := row_genuine hq hz h hc
  have hxd : x = .cell L R :=
    claim_census_injΛ hq hz h hΛ hT2 hx hxl hxq (mem_decodedNouns_of hdec) (by rw [hfp, hp])
  rw [denH_cell, hidx, hdec, hxd]

end Census

/-- The claim nouns as a list `[s, f, e]`. -/
def claimList (c : P8PublicClaim) : List Noun := (List.finRange 3).map (claimNoun c)

theorem claimNoun_mem (c : P8PublicClaim) (k : Fin 3) : claimNoun c k ∈ claimList c :=
  List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩

/-- **The VS claim census fuel**: `fuelChip` or the largest claim noun's leaf count. -/
def claimFuel (c : P8PublicClaim) : ℕ :=
  max fuelChip (max c.subject.leaves (max c.formula.leaves c.result.leaves))

theorem fuelChip_le_claimFuel (c : P8PublicClaim) : fuelChip ≤ claimFuel c := le_max_left _ _

theorem claimNoun_leaves_le (c : P8PublicClaim) (k : Fin 3) : (claimNoun c k).leaves ≤ claimFuel c := by
  unfold claimFuel
  fin_cases k <;> simp [claimNoun]

/-! ## 2. At VS -/

section VS

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr hC : ℕ)
  {sumC : VerifierData F K hC (shapeVS hT hP) → ClaimMsgVS → SummandsVS (F := F) (K := K) hT hP hC}
  {sumM : VerifierData F K hC (shapeVS hT hP) → Unit → SummandsVS (F := F) (K := K) hT hP hC}

/-- `𝕂′` has characteristic `char 𝔽` (local instance). -/
theorem quadCharF : CharP (Quad (algebraMap F K δF)) (ringChar F) := by
  rw [← ringChar_quad_eq (K := K) δF]; exact ringChar.charP _

attribute [local instance] quadCharF

/-- The `ZMod (char 𝔽)`-algebra structure of `𝕂′` (local instance). -/
abbrev quadZAlg : Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF)) := ZMod.algebra _ _

attribute [local instance] quadZAlg

theorem zVS_chals (χ : Coins frameVS K) :
    Quad.mk (algebraMap F K δF) (chalsVS δF χ 2) (chalsVS δF χ 3) = zVS δF χ := by
  rw [chalsVS_old δF χ 2 (by norm_num), chalsVS_old δF χ 3 (by norm_num)]
  rfl

/-- The decoded (restricted) cell table at VS. -/
abbrev tVS (V : VerifierData F K hC (shapeVS hT hP))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K) :=
  cellTableOf δF V.basis (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP)) (chalsVS δF χ)
    (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2) (qCellVS δF hT hP kr hC V msg χ)

/-- Outside `valSummand`, with the seed
nonzero, the decoded restricted cell table is `TableAccepts` (its validity lookup discharged with the
verifier's claim records as the external consumers). -/
theorem claim_table_VS (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hnot : ¬ (valSummand δF hT hP hC V msg.msg0C).mem (msg.traces χ) χ)
    (hz : zVS δF χ ≠ 0) :
    TableAccepts (zVS δF χ) (tVS δF hT hP kr hC V msg χ) [] := by
  obtain ⟨hg, -⟩ := compute_facts δF hT hP kr hC V msg χ h
  obtain ⟨hgM, hwT, hsatT⟩ := cell_facts δF hT hP kr hC V msg χ h
  have hsatO := cellChipH_restrict_sat δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
    (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    _ hsatT.1
  have hbindO := cellChipH_restrict_bind δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
    (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    _ hsatT.2
  have hchar : ringChar (Quad (algebraMap F K δF)) = ringChar F := ringChar_quad_eq δF
  have hcons0 := hV.hcons 0
  simp [reqBoundVS, internalBoundVS, hchar] at hcons0
  obtain ⟨e1, e2⟩ := valLists_at δF hT hP kr hC V msg χ
  have hio : (Quad.mk (algebraMap F K δF) (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩),
        Quad.mk (algebraMap F K δF) (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩)) ∉
      FiniteIO.IOFailureEventW (claimRecs δF V.claim msg.msg0C χ ++
          cellVInternal δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP)) (V.orbitM (tCS hT hP))
            (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
            (qCellVS δF hT hP kr hC V msg χ))
        (SVFrame.liftWts (cellVRecords δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
          (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
          (qCellVS δF hT hP kr hC V msg χ))) := by
    rw [← e1, ← e2]
    exact fun hm => hnot ((mem_valSummand δF hT hP hC V msg.msg0C (msg.traces χ) χ).mpr hm)
  have hne := TeleC.den_ne_of_out _ _ _ _ hio
  have hz' : Quad.mk (algebraMap F K δF) (chalsVS δF χ 2) (chalsVS δF χ 3) ≠ 0 := by
    rw [zVS_chals]; exact hz
  have hacc := cellTable_accepts_of_lookup δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
    (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
    (qCellVS δF hT hP kr hC V msg χ) hgM.2.2.1 hgM.2.2.2.1 hz' hsatO hbindO
    (hV.memNodes_injective _) (hV.hadjM _) (by have := hgM.2.2.2.2; omega) _ _ (chalsOK_VS δF χ)
    (p := ringChar F) (claimRecs δF V.claim msg.msg0C χ) ?_
    (fun r hr => hne r (List.mem_append_left _ hr))
    (fun hc => hio (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inl hc)))
    (fun hc => hio (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc)))) ?_ []
  · rw [zVS_chals] at hacc; exact hacc
  · rw [show (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 0) =
        pubsC δF (rho3 δF (msg.requests χ)) (msg.msg2M χ).1 0 by simp [pubsCH, CellH.pubH],
      show (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2 1) =
        pubsC δF (rho3 δF (msg.requests χ)) (msg.msg2M χ).1 1 by simp [pubsCH, CellH.pubH],
      pubsC_01]
    simp only [rho3]
    exact hg.2.2.2.1.symm
  · rw [List.length_append]
    have h1 := claimRecs_length_le δF V.claim msg.msg0C χ
    have h2 := cellVInternal_length_le δF V.basis (V.hM (tCS hT hP)) (V.memNodes (tCS hT hP))
      (V.orbitM (tCS hT hP)) (chalsVS δF χ) (pubsCH δF (msg.requests χ) (msg.msg2M χ).1 (msg.msg2M χ).2)
      (qCellVS δF hT hP kr hC V msg χ)
    exact lt_of_le_of_lt (Nat.add_le_add h1 h2) (by omega)

/-- Outside `valSummand` and the
claim census at `claimFuel`, with the seed nonzero: every claim noun `x_k`'s public handle at the
serial the compute chip reads, `claimHandle x_k (natOf (idx_k : 𝔽))`, denotes `x_k` in the decoded cell
table (atoms by their own value, cells through the served claim record). -/
theorem claim_handles_VS (V : VerifierData F K hC (shapeVS hT hP))
    (hV : V.Checks (fun a => reqBoundVS hT hP hC V a + internalBoundVS hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (msg : MessagesG (compCoreVS δF hT hP hC sumC) (memCoreVS δF hT hP kr hC sumM)) (χ : Coins frameVS K)
    (h : AcceptsG V msg χ)
    (hnot : ¬ (valSummand δF hT hP hC V msg.msg0C).mem (msg.traces χ) χ)
    (hz : zVS δF χ ≠ 0)
    (hT2 : zVS δF χ ∉ tableBadSeeds (Kfp := Quad (algebraMap F K δF)) (claimFuel V.claim)
      ((tVS δF hT hP kr hC V msg χ).map (·.b0)) (claimList V.claim)) :
    ∀ k : Fin 3, denH ((tVS δF hT hP kr hC V msg χ).map (·.b0))
      (claimHandle (claimNoun V.claim k) (natOf ((msg.msg0C k).1 : F))) = some (claimNoun V.claim k) := by
  obtain ⟨hgM, -, -⟩ := cell_facts δF hT hP kr hC V msg χ h
  have hq := hgM.2.2.2.1
  haveI : Fact (ringChar F).Prime :=
    ⟨(CharP.char_is_prime_or_zero F (ringChar F)).resolve_right (by omega)⟩
  have hacc := claim_table_VS δF hT hP kr hC V hV msg χ h hnot hz
  have hprov := claims_provided_VS' δF hT hP kr hC V hV msg χ h hnot
  intro k
  have hxq : ∀ j ∈ (claimNoun V.claim k).leafList, j < ringChar F := by
    apply GlobalCarryRecognizer.bounded_leafList
    obtain ⟨hs, hf, he⟩ := hV.hclaim
    fin_cases k
    · exact hs
    · exact hf
    · exact he
  cases hx : claimNoun V.claim k with
  | atom v => rfl
  | cell L R =>
    have hp := hprov k (by rw [hx]; rfl)
    rw [hx] at hp hxq
    have := claimH_genuineΛ hq hz hacc (fuelChip_le_claimFuel V.claim) hT2
      (hx ▸ claimNoun_mem V.claim k) (hx ▸ claimNoun_leaves_le V.claim k) hxq hp
    exact this

end VS

end

end Nock.NockVMROM.Thm54.VclL.Handle.ClaimDenVS
