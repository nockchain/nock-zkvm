/-
J-9 A L7 balance, the atom export `hbalA'`.

  * `awKey_gen`, `vhX9_eq_gen`: J-9 B's `awKey9` / `vhX9_eq` over any data record `D` whose atom cells are
    canonical combs closed under tails (`hcellsC hshape hclosed`), whose atom-walk nodes are atom cells (`hwcell`),
    whose reads are path axes (`hall`), and whose `mxA` / `vs` are the generator's (`hmxA hvs`).  Any orbit.
  * `incT_A`: J-9 B's `incT9` at `DA = j9aDataOf` and its own orbit `orbJ8 DA`, with no J-8 run binder
    (`ComplJ9ATables.genHyp_mbXA` / `acs_okA`: the J-8 binders were used only for `SmallX` at OP4 rows).
  * `balV2_A`, `hbalA_A_of`: the `hbalA'` field of `ComplJ9AObligations` at `BRun9A` (verbatim), from the J-9 A
    atom-walk read facts `hallA` / `hwA` plus binders `hax9 hwalkA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalF2
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ATables
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalV

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalV2

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.V1J8.Gen (hdN' tlN')
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF (vValsC9 kLV9 vLV9 kRV9 vRV9)

noncomputable section

section Gen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`awKey9` over a record**: the atom-walk handle key of a spec row is the atom cell handle key of its row. -/
theorem awKey_gen (hpG : p = Nock.Atoms.p) (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length)
    (hcellsC : ∀ c ∈ D.acs, c.isCell = true)
    (hshape : ∀ y ∈ D.acs, ∃ l, 2 ≤ l.length ∧ Nock.Atoms.Canonical l ∧ y = Nock.V1J8.Gen.combOf l)
    (hclosed : ∀ y ∈ D.acs, (tlN y).isCell = true → tlN y ∈ D.acs)
    (hne : D.preads ≠ []) (hwcell : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjA : Function.Injective (powN o D.acs.length))
    (hinjV : Function.Injective (powN o (nVOf D))) (χ : Coins frameJ8 K) (k : ℕ) (hk : k < nVOf D) :
    (ComplJ9BBalF.vdN9 δ b D o χ WalkHC.xKeyH k)⁻¹ =
      (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o
        (ComplJ9BAWR.idxRW D.acs (ComplJ9BBalF.rIA D) (wTrie D.acs D.preads k)) χ)⁻¹ := by
  have hnV : nVOf D = (walkRows D.acs D.preads).length := by unfold nVOf; rw [if_neg hne]
  have hmem := wTrie_mem D.acs D.preads (hnV ▸ hk)
  have hwn := hwcell _ hmem
  have hcl := hcellsC _ hwn
  obtain ⟨hget, hjlt, -⟩ := ComplJ9BBalF.idxRW_facts D _ hwn hcl
  set j := ComplJ9BAWR.idxRW D.acs (ComplJ9BBalF.rIA D) (wTrie D.acs D.preads k) with hj
  have hgetE : D.acs[j]'hjlt = (wTrie D.acs D.preads k).label.node := by
    rw [List.getD_eq_getElem _ _ hjlt] at hget; exact hget
  obtain ⟨l, h2, hcan, hl⟩ := hshape _ hwn
  have hBp : Nock.Atoms.B ≤ p := by rw [hpG]; exact Nock.Atoms.B_lt_p.le
  have hlimb : ∀ x ∈ l, x < p := fun x hx => lt_of_lt_of_le (hcan.1 x hx) hBp
  have hhd : Nock.V1J8.Gen.hdN' D.acs[j] = .atom (l.headD 0) := by
    rw [hgetE, hl, ComplJ8Atom.hd_combOf l h2]
  have hd : ComplJ9BBalF.vdN9 δ b D o χ WalkHC.xKeyH k = ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ)
      ((vValsC9 δ D χ ⟨k, hk⟩).idx, (kLV9 D ⟨k, hk⟩, vLV9 D ⟨k, hk⟩), (kRV9 D ⟨k, hk⟩, vRV9 D ⟨k, hk⟩)) := by
    simp only [ComplJ9BBalF.vdN9, WalkTraceHQ.dN, dif_pos hk]
    exact (ComplJ9BBalF.aw_dRow_split9 δ b D o hinjV χ (ComplJ9BBalF.pubsV09 δ D χ) ⟨k, hk⟩).1
  rw [hd, aHx_gen δ b D hA o hinjA χ j hjlt (by rw [hhd]; rfl), hhd]
  have ehd : VclL.hdN (vNode D k) = .atom (l.headD 0) := by
    rw [ComplJ8OfBal.hdN_eq]; show hdN' (wTrie D.acs D.preads k).label.node = _
    rw [hl, ComplJ8Atom.hd_combOf l h2]
  have etl : VclL.tlN (vNode D k) = tlN' D.acs[j] := by
    rw [ComplJ8OfBal.tlN_eq, hgetE]
  have hx0 : l.headD 0 < p := by
    cases l with
    | nil => simp at h2
    | cons x l' => exact hlimb x (by simp)
  have hk0 : ((ComplJ9BBalF.HA D (VclL.hdN (vNode D k))).1 : ZMod p) = 0 ∧
      ((ComplJ9BBalF.HA D (VclL.hdN (vNode D k))).2 : ZMod p) = ((l.headD 0 : ℕ) : ZMod p) := by
    rw [ehd]; simp only [ComplJ9BBalF.HA, ComplJ9BBalV.hdl_small hpG _ _ hx0]; simp
  have hcell : (tlN' D.acs[j]).isCell = true → tlN' D.acs[j] ∈ D.acs := fun hc => by
    have := hclosed _ (hgetE ▸ hwn)
    rw [ComplJ8OfBal.tlN_eq] at this
    exact this hc
  have hR : ((ComplJ9BBalF.HA D (tlN' D.acs[j])).1 : ZMod p) =
        ((if (tlN' D.acs[j]).isCell = true then 1 else 0 : ℕ) : ZMod p) ∧
      ((ComplJ9BBalF.HA D (tlN' D.acs[j])).2 : ZMod p) =
        (if (tlN' D.acs[j]).isCell = true then ((List.idxOf (tlN' D.acs[j]) D.acs : ℕ) : ZMod p)
          else ((V1J8.Gen.atomV (tlN' D.acs[j]) : ℕ) : ZMod p)) := by
    have htl : tlN' D.acs[j] = if 3 ≤ l.length then V1J8.Gen.combOf l.tail else .atom (l.getD 1 0) := by
      rw [hgetE, hl, ComplJ8Atom.tl_combOf l h2]
    by_cases h3 : 3 ≤ l.length
    · have hc : (tlN' D.acs[j]).isCell = true := by
        rw [htl, if_pos h3]; exact ComplJ8Atom.combOf_isCell _ (by rw [List.length_tail]; omega)
      have hm := hcell hc
      rw [if_pos hc, if_pos hc]
      cases hy : tlN' D.acs[j] with
      | atom v => rw [hy] at hc; simp [Noun.isCell] at hc
      | cell a c =>
        rw [hy] at hm
        simp only [ComplJ9BBalF.HA, V1J8.Gen.hdl, genIdxOf_eq _ _ hm]
        simp
    · have ha : tlN' D.acs[j] = .atom (l.getD 1 0) := by rw [htl, if_neg h3]
      have hv : l.getD 1 0 < p := by
        by_cases h : 1 < l.length
        · rw [List.getD_eq_getElem _ _ h]; exact hlimb _ (List.getElem_mem _)
        · omega
      rw [ha]
      simp only [Noun.isCell, Bool.false_eq_true, if_false, ComplJ9BBalF.HA, ComplJ9BBalV.hdl_small hpG _ _ hv,
        V1J8.Gen.atomV]
      simp
  have hidx : (vValsC9 δ D χ ⟨k, hk⟩).idx = ((j : ℕ) : ZMod p) := rfl
  have eR1 : kRV9 D ⟨k, hk⟩ = ((if (tlN' D.acs[j]).isCell = true then 1 else 0 : ℕ) : ZMod p) := by
    show ((ComplJ9BBalF.HA D (VclL.tlN (vNode D k))).1 : ZMod p) = _
    rw [etl]; exact hR.1
  have eR2 : vRV9 D ⟨k, hk⟩ = (if (tlN' D.acs[j]).isCell = true then ((ComplJ8Data.ptrP p D.acs D.rows D.acs[j] : ℕ) : ZMod p)
          else ((V1J8.Gen.atomV (tlN' D.acs[j]) : ℕ) : ZMod p)) := by
    have hvn : vNode D k = D.acs[j] := hgetE.symm
    show (if (VclL.tlN (vNode D k)).isCell then ((ComplJ8Data.ptrP p D.acs D.rows (vNode D k) : ℕ) : ZMod p)
      else ((ComplJ9BBalF.HA D (VclL.tlN (vNode D k))).2 : ZMod p)) = _
    rw [etl, hvn]
    by_cases hc : (tlN' D.acs[j]).isCell = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, hR.2, if_neg hc]
  rw [hidx, eR1, eR2, show kLV9 D ⟨k, hk⟩ = 0 from hk0.1, show vLV9 D ⟨k, hk⟩ = ((l.headD 0 : ℕ) : ZMod p) from hk0.2]
  rfl

/-- **`vhX9_eq` over a record** (atom walk present; any orbit): the atom-walk handle import is the
atom-walk-weighted atom cell handle sum. -/
theorem vhX9_eq_gen (hpG : p = Nock.Atoms.p) (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length)
    (hcellsC : ∀ c ∈ D.acs, c.isCell = true)
    (hshape : ∀ y ∈ D.acs, ∃ l, 2 ≤ l.length ∧ Nock.Atoms.Canonical l ∧ y = Nock.V1J8.Gen.combOf l)
    (hclosed : ∀ y ∈ D.acs, (tlN y).isCell = true → tlN y ∈ D.acs)
    (hne : D.preads ≠ [])
    (hmxA : D.mxA = Nock.V1J8.Gen.wCounts (ComplJ8Data.rIAP p D.acs) D.acs D.vs)
    (hvs : D.vs = (Nock.V1J8.Gen.walkGen (D.acs.headD (.atom 0)) D.preads).1)
    (hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true) (hwalkA : ComplJ8Walk.WalkDepthOK D.preads)
    (hwcell : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjA : Function.Injective (powN o D.acs.length))
    (hinjV : Function.Injective (powN o (nVOf D))) (χ : Coins frameJ8 K) :
    ComplJ9BBalF.vhX9 δ b D o χ =
      ∑ j ∈ Finset.range D.acs.length,
        ((D.mxA.getD j 0 : ℕ) : 𝕂′) * (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ := by
  have h62 := ComplJ8Walk.walkDepth62 hwalkA
  have hspec := ComplJ9ABalF2.mxA_spec_gen D hmxA hvs hall h62
  set n := D.acs.length
  set G : ℕ → 𝕂′ := fun j => (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ with hG
  have hF : ∀ u ∈ walkRows D.acs D.preads, _ := fun u hu =>
    ComplJ9BBalF.idxRW_facts D u (hwcell u hu) (hcellsC _ (hwcell u hu))
  have hnV : nVOf D = (walkRows D.acs D.preads).length := by unfold nVOf; rw [if_neg hne]
  have hW : ComplJ9BBalF.vhX9 δ b D o χ =
      ((walkRows D.acs D.preads).map fun u => G (ComplJ9BAWR.idxRW D.acs (ComplJ9BBalF.rIA D) u)).sum := by
    unfold ComplJ9BBalF.vhX9
    rw [hnV, ← sum_range_getD' (trie (.atom 0) (.atom 0) [] []) _ (walkRows D.acs D.preads)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have e := awKey_gen δ b hpG D hA hcellsC hshape hclosed hne hwcell o hinjA hinjV χ k (hnV ▸ hk')
    rw [e]
    rw [show (walkRows D.acs D.preads).getD k (trie (.atom 0) (.atom 0) [] []) = wTrie D.acs D.preads k from rfl]
  have hS := sum_serial n (fun u : NTree WN => ComplJ9BAWR.idxRW D.acs (ComplJ9BBalF.rIA D) u) G
    (walkRows D.acs D.preads) (fun u hu => (hF u hu).2.1)
  rw [hW, hS]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  rw [hspec j (Finset.mem_range.mp hj)]
  congr 1
  refine List.filter_congr fun u hu => ?_
  rw [hcellsC _ (hwcell u hu), (hF u hu).2.2]
  simp

end Gen

/-! ## `hbalA'` at `BRun9A` -/

section J9A
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf preadsA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A
local notation "oA" => orbJ8 (j9aDataOf p Rg Rt hgen) (hF_run Rt hgen hpG h31A)

/-- **The atom inc terminal at `DA`, orbit `orbJ8 DA`** (`incT9` with no J-8 run binder: `genHyp_mbXA`,
`acs_okA`). -/
theorem incT_A (χ : Coins frameJ8 K) :
      ∑ j ∈ Finset.range (DA).acs.length,
        liftQ δ (HonestA8.cNat j (newBA (DA) AtomChipHQ.inc)) *
          (HonestA8.dNat δ (HonestA8.dC δ b (ComplJ9ADataRec.acsA_pos Rt hgen) (powN (oA) _)
            (oA) (ChalsAZJ8.chalsAJ8Z δ χ)
            (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (oA) χ)
            (colAH δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (oA) χ
              (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (oA) χ))
            (newBA (DA))) j)⁻¹ =
        ∑ j ∈ Finset.range (DA).acs.length,
          ((((DA).info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) *
            (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (oA) j χ)⁻¹ := by
  subst hpG
  set D := j9aDataOf Nock.Atoms.p Rg Rt hgen with hD
  set o := orbJ8 D (hF_run Rt hgen rfl h31A) with ho
  have hA : 0 < D.acs.length := ComplJ9ADataRec.acsA_pos Rt hgen
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjA := (powN_ok o (le_two_pow_ht D hmA)).1
  have hN := ComplJ9ATables.rows_leA Rg Rt hgen (rows31_of_A h31A)
  have hg := ComplJ9ATables.genHyp_mbXA Rg Rt hgen hN
  obtain ⟨-, -, htl⟩ := ComplJ9ATables.acs_okA Rg Rt hgen hN (rows31_of_A h31A _ hmA)
  set T := ComplJ8Atom.tabOf D.acs D.info D.mb D.rows with hT
  set G : ℕ → Quad (algebraMap (ZMod Nock.Atoms.p) K δ) := fun j =>
    (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ with hG
  set J : ℕ → ℕ := fun m => (T.row m).idxO with hJ
  set C := (List.range D.acs.length).filter fun m => T.inc m with hCdef
  have hold : ∀ m, T.inc m = true → D.acs[J m]? = some (Nock.V1J8.Gen.combOf (T.lo m)) ∧
      J m < D.acs.length ∧ 2 ≤ (T.lo m).length ∧ Nock.V1J8.Gen.combOf (T.lo m) ∈ D.acs := by
    intro m hm
    obtain ⟨-, h2, hmem⟩ := ComplJ8Atom.inc_old _ _ _ _ hg m hm
    obtain ⟨hl, he⟩ := ComplJ8Atom.idxO_copy _ _ _ _ hg m hm
    exact ⟨he, hl, h2, hmem⟩
  have hterm : ∀ j ∈ Finset.range D.acs.length,
      liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.inc)) *
        (HonestA8.dNat δ (HonestA8.dC δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) (pubsAOf δ b D hA o χ)
          (colAH δ b D hA o χ (pubsAOf δ b D hA o χ)) (newBA D)) j)⁻¹ =
      if T.inc j = true then G (J j) else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [HonestA8.cNat, HonestA8.dNat, dif_pos hj']
    rw [newBA_inc]
    by_cases hi : T.inc j = true
    · have hi' : (D.info.getD j Nock.V1J8.Gen.AInfo.z).inc = true := hi
      rw [if_pos hi', if_pos hi]
      obtain ⟨eJ, hJn, h2, hmem⟩ := hold j hi
      set l := T.lo j with hl
      rw [dC_key δ b D hA o hinjA χ _ ⟨j, hj'⟩]
      simp only [Fin.val_mk, liftQ, map_one, one_mul, hG]
      have hget : D.acs[J j]'hJn = Nock.V1J8.Gen.combOf l := by
        rw [List.getElem?_eq_getElem hJn] at eJ; exact Option.some.inj eJ
      have hhd : Nock.V1J8.Gen.hdN' D.acs[J j] = .atom (l.headD 0) := by rw [hget, ComplJ8Atom.hd_combOf l h2]
      rw [aHx_gen δ b D hA o hinjA χ (J j) hJn (by rw [hhd]; rfl), hhd]
      have hrow : (T.row j).idxO = J j ∧ (T.row j).lO = l.headD 0 ∧
          (T.row j).kRO = (if 3 ≤ l.length then 1 else 0) ∧
          (T.row j).vRO = (if 3 ≤ l.length then T.ip l else l.getD 1 0) := by
        refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [ComplJ8Atom.AtomTab.row, hi, hl]
      rw [hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2]
      have htl' := ComplJ8Atom.tl_combOf l h2
      by_cases h3 : 3 ≤ l.length
      · have e2 : Nock.V1J8.Gen.tlN' D.acs[J j] = Nock.V1J8.Gen.combOf l.tail := by rw [hget, htl', if_pos h3]
        have hc : (Nock.V1J8.Gen.tlN' D.acs[J j]).isCell = true := by
          rw [e2]; exact ComplJ8Atom.combOf_isCell _ (by rw [List.length_tail]; omega)
        have hm2 : Nock.V1J8.Gen.combOf l.tail ∈ D.acs := e2 ▸ htl _ (List.getElem_mem _) hc
        have hix : T.ip l = ComplJ8Data.ptrP Nock.Atoms.p D.acs D.rows D.acs[J j] := by
          show ComplJ8Data.ptrP Nock.Atoms.p D.acs D.rows (Nock.V1J8.Gen.combOf l) = _
          rw [hget]
        have hc' : (Nock.V1J8.Gen.combOf l.tail).isCell = true := e2 ▸ hc
        simp only [if_pos h3, hc', if_true, hix, e2, Nock.V1J8.Gen.atomV]
      · have e2 : Nock.V1J8.Gen.tlN' D.acs[J j] = .atom (l.getD 1 0) := by rw [hget, htl', if_neg h3]
        simp only [if_neg h3, e2, Noun.isCell, Bool.false_eq_true, if_false, Nock.V1J8.Gen.atomV]
    · have hi' : ¬ (D.info.getD j Nock.V1J8.Gen.AInfo.z).inc = true := hi
      rw [if_neg hi', if_neg hi]
      simp only [liftQ, map_zero, zero_mul]
  rw [Finset.sum_congr rfl hterm, sum_range_ite_list (fun m => T.inc m) (fun m => G (J m)) D.acs.length]
  have hss := sum_serial D.acs.length J G C (fun m hm => (hold m (List.mem_filter.mp hm).2).2.1)
  rw [hss]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  congr 1
  set Fd := ComplJ8Atom.infoFold Nock.Atoms.p D.acs D.rows with hFd
  have hinfo : D.info = Nock.V1J8.Gen.recountMhx Fd := ComplJ8Atom.infoOfP_eq _ _ _
  have hsz : Fd.size = D.acs.length := by
    have := ComplJ8Atom.recountMhx_size Fd
    rw [← hinfo] at this
    rw [← this]
    exact (ComplJ8Atom.stInv_gen _ _ _ _ hg).size
  have hm : (D.info.getD j Nock.V1J8.Gen.AInfo.z).mhx = Nock.V1J8.Gen.mhxOf Fd j := by
    rw [hinfo, ComplJ8Atom.getD_recountMhx, if_pos (by rw [hsz]; exact hj')]
  rw [hm]
  unfold Nock.V1J8.Gen.mhxOf
  rw [toList_eq_range, hsz, List.filter_map, List.length_map, hCdef, List.filter_filter]
  congr 2
  refine List.filter_congr fun m hmr => ?_
  have hR := ComplJ8Atom.recountMhx_fields Fd m
  have e1 : (Fd.getD m Nock.V1J8.Gen.AInfo.z).inc = T.inc m := by
    show _ = (D.info.getD m Nock.V1J8.Gen.AInfo.z).inc; rw [hinfo, hR.1]
  have e2 : (Fd.getD m Nock.V1J8.Gen.AInfo.z).idxO = (D.info.getD m Nock.V1J8.Gen.AInfo.z).idxO := by
    rw [hinfo, hR.2.2.2.1]
  have e3 : (T.row m).idxO = (D.info.getD m Nock.V1J8.Gen.AInfo.z).idxO :=
    (ComplJ8Atom.row_info _ _ _ _ hg m).2.2.2.1
  simp only [Function.comp, e1, e2, hJ, e3]
  cases T.inc m <;> simp <;> exact Bool.eq_iff_iff.mpr (by simp)

/-- **`balV`'s second clause at `DA`, orbit `orbJ8 DA`** (every coin): the atom table's handle export plus the
J-9 A atom walk's handle import balance the atom inc terminal.  Read facts `hallA hwA`, binders
`hax9 hwalkA`. -/
theorem balV2_A (hax9 : ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hallA : ∀ x ∈ (DA).preads, VclL.isPathAx x.2 = true)
    (hwA : ∀ u ∈ walkRows (DA).acs (DA).preads, u.label.node ∈ (DA).acs) (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ)
        (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (oA) χ CellHQ.pubHQ)
        (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (oA) χ (CellHQ.pubHQ + 1)) =
      Quad.mk (algebraMap (ZMod p) K δ)
          (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (oA) χ AtomChipHQ.pubC)
          (pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (oA) χ (AtomChipHQ.pubC + 1)) +
        Quad.mk (algebraMap (ZMod p) K δ)
          (ComplJ9BBalF.pubsVOf9 δ b (DA) (oA) χ WalkHQ.pubXQ)
          (ComplJ9BBalF.pubsVOf9 δ b (DA) (oA) χ (WalkHQ.pubXQ + 1)) := by
  set D := DA with hD
  set o := oA with ho
  have hA : 0 < D.acs.length := ComplJ9ADataRec.acsA_pos Rt hgen
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjA := (powN_ok o (le_two_pow_ht D hmA)).1
  have hinjV := (powN_ok o (le_two_pow_ht D hmV)).1
  set G : ℕ → 𝕂′ := fun j => (ComplJ8Bad.ρH δ χ + ComplJ8OfAtom.aHx δ b D hA o j χ)⁻¹ with hG
  obtain ⟨-, -, tHQ, -, tC, -⟩ := ComplJ8OfAtom.atomTerms δ b D hA o χ
  show Quad.mk _ (pubsAOf δ b D hA o χ CellHQ.pubHQ) (pubsAOf δ b D hA o χ (CellHQ.pubHQ + 1)) =
    Quad.mk _ (pubsAOf δ b D hA o χ AtomChipHQ.pubC) (pubsAOf δ b D hA o χ (AtomChipHQ.pubC + 1)) +
      Quad.mk _ (ComplJ9BBalF.pubsVOf9 δ b D o χ WalkHQ.pubXQ) (ComplJ9BBalF.pubsVOf9 δ b D o χ (WalkHQ.pubXQ + 1))
  rw [tHQ, tC, incT_A δ b Rt hgen hpG h31A χ]
  have hL : ∑ j ∈ Finset.range D.acs.length, liftQ δ (CellTraceH.mN (mhvA D) j) *
      (CellTraceHQ.dN δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ)
        (pubsAOf δ b D hA o χ) (aCol δ b D χ) (mhvA D) j)⁻¹ =
      ∑ j ∈ Finset.range D.acs.length, (((D.info.getD j Nock.V1J8.Gen.AInfo.z).mhx : ℕ) : 𝕂′) * G j +
      ∑ j ∈ Finset.range D.acs.length, ((D.mhA.getD j 0 : ℕ) : 𝕂′) * G j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    simp only [CellTraceH.mN, CellTraceHQ.dN, dif_pos hj', hG]
    rw [ComplJ8OfAtom.aRow_split δ b D hA o χ _ ⟨j, hj'⟩]
    simp only [mhvA, mhAF, liftQ, Nat.cast_add, map_add, map_natCast]
    ring
  rw [hL]
  congr 1
  have hvsdef : D.vs = (if D.preads.isEmpty then (([], 0) : List Nock.V1J8.Gen.WRow × ℕ)
      else Nock.V1J8.Gen.walkGen Nock.V1J8.Gen.padN D.preads).1 := rfl
  have hmhA : D.mhA = Nock.V1J8.Gen.wCounts (ComplJ8Data.rIAP p D.acs) D.acs D.vs := rfl
  by_cases h0 : D.preads = []
  · have hz : (0 : 𝕂′) = Quad.mk _ 0 0 := ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
    have hv : ∀ i, ComplJ9BBalF.pubsVOf9 δ b D o χ i = 0 := fun i => by
      simp [ComplJ9BBalF.pubsVOf9, h0]
    rw [hv, hv, ← hz]
    have hvs0 : D.vs = [] := by rw [hvsdef, if_pos (by simp [h0])]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hm : D.mhA.getD j 0 = 0 := by
      rw [hmhA, ComplJ8Data.wCounts_eq, ComplJ8Data.bumpAll0_getD _ _ _ (Finset.mem_range.mp hj), hvs0]
      simp [ComplJ8Data.wPairs, ComplJ8Data.sumAt]
    simp [hm]
  · have h4 : ComplJ9BBalF.pubsVOf9 δ b D o χ WalkHQ.pubXQ = pub2 δ (ComplJ9BBalF.vhX9 δ b D o χ) 4 := by
      simp [ComplJ9BBalF.pubsVOf9, h0, WalkHQ.pubXQ]
    have h5 : ComplJ9BBalF.pubsVOf9 δ b D o χ (WalkHQ.pubXQ + 1) = pub2 δ (ComplJ9BBalF.vhX9 δ b D o χ) 5 := by
      simp [ComplJ9BBalF.pubsVOf9, h0, WalkHQ.pubXQ]
    have hvs : D.vs = (Nock.V1J8.Gen.walkGen (D.acs.headD (.atom 0)) D.preads).1 := by
      rw [hvsdef, if_neg (by simpa using h0)]
      exact walkGen_dummy _ _ _ h0
    have hcellsC : ∀ c ∈ D.acs, c.isCell = true := ComplJ8OfBal.acs_cell Rt hgen hpG
    have hshape := ComplJ9BBalV.acs_shape Rt hgen hpG
    have hclosed : ∀ y ∈ D.acs, (tlN y).isCell = true → tlN y ∈ D.acs := fun y hy =>
      (ComplJ8OfBal.acs_closed_run Rt hgen hpG y hy).2
    rw [h4, h5, pub2_mk2 δ _ 4 rfl,
      vhX9_eq_gen δ b hpG D hA hcellsC hshape hclosed h0 rfl hvs hallA
        (ComplJ9ADataRec.walkDepthOK_preadsA Rt hgen hax9 hwalkA) hwA o hinjA hinjV χ]
    refine Finset.sum_congr rfl fun j hj => ?_
    rfl

/-- **`hbalA'` at `BRun9A`** (the `hbalA'` field of `ComplJ9AObligations`, verbatim), from the J-9 A atom-walk
read facts `hallA` (every read is at a path axis) and `hwA` (every atom-walk node is an atom cell).
Binders `hax9 hwalkA`. -/
theorem hbalA_A_of (hax9 : ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hallA : ∀ x ∈ (DA).preads, VclL.isPathAx x.2 = true)
    (hwA : ∀ u ∈ walkRows (DA).acs (DA).preads, u.label.node ∈ (DA).acs) :
    ∀ χ, (BA).Good χ →
      Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsA CellHQ.pubHQ) (((BA).M χ).pubsA (CellHQ.pubHQ + 1)) =
        Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsA AtomChipHQ.pubC)
            (((BA).M χ).pubsA (AtomChipHQ.pubC + 1)) +
          Quad.mk (algebraMap (ZMod p) K δ) (((BA).M χ).pubsV WalkHQ.pubXQ)
            (((BA).M χ).pubsV (WalkHQ.pubXQ + 1)) := by
  intro χ _
  have eA : ((BA).M χ).pubsA = pubsAOf δ b (DA) (ComplJ9ADataRec.acsA_pos Rt hgen) (oA) χ := rfl
  have eV : ((BA).M χ).pubsV = ComplJ9BBalF.pubsVOf9 δ b (DA) (oA) χ := rfl
  rw [eA, eV]
  exact balV2_A δ b Rt hgen hpG h31A hax9 hwalkA hallA hwA χ

end J9A

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalV2

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalV2
#print axioms awKey_gen
#print axioms vhX9_eq_gen
#print axioms incT_A
#print axioms balV2_A
#print axioms hbalA_A_of
end Axioms
