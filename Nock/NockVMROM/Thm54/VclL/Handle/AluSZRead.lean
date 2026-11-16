/-
  Chip: `H/AluSZChipJ9.lean`.  * §1 **The third consumer list (the served route).**  The cell validity balance is
    `CellTwinK.ValidityBalanced2 t vp vl` (cell rows + external providers `vp` provide; cell children + the lookups
    `vl` consume).  The ALU is a third consumer list: instantiate `vl := claimRecs ++ alu`.  Nothing new is needed:
    `cellServed_of_balanced3` is `TwoProviderQ.served2_of_balanced2` at `vl ++ alu` (the cell children stay served),
    and `aluServed_of_balanced3` gives every ALU key the served form `Served2 t vp k` (a provider of the
    two-provider multiset).  `mem_vp_of_served_rank0`: a served key of rank `(0, 0)` is an external provider
    (`CellTwinK.no_cell_provides_rank0`).
  * §2 **`fp_read_sound`**: an ALU validity read `(⟨z, 0, L⟩, 0, 0, v)` (the chip's `[z, 0, L, 0, v]`, rank `0 + 0√δ`)
    that is served (the parameter `hserved`, the final assembly discharges it from the balance) names an exported (`mb ≠ 0`) row of
    the atom table: `∃ l, Denotes r v l ∧ p ≤ val l ∧ Canonical l ∧ L = horner y l ∧ D (2, v) = atom (val l)`
    (`D = denK tb (extB p r)` for every cell table `tb`, and also `extA r v`).  Route: §1, then
    `AtomLeavesUJ8.mbVp_atomLeavesU` (g4 + g5 + T1 on the atom table, `leaf_eq_leafVal`), `extB`'s choice,
    `AtomCombJ8.denotes_last_ne` + `topNZ_of_gates` (g3), `Denotes.bounded` (g1), `G5J8.leafVal_val`.
    `fp_read_sound_aeval`: the same with `L = aeval y (limbPoly l)`.
  * §3 per-row helpers on the ALU gates (`RowGates`: every base gate and every mixed gate of `aluSZChipJ9`
    vanishes at the row): `qz_eq` (a `𝕂′` selector gate at selector value `1`), `lane_nat` (the 32 lane bits give
    `ℓ = e + 2^16·o`, `e, o < 2^16`, `o` = the high half `oE`), `modes_sum` / `hz_one` (one-hot modes on a lane row).
  * §4 **`horner_block`**: a slot of `m ≥ 1` lane rows in a Horner mode (`mS mV mW mQM`), `fst` on its first row
    and `eos` exactly on its last, gives limb lists `ℓs, os` (`ℓs[i]` = the lane value of row `i`, `< B`;
    `os[i] = ℓs[i] / 2^16` = its high half, `< 2^16`) with `H(first) = aeval y (limbPoly ℓs)` and
    `H_O(first) = aeval y (limbPoly os)` (`horner_block_horner`: the same with `horner`).
  * §5 **`split_sound`**: a split slot (`fst = 1`, `mS = 1` on its head) gives `lo hi < B`,
    `sv.val = lo + B·hi < p` (the `< p` gate `sf·ℓ·((ℓ′ − (B − 1))·invP − 1)`), and `H32 = lo + y·hi`.

  All §3–§5 statements are at ROW-ENVIRONMENT level (`Env K`, `Env F` per row, with the next-row reads linked);
  the chip-satisfaction ⇒ per-row-gates step is the `atom_base` pattern (`expandChip_satisfies_iff_language`) and is
  left to the consumer (`AluSZOps`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.AtomLeavesUJ8
import Nock.NockVMROM.Thm54.VclL.Handle.TwoProviderQ
import Nock.NockVMROM.Thm54.VclL.Handle.G5J8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluSZRead

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads atomChipHQ LimbsBounded)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (aEF aEK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.G5J8 (horner aeval_limbPoly)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG CopyG Op)
open Nock.ComputeTable (FP)
open Nock.Atoms (val B Canonical limbPoly Fp)
open Nock.NockVMROM.Thm54.VclL.Chips.CertBound (bits_sum_nat bool_cases)

noncomputable section

/-! ## 1. The ALU as a third consumer list of the cell validity balance -/

section Served
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Algebra (ZMod q) Kfp]

/-- **Served by the two-provider balance**: `k` is in the provider multiset (cell rows' keys, external keys). -/
def Served2 (t : List (CellRow q Kfp)) (vp : List (VKey Kfp)) (k : VKey Kfp) : Prop :=
  k ∈ expand (vProv t ++ vp.map (·, 1))

/-- **The third consumer list does not disturb the cell children**: A-3r's two-provider lemma at
`vl := vl ++ alu`. -/
theorem cellServed_of_balanced3 {t : List (CellRow q Kfp)} {vp vl alu : List (VKey Kfp)}
    (hbal : CellTwinK.ValidityBalanced2 t vp (vl ++ alu)) : ValidityServed2 t vp :=
  TwoProviderQ.served2_of_balanced2 hbal

/-- **Every ALU key is served** by the two-provider balance with the ALU as a third consumer list. -/
theorem aluServed_of_balanced3 {t : List (CellRow q Kfp)} {vp vl alu : List (VKey Kfp)}
    (hbal : CellTwinK.ValidityBalanced2 t vp (vl ++ alu)) {k : VKey Kfp} (hk : k ∈ alu) : Served2 t vp k := by
  have hmem : k ∈ expand (vCons t ++ (vl ++ alu).map (·, 1)) := by
    rw [mem_expand]
    exact ⟨(k, 1), List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_append_right _ hk, rfl⟩),
      one_ne_zero, rfl⟩
  exact hbal.mem_iff.mpr hmem

/-- **A served key of rank `(0, 0)` is an external provider** (no cell row provides rank `(0, 0)`). -/
theorem mem_vp_of_served_rank0 [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} {t : List (CellRow q Kfp)}
    (hrows : ∀ c ∈ t, RowOK z c) {vp : List (VKey Kfp)} {k : VKey Kfp} (hs : Served2 t vp k)
    (h0 : k.2.1 = 0 ∧ k.2.2.1 = 0) : k ∈ vp := by
  unfold Served2 at hs
  rw [expand, List.flatMap_append, List.mem_append] at hs
  rcases hs with hp | hp
  · exact (CellTwinK.no_cell_provides_rank0 hq hrows (k := k) hp h0).elim
  · rw [List.mem_flatMap] at hp
    obtain ⟨kc, hkc, hk⟩ := hp
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hkc
    rw [List.mem_replicate] at hk
    rw [hk.2]; exact hk'

end Served

/-! ## 2. `fp_read_sound` -/

section Read
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Fp (Quad (algebraMap (ZMod p) K δ))]
  {hA nA : ℕ} {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA}
  {chalsA pubsA : ℕ → K}
  {QA : Fin (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "AE" => aEF b nodesA orbitA chalsA pubsA QA

/-- **`fp_read_sound`**: a served ALU validity read `(⟨z, 0, L⟩, 0, 0, v)` (the chip's key `[z, 0, L, 0, v]`) names an
exported row of the atom table: the limb list `l` row `v` denotes is canonical and big, `L` is its limb
polynomial at the limb coin `y`, and the handle `(2, v)` decodes to `atom (val l)`.
Atom-table hypotheses: those of `AtomLeavesUJ8.mbVp_atomLeavesU` (accepted, preprocessing bound, the atom table's
own T1 served, the ℕ reading `r`).  Served hypothesis (`hserved`, the assembly's obligation): the key is in the provider
multiset of the cell validity balance whose external providers are the atom table's exported keys `mbVp`; the cell
table `t` is any list of `RowOK` rows. -/
theorem fp_read_sound (hq : 2 ^ 63 < p) (hpG : p = Nock.Atoms.p)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnp : nA < p) (hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (AE k) (r k)) (hs : ∀ k : Fin nA, SmallU (r k))
    (hidx : ∀ k : Fin nA, (r k).idx = k) (hB : LimbsBounded r) (hwR : ∀ k : Fin nA, (r k).wR ≤ 1)
    (hTout : ∀ j, nA ≤ j → (r j).wR = 0 → (r j).aR ≠ 0)
    (z : 𝕂′) (hzAt : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 37) (chalsA 38) = z)
    {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) 𝕂′] (hqc : 2 ^ 63 < q) {zc : 𝕂′} {t : List (CellRow q 𝕂′)}
    (hrows : ∀ c ∈ t, RowOK zc c) {L : 𝕂′} {v : ℕ}
    (hserved : Served2 t (AcceptsJ8P.mbVp δ b nodesA orbitA chalsA pubsA QA) (FP.atomFP z L, 0, 0, v)) :
    ∃ l : List ℕ, Denotes r v l ∧ Nock.Atoms.p ≤ val l ∧ Canonical l ∧
      L = horner (Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3)) l ∧
      (∀ tb : List (CellRowB0 q), denK tb (extB p r) (2, v) = some (.atom (val l))) ∧
      AtomDenJ8.extA r v = some (.atom (val l)) := by
  set y := Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) with hyd
  -- rank 0 ⇒ an exported key of the atom table
  have hk := mem_vp_of_served_rank0 hqc hrows hserved ⟨rfl, rfl⟩
  have hAL := AtomLeavesUJ8.mbVp_atomLeavesU hq hpG hsat hbind hinj hadj hnp hy hservedA hR hs hidx hB hwR hTout z
    hzAt
  obtain ⟨-, -, v', hext, hfp⟩ := hAL _ hk
  try dsimp only at hext hfp
  -- `extB`'s choice: a denoted big limb list
  have hex : ∃ l, Denotes r v l ∧ p ≤ val l := by
    by_contra hn
    simp [extB, hn] at hext
  obtain ⟨l, hl, hbig⟩ := hex
  have hext' := AtomBigJ8.extB_of_denotes hl hbig
  rw [hext'] at hext
  have hv' : v' = val l := by
    have := Option.some.inj hext
    injection this with h
    exact h.symm
  subst hv'
  have hbigG : Nock.Atoms.p ≤ val l := hpG ▸ hbig
  have hbd := hl.bounded hB
  have hTZ := AtomLeavesBJ8.topNZ_of_gates hsat hR hTout
  have hcan : Canonical l := ⟨hbd, AtomCombJ8.denotes_last_ne hTZ hl⟩
  -- the leaf: `L = leafVal y (val l) = horner y l`
  have hL : L = Nock.Atoms.leafVal y (val l) := by
    have := congrArg FP.leaf hfp
    simpa [encZY, FP.atomFP] using this
  refine ⟨l, hl, hbigG, hcan, ?_, fun tb => ?_, AtomDenJ8.extA_of_denotes hl⟩
  · rw [hL, G5J8.leafVal_val y hbd hbigG]
  · show extB p r v = _
    exact hext'

/-- `fp_read_sound` with the leaf as the limb polynomial: `L = aeval y (limbPoly l)`. -/
theorem fp_read_sound_aeval (hq : 2 ^ 63 < p) (hpG : p = Nock.Atoms.p)
    (hsat : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbind : (atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinj : Function.Injective nodesA)
    (hadj : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hnp : nA < p) (hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    {r : ℕ → ARow} (hR : ∀ k : Fin nA, Reads (AE k) (r k)) (hs : ∀ k : Fin nA, SmallU (r k))
    (hidx : ∀ k : Fin nA, (r k).idx = k) (hB : LimbsBounded r) (hwR : ∀ k : Fin nA, (r k).wR ≤ 1)
    (hTout : ∀ j, nA ≤ j → (r j).wR = 0 → (r j).aR ≠ 0)
    (z : 𝕂′) (hzAt : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 37) (chalsA 38) = z)
    {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) 𝕂′] (hqc : 2 ^ 63 < q) {zc : 𝕂′} {t : List (CellRow q 𝕂′)}
    (hrows : ∀ c ∈ t, RowOK zc c) {L : 𝕂′} {v : ℕ}
    (hserved : Served2 t (AcceptsJ8P.mbVp δ b nodesA orbitA chalsA pubsA QA) (FP.atomFP z L, 0, 0, v)) :
    ∃ l : List ℕ, Denotes r v l ∧ Nock.Atoms.p ≤ val l ∧ Canonical l ∧
      L = aeval (Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3)) (limbPoly l) ∧
      (∀ tb : List (CellRowB0 q), denK tb (extB p r) (2, v) = some (.atom (val l))) ∧
      AtomDenJ8.extA r v = some (.atom (val l)) := by
  obtain ⟨l, h1, h2, h3, h4, h5, h6⟩ := fp_read_sound hq hpG hsat hbind hinj hadj hnp hy hservedA hR hs hidx hB
    hwR hTout z hzAt hqc hrows hserved
  exact ⟨l, h1, h2, h3, by rw [aeval_limbPoly]; exact h4, h5, h6⟩

end Read

/-! ## 3. Per-row helpers on the ALU gates -/

section Row
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F)

/-- **The ALU's gates at one row**: every base gate and every mixed gate of `aluSZChipJ9` vanishes. -/
def RowGates (eK : Env K) (eF : Env F) : Prop :=
  (∀ g ∈ (baseGates : List (CoeffExpr F)), g.eval eF = 0) ∧ ∀ g ∈ aluMixed δF, g.eval eK eF = 0

variable {δF} {eK : Env K} {eF : Env F}

theorem ag_zero (h : RowGates δF eK eF) {a : AG F} (ha : a ∈ baseAG) : a.gate.eval eF = 0 :=
  h.1 _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem qe_zero (h : RowGates δF eK eF) {e : QE F} (he : e ∈ aluQ δF) : e.ev δF eK eF = 0 :=
  ev_eq_zero_of_gates δF eK eF e fun g hg => h.2 g (List.mem_flatMap.mpr ⟨e, he, hg⟩)

/-- A `𝕂′` selector gate `σ·(a − b)` at a row where `σ = 1`: `a = b`. -/
theorem qz_eq (h : RowGates δF eK eF) {σ : CoeffExpr F} {a b : QE F} (he : qz σ a b ∈ aluQ δF)
    (hσ : σ.eval eF = 1) : a.ev δF eK eF = b.ev δF eK eF := by
  have := qe_zero h he
  simp only [qz, ev_scale, ev_sub, hσ, liftQ, map_one, one_mul] at this
  exact sub_eq_zero.mp this

theorem mem_kind {a : AG F} (ha : a ∈ gKind) : a ∈ baseAG := by
  simp only [baseAG, List.mem_append]; tauto
theorem mem_slot {a : AG F} (ha : a ∈ gSlot) : a ∈ baseAG := by
  simp only [baseAG, List.mem_append]; tauto
theorem mem_compat {a : AG F} (ha : a ∈ gCompat) : a ∈ baseAG := by
  simp only [baseAG, List.mem_append]; tauto
theorem mem_flag {a : AG F} (ha : a ∈ gFlag) : a ∈ baseAG := by
  simp only [baseAG, List.mem_append]; tauto
theorem mem_bits {a : AG F} (ha : a ∈ gBits) : a ∈ baseAG := by
  simp only [baseAG, List.mem_append]; tauto
theorem mem_split {a : AG F} (ha : a ∈ gSplit) : a ∈ baseAG := by
  simp only [baseAG, List.mem_append]; tauto

theorem mem_identQ {e : QE F} (he : e ∈ identQ δF) : e ∈ aluQ δF := List.mem_append_left _ he

/-- Lane bit `t < 32` is boolean. -/
theorem bit_bool (h : RowGates δF eK eF) {t : ℕ} (ht : t < 32) :
    eF.trace (bt0 + t) * (eF.trace (bt0 + t) - 1) = 0 := by
  have hm : (ar (boolE (cv (bt0 + t))) : AG F) ∈ gBits :=
    List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  simpa [AG.gate, ar, boolE, cv, CoeffExpr.eval] using ag_zero h (mem_bits hm)

/-- **The lane value in ℕ**: `ℓ = e + 2^16·o` with `e, o < 2^16`, `o` the high half `oE`. -/
theorem lane_nat (h : RowGates δF eK eF) :
    ∃ e o : ℕ, e < 2 ^ 16 ∧ o < 2 ^ 16 ∧ (((e + 2 ^ 16 * o : ℕ) : F) = (lE : CoeffExpr F).eval eF) ∧
      ((o : ℕ) : F) = (oE : CoeffExpr F).eval eF := by
  obtain ⟨e, he, hes⟩ := bits_sum_nat (fun i => eF.trace (bt0 + i)) 16
    (fun i hi => bit_bool h (by omega))
  obtain ⟨o, ho, hos⟩ := bits_sum_nat (fun i => eF.trace (bt0 + 16 + i)) 16
    (fun i hi => by rw [Nat.add_assoc]; exact bit_bool h (by omega))
  refine ⟨e, o, he, ho, ?_, ?_⟩
  · rw [lE, eval_bitSum, show (32 : ℕ) = 16 + 16 from rfl, Finset.sum_range_add]
    push_cast
    rw [hes, hos, Finset.mul_sum]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
    rw [pow_add, ← Nat.add_assoc]; ring
  · rw [oE, eval_bitSum]; exact hos

/-- The six modes sum to `sL` (the two `gKind` sum gates). -/
theorem modes_sum (h : RowGates δF eK eF) :
    eF.trace sL = eF.trace mR + eF.trace mS + eF.trace mV + eF.trace mW + eF.trace mQ1 + eF.trace mQM := by
  have g1 := ag_zero h (mem_kind (a := ar (.sub (cv sL) (sumC (roleCols ++ [mQ1, mQM]))))
    (by unfold gKind; exact List.mem_append_right _ (by simp)))
  have g2 := ag_zero h (mem_kind (a := ar (.sub (sumC roleCols) (sumC [mR, mS, mV, mW])))
    (by unfold gKind; exact List.mem_append_right _ (by simp)))
  simp only [AG.gate, ar, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, roleCols, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.sum_cons, List.sum_nil] at g1 g2
  linear_combination g1 + g2

theorem mode_bool (h : RowGates δF eK eF) {j : ℕ} (hj : j ∈ modeCols) :
    ∃ c : ℕ, c ≤ 1 ∧ eF.trace j = c := by
  have hm : (ar (boolE (cv j)) : AG F) ∈ gKind := by
    unfold gKind
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
  have := ag_zero h (mem_kind hm)
  simp only [AG.gate, ar, boolE, cv, CoeffExpr.eval] at this
  rcases bool_cases this with h0 | h1
  · exact ⟨0, by omega, by simp [h0]⟩
  · exact ⟨1, le_rfl, by simp [h1]⟩

/-- **One-hot modes on a lane row**: if `sL = 1` and the Horner mode `md` is `1`, then `hz = 1` and
`mQ1 = 0`. -/
theorem hz_one (hq : 2 ^ 63 < ringChar F) (h : RowGates δF eK eF) (hsL : eF.trace sL = 1) {md : ℕ}
    (hmd : md ∈ [mS, mV, mW, mQM]) (h1 : eF.trace md = 1) :
    (hz : CoeffExpr F).eval eF = 1 ∧ eF.trace mQ1 = 0 := by
  have hs := modes_sum h
  obtain ⟨cR, hR1, hR⟩ := mode_bool h (j := mR) (by simp [modeCols])
  obtain ⟨cS, hS1, hS⟩ := mode_bool h (j := mS) (by simp [modeCols])
  obtain ⟨cV, hV1, hV⟩ := mode_bool h (j := mV) (by simp [modeCols])
  obtain ⟨cW, hW1, hW⟩ := mode_bool h (j := mW) (by simp [modeCols])
  obtain ⟨c1, h11, h1'⟩ := mode_bool h (j := mQ1) (by simp [modeCols])
  obtain ⟨cM, hM1, hM⟩ := mode_bool h (j := mQM) (by simp [modeCols])
  rw [hsL, hR, hS, hV, hW, h1', hM] at hs
  have hsum : cR + cS + cV + cW + c1 + cM = 1 := by
    have e : (((cR + cS + cV + cW + c1 + cM : ℕ)) : F) = ((1 : ℕ) : F) := by push_cast; exact hs.symm
    exact AtomChipHQ.cast_inj hq (by omega) (by norm_num) e
  have hc : ∀ {c : ℕ}, c ≤ 1 → (c : F) = 1 → c = 1 := fun hc e =>
    AtomChipHQ.cast_inj hq (by omega) (by norm_num) (e.trans Nat.cast_one.symm)
  have hz4 : cS + cV + cW + cM = 1 ∧ c1 = 0 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmd
    rcases hmd with rfl | rfl | rfl | rfl
    · have := hc hS1 (hS ▸ h1); omega
    · have := hc hV1 (hV ▸ h1); omega
    · have := hc hW1 (hW ▸ h1); omega
    · have := hc hM1 (hM ▸ h1); omega
  refine ⟨?_, by rw [h1', hz4.2]; simp⟩
  simp only [hz, sumC, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hS, hV, hW, hM]
  have : (((cS + cV + cW + cM : ℕ)) : F) = 1 := by rw [hz4.1]; simp
  push_cast at this
  linear_combination this

end Row

/-! ## 4. `horner_block` -/

section Horner
variable {F K : Type} [Field F] [Field K] [Algebra F K] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))]

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- The lift of a cast natural. -/
theorem liftQ_natCast (n : ℕ) : liftQ (K := K) δF ((n : ℕ) : F) = ((n : ℕ) : 𝕂′) := by
  simp [liftQ, map_natCast]

/-- **The Horner chain of one `𝕂′` column over a slot** (`H` with `lE`, or `H_O` with `oE`). -/
theorem horner_chain {m : ℕ} (eK : ℕ → Env K) (eF : ℕ → Env F) (hg : ∀ i < m, RowGates δF (eK i) (eF i))
    (hnK : ∀ i, i + 1 < m → ∀ j, (eK i).traceNext j = (eK (i + 1)).trace j)
    {y : 𝕂′} (hy : ∀ i < m, Quad.mk _ ((eK i).chal 2) ((eK i).chal 3) = y)
    (hhz : ∀ i < m, (hz : CoeffExpr F).eval (eF i) = 1)
    (heos : ∀ i, i + 1 < m → (eF i).trace eos = 0) (heosL : (eF (m - 1)).trace eos = 1)
    (col : ℕ) (ex : CoeffExpr F)
    (hstep : qz (.mul hz (notE (cv eos))) (QE.var col) (QE.add (QE.base ex) (QE.mul δF yQ (QE.next col))) ∈
      aluQ δF)
    (hend : qz (.mul hz (cv eos)) (QE.var col) (QE.base ex) ∈ aluQ δF)
    (f : ℕ → ℕ) (hf : ∀ i < m, ((f i : ℕ) : F) = ex.eval (eF i)) :
    ∀ k i, i + k + 1 = m → (QE.var col).ev δF (eK i) (eF i) = horner y ((List.range (k + 1)).map fun j => f (i + j)) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have hi' : i = m - 1 := by omega
    have him : i < m := by omega
    have he : (eF i).trace eos = 1 := by rw [hi']; exact heosL
    have := qz_eq (hg i him) hend (by simp [CoeffExpr.eval, cv, hhz i him, he])
    rw [this, ev_base, ← hf i him, liftQ_natCast]
    simp [horner]
  | succ k ih =>
    intro i hi
    have him : i < m := by omega
    have := qz_eq (hg i him) hstep (by simp [CoeffExpr.eval, notE, cv, hhz i him, heos i (by omega)])
    rw [this, ev_add, ev_base, ev_mul, ← hf i him, liftQ_natCast, ev_next, yQ, ev_chal, hy i him,
      hnK i (by omega) col, hnK i (by omega) (col + 1)]
    have ih' := ih (i + 1) (by omega)
    rw [ev_var] at ih'
    have hr : (List.range (k + 1 + 1)).map (fun j => f (i + j)) =
        f i :: (List.range (k + 1)).map (fun j => f (i + 1 + j)) := by
      rw [List.range_succ_eq_map (n := k + 1), List.map_cons, List.map_map, Nat.add_zero]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, Nat.succ_eq_add_one]
      congr 1; omega
    rw [ih', hr]
    simp [horner]

/-- **`horner_block` (Horner form)**: a slot of `m ≥ 1` lane rows in a Horner mode `md ∈ {mS, mV, mW, mQM}`
(`fst` on row `0`, `md = 1` on row `0`, `eos` exactly on row `m − 1`) has limb lists `ℓs` (the rows' lane values,
`< B`) and `os` (their high halves `ℓs[i] / 2^16`, `< 2^16`) with `H(first) = horner y ℓs` and
`H_O(first) = horner y os`. -/
theorem horner_block_horner (hq : 2 ^ 63 < ringChar F) {m : ℕ} (hm : 0 < m)
    (eK : ℕ → Env K) (eF : ℕ → Env F) (hg : ∀ i < m, RowGates δF (eK i) (eF i))
    (hnF : ∀ i, i + 1 < m → ∀ j, (eF i).traceNext j = (eF (i + 1)).trace j)
    (hnK : ∀ i, i + 1 < m → ∀ j, (eK i).traceNext j = (eK (i + 1)).trace j)
    {y : 𝕂′} (hy : ∀ i < m, Quad.mk _ ((eK i).chal 2) ((eK i).chal 3) = y)
    {md : ℕ} (hmd : md ∈ [mS, mV, mW, mQM]) (hfst : (eF 0).trace fst = 1) (hmd0 : (eF 0).trace md = 1)
    (heos : ∀ i, i + 1 < m → (eF i).trace eos = 0) (heosL : (eF (m - 1)).trace eos = 1) :
    ∃ ls os : List ℕ, ls.length = m ∧ os.length = m ∧ (∀ a ∈ ls, a < B) ∧ (∀ a ∈ os, a < 2 ^ 16) ∧
      (∀ i < m, ((ls.getD i 0 : ℕ) : F) = (lE : CoeffExpr F).eval (eF i) ∧
        ((os.getD i 0 : ℕ) : F) = (oE : CoeffExpr F).eval (eF i) ∧ ls.getD i 0 / 2 ^ 16 = os.getD i 0) ∧
      (QE.var H).ev δF (eK 0) (eF 0) = horner y ls ∧ (QE.var HO).ev δF (eK 0) (eF 0) = horner y os := by
  -- sL and the mode propagate along the slot
  have hprop : ∀ i < m, (eF i).trace sL = 1 ∧ (eF i).trace md = 1 := by
    intro i
    induction i with
    | zero =>
      intro h0
      have g := ag_zero (hg 0 h0) (mem_slot (a := ar (.mul (cv fst) (notE (cv sL))))
        (by unfold gSlot; exact List.mem_append_left _ (by simp)))
      simp only [AG.gate, ar, notE, cv, CoeffExpr.eval, hfst, one_mul] at g
      exact ⟨by linear_combination -g, hmd0⟩
    | succ i ih =>
      intro hi
      obtain ⟨hsL, hmdi⟩ := ih (by omega)
      have he := heos i hi
      have g1 := ag_zero (hg i (by omega))
        (mem_slot (a := ar (prod3 (cv sL) (notE (cv eos)) (notE (nv sL))))
          (by unfold gSlot; exact List.mem_append_left _ (by simp)))
      have hmm : md ∈ roleCols ++ modeCols := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmd
        rcases hmd with rfl | rfl | rfl | rfl <;> simp [roleCols, modeCols]
      have g2 := ag_zero (hg i (by omega))
        (mem_slot (a := ar (prod3 (cv sL) (notE (cv eos)) (.sub (nv md) (cv md))))
          (by unfold gSlot; exact List.mem_append_right _ (List.mem_map.mpr ⟨md, hmm, rfl⟩)))
      simp only [AG.gate, ar, prod3, notE, cv, nv, CoeffExpr.eval, hsL, he, hnF i hi, hmdi] at g1 g2
      exact ⟨by linear_combination -g1, by linear_combination g2⟩
  have hhz : ∀ i < m, (hz : CoeffExpr F).eval (eF i) = 1 := fun i hi =>
    (hz_one hq (hg i hi) (hprop i hi).1 hmd (hprop i hi).2).1
  -- the lanes in ℕ
  have hlane : ∀ i, ∃ e o : ℕ, i < m → (e < 2 ^ 16 ∧ o < 2 ^ 16 ∧
      (((e + 2 ^ 16 * o : ℕ) : F) = (lE : CoeffExpr F).eval (eF i)) ∧ ((o : ℕ) : F) = (oE : CoeffExpr F).eval (eF i)) := by
    intro i
    by_cases hi : i < m
    · obtain ⟨e, o, h⟩ := lane_nat (hg i hi); exact ⟨e, o, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hi⟩
  choose E O hEO using hlane
  set fl : ℕ → ℕ := fun i => E i + 2 ^ 16 * O i with hfl
  refine ⟨(List.range m).map fl, (List.range m).map O, by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    obtain ⟨h1, h2, -⟩ := hEO i (List.mem_range.mp hi)
    show E i + 2 ^ 16 * O i < B
    rw [Nock.Atoms.B_eq]; norm_num at h1 h2 ⊢; omega
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact (hEO i (List.mem_range.mp hi)).2.1
  · intro i hi
    have h := hEO i hi
    have g1 : ((List.range m).map fl).getD i 0 = fl i := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    have g2 : ((List.range m).map O).getD i 0 = O i := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rw [g1, g2]
    refine ⟨h.2.2.1, h.2.2.2, ?_⟩
    show (E i + 2 ^ 16 * O i) / 2 ^ 16 = O i
    rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt h.1, zero_add]
  · have := horner_chain eK eF hg hnK hy hhz heos heosL H lE (mem_identQ (by simp [identQ]))
      (mem_identQ (by simp [identQ])) fl (fun i hi => (hEO i hi).2.2.1) (m - 1) 0 (by omega)
    rw [this, show m - 1 + 1 = m by omega]
    simp
  · have := horner_chain eK eF hg hnK hy hhz heos heosL HO oE (mem_identQ (by simp [identQ]))
      (mem_identQ (by simp [identQ])) O (fun i hi => (hEO i hi).2.2.2) (m - 1) 0 (by omega)
    rw [this, show m - 1 + 1 = m by omega]
    simp

/-- **`horner_block`**: as `horner_block_horner`, with `H(first) = aeval y (limbPoly ℓs)` and
`H_O(first) = aeval y (limbPoly os)`. -/
theorem horner_block [Algebra Fp 𝕂′] (hq : 2 ^ 63 < ringChar F) {m : ℕ} (hm : 0 < m)
    (eK : ℕ → Env K) (eF : ℕ → Env F) (hg : ∀ i < m, RowGates δF (eK i) (eF i))
    (hnF : ∀ i, i + 1 < m → ∀ j, (eF i).traceNext j = (eF (i + 1)).trace j)
    (hnK : ∀ i, i + 1 < m → ∀ j, (eK i).traceNext j = (eK (i + 1)).trace j)
    {y : 𝕂′} (hy : ∀ i < m, Quad.mk _ ((eK i).chal 2) ((eK i).chal 3) = y)
    {md : ℕ} (hmd : md ∈ [mS, mV, mW, mQM]) (hfst : (eF 0).trace fst = 1) (hmd0 : (eF 0).trace md = 1)
    (heos : ∀ i, i + 1 < m → (eF i).trace eos = 0) (heosL : (eF (m - 1)).trace eos = 1) :
    ∃ ls os : List ℕ, ls.length = m ∧ os.length = m ∧ (∀ a ∈ ls, a < B) ∧ (∀ a ∈ os, a < 2 ^ 16) ∧
      (∀ i < m, ((ls.getD i 0 : ℕ) : F) = (lE : CoeffExpr F).eval (eF i) ∧
        ((os.getD i 0 : ℕ) : F) = (oE : CoeffExpr F).eval (eF i) ∧ ls.getD i 0 / 2 ^ 16 = os.getD i 0) ∧
      (QE.var H).ev δF (eK 0) (eF 0) = aeval y (limbPoly ls) ∧
      (QE.var HO).ev δF (eK 0) (eF 0) = aeval y (limbPoly os) := by
  obtain ⟨ls, os, h1, h2, h3, h4, h5, h6, h7⟩ :=
    horner_block_horner hq hm eK eF hg hnF hnK hy hmd hfst hmd0 heos heosL
  exact ⟨ls, os, h1, h2, h3, h4, h5, by rw [aeval_limbPoly]; exact h6, by rw [aeval_limbPoly]; exact h7⟩

end Horner

/-! ## 5. `split_sound` -/

section Split
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem lN_eval {e0 e1 : Env (ZMod p)} (hn : ∀ j, e0.traceNext j = e1.trace j) :
    (lN : CoeffExpr (ZMod p)).eval e0 = (lE : CoeffExpr (ZMod p)).eval e1 := by
  simp only [lN, lE, bitSum, CoeffExpr.eval_sumList, CoeffExpr.eval, cv, nv, hn]

/-- **`split_sound`**: a split slot (head row `e0` with `fst = 1`, `mS = 1`; the next row `e1`) gives `lo, hi < B`
(the two rows' lane values) with `sv.val = lo + B·hi < p` (the `< p` gate) and `H32 = lo + y·hi`. -/
theorem split_sound (hpG : p = Nock.Atoms.p) (e0K e1K : Env K) (e0F e1F : Env (ZMod p))
    (h0 : RowGates δ e0K e0F) (h1 : RowGates δ e1K e1F)
    (hnF : ∀ j, e0F.traceNext j = e1F.trace j) (hnK : ∀ j, e0K.traceNext j = e1K.trace j)
    {y : 𝕂′} (hy0 : Quad.mk _ (e0K.chal 2) (e0K.chal 3) = y) (hy1 : Quad.mk _ (e1K.chal 2) (e1K.chal 3) = y)
    (hfst : e0F.trace fst = 1) (hmS : e0F.trace mS = 1) :
    ∃ lo hi : ℕ, lo < B ∧ hi < B ∧ (e0F.trace sv).val = lo + B * hi ∧ lo + B * hi < p ∧
      ((lo : ℕ) : ZMod p) = (lE : CoeffExpr (ZMod p)).eval e0F ∧
      ((hi : ℕ) : ZMod p) = (lE : CoeffExpr (ZMod p)).eval e1F ∧
      (QE.var H).ev δ e0K e0F = ((lo : ℕ) : 𝕂′) + y * ((hi : ℕ) : 𝕂′) := by
  have hpn : p = 18446744069414584321 := by rw [hpG]; norm_num [Nock.Field.p]
  have hq : 2 ^ 63 < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n, hpn]; norm_num
  -- the slot flags
  have gsf := ag_zero h0 (mem_flag (a := ar (.sub (cv sf) (.mul (cv fst) (cv mS)))) (by simp [gFlag]))
  have ge0 := ag_zero h0 (mem_compat (a := ar (prod3 (cv fst) (cv mS) (cv eos))) (by simp [gCompat]))
  have ge1 := ag_zero h0 (mem_compat (a := ar (prod3 (cv fst) (cv mS) (notE (nv eos)))) (by simp [gCompat]))
  simp only [AG.gate, ar, prod3, notE, cv, nv, CoeffExpr.eval, hfst, hmS, one_mul, hnF] at gsf ge0 ge1
  have hsf : e0F.trace sf = 1 := by linear_combination gsf
  have heos1 : e1F.trace eos = 1 := by linear_combination -ge1
  -- the Horner block of length 2
  set eK : ℕ → Env K := fun i => if i = 0 then e0K else e1K with heK
  set eF : ℕ → Env (ZMod p) := fun i => if i = 0 then e0F else e1F with heF
  have hg : ∀ i < 2, RowGates δ (eK i) (eF i) := by
    intro i hi; rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [heK, heF, h0, h1]
  obtain ⟨ls, os, hlen, -, hlsB, -, hval, hH, -⟩ := horner_block_horner hq (m := 2) (y := y) (by omega) eK eF hg
    (fun i hi j => by rcases (show i = 0 by omega) with rfl; simpa [heF] using hnF j)
    (fun i hi j => by rcases (show i = 0 by omega) with rfl; simpa [heK] using hnK j)
    (fun i hi => by rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [heK, hy0, hy1])
    (md := mS) (by simp) (by simpa [heF] using hfst) (by simpa [heF] using hmS)
    (fun i hi => by rcases (show i = 0 by omega) with rfl; simpa [heF] using ge0)
    (by simpa [heF] using heos1)
  rcases ls with _ | ⟨lo, _ | ⟨hi, _ | ⟨c, t⟩⟩⟩
  · simp only [List.length_nil] at hlen; omega
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  swap
  · simp only [List.length_cons] at hlen; omega
  have hlo : lo < B := hlsB lo (by simp)
  have hhi : hi < B := hlsB hi (by simp)
  have hv0 : ((lo : ℕ) : ZMod p) = (lE : CoeffExpr (ZMod p)).eval e0F := by
    have := (hval 0 (by omega)).1; simpa [heF] using this
  have hv1 : ((hi : ℕ) : ZMod p) = (lE : CoeffExpr (ZMod p)).eval e1F := by
    have := (hval 1 (by omega)).1; simpa [heF] using this
  -- the split value and the `< p` gate
  have gV := ag_zero h0 (mem_split (a := ar gSplitV) (by simp [gSplit]))
  have gP := ag_zero h0 (mem_split (a := ar gLtP) (by simp [gSplit]))
  have gC := ag_zero h0 (mem_split (a := AG.cp ⟨cv sf, .cur sv, .cur Vc⟩) (by simp [gSplit]))
  have hlN := lN_eval hnF
  simp only [AG.gate, ar, gSplitV, gLtP, CopyG.gate, Op.expr, cv, CoeffExpr.eval, hsf, one_mul, hlN] at gV gP gC
  have hBf : (Bf : ZMod p) = ((B : ℕ) : ZMod p) := by unfold Bf B; push_cast; ring
  rw [← hv0, ← hv1, hBf] at gV gP
  have hsv : e0F.trace sv = ((lo + B * hi : ℕ) : ZMod p) := by
    push_cast; linear_combination gC + gV
  have hBn := Nock.Atoms.B_eq
  have hlt : lo + B * hi < p := by
    rcases mul_eq_zero.mp gP with h | h
    · have : lo = 0 := AtomChipHQ.cast_inj hq (by rw [hBn] at hlo; omega) (by norm_num)
        (h.trans Nat.cast_zero.symm)
      rw [hpn, hBn, this]; rw [hBn] at hhi; omega
    · have hne : hi ≠ B - 1 := by
        intro e; rw [e, Nat.cast_sub (by rw [hBn]; norm_num), Nat.cast_one] at h
        simp at h
      rw [hpn, hBn]; rw [hBn] at hhi hlo hne; omega
  refine ⟨lo, hi, hlo, hhi, ?_, hlt, hv0, hv1, ?_⟩
  · rw [hsv, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  · rw [show e0K = eK 0 by simp [heK], show e0F = eF 0 by simp [heF], hH]
    simp [horner]

end Split

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluSZRead
