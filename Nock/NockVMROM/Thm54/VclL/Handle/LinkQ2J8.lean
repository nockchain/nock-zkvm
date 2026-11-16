/-
  Nock/NockVMROM/Thm54/VclL/Handle/LinkQ2J8.lean

  **The `LinkJ8` fields L5 / L3 / L7.**

  * The atom table's base gates do
    not see `vRO` / `lO` on a non-inc row (`atomGates_update_vRO`, `atomGates_update_lO`, `cellBase_update`).
  * §2 **`houtA`** from summand #4 (`houtA_of_outside`) at a readout of `R.D.axReqs / axProvs` and its budget;
    **`hcountA`** from that budget at the census corner (`hcountA_of_budget`).
  * §3 **`hext`** (`hext_of_rows`): every `extB` atom has `≤ n + 2` limbs at a reader with limbs `< B` whose rows
    past `n` are unweighted (`denotes_length_le`: the weighted rows a denotation visits are distinct).
  * §6 the canonical reader `valReader` (`ZMod.val` of each column): `hRA`, `hrn`, `hwRA` discharged.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree pair_notMem_of_io)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)

noncomputable section

/-! ## 1. -/

section S1

/-- A natural `< 2^62` never casts to `-1` in `ZMod p` once `2^62 + 1 < p`. -/
theorem natCast_ne_neg_one {p : ℕ} [Fact p.Prime] (hp : 2 ^ 62 + 1 < p) {x : ℕ} (hx : x < 2 ^ 62) :
    ((x : ℕ) : ZMod p) ≠ -1 := by
  intro h
  have h0 : ((x + 1 : ℕ) : ZMod p) = 0 := by push_cast; rw [h]; ring
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd (by omega) h0
  omega

/-- **S1 witness (reader half), `vRO`**: a row whose `vRO` column is `-1` has no `Small` reading. -/
theorem not_small_of_vRO {p : ℕ} [Fact p.Prime] (hp : 2 ^ 62 + 1 < p) {e : Env (ZMod p)} {a : ARow}
    (hr : Reads e a) (h : e.trace AtomChipHQ.vRO = -1) : ¬ a.Small := by
  intro hs
  exact natCast_ne_neg_one hp hs.2.2.2.2.2.2.2.2.2.2 (hr.vRO.symm.trans h)

/-- **S1 witness (reader half), `lO`**. -/
theorem not_small_of_lO {p : ℕ} [Fact p.Prime] (hp : 2 ^ 62 + 1 < p) {e : Env (ZMod p)} {a : ARow}
    (hr : Reads e a) (h : e.trace AtomChipHQ.lO = -1) : ¬ a.Small := by
  intro hs
  exact natCast_ne_neg_one hp hs.2.2.2.2.2.2.2.2.1 (hr.lO.symm.trans h)

/-- **S1 witness (reader half), `idR`**. -/
theorem not_small_of_idR {p : ℕ} [Fact p.Prime] (hp : 2 ^ 62 + 1 < p) {e : Env (ZMod p)} {a : ARow}
    (hr : Reads e a) (h : e.trace Cell.idR = -1) : ¬ a.Small := by
  intro hs
  exact natCast_ne_neg_one hp hs.2.2.2.1 (hr.idR.symm.trans h)

/-- **S1, the `LinkJ8` pair `hRA ∧ hsA` is unsatisfiable** at any trace with one atom row (`k : Fin nA`) whose
`vRO` column holds `-1`: no `rA` reads every row AND is small at every row. -/
theorem no_small_reader {p : ℕ} [Fact p.Prime] (hp : 2 ^ 62 + 1 < p) {nA : ℕ} (env : Fin nA → Env (ZMod p))
    (k : Fin nA) (h : (env k).trace AtomChipHQ.vRO = -1) :
    ¬ ∃ rA : ℕ → ARow, (∀ j : Fin nA, Reads (env j) (rA j)) ∧ ∀ j : Fin nA, (rA j).Small := by
  rintro ⟨rA, hR, hs⟩
  exact not_small_of_vRO hp (hR k) h (hs k)

variable {F : Type} [Field F]

/-- The environment `e` with the current-row column `c` overwritten by `v`. -/
def updCur (e : Env F) (c : ℕ) (v : F) : Env F :=
  { e with trace := Function.update e.trace c v }

/-- **S1 witness (gate half), `vRO`**: on a row with `inc = 0` and `c_out = 0` (`(1 − inc)·c_out` forces the
latter), every added base gate of the atom table evaluates the same whatever `vRO` holds. -/
theorem atomGates_update_vRO (e : Env F) (v : F) (hinc : e.trace AtomChipHQ.inc = 0)
    (hcout : e.trace AtomChipHQ.cout = 0) :
    ∀ g ∈ (AtomChipHQ.atomGates (F := F)), g.eval (updCur e AtomChipHQ.vRO v) = g.eval e := by
  simp only [AtomChipHQ.inc, AtomChipHQ.cout] at hinc hcout
  simp [AtomChipHQ.atomGates, AtomChipHQ.g1, AtomChipHQ.g23, AtomChipHQ.bnd, AtomChipHQ.g70,
    AtomChipHQ.g71, AtomChipHQ.g72, AtomChipHQ.g73, AtomChipHQ.ovf, AtomChipHQ.g74, AtomChipHQ.g8, bitSum,
    CoeffExpr.sumList, List.range_succ, AtomChipHQ.valR, CellH.valE, Cell.wL, Cell.wR, Cell.aL, Cell.aR,
    Cell.idR, Cell.idx, AtomChipHQ.bitA, AtomChipHQ.bitR, AtomChipHQ.invT, AtomChipHQ.invB, AtomChipHQ.mb,
    AtomChipHQ.mi, AtomChipHQ.inc, AtomChipHQ.conv, AtomChipHQ.cout, AtomChipHQ.idxO, AtomChipHQ.lO,
    AtomChipHQ.kRO, AtomChipHQ.vRO, updCur, CoeffExpr.eval, Function.update_apply, hinc, hcout]

/-- **S1 witness (gate half), `lO`**: the same on a row with `inc = 0`. -/
theorem atomGates_update_lO (e : Env F) (v : F) (hinc : e.trace AtomChipHQ.inc = 0) :
    ∀ g ∈ (AtomChipHQ.atomGates (F := F)), g.eval (updCur e AtomChipHQ.lO v) = g.eval e := by
  simp only [AtomChipHQ.inc] at hinc
  simp [AtomChipHQ.atomGates, AtomChipHQ.g1, AtomChipHQ.g23, AtomChipHQ.bnd, AtomChipHQ.g70,
    AtomChipHQ.g71, AtomChipHQ.g72, AtomChipHQ.g73, AtomChipHQ.ovf, AtomChipHQ.g74, AtomChipHQ.g8, bitSum,
    CoeffExpr.sumList, List.range_succ, AtomChipHQ.valR, CellH.valE, Cell.wL, Cell.wR, Cell.aL, Cell.aR,
    Cell.idR, Cell.idx, AtomChipHQ.bitA, AtomChipHQ.bitR, AtomChipHQ.invT, AtomChipHQ.invB, AtomChipHQ.mb,
    AtomChipHQ.mi, AtomChipHQ.inc, AtomChipHQ.conv, AtomChipHQ.cout, AtomChipHQ.idxO, AtomChipHQ.lO,
    AtomChipHQ.kRO, AtomChipHQ.vRO, updCur, CoeffExpr.eval, Function.update_apply, hinc]

/-- The cell base gates read columns `< 129` only, so they never see `vRO` (`203`), `lO` (`201`). -/
theorem cellBase_update (e : Env F) {c : ℕ} (hc : 129 ≤ c) (v : F) :
    ∀ g ∈ (Cell.baseGates (F := F)), g.eval (updCur e c v) = g.eval e := by
  intro g hg
  exact (Nock.NockVMROM.Thm54.VclL.Handle.colsBelow_eval (Nock.NockVMROM.Thm54.VclL.Handle.cellBase_below g hg)
    (fun j hj => by simp [updCur, Function.update_apply, show j ≠ c by omega]) (fun j hj => rfl))

end S1

/-! ## 2. `houtA` from summand #4, `hcountA` from its budget -/

section Export
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- #4 at `R.D`'s atom-export lists: the handle coins `(gamHQ, rhoHQ)` are outside its IO event. -/
theorem hout_ax_of_outside (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ sumJ8 R .atomExport, ¬ s.mem tr χ)
    (h1 : (R.axReqs tr χ).length ≤ r.A + r.inc + r.AW) (h2 : (R.axProvs tr χ).length ≤ r.A) :
    (gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)) ∉ IOFailureEventW (R.axReqs tr χ) (R.axProvs tr χ) := by
  have hs := h
  simp only [sumJ8, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at hs
  exact pair_notMem_of_io _ _ _ St _ _ _ _ _ hs h1 h2

/-- **`houtA` outside summand #4**: if `R`'s atom-export readout at `(tr, χ)` is `(reqs, provs)` within the #4
budgets `A + inc + AW` / `A`, then the atom table's handle coins `acoins (chalsAJ8 χ)` are outside the IO event. -/
theorem houtA_of_outside
    (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ)
    (reqs : List (Fin 5 → 𝕂′)) (provs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hr : R.D.axReqs tr χ = reqs) (hp : R.D.axProvs tr χ = provs)
    (h1 : reqs.length ≤ r.A + r.inc + r.AW) (h2 : provs.length ≤ r.A) :
    ((AtomServedQ.acoins δ (chalsAJ8 δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8 δ χ)).pole) ∉
      IOFailureEventW reqs provs := by
  have e : AtomServedQ.acoins δ (chalsAJ8 δ χ) = (⟨gamHQ δ (toVSQ χ), rhoHQ δ (toVSQ χ)⟩ : IOCoins 𝕂′) :=
    VerJ8.mcoins_of_agree δ χ (chalsAJ8 δ χ) (chalsAJ8_agree (δ := δ) χ)
  have H := hout_ax_of_outside R.D (outside_sumJ8_D R h .atomExport (by decide) (by decide) (by decide))
    (hr ▸ h1) (hp ▸ h2)
  rw [hr, hp] at H
  rw [e]
  exact H

/-- **`hcountA` at the census corner**: a list within the #4 consumer budget is shorter than `p`. -/
theorem hcountA_of_budget {α : Type} {l : List α} (hpG : p = Nock.Atoms.p)
    (hr : RowsLe r EncInjJ8.cornerC) (h1 : l.length ≤ r.A + r.inc + r.AW) : l.length < p := by
  obtain ⟨-, -, -, -, hA, hAW, -, -, hinc, -⟩ := hr
  have e1 : EncInjJ8.cornerC.A = 2 ^ 31 := rfl
  have e2 : EncInjJ8.cornerC.AW = 2 ^ 31 := rfl
  have e3 : EncInjJ8.cornerC.inc = 2 ^ 31 := rfl
  have hp : 3 * 2 ^ 31 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  omega

end Export

/-! ## 3. L3 `hext`: every big-row atom has at most `nA + 2` limbs -/

section Hext
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (Denotes LimbsBounded)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Atoms (val B lenL limbs)

/-- The weighted rows a denotation steps through are distinct, each carries `wR = 1`, and there are
`l.length − 2` of them. -/
theorem denotes_rows {r : ℕ → ARow} {i : ℕ} {l : List ℕ} (h : Denotes r i l) :
    ∃ vs : List ℕ, vs.Nodup ∧ vs.length + 2 = l.length ∧
      ∀ k ∈ vs, (r k).wR = 1 ∧ ∃ s, Denotes r k s ∧ s.length ≤ l.length := by
  induction h with
  | top _ => exact ⟨[], List.nodup_nil, by simp, by simp⟩
  | @step i l' hw hd ih =>
    obtain ⟨vs, hnd, hlen, hvs⟩ := ih
    refine ⟨i :: vs, List.nodup_cons.mpr ⟨fun hi => ?_, hnd⟩, by simp [hlen], ?_⟩
    · obtain ⟨-, s, hs, hsl⟩ := hvs i hi
      have := AtomDenJ8.denotes_unique hs (Denotes.step hw hd)
      subst this
      simp at hsl
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact ⟨hw, _, Denotes.step hw hd, le_rfl⟩
      · obtain ⟨h1, s, hs, hsl⟩ := hvs k hk
        exact ⟨h1, s, hs, hsl.trans (by simp)⟩

/-- **A denotation is at most `n + 2` limbs long** when every row past `n` is unweighted. -/
theorem denotes_length_le {r : ℕ → ARow} {n : ℕ} (hout : ∀ k, n ≤ k → (r k).wR = 0) {i : ℕ} {l : List ℕ}
    (h : Denotes r i l) : l.length ≤ n + 2 := by
  obtain ⟨vs, hnd, hlen, hvs⟩ := denotes_rows h
  have hsub : vs.toFinset ⊆ Finset.range n := by
    intro k hk
    rw [List.mem_toFinset] at hk
    rw [Finset.mem_range]
    by_contra hkn
    have := hout k (by omega)
    rw [(hvs k hk).1] at this
    exact one_ne_zero this
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at this
  omega

/-- `lenL (val l) ≤ l.length` for a nonempty limb list with limbs `< B`. -/
theorem lenL_val_le {l : List ℕ} (hB : ∀ x ∈ l, x < B) (h1 : 1 ≤ l.length) : lenL (val l) ≤ l.length := by
  unfold lenL
  split_ifs
  · exact h1
  · have hb : 1 < B := by norm_num [B]
    have := Nat.ofDigits_lt_base_pow_length hb hB
    exact (Nat.digits_length_le_iff hb _).mpr this

/-- **L3 `hext`**: at any reading `r` whose limbs are `< B` and whose rows past `n` are unweighted, every
`extB` value is an atom of at most `n + 2` limbs; so `hext` holds at every `maxlen ≥ n + 2`. -/
theorem hext_of_rows {q : ℕ} {r : ℕ → ARow} {n maxlen : ℕ} (hB : LimbsBounded r)
    (hout : ∀ k, n ≤ k → (r k).wR = 0) (hM : n + 2 ≤ maxlen) :
    ∀ j m, extB q r j = some m → ∃ v, m = .atom v ∧ lenL v ≤ maxlen := by
  intro j m hj
  unfold extB at hj
  split_ifs at hj with he
  obtain ⟨hd, -⟩ := Classical.choose_spec he
  refine ⟨_, (Option.some.inj hj).symm, ?_⟩
  exact (lenL_val_le (hd.bounded hB) (by have := AtomCombJ8.denotes_len hd; omega)).trans
    ((denotes_length_le hout hd).trans hM)

end Hext

/-! ## 4. L7 `hinjE`: the registered nouns join the census -/

section HinjE
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8
open Nock.Atoms (lenL)
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp] [Fact q.Prime]

/-- **L7 at the table**: if the census readout covers the decoded nouns, the atom children AND a list `G` of
nouns (the registered templates) whose leaves are `≤ fuelChip` and whose atoms have `≤ M` limbs, then `encZY z y`
separates every noun of `G` from every decoded noun. -/
theorem hinjE_of_sep [Algebra Nock.Atoms.Fp Kfp] (hq : 2 ^ 63 < q) {z y : Kfp} (hz : z ≠ 0)
    (hE : InlineAtoms q z (encZY z y)) {t : List (CellRow q Kfp)} {vp : List (VKey Kfp)}
    {ext : ℕ → Option Noun} (h : TableAccepts2 z t vp) (hvp : AtomLeaves (encZY z y) vp ext)
    {k M : ℕ} (hext : ∀ j m, ext j = some m → ∃ v, m = .atom v ∧ lenL v ≤ M)
    (hqM : ∀ x < q, lenL x ≤ M) (hk : 2 * fuelChip ≤ k) {G : List Noun}
    (hG : ∀ n ∈ G, n.leaves ≤ fuelChip ∧ ∀ x ∈ n.leafList, lenL x ≤ M) {prs : List (List ℕ × List ℕ)}
    (hsub : ∀ pr ∈ censusPairs (censusList2 (t.map (·.b0)) ext ++ G), pr ∈ prs) (hsep : SepAt y z prs k M) :
    ∀ x ∈ G, ∀ d ∈ decodedNouns2 (t.map (·.b0)) ext, encZY z y x = encZY z y d → x = d := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hM1 : 1 ≤ M := (Nock.Atoms.one_le_lenL 0).trans (hqM 0 (by have := (Fact.out : q.Prime).pos; omega))
  have hextM : ∀ j m, ext j = some m → ∀ x ∈ m.leafList, lenL x ≤ M := by
    intro j m hj x hx
    obtain ⟨v, rfl, hv⟩ := hext j m hj
    simp only [Noun.leafList, List.mem_singleton] at hx
    exact hx ▸ hv
  have hS : ∀ n ∈ censusList2 (t.map (·.b0)) ext ++ G,
      n.leaves ≤ fuelChip ∧ ∀ x ∈ n.leafList, lenL x ≤ M := by
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · rcases List.mem_append.mp hn with hn | hn
      · refine ⟨decoded2_leaves_le hq (encZY_cell z y) hE h hvp hn, ?_⟩
        obtain ⟨i, -, hd⟩ := List.mem_filterMap.mp hn
        intro x hx
        rcases decodeTree2_atoms _ ext _ _ _ hd x hx with hx | ⟨j, m, hj, hxm⟩
        · exact hqM x hx
        · exact hextM j m hj x hxm
      · obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hn
        obtain ⟨s, -, hs⟩ := List.mem_filterMap.mp hc
        unfold kidOf at hs
        split_ifs at hs with hw h0
        · cases hs
          refine ⟨by simp [Noun.leaves, fuelChip], ?_⟩
          intro x hx
          simp only [Noun.leafList, List.mem_singleton] at hx
          exact hx ▸ hqM _ (ZMod.val_lt _)
        · obtain ⟨v, rfl, hv⟩ := hext _ n hs
          refine ⟨by simp [Noun.leaves, fuelChip], ?_⟩
          intro x hx
          simp only [Noun.leafList, List.mem_singleton] at hx
          exact hx ▸ hv
    · exact hG n hn
  have hinj := encZY_inj_of_sep hz hsub hsep (fun n hn => (hS n hn).1) hk hM1 (fun n hn => (hS n hn).2)
  intro x hx d hd he
  exact hinj x (List.mem_append_right _ hx) d (List.mem_append_left _ (List.mem_append_left _ hd)) he

theorem censusPairs_reg_length_le (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) (G : List Noun)
    (ht : t.length ≤ 2 ^ 31) (hG : G.length ≤ 2 ^ 31) :
    (censusPairs (censusList2 t ext ++ G)).length ≤ 2 ^ 66 := by
  rw [censusPairs_length]
  have h1 := censusList2_length_le t ext
  have h2 : pairCount (censusList2 t ext ++ G).length ≤ pairCount (4 * 2 ^ 31) := by
    apply pairCount_mono; rw [List.length_append]; omega
  have h3 : pairCount (4 * 2 ^ 31) ≤ 2 ^ 65 := by unfold pairCount; norm_num
  omega

end HinjE

/-! ## 5. -/

section HinjOut
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY)
open Nock.Atoms (lenL)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **L7 `hinjE` outside `allJ8C`** (the shape of `encInj2_of_outside`, one list `G` longer): at `E = encZY z y`,
`z = (χ₂, χ₃)`, `y = (χ₁₇, χ₁₈)`, if the census readout `R.D.prs tr` covers `censusList2 … ++ G`, every noun of
`G` with `≤ fuelChip` leaves and `≤ maxlen`-limb atoms is separated from every decoded noun. -/
theorem hinjE_of_outside (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ)
    {qc : ℕ} [Fact qc.Prime] [Algebra (ZMod qc) 𝕂′] (hq : 2 ^ 63 < qc)
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) ≠ 0)
    (hE : InlineAtoms qc (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3))
      (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))))
    {t : List (CellRow qc 𝕂′)} {vp : List (VKey 𝕂′)} {ext : ℕ → Option Noun}
    (htab : TableAccepts2 (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) t vp)
    (hvp : AtomLeaves (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3))
      (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))) vp ext)
    (hext : ∀ j m, ext j = some m → ∃ v, m = .atom v ∧ lenL v ≤ r.maxlen)
    (hqM : ∀ x < qc, lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves) {G : List Noun}
    (hG : ∀ n ∈ G, n.leaves ≤ fuelChip ∧ ∀ x ∈ n.leafList, lenL x ≤ r.maxlen)
    (hprs : ∀ pr ∈ censusPairs (censusList2 (t.map (·.b0)) ext ++ G), pr ∈ R.D.prs tr) :
    ∀ x ∈ G, ∀ d ∈ decodedNouns2 (t.map (·.b0)) ext,
      encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) x =
        encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2)) d →
      x = d :=
  hinjE_of_sep hq hz hE htab hvp hext hqM hk hG hprs
    (fun _pr hpr hlen hne hkk hM1 hM2 => ListJ8C.biv_out_of_outsideC R h hpr hlen hne hkk hM1 hM2)

end HinjOut

/-! ## 6. L5: the canonical reader `rA` (`ZMod.val` of every column) and the fields it discharges -/

section Reader
variable {p : ℕ} [Fact p.Prime]

/-- **The canonical atom-table reader**: row `k < n` reads `ZMod.val` of its eleven chain columns; every row past
`n` is the padding row `(k, 0, 0, 0, 1, 0, …)` (unweighted, top limb `1`, no inc). -/
def valReader {n : ℕ} (e : Fin n → Env (ZMod p)) (k : ℕ) : ARow :=
  if h : k < n then
    let t := (e ⟨k, h⟩).trace
    ⟨(t Cell.idx).val, (t Cell.aL).val, (t Cell.wR).val, (t Cell.idR).val, (t Cell.aR).val,
      (t AtomChipHQ.inc).val, (t AtomChipHQ.cout).val, (t AtomChipHQ.idxO).val, (t AtomChipHQ.lO).val,
      (t AtomChipHQ.kRO).val, (t AtomChipHQ.vRO).val⟩
  else ⟨k, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩

theorem valReader_lt {n : ℕ} (e : Fin n → Env (ZMod p)) (k : Fin n) :
    valReader e k = ⟨((e k).trace Cell.idx).val, ((e k).trace Cell.aL).val, ((e k).trace Cell.wR).val,
      ((e k).trace Cell.idR).val, ((e k).trace Cell.aR).val, ((e k).trace AtomChipHQ.inc).val,
      ((e k).trace AtomChipHQ.cout).val, ((e k).trace AtomChipHQ.idxO).val, ((e k).trace AtomChipHQ.lO).val,
      ((e k).trace AtomChipHQ.kRO).val, ((e k).trace AtomChipHQ.vRO).val⟩ := by
  simp [valReader, k.2]

/-- **L5 `hRA`** at the canonical reader: every row reads (a `ZMod.val` casts back). -/
theorem hRA_valReader {n : ℕ} (e : Fin n → Env (ZMod p)) : ∀ k : Fin n, Reads (e k) (valReader e k) := by
  intro k
  rw [valReader_lt]
  exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- **L5 `hrn`** at the canonical reader: no inc past the table. -/
theorem hrn_valReader {n : ℕ} (e : Fin n → Env (ZMod p)) : ∀ k, n ≤ k → (valReader e k).inc = 0 := by
  intro k hk
  simp [valReader, show ¬ k < n by omega]

/-- The padding rows are unweighted (the `hout` of `hext_of_rows`, the `hTout` of `atomLeaves_extB_of_mb`). -/
theorem wR_valReader_out {n : ℕ} (e : Fin n → Env (ZMod p)) : ∀ k, n ≤ k → (valReader e k).wR = 0 := by
  intro k hk
  simp [valReader, show ¬ k < n by omega]

theorem aR_valReader_out {n : ℕ} (e : Fin n → Env (ZMod p)) : ∀ k, n ≤ k → (valReader e k).wR = 0 →
    (valReader e k).aR ≠ 0 := by
  intro k hk _
  simp [valReader, show ¬ k < n by omega]

/-- **L5 `hwRA`** at the canonical reader, from the cell base gate `wR·(wR − 1)` at every row. -/
theorem hwRA_valReader {n : ℕ} (e : Fin n → Env (ZMod p))
    (hbool : ∀ k : Fin n, (e k).trace Cell.wR * ((e k).trace Cell.wR - 1) = 0) :
    ∀ j, (valReader e j).wR ≤ 1 := by
  intro j
  by_cases hj : j < n
  · have h := valReader_lt e ⟨j, hj⟩
    simp only at h
    rw [h]
    rcases mul_eq_zero.mp (hbool ⟨j, hj⟩) with h0 | h1
    · simp [h0]
    · rw [sub_eq_zero.mp h1, ZMod.val_one]
  · simp [valReader, hj]

/-- `wR·(wR − 1)` at every atom-table row, from the accepted chip's cell base gates. -/
theorem atom_wR_bool {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K] [Fintype K]
    {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K} {hA nA : ℕ}
    {hnA : 0 < nA} {nodesA : Fin nA → ZMod p} {orbitA : StrictOrbitDomain (ZMod p) 3 hA} {chalsA pubsA : ℕ → K}
    {QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X]}
    (hsat : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA) (k : Fin nA) :
    (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k).trace Cell.wR *
      ((AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k).trace Cell.wR - 1) = 0 := by
  have hg := AtomServedQ.atom_base δ b hnA nodesA orbitA chalsA pubsA QA hsat k
  have g := hg (boolE (cv Cell.wR)) (List.mem_append_left _ (by simp [Cell.baseGates]))
  simpa [CoeffExpr.eval, cv, boolE] using g

end Reader

end

end Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8
