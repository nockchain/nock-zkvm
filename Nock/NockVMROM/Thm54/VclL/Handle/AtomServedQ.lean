/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomServedQ.lean

  * `atom_qgates`, `atom_base`, `atom_masks` — the gate / mask facts at every row;
  * `atom_inv` — an inverse gate `inv · den = 1`;
  * `atom_tele` — the generic init / step / terminal telescope over a `(m, inv, acc, pub)` quadruple;
  * `atomProvs_sum` (`Σ mh · invHQ = (pub₄, pub₅)`), `atomCReqs_sum` (`Σ_{inc = 1} den(oldKey)⁻¹ =
    (pub₁₀, pub₁₁)`, using the `inc` booleanity of g7.0);
  * **`atom_consume_served`** — outside the weighted IO failure event of summand #4 (at the `𝕂′` coins
    `(γH′, ρH′)`, lifted records), under the verifier's balance `(pub₄, pub₅) = (pub₁₀, pub₁₁) + Σ_wreqs`
    and the consumer count `< p`: every consumed key (inc rows and the walk) is a provided key;
  * **`consumeServedQ_of_balance`** — A-2's named hypothesis `ConsumeServedQ` discharged.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ
import Nock.NockVMROM.Thm54.VclL.Handle.TeleHQ
import Nock.NockVMROM.Thm54.VclL.Handle.TeleC

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ
open Module
open scoped Polynomial

noncomputable section

section Atom
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (atomChipHQ δF b hn nodes orbit chals pubs).rap.w → F[X])

local notation "𝕂′" => Quad (algebraMap F K δF)

/-- Row `i`'s base environment on the atom chip. -/
abbrev aEF {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env F :=
  Reify.envOfTrace Q' orbit.ω (nodes i) (slotVal b 205 chals) (slotVal b 205 pubs)

/-- Row `i`'s gathered `𝕂` environment on the atom chip. -/
abbrev aEK {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) : Env K :=
  gatherEnv b ((atomTemplateHQ δF).col0 3) (aEF b nodes orbit chals pubs Q' i)

/-- The `𝕂′` gates of the atom chip (the cell twin's export gates and the added ones). -/
def qList : List (QE F) := CellHQ.gatesQ δF ++ atomQ δF

theorem atom_qgates (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ e ∈ qList δF, e.ev δF (aEK δF b nodes orbit chals pubs Q i) (aEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (atomTemplateHQ δF) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  intro e he
  refine ev_eq_zero_of_gates δF _ _ e fun g hg => hl.2.2.2 g ?_
  show g ∈ Cell.mixedGates δF ++ CellHQ.gates δF ++ atomMixed δF
  rcases List.mem_append.mp he with he | he
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩))
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hg⟩)

theorem atom_base (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    ∀ g ∈ Cell.baseGates ++ atomGates, g.eval (aEF b nodes orbit chals pubs Q i) = 0 := by
  have hl := (expandChip_satisfies_iff_language (atomTemplateHQ δF) b _ _ orbit _ Q).mp hsat (nodes i)
    (mem_rowNodeSet nodes i)
  exact hl.1

theorem atom_masks (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (aEF b nodes orbit chals pubs Q i).trace Cell.isF = (if (i : ℕ) = 0 then 1 else 0) ∧
      (aEF b nodes orbit chals pubs Q i).trace Cell.isL = (if (i : ℕ) = n - 1 then 1 else 0) := by
  have hw : (atomChipHQ δF b hn nodes orbit chals pubs).rap.w = 349 :=
    atomChipHQ_width δF b hn nodes orbit chals pubs
  have h0 : Q ⟨0, by rw [hw]; omega⟩ = firstRowMask nodes := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 : Q ⟨1, by rw [hw]; omega⟩ = lastRowMask hn nodes := hbind ⟨1, by show 1 < 2; omega⟩
  exact masks_of hn nodes orbit Q _ _ h0 h1 hinj _ _ i

theorem aEK_pub (i : Fin n) (idx : ℕ) : (aEK δF b nodes orbit chals pubs Q i).pub idx = pubs idx :=
  gather_pub_T b (atomTemplateHQ δF) 205 (atomTemplateHQ_baseCols δF) _ pubs rfl idx

theorem aEK_chal (i : Fin n) (idx : ℕ) : (aEK δF b nodes orbit chals pubs Q i).chal idx = chals idx :=
  gather_chal_T b (atomTemplateHQ δF) 205 (atomTemplateHQ_baseCols δF) _ chals rfl idx

theorem aEF_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (aEF b nodes orbit chals pubs Q i).traceNext j = (aEF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem aEK_next (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (aEK δF b nodes orbit chals pubs Q i).traceNext r = (aEK δF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace r :=
  gather_next_T b _ _ _ (aEF_next δF b hn nodes orbit chals pubs Q hadj i hi) r

/-- A `𝕂′` role pair read at row `i`. -/
abbrev rq {w : ℕ} (Q' : Fin w → F[X]) (r : ℕ) (i : Fin n) : 𝕂′ :=
  Quad.mk _ ((aEK δF b nodes orbit chals pubs Q' i).trace r) ((aEK δF b nodes orbit chals pubs Q' i).trace (r + 1))

/-- The `𝕂′` denominator of key `l` at row `i`. -/
abbrev aDen {w : ℕ} (Q' : Fin w → F[X]) (l : List (CoeffExpr F)) (i : Fin n) : 𝕂′ :=
  (HQ.denKeyQ δF l).ev δF (aEK δF b nodes orbit chals pubs Q' i) (aEF b nodes orbit chals pubs Q' i)

/-- **An inverse gate**: `inv · den = 1`. -/
theorem atom_inv (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) (inv : ℕ)
    (l : List (CoeffExpr F)) (hg : QE.sub (QE.mul δF (QE.var inv) (HQ.denKeyQ δF l)) QE.one ∈ qList δF)
    (i : Fin n) :
    aDen δF b nodes orbit chals pubs Q l i ≠ 0 ∧
      rq δF b nodes orbit chals pubs Q inv i = (aDen δF b nodes orbit chals pubs Q l i)⁻¹ := by
  have g := atom_qgates δF b hn nodes orbit chals pubs Q hsat i _ hg
  rw [ev_sub, ev_mul, ev_var, ev_one, sub_eq_zero] at g
  exact ⟨right_ne_zero_of_mul_eq_one g, eq_inv_of_mul_eq_one_left g⟩

/-- **The generic atom-chip `𝕂′` telescope** over a `(m, inv, acc, pub)` quadruple whose three
accumulator gates are in the chip. -/
theorem atom_tele (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (m inv acc pub : ℕ)
    (g0 : QE.scale (cv Cell.isF) (QE.sub (QE.var acc) (QE.scale (cv m) (QE.var inv))) ∈ qList δF)
    (gs : QE.scale (notE (cv Cell.isL)) (QE.sub (QE.sub (QE.next acc) (QE.var acc))
      (QE.scale (nv m) (QE.next inv))) ∈ qList δF)
    (gT : QE.scale (cv Cell.isL) (QE.sub (QE.var acc) (QE.pub pub)) ∈ qList δF) :
    ∑ i, liftQ δF ((aEF b nodes orbit chals pubs Q i).trace m) * rq δF b nodes orbit chals pubs Q inv i =
      Quad.mk _ (pubs pub) (pubs (pub + 1)) := by
  have hg := atom_qgates δF b hn nodes orbit chals pubs Q hsat
  refine TeleHQ.qTelescope δF hn (fun i => (aEF b nodes orbit chals pubs Q i).trace Cell.isF)
    (fun i => (aEF b nodes orbit chals pubs Q i).trace Cell.isL)
    (fun i => rq δF b nodes orbit chals pubs Q acc i) _ _
    (fun i => (atom_masks δF b hn nodes orbit chals pubs Q hbind hinj i).1)
    (fun i => (atom_masks δF b hn nodes orbit chals pubs Q hbind hinj i).2) ?_ ?_ ?_
  · intro i
    have g := hg i _ g0
    rw [ev_scale, ev_sub, ev_var, ev_scale, ev_var] at g
    simpa only [cv, CoeffExpr.eval] using g
  · intro i hi
    have g := hg i _ gs
    rw [ev_scale, ev_sub, ev_sub, ev_next, ev_var, ev_scale, ev_next] at g
    simp only [notE, cv, nv, CoeffExpr.eval, aEK_next δF b hn nodes orbit chals pubs Q hadj i hi,
      aEF_next δF b hn nodes orbit chals pubs Q hadj i hi] at g
    simpa only [rq, liftQ, map_sub, map_one] using g
  · intro i
    have g := hg i _ gT
    rw [ev_scale, ev_sub, ev_var, ev_pub, aEK_pub, aEK_pub] at g
    simpa only [cv, CoeffExpr.eval] using g

/-- The `𝕂′` coins at the memory leaves `33 / 35`, `34 / 36` (`(γH′, ρH′)` at VSQ). -/
abbrev acoins : IOCoins 𝕂′ := ⟨Quad.mk _ (chals 33) (chals 35), Quad.mk _ (chals 34) (chals 36)⟩

theorem aDen_eq (l : List (CoeffExpr F)) (hl : l.length = 5) (i : Fin n) :
    aDen δF b nodes orbit chals pubs Q l i =
      compress (acoins δF chals) (liftRec (K := K) (L := 𝕂′) (ServeH.keyVec5 l (aEF b nodes orbit chals pubs Q i))) := by
  rw [aDen, TeleHQ.denKeyQ_ev δF _ _ _ hl]
  simp only [TeleHQ.coinsQ, aEK_chal]

/-! ### The two sides of summand #4 -/

/-- **The atom table's export providers**: `(keyH, mh)` per row. -/
def atomProvs {w : ℕ} (Q' : Fin w → F[X]) : List ((Fin 5 → K) × K) :=
  (List.finRange n).map fun i =>
    (ServeH.keyVec5 CellH.keyH (aEF b nodes orbit chals pubs Q' i),
      algebraMap F K ((aEF b nodes orbit chals pubs Q' i).trace CellH.mh))

/-- **The atom table's consumed old-node keys**: `oldKey` on every inc row (`inc = 1`). -/
def atomCReqs [DecidableEq F] {w : ℕ} (Q' : Fin w → F[X]) : List (Fin 5 → K) :=
  (List.finRange n).flatMap fun i =>
    if (aEF b nodes orbit chals pubs Q' i).trace inc = 1 then
      [ServeH.keyVec5 oldKey (aEF b nodes orbit chals pubs Q' i)] else []

/-- The lifted weighted providers. -/
abbrev liftProvs (provs : List ((Fin 5 → K) × K)) : List ((Fin 5 → 𝕂′) × 𝕂′) :=
  provs.map fun q => (liftRec (K := K) (L := 𝕂′) q.1, algebraMap K 𝕂′ q.2)

theorem keyH_len : (CellH.keyH : List (CoeffExpr F)).length = 5 := by simp [CellH.keyH]
theorem oldKey_len : (oldKey : List (CoeffExpr F)).length = 5 := by simp [oldKey]

theorem gate_inv_keyH :
    QE.sub (QE.mul δF (QE.var CellHQ.invHQ) (HQ.denKeyQ δF CellH.keyH)) QE.one ∈ qList δF := by
  simp [qList, CellHQ.gatesQ]
theorem gate_inv_old : QE.sub (QE.mul δF (QE.var cInv) (HQ.denKeyQ δF oldKey)) QE.one ∈ qList δF := by
  simp [qList, atomQ]

/-- **The providers' weighted `𝕂′` sum is the terminal `(pub₄, pub₅)`.** -/
theorem atomProvs_sum (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ((liftProvs δF (atomProvs b nodes orbit chals pubs Q)).map fun q =>
        q.2 * (compress (acoins δF chals) q.1)⁻¹).sum =
      Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) := by
  rw [← atom_tele δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj CellH.mh CellHQ.invHQ
    CellHQ.accHQ CellHQ.pubHQ (by simp [qList, CellHQ.gatesQ]) (by simp [qList, CellHQ.gatesQ])
    (by simp [qList, CellHQ.gatesQ])]
  simp only [liftProvs, atomProvs, List.map_map, Function.comp_def]
  rw [sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(atom_inv δF b hn nodes orbit chals pubs Q hsat _ _ (gate_inv_keyH δF) i).2,
    aDen_eq δF b hn nodes orbit chals pubs Q _ keyH_len]

theorem atomProvs_den (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) :
    ∀ q ∈ liftProvs δF (atomProvs b nodes orbit chals pubs Q), compress (acoins δF chals) q.1 ≠ 0 := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq'
  rw [← aDen_eq δF b hn nodes orbit chals pubs Q _ keyH_len]
  exact (atom_inv δF b hn nodes orbit chals pubs Q hsat _ _ (gate_inv_keyH δF) i).1

/-- `inc` is boolean at every row (g7.0). -/
theorem inc_bool (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (aEF b nodes orbit chals pubs Q i).trace inc = 0 ∨ (aEF b nodes orbit chals pubs Q i).trace inc = 1 := by
  have g := atom_base δF b hn nodes orbit chals pubs Q hsat i (boolE (cv inc))
    (List.mem_append_right _ (by simp [atomGates, g70]))
  simp only [boolE, cv, CoeffExpr.eval] at g
  rcases mul_eq_zero.mp g with g | g
  · exact Or.inl g
  · exact Or.inr (sub_eq_zero.mp g)

/-- **The inc rows' consumed keys sum to the consume terminal `(pub₁₀, pub₁₁)`.** -/
theorem atomCReqs_sum [DecidableEq F] (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    (((atomCReqs b nodes orbit chals pubs Q).map (liftRec (K := K) (L := 𝕂′))).map fun r =>
        (compress (acoins δF chals) r)⁻¹).sum = Quad.mk _ (pubs pubC) (pubs (pubC + 1)) := by
  rw [← atom_tele δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj inc cInv cAcc pubC
    (by simp [qList, atomQ]) (by simp [qList, atomQ]) (by simp [qList, atomQ])]
  rw [List.map_map, atomCReqs, map_flatMap_sum, sum_finRange]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := (atom_inv δF b hn nodes orbit chals pubs Q hsat _ _ (gate_inv_old δF) i).2
  rw [aDen_eq δF b hn nodes orbit chals pubs Q _ oldKey_len] at hi
  rcases inc_bool δF b hn nodes orbit chals pubs Q hsat i with h0 | h1
  · rw [if_neg (by rw [h0]; exact zero_ne_one), h0]; simp [liftQ]
  · rw [if_pos h1, h1, hi]; simp [liftQ]

/-! ### Summand #4 outside its event ⇒ every consumed key is provided -/

variable [DecidableEq F] [DecidableEq K] [DecidableEq (Quad (algebraMap F K δF))]

/-- **`atom_consume_served`** (summand #4).  Outside
the weighted IO failure event of the lifted records at `(γH′, ρH′)` and under the consumer count
`< p`: every consumed key is a provided key. -/
theorem atom_consume_served {p : ℕ} [CharP 𝕂′ p]
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (wreqs : List (Fin 5 → K))
    (hbal : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubs pubC) (pubs (pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (acoins δF chals) r)⁻¹).sum)
    (hout : ((acoins δF chals).gamma, (acoins δF chals).pole) ∉
      IOFailureEventW ((atomCReqs b nodes orbit chals pubs Q ++ wreqs).map (liftRec (K := K) (L := 𝕂′)))
        (liftProvs δF (atomProvs b nodes orbit chals pubs Q)))
    (hcount : (atomCReqs b nodes orbit chals pubs Q ++ wreqs).length < p) :
    ∀ r ∈ atomCReqs b nodes orbit chals pubs Q ++ wreqs, r ∈ (atomProvs b nodes orbit chals pubs Q).map Prod.fst := by
  have hd := TeleC.den_ne_of_out _ _ _ _ hout
  have hs := ServeH.served_of_balance (p := p) _ _ _ _ hd
    (atomProvs_den δF b hn nodes orbit chals pubs Q hsat) ?_ (by rw [List.length_map]; exact hcount) hout
  · intro r hr
    obtain ⟨q, hq, hqr⟩ := List.mem_map.mp (hs _ (List.mem_map_of_mem hr))
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact List.mem_map.mpr ⟨q', hq', liftRec_inj hqr⟩
  · rw [List.map_append, List.map_append, List.sum_append,
      atomCReqs_sum δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj,
      atomProvs_sum δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj, hbal]

/-- The atom table's row environments, indexed by `ℕ` (rows `≥ n` read row `0`). -/
def atomEnvN {w : ℕ} (Q' : Fin w → F[X]) (k : ℕ) : Env F :=
  if hk : k < n then aEF b nodes orbit chals pubs Q' ⟨k, hk⟩ else aEF b nodes orbit chals pubs Q' ⟨0, hn⟩

theorem atomEnvN_lt {w : ℕ} (Q' : Fin w → F[X]) (i : Fin n) :
    atomEnvN b hn nodes orbit chals pubs Q' i = aEF b nodes orbit chals pubs Q' i := by
  simp [atomEnvN, i.isLt]

/-- Two lifted keys of length `5` that agree as vectors agree entrywise in `F`. -/
theorem map_eval_eq_of_keyVec5 {l l' : List (CoeffExpr F)} (hl : l.length = 5) (hl' : l'.length = 5)
    {e e' : Env F} (h : (ServeH.keyVec5 l e : Fin 5 → K) = ServeH.keyVec5 l' e') :
    l.map (fun g => g.eval e) = l'.map (fun g => g.eval e') := by
  apply List.ext_getElem (by simp [hl, hl'])
  intro c hc hc'
  rw [List.length_map, hl] at hc
  have := congrFun h ⟨c, hc⟩
  simp only [ServeH.keyVec5] at this
  have e1 := (algebraMap F K).injective this
  simp only [List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e1
  exact e1

/-- **`consumeServedQ_of_balance`** — A-2's named hypothesis `ConsumeServedQ` (every inc row's
consumed old key equals some row's provided `keyH`), from summand #4 outside its event. -/
theorem consumeServedQ_of_balance {p : ℕ} [CharP 𝕂′ p]
    (hsat : (atomChipHQ δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (atomChipHQ δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (wreqs : List (Fin 5 → K))
    (hbal : Quad.mk _ (pubs CellHQ.pubHQ) (pubs (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubs pubC) (pubs (pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (acoins δF chals) r)⁻¹).sum)
    (hout : ((acoins δF chals).gamma, (acoins δF chals).pole) ∉
      IOFailureEventW ((atomCReqs b nodes orbit chals pubs Q ++ wreqs).map (liftRec (K := K) (L := 𝕂′)))
        (liftProvs δF (atomProvs b nodes orbit chals pubs Q)))
    (hcount : (atomCReqs b nodes orbit chals pubs Q ++ wreqs).length < p) :
    ConsumeServedQ (atomEnvN b hn nodes orbit chals pubs Q) n := by
  have hs := atom_consume_served δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj wreqs hbal hout hcount
  intro i hi hinc
  rw [atomEnvN_lt b hn nodes orbit chals pubs Q ⟨i, hi⟩] at hinc ⊢
  have hmem : ServeH.keyVec5 oldKey (aEF b nodes orbit chals pubs Q ⟨i, hi⟩) ∈
      atomCReqs b nodes orbit chals pubs Q ++ wreqs := by
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨⟨i, hi⟩, List.mem_finRange _, ?_⟩)
    rw [if_pos hinc]; exact List.mem_singleton_self _
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp (hs _ hmem)
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq
  refine ⟨j, j.isLt, ?_⟩
  rw [atomEnvN_lt b hn nodes orbit chals pubs Q j]
  exact map_eval_eq_of_keyVec5 keyH_len oldKey_len hqe

end Atom

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ
