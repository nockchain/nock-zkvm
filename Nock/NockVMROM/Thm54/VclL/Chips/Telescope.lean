/-
  Nock/NockVMROM/Thm54/VclL/Chips/Telescope.lean

  **The cell table's validity accumulator
  telescope ⇒ weighted IO facts ⇒ `ValidityServed`.**

  * `den_ev_compress` — the `𝕂′`-key ↔ `FiniteIO.compress` lemma: the chip's denominator
    `ρ′ + RLC′(es)` at a row is `compress ⟨γ′, ρ′⟩ (keyVec es)` when the challenge leaves
    `5 / 7` carry `ρ′` and the leaves `11 + 2i / 12 + 2i` carry the coordinates of `γ′^i`
    (`ChalsOK`; the γ′-power slots `11 … 30` collide with no coin leaf `2 … 7`).
  * `telescope` (abstract) and the validity accumulator at an accepted cell trace
    (`cell_validity_sum`): `Σ_i mvᵢ·den(vKeyPᵢ)⁻¹ = ρ_V + Σ_{weighted children} den(childKey)⁻¹`,
    from the init / step / terminal gates, the masks, row adjacency and the three inverse gates
    (incl.
  * `cellValidityFacts` — the frame's weighted `IOFacts` at `m = 5` (providers `(vKeyP, mv)`,
    internal = the weighted child keys `cellValidityInternal`).
  * `cell_validityServed` — `ValidityServed (cellTableOf …)` from `finiteIO_lookup_sound_weighted`
    over `reqs ++ internal`, given the compute side's root-binding requests summing to `ρ_V`, the
    weighted IO exclusion and the consumer count `< p` (exactly `MF.response_sound`'s hypotheses).
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ChipV
import Nock.NockVMROM.Thm54.P8Core.SVFrame.WeightedIO

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The abstract telescope -/

theorem telescope_le {L : Type*} [AddCommMonoid L] (n : ℕ) (acc term : ℕ → L)
    (h0 : acc 0 = term 0) (hs : ∀ i, i + 1 < n → acc (i + 1) = acc i + term (i + 1)) :
    ∀ k, k < n → acc k = ∑ i ∈ Finset.range (k + 1), term i := by
  intro k
  induction k with
  | zero => intro _; simp [h0]
  | succ k ih =>
    intro hk
    rw [hs k hk, ih (by omega), Finset.sum_range_succ _ (k + 1)]

/-- **The telescope**: init `acc 0 = term 0`, step, terminal `acc (n−1) = ρ` give `Σ term = ρ`. -/
theorem telescope {L : Type*} [AddCommMonoid L] (n : ℕ) (hn : 0 < n) (acc term : ℕ → L) (ρ : L)
    (h0 : acc 0 = term 0) (hs : ∀ i, i + 1 < n → acc (i + 1) = acc i + term (i + 1))
    (hT : acc (n - 1) = ρ) : ∑ i ∈ Finset.range n, term i = ρ := by
  rw [← hT, telescope_le n acc term h0 hs (n - 1) (by omega), Nat.sub_add_cancel hn]

/-! ## 2. Keys as vectors; the denominator is `compress` -/

section Key
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]

/-- The `𝕂′` record a key expression list denotes (entries past the list read `0`). -/
def keyVec (m : ℕ) (es : List (QE F)) (eK : Env K) (eF : Env F) : Fin m → Quad (algebraMap F K δF) :=
  fun c => (es.getD c QE.zero).ev δF eK eF

theorem zipIdx_sum (f : ℕ → Quad (algebraMap F K δF)) (g : QE F → Quad (algebraMap F K δF)) :
    ∀ (es : List (QE F)) (k : ℕ),
      ((es.zipIdx k).map fun ei => f ei.2 * g ei.1).sum =
        ∑ c : Fin es.length, f (k + c) * g (es.getD c QE.zero)
  | [], _ => by simp
  | a :: t, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_sum f g t (k + 1)]
    show _ = ∑ c : Fin (t.length + 1), f (k + c) * g ((a :: t).getD c QE.zero)
    rw [Fin.sum_univ_succ]
    simp only [List.length_cons, Fin.val_zero, add_zero, List.getD_cons_zero, Fin.val_succ,
      List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show k + 1 + (c : ℕ) = k + ((c : ℕ) + 1) by omega]

/-- **What the chip's challenge vector must carry** for its denominators to be the frame's
`compress` at `⟨γ′, ρ′⟩`: `ρ′` at leaves `5 / 7`, the coordinates of `γ′^i` at `11 + 2i / 12 + 2i`. -/
def ChalsOK (chals : ℕ → K) (γ ρ : Quad (algebraMap F K δF)) (m : ℕ) : Prop :=
  Quad.mk _ (chals 5) (chals 7) = ρ ∧
    ∀ i < m, Quad.mk _ (chals (11 + 2 * i)) (chals (12 + 2 * i)) = γ ^ i

/-- **The `𝕂′`-key ↔ `FiniteIO.compress` lemma.** -/
theorem den_ev_compress (es : List (QE F)) (eK : Env K) (eF : Env F)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF eK.chal γ ρ es.length) :
    (den δF es).ev δF eK eF =
      FiniteIO.compress (m := es.length) ⟨γ, ρ⟩ (keyVec δF es.length es eK eF) := by
  rw [ev_den, ev_rlc, zipIdx_sum δF (fun i => (QE.gpow i : QE F).ev δF eK eF)
    (fun e => e.ev δF eK eF) es 0]
  simp only [FiniteIO.compress, Walk.rlc, keyVec, rQ, ev_chal, ev_gpow, zero_add]
  rw [hok.1]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hok.2 c c.isLt]

/-- **The VCL-L challenge vector** of the memory chips at frame coins `χ` (`frameVCL`, 11 coins):
leaf `j < 11` is the coin `χ j` (so `z′ = (χ₂, χ₃)`, `ρ′ = (χ₅, χ₇)`), leaves `11 + 2i / 12 + 2i`
are the coordinates of `γ′^i`, `γ′ = χ₄ + χ₆√δ` (`ioSpecVCLQuad`). -/
def chalsVCL [Fintype K] (χ : Fin 11 → K) (j : ℕ) : K :=
  if h : j < 11 then χ ⟨j, h⟩
  else if (j - 11) % 2 = 0 then Quad.re _ (Quad.mk (algebraMap F K δF) (χ 4) (χ 6) ^ ((j - 11) / 2))
  else Quad.im _ (Quad.mk (algebraMap F K δF) (χ 4) (χ 6) ^ ((j - 12) / 2))

theorem chalsVCL_ok [Fintype K] (χ : Fin 11 → K) (m : ℕ) :
    ChalsOK δF (chalsVCL δF χ) (Quad.mk _ (χ 4) (χ 6)) (Quad.mk _ (χ 5) (χ 7)) m := by
  refine ⟨by simp [chalsVCL], fun i _ => ?_⟩
  have h1 : ¬ 11 + 2 * i < 11 := by omega
  have h2 : ¬ 12 + 2 * i < 11 := by omega
  have h3 : (11 + 2 * i - 11) % 2 = 0 := by omega
  have h4 : ¬ (12 + 2 * i - 11) % 2 = 0 := by omega
  have h5 : (11 + 2 * i - 11) / 2 = i := by omega
  have h6 : (12 + 2 * i - 12) / 2 = i := by omega
  simp only [chalsVCL, dif_neg h1, dif_neg h2, if_pos h3, if_neg h4, h5, h6]
  exact Quad.mk_re_im _ _

/-- The γ′-power leaves `11 … 32` (`i < 11`) collide with no coin leaf of the gates (`2, 3, 5, 7`). -/
theorem gpow_slots_disjoint :
    ∀ i < 11, 11 + 2 * i ∉ ({2, 3, 5, 7} : Finset ℕ) ∧ 12 + 2 * i ∉ ({2, 3, 5, 7} : Finset ℕ) := by
  decide

end Key

/-! ## 3. The cell table's validity accumulator -/

section CellAcc
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)
  (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])

/-- A base column at row `i`. -/
abbrev cellB (j : ℕ) (i : Fin n) : F := (cellEnvF b nodes orbit chals pubs Q i).trace j
/-- A `𝕂′` column at row `i`. -/
abbrev cellQ (r : ℕ) (i : Fin n) : Quad (algebraMap F K δF) :=
  (QE.var r : QE F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i)
/-- A denominator at row `i`. -/
abbrev cellDen (es : List (QE F)) (i : Fin n) : Quad (algebraMap F K δF) :=
  (den δF es).ev δF (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i)
/-- A key vector at row `i`. -/
abbrev cellKey (m : ℕ) (es : List (QE F)) (i : Fin n) : Fin m → Quad (algebraMap F K δF) :=
  keyVec δF m es (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i)

theorem cell_w : (cellChip δF b hn nodes orbit chals pubs).rap.w = 225 :=
  (cellChip_fingerprint δF b hn nodes orbit chals pubs).1

/-- Row `i`'s gates in the row environments. -/
theorem cell_gates (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (∀ g ∈ Cell.baseGates (F := F), g.eval (cellEnvF b nodes orbit chals pubs Q i) = 0) ∧
      (∀ e ∈ Cell.qEqs δF, e.ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
        (cellEnvF b nodes orbit chals pubs Q i) = 0) := by
  have hl := cellChip_rowLocal δF b hn nodes orbit chals pubs Q hsat i
  exact ⟨hl.1, fun e he => ev_eq_zero_of_gates δF _ _ e fun g hg =>
    hl.2 g (List.mem_flatMap.mpr ⟨e, he, hg⟩)⟩

theorem cell_isF (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    cellB δF b hn nodes orbit chals pubs Q Cell.isF i = if (i : ℕ) = 0 then 1 else 0 := by
  show (Reify.envOfTrace Q orbit.ω (nodes i) _ _).trace 0 = _
  rw [envOfTrace_trace Q _ _ _ _ (show 0 < _ by rw [cell_w]; omega)]
  exact (cellChip_masks δF b hn nodes orbit chals pubs Q hbind hinj i).1

theorem cell_isL (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    cellB δF b hn nodes orbit chals pubs Q Cell.isL i =
      if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0 := by
  show (Reify.envOfTrace Q orbit.ω (nodes i) _ _).trace 1 = _
  rw [envOfTrace_trace Q _ _ _ _ (show 1 < _ by rw [cell_w]; omega)]
  exact (cellChip_masks δF b hn nodes orbit chals pubs Q hbind hinj i).2

theorem cell_traceNext
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (cellEnvF b nodes orbit chals pubs Q i).traceNext j =
      (cellEnvF b nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  traceNext_eq nodes orbit Q _ _ hadj i hi j

theorem cell_ev_next
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (r : ℕ) :
    (QE.next r : QE F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
        (cellEnvF b nodes orbit chals pubs Q i) =
      cellQ δF b hn nodes orbit chals pubs Q r ⟨(i : ℕ) + 1, hi⟩ := by
  simp only [ev_next, ev_var, cellQ, cellEnvK, gatherEnv, ChipTemplate.col0,
    cell_traceNext δF b hn nodes orbit chals pubs Q hadj i hi]

/-- The validity row term `mv·inv_v − inv_L − inv_R`. -/
abbrev vT (i : Fin n) : Quad (algebraMap F K δF) :=
  liftQ δF (cellB δF b hn nodes orbit chals pubs Q Cell.mv i) * cellQ δF b hn nodes orbit chals pubs Q Cell.vProvInv i
    - cellQ δF b hn nodes orbit chals pubs Q Cell.consLInv i
    - cellQ δF b hn nodes orbit chals pubs Q Cell.consRInv i

theorem vTerm_cur (i : Fin n) :
    (Cell.vTerm true : QE F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
      (cellEnvF b nodes orbit chals pubs Q i) = vT δF b hn nodes orbit chals pubs Q i := by
  simp only [Cell.vTerm, if_true, ev_sub, ev_scale, CoeffExpr.eval, cv]

theorem vTerm_next
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (Cell.vTerm false : QE F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
      (cellEnvF b nodes orbit chals pubs Q i) = vT δF b hn nodes orbit chals pubs Q ⟨(i : ℕ) + 1, hi⟩ := by
  simp only [Cell.vTerm, Bool.false_eq_true, if_false, ev_sub, ev_scale, CoeffExpr.eval, nv,
    cell_ev_next δF b hn nodes orbit chals pubs Q hadj i hi,
    cell_traceNext δF b hn nodes orbit chals pubs Q hadj i hi]

theorem qeq_mem_v (k : ℕ) (e : QE F) (he : (Cell.qEqs δF).getD k QE.zero = e) (hk : k < (Cell.qEqs δF).length) :
    e ∈ Cell.qEqs δF := by
  rw [← he, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

/-- **The validity telescope** at an accepted cell trace: `Σ_i vTᵢ = ρ_V` (public slots `0 / 1`). -/
theorem cell_validity_telescope (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∑ i : Fin n, vT δF b hn nodes orbit chals pubs Q i = Quad.mk _ (pubs 0) (pubs 1) := by
  have hmem : ∀ e, e ∈ Cell.qEqs δF → ∀ i, e.ev δF (cellEnvK δF b nodes orbit chals pubs Q i)
      (cellEnvF b nodes orbit chals pubs Q i) = 0 := fun e he i =>
    (cell_gates δF b hn nodes orbit chals pubs Q hsat i).2 e he
  set acc : ℕ → Quad (algebraMap F K δF) := fun k =>
    if hk : k < n then cellQ δF b hn nodes orbit chals pubs Q Cell.vAcc ⟨k, hk⟩ else 0 with hacc
  set term : ℕ → Quad (algebraMap F K δF) := fun k =>
    if hk : k < n then vT δF b hn nodes orbit chals pubs Q ⟨k, hk⟩ else 0 with hterm
  have h0 : acc 0 = term 0 := by
    simp only [hacc, hterm, dif_pos hn]
    have g := hmem (QE.scale (cv Cell.isF)
      (QE.sub (QE.var Cell.vAcc) (Cell.vTerm true))) (by simp [Cell.qEqs]) ⟨0, hn⟩
    rw [ev_scale, ev_sub, vTerm_cur] at g
    have hf : (CoeffExpr.eval (cv Cell.isF) (cellEnvF b nodes orbit chals pubs Q ⟨0, hn⟩) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]
      exact (cell_isF δF b hn nodes orbit chals pubs Q hbind hinj ⟨0, hn⟩).trans (if_pos rfl)
    rw [hf, liftQ, map_one, map_one, one_mul] at g
    exact sub_eq_zero.mp g
  have hs : ∀ i, i + 1 < n → acc (i + 1) = acc i + term (i + 1) := by
    intro i hi
    simp only [hacc, hterm, dif_pos hi, dif_pos (show i < n by omega)]
    have g := hmem (QE.scale (notE (cv Cell.isL))
      (QE.sub (QE.sub (QE.next Cell.vAcc) (QE.var Cell.vAcc)) (Cell.vTerm false))) (by simp [Cell.qEqs])
      ⟨i, by omega⟩
    rw [ev_scale, ev_sub, ev_sub, vTerm_next δF b hn nodes orbit chals pubs Q hadj ⟨i, by omega⟩ hi,
      cell_ev_next δF b hn nodes orbit chals pubs Q hadj ⟨i, by omega⟩ hi] at g
    have hl : (CoeffExpr.eval (notE (cv Cell.isL)) (cellEnvF b nodes orbit chals pubs Q ⟨i, by omega⟩) : F) = 1 := by
      simp only [CoeffExpr.eval, cv, notE]
      have hL := cell_isL δF b hn nodes orbit chals pubs Q hbind hinj ⟨i, by omega⟩
      simp only [cellB] at hL
      rw [hL, if_neg]
      · simp
      · intro h; have := congrArg Fin.val h; simp at this; omega
    rw [hl, liftQ, map_one, map_one, one_mul] at g
    linear_combination g
  have hT : acc (n - 1) = Quad.mk _ (pubs 0) (pubs 1) := by
    simp only [hacc, dif_pos (show n - 1 < n by omega)]
    have g := hmem (QE.scale (cv Cell.isL)
      (QE.sub (QE.var Cell.vAcc) (QE.pub 0))) (by simp [Cell.qEqs]) ⟨n - 1, by omega⟩
    rw [ev_scale, ev_sub, ev_pub] at g
    have hl : (CoeffExpr.eval (cv Cell.isL) (cellEnvF b nodes orbit chals pubs Q ⟨n - 1, by omega⟩) : F) = 1 := by
      simp only [CoeffExpr.eval, cv]
      exact (cell_isL δF b hn nodes orbit chals pubs Q hbind hinj ⟨n - 1, by omega⟩).trans (if_pos rfl)
    rw [hl, liftQ, map_one, map_one, one_mul,
      gather_pub_cell δF b pubs _ rfl, gather_pub_cell δF b pubs _ rfl] at g
    exact sub_eq_zero.mp g
  have := telescope n hn acc term _ h0 hs hT
  rw [Finset.sum_range] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hterm, dif_pos i.isLt]

/-! ## 4. The inverse gates -/

theorem den_ev_compress' (es : List (QE F)) {m : ℕ} (hlen : es.length = m) (eK : Env K) (eF : Env F)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF eK.chal γ ρ m) :
    (den δF es).ev δF eK eF = FiniteIO.compress (m := m) ⟨γ, ρ⟩ (keyVec δF m es eK eF) := by
  subst hlen; exact den_ev_compress δF es eK eF γ ρ hok

theorem chalsOK_mono {chals : ℕ → K} {γ ρ : Quad (algebraMap F K δF)} {m m' : ℕ} (hm : m ≤ m')
    (h : ChalsOK δF chals γ ρ m') : ChalsOK δF chals γ ρ m :=
  ⟨h.1, fun i hi => h.2 i (by omega)⟩

theorem cell_chal (i : Fin n) : (cellEnvK δF b nodes orbit chals pubs Q i).chal = chals :=
  funext fun j => gather_chal_cell δF b chals _ rfl j

/-- A provider inverse gate `inv·den − 1 = 0`: `den ≠ 0`, `inv = den⁻¹`. -/
theorem prov_inv {inv d : Quad (algebraMap F K δF)} (h : inv * d - 1 = 0) : d ≠ 0 ∧ inv = d⁻¹ := by
  have h1 : inv * d = 1 := sub_eq_zero.mp h
  have hd : d ≠ 0 := by rintro rfl; simp at h1
  exact ⟨hd, eq_inv_of_mul_eq_one_left h1⟩

/-- A consumer inverse gate `inv·den − w = 0` with the zero-weight gate `(1 − w)·inv = 0` and
`w ∈ {0, 1}`: `inv = [w = 1]·den⁻¹`, and `den ≠ 0` when `w = 1`. -/
theorem cons_inv {inv d : Quad (algebraMap F K δF)} {w : F} (hw : w = 0 ∨ w = 1)
    (h : inv * d - liftQ δF w = 0) (h0 : liftQ δF (1 - w) * inv = 0) :
    (w = 1 → d ≠ 0) ∧ inv = if w = 1 then d⁻¹ else 0 := by
  rcases hw with rfl | rfl
  · have : inv = 0 := by simpa [liftQ] using h0
    simp [this]
  · have h1 : inv * d = 1 := by simpa [liftQ] using sub_eq_zero.mp h
    have hd : d ≠ 0 := by rintro rfl; simp at h1
    exact ⟨fun _ => hd, by rw [if_pos rfl]; exact eq_inv_of_mul_eq_one_left h1⟩

theorem cell_bool (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n)
    (j : ℕ) (hj : (boolE (cv j) : CoeffExpr F) ∈ Cell.baseGates) :
    cellB δF b hn nodes orbit chals pubs Q j i = 0 ∨ cellB δF b hn nodes orbit chals pubs Q j i = 1 :=
  bool_val (by simpa [CoeffExpr.eval, cv, boolE] using
    (cell_gates δF b hn nodes orbit chals pubs Q hsat i).1 _ hj)

/-- The inverse facts of row `i`: provider `vKeyP` and the two weighted children. -/
theorem cell_inv_facts (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (cellDen δF b hn nodes orbit chals pubs Q Cell.vKeyP i ≠ 0 ∧
      cellQ δF b hn nodes orbit chals pubs Q Cell.vProvInv i = (cellDen δF b hn nodes orbit chals pubs Q Cell.vKeyP i)⁻¹) ∧
    ((cellB δF b hn nodes orbit chals pubs Q Cell.wL i = 1 → cellDen δF b hn nodes orbit chals pubs Q Cell.vKeyL i ≠ 0) ∧
      cellQ δF b hn nodes orbit chals pubs Q Cell.consLInv i =
        if cellB δF b hn nodes orbit chals pubs Q Cell.wL i = 1 then (cellDen δF b hn nodes orbit chals pubs Q Cell.vKeyL i)⁻¹ else 0) ∧
    ((cellB δF b hn nodes orbit chals pubs Q Cell.wR i = 1 → cellDen δF b hn nodes orbit chals pubs Q Cell.vKeyR i ≠ 0) ∧
      cellQ δF b hn nodes orbit chals pubs Q Cell.consRInv i =
        if cellB δF b hn nodes orbit chals pubs Q Cell.wR i = 1 then (cellDen δF b hn nodes orbit chals pubs Q Cell.vKeyR i)⁻¹ else 0) := by
  have hm := (cell_gates δF b hn nodes orbit chals pubs Q hsat i).2
  have gP := hm (QE.sub (QE.mul δF (QE.var Cell.vProvInv) (den δF Cell.vKeyP)) QE.one) (by simp [Cell.qEqs])
  have gL := hm (QE.sub (QE.mul δF (QE.var Cell.consLInv) (den δF Cell.vKeyL)) (QE.base (cv Cell.wL)))
    (by simp [Cell.qEqs])
  have gR := hm (QE.sub (QE.mul δF (QE.var Cell.consRInv) (den δF Cell.vKeyR)) (QE.base (cv Cell.wR)))
    (by simp [Cell.qEqs])
  have zL := hm (QE.scale (notE (cv Cell.wL)) (QE.var Cell.consLInv)) (by simp [Cell.qEqs])
  have zR := hm (QE.scale (notE (cv Cell.wR)) (QE.var Cell.consRInv)) (by simp [Cell.qEqs])
  rw [ev_sub, ev_mul, ev_one] at gP
  rw [ev_sub, ev_mul, ev_base] at gL gR
  rw [ev_scale] at zL zR
  simp only [CoeffExpr.eval, cv, notE] at gL gR zL zR
  exact ⟨prov_inv δF gP,
    cons_inv δF (cell_bool δF b hn nodes orbit chals pubs Q hsat i Cell.wL (by simp [Cell.baseGates])) gL zL,
    cons_inv δF (cell_bool δF b hn nodes orbit chals pubs Q hsat i Cell.wR (by simp [Cell.baseGates])) gR zR⟩

/-! ## 5. The weighted validity IO facts -/

/-- The validity providers: one `(vKeyP, mv)` per row. -/
def cellVRecords : List ((Fin 5 → Quad (algebraMap F K δF)) × F) :=
  (List.finRange n).map fun i =>
    (cellKey δF b hn nodes orbit chals pubs Q 5 Cell.vKeyP i, cellB δF b hn nodes orbit chals pubs Q Cell.mv i)

/-- The validity accumulator's internal consumers: each weighted child's key. -/
def cellVInternal : List (Fin 5 → Quad (algebraMap F K δF)) :=
  (List.finRange n).flatMap fun i =>
    (if cellB δF b hn nodes orbit chals pubs Q Cell.wL i = 1 then [cellKey δF b hn nodes orbit chals pubs Q 5 Cell.vKeyL i] else []) ++
    (if cellB δF b hn nodes orbit chals pubs Q Cell.wR i = 1 then [cellKey δF b hn nodes orbit chals pubs Q 5 Cell.vKeyR i] else [])

variable {δF b hn nodes orbit chals pubs Q} in
theorem cell_compress (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    (es : List (QE F)) {m : ℕ} (hlen : es.length = m) (hm : m ≤ 11) (i : Fin n) :
    FiniteIO.compress (m := m) ⟨γ, ρ⟩ (cellKey δF b hn nodes orbit chals pubs Q m es i) =
      cellDen δF b hn nodes orbit chals pubs Q es i := by
  rw [cellDen, den_ev_compress' δF es hlen _ _ γ ρ]
  rw [cell_chal]; exact chalsOK_mono δF hm hok

theorem map_flatMap_sum {α β M : Type*} [AddCommMonoid M] (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih]

theorem sum_finRange {M : Type*} [AddCommMonoid M] (f : Fin n → M) :
    ((List.finRange n).map f).sum = ∑ i, f i := by
  rw [Fin.sum_univ_def]

/-- **The validity accumulator as weighted IO facts**: `Σ mv·den(vKeyP)⁻¹ = ρ_V + Σ_internal den⁻¹`. -/
theorem cell_validity_sum (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) :
    ((cellVRecords δF b hn nodes orbit chals pubs Q).map fun r =>
        algebraMap F (Quad (algebraMap F K δF)) r.2 * (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r.1)⁻¹).sum =
      Quad.mk _ (pubs 0) (pubs 1) +
        ((cellVInternal δF b hn nodes orbit chals pubs Q).map fun r =>
          (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum := by
  have hT := cell_validity_telescope δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj
  rw [← hT]
  simp only [cellVRecords, cellVInternal, List.map_map, map_flatMap_sum,
    Function.comp_def, sum_finRange]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨-, hP⟩, ⟨-, hL⟩, ⟨-, hR⟩⟩ := cell_inv_facts δF b hn nodes orbit chals pubs Q hsat i
  rw [cell_compress (m := 5) γ ρ hok Cell.vKeyP rfl (by norm_num)]
  simp only [vT, hP, hL, hR]
  split_ifs <;>
    simp [cell_compress (m := 5) γ ρ hok Cell.vKeyL rfl (by norm_num), cell_compress (m := 5) γ ρ hok Cell.vKeyR rfl (by norm_num),
      liftQ, IsScalarTower.algebraMap_apply F K (Quad (algebraMap F K δF))] <;> ring

/-- **The validity accumulator's weighted IO facts** (the frame's `IOFacts` at `m = 5`, IO coins
`⟨γ′, ρ′⟩`, terminal `ρ_V + Σ internal`). -/
def cellValidityFacts (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11) :
    SVFrame.IOFacts F (FiniteIO.compress (m := 5) ⟨γ, ρ⟩)
      (Quad.mk _ (pubs 0) (pubs 1) +
        ((cellVInternal δF b hn nodes orbit chals pubs Q).map fun r =>
          (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum) where
  records := cellVRecords δF b hn nodes orbit chals pubs Q
  sum_eq := cell_validity_sum δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj γ ρ hok
  ne_zero := by
    intro r hr
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
    rw [cell_compress (m := 5) γ ρ hok Cell.vKeyP rfl (by norm_num)]
    exact (cell_inv_facts δF b hn nodes orbit chals pubs Q hsat i).1.1

/-! ## 6. `ValidityServed` -/

theorem natOf_congr {x y : F} (h : x = y) : natOf x = natOf y := by rw [h]

/-- **Decoding a matched validity key**: a child key equal to a provider key names the provider
row's fingerprint, limbs and serial. -/
theorem vKey_decode (i j : Fin n) (lR loL hiL idL : ℕ)
    (hk : cellKey δF b hn nodes orbit chals pubs Q 5
        ((QFP.var lR).entries ++ [QE.mk2 (cv loL) (cv hiL), QE.base (cv idL)]) i =
      cellKey δF b hn nodes orbit chals pubs Q 5 Cell.vKeyP j) :
    (QFP.var lR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q i) (cellEnvF b nodes orbit chals pubs Q i) =
        (QFP.var Cell.pR : QFP F).ev δF (cellEnvK δF b nodes orbit chals pubs Q j) (cellEnvF b nodes orbit chals pubs Q j) ∧
      cellB δF b hn nodes orbit chals pubs Q hiL i = cellB δF b hn nodes orbit chals pubs Q Cell.hi j ∧
      cellB δF b hn nodes orbit chals pubs Q loL i = cellB δF b hn nodes orbit chals pubs Q Cell.lo j ∧
      cellB δF b hn nodes orbit chals pubs Q idL i = cellB δF b hn nodes orbit chals pubs Q Cell.idx j := by
  have e : ∀ c : Fin 5, _ := fun c => congrFun hk c
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  simp only [cellKey, keyVec, Cell.vKeyP, QFP.var, QFP.entries, List.cons_append, List.nil_append,
    Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4
  have e3' : (3 : Fin 5).val = 3 := rfl
  have e4' : (4 : Fin 5).val = 4 := rfl
  simp only [e3', e4', List.getD_cons_succ, List.getD_cons_zero] at e3 e4
  rw [ev_mk2, ev_mk2, Quad.mk_eq_mk_iff] at e3
  rw [ev_base, ev_base, liftQ, liftQ] at e4
  have e4'' := (algebraMap F K).injective ((algebraMap K (Quad (algebraMap F K δF))).injective e4)
  refine ⟨?_, (algebraMap F K).injective e3.2, (algebraMap F K).injective e3.1, e4''⟩
  simp only [QFP.ev, QFP.var, e0, e1, e2]

variable [Fintype K] [DecidableEq (Quad (algebraMap F K δF))]

/-- **`ValidityServed` on an accepted cell table** from the weighted lookup: the compute side's
validity requests `reqs` (root bindings) sum to the public `ρ_V`; outside the weighted IO event at
`reqs ++ internal` and with the consumer count below the characteristic, every weighted child's key is
a provided row key. -/
theorem cell_validityServed
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    {p : ℕ} [CharP (Quad (algebraMap F K δF)) p] (reqs : List (Fin 5 → Quad (algebraMap F K δF)))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum = Quad.mk _ (pubs 0) (pubs 1))
    (hne : ∀ r ∈ reqs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r ≠ 0)
    (hγ : γ ∉ FiniteIO.IORLCCollisionEvent (FiniteIO.recordsW (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q)
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs Q))))
    (hpole : ρ ∉ FiniteIO.IOLogDerivEventW (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q)
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs Q)) γ)
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q).length < p) :
    ValidityServed (cellTableOf δF b nodes orbit chals pubs Q) := by
  set M := cellValidityFacts δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj γ ρ hok with hM
  have hinne : ∀ r ∈ cellVInternal δF b hn nodes orbit chals pubs Q,
      FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r ≠ 0 := by
    intro r hr
    obtain ⟨i, -, hri⟩ := List.mem_flatMap.mp hr
    obtain ⟨-, ⟨hL, -⟩, ⟨hR, -⟩⟩ := cell_inv_facts δF b hn nodes orbit chals pubs Q hsat i
    rcases List.mem_append.mp hri with h | h
    · split_ifs at h with hw
      · rw [List.mem_singleton.mp h, cell_compress (m := 5) γ ρ hok Cell.vKeyL rfl (by norm_num)]
        exact hL hw
      · simp at h
    · split_ifs at h with hw
      · rw [List.mem_singleton.mp h, cell_compress (m := 5) γ ρ hok Cell.vKeyR rfl (by norm_num)]
        exact hR hw
      · simp at h
  have hlook := FiniteIO.finiteIO_lookup_sound_weighted (p := p)
    (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q) (SVFrame.liftWts M.records) ⟨γ, ρ⟩
    (by
      intro r hr
      rcases List.mem_append.mp hr with h | h
      · exact hne r h
      · exact hinne r h)
    (by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact M.ne_zero r hr)
    (by
      rw [List.map_append, List.sum_append, hsum]
      have := M.sum_eq
      simp only [SVFrame.liftWts, List.map_map, Function.comp_def]
      exact this.symm)
    hcount hγ hpole
  have hfind : ∀ r ∈ cellVInternal δF b hn nodes orbit chals pubs Q,
      ∃ j : Fin n, cellKey δF b hn nodes orbit chals pubs Q 5 Cell.vKeyP j = r := by
    intro r hr
    have := hlook r (List.mem_append_right _ hr)
    rw [SVFrame.liftWts_fst] at this
    obtain ⟨q, hq, hqr⟩ := List.mem_map.mp this
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq
    exact ⟨j, hqr⟩
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  have hmem : ∀ j : Fin n, cellRowOf δF (cellEnvK δF b nodes orbit chals pubs Q j) (cellEnvF b nodes orbit chals pubs Q j) ∈
      cellTableOf δF b nodes orbit chals pubs Q := fun j => List.mem_ofFn.mpr ⟨j, rfl⟩
  constructor
  · intro hw
    have hw1 : cellB δF b hn nodes orbit chals pubs Q Cell.wL i = 1 := by
      simpa [cellRowOf, cellB0Of] using hw
    obtain ⟨j, hj⟩ := hfind _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_append_left _ (by rw [if_pos hw1]; exact List.mem_singleton_self _)⟩)
    obtain ⟨hfp, hhi, hlo, hid⟩ := vKey_decode δF b hn nodes orbit chals pubs Q i j Cell.lR Cell.loL Cell.hiL Cell.idL hj.symm
    exact ⟨_, hmem j, hfp, natOf_congr hhi, natOf_congr hlo, natOf_congr hid⟩
  · intro hw
    have hw1 : cellB δF b hn nodes orbit chals pubs Q Cell.wR i = 1 := by
      simpa [cellRowOf, cellB0Of] using hw
    obtain ⟨j, hj⟩ := hfind _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_append_right _ (by rw [if_pos hw1]; exact List.mem_singleton_self _)⟩)
    obtain ⟨hfp, hhi, hlo, hid⟩ := vKey_decode δF b hn nodes orbit chals pubs Q i j Cell.rR Cell.loR Cell.hiR Cell.idR hj.symm
    exact ⟨_, hmem j, hfp, natOf_congr hhi, natOf_congr hlo, natOf_congr hid⟩

/-- **The accepted cell table** (`Table.TableAccepts`) with its validity lookup discharged by the
accumulator (`cell_validityServed`): no `ValidityServed` premise left. -/
theorem cellTable_accepts_of_lookup [Algebra (ZMod (ringChar F)) (Quad (algebraMap F K δF))]
    (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    (hz : Quad.mk (algebraMap F K δF) (chals 2) (chals 3) ≠ 0)
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hnp : n < ringChar F)
    (γ ρ : Quad (algebraMap F K δF)) (hok : ChalsOK δF chals γ ρ 11)
    {p : ℕ} [CharP (Quad (algebraMap F K δF)) p] (reqs : List (Fin 5 → Quad (algebraMap F K δF)))
    (hsum : (reqs.map fun r => (FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r)⁻¹).sum = Quad.mk _ (pubs 0) (pubs 1))
    (hne : ∀ r ∈ reqs, FiniteIO.compress (m := 5) ⟨γ, ρ⟩ r ≠ 0)
    (hγ : γ ∉ FiniteIO.IORLCCollisionEvent (FiniteIO.recordsW (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q)
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs Q))))
    (hpole : ρ ∉ FiniteIO.IOLogDerivEventW (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q)
      (SVFrame.liftWts (cellVRecords δF b hn nodes orbit chals pubs Q)) γ)
    (hcount : (reqs ++ cellVInternal δF b hn nodes orbit chals pubs Q).length < p)
    (vl : List (VKey (Quad (algebraMap F K δF)))) :
    TableAccepts (Quad.mk (algebraMap F K δF) (chals 2) (chals 3))
      (cellTableOf δF b nodes orbit chals pubs Q) vl :=
  cellTable_accepts δF b hn nodes orbit chals pubs Q hsat hF hq hz hbind hinj hadj hnp
    (cell_validityServed δF b hn nodes orbit chals pubs Q hsat hbind hinj hadj γ ρ hok reqs hsum hne hγ hpole hcount) vl

end CellAcc

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
