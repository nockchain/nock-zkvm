/-
  Nock/NockVMROM/Thm54/VclL/Chips/RowBridge.lean

  For either VCL-L chip (`cellChip` / `pathChip`, `ChipRAP.lean`) and any trace `Q` it accepts:
  * `cellChip_rowLocal` / `pathChip_rowLocal`: at every row node `nodes i`, every base-field gate of
    the chip's list vanishes in the base environment and every mixed gate vanishes in the gathered
    `𝕂` environment (`expandChip_satisfies_iff_language` at `x = nodes i ∈ rowNodeSet nodes`);
  * `next_node`: under row adjacency (`SVFrame.VerifierData.Checks.memAdjacent`, R-LC8) the
    environment's next row `ω · nodes i` IS `nodes (i + 1)`, so every `traceNext` leaf reads row
    `i + 1` of the committed table;
  * `cellChip_masks` / `pathChip_masks`: the two fixed columns evaluate to `[i = 0]` and
    `[i = n − 1]` at row `i` (preprocessing binding + `firstRowMask_eval` / `lastRowMask_eval`);
  * `gather_chal_cell` / `gather_pub_cell` (and the path twins): the gathered `𝕂` challenge / public
    leaves are exactly the supplied `chals` / `pubs` (`slotVal` is the inverse of the compiler's
    slot layout).

  NOT here (the remaining half): reading the per-row equations as `Table.RowOK` / `SerialOK` /
  `ValidityServed` and `Chain` edges — the ℕ-valued limbs and serials from `𝔽` (via
  `PrimeFieldElems`), the bit certificates, the `𝕂′` recombination (`Quad.mk`), and the LogUp
  telescoping into `IOFacts`.  **Unconfirmed** until compiled.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

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
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

theorem mem_rowNodeSet (i : Fin n) : nodes i ∈ rowNodeSet nodes := by
  classical
  unfold rowNodeSet
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-! ## 1. Row-local gate equations -/

/-- **Cell table, row-local**: at row `i` every base gate and every mixed gate vanishes. -/
theorem cellChip_rowLocal (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (∀ g ∈ Cell.baseGates (F := F),
        g.eval (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 129 chals) (slotVal b 129 pubs)) = 0) ∧
      (∀ g ∈ Cell.mixedGates δF,
        g.eval (gatherEnv b ((cellTemplate δF).col0 3)
            (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 129 chals) (slotVal b 129 pubs)))
          (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 129 chals) (slotVal b 129 pubs)) = 0) := by
  have hl := (expandChip_satisfies_iff_language (cellTemplate δF) b (slotVal b 129 chals)
    (slotVal b 129 pubs) orbit (rowNodeSet nodes) Q).mp hsat (nodes i) (mem_rowNodeSet nodes i)
  exact ⟨hl.1, hl.2.2.2⟩

/-- **Path chip, row-local.** -/
theorem pathChip_rowLocal (Q : Fin (pathChip δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (pathChip δF b hn nodes orbit chals pubs).rap.Satisfies Q) (i : Fin n) :
    (∀ g ∈ Path.baseGates (F := F),
        g.eval (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 16 chals) (slotVal b 16 pubs)) = 0) ∧
      (∀ g ∈ Path.mixedGates δF,
        g.eval (gatherEnv b ((pathTemplate δF).col0 3)
            (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 16 chals) (slotVal b 16 pubs)))
          (Reify.envOfTrace Q orbit.ω (nodes i) (slotVal b 16 chals) (slotVal b 16 pubs)) = 0) := by
  have hl := (expandChip_satisfies_iff_language (pathTemplate δF) b (slotVal b 16 chals)
    (slotVal b 16 pubs) orbit (rowNodeSet nodes) Q).mp hsat (nodes i) (mem_rowNodeSet nodes i)
  exact ⟨hl.1, hl.2.2.2⟩

/-! ## 2. The next row -/

/-- **Under row adjacency the environment's next row is row `i + 1`** (`Checks.memAdjacent`:
`nodes (i+1) = nodes i · ω`; `envOfTrace` reads `traceNext` at `ω · x`). -/
theorem next_node (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) : orbit.ω * nodes i = nodes ⟨(i : ℕ) + 1, hi⟩ := by
  rw [hadj i hi, mul_comm]

/-- The next-row leaf of column `j` at row `i` is column `j` at row `i + 1`. -/
theorem traceNext_eq {w : ℕ} (Q : Fin w → F[X]) (cv pv : ℕ → F)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) :
    (Reify.envOfTrace Q orbit.ω (nodes i) cv pv).traceNext j =
      (Reify.envOfTrace Q orbit.ω (nodes ⟨(i : ℕ) + 1, hi⟩) cv pv).trace j := by
  simp only [Reify.envOfTrace, next_node nodes orbit hadj i hi]

/-! ## 3. The endpoint masks -/

/-- **Cell table masks**: column `0` is `[i = 0]`, column `1` is `[i = n − 1]` at row `i`. -/
theorem cellChip_masks (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (Q ⟨0, by rw [(cellChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega⟩).eval (nodes i) =
        (if (i : ℕ) = 0 then 1 else 0) ∧
      (Q ⟨1, by rw [(cellChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega⟩).eval (nodes i) =
        (if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0) := by
  have h0 := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 := hbind ⟨1, by show 1 < 2; omega⟩
  refine ⟨?_, ?_⟩
  · have : Q ⟨0, _⟩ = firstRowMask nodes := h0
    rw [this, firstRowMask_eval nodes hinj i]
  · have : Q ⟨1, _⟩ = lastRowMask hn nodes := h1
    rw [this, lastRowMask_eval hn nodes hinj i]

/-- **Path chip masks.** -/
theorem pathChip_masks (Q : Fin (pathChip δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hbind : (pathChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes) (i : Fin n) :
    (Q ⟨0, by rw [(pathChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega⟩).eval (nodes i) =
        (if (i : ℕ) = 0 then 1 else 0) ∧
      (Q ⟨1, by rw [(pathChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega⟩).eval (nodes i) =
        (if i = ⟨n - 1, Nat.sub_lt hn (by omega)⟩ then 1 else 0) := by
  have h0 := hbind ⟨0, by show 0 < 2; omega⟩
  have h1 := hbind ⟨1, by show 1 < 2; omega⟩
  refine ⟨?_, ?_⟩
  · have : Q ⟨0, _⟩ = firstRowMask nodes := h0
    rw [this, firstRowMask_eval nodes hinj i]
  · have : Q ⟨1, _⟩ = lastRowMask hn nodes := h1
    rw [this, lastRowMask_eval hn nodes hinj i]

/-! ## 4. The gathered challenge / public leaves are the supplied values -/

/-- `slotVal` inverts the compiler's slot layout: the `e = 3` coordinates at `base + 3 idx + k`
recombine to `v idx`. -/
theorem sum_slotVal (base idx : ℕ) (v : ℕ → K) :
    ∑ k : Fin 3, slotVal b base v (base + 3 * idx + (k : ℕ)) • b k = v idx := by
  have hk : ∀ k : Fin 3, slotVal b base v (base + 3 * idx + (k : ℕ)) = coord b (v idx) k := by
    intro k
    have hle : base ≤ base + 3 * idx + (k : ℕ) := by omega
    have hdiv : (base + 3 * idx + (k : ℕ) - base) / 3 = idx := by
      have := k.isLt; omega
    have hmod : (base + 3 * idx + (k : ℕ) - base) % 3 = (k : ℕ) := by
      have := k.isLt; omega
    unfold slotVal
    rw [if_pos hle]
    congr 1
    · rw [hdiv]
    · exact Fin.ext hmod
  simp only [hk, coord]
  exact b.sum_repr (v idx)

theorem gather_chal_cell (env : Env F) (henv : env.chal = slotVal b 129 chals) (idx : ℕ) :
    (gatherEnv b ((cellTemplate δF).col0 3) env).chal idx = chals idx := by
  simp only [gatherEnv, ChipTemplate.col0, cellTemplate_baseCols, henv]
  exact sum_slotVal b 129 idx chals

theorem gather_pub_cell (env : Env F) (henv : env.pub = slotVal b 129 pubs) (idx : ℕ) :
    (gatherEnv b ((cellTemplate δF).col0 3) env).pub idx = pubs idx := by
  simp only [gatherEnv, ChipTemplate.col0, cellTemplate_baseCols, henv]
  exact sum_slotVal b 129 idx pubs

theorem gather_chal_path (env : Env F) (henv : env.chal = slotVal b 16 chals) (idx : ℕ) :
    (gatherEnv b ((pathTemplate δF).col0 3) env).chal idx = chals idx := by
  simp only [gatherEnv, ChipTemplate.col0, pathTemplate_baseCols, henv]
  exact sum_slotVal b 16 idx chals

theorem gather_pub_path (env : Env F) (henv : env.pub = slotVal b 16 pubs) (idx : ℕ) :
    (gatherEnv b ((pathTemplate δF).col0 3) env).pub idx = pubs idx := by
  simp only [gatherEnv, ChipTemplate.col0, pathTemplate_baseCols, henv]
  exact sum_slotVal b 16 idx pubs

/-! ## 5. A first row-model consequence: serial threading (`Table.SerialOK`, field form) -/

theorem envOfTrace_trace {w : ℕ} (P : Fin w → F[X]) (ω x : F) (cv pv : ℕ → F) {j : ℕ} (hj : j < w) :
    (Reify.envOfTrace P ω x cv pv).trace j = (P ⟨j, hj⟩).eval x := by
  simp [Reify.envOfTrace, hj]

theorem envOfTrace_traceNext {w : ℕ} (P : Fin w → F[X]) (ω x : F) (cv pv : ℕ → F) {j : ℕ}
    (hj : j < w) : (Reify.envOfTrace P ω x cv pv).traceNext j = (P ⟨j, hj⟩).eval (ω * x) := by
  simp [Reify.envOfTrace, hj]

/-- **The serial column threads `0, 1, 2, …`** on any accepted cell table (the gates
`isFirst·idx` and `(1 − isLast)(idx′ − idx − 1)`, the masks, and row adjacency): the value of
`idx` at row `i` is `i`.  This is `Table.SerialOK` in the field; with `n < p` (`Checks.hrowsM`) it
is the ℕ statement. -/
theorem cellChip_serial (Q : Fin (cellChip δF b hn nodes orbit chals pubs).rap.w → F[X])
    (hsat : (cellChip δF b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (cellChip δF b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    ∀ i : Fin n, (Q ⟨2, by rw [(cellChip_fingerprint δF b hn nodes orbit chals pubs).1]; omega⟩).eval
      (nodes i) = ((i : ℕ) : F) := by
  have hw : (cellChip δF b hn nodes orbit chals pubs).rap.w = 225 :=
    (cellChip_fingerprint δF b hn nodes orbit chals pubs).1
  intro i
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero =>
    have hrow := (cellChip_rowLocal δF b hn nodes orbit chals pubs Q hsat ⟨0, hi⟩).1
    have g := hrow (.mul (cv Cell.isF) (cv Cell.idx)) (by simp [Cell.baseGates])
    have hm := (cellChip_masks δF b hn nodes orbit chals pubs Q hbind hinj ⟨0, hi⟩).1
    simp only [CoeffExpr.eval, cv, Cell.isF, Cell.idx,
      envOfTrace_trace Q _ _ _ _ (show 0 < _ by rw [hw]; omega),
      envOfTrace_trace Q _ _ _ _ (show 2 < _ by rw [hw]; omega)] at g
    rw [hm] at g
    simpa using g
  | succ k ih =>
    have hk : k < n := by omega
    have hrow := (cellChip_rowLocal δF b hn nodes orbit chals pubs Q hsat ⟨k, hk⟩).1
    have g := hrow (.mul (notE (cv Cell.isL)) (.sub (.sub (nv Cell.idx) (cv Cell.idx)) (.const 1)))
      (by simp [Cell.baseGates])
    have hm := (cellChip_masks δF b hn nodes orbit chals pubs Q hbind hinj ⟨k, hk⟩).2
    have hnext := next_node nodes orbit hadj ⟨k, hk⟩ hi
    simp only [CoeffExpr.eval, cv, nv, notE, Cell.isL, Cell.idx,
      envOfTrace_trace Q _ _ _ _ (show 1 < _ by rw [hw]; omega),
      envOfTrace_trace Q _ _ _ _ (show 2 < _ by rw [hw]; omega),
      envOfTrace_traceNext Q _ _ _ _ (show 2 < _ by rw [hw]; omega)] at g
    rw [hm, hnext, ih hk] at g
    have hne : (⟨k, hk⟩ : Fin n) ≠ ⟨n - 1, Nat.sub_lt hn (by omega)⟩ := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    rw [if_neg hne] at g
    push_cast
    linear_combination g


end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
