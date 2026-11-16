/-
  Nock/NockVMROM/Thm54/P8Core/SVWalk/MemWindow.lean

  **The walk instance's served-noun window, `window_le`.**

  The r2 frame asks `MF.served_leaves_le` and `MF.window_le` at EVERY B0 message (no acceptance),
  with a trace-free `windowBound V x := V.memRows 0`.  The decoded nouns are bounded by `M` only
  under queue validity (`BFSValidF`), which acceptance supplies.  So the instance serves the
  CAPPED decode:

  * `servedNounOfEnvs_leaves_le` : under `BFSValidF kroots (preFoOfEnvs envs hM) M` every served
    noun has `≤ M` leaves (`preZNounOfEnvs_leaves_le`, the route-B C3 cell; `atom 0` if no row);
  * `capped n M` := `n` if `n.leaves ≤ M` else `atom 0`; `capped_leaves_le` (unconditional, so
    `window := M`, `window_le := le_rfl`, `served_leaves_le` hold at every message);
    `servedCapped_eq` : under `BFSValidF` the capped decode IS the served noun, so
    `response_sound` (which runs under acceptance) sees the true decode.
-/
import Nock.NockVMROM.Thm54.BuildTFWindow
import Nock.NockVMROM.Thm54.PreZComputeCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.SVWalk

open Nock Nock.Reified Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.PreZComputeCore.Served

noncomputable section

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {M : ℕ}

/-- **Served nouns are in the window `M`** under queue validity. -/
theorem servedNounOfEnvs_leaves_le (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M)
    (hvalid : BFSValidF kroots (preFoOfEnvs envs hM) M) (st : MState) (k : ℕ) :
    (servedNounOfEnvs K q kroots envs hM st k).leaves ≤ M := by
  unfold servedNounOfEnvs
  split
  · simp [Noun.leaves]; omega
  · rename_i j rest hrows
    have hj : j ∈ servedRowsOfEnvs envs hM st k := by rw [hrows]; exact List.mem_cons_self ..
    unfold servedRowsOfEnvs at hj
    rw [List.mem_filter, List.mem_range'_1] at hj
    exact preZNounOfEnvs_leaves_le K q kroots envs hM hvalid (by omega) (by omega)

/-- The window cap. -/
def capped (n : Noun) (W : ℕ) : Noun := if n.leaves ≤ W then n else .atom 0

theorem capped_leaves_le (n : Noun) (W : ℕ) (hW : 1 ≤ W) : (capped n W).leaves ≤ W := by
  unfold capped
  split_ifs with h
  · exact h
  · simp [Noun.leaves]; exact hW

theorem capped_eq (n : Noun) (W : ℕ) (h : n.leaves ≤ W) : capped n W = n := by
  simp [capped, h]

/-- The capped served decode. -/
def servedCapped (K : Type) [Field K] [Algebra F K] (q kroots : ℕ) (envs : Fin M → Env F)
    (hM : 0 < M) (st : MState) (k : ℕ) : Noun :=
  capped (servedNounOfEnvs K q kroots envs hM st k) M

/-- **`window_le` / `served_leaves_le` at the walk instance**: every capped served noun has
`≤ M = memRows` leaves, at every message. -/
theorem servedCapped_leaves_le (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M) (st : MState) (k : ℕ) :
    (servedCapped K q kroots envs hM st k).leaves ≤ M :=
  capped_leaves_le _ _ hM

/-- Under queue validity the cap is invisible. -/
theorem servedCapped_eq (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M)
    (hvalid : BFSValidF kroots (preFoOfEnvs envs hM) M) (st : MState) (k : ℕ) :
    servedCapped K q kroots envs hM st k = servedNounOfEnvs K q kroots envs hM st k :=
  capped_eq _ _ (servedNounOfEnvs_leaves_le K q kroots envs hM hvalid st k)

/-- The capped decode reads the pre-`z` columns only (`preZMemCols`, all round 0): inherited from
the served decode by congruence. -/
theorem servedCapped_congr (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    {envs envs' : Fin M → Env F} (hM : 0 < M)
    (h : servedNounOfEnvs K q kroots envs hM = servedNounOfEnvs K q kroots envs' hM) :
    servedCapped K q kroots envs hM = servedCapped K q kroots envs' hM := by
  funext st k
  unfold servedCapped
  rw [h]

end

end Nock.NockVMROM.Thm54.SVWalk
