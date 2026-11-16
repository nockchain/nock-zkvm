/-
  Nock/NockVMROM/Thm54/P8Core/SVFrame/MemSoundnessFamily.lean

  Every name is kept. No-digest-move,
  additive; this module imports P8Core only and never the statement file.

  `CF.recKey` stays
  B0-typed as in r2. `axisOfRecords` (unused since r2) is deleted.

  Original header:

  **The generic frame for the 38th: coins as a frame, tables as a shape, the memory side as a
  `MemSoundnessFamily`, the compute side as a `CompSoundnessFamily`, and the generic
  `StandaloneThm54Statement`.**  Compiled against the live build via `LEAN_PATH`.
  Nothing here is a theorem about the chips; every field is an OBLIGATION the instance discharges.

  Designed for four points:
  1. relinking: the served nouns are decoded from B0 columns BY TYPE (`B0Cols`), so a decode that
     reads a post-`z` column cannot be an instance (`served : … → (∀ t, B0Cols F (S.table t)) → …`);
  2. multi-chip memory: `MemShape.k` tables, each with its own width, column-round map and height;
     `AcceptsV.memory` is `∀ t`; the verifier carries one orbit per table (`VerifierData.orbitM`);
  3. decode from B0: as 1, plus `CompSoundnessFamily.skeleton` from the compute B0 columns;
  4. coins: `CoinFrame` (`n`, `sampledAfter`) — no `Tuple12`, no `α`,
     `αW`, `λ`, `interPole` in the frame; the current chip's twelve coins are `frame12`, the
     tower's thirteen are `frame13`; every coin a summand prices is named by the summand itself.

`VerifierData.Checks` takes the
  per-accumulator consumer bound and the IO characteristic, `V.Checks consumerBound pIO`, with the new
  field `hcons : ∀ a, consumerBound a < pIO`; the statement checks it at
  `consumerBound CF MF V a = CF.reqBound V a + MF.internalBound V a` (the `k₁` the IO summand prices;
  VCL-L export: `3N + P`) and `pIO = ringChar Kio` — public sizes only, no trace read (the same kind
  as `hrowsC`). The row bounds `3N < p`, `P < p` do NOT imply `3N + P < p` (`p = 97`, `N = P = 32`). `serves` / `response_sound` receive the count `(reqs a ++ internal …).length < ringChar Kio`, which
  the generic proof supplies from `hcons` and the two length fields.

  `VerifierData`'s node lists are FREE data (`computeNodes : Fin N → F`, `memNodes t`), so adjacency
  is not a theorem of the datum; it is a public-data verifier check, the package's
  `computeAdjacentOrbit` / `memoryAdjacentOrbit`: `Checks.hadjC : V.AdjacentC`
  (`computeNodes ⟨i+1,_⟩ = orbitC.ω * computeNodes i`) and `Checks.hadjM : ∀ t, V.AdjacentM t`
  (`memNodes t ⟨i+1,_⟩ = memNodes t i * (orbitM t).ω`), both `Decidable` from `V` alone (no trace
  read). `Checks.computeAdjacent` / `Checks.memAdjacent` expose them; `AdjacentC.nodes_eq_pow` /
  `AdjacentM.nodes_eq_pow` give the closed form `ω^i·x₀`. No chip reads them. -/
import Nock.NockVMROM.Thm54.StandaloneVerifierData
import Nock.NockVMROM.Thm54.P8Core.SVIOAssembly
import Nock.NockVMROM.Thm54.P8Core.RootGoodFJoin
import Nock.NockVMROM.Thm54.P8Core.SVFrame.WeightedIO

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVFrame

open Nock Nock.Framework Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF)
open Nock.ComputeTable (FP State DTcomp)
open Nock.MemoryTable (MState)
open Nock.Walk (NTree)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Coins: a frame, not a tuple -/

/-- **A coin frame**: `n` coins and the block after which each is sampled (`sampledAfter`, the shape
of `ChallengeChronology.sampledAfter`). -/
structure CoinFrame where
  n : ℕ
  sampledAfter : Fin n → ℕ

/-- The coins as a vector (the `tuple12VecEquiv` view, at any `n`). -/
abbrev Coins (Φ : CoinFrame) (K : Type) := Fin Φ.n → K

/-- **Staging at a frame** (`Staged12` / `StagedVec` at any `n`): a column of round `r` is a function
of the coins sampled after blocks `< r` only. -/
def StagedCols (Φ : CoinFrame) {K : Type} {ι β : Type*} (colRound : ι → ℕ)
    (Q : Coins Φ K → ι → β) : Prop :=
  ∀ j χ χ', (∀ i : Fin Φ.n, Φ.sampledAfter i < colRound j → χ i = χ' i) → Q χ j = Q χ' j

theorem stagedCols_const (Φ : CoinFrame) {K : Type} {ι β : Type*} (colRound : ι → ℕ) (q : ι → β) :
    StagedCols Φ (K := K) colRound (fun _ => q) :=
  fun _ _ _ _ => rfl

/-- A bad set reads only the coins in `dep` (`RoundFibred.ReadsOn` at the frame). -/
def ReadsOnC (Φ : CoinFrame) {K : Type} {β : Type*} (dep : Finset (Fin Φ.n))
    (f : Coins Φ K → β) : Prop :=
  ∀ χ χ' : Coins Φ K, (∀ j ∈ dep, χ j = χ' j) → f χ = f χ'

/-- Walk: `Kio = 𝕂`, `dep = {4, 5}` (`ioSpec12`); VCL-L (DESIGN §2
(II)): `Kio = 𝕂′`, `dep = {4, 5, 6, 7}` (`ioSpecVCL`). -/
structure IOCoinSpec (Φ : CoinFrame) (K Kio : Type) where
  ioCoins : Coins Φ K → FiniteIO.IOCoins Kio
  dep : Finset (Fin Φ.n)
  readsOn : ReadsOnC Φ dep ioCoins
  inj : ∀ χ χ' : Coins Φ K, ioCoins χ = ioCoins χ' → ∀ i ∈ dep, χ i = χ' i

/-- The IO coins of a vector as a `(γ, pole)` pair (the coordinates of `FiniteIO.IOFailureEvent`). -/
def IOCoinSpec.pair {Φ : CoinFrame} {K Kio : Type} (I : IOCoinSpec Φ K Kio) (χ : Coins Φ K) :
    Kio × Kio :=
  ((I.ioCoins χ).gamma, (I.ioCoins χ).pole)

/-- **IO coins in `𝕂` at two frame indices**. -/
def IOCoinSpec.ofPair (Φ : CoinFrame) (K : Type) (iγ iρ : Fin Φ.n) : IOCoinSpec Φ K K where
  ioCoins χ := ⟨χ iγ, χ iρ⟩
  dep := {iγ, iρ}
  readsOn χ χ' h := by
    show (⟨χ iγ, χ iρ⟩ : FiniteIO.IOCoins K) = ⟨χ' iγ, χ' iρ⟩
    rw [h iγ (by simp), h iρ (by simp)]
  inj χ χ' h i hi := by
    have hg : χ iγ = χ' iγ := congrArg FiniteIO.IOCoins.gamma h
    have hp : χ iρ = χ' iρ := congrArg FiniteIO.IOCoins.pole h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hg
    · exact hp


def IOCoinSpec.ofExt (Φ : CoinFrame) {K Kio : Type} (mk : K → K → Kio)
    (hmk : ∀ a b c d, mk a b = mk c d → a = c ∧ b = d) (iγ iρ : Fin Φ.n × Fin Φ.n) :
    IOCoinSpec Φ K Kio where
  ioCoins χ := ⟨mk (χ iγ.1) (χ iγ.2), mk (χ iρ.1) (χ iρ.2)⟩
  dep := {iγ.1, iγ.2, iρ.1, iρ.2}
  readsOn χ χ' h := by
    show (⟨mk (χ iγ.1) (χ iγ.2), mk (χ iρ.1) (χ iρ.2)⟩ : FiniteIO.IOCoins Kio) =
      ⟨mk (χ' iγ.1) (χ' iγ.2), mk (χ' iρ.1) (χ' iρ.2)⟩
    rw [h iγ.1 (by simp), h iγ.2 (by simp), h iρ.1 (by simp), h iρ.2 (by simp)]
  inj χ χ' h i hi := by
    have hg := hmk _ _ _ _ (congrArg FiniteIO.IOCoins.gamma h :
      mk (χ iγ.1) (χ iγ.2) = mk (χ' iγ.1) (χ' iγ.2))
    have hp := hmk _ _ _ _ (congrArg FiniteIO.IOCoins.pole h :
      mk (χ iρ.1) (χ iρ.2) = mk (χ' iρ.1) (χ' iρ.2))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hg.1
    · exact hg.2
    · exact hp.1
    · exact hp.2

/-- **The current schedule as a frame**: `repartitionedChronology`'s twelve coins
`[αC, γ, αM, z, IOγ, IOpole, a, b, c, interPole, λ, αW]`, IO coins at `4`/`5`. -/
def frame12 : CoinFrame where
  n := 12
  sampledAfter := fun i => ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1] i

/-- `frame12`'s IO coins: slots `4`/`5` in `𝕂`. -/
def ioSpec12 (K : Type) : IOCoinSpec frame12 K K :=
  IOCoinSpec.ofPair frame12 K ⟨4, by decide⟩ ⟨5, by decide⟩

/-- `frame12` is `repartitionedChronology`'s schedule. -/
theorem frame12_sampledAfter (i : Fin 12) :
    frame12.sampledAfter i =
      ((RepartitionedStaging.repartitionedChronology.sampledAfter i : Fin 3) : ℕ) := by
  fin_cases i <;> rfl

/-- **The tower frame (T0)**: `frame12` plus `z₂` at index `12`, sampled after B0 (M1). -/
def frame13 : CoinFrame where
  n := 13
  sampledAfter := fun i => ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0] i

/-- `frame13`'s IO coins: slots `4`/`5` in `𝕂`. -/
def ioSpec13 (K : Type) : IOCoinSpec frame13 K K :=
  IOCoinSpec.ofPair frame13 K ⟨4, by decide⟩ ⟨5, by decide⟩

/-- No `α`, `interPole`, `λ`, `αW`. -/
def frameVCL : CoinFrame where
  n := 11
  sampledAfter := fun i => ![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0] i

/-- The `γ′` index pair of `frameVCL`. -/
def ioγVCL : Fin frameVCL.n × Fin frameVCL.n := (⟨4, by decide⟩, ⟨6, by decide⟩)

/-- The `ρ′` index pair of `frameVCL`. -/
def ioρVCL : Fin frameVCL.n × Fin frameVCL.n := (⟨5, by decide⟩, ⟨7, by decide⟩)

/-- **The VCL-L IO coins in `𝕂′`** through an injective coordinate map (at `Kio = Quad δ`:
`Quad.mk δ`, so `Fintype.card Kio = |𝕂|²`, `quad_card`). -/
def ioSpecVCL {K Kio : Type} (mk : K → K → Kio) (hmk : ∀ a b c d, mk a b = mk c d → a = c ∧ b = d) :
    IOCoinSpec frameVCL K Kio :=
  IOCoinSpec.ofExt frameVCL mk hmk ioγVCL ioρVCL

/-- The VCL-L IO coins are four frame coins. -/
theorem ioSpecVCL_dep_card {K Kio : Type} (mk : K → K → Kio)
    (hmk : ∀ a b c d, mk a b = mk c d → a = c ∧ b = d) : (ioSpecVCL mk hmk).dep.card = 4 := by
  show ({ioγVCL.1, ioγVCL.2, ioρVCL.1, ioρVCL.2} : Finset (Fin frameVCL.n)).card = 4
  decide

/-- The VCL-L IO coins are all sampled after B1 (M2). -/
theorem ioSpecVCL_round {K Kio : Type} (mk : K → K → Kio)
    (hmk : ∀ a b c d, mk a b = mk c d → a = c ∧ b = d) :
    ∀ i ∈ (ioSpecVCL mk hmk).dep, frameVCL.sampledAfter i = 1 := by
  show ∀ i ∈ ({ioγVCL.1, ioγVCL.2, ioρVCL.1, ioρVCL.2} : Finset (Fin frameVCL.n)),
    frameVCL.sampledAfter i = 1
  decide

/-! ## 2. Tables: width, column rounds, height; the B0 columns by type -/

/-- One committed table: its width, its column → round map, and its own domain height. -/
structure TableSpec where
  width : ℕ
  colRound : Fin width → ℕ
  height : ℕ

/-- **The round-0 columns of a table**, by type: a decoder typed on `B0Cols` cannot read a
post-`z` column (point 3; the relinking attack of VCL as designed read `fp`, a round-1
column). -/
abbrev B0Cols (F : Type) [Field F] (T : TableSpec) :=
  {j : Fin T.width // T.colRound j = 0} → F[X]

/-- The B0 projection of a full trace. -/
def b0 {F : Type} [Field F] {T : TableSpec} (Q : Fin T.width → F[X]) : B0Cols F T :=
  fun j => Q j.1

/-- The memory side's shape: `k` tables (the walk chip: `k = 1`; VCL-L: `k = 2`, cells + paths). -/
structure MemShape where
  k : ℕ
  table : Fin k → TableSpec

/-- The current memory table at the current schedule. -/
def table205 (h : ℕ) : TableSpec where
  width := 205
  colRound := fun j => RepartitionedStaging.newMemoryColRound j
  height := h

/-- The current compute table at the current schedule. -/
def table309 (h : ℕ) : TableSpec where
  width := 309
  colRound := fun j => RepartitionedStaging.newComputeColRound j
  height := h

def shapeWalk (h : ℕ) : MemShape where
  k := 1
  table := fun _ => table205 h

/-- The VCL-L shape: a cell table and a path chip, each with its own width, column-round map and
height. -/
def shapeVCL (hT hP wT wP : ℕ) (rT : Fin wT → ℕ) (rP : Fin wP → ℕ) : MemShape where
  k := 2
  table := fun t => if (t : ℕ) = 0 then ⟨wT, rT, hT⟩ else ⟨wP, rP, hP⟩

/-! ## 3. Verifier data with separate heights -/

/-- **What the verifier holds** (`StandaloneVerifierData.VerifierData` with the memory side split
into `S.k` tables and the compute height `hC` separate from each table's `(S.table t).height`).
The sizes are prover-sent (B0) and verifier-checked (`Checks`). -/
structure VerifierData (F K : Type) [Field F] [Field K] [Algebra F K] (hC : ℕ) (S : MemShape) where
  claim : P8PublicClaim
  N : ℕ
  hN : 0 < N
  Ksz : ℕ
  basis : Basis (Fin 3) F K
  orbitC : StrictOrbitDomain F 3 hC
  computeNodes : Fin N → F
  memRows : Fin S.k → ℕ
  hM : ∀ t, 0 < memRows t
  orbitM : ∀ t, StrictOrbitDomain F 3 (S.table t).height
  memNodes : ∀ t, Fin (memRows t) → F

/-- The
same shape as `SVCompute.ChipData.Adjacent` at `nodes := V.computeNodes`, `orbit := V.orbitC`. -/
def VerifierData.AdjacentC {F K : Type} [Field F] [Field K] [Algebra F K] {hC : ℕ} {S : MemShape}
    (V : VerifierData F K hC S) : Prop :=
  ∀ (i : Fin V.N) (hi : (i : ℕ) + 1 < V.N),
    V.computeNodes ⟨(i : ℕ) + 1, hi⟩ = V.orbitC.ω * V.computeNodes i


def VerifierData.AdjacentM {F K : Type} [Field F] [Field K] [Algebra F K] {hC : ℕ} {S : MemShape}
    (V : VerifierData F K hC S) (t : Fin S.k) : Prop :=
  ∀ (i : Fin (V.memRows t)) (hi : (i : ℕ) + 1 < V.memRows t),
    V.memNodes t ⟨(i : ℕ) + 1, hi⟩ = V.memNodes t i * (V.orbitM t).ω

/-- The compute adjacency check is decided from `V` alone (finitely many node equalities). -/
instance VerifierData.decAdjacentC {F K : Type} [Field F] [Field K] [Algebra F K] {hC : ℕ}
    {S : MemShape} [DecidableEq F] (V : VerifierData F K hC S) : Decidable V.AdjacentC := by
  unfold VerifierData.AdjacentC; infer_instance

/-- The memory adjacency check is decided from `V` alone. -/
instance VerifierData.decAdjacentM {F K : Type} [Field F] [Field K] [Algebra F K] {hC : ℕ}
    {S : MemShape} [DecidableEq F] (V : VerifierData F K hC S) (t : Fin S.k) :
    Decidable (V.AdjacentM t) := by
  unfold VerifierData.AdjacentM; infer_instance

/-- The verifier's checks (none read by a chip): row budgets per table at its own height,
`rowsBound` per table, the IO window, the base-field facts. Form R's `hbasis`/`hp64` are NOT here:
they belong to the current compute instance (point 4). -/
structure VerifierData.Checks {F K : Type} [Field F] [Field K] [Algebra F K] {hC : ℕ} {S : MemShape}
    (V : VerifierData F K hC S) {nAcc : ℕ} (consumerBound : Fin nAcc → ℕ) (pIO : ℕ) : Prop where
  hcapC : V.N ≤ 2 ^ hC
  hcapM : ∀ t, V.memRows t ≤ 2 ^ (S.table t).height
  hrowsC : 3 * V.N < ringChar K
  hrowsM : ∀ t, V.memRows t < ringChar K
  hKsz : V.Ksz < ringChar K
  hF : GeneratedField.PrimeFieldElems F
  /-- The base-field floor. -/
  hp : 25 ≤ ringChar F
  /-- The claim's nouns are over `𝔽`: every atom below the characteristic. -/
  hclaim : FieldEmbedding.BoundedBy (ringChar F) V.claim.subject ∧
    FieldEmbedding.BoundedBy (ringChar F) V.claim.formula ∧
    FieldEmbedding.BoundedBy (ringChar F) V.claim.result
  computeNodes_injective : Function.Injective V.computeNodes
  memNodes_injective : ∀ t, Function.Injective (V.memNodes t)
  /-- A size check on public data
  (VCL-L export: `3N + P < p`), not implied by `hrowsC` / `hrowsM`. -/
  hcons : ∀ a, consumerBound a < pIO

  hadjC : V.AdjacentC

  hadjM : ∀ t, V.AdjacentM t

section Adjacency

variable {F K : Type} [Field F] [Field K] [Algebra F K] {hC : ℕ} {S : MemShape}
  {V : VerifierData F K hC S}

/-- **Compute adjacency from the checks** — the premise V4T's `WalkSatVCL` takes as
`hadj : D.Adjacent` (definitionally this statement at `nodes := V.computeNodes`,
`orbit := V.orbitC`). -/
theorem VerifierData.Checks.computeAdjacent {nAcc : ℕ} {cb : Fin nAcc → ℕ} {pIO : ℕ}
    (hV : V.Checks cb pIO) (i : Fin V.N) (hi : (i : ℕ) + 1 < V.N) :
    V.computeNodes ⟨(i : ℕ) + 1, hi⟩ = V.orbitC.ω * V.computeNodes i :=
  hV.hadjC i hi

/-- **Memory adjacency from the checks** (table `t`) — the memory twin R-V2 needs. -/
theorem VerifierData.Checks.memAdjacent {nAcc : ℕ} {cb : Fin nAcc → ℕ} {pIO : ℕ}
    (hV : V.Checks cb pIO) (t : Fin S.k) (i : Fin (V.memRows t))
    (hi : (i : ℕ) + 1 < V.memRows t) :
    V.memNodes t ⟨(i : ℕ) + 1, hi⟩ = V.memNodes t i * (V.orbitM t).ω :=
  hV.hadjM t i hi

/-- Closed form of the compute nodes under adjacency: row `n` is `ω^n · x₀`. -/
theorem VerifierData.AdjacentC.nodes_eq_pow (h : V.AdjacentC) :
    ∀ (n : ℕ) (hn : n < V.N),
      V.computeNodes ⟨n, hn⟩ = V.orbitC.ω ^ n * V.computeNodes ⟨0, V.hN⟩
  | 0, _ => by simp
  | n + 1, hn => by
    calc V.computeNodes ⟨n + 1, hn⟩ = V.orbitC.ω * V.computeNodes ⟨n, by omega⟩ :=
          h ⟨n, by omega⟩ hn
      _ = V.orbitC.ω ^ (n + 1) * V.computeNodes ⟨0, V.hN⟩ := by
          rw [VerifierData.AdjacentC.nodes_eq_pow h n (by omega), pow_succ]; ring

/-- Closed form of table `t`'s nodes under adjacency: row `n` is `x₀ · ω^n`. -/
theorem VerifierData.AdjacentM.nodes_eq_pow {t : Fin S.k} (h : V.AdjacentM t) :
    ∀ (n : ℕ) (hn : n < V.memRows t),
      V.memNodes t ⟨n, hn⟩ = V.memNodes t ⟨0, V.hM t⟩ * (V.orbitM t).ω ^ n
  | 0, _ => by simp
  | n + 1, hn => by
    calc V.memNodes t ⟨n + 1, hn⟩ = V.memNodes t ⟨n, by omega⟩ * (V.orbitM t).ω :=
          h ⟨n, by omega⟩ hn
      _ = V.memNodes t ⟨0, V.hM t⟩ * (V.orbitM t).ω ^ (n + 1) := by
          rw [VerifierData.AdjacentM.nodes_eq_pow h n (by omega), pow_succ]; ring

end Adjacency

/-! ## 4. Records, IO facts, and the served-noun key -/

/-- **`RecordView` r2.**  r1's `axis : record → ℕ` is NOT definable on the walk instance: a record
carries the Form R pair `(T, C′)`, whose axis is recovered only with the compute-side certificate
bits (B0 columns `202..295`, `certAxisOfEnvs`).  r2 lets `axis` read the B0 columns of both sides
(walk: `certAxisOfEnvs` at the record's exponent; VCL-L: the path record's `acc` slot). -/
structure RecordView (F K Kio Kfp Key : Type) [Field F] [Field K] [Algebra F K] (C : TableSpec)
    (S : MemShape) (hC : ℕ) {nAcc : ℕ} (m : Fin nAcc → ℕ) where
  key : ∀ a : Fin nAcc, (Fin (m a) → Kio) → Key
  root : ∀ a : Fin nAcc, (Fin (m a) → Kio) → FP Kfp
  child : ∀ a : Fin nAcc, (Fin (m a) → Kio) → FP Kfp
  axis : ∀ a : Fin nAcc, VerifierData F K hC S → B0Cols F C → (∀ t, B0Cols F (S.table t)) →
    (Fin (m a) → Kio) → ℕ

/-- **Consumer IO facts at one accumulator** (the compute side's request records, unit weights):
a committed list whose LogUp sum is the terminal `ρ`, with nonvanishing denominators. -/
structure ReqIOFacts {Kio : Type} [Field Kio] {m : ℕ} (den : (Fin m → Kio) → Kio) (ρ : Kio) where
  records : List (Fin m → Kio)
  sum_eq : (records.map fun r => (den r)⁻¹).sum = ρ
  ne_zero : ∀ r ∈ records, den r ≠ 0


structure IOFacts (F : Type) {Kio : Type} [Field F] [Field Kio] [Algebra F Kio] {m : ℕ}
    (den : (Fin m → Kio) → Kio) (ρ : Kio) where
  records : List ((Fin m → Kio) × F)
  sum_eq : (records.map fun r => algebraMap F Kio r.2 * (den r.1)⁻¹).sum = ρ
  ne_zero : ∀ r ∈ records, den r.1 ≠ 0

/-- The provider rows with their weights mapped into the IO field (what `IOFailureEventW` reads). -/
def liftWts {F Kio : Type} [Field F] [Field Kio] [Algebra F Kio] {m : ℕ}
    (l : List ((Fin m → Kio) × F)) : List ((Fin m → Kio) × Kio) :=
  l.map fun r => (r.1, algebraMap F Kio r.2)

@[simp] theorem liftWts_length {F Kio : Type} [Field F] [Field Kio] [Algebra F Kio] {m : ℕ}
    (l : List ((Fin m → Kio) × F)) : (liftWts l).length = l.length := by
  simp [liftWts]

theorem liftWts_fst {F Kio : Type} [Field F] [Field Kio] [Algebra F Kio] {m : ℕ}
    (l : List ((Fin m → Kio) × F)) : (liftWts l).map Prod.fst = l.map Prod.fst := by
  simp [liftWts, Function.comp_def]


def IOFacts.withNoInternal {F Kio : Type} [Field F] [Field Kio] [Algebra F Kio] {m : ℕ}
    {den : (Fin m → Kio) → Kio} {ρ : Kio}
    (M : IOFacts F den ρ) :
    IOFacts F den (ρ + (([] : List (Fin m → Kio)).map fun r => (den r)⁻¹).sum) :=
  ⟨M.records, by simpa using M.sum_eq, M.ne_zero⟩

/-- `SVIO.MemIOFacts` is the width-10 instance at `compress`, every row of weight `1`. -/
def IOFacts.ofMem (F : Type) {K : Type} [Field F] [Field K] [Algebra F K] {coins : FiniteIO.IOCoins K}
    {ρ : K} (M : SVIO.MemIOFacts coins ρ) : IOFacts F (FiniteIO.compress (m := 10) coins) ρ :=
  ⟨M.responses.map fun r => (r, 1),
    by
      have h : (M.responses.map fun r => (FiniteIO.compress (m := 10) coins r)⁻¹).sum = ρ := M.sum_eq
      simpa [List.map_map, Function.comp_def] using h,
    by
      intro r hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact M.ne_zero q hq⟩

/-! ## 5. Bad-event summands: priced coins, read set, weight -/

/-- **A priced summand** at a frame: the coins it is a cylinder over, the coins its bad set may read
(disjoint from the priced ones), the bad set of priced-coin values given the traces, its weight,
and round-locality: along any staged strategy the bad set reads only `dep` (the H2.1 table's
shape, `summand_k_readsOn12`).  The generic fibre bound gives `Pr[χ|coins ∈ badSet] ≤ weight / |𝕂|^|coins|`. -/
structure BadSummand (Φ : CoinFrame) (K : Type) [Fintype K] [DecidableEq K] (Tr : Type)
    (Staged : (Coins Φ K → Tr) → Prop) where
  coins : Finset (Fin Φ.n)
  dep : Finset (Fin Φ.n)
  disj : Disjoint coins dep
  badSet : Tr → Coins Φ K → Finset (coins → K)
  weight : ℕ
  card_le : ∀ tr χ, (badSet tr χ).card ≤ weight
  readsOn : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ dep (fun χ => badSet (Q χ) χ)

/-- Membership of a coin vector in a summand's event at traces `tr`. -/
def BadSummand.mem {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {Tr : Type}
    {Staged : (Coins Φ K → Tr) → Prop} (s : BadSummand Φ K Tr Staged) (tr : Tr) (χ : Coins Φ K) :
    Prop :=
  (fun i : s.coins => χ i) ∈ s.badSet tr χ

/-- **The bound function of a summand list**: `Σ weight / |𝕂|^|coins|`. -/
def epsilonOf {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {Tr : Type}
    {Staged : (Coins Φ K → Tr) → Prop} (summands : List (BadSummand Φ K Tr Staged)) : ℚ :=
  (summands.map fun s => (s.weight : ℚ) / ((Fintype.card K : ℚ) ^ s.coins.card)).sum

/-! ## 6. Traces and staging at a frame -/

/-- The traces both sides commit at one coin vector. -/
abbrev Traces (F : Type) [Field F] (C : TableSpec) (S : MemShape) :=
  (Fin C.width → F[X]) × (∀ t : Fin S.k, Fin (S.table t).width → F[X])

/-- A trace strategy is staged when every column of every table is. -/
def TracesStaged (Φ : CoinFrame) {F K : Type} [Field F] (C : TableSpec) (S : MemShape)
    (Q : Coins Φ K → Traces F C S) : Prop :=
  StagedCols Φ C.colRound (fun χ => (Q χ).1) ∧
    ∀ t, StagedCols Φ (S.table t).colRound (fun χ => (Q χ).2 t)

/-! ## 6b. r2: the seed specification, the join's record axes, the B0 shape -/

/-! ## (S) The seed specification -/

/-- **The NPR seed as a coin function with its read set**: `seed` reads only the coins in `dep`, every
such coin is sampled after B0 (M1), and `seed` is injective on them (so a bad-seed set of card `w`
pulls back to a bad set of `(dep → K)` of card `≤ w`).  Walk: `dep = {3}`, `seed χ = χ 3`; tower:
`dep = {3, 12}`, `seed χ = ⟨χ 3, χ 12⟩ : Quad K`; VCL-L: `dep = {2, 3}`. -/
structure SeedSpec (Φ : CoinFrame) (K Kfp : Type) where
  seed : Coins Φ K → Kfp
  dep : Finset (Fin Φ.n)
  readsOn : ReadsOnC Φ dep seed
  round0 : ∀ i ∈ dep, Φ.sampledAfter i = 0
  inj : ∀ χ χ' : Coins Φ K, seed χ = seed χ' → ∀ i ∈ dep, χ i = χ' i

/-- The seed coin of `frame12` (slot 3). -/
def i3 : Fin frame12.n := ⟨3, by decide⟩

theorem frame12_i3_round0 : frame12.sampledAfter i3 = 0 := by decide

/-- The walk seed (slot 3). -/
def seedSpec12 (K : Type) : SeedSpec frame12 K K where
  seed := fun χ => χ i3
  dep := {i3}
  readsOn := fun χ χ' h => h i3 (Finset.mem_singleton_self i3)
  round0 := fun i hi => by
    rw [Finset.mem_singleton] at hi
    rw [hi]
    exact frame12_i3_round0
  inj := fun χ χ' h i hi => by
    rw [Finset.mem_singleton] at hi
    rw [hi]
    exact h

/-! ## (3) The join's record axes, as a function of the axis oracle -/

/-- The axis the field C2 join assigns to record `j` of a row in state `st` at exponent prefix `S`
(`SVJoinF.c2SkeletonRowF`'s `memoryRecord`): record `0` is the formula decomposition at axis `3`;
OP0's record `1` is the read at `ax (S+2)`; OP9's record `2` is the arm at `ax (S+3)`; every other
record is a tail decomposition at axis `2`. -/
def joinRecordAxis (st : State) (ax : ℕ → ℕ) (S : ℕ) (j : ℕ) : ℕ :=
  match st, j with
  | _, 0 => 3
  | .s0, 1 => ax (S + 2)
  | .s9, 2 => ax (S + 3)
  | _, _ => 2

/-- The `j`-th trace record of a node label (`Batch1171.traceRec`'s shape). -/
def traceRecOf {Kfp : Type} (row : (State × DTcomp Kfp) × ℕ) : ℕ → ComputeTable.MemRec Kfp
  | 0 => row.1.2.2.1.mr1
  | 1 => row.1.2.2.1.mr2
  | _ => row.1.2.2.1.mr3

/-- The B0 shape of a labelled tree: states and exponent prefixes. -/
def shapeOfTree {Kfp : Type} (t : NTree ((State × DTcomp Kfp) × ℕ)) : NTree (State × ℕ) :=
  mapNTree (fun l => (l.1.1, l.2)) t

/-! ## 7–9. The two families, messages, acceptance, the generic statement (I0 r2) -/

/-! ## The memory interface, r2 -/


structure MemSoundnessFamily (F K Kio Kfp Key : Type) [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
    [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
    (Φ : CoinFrame) (hC : ℕ) (S : MemShape) (C : TableSpec) (nAcc : ℕ) {m : Fin nAcc → ℕ}
    (R : RecordView F K Kio Kfp Key C S hC m) (Z : SeedSpec Φ K Kfp)
    (I : IOCoinSpec Φ K Kio) where
  Msg0 : Type
  Msg2 : Type
  chip : ∀ (V : VerifierData F K hC S) (t : Fin S.k),
    Msg0 → (Fin nAcc → Kio) → Msg2 → Coins Φ K → FixedPreprocessingRAP F
  chip_width : ∀ V t x ρ y χ, (chip V t x ρ y χ).rap.w = (S.table t).width
  /-- Per accumulator. -/
  respBound : VerifierData F K hC S → Fin nAcc → ℕ
  /- Walk-style instances: `internal := []`, `internalBound := 0`. -/
  internal : VerifierData F K hC S → Msg0 → (∀ t : Fin S.k, Fin (S.table t).width → F[X]) →
    Coins Φ K → ∀ a : Fin nAcc, List (Fin (m a) → Kio)
  internalBound : VerifierData F K hC S → Fin nAcc → ℕ


  ioFacts : ∀ (V : VerifierData F K hC S) (x : Msg0) (ρ : Fin nAcc → Kio) (y : Msg2) (χ : Coins Φ K)
    (Q : ∀ t : Fin S.k, Fin (S.table t).width → F[X]),
    (∀ t, RAP.SatisfiesWithPreprocessing (chip V t x ρ y χ)
      (fun j => Q t (Fin.cast (chip_width V t x ρ y χ) j))) →
    ∀ a : Fin nAcc, IOFacts F (FiniteIO.compress (m := m a) (I.ioCoins χ))
      (ρ a + ((internal V x Q χ a).map fun r => (FiniteIO.compress (m := m a) (I.ioCoins χ) r)⁻¹).sum)

  ioFacts_length : ∀ V x ρ y χ Q h a, (ioFacts V x ρ y χ Q h a).records.length ≤ respBound V a
  internal_length : ∀ V x ρ y χ Q
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (chip V t x ρ y χ)
      (fun j => Q t (Fin.cast (chip_width V t x ρ y χ) j))) (a : Fin nAcc),
    (internal V x Q χ a).length ≤ internalBound V a
  internal_ne_zero : ∀ V x ρ y χ Q
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (chip V t x ρ y χ)
      (fun j => Q t (Fin.cast (chip_width V t x ρ y χ) j))) (a : Fin nAcc),
    ∀ r ∈ internal V x Q χ a, FiniteIO.compress (m := m a) (I.ioCoins χ) r ≠ 0
  /-- r2 (4): the committed response records as a function of the memory columns alone, reading
  only columns of round `≤ respRound`, sampled before the IO coins; `ioFacts` returns exactly them. -/

  respRecords : VerifierData F K hC S → Msg0 → (∀ t : Fin S.k, Fin (S.table t).width → F[X]) →
    Coins Φ K →
    ∀ a : Fin nAcc, List ((Fin (m a) → Kio) × F)
  respRound : ℕ                                                            -- r2 (4)
  respRound_le_io : ∀ i ∈ I.dep, respRound ≤ Φ.sampledAfter i
  respRecords_round : ∀ V x Q Q' (χ χ' : Coins Φ K),
    (∀ t j, (S.table t).colRound j ≤ respRound → Q t j = Q' t j) →
    (∀ i : Fin Φ.n, Φ.sampledAfter i < respRound → χ i = χ' i) →
    respRecords V x Q χ = respRecords V x Q' χ'
  ioFacts_records : ∀ V x ρ y χ Q h a, (ioFacts V x ρ y χ Q h a).records = respRecords V x Q χ a  -- r2 (4)
  internal_round : ∀ V x Q Q' (χ χ' : Coins Φ K),
    (∀ t j, (S.table t).colRound j ≤ respRound → Q t j = Q' t j) →
    (∀ i : Fin Φ.n, Φ.sampledAfter i < respRound → χ i = χ' i) →
    internal V x Q χ = internal V x Q' χ'
  servedKeys : VerifierData F K hC S → Msg0 → (∀ t, B0Cols F (S.table t)) → List Key
  servedRoot : VerifierData F K hC S → Msg0 → (∀ t, B0Cols F (S.table t)) → Key → Noun
  served : VerifierData F K hC S → Msg0 → (∀ t, B0Cols F (S.table t)) → Key → Noun
  servedKeys_length : ∀ V x b, (servedKeys V x b).length ≤ ∑ a, respBound V a
  window : VerifierData F K hC S → Msg0 → (∀ t, B0Cols F (S.table t)) → ℕ
  served_leaves_le : ∀ V x b κ, κ ∈ servedKeys V x b →
    (servedRoot V x b κ).leaves ≤ window V x b ∧ (served V x b κ).leaves ≤ window V x b
  /-- r2 (W): the trace-free majorant of the window (walk: `memRows`; VCL-L: `2^110`). -/
  windowBound : VerifierData F K hC S → Msg0 → ℕ                           -- r2 (W)
  window_le : ∀ V x b, window V x b ≤ windowBound V x                       -- r2 (W)
  /-- r2 (1): the summands at a verifier datum and a B0 message. -/
  summands : VerifierData F K hC S → Msg0 →
    List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))              -- r2 (1)

  reqCond : VerifierData F K hC S → (∀ a : Fin nAcc, List (Fin (m a) → Kio)) → Coins Φ K → Prop
  serves : ∀ V x ρ y χ Q h (Qc : Fin C.width → F[X]) (reqs : ∀ a : Fin nAcc, List (Fin (m a) → Kio)),
    reqCond V reqs χ →
    (∀ a, ((reqs a).map fun r => (FiniteIO.compress (m := m a) (I.ioCoins χ) r)⁻¹).sum = ρ a) →
    (∀ a, ∀ r ∈ reqs a, FiniteIO.compress (m := m a) (I.ioCoins χ) r ≠ 0) →

    (∀ a, I.pair χ ∉ FiniteIO.IOFailureEventW
      (reqs a ++ internal V x Q χ a) (liftWts (respRecords V x Q χ a))) →

    (∀ a, (reqs a ++ internal V x Q χ a).length < ringChar Kio) →
    (∀ s ∈ summands V x, ¬ s.mem (Qc, Q) χ) →                                -- r2 (1)
    ∀ a, ∀ r ∈ reqs a, r ∈ (ioFacts V x ρ y χ Q h a).records.map Prod.fst

  response_sound : ∀ V x ρ y χ Q h (Qc : Fin C.width → F[X])
    (reqs : ∀ a : Fin nAcc, List (Fin (m a) → Kio)),
    reqCond V reqs χ →
    (∀ a, ((reqs a).map fun r => (FiniteIO.compress (m := m a) (I.ioCoins χ) r)⁻¹).sum = ρ a) →
    (∀ a, ∀ r ∈ reqs a, FiniteIO.compress (m := m a) (I.ioCoins χ) r ≠ 0) →
    (∀ a, I.pair χ ∉ FiniteIO.IOFailureEventW
      (reqs a ++ internal V x Q χ a) (liftWts (respRecords V x Q χ a))) →
    (∀ a, (reqs a ++ internal V x Q χ a).length < ringChar Kio) →
    (∀ s ∈ summands V x, ¬ s.mem (Qc, Q) χ) →                                -- r2 (1)
    ∀ a, ∀ r ∈ (ioFacts V x ρ y χ Q h a).records,
      R.key a r.1 ∈ servedKeys V x (fun t => b0 (Q t)) ∧
      R.root a r.1 = GlobalCarryRecognizer.enc (Z.seed χ) (servedRoot V x (fun t => b0 (Q t)) (R.key a r.1)) ∧
      R.child a r.1 = GlobalCarryRecognizer.enc (Z.seed χ) (served V x (fun t => b0 (Q t)) (R.key a r.1)) ∧
      Noun.slot (R.axis a V (b0 Qc) (fun t => b0 (Q t)) r.1) (servedRoot V x (fun t => b0 (Q t)) (R.key a r.1)) =
        some (served V x (fun t => b0 (Q t)) (R.key a r.1))
  Honest : Type
  honestV : Honest → VerifierData F K hC S
  honestMsg0 : Honest → Msg0
  honestReq : Honest → Coins Φ K → Fin nAcc → Kio
  honestMsg2 : Honest → Coins Φ K → Msg2
  honestQ : Honest → Coins Φ K → ∀ t : Fin S.k, Fin (S.table t).width → F[X]
  /-- `honestQ` is the instance's EXPLICIT coin-indexed construction (a canonical completion), never a
  `Classical.choice` whose type reads the coins: `honest_staged` is a
  theorem about that construction. -/
  honest_staged : ∀ H t, StagedCols Φ (S.table t).colRound (fun χ => honestQ H χ t)
  /-- r2 (H): the honest bad set is a LIST OF SUMMANDS (seed events over `|𝕂|²`, the IO event at
  `(ioγ, ioρ)`, order conditions on `α`/`αC`/`αW`, pole hits, …), priced by `epsilonOf`, read at the
  honest traces. -/
  honestBad : Honest → List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))   -- r2 (H)
  honest_accepted : ∀ H χ (Qc : Fin C.width → F[X]),
    (∀ s ∈ honestBad H, ¬ s.mem (Qc, honestQ H χ) χ) → ∀ t,                          -- r2 (H)
    RAP.SatisfiesWithPreprocessing
      (chip (honestV H) t (honestMsg0 H) (honestReq H χ) (honestMsg2 H χ) χ)
      (fun j => honestQ H χ t (Fin.cast (chip_width _ _ _ _ _ _) j))

/-! ## The compute interface, r2 -/


structure CompSoundnessFamily (F K Kio Kfp Key : Type) [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
    [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
    (Φ : CoinFrame) (hC : ℕ) (S : MemShape) (C : TableSpec) (nAcc : ℕ) {m : Fin nAcc → ℕ}
    (R : RecordView F K Kio Kfp Key C S hC m) (Z : SeedSpec Φ K Kfp)
    (I : IOCoinSpec Φ K Kio) where
  Msg0 : Type
  chip : VerifierData F K hC S → Msg0 → (Fin nAcc → Kio) → Coins Φ K → FixedPreprocessingRAP F
  chip_width : ∀ V x ρ χ, (chip V x ρ χ).rap.w = C.width
  /-- Per accumulator. -/
  reqBound : VerifierData F K hC S → Fin nAcc → ℕ
  reqFacts : ∀ (V : VerifierData F K hC S) (x : Msg0) (ρ : Fin nAcc → Kio) (χ : Coins Φ K)
    (Q : Fin C.width → F[X]),
    RAP.SatisfiesWithPreprocessing (chip V x ρ χ) (fun j => Q (Fin.cast (chip_width V x ρ χ) j)) →
    ∀ a : Fin nAcc, ReqIOFacts (FiniteIO.compress (m := m a) (I.ioCoins χ)) (ρ a)
  reqFacts_length : ∀ V x ρ χ Q h a, (reqFacts V x ρ χ Q h a).records.length ≤ reqBound V a
  /-- r2 (4): the committed request records as a function of the compute columns alone. -/

  reqRecords : VerifierData F K hC S → Msg0 → (Fin C.width → F[X]) → Coins Φ K →
    ∀ a : Fin nAcc, List (Fin (m a) → Kio)
  recRound : ℕ                                                             -- r2 (4)
  recRound_le_io : ∀ i ∈ I.dep, recRound ≤ Φ.sampledAfter i
  reqRecords_round : ∀ V x Q Q' (χ χ' : Coins Φ K), (∀ j, C.colRound j ≤ recRound → Q j = Q' j) →
    (∀ i : Fin Φ.n, Φ.sampledAfter i < recRound → χ i = χ' i) →
    reqRecords V x Q χ = reqRecords V x Q' χ'
  reqFacts_records : ∀ V x ρ χ Q h a, (reqFacts V x ρ χ Q h a).records = reqRecords V x Q χ a   -- r2 (4)
  /-- r2 (T): the B0 SHAPE of the exec tree (states, exponent prefixes) — what the census reads. -/
  shape : VerifierData F K hC S → Msg0 → B0Cols F C → NTree (State × ℕ)   -- r2 (T)
  shape_size : ∀ V x b, (shape V x b).size ≤ V.N                            -- r2 (T)
  /-- r2 (T): the labelled exec tree (fingerprints at round `treeRound`), with the shape above. -/

  tree : VerifierData F K hC S → Msg0 → (Fin C.width → F[X]) → Coins Φ K →
    NTree ((State × DTcomp Kfp) × ℕ)
  treeRound : ℕ                                                            -- r2 (T)
  tree_round : ∀ V x Q Q' (χ χ' : Coins Φ K), (∀ j, C.colRound j ≤ treeRound → Q j = Q' j) →
    (∀ i : Fin Φ.n, Φ.sampledAfter i < treeRound → χ i = χ' i) →
    tree V x Q χ = tree V x Q' χ'
  tree_shape : ∀ V x Q χ, shapeOfTree (tree V x Q χ) = shape V x (b0 Q)    -- r2 (T)
  /-- r2 (2): the axis oracle decoded from the B0 columns of both sides (by type). -/
  axB0 : VerifierData F K hC S → Msg0 → B0Cols F C → (∀ t, B0Cols F (S.table t)) → ℕ → ℕ  -- r2 (2)
  /-- The served-noun key the join asks for (`sv st k`). -/
  keyOf : VerifierData F K hC S → Msg0 → B0Cols F C → MState → ℕ → Key
  /-- r2 (3): the key of record `j` of a row in state `st` at exponent prefix `S`; OP0's read is
  the join's `sv .verify_child (S + 2)`. -/
  recKey : VerifierData F K hC S → Msg0 → B0Cols F C → State → ℕ → ℕ → Key   -- r2 (3)
  recKey_s0 : ∀ V x b S', recKey V x b .s0 S' 1 = keyOf V x b .verify_child (S' + 2)   -- r2 (3)
  /- An inline record is never OP0's read or OP9's arm (`inline_not_read`). `inlinePairs st j rt` are the noun pairs the instance's inline argument needs separated at the
  seed (priced by the joint `inlineSummand`, `inlinePairCount` pairs per record). -/
  inlineRecords : State → ℕ
  inline_not_read : ∀ (st : State) (j : ℕ), j < inlineRecords st →
    ¬ (st = .s0 ∧ j = 1) ∧ ¬ (st = .s9 ∧ j = 2)
  inlinePairs : State → ℕ → Noun → List (Noun × Noun)
  inlinePairCount : ℕ
  inlinePairs_length : ∀ st j rt, (inlinePairs st j rt).length ≤ inlinePairCount
  /-- r2 (1): the summands at a verifier datum and a B0 message. -/
  summands : VerifierData F K hC S → Msg0 →
    List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))              -- r2 (1)
  /-- r2 (3): **the row-to-record link.**  Outside the summands, every node of the tree and every
  record `j < recordCount st` has a request record (in some accumulator) whose root/child are the
  node's trace record, whose key is `recKey st S j`, and whose axis is the join's record axis at
  `axB0` — or it is OP0's read / OP9's arm at record axis `1` with child = root. -/
  node_records : ∀ V x ρ χ (Q : Fin C.width → F[X]) (h : RAP.SatisfiesWithPreprocessing (chip V x ρ χ)
      (fun j => Q (Fin.cast (chip_width V x ρ χ) j))) (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X]),
    (∀ s ∈ summands V x, ¬ s.mem (Q, Qm) χ) →
    ∀ u : NTree ((State × DTcomp Kfp) × ℕ), Nock.Walk.InTree (tree V x Q χ) u →
      ∀ j : ℕ, inlineRecords u.label.1.1 ≤ j → j < Nock.Framework.recordCount u.label.1.1 →
      (∃ a, ∃ r ∈ (reqFacts V x ρ χ Q h a).records,
        R.root a r = (traceRecOf u.label j).root ∧
        R.child a r = (traceRecOf u.label j).child ∧
        R.key a r = recKey V x (b0 Q) u.label.1.1 u.label.2 j ∧
        R.axis a V (b0 Q) (fun t => b0 (Qm t)) r =
          joinRecordAxis u.label.1.1 (axB0 V x (b0 Q) (fun t => b0 (Qm t))) u.label.2 j) ∨  -- r2 (3),(A)

      (((u.label.1.1 = .s0 ∧ j = 1) ∨ (u.label.1.1 = .s9 ∧ j = 2)) ∧
        joinRecordAxis u.label.1.1 (axB0 V x (b0 Q) (fun t => b0 (Qm t))) u.label.2 j = 1 ∧
        (traceRecOf u.label j).child = (traceRecOf u.label j).root)

  inline_records : ∀ V x ρ χ (Q : Fin C.width → F[X]) (h : RAP.SatisfiesWithPreprocessing (chip V x ρ χ)
      (fun j => Q (Fin.cast (chip_width V x ρ χ) j))) (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X]),
    (∀ s ∈ summands V x, ¬ s.mem (Q, Qm) χ) →
    ∀ u : NTree ((State × DTcomp Kfp) × ℕ), Nock.Walk.InTree (tree V x Q χ) u →
      ∀ j : ℕ, j < inlineRecords u.label.1.1 → j < Nock.Framework.recordCount u.label.1.1 →
      ∀ (W : ℕ) (rt : Noun),
        GlobalCarryRecognizer.enc (Z.seed χ) rt = (traceRecOf u.label j).root →
        rt.leaves ≤ W → FieldEmbedding.BoundedBy (ringChar Kfp) rt →
        (∀ p ∈ inlinePairs u.label.1.1 j rt, p.1.leaves ≤ W → p.2.leaves ≤ W →
          GlobalCarryRecognizer.SepSeed (Z.seed χ) p.1 p.2) →
        ∃ ch : Noun, Noun.slot (joinRecordAxis u.label.1.1 (axB0 V x (b0 Q) (fun t => b0 (Qm t)))
            u.label.2 j) rt = some ch ∧
          GlobalCarryRecognizer.enc (Z.seed χ) ch = (traceRecOf u.label j).child
  /-- The root row binds the claim (N4 + `root_bindings`): subject, formula and result. -/
  root_binds : ∀ V x ρ χ (Q : Fin C.width → F[X]) (h : RAP.SatisfiesWithPreprocessing (chip V x ρ χ)
      (fun j => Q (Fin.cast (chip_width V x ρ χ) j))) (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X]),
    (∀ s ∈ summands V x, ¬ s.mem (Q, Qm) χ) →                                -- r2 (1)
    SemanticStrategy.bindFP (Z.seed χ) V.claim.subject (tree V x Q χ).label.1.2.2.1.s ∧
    SemanticStrategy.bindFP (Z.seed χ) V.claim.formula (tree V x Q χ).label.1.2.2.1.f ∧
    SemanticStrategy.bindFP (Z.seed χ) V.claim.result (tree V x Q χ).label.1.2.2.1.e
  Honest : Type
  honestV : Honest → VerifierData F K hC S
  honestMsg0 : Honest → Msg0
  honestReq : Honest → Coins Φ K → Fin nAcc → Kio
  honestQ : Honest → Coins Φ K → Fin C.width → F[X]
  /-- `honestQ` is the instance's EXPLICIT construction (canonical completions, `rapcomp_canon`-style),
  never the package's `exactFamilyCompletion` choice. -/
  honest_staged : ∀ H, StagedCols Φ C.colRound (honestQ H)
  honestBad : Honest → List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))   -- r2 (H)
  honest_accepted : ∀ H χ (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X]),
    (∀ s ∈ honestBad H, ¬ s.mem (honestQ H χ, Qm) χ) →                                -- r2 (H)
    RAP.SatisfiesWithPreprocessing (chip (honestV H) (honestMsg0 H) (honestReq H χ) χ)
      (fun j => honestQ H χ (Fin.cast (chip_width _ _ _ _) j))

/-! ## Messages, acceptance, the generic statement (r2) -/

section Generic

attribute [local instance] Classical.propDecidable

variable {F K Kio Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  {Φ : CoinFrame} {hC : ℕ} {S : MemShape} {C : TableSpec} {nAcc : ℕ} {m : Fin nAcc → ℕ}
  {R : RecordView F K Kio Kfp Key C S hC m} {Z : SeedSpec Φ K Kfp} {I : IOCoinSpec Φ K Kio}

structure Messages (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
    (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I) where
  Qc : Coins Φ K → Fin C.width → F[X]
  Qm : Coins Φ K → ∀ t : Fin S.k, Fin (S.table t).width → F[X]
  msg0C : CF.Msg0
  msg0M : MF.Msg0
  requests : Coins Φ K → Fin nAcc → Kio
  msg2M : Coins Φ K → MF.Msg2

variable {CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I}
  {MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I}

/-- VCL-L export: `3N + P`. -/
def consumerBound (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
    (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I) (V : VerifierData F K hC S)
    (a : Fin nAcc) : ℕ :=
  CF.reqBound V a + MF.internalBound V a

def Messages.traces (msg : Messages CF MF) (χ : Coins Φ K) : Traces F C S := (msg.Qc χ, msg.Qm χ)

def Messages.Staged (msg : Messages CF MF) : Prop := TracesStaged Φ C S msg.traces

structure AcceptsV (V : VerifierData F K hC S) (msg : Messages CF MF) (χ : Coins Φ K) : Prop where
  compute : RAP.SatisfiesWithPreprocessing (CF.chip V msg.msg0C (msg.requests χ) χ)
    (fun j => msg.Qc χ (Fin.cast (CF.chip_width _ _ _ _) j))
  memory : ∀ t, RAP.SatisfiesWithPreprocessing (MF.chip V t msg.msg0M (msg.requests χ) (msg.msg2M χ) χ)
    (fun j => msg.Qm χ t (Fin.cast (MF.chip_width _ _ _ _ _ _) j))

/-- r2 (W): the window is a function of `(V, msg0M)` — the instance's field-run window joined with
the memory family's trace-free window bound. -/
def windowAt (leafBoundF : ℕ → ℕ → P8PublicClaim → ℕ) (V : VerifierData F K hC S)
    (msg : Messages CF MF) : ℕ :=
  max (leafBoundF (ringChar Kfp) V.N V.claim) (MF.windowBound V msg.msg0M)

/-- r2 (1): the summand list at `(V, msg0C, msg0M)`. -/
def allSummands (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0)
    (joint : VerifierData F K hC S → CF.Msg0 → MF.Msg0 →
      List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))) :
    List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S)) :=
  CF.summands V x ++ MF.summands V y ++ joint V x y

/-- **The L-C obligation, r2**: `CtxW` at the served oracle, the B0 axis oracle and the trace-free
window; the tree is `CF.tree` (its shape is B0). -/
def CtxWObligation [Fintype Kfp] [DecidableEq Kfp] [CharP Kfp (ringChar Kfp)]
    (joint : VerifierData F K hC S → CF.Msg0 → MF.Msg0 →
      List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S)))
    (leafBoundF : ℕ → ℕ → P8PublicClaim → ℕ) : Prop :=
  ∀ (V : VerifierData F K hC S) (msg : Messages CF MF) (χ : Coins Φ K), AcceptsV V msg χ →
    (∀ s ∈ allSummands (CF := CF) (MF := MF) V msg.msg0C msg.msg0M joint, ¬ s.mem (msg.traces χ) χ) →
    RootGoodFJoin.CtxW
      (sv := fun st k => MF.served V msg.msg0M (fun t => b0 (msg.Qm χ t))
        (CF.keyOf V msg.msg0C (b0 (msg.Qc χ)) st k))
      (ax := CF.axB0 V msg.msg0C (b0 (msg.Qc χ)) (fun t => b0 (msg.Qm χ t)))
      (Z.seed χ) (ringChar Kfp) (windowAt leafBoundF V msg)
      (CF.tree V msg.msg0C (msg.Qc χ) χ).size
      (CF.tree V msg.msg0C (msg.Qc χ) χ) V.claim.subject V.claim.formula

/-- **The generic standalone statement, r2**: `ε` is a function of `(V, msg0C, msg0M)`. -/
structure StandaloneThm54Statement (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
    (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
    (joint : VerifierData F K hC S → CF.Msg0 → MF.Msg0 →
      List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))) : Prop where
  soundness : ∀ (V : VerifierData F K hC S), V.Checks (consumerBound CF MF V) (ringChar Kio) →
    ∀ msg : Messages CF MF, msg.Staged →
    ((Finset.univ.filter fun χ : Coins Φ K =>
        AcceptsV V msg χ ∧ ¬ HoldsF (ringChar K) V.claim).card : ℚ) /
        Fintype.card (Coins Φ K) ≤
      epsilonOf (allSummands (CF := CF) (MF := MF) V msg.msg0C msg.msg0M joint)
  /-- r2 (H): completeness is the union bound over the two honest summand lists at the honest
  traces (`FibreBound.union_prob_le` at the staged honest strategy). -/
  completeness : ∀ (HC : CF.Honest) (HM : MF.Honest), CF.honestV HC = MF.honestV HM →
    CF.honestReq HC = MF.honestReq HM →
    ((Finset.univ.filter fun χ : Coins Φ K =>
        ∃ s ∈ CF.honestBad HC ++ MF.honestBad HM,
          s.mem (CF.honestQ HC χ, MF.honestQ HM χ) χ).card : ℚ) /
        Fintype.card (Coins Φ K) ≤
      epsilonOf (CF.honestBad HC ++ MF.honestBad HM)

/-- The fixed-trace corollary shape (`fixed_of_staged` at a frame): a constant strategy is staged
(kept from r1). -/
theorem tracesStaged_const (q : Traces F C S) : TracesStaged Φ C S (K := K) (fun _ => q) :=
  ⟨stagedCols_const Φ _ _, fun _ => stagedCols_const Φ _ _⟩

end Generic

/-! ## 10. The current chip as the walk instance: the shape, the record view, the frame -/

section Current

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] [Fintype F]

/-- The current record key: `(state, exponent)` read off a width-10 record. -/
abbrev KeyWalk := MState × ℕ

/-- The twelve-coin vector's NPR seed (slot 3 of `landedVec12`). -/
def seed12 (χ : Coins frame12 K) : K := χ ⟨3, by decide⟩

/-- The tower seed on `frame13` (T0): `z₁ + z₂ √δ`, to be `Quad.mk (χ 3) (χ 12)`; the field `Quad K`
is T0's.  Stated here at the pair, `K × K`, as the frame's view. -/
def seed13pair (χ : Coins frame13 K) : K × K := (χ ⟨3, by decide⟩, χ ⟨12, by decide⟩)

/-- `StandaloneVerifierData.VerifierData` (one memory table) is the `shapeWalk` verifier datum at
equal heights. -/
def verifierDataOfCurrent {h : ℕ} (V : StandaloneVerifier.VerifierData F K h) :
    VerifierData F K h (shapeWalk h) where
  claim := V.claim
  N := V.N
  hN := V.hN
  Ksz := V.Ksz
  basis := V.basis
  orbitC := V.orbit
  computeNodes := V.computeNodes
  memRows := fun _ => V.M
  hM := fun _ => V.hM
  orbitM := fun _ => V.orbit
  memNodes := fun _ => V.memoryNodes

/-- The twelve-coin tuple of a `frame12` vector (the existing `tuple12OfVec`). -/
def tupleOf12 (χ : Coins frame12 K) : PartA12.OptimizedProductionChallengeTuple12 K F :=
  PartA12.tuple12OfVec χ

/-- `frame12`'s IO coins (`ioSpec12`) are the tuple's `c.2.1` (the memory slots `4`/`5`,
`memIOFacts12`'s coins). -/
theorem ioCoins12 (χ : Coins frame12 K) :
    (ioSpec12 K).ioCoins χ = (⟨(tupleOf12 (F := F) χ).2.1.1, (tupleOf12 (F := F) χ).2.1.2⟩ :
      FiniteIO.IOCoins K) := rfl

/-- The current memory chip at a `frame12` vector, through `currentMemFamily` (the chip field of
the walk instance: `memoryChipAt12` at `pubMCurrent`). -/
def chipWalk {h : ℕ} [FiniteDimensional F K] (V : StandaloneVerifier.VerifierData F K h)
    (rest : ℕ → F) (req seed : K) (χ : Coins frame12 K) : FixedPreprocessingRAP F :=
  (StandaloneVerifier.currentMemFamily (F := F) (K := K) h).chip V rest req seed (tupleOf12 χ)

theorem chipWalk_width {h : ℕ} [FiniteDimensional F K] (V : StandaloneVerifier.VerifierData F K h)
    (rest : ℕ → F) (req seed : K) (χ : Coins frame12 K) :
    (chipWalk V rest req seed χ).rap.w = (table205 h).width :=
  (StandaloneVerifier.currentMemFamily (F := F) (K := K) h).chip_width V rest req seed (tupleOf12 χ)

/-- The walk instance's `reqCond`: the mechanism is `IO.LIO` (a permutation), so the compute
requests must be `Nodup` and in the IO window — exactly `lio_of_common_requests`'s `hreqnd`
(timestamps) and `hKreq`.  This is the ONLY place timestamps touch the interface. -/
def reqCondWalk (Ksz : ℕ) (reqs : ∀ _ : Fin 1, List (Fin 10 → K)) (_ : Coins frame12 K) : Prop :=
  (reqs 0).Nodup ∧ IO.InRange Ksz (reqs 0).length


def reqCondVCL {Kv Kio : Type} {m : Fin 3 → ℕ} (_ : ∀ a : Fin 3, List (Fin (m a) → Kio))
    (_ : Coins frameVCL Kv) : Prop := True

end Current

end

end Nock.NockVMROM.Thm54.SVFrame
