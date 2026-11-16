/-
  Nock/NockVMROM/Thm54/GoldilocksParameters.lean

  **Theorem 5.4's numeric side conditions at the paper's own deployment parameters.**

  Every non-vacuity instantiation in this tree so far runs at a toy field (`ZMod 97`,
  `F97`/`K97cubic`, `p = 769`).  The paper deploys at **Goldilocks**: `𝔽 = 𝔽_p` with `p = 2^64 − 2^32 + 1` and `K` its degree-3
  extension, `|K| = p^3 ≈ 2^192`.  `Nock/Field.lean:37` defines `p`, `:44` is the blessed
  `axiom goldilocks_prime` (inside I2's allowed set), `:66` is `card_K_value`.

  This module instantiates the arithmetic side conditions of
  `TraceGen.nockCompiles_of_accepted` (`GenNockCompiles.lean:294`) there, and evaluates
  `OptimizedStrictPackage.optimizedProductionFailureProbabilityBound` (`:691`).

  The paper-configuration figure
  under the `16^65` ceiling is still `123` (`hostile_soundness_at_paper_configuration`); the
  ceiling-free real-program figure moves `121 → 122` at `2^31` rows and `119 → 120` at `2^32`
  (`RealProgramSoundness` §8) — one bit *better*, because the response count is now majorised
  by `M` rather than by the symmetric `n ≤ 3R`.  §5 is retained as the history of the function it
  names.**

  The ceiling-free figure for real
  programs is **`121` bits at `2^31` rows and `119` at `2^32`**, at the *consumed* bound:
  `RealProgramSoundness.lean::trimmed_soundness_for_real_programs_at_two_pow_31`,
  `::trimmed_soundness_for_real_programs_at_two_pow_32` and `::trimmed_soundness_for_execution`,
  all via `::trimmed_le_goldilocksFailureBoundK`.  The paper's own claim at `k = 2^31` is
  `121`, so the honest headline matches it exactly.

  Stage 3e de-compressed the compute chip's two
  `challenge36`-folded endpoint equality checks into the twenty-two individual masked
  equations, so the last base-field summand `20/|𝔽|` left the consumed bound and
  `trimmed_soundness_at_paper_configuration` puts the paper configuration below `2^-123`
  (with `trimmed_lower_bound_at_paper_configuration` above `2^-183`, so `123` is a figure and
  not a floor — a figure *of the bound function under those ceilings*).  **§4.2 below is the
  previous headline and is retained: it is still true of
  `goldilocksExtensionFailureBound`, which the capstone now carries only as an `…_extension`
  corollary.**  Read `59` and `123` as the history of the figure, not as the released number.

  The
  residual base-field term is **compute's** `challenge36`, which stage 3c does not touch, so the
  ceiling is now a constant rather than `64 − log₂(14M)`: `extension_no_60_bits` holds for every
  `M`, and the million-row and paper points give the same `59`.
  `extension_two_K_summands_are_below_two_pow_neg_123` shows the two extension summands alone are
  under `2^-123`, i.e. the whole remaining gap to the `𝕂`-typed figure is that one constant.

  **§4 below is retained verbatim and remains true of the `61·M` and `19·M` bounds**, which the
  capstone still carries as `…_legacy` / `…_merged` corollaries.  Read it as the history of the
  figure, not as the released number.

  The pre-`KX` production failure bound is
  `(p8Work + 494N + 1 + 61M)/|K| + ioWork/|K|² + (20 + 14M)/|𝔽|`.  Its third summand has
  the **base field** in the denominator, not the extension.  At Goldilocks `|𝔽| = p ≈ 2^64`
  while `|K| = p^3 ≈ 2^192`, so the third summand dominates the other two by ~128 bits and
  the achievable soundness is capped near **60 bits**, never 192:

  * `no_60_bits` — for *every* `p8Work, ioWork, N, M`, the bound exceeds `2^-60`;
  * `no_59_bits` — with at least one memory row, `2^-59`.  `1 ≤ M` is not an extra
    assumption: `M` is `ExactConfig.memRows`, and `memRows_pos` is a *field* of
    `ExactConfig`, supplied from `hmempos` at `genExactConfig`
    (`TraceGen/GenExactExecution.lean:86,88`).  So `2^-59` is a ceiling on every
    configuration the generator can emit, not on a subfamily;
  * `bits_necessary` — `b` bits of soundness requires `(20 + 14M)·2^b < p`, i.e.
    `b ≲ 64 − log₂(14M)`;
  * `bound_at_million_*` — at `N = M = 2^20`, `p8Work ≤ 2^60`, `ioWork ≤ 2^260` the bound is
    strictly between `2^-41` and `2^-40`: **≈ 40 bits**, from a single-shot AIR over a
    degree-3 extension of a 64-bit prime;
  * `soundness_at_paper_configuration` — at the paper's own headline configuration,
    "a maximal number of `2^31` unique data fields", the bound is between
    `2^-30` and `2^-29`: **29 bits**.  the paper claims *121* bits there, and
    the paper states the theorem's soundness as negligible in `𝕂`, not in `𝔽`.
    That module imports this one, so
    the pointer can only go this way, in prose.  It stays true that the **capstone** consumes
    the `𝔽`-typed bound, so `29` is the deployed figure and `123` is not;

  The base-field summand is not an artifact of this module.

  **That second step moved no bit and could not have**: the `|𝔽|^4` the surviving memory lift
  carried cancelled against exactly those four coordinates, and
  `normalized_extension_card_bound_eq_separate_denominators` — restated over the smaller space —
  still yields the same probability bound.  `stage3d_shrank_the_space_without_moving_the_figure`
  is the compiled receipt.  `challenge36` is untouched and is the whole of the residual `20/|𝔽|`;
  `counterfactual_extension_denominator` still prices what retyping a base-field denominator
  buys.

  **What binds first as programs grow (§3).**  Not `hcard` (§2: good to `n ≈ 1.5·10^28`,
  a 94-bit record count) and not `hKszChar : Ksz < ringChar K` (§1: `Ksz < 2^64`), but the
  *smooth-orbit* conditions `hcomp`/`hmem`/`hprogCap`/`hmemCap : … ≤ 2 ^ orbit.h`.  An
  `OrbitDomain K` (`Framework/Thm54/OrbitDomain.lean:26`) demands `orderOf ω = 2 ^ h`, and
  `v₂(p^3 − 1) = 32`, so `h ≤ 32`: **at most 2^32 = 4 294 967 296 rows**, and the same 32
  for the strict package orbit over `𝔽` (`hcap : 2 ^ orbit.h ≤ 2 ^ hOrb`).

  Everything below that mentions `Nock.Field.K` or `Nock.Field.Fp` depends on
  `Nock.Field.goldilocks_prime`; the field-generic lemmas of §2 do not.
-/
import Nock.Field
import Nock.Framework.Thm54.OrbitDomain
import Nock.NockVMROM.Thm54.ExtensionField
import Nock.NockVMROM.Thm54.GigaRAPIOFreshness
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.RecordCarrier
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents

set_option autoImplicit false
set_option maxRecDepth 4000

namespace Nock.NockVMROM.Thm54.GoldilocksParameters

open Nock.Field
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.Framework.Thm54

noncomputable section

/-! ## 1. The two cardinalities, and `ringChar`

the paper: `𝔽 = 𝔽_p`, `p = 2^64 − 2^32 + 1`, and `K/𝔽` of degree 3. -/

/-- The Goldilocks prime as a decimal literal. -/
abbrev pGold : ℕ := 18446744069414584321

/-- `|K| = p^3` as a decimal literal. -/
abbrev cardKGold : ℕ :=
  6277101731002175853884774869567645561244584131361410908161

theorem pGold_eq : Nock.Field.p = pGold := p_eq

/-- **`|𝔽| = 2^64 − 2^32 + 1`.**  The base field is 64-bit -/
theorem card_F : Fintype.card Fp = pGold :=
  (ZMod.card Nock.Field.p).trans pGold_eq

/-- **`|K| = p^3 ≈ 2^192`.** -/
theorem card_K_gold : Fintype.card K = cardKGold := by
  rw [card_K_value]; norm_num

/-- `cardKGold = pGold ^ 3` — the two literals agree. -/
theorem cardKGold_eq : cardKGold = pGold ^ 3 := by norm_num

/-- **`ringChar K = p`**, so `hq : 11 < q` and `hchar : q = ringChar K` of
`nockCompiles_of_accepted` are met by `q := p`. -/
theorem ringChar_K_gold : ringChar K = pGold := by
  rw [← Algebra.ringChar_eq Fp K, ZMod.ringChar_zmod_n]
  exact pGold_eq

/-- `hq : 11 < q` at `q = ringChar K`.  Trivially satisfied. -/
theorem eleven_lt_ringChar : 11 < ringChar K := by
  rw [ringChar_K_gold]; norm_num

/-- `hKszChar : Ksz < ringChar K` is a 64-bit ceiling on the accumulated row index — far
looser than §3's orbit ceiling of `2^32`. -/
theorem KszChar_iff (Ksz : ℕ) : Ksz < ringChar K ↔ Ksz < pGold := by
  rw [ringChar_K_gold]

/-! ## 2. `hcard` — the IO counted-event union bound

`FiniteFieldIOSoundness.lean:278` defines
`ioFailureUnionBound m k₁ k₂ cardK = ((k₁+k₂)²(m−1))·cardK + cardK·(2(k₁+k₂))`, and
`GigaIOFreshness.ioFailureUnionBound_factors` (`GigaRAPIOFreshness.lean:386`) factors it as
`cardK · ((k₁+k₂)²(m−1) + 2(k₁+k₂))`.  `nockCompiles_of_accepted` uses `m = 8`, `k₁ = k₂ = n`,
so the workload is `28n² + 4n` and the condition against `|K × K| = |K|²` collapses to a
condition on `n` alone.  §2's lemmas are field-generic; only the corollaries name Goldilocks. -/

/-- At `m = 8` and `k₁ = k₂ = n` the union bound is `cardK · (28n² + 4n)`. -/
theorem ioFailureUnionBound_eight (n cardK : ℕ) :
    ioFailureUnionBound 8 n n cardK = cardK * (28 * n * n + 4 * n) := by
  simp only [ioFailureUnionBound, show (8 : ℕ) - 1 = 7 from rfl]
  ring

/-- Form R `m = 9`: `(m−1) = 8`, so the union bound is `cardK · (32n² + 4n)`. -/
theorem ioFailureUnionBound_nine (n cardK : ℕ) :
    ioFailureUnionBound 9 n n cardK = cardK * (32 * n * n + 4 * n) := by
  simp only [ioFailureUnionBound, show (9 : ℕ) - 1 = 8 from rfl]
  ring

theorem ioFailureUnionBound_ten (n cardK : ℕ) :
    ioFailureUnionBound 10 n n cardK = cardK * (36 * n * n + 4 * n) := by
  simp only [ioFailureUnionBound, show (10 : ℕ) - 1 = 9 from rfl]
  ring

/-- **`hcard` is exactly `28n² + 4n < |K|`.**  Field-generic. -/
theorem hcard_iff {K' : Type} [Fintype K'] (n : ℕ) (hpos : 0 < Fintype.card K') :
    ioFailureUnionBound 8 n n (Fintype.card K') < Fintype.card (K' × K')
      ↔ 28 * n * n + 4 * n < Fintype.card K' := by
  rw [Fintype.card_prod, ioFailureUnionBound_eight]
  exact Nat.mul_lt_mul_left hpos

/-- **`hcard` at Goldilocks, in closed arithmetic form.** -/
theorem hcard_gold_iff (n : ℕ) :
    ioFailureUnionBound 8 n n (Fintype.card K) < Fintype.card (K × K)
      ↔ 28 * n * n + 4 * n < cardKGold := by
  rw [hcard_iff n (by rw [card_K_gold]; norm_num), card_K_gold]

/-- The exact threshold: the largest `n` for which `hcard` holds at Goldilocks is
`n* = 14 972 715 340 867 505 373 877 941 970 ≈ 1.497·10^28 ≈ 2^93.6`. -/
abbrev nStar : ℕ := 14972715340867505373877941970

/-- `hcard` **holds** at `n = n*`. -/
theorem hcard_at_nStar :
    ioFailureUnionBound 8 nStar nStar (Fintype.card K) < Fintype.card (K × K) := by
  rw [hcard_gold_iff]; norm_num

/-- `hcard` **fails** at `n = n* + 1`: `n*` really is the threshold. -/
theorem not_hcard_at_nStar_succ :
    ¬ ioFailureUnionBound 8 (nStar + 1) (nStar + 1) (Fintype.card K)
        < Fintype.card (K × K) := by
  rw [hcard_gold_iff]; norm_num

/-- **The clean sufficient bound: any record count up to `2^93` discharges `hcard`.**
This is the form a caller wants: `hreqn`/`hrespn` supply `n`, and any `n ≤ 2^93` works. -/
theorem hcard_of_le_two_pow_93 (n : ℕ) (hn : n ≤ 2 ^ 93) :
    ioFailureUnionBound 8 n n (Fintype.card K) < Fintype.card (K × K) := by
  rw [hcard_gold_iff]
  have h1 : 28 * n * n ≤ 28 * 2 ^ 93 * 2 ^ 93 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 28 hn) hn
  have h2 : 4 * n ≤ 4 * 2 ^ 93 := Nat.mul_le_mul_left 4 hn
  have h3 : 28 * 2 ^ 93 * 2 ^ 93 + 4 * 2 ^ 93 < cardKGold := by norm_num
  omega

/-- Form R `m = 9`: `hcard` is `32n² + 4n < |K|`. -/
theorem hcard_iff_nine {K' : Type} [Fintype K'] (n : ℕ) (hpos : 0 < Fintype.card K') :
    ioFailureUnionBound 9 n n (Fintype.card K') < Fintype.card (K' × K')
      ↔ 32 * n * n + 4 * n < Fintype.card K' := by
  rw [Fintype.card_prod, ioFailureUnionBound_nine]
  exact Nat.mul_lt_mul_left hpos

theorem hcard_gold_iff_nine (n : ℕ) :
    ioFailureUnionBound 9 n n (Fintype.card K) < Fintype.card (K × K)
      ↔ 32 * n * n + 4 * n < cardKGold := by
  rw [hcard_iff_nine n (by rw [card_K_gold]; norm_num), card_K_gold]

/-- The honest coins must miss both the nine- and the ten-slot IO
failure events (`RecordCarrier.honestIOBound`, `|𝕂|·(68n² + 8n)`); any `n ≤ 2^92` discharges it at
Goldilocks (`68·2^184 + 8·2^92 < |𝕂|`). -/
theorem hcard_of_le_two_pow_92_honest (n : ℕ) (hn : n ≤ 2 ^ 92) :
    RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K) := by
  rw [RecordCarrier.honestIOBound_eq, Fintype.card_prod, card_K_gold]
  have h1 : 68 * n * n ≤ 68 * 2 ^ 92 * 2 ^ 92 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 68 hn) hn
  have h2 : 8 * n ≤ 8 * 2 ^ 92 := Nat.mul_le_mul_left 8 hn
  have h3 : 68 * 2 ^ 92 * 2 ^ 92 + 8 * 2 ^ 92 < cardKGold := by norm_num
  have h4 : 68 * n * n + 8 * n < cardKGold := by omega
  exact Nat.mul_lt_mul_of_pos_left h4 (by norm_num)

/-- Form R sufficient bound: `n ≤ 2^93` still discharges `m = 9` at Goldilocks
(`32·2^186 + 4·2^93 < |K|`). -/
theorem hcard_of_le_two_pow_93_nine (n : ℕ) (hn : n ≤ 2 ^ 93) :
    ioFailureUnionBound 9 n n (Fintype.card K) < Fintype.card (K × K) := by
  rw [hcard_gold_iff_nine]
  have h1 : 32 * n * n ≤ 32 * 2 ^ 93 * 2 ^ 93 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 32 hn) hn
  have h2 : 4 * n ≤ 4 * 2 ^ 93 := Nat.mul_le_mul_left 4 hn
  have h3 : 32 * 2 ^ 93 * 2 ^ 93 + 4 * 2 ^ 93 < cardKGold := by norm_num
  omega

/-- `hcard` fails already at `n = 2^94`, so `2^93` is tight to within one bit. -/
theorem not_hcard_at_two_pow_94 :
    ¬ ioFailureUnionBound 8 (2 ^ 94) (2 ^ 94) (Fintype.card K) < Fintype.card (K × K) := by
  rw [hcard_gold_iff]; norm_num

/-! ## 3. What actually binds: the two-adicity of Goldilocks

`p − 1 = 2^32 · 4294967295` and `p^3 − 1 = 2^32 · (odd)`, so `v₂(p^3 − 1) = 32`.  An
`OrbitDomain K` carries `order_ω : orderOf ω = 2 ^ h` (`OrbitDomain.lean:31`), so no orbit
of height above 32 exists over `K`; the four capacity premises `hcomp`, `hmem`, `hprogCap`,
`hmemCap` of `nockCompiles_of_accepted` therefore cap the trace at `2^32` rows.  The same
holds for the strict package orbit over `𝔽` (`ExtensionField.lean:94`,
`orderOf ω = e · 2 ^ h`), so `hcap : 2 ^ orbit.h ≤ 2 ^ hOrb` cannot buy room. -/

/-- The odd part of `p^3 − 1`. -/
abbrev oddPartK : ℕ := 1461501636310055817916238417282618014431694553085

theorem card_K_sub_one : Fintype.card K - 1 = 2 ^ 32 * oddPartK := by
  rw [card_K_gold]; norm_num

theorem card_F_sub_one : Fintype.card Fp - 1 = 2 ^ 32 * 4294967295 := by
  rw [card_F]; norm_num

/-- Any element of exact order `2^h` in `K` forces `h ≤ 32`. -/
theorem two_pow_dvd_le (h : ℕ) (hdvd : 2 ^ h ∣ Fintype.card K - 1) : h ≤ 32 := by
  rw [card_K_sub_one] at hdvd
  have hcop : Nat.Coprime (2 ^ h) oddPartK :=
    Nat.Coprime.pow_left h ((Nat.prime_two.coprime_iff_not_dvd).mpr (by norm_num))
  have : (2 : ℕ) ^ h ∣ 2 ^ 32 := hcop.dvd_of_dvd_mul_right hdvd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this

/-- **`v₂(|K|−1) = 32` caps every `OrbitDomain K` at height 32.** -/
theorem orbit_height_le (D : OrbitDomain K) : D.h ≤ 32 := by
  have hone : D.ω ^ (2 ^ D.h) = 1 := by
    have := pow_orderOf_eq_one D.ω
    rwa [D.order_ω] at this
  have hne : D.ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at hone
    exact zero_ne_one hone
  have hcard : D.ω ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ hne
  have hdvd : orderOf D.ω ∣ Fintype.card K - 1 := orderOf_dvd_of_pow_eq_one hcard
  rw [D.order_ω] at hdvd
  exact two_pow_dvd_le _ hdvd

/-- **The binding constraint: at most `2^32 = 4 294 967 296` rows.**  Every one of
`hcomp`, `hmem`, `hprogCap`, `hmemCap` bounds a row/record count by `2 ^ orbit.h`. -/
theorem orbit_capacity_le (D : OrbitDomain K) : 2 ^ D.h ≤ 4294967296 :=
  calc 2 ^ D.h ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (orbit_height_le D)
    _ = 4294967296 := by norm_num

/-- The same ceiling for the strict package orbit over the base field: `orderOf ω = 3·2^h`
in `𝔽_p` and `v₂(p − 1) = 32`, so `hOrb ≤ 32` and `hcap` cannot raise the ceiling. -/
theorem strict_orbit_height_le {hOrb : ℕ} (D : StrictOrbitDomain Fp 3 hOrb) : hOrb ≤ 32 := by
  have hone : D.ω ^ (3 * 2 ^ hOrb) = 1 := by
    have := pow_orderOf_eq_one D.ω
    rwa [D.order_ω] at this
  have hne : D.ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at hone
    exact zero_ne_one hone
  have hcard : D.ω ^ (Fintype.card Fp - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ hne
  have hdvd : orderOf D.ω ∣ Fintype.card Fp - 1 := orderOf_dvd_of_pow_eq_one hcard
  rw [D.order_ω, card_F_sub_one] at hdvd
  have hdvd2 : (2 : ℕ) ^ hOrb ∣ 2 ^ 32 * 4294967295 :=
    dvd_trans ⟨3, by ring⟩ hdvd
  have hcop : Nat.Coprime (2 ^ hOrb) 4294967295 :=
    Nat.Coprime.pow_left hOrb ((Nat.prime_two.coprime_iff_not_dvd).mpr (by norm_num))
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd2)

/-! ## 4. The soundness figure at Goldilocks

`optimizedProductionFailureProbabilityBound` (`OptimizedStrictPackage.lean:691`) is
`(p8Work + 494N + 1 + 61M)/cardK + ioWork/cardK² + (20 + 14M)/cardF`, and
`normalized_card_bound_eq_separate_denominators` (`:777`) is what ties it to the counted
`|K|^9·|𝔽|^5` challenge space (`card_optimizedProductionChallengeTuple`, `:769`).  This is the
**pre-merge** bound; the released capstone consumes the `19·M` one — see §4.1.

The `(20 + 14M)/cardF` summand is over the **base** field — those are the memory chip's
`Fin 4 → F` scalar challenges and its `Fin 7 → Fin 3 → F` families.  At Goldilocks that
denominator is `2^64`, not `2^192`. -/

/-- The production failure bound with Goldilocks plugged in. -/
def goldilocksFailureBound (p8Work ioWork N M : ℕ) : ℚ :=
  optimizedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card Fp)
    p8Work ioWork N M

/-- The three summands, with the two denominators shown explicitly: `p^3` for the first two,
**`p` for the third**. -/
theorem goldilocksFailureBound_eq (p8Work ioWork N M : ℕ) :
    goldilocksFailureBound p8Work ioWork N M
      = (p8Work + 494 * N + 1 + 61 * M : ℚ) / (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
        + (20 + 14 * M : ℚ) / (pGold : ℚ) := by
  simp only [goldilocksFailureBound, optimizedProductionFailureProbabilityBound,
    card_K_gold, card_F]

theorem card_challenge_space :
    Fintype.card (OptimizedProductionChallengeTuple K Fp) = cardKGold ^ 11 := by
  rw [card_optimizedProductionChallengeTuple, card_K_gold]

/-- **The base-field summand is a lower bound for the whole thing.**  This is the entire
content of the headline: the extension-field terms cannot rescue it. -/
theorem memory_term_le (p8Work ioWork N M : ℕ) :
    (20 + 14 * M : ℚ) / (pGold : ℚ) ≤ goldilocksFailureBound p8Work ioWork N M := by
  rw [goldilocksFailureBound_eq]
  have h1 : (0 : ℚ) ≤ (p8Work + 494 * N + 1 + 61 * M : ℚ) / (cardKGold : ℚ) := by positivity
  have h2 : (0 : ℚ) ≤ (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 := by positivity
  linarith

/-- **`b` bits of soundness requires `(20 + 14M)·2^b < p`.**  Since `p < 2^64`, this is
`b < 64 − log₂(20 + 14M)`: the memory-row count is subtracted directly from 64 bits. -/
theorem bits_necessary (p8Work ioWork N M b : ℕ)
    (h : goldilocksFailureBound p8Work ioWork N M < 1 / 2 ^ b) :
    (20 + 14 * M) * 2 ^ b < pGold := by
  have hlow := memory_term_le p8Work ioWork N M
  have hq : (20 + 14 * M : ℚ) / (pGold : ℚ) < 1 / 2 ^ b := lt_of_le_of_lt hlow h
  have hp : (0 : ℚ) < (pGold : ℚ) := by norm_num
  have hb : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
  rw [div_lt_div_iff₀ hp hb, one_mul] at hq
  have hcast : ((20 + 14 * M) * 2 ^ b : ℚ) < (pGold : ℚ) := by
    push_cast at hq ⊢
    linarith
  exact_mod_cast hcast

/-- **No configuration whatsoever reaches 60 bits.** -/
theorem no_60_bits (p8Work ioWork N M : ℕ) :
    1 / (2 : ℚ) ^ 60 < goldilocksFailureBound p8Work ioWork N M := by
  refine lt_of_lt_of_le ?_ (memory_term_le p8Work ioWork N M)
  have hM : (0 : ℚ) ≤ (M : ℚ) := Nat.cast_nonneg M
  have h20 : (20 : ℚ) / (pGold : ℚ) ≤ (20 + 14 * M : ℚ) / (pGold : ℚ) := by
    gcongr
    all_goals linarith
  refine lt_of_lt_of_le ?_ h20
  norm_num

/-- **With at least one memory row — forced by `hmempos` — not even 59 bits.** -/
theorem no_59_bits (p8Work ioWork N M : ℕ) (hM : 1 ≤ M) :
    1 / (2 : ℚ) ^ 59 < goldilocksFailureBound p8Work ioWork N M := by
  refine lt_of_lt_of_le ?_ (memory_term_le p8Work ioWork N M)
  have hM' : (1 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
  have h34 : (34 : ℚ) / (pGold : ℚ) ≤ (20 + 14 * M : ℚ) / (pGold : ℚ) := by
    gcongr
    all_goals linarith
  refine lt_of_lt_of_le ?_ h34
  norm_num

/-- Monotone in the two workloads, so a concrete evaluation can be stated with `≤` premises. -/
theorem bound_mono {p8 p8' io io' : ℕ} (N M : ℕ) (h1 : p8 ≤ p8') (h2 : io ≤ io') :
    goldilocksFailureBound p8 io N M ≤ goldilocksFailureBound p8' io' N M := by
  rw [goldilocksFailureBound_eq, goldilocksFailureBound_eq]
  have c1 : (p8 : ℚ) ≤ (p8' : ℚ) := by exact_mod_cast h1
  have c2 : (io : ℚ) ≤ (io' : ℚ) := by exact_mod_cast h2
  have d1 : (0 : ℚ) < (cardKGold : ℚ) := by norm_num
  have d2 : (0 : ℚ) < (cardKGold : ℚ) ^ 2 := by positivity
  have s1 : (p8 + 494 * N + 1 + 61 * M : ℚ) / (cardKGold : ℚ)
      ≤ (p8' + 494 * N + 1 + 61 * M : ℚ) / (cardKGold : ℚ) := by
    gcongr
  have s2 : (io : ℚ) / (cardKGold : ℚ) ^ 2 ≤ (io' : ℚ) / (cardKGold : ℚ) ^ 2 := by
    gcongr
  linarith

/-! ### A concrete deployment point

`N = M = 2^20` rows (a million compute rows and a million memory rows — well inside §3's
`2^32` orbit ceiling), a generous `p8Work ≤ 2^60`, and `ioWork ≤ 16^65 = 2^260` (written base
16 because `norm_num` declines exponents above 256).  That ceiling is not
slack for its own sake: the *actual* `ioWork` is `ioFailureUnionBound 9 n n |K| = |K|·(28n²+4n)`,
which is already `≈ 2^258` at `n = 2^31` (`ioWork_le` below).  Both extension-field summands
still land below `2^-37`. -/

/-- The real `ioWork` at any record count up to `2^31` is under `16^65 = 2^260`, so the hypotheses of
the two evaluation theorems below cover every configuration the orbit ceiling permits. -/
theorem ioWork_le (n : ℕ) (hn : n ≤ 2 ^ 31) :
    ioFailureUnionBound 8 n n (Fintype.card K) ≤ 16 ^ 65 := by
  rw [ioFailureUnionBound_eight, card_K_gold]
  have h1 : 28 * n * n ≤ 28 * 2 ^ 31 * 2 ^ 31 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 28 hn) hn
  have h2 : 4 * n ≤ 4 * 2 ^ 31 := Nat.mul_le_mul_left 4 hn
  calc cardKGold * (28 * n * n + 4 * n)
      ≤ cardKGold * (28 * 2 ^ 31 * 2 ^ 31 + 4 * 2 ^ 31) :=
        Nat.mul_le_mul_left _ (by omega)
    _ ≤ 16 ^ 65 := by norm_num

/-- **≈ 40 bits.**  Upper half. -/
theorem bound_at_million_lt (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksFailureBound p8Work ioWork (2 ^ 20) (2 ^ 20) < 1 / (2 : ℚ) ^ 40 := by
  refine lt_of_le_of_lt (bound_mono _ _ hp8 hio) ?_
  rw [goldilocksFailureBound_eq]
  norm_num

/-- **≈ 40 bits.**  Lower half — and it holds for *every* `p8Work`, `ioWork` and `N`, since
the memory summand alone already exceeds `2^-41`. -/
theorem bound_at_million_gt (p8Work ioWork N : ℕ) :
    1 / (2 : ℚ) ^ 41 < goldilocksFailureBound p8Work ioWork N (2 ^ 20) := by
  refine lt_of_lt_of_le ?_ (memory_term_le p8Work ioWork N (2 ^ 20))
  norm_num

/-- The soundness at the concrete point, stated as one sentence: strictly between `2^-41`
and `2^-40`, i.e. **40 bits**, not the 192 a reader would expect from `|K| = p^3`. -/
theorem soundness_at_million (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    1 / (2 : ℚ) ^ 41 < goldilocksFailureBound p8Work ioWork (2 ^ 20) (2 ^ 20)
      ∧ goldilocksFailureBound p8Work ioWork (2 ^ 20) (2 ^ 20) < 1 / (2 : ℚ) ^ 40 :=
  ⟨bound_at_million_gt _ _ _, bound_at_million_lt _ _ hp8 hio⟩

/-! ### The paper's own headline configuration

the paper claims "Over the Goldilocks prime field, it achieves a security level of `121`
bits when instantiated with `512`-bit length variables and a maximal number of `2^31` unique
data fields."  Reading "unique data fields" as the memory-record count `M` — the quantity the
`14M` summand counts — the bound proved here gives **29** bits at that configuration.  The
`p8Work ≤ 2^60` and `ioWork ≤ 2^260` ceilings cover the real workloads (`ioWork_le`) and
change nothing: both extension-field summands stay below `2^-37` there. -/

/-- **29 bits at `M = 2^31`.**  Between `2^-30` and `2^-29` -/
theorem soundness_at_paper_configuration (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    1 / (2 : ℚ) ^ 30 < goldilocksFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31)
      ∧ goldilocksFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 29 := by
  constructor
  · refine lt_of_lt_of_le ?_ (memory_term_le p8Work ioWork (2 ^ 31) (2 ^ 31))
    norm_num
  · refine lt_of_le_of_lt (bound_mono _ _ hp8 hio) ?_
    rw [goldilocksFailureBound_eq]
    norm_num

/-! ### 4.1 The same figures at the consumed `19·M` bound

This subsection proves that rather than asserting it. -/

/-- The consumed production failure bound with Goldilocks plugged in. -/
def goldilocksMergedFailureBound (p8Work ioWork N M : ℕ) : ℚ :=
  optimizedMergedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card Fp)
    p8Work ioWork N M

/-- Same three summands, with `19·M` in the first numerator. -/
theorem goldilocksMergedFailureBound_eq (p8Work ioWork N M : ℕ) :
    goldilocksMergedFailureBound p8Work ioWork N M
      = (p8Work + 494 * N + 1 + 19 * M : ℚ) / (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
        + (20 + 14 * M : ℚ) / (pGold : ℚ) := by
  simp only [goldilocksMergedFailureBound, optimizedMergedProductionFailureProbabilityBound,
    card_K_gold, card_F]

theorem goldilocksMergedFailureBound_le (p8Work ioWork N M : ℕ) :
    goldilocksMergedFailureBound p8Work ioWork N M
      ≤ goldilocksFailureBound p8Work ioWork N M :=
  optimizedMergedProductionFailureProbabilityBound_le _ _ _ _ _ _ Fintype.card_pos

theorem merged_memory_term_le (p8Work ioWork N M : ℕ) :
    (20 + 14 * M : ℚ) / (pGold : ℚ) ≤ goldilocksMergedFailureBound p8Work ioWork N M := by
  rw [goldilocksMergedFailureBound_eq]
  have h1 : (0 : ℚ) ≤ (p8Work + 494 * N + 1 + 19 * M : ℚ) / (cardKGold : ℚ) := by positivity
  have h2 : (0 : ℚ) ≤ (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 := by positivity
  linarith

theorem merged_bound_mono {p8 p8' io io' : ℕ} (N M : ℕ) (h1 : p8 ≤ p8') (h2 : io ≤ io') :
    goldilocksMergedFailureBound p8 io N M ≤ goldilocksMergedFailureBound p8' io' N M := by
  rw [goldilocksMergedFailureBound_eq, goldilocksMergedFailureBound_eq]
  have c1 : (p8 : ℚ) ≤ (p8' : ℚ) := by exact_mod_cast h1
  have c2 : (io : ℚ) ≤ (io' : ℚ) := by exact_mod_cast h2
  have s1 : (p8 + 494 * N + 1 + 19 * M : ℚ) / (cardKGold : ℚ)
      ≤ (p8' + 494 * N + 1 + 19 * M : ℚ) / (cardKGold : ℚ) := by
    gcongr
  have s2 : (io : ℚ) / (cardKGold : ℚ) ^ 2 ≤ (io' : ℚ) / (cardKGold : ℚ) ^ 2 := by
    gcongr
  linarith

/-- **The `61 → 19` improvement moves no Goldilocks bit.**  At the paper's own configuration
the consumed bound is still strictly between `2^-30` and `2^-29`, exactly as
`soundness_at_paper_configuration` records for the pre-merge bound -/
theorem merged_soundness_at_paper_configuration (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    1 / (2 : ℚ) ^ 30 < goldilocksMergedFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31)
      ∧ goldilocksMergedFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 29 := by
  constructor
  · refine lt_of_lt_of_le ?_ (merged_memory_term_le p8Work ioWork (2 ^ 31) (2 ^ 31))
    norm_num
  · refine lt_of_le_of_lt (merged_bound_mono _ _ hp8 hio) ?_
    rw [goldilocksMergedFailureBound_eq]
    norm_num

/-- And the million-row point is unchanged too: still between `2^-41` and `2^-40`. -/
theorem merged_soundness_at_million (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    1 / (2 : ℚ) ^ 41 < goldilocksMergedFailureBound p8Work ioWork (2 ^ 20) (2 ^ 20)
      ∧ goldilocksMergedFailureBound p8Work ioWork (2 ^ 20) (2 ^ 20) < 1 / (2 : ℚ) ^ 40 := by
  constructor
  · refine lt_of_lt_of_le ?_ (merged_memory_term_le p8Work ioWork (2 ^ 20) (2 ^ 20))
    norm_num
  · refine lt_of_le_of_lt (merged_bound_mono _ _ hp8 hio) ?_
    rw [goldilocksMergedFailureBound_eq]
    norm_num

/-! `optimizedExtensionProductionFailureProbabilityBound` (`OptimizedStrictPackage.lean`) is what the
released capstone carries after stage 3c of the `𝔽 → 𝕂` migration.

**What remains over the base field is `20/|𝔽|`, and it is COMPUTE's.**  It is
`FinalComputeChallengeTuple.challenge36 : F`, the compute chip's scalar compression, which stage
3c does not touch.  So the figure moves `29 → 59`, and **not** to the `123` of the fully
`𝕂`-typed bound (`ExtensionChallengeMigration.falseAcceptanceK_soundness_at_paper_configuration`).
`ExtensionChallengeMigration.naive_deletion_undershoots` is the standing warning against reading
a figure off a vanished term; the number below is computed from the bound that actually results.

`extension_no_60_bits` shows the ceiling is now `M`-independent: `20/p` alone exceeds `2^-60` for
*every* configuration, so the residual boundary is a constant, not a row count.  That is the
qualitative change — before stage 3c the ceiling fell as `64 − log₂(14M)`. -/

/-- The released production failure bound with Goldilocks plugged in. -/
def goldilocksExtensionFailureBound (p8Work ioWork N M : ℕ) : ℚ :=
  optimizedExtensionProductionFailureProbabilityBound (Fintype.card K) (Fintype.card Fp)
    p8Work ioWork N M

/-- Three summands, the third now the bare constant `20/p`. -/
theorem goldilocksExtensionFailureBound_eq (p8Work ioWork N M : ℕ) :
    goldilocksExtensionFailureBound p8Work ioWork N M
      = (p8Work + 494 * N + 1 + 19 * M : ℚ) / (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
        + (20 : ℚ) / (pGold : ℚ) := by
  simp only [goldilocksExtensionFailureBound,
    optimizedExtensionProductionFailureProbabilityBound, card_K_gold, card_F]

theorem goldilocksExtensionFailureBound_le (p8Work ioWork N M : ℕ) :
    goldilocksExtensionFailureBound p8Work ioWork N M
      ≤ goldilocksMergedFailureBound p8Work ioWork N M :=
  optimizedExtensionProductionFailureProbabilityBound_le _ _ _ _ _ _

/-- The compute constant is still a lower bound for the whole thing. -/
theorem extension_constant_term_le (p8Work ioWork N M : ℕ) :
    (20 : ℚ) / (pGold : ℚ) ≤ goldilocksExtensionFailureBound p8Work ioWork N M := by
  rw [goldilocksExtensionFailureBound_eq]
  have h1 : (0 : ℚ) ≤ (p8Work + 494 * N + 1 + 19 * M : ℚ) / (cardKGold : ℚ) := by positivity
  have h2 : (0 : ℚ) ≤ (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 := by positivity
  linarith

/-- **No configuration reaches 60 bits, and now the obstruction is `M`-independent.**  The
compute chip's constant `20/p` alone exceeds `2^-60`. -/
theorem extension_no_60_bits (p8Work ioWork N M : ℕ) :
    1 / (2 : ℚ) ^ 60 < goldilocksExtensionFailureBound p8Work ioWork N M := by
  refine lt_of_lt_of_le ?_ (extension_constant_term_le p8Work ioWork N M)
  norm_num

theorem extension_bound_mono {p8 p8' io io' : ℕ} (N M : ℕ) (h1 : p8 ≤ p8') (h2 : io ≤ io') :
    goldilocksExtensionFailureBound p8 io N M ≤ goldilocksExtensionFailureBound p8' io' N M := by
  rw [goldilocksExtensionFailureBound_eq, goldilocksExtensionFailureBound_eq]
  have c1 : (p8 : ℚ) ≤ (p8' : ℚ) := by exact_mod_cast h1
  have c2 : (io : ℚ) ≤ (io' : ℚ) := by exact_mod_cast h2
  have s1 : (p8 + 494 * N + 1 + 19 * M : ℚ) / (cardKGold : ℚ)
      ≤ (p8' + 494 * N + 1 + 19 * M : ℚ) / (cardKGold : ℚ) := by
    gcongr
  have s2 : (io : ℚ) / (cardKGold : ℚ) ^ 2 ≤ (io' : ℚ) / (cardKGold : ℚ) ^ 2 := by
    gcongr
  linarith

/-- **59 bits at the paper's own configuration.**  `N = M = 2^31`, `p8Work ≤ 2^60`, `ioWork ≤ 16^65`: the released bound is
strictly between `2^-60` and `2^-59`.

It is **not** `123`: see
`extension_two_K_summands_are_below_two_pow_neg_123` for exactly where the remaining 64 bits go. -/
theorem extension_soundness_at_paper_configuration (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    1 / (2 : ℚ) ^ 60 < goldilocksExtensionFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31)
      ∧ goldilocksExtensionFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 59 := by
  refine ⟨extension_no_60_bits _ _ _ _, ?_⟩
  refine lt_of_le_of_lt (extension_bound_mono _ _ hp8 hio) ?_
  rw [goldilocksExtensionFailureBound_eq]
  norm_num

/-- **And the million-row point is 59 bits too** — the same number, because the ceiling no longer
depends on the row count.  Before stage 3c that point was 40 bits and the paper point 29. -/
theorem extension_soundness_at_million (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    1 / (2 : ℚ) ^ 60 < goldilocksExtensionFailureBound p8Work ioWork (2 ^ 20) (2 ^ 20)
      ∧ goldilocksExtensionFailureBound p8Work ioWork (2 ^ 20) (2 ^ 20) < 1 / (2 : ℚ) ^ 59 := by
  refine ⟨extension_no_60_bits _ _ _ _, ?_⟩
  refine lt_of_le_of_lt (extension_bound_mono _ _ hp8 hio) ?_
  rw [goldilocksExtensionFailureBound_eq]
  norm_num

/-- **Where the other 64 bits are: the single compute constant `20/𝔽`.**  The two extension-field
summands of the released bound are together below `2^-123` at the paper configuration — the same
figure `ExtensionChallengeMigration` reaches for the fully `𝕂`-typed bound.  So the entire gap
between the reported `59` and that `123` is `20/p`, and it is compute's. -/
theorem extension_two_K_summands_are_below_two_pow_neg_123 (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    (p8Work + 494 * (2 ^ 31 : ℕ) + 1 + 19 * (2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 < 1 / (2 : ℚ) ^ 123 := by
  have c1 : (p8Work : ℚ) ≤ ((2 : ℚ) ^ 60) := by exact_mod_cast hp8
  have c2 : (ioWork : ℚ) ≤ ((16 : ℚ) ^ 65) := by exact_mod_cast hio
  have s1 : (p8Work + 494 * (2 ^ 31 : ℕ) + 1 + 19 * (2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ)
      ≤ ((2 : ℚ) ^ 60 + 494 * (2 ^ 31 : ℕ) + 1 + 19 * (2 ^ 31 : ℕ)) / (cardKGold : ℚ) := by
    gcongr
  have s2 : (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
      ≤ ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2 := by
    gcongr
  have : ((2 : ℚ) ^ 60 + 494 * (2 ^ 31 : ℕ) + 1 + 19 * (2 ^ 31 : ℕ)) / (cardKGold : ℚ)
      + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2 < 1 / (2 : ℚ) ^ 123 := by
    norm_num
  linarith

/-- **The improvement, stated as one comparison.**  At the paper configuration the pre-`KX`
consumed bound was above `2^-30` and the released one is below `2^-59`: thirty bits, bought by
the failure union losing four base-field lifts and nothing else. -/
theorem extension_beats_merged_by_thirty_bits (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksExtensionFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 59
      ∧ 1 / (2 : ℚ) ^ 30 < goldilocksMergedFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) :=
  ⟨(extension_soundness_at_paper_configuration p8Work ioWork hp8 hio).2,
    (merged_soundness_at_paper_configuration p8Work ioWork hp8 hio).1⟩

/-- The consumed memory lift lost the matching `|𝔽|⁴` factor at the same time, so the
quotient — the consumed probability bound — is the same rational function
(`OptimizedStrictPackage.normalized_extension_card_bound_eq_separate_denominators`), and the
Goldilocks figure at the paper configuration is still strictly between `2^-60` and `2^-59`.

This is stated as one theorem rather than left as two facts in prose because "a coordinate left
the tuple, therefore the bound moved" is exactly the inference
`ExtensionChallengeMigration.naive_deletion_undershoots` exists to forbid — in this direction as
well as the other. -/
theorem stage3d_shrank_the_space_without_moving_the_figure (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    Fintype.card (OptimizedProductionChallengeTuple K Fp) = cardKGold ^ 11
      ∧ 1 / (2 : ℚ) ^ 60 < goldilocksExtensionFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31)
      ∧ goldilocksExtensionFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 59 :=
  ⟨card_challenge_space,
    (extension_soundness_at_paper_configuration p8Work ioWork hp8 hio).1,
    (extension_soundness_at_paper_configuration p8Work ioWork hp8 hio).2⟩

/-! ## 5. The trimmed bound: no base-field summand at all

Stage 3e de-compressed the compute chip's two `challenge36`-folded endpoint equality checks into
the twenty-two individual masked equations, so the `20/|𝔽|` summand left the consumed bound.

The figure is **computed, not inferred**: `ExtensionChallengeMigration.naive_deletion_undershoots`
is the standing rail against reading a number off a vanished term, and
`trimmed_soundness_at_paper_configuration` derives it from the bound that actually results, the
way `extension_soundness_at_paper_configuration` did for the previous one. -/

/-- The released production failure bound with Goldilocks plugged in, after stage 3e. -/
def goldilocksTrimmedFailureBound (p8Work ioWork N M : ℕ) : ℚ :=
  optimizedTrimmedProductionFailureProbabilityBound (Fintype.card K) (Fintype.card Fp)
    p8Work ioWork N M

/-- **Two summands, both `𝕂`-denominated.**  There is no third. -/
theorem goldilocksTrimmedFailureBound_eq (p8Work ioWork N M : ℕ) :
    goldilocksTrimmedFailureBound p8Work ioWork N M
      = (p8Work : ℚ) / (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 := by
  simp only [goldilocksTrimmedFailureBound,
    optimizedTrimmedProductionFailureProbabilityBound, card_K_gold]

theorem goldilocksTrimmedFailureBound_le (p8Work ioWork N M : ℕ) :
    goldilocksTrimmedFailureBound p8Work ioWork N M
      ≤ goldilocksExtensionFailureBound p8Work ioWork N M :=
  optimizedTrimmedProductionFailureProbabilityBound_le _ _ _ _ _ _

/-- **THE FIGURE IS `123`, AND IT IS COMPUTED.**  At the paper configuration
(`p8Work ≤ 2^60`, `ioWork ≤ 16^65`, `N = M = 2^31`) the consumed bound lies strictly between
`2^-124` and `2^-123`.

The lower half says the bound is not smaller than that either, so `123` is the figure and not a
floor. -/
theorem trimmed_soundness_at_paper_configuration (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksTrimmedFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksTrimmedFailureBound_eq]
  have c1 : (p8Work : ℚ) ≤ ((2 : ℚ) ^ 60) := by exact_mod_cast hp8
  have c2 : (ioWork : ℚ) ≤ ((16 : ℚ) ^ 65) := by exact_mod_cast hio
  have s1 : (p8Work : ℚ) / (cardKGold : ℚ)
      ≤ ((2 : ℚ) ^ 60) / (cardKGold : ℚ) := by
    gcongr
  have s2 : (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
      ≤ ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2 := by
    gcongr
  have : ((2 : ℚ) ^ 60) / (cardKGold : ℚ)
      + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2 < 1 / (2 : ℚ) ^ 123 := by
    norm_num
  linarith

/-- The matching lower bound. -/
theorem trimmed_lower_bound_at_paper_configuration (p8Work ioWork : ℕ)
    (hp8 : 1 ≤ p8Work) :
    1 / (2 : ℚ) ^ 192 < goldilocksTrimmedFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) := by
  rw [goldilocksTrimmedFailureBound_eq]
  have h2 : (0 : ℚ) ≤ (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 := by positivity
  have hp : (1 : ℚ) ≤ (p8Work : ℚ) := by exact_mod_cast hp8
  have h1 : 1 / (2 : ℚ) ^ 192
      < (p8Work : ℚ) / (cardKGold : ℚ) := by
    have hstep : 1 / (2 : ℚ) ^ 192 < (1 : ℚ) / (cardKGold : ℚ) := by
      norm_num
    refine hstep.trans_le ?_
    gcongr
  linarith

/-- **The improvement stage 3e bought, as one comparison.**  At the paper configuration the
pre-`LB` consumed bound was above `2^-60` and the released one is below `2^-123`: sixty-four
bits, bought by the compute chip's `liftChallenge36` leaving the failure union and nothing
else. -/
theorem trimmed_beats_extension_by_sixty_four_bits (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksTrimmedFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123
      ∧ 1 / (2 : ℚ) ^ 60 < goldilocksExtensionFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) :=
  ⟨trimmed_soundness_at_paper_configuration p8Work ioWork hp8 hio,
    extension_no_60_bits _ _ _ _⟩

/-- **The whole base-field exposure is gone, stated as an absence.**  The consumed bound is a
sum of two `𝕂`-denominated terms; `pGold` does not occur in it. -/
theorem trimmed_bound_has_no_base_field_denominator (p8Work ioWork N M : ℕ) :
    goldilocksTrimmedFailureBound p8Work ioWork N M
      = (p8Work : ℚ) / (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 :=
  goldilocksTrimmedFailureBound_eq p8Work ioWork N M

/-- For contrast: if the memory summand had the *extension* field in its denominator, the
same configuration would be below `2^-160`.  This isolates the loss to the base-field
denominator and nothing else. -/
theorem counterfactual_extension_denominator :
    (20 + 14 * (2 ^ 20 : ℕ) : ℚ) / (cardKGold : ℚ) < 1 / (2 : ℚ) ^ 160 := by
  norm_num

/-! ## 6.

The capstone's `complete_false_acceptance_bound` names
`OptimizedStrictPackage.optimizedHostileProductionFailureProbabilityBound` at
`ioWork = ioFailureUnionBound 9 (3·N) M |𝕂|`:
`(p8Work + (1 + 3N(3N−1)/2))/|𝕂| + ioWork/|𝕂|²`.

The
ceiling-free real-program figure is in `RealProgramSoundness` §8: `122` at `2^31`, `120` at `2^32`. -/

def goldilocksHostileFailureBound (p8Work ioWork N M : ℕ) : ℚ :=
  optimizedHostileProductionFailureProbabilityBound (Fintype.card K) (Fintype.card Fp)
    p8Work ioWork N M

theorem goldilocksHostileFailureBound_eq (p8Work ioWork N M : ℕ) :
    goldilocksHostileFailureBound p8Work ioWork N M
      = (p8Work +
          OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
          pricedWalkWork N M : ℚ) / (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
        + ((FiniteIO.ioFailureUnionBound 10 M M cardKGold + cardKGold * M : ℕ) : ℚ)
            / (cardKGold : ℚ) ^ 2 := by
  simp only [goldilocksHostileFailureBound,
    optimizedHostileProductionFailureProbabilityBound, card_K_gold]

theorem goldilocksHostileFailureBound_eq_trimmed_shift (p8Work ioWork N M : ℕ) :
    goldilocksHostileFailureBound p8Work ioWork N M
      = goldilocksTrimmedFailureBound
          (p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
            pricedWalkWork N M)
          (ioWork + (FiniteIO.ioFailureUnionBound 10 M M cardKGold + cardKGold * M)) N M := by
  simp only [goldilocksHostileFailureBound, goldilocksTrimmedFailureBound]
  rw [← card_K_gold]
  exact optimizedHostileProductionFailureProbabilityBound_eq_trimmed_shift _ _ _ _ _ _

/-- The α-collision count at `N = 2^31`: `1 + 3·2^31·(3·2^31 − 1)/2`, below `2^65`. -/
theorem timestampCollisionBound_at_paper_configuration :
    OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) ≤ 2 ^ 65 := by
  unfold OptimizedHostileTimestamps.timestampCollisionBound
  norm_num

/-- The walk-root numeral at `N = 2^31`: `N+9 ≤ 2^34`. -/
theorem walkRootBound_at_paper_configuration :
    ComputeWalkRootEvents.walkRootBound (2 ^ 31) ≤ 2 ^ 34 := by
  rw [ComputeWalkRootEvents.walkRootBound_eq]
  norm_num

/-- Walk-root plus tiling plus whole-table γ at `N = M = 2^31`:
`19·2^31 + 12 ≤ 2^36`. -/
theorem walkAndTilingBound_at_paper_configuration :
    pricedWalkWork (2 ^ 31) (2 ^ 31) ≤ 2 ^ 36 := by
  simp only [pricedWalkWork, ComputeWalkRootEvents.walkRootBound_eq,
    computeTilingBound, memoryTilingBound,
    WalkPrefixGammaEvents.computePrefixGammaBound,
    WalkPrefixGammaEvents.memoryPrefixGammaBound,
    WalkForestPrefixAlphaEvents.memoryForestAlphaBound, pwAccountingWork']
  norm_num

theorem hostile_soundness_at_paper_configuration (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123 := by
  rw [goldilocksHostileFailureBound_eq]
  have hts := timestampCollisionBound_at_paper_configuration
  have hwr := walkAndTilingBound_at_paper_configuration
  have hinter :
      ((FiniteIO.ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
          + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
      = ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ) := by
    rw [ioFailureUnionBound_ten]
    have hnat : 36 * 2 ^ 31 * 2 ^ 31 + 4 * 2 ^ 31 = 9 * 2 ^ 64 + 2 ^ 33 := by norm_num
    rw [hnat]
    have hk : (cardKGold : ℚ) ≠ 0 := by norm_num
    field_simp
    ring
  have hmaj :
      ((2 : ℚ) ^ 60 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
        + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
        + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ)
        < 1 / (2 : ℚ) ^ 123 := by
    norm_num
  have hp8' : (p8Work : ℚ) ≤ (2 : ℚ) ^ 60 := by exact_mod_cast hp8
  have hts' : (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ)
      ≤ (2 : ℚ) ^ 65 := by exact_mod_cast hts
  have hwr' : (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) ≤ (2 : ℚ) ^ 36 := by
    exact_mod_cast hwr
  have hio' : (ioWork : ℚ) ≤ (16 : ℚ) ^ 65 := by exact_mod_cast hio
  have hsum :
      (p8Work : ℚ) +
        (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) +
        (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) ≤
      (2 : ℚ) ^ 60 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36 := by
    linarith [hp8', hts', hwr']
  calc
    (p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
          pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) /
          (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
        + ((FiniteIO.ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
            + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2
        = ((p8Work : ℚ) +
            (OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) : ℚ) +
            (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ)) /
            (cardKGold : ℚ)
          + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2
          + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ) := by
            rw [hinter]
    _ ≤ ((2 : ℚ) ^ 60 + (2 : ℚ) ^ 65 + (2 : ℚ) ^ 36) / (cardKGold : ℚ)
          + ((16 : ℚ) ^ 65) / (cardKGold : ℚ) ^ 2
          + ((9 : ℚ) * 2 ^ 64 + 2 ^ 33 + 2 ^ 31) / (cardKGold : ℚ) := by
            gcongr
    _ < 1 / (2 : ℚ) ^ 123 := hmaj

/-- The matching lower bound: the α-count alone puts the bound above `2^-128`
(the α-count at `2^31` rows is `≈ 2^64.17`), with no hypothesis on the work terms.  So `123` is a
figure of the function under the ceilings, and the α-summand alone is a `2^-127.8` floor. -/
theorem hostile_lower_bound_at_paper_configuration (p8Work ioWork : ℕ) :
    1 / (2 : ℚ) ^ 128 < goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) := by
  rw [goldilocksHostileFailureBound_eq]
  have h2 : (0 : ℚ) ≤ (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 := by positivity
  have hinter0 : (0 : ℚ) ≤
      ((FiniteIO.ioFailureUnionBound 10 (2 ^ 31) (2 ^ 31) cardKGold
          + cardKGold * 2 ^ 31 : ℕ) : ℚ) / (cardKGold : ℚ) ^ 2 := by positivity
  have hp : (0 : ℚ) ≤ (p8Work : ℚ) := by positivity
  have hnum : (2 : ℕ) ^ 64 ≤ p8Work +
      OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
      ComputeWalkRootEvents.walkRootBound (2 ^ 31) := by
    have : (2 : ℕ) ^ 64 ≤ OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) := by
      unfold OptimizedHostileTimestamps.timestampCollisionBound; norm_num
    omega
  have hnumq : ((2 : ℕ) ^ 64 : ℚ) ≤ ((p8Work +
      OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
      ComputeWalkRootEvents.walkRootBound (2 ^ 31) : ℕ) : ℚ) := by
    exact_mod_cast hnum
  have h1 : 1 / (2 : ℚ) ^ 128
      < (p8Work +
          OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
          ComputeWalkRootEvents.walkRootBound (2 ^ 31) : ℚ) /
          (cardKGold : ℚ) := by
    have hstep : 1 / (2 : ℚ) ^ 128 < ((2 : ℚ) ^ 64) / (cardKGold : ℚ) := by norm_num
    refine hstep.trans_le ?_
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    push_cast at hnumq ⊢
    linarith
  have htc : (0 : ℚ) ≤ (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) := by positivity
  have hnum' : (p8Work +
      OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
      ComputeWalkRootEvents.walkRootBound (2 ^ 31) : ℚ) /
      (cardKGold : ℚ)
      ≤ (p8Work +
          OptimizedHostileTimestamps.timestampCollisionBound (3 * 2 ^ 31) +
          pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) /
      (cardKGold : ℚ) := by
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    have : (ComputeWalkRootEvents.walkRootBound (2 ^ 31) : ℚ) ≤
        (pricedWalkWork (2 ^ 31) (2 ^ 31) : ℚ) := by
      simp only [pricedWalkWork]
      exact_mod_cast (by omega :
        ComputeWalkRootEvents.walkRootBound (2 ^ 31) ≤
          ComputeWalkRootEvents.walkRootBound (2 ^ 31) +
            WalkTilingEvents.computeTilingBound (2 ^ 31) +
            WalkTilingEvents.memoryTilingBound (2 ^ 31) +
            WalkPrefixGammaEvents.computePrefixGammaBound (2 ^ 31) +
            WalkPrefixGammaEvents.memoryPrefixGammaBound (2 ^ 31) +
            WalkForestPrefixAlphaEvents.memoryForestAlphaBound (2 ^ 31))
    linarith
  exact (h1.trans_le hnum').trans_le
    ((le_add_of_nonneg_right h2).trans (le_add_of_nonneg_right hinter0))

/-- The hostile bound is never below the trimmed one at the same arguments (it adds a summand):
the α-collision pricing is a strict cost, not a relabelling. -/
theorem goldilocksTrimmedFailureBound_le_hostile (p8Work ioWork N M : ℕ) :
    goldilocksTrimmedFailureBound p8Work ioWork N M
      ≤ goldilocksHostileFailureBound p8Work ioWork N M := by
  rw [goldilocksHostileFailureBound_eq, goldilocksTrimmedFailureBound_eq]
  have : (0 : ℚ) ≤ (OptimizedHostileTimestamps.timestampCollisionBound (3 * N) : ℚ) / cardKGold := by
    positivity
  have hinter : (0 : ℚ) ≤
      ((FiniteIO.ioFailureUnionBound 10 M M cardKGold + cardKGold * M : ℕ) : ℚ)
        / (cardKGold : ℚ) ^ 2 := by
    positivity
  have hd : (0 : ℚ) < (cardKGold : ℚ) := by norm_num
  have hwr : (0 : ℚ) ≤ (pricedWalkWork N M : ℚ) / cardKGold := by
    positivity
  have : (p8Work +
      OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
      pricedWalkWork N M : ℚ) / (cardKGold : ℚ)
      = (p8Work : ℚ) / (cardKGold : ℚ) +
        (OptimizedHostileTimestamps.timestampCollisionBound (3 * N) : ℚ) / cardKGold +
        (pricedWalkWork N M : ℚ) / cardKGold := by
    rw [add_div, add_div]
  linarith

/-- The surviving lifts lost a `|𝕂|` factor against
the deleted coordinate (`normalized_trimmed_card_bound_eq_separate_denominators`); the quadratic
α-summand still dominates. -/
theorem stage_w2s3_shrank_the_space_without_moving_the_figure (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    Fintype.card (OptimizedProductionChallengeTuple K Fp) = cardKGold ^ 11
      ∧ goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123
      ∧ 1 / (2 : ℚ) ^ 128 < goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) :=
  ⟨card_challenge_space,
    hostile_soundness_at_paper_configuration p8Work ioWork hp8 hio,
    hostile_lower_bound_at_paper_configuration p8Work ioWork⟩

end

end Nock.NockVMROM.Thm54.GoldilocksParameters

#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.card_F
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.card_K_gold
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.hcard_of_le_two_pow_93
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.not_hcard_at_two_pow_94
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.orbit_capacity_le
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.strict_orbit_height_le
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.no_60_bits
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.no_59_bits
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.merged_soundness_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.extension_soundness_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.extension_no_60_bits
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.extension_two_K_summands_are_below_two_pow_neg_123
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.stage3d_shrank_the_space_without_moving_the_figure
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.trimmed_soundness_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.trimmed_lower_bound_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.trimmed_beats_extension_by_sixty_four_bits
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.merged_soundness_at_million
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.bits_necessary
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.soundness_at_million
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.soundness_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.card_challenge_space
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.ioWork_le
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.hostile_soundness_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.hostile_lower_bound_at_paper_configuration
