/-
the ABSTRACT J-8 interface `RapAirJ`, at one fixed checked datum
`(Pb, Rg, c, r, g)`, mirroring `CleanJ8.lean:49`. No J-8 import (J-8 is on Lean 4.31).
Field numbering is as in the J-8 interface.
-/
import NockvmE2E.Rap.Frame
import NockvmE2E.Succ.Local
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

set_option autoImplicit false

open Polynomial

namespace NockvmE2E.J8

open NockvmE2E.Rap NockvmE2E.Succ

/-- **The abstract J-8 interface** (base field `B`, coin field `K`). `R` is fixed to `2` (J-8 has coins
sampled after rounds `0,1`; `α`, `ζ` are added after rounds `2`, `3`). -/
structure RapAirJ (B K : Type) [Field B] [Field K] [Algebra B K] [Fintype K] [DecidableEq K] where
  /-- 1: the coin frame (`frameJ8`, `FrameJ8.lean:34`). -/
  Φ0 : CoinFrame
  /-- 2: columns and their rounds (`TraceJ8.lean:55-72`). -/
  ι0 : Type
  fι : Fintype ι0
  dι : DecidableEq ι0
  colRound0 : ι0 → ℕ
  /-- 3: column rounds `≤ 2`. -/
  hround : ∀ j, colRound0 j ≤ 2
  /-- 4: every coin is sampled before `α` (after a round `< 2`). -/
  hcoin : ∀ i, Φ0.sampledAfter i < 2
  /-- 5: verifier-fixed (preprocessed) columns (`FixedPreprocessingRAP.preprocessing`). -/
  pre : ι0 → Option B[X]
  /-- 6: the public message (`MsgJ8'`), its finite code, and the decoding. -/
  Msg : Type
  Mcode : Type
  fM : Fintype Mcode
  dM : DecidableEq Mcode
  dec : Mcode → Msg
  /-- 7: the accept predicate (`AcceptsJ8V`, `AcceptsJ8V.lean:149`). -/
  Acc : Coins Φ0 K → Msg → (ι0 → B[X]) → Prop
  /-- 8: the claim (`Nock.Jet.HoldsN c`). -/
  Holds : Prop
  /-- 9: the priced bad summands (`allJ8X` at the present/absent list). -/
  summands : List (BadSummand Φ0 K (ι0 → B[X]) (TracesStaged Φ0 colRound0))
  /-- 10: POINTWISE soundness (the `hsound` lambdas of `LinkJ8NV.lean:736`, `LinkJ8A.lean:863`). -/
  sound : ∀ (χ : Coins Φ0 K) (M : Msg) (tr : ι0 → B[X]),
    Acc χ M tr → (∀ s ∈ summands, ¬ s.mem tr χ) → Holds
  /-- 11: the total price (`epsJ8X_lt_155_census32`). -/
  eps : epsilonOf summands ≤ 1 / 2 ^ 155
  /-- 12: each summand in one sampling round (NEW nockvm obligation N3). -/
  oneRound : ∀ s ∈ summands, OneRound s
  /-- 13 (union domain): the combined trace domain `H ⊇ ⋃ H_t`, the `T` tables with their domains `H_t`,
  row shifts `ω_t`, offset count `r`, per-table offsets `ω_t^k`, and the table of every column. -/
  H : Finset B
  T : ℕ
  Ht : Fin T → Finset B
  hHt : ∀ t, Ht t ⊆ H
  ωt : Fin T → B
  r : ℕ
  off : Fin T → Fin r → B
  hoff : ∀ t k, off t k = ωt t ^ (k : ℕ)
  tabC : ι0 → Fin T
  /-- 14: the flattened chip constraints (coins, public message, row-shifted columns), degree, and the table of
  every constraint. -/
  ns : ℕ
  tabS : Fin ns → Fin T
  d : ℕ
  /-- `d ≥ 2`, or every table domain is the whole `H` (one-table style; then the vanishing factor is `1`). -/
  hd2 : 2 ≤ d ∨ ∀ t, Ht t = H
  C : Coins Φ0 K → Msg → Fin ns → MvPolynomial (ι0 × Fin r) B
  hdeg : ∀ χ M i, (C χ M i).totalDegree ≤ d
  /-- 15: the constraints read all coins (all are sampled before `α`). -/
  hCreads : ∀ M i, ReadsOnC Φ0 Finset.univ (fun χ => C χ M i)
  /-- 16: the non-chip conjuncts on `M, χ` and the statement-level conjuncts. -/
  Pub : Coins Φ0 K → Msg → Prop
  StmtOK : Prop
  /-- 17: vanishing of the composed constraints on `H`, `Pub`, `StmtOK` and the fixed columns give `Acc`. -/
  acc_of : ∀ (χ : Coins Φ0 K) (M : Msg) (tr : ι0 → B[X]),
    (∀ i, ∀ x ∈ Ht (tabS i), (MvPolynomial.aeval
        (fun p : ι0 × Fin r => (tr p.1).comp (Polynomial.C (off (tabC p.1) p.2) * Polynomial.X)) (C χ M i)).eval x = 0) →
    Pub χ M → StmtOK → (∀ j c, pre j = some c → tr j = c) → Acc χ M tr
  /-- 18: caps used by the E2E numbers (counted on the J-8 side, N6). -/
  cap_ns : ns ≤ 2 ^ 20
  cap_d : 3 * (d - 1) + 1 ≤ 2 ^ 8
  cap_m : Fintype.card ι0 * r + 3 * (d - 1) ≤ 2 ^ 12
  cap_H : H.card ≤ 2 ^ 26

attribute [instance] RapAirJ.fι RapAirJ.dι RapAirJ.fM RapAirJ.dM

variable {B K : Type} [Field B] [Field K] [Algebra B K] [Fintype K] [DecidableEq K]

/-- The composed constraint `i` at the trace polynomials `tr` (the `RAP.compose` of `Core.lean:140`). -/
noncomputable def RapAirJ.compose (J : RapAirJ B K) (χ : Coins J.Φ0 K) (M : J.Msg) (tr : J.ι0 → B[X])
    (i : Fin J.ns) : B[X] :=
  MvPolynomial.aeval
    (fun p : J.ι0 × Fin J.r => (tr p.1).comp (Polynomial.C (J.off (J.tabC p.1) p.2) * Polynomial.X)) (J.C χ M i)

/-- `acc_of` in terms of `compose`. -/
theorem RapAirJ.acc_of' (J : RapAirJ B K) (χ : Coins J.Φ0 K) (M : J.Msg) (tr : J.ι0 → B[X])
    (h : ∀ i, ∀ x ∈ J.Ht (J.tabS i), (J.compose χ M tr i).eval x = 0) (hp : J.Pub χ M) (hs : J.StmtOK)
    (hpre : ∀ j c, J.pre j = some c → tr j = c) : J.Acc χ M tr :=
  J.acc_of χ M tr h hp hs hpre

/-- Pointwise soundness at every message code. -/
theorem RapAirJ.sound' (J : RapAirJ B K) (χ : Coins J.Φ0 K) (m : J.Mcode) (tr : J.ι0 → B[X])
    (h : J.Acc χ (J.dec m) tr) (hs : ∀ s ∈ J.summands, ¬ s.mem tr χ) : J.Holds :=
  J.sound χ (J.dec m) tr h hs

/-- Every priced coin of a summand is sampled in a round `< 2` (from `hcoin`). -/
theorem RapAirJ.coin_lt (J : RapAirJ B K) {s : BadSummand J.Φ0 K (J.ι0 → B[X]) (TracesStaged J.Φ0 J.colRound0)}
    (_hs : s ∈ J.summands) {i : Fin J.Φ0.n} (_ : i ∈ s.coins) : J.Φ0.sampledAfter i < 2 :=
  J.hcoin i

/-- Each summand's block is `< 2`. -/
theorem RapAirJ.blk_lt (J : RapAirJ B K) {s : BadSummand J.Φ0 K (J.ι0 → B[X]) (TracesStaged J.Φ0 J.colRound0)}
    (_hs : s ∈ J.summands) : blkOf s < 2 := by
  unfold blkOf
  split_ifs with h
  · exact J.hcoin _
  · omega

end NockvmE2E.J8
