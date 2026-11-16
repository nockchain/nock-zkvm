/-
the staged-RAP statement `rapJ` of an abstract J-8 interface
`J : RapAirJ B K` over WORD traces `ι → β` and the extended frame `ΦX = extFrame J.Φ0 2`, and its RAP-level
inputs: `SoundG` (from `J.sound`), `OneRound` of every summand, blocks `< 4`, the round bound
`roundBound ≤ epsilonOf ≤ 2^-155`.

The public message is NOT a protocol message here: it is the function `pread` of the
word trace (the fixed-point openings of the round-2 public columns), so `Mfin := Unit` and `Accepts` reads
`pread tr`. Model gap: Plonky3 observes the publics in the clear; here they sit in the round-2 commitment.
-/
import NockvmE2E.J8.Interface
import NockvmE2E.J8.Lift
import NockvmE2E.Rap.Bridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped ENNReal

namespace NockvmE2E.J8

open NockvmE2E.Rap NockvmE2E.Succ

variable {B K : Type} [Field B] [Field K] [Algebra B K] [Fintype K] [DecidableEq K]

/-- The word-trace layout of an interface: which word column carries each interface column, and its
decoding to a base-field polynomial (preprocessed columns decode to their fixed polynomial). -/
structure WordMap (J : RapAirJ B K) {ι : Type} (colRound : ι → ℕ) (β : Type) where
  col : J.ι0 → ι
  hcol : ∀ j, colRound (col j) = J.colRound0 j
  hround : ∀ j, colRound j ≤ 2
  dec : J.ι0 → β → B[X]
  hpre : ∀ j c, J.pre j = some c → ∀ w, dec j w = c

variable {J : RapAirJ B K} {ι β : Type} {colRound : ι → ℕ}

/-- The interface trace read off a word trace. -/
def WordMap.base (wm : WordMap J colRound β) (tr : Tr ι β) : J.ι0 → B[X] :=
  fun j => wm.dec j (tr (wm.col j))

/-- The base trace of a word trace satisfies the fixed-column binding. -/
theorem WordMap.base_pre (wm : WordMap J colRound β) (tr : Tr ι β) :
    ∀ j c, J.pre j = some c → wm.base tr j = c := fun j c h => wm.hpre j c h _

/-- Pull a summand back from interface traces to word traces. -/
noncomputable def pullW (wm : WordMap J colRound β)
    (s : BadSummand J.Φ0 K (J.ι0 → B[X]) (TracesStaged J.Φ0 J.colRound0)) :
    BadSummand J.Φ0 K (Tr ι β) (TracesStaged J.Φ0 colRound) :=
  pullback wm.base (staged_colMap colRound J.colRound0 wm.col wm.hcol wm.dec) s

/-- **The staged-RAP statement of the interface** (over word traces, on `ΦX`). -/
noncomputable def rapJ (J : RapAirJ B K) {ι : Type} {colRound : ι → ℕ} {β : Type}
    (wm : WordMap J colRound β) (pread : Tr ι β → J.Msg) :
    RapStatement (extFrame J.Φ0 2) K ι β colRound where
  M0 := Unit
  Mfin := Unit
  summands _ := (J.summands.map (pullW wm)).map (liftX wm.hround)
  Accepts _ tr _ χ := J.Acc (restr 2 χ) (pread tr) (wm.base tr)
  Holds := J.Holds

/-! ### Pointwise soundness -/

/-- **`SoundG (rapJ J wm pread)`** from the interface's pointwise soundness. -/
theorem soundG_rapJ (wm : WordMap J colRound β) (pread : Tr ι β → J.Msg) : SoundG (rapJ J wm pread) := by
  intro m0 tr fin χ hacc hall
  refine J.sound (restr 2 χ) (pread tr) (wm.base tr) hacc ?_
  intro s hs hm
  apply hall (liftX wm.hround (pullW wm s))
  · exact List.mem_map.mpr ⟨pullW wm s, List.mem_map_of_mem hs, rfl⟩
  · exact (mem_liftX wm.hround (pullW wm s) tr χ).2 hm

/-! ### `OneRound` and blocks -/

theorem oneRound_liftX {R : ℕ} {ι β : Type} {colRound : ι → ℕ} {Φ : CoinFrame} [Zero K]
    (hR : ∀ j, colRound j ≤ R) {s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)}
    (h : OneRound s) : OneRound (liftX hR s) where
  ne := h.ne.map
  same i hi i' hi' := by
    obtain ⟨a, ha, rfl⟩ := sampledAfter_liftX hR s hi
    obtain ⟨b, hb, rfl⟩ := sampledAfter_liftX hR s hi'
    rw [sampledAfter_extC, sampledAfter_extC]
    exact h.same a ha b hb
  dep_le i hi i' hi' := by
    obtain ⟨a, ha, rfl⟩ : ∃ a ∈ s.dep, i = extC Φ R a := by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hi
      exact ⟨y, hy, rfl⟩
    obtain ⟨b, hb, rfl⟩ := sampledAfter_liftX hR s hi'
    rw [sampledAfter_extC, sampledAfter_extC]
    exact h.dep_le a ha b hb

theorem blkOf_liftX_lt {R : ℕ} {ι β : Type} {colRound : ι → ℕ} {Φ : CoinFrame} [Zero K]
    (hR : ∀ j, colRound j ≤ R) (s : BadSummand Φ K (Tr ι β) (TracesStaged Φ colRound)) {b : ℕ}
    (hb : ∀ i ∈ s.coins, Φ.sampledAfter i < b) (hb0 : 0 < b) : blkOf (liftX hR s) < b := by
  unfold blkOf
  split_ifs with h
  · obtain ⟨a, ha, he⟩ := sampledAfter_liftX hR s h.choose_spec
    rw [he, sampledAfter_extC]
    exact hb a ha
  · exact hb0

theorem oneRound_rapJ (wm : WordMap J colRound β) (pread : Tr ι β → J.Msg) :
    ∀ m0, ∀ s ∈ (rapJ J wm pread).summands m0, OneRound s := by
  intro m0 s hs
  obtain ⟨s1, hs1, rfl⟩ := List.mem_map.mp hs
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs1
  have h0 := J.oneRound s0 hs0
  exact oneRound_liftX wm.hround (s := pullW wm s0) ⟨h0.ne, h0.same, h0.dep_le⟩

theorem blk_lt_rapJ (wm : WordMap J colRound β) (pread : Tr ι β → J.Msg) :
    ∀ m0, ∀ s ∈ (rapJ J wm pread).summands m0, blkOf s < 4 := by
  intro m0 s hs
  obtain ⟨s1, hs1, rfl⟩ := List.mem_map.mp hs
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs1
  exact blkOf_liftX_lt wm.hround (pullW wm s0) (b := 2) (fun i _ => J.hcoin i) (by norm_num)
    |>.trans (by norm_num)

theorem card_rapJ (_J : RapAirJ B K) : 1 < Fintype.card K := Fintype.one_lt_card

/-! ### Price -/

theorem epsilonOf_rapJ (wm : WordMap J colRound β) (pread : Tr ι β → J.Msg) (m0 : (rapJ J wm pread).M0) :
    epsilonOf ((rapJ J wm pread).summands m0) = epsilonOf J.summands := by
  show epsilonOf ((J.summands.map (pullW wm)).map (liftX wm.hround)) = _
  rw [epsilonOf_map_liftX]
  exact epsilonOf_map_pullback wm.base (staged_colMap colRound J.colRound0 wm.col wm.hcol wm.dec) _

/-- **`roundBound ≤ epsilonOf`**. -/
theorem roundBound_rapJ_le_eps (wm : WordMap J colRound β) (pread : Tr ι β → J.Msg) (m0 : (rapJ J wm pread).M0) (r : ℕ) :
    roundBound (rapJ J wm pread) blkOf m0 r ≤ ENNReal.ofReal ((epsilonOf J.summands : ℚ) : ℝ) := by
  have hK : 0 < Fintype.card K := Fintype.card_pos
  rw [← epsilonOf_rapJ wm pread m0]
  exact sum_round_le hK ((rapJ J wm pread).summands m0) blkOf r

/-- **`roundBound ≤ 2^-155`** (from `J.eps`). -/
theorem roundBound_rapJ_le (wm : WordMap J colRound β) (pread : Tr ι β → J.Msg) (m0 : (rapJ J wm pread).M0) (r : ℕ) :
    roundBound (rapJ J wm pread) blkOf m0 r ≤ ENNReal.ofReal (1 / 2 ^ 155) := by
  refine (roundBound_rapJ_le_eps wm pread m0 r).trans (ENNReal.ofReal_le_ofReal ?_)
  have := (Rat.cast_le (K := ℝ)).2 J.eps
  push_cast at this
  exact this

end NockvmE2E.J8
