/-
  Nock/NockVMROM/Thm54/VclL/Handle/ChoiceQ.lean

  Additive: a new module, no existing module edited.

  The reduction re-fills the handle columns of a `𝕂′`-accepted trace at a `𝕂` coin pair `(γ, ρ)` and
  runs `hsoundVS` there.  `hsoundVS` reads the two handle summands `ioSummandHX / ioSummandHP` at that
  pair, whose events `evX / evP` read ONLY the round-0 columns of the trace (`IOVS` §1–2: compute
  `< 43`, walk twin `< 25`, cell twin `< 130`), which the re-fill does not touch.  So the pair is chosen
  outside a FIXED set, and this module shows the set is never all of `𝕂²`:

  * `ioUB_pair_lt` — the arithmetic: `ioFUB 5 a t c + ioFUB 5 n (2w) c < c²` when `a, t, n, w < p`,
    `53 ≤ p` and `p³ ≤ c`;
  * `ringChar_cube_le_card` — `p³ ≤ |𝕂|` from a basis `Fin 3 → 𝕂` over a finite `𝔽` (`p = char 𝔽`);
  * **`exists_pair_outside`** — for every VS trace pair `tr` and every verifier datum passing the VS
    checks (with `2^63 < p`, which `GoodCVSQ` gives at every accepted coin), some `(γ, ρ) ∈ 𝕂²` lies
    outside `evX tr ∪ evP tr`.

  **No new soundness hypothesis.**  The choice is existential (the reduction needs one good pair, not
  a probability), so no failure mass is priced for it; the `𝕂′` coins' own failure mass is the four-coin
  handle summands of the VSQ list.  The size facts are the VS consumer checks `hcons` and `hrowsM`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.IOVS
import Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ChoiceQ

open Nock Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.IOVS Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Module

noncomputable section

/-! ## 1. Arithmetic -/

/-- **The two handle failure bounds together are below `c²`.** -/
theorem ioUB_pair_lt (p c a t n w : ℕ) (ha : a < p) (ht : t < p) (hn : n < p) (hw : w < p)
    (hp : 53 ≤ p) (hc : p ^ 3 ≤ c) :
    ioFailureUnionBound 5 a t c + ioFailureUnionBound 5 n (2 * w) c < c * c := by
  unfold ioFailureUnionBound
  set s := a + t with hs
  set s' := n + 2 * w with hs'
  have hs2 : s < 2 * p := by omega
  have hs3 : s' < 3 * p := by omega
  have hX : 4 * (s * s) + 2 * s + (4 * (s' * s') + 2 * s') < c := by
    have h1 : s * s ≤ (2 * p) * (2 * p) := Nat.mul_le_mul hs2.le hs2.le
    have h2 : s' * s' ≤ (3 * p) * (3 * p) := Nat.mul_le_mul hs3.le hs3.le
    have h3 : 52 * (p * p) + 10 * p < p ^ 3 := by
      have : p ^ 3 = p * (p * p) := by ring
      rw [this]
      have hpp : 53 * (p * p) ≤ p * (p * p) := Nat.mul_le_mul_right _ hp
      have h10 : 10 * p < p * p := by
        have : 53 * p ≤ p * p := Nat.mul_le_mul_right _ hp
        have : 0 < p := by omega
        omega
      omega
    have : 4 * (s * s) + 2 * s + (4 * (s' * s') + 2 * s') ≤ 52 * (p * p) + 10 * p := by
      nlinarith
    omega
  have hc0 : 0 < c := by
    have : 0 < p ^ 3 := by positivity
    omega
  have e : s * s * (5 - 1) * c + c * (2 * s) + (s' * s' * (5 - 1) * c + c * (2 * s')) =
      c * (4 * (s * s) + 2 * s + (4 * (s' * s') + 2 * s')) := by
    simp only [show (5 : ℕ) - 1 = 4 by rfl]; ring
  rw [e]
  exact Nat.mul_lt_mul_of_pos_left hX hc0

/-! ## 2. `p³ ≤ |𝕂|` -/

section Card
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]

/-- `|𝕂| = |𝔽|³` from a basis indexed by `Fin 3`. -/
theorem card_K_eq (b : Basis (Fin 3) F K) : Fintype.card K = Fintype.card F ^ 3 := by
  haveI : FiniteDimensional F K := Module.Finite.of_basis b
  rw [Module.card_eq_pow_finrank (K := F) (V := K), Module.finrank_eq_card_basis b, Fintype.card_fin]

/-- `char 𝔽 ≤ |𝔽|`. -/
theorem ringChar_le_card : ringChar F ≤ Fintype.card F :=
  Nat.le_of_dvd Fintype.card_pos (ringChar.dvd (FiniteField.cast_card_eq_zero F))

/-- **`p³ ≤ |𝕂|`.** -/
theorem ringChar_cube_le_card (b : Basis (Fin 3) F K) : ringChar F ^ 3 ≤ Fintype.card K := by
  rw [card_K_eq b]
  exact Nat.pow_le_pow_left ringChar_le_card 3

end Card

/-! ## 3. A pair outside both handle events -/

section Choice
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (hT hP hC : ℕ)

/-- **The two handle events miss some pair**, from the size facts alone. -/
theorem exists_pair_outside_of_sizes (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC)
    (hX : 3 * V.N + V.memRows (tWS hT hP) < ringChar F) (hPn : 2 * V.N < ringChar F)
    (hT' : V.memRows (tCS hT hP) < ringChar F) (hW : V.memRows (tWS hT hP) < ringChar F)
    (hp : 53 ≤ ringChar F) :
    ∃ q : K × K, q ∉ evX hT hP hC V tr ∧ q ∉ evP hT hP hC V tr := by
  classical
  by_contra hno
  push Not at hno
  have hsub : (Finset.univ : Finset (K × K)) ⊆ evX hT hP hC V tr ∪ evP hT hP hC V tr := by
    intro q _
    by_cases hq : q ∈ evX hT hP hC V tr
    · exact Finset.mem_union_left _ hq
    · exact Finset.mem_union_right _ (hno q hq)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_prod] at hcard
  have hU := (Finset.card_union_le (evX hT hP hC V tr) (evP hT hP hC V tr)).trans
    (Nat.add_le_add (evX_card hT hP hC V tr) (evP_card hT hP hC V tr))
  have hlt := ioUB_pair_lt (ringChar F) (Fintype.card K) _ _ _ _ hX hT' hPn hW hp
    (ringChar_cube_le_card V.basis)
  omega

/-- **`exists_pair_outside`**: at every verifier datum passing the VS checks (any consumer-bound
function agreeing with the VS cores' at the two handle accumulators), with `2^63 < p`, every VS trace
pair has a `𝕂` coin pair outside both handle IO events. -/
theorem exists_pair_outside (V : VerifierData F K hC (shapeVS hT hP)) (tr : TrVS F hT hP hC)
    {cb : Fin 5 → ℕ} {pIO : ℕ} (hV : V.Checks cb pIO) (hpIO : pIO = ringChar F)
    (hcb3 : cb 3 = 3 * V.N + V.memRows (tWS hT hP)) (hcb4 : cb 4 = 2 * V.N)
    (hp : 2 ^ 63 < ringChar F) :
    ∃ q : K × K, q ∉ evX hT hP hC V tr ∧ q ∉ evP hT hP hC V tr := by
  have hKF : ringChar K = ringChar F := (Algebra.ringChar_eq F K).symm
  have h3 := hV.hcons 3
  have h4 := hV.hcons 4
  rw [hcb3, hpIO] at h3
  rw [hcb4, hpIO] at h4
  have hT' := hV.hrowsM (tCS hT hP)
  have hW := hV.hrowsM (tWS hT hP)
  rw [hKF] at hT' hW
  exact exists_pair_outside_of_sizes hT hP hC V tr h3 h4 hT' hW (by omega)

/-- The VS cores' consumer bound at the two handle accumulators (`reqBoundVS + internalBoundVS`). -/
theorem vs_cb3 (V : VerifierData F K hC (shapeVS hT hP)) :
    reqBoundVS hT hP hC V 3 + internalBoundVS hT hP hC V 3 = 3 * V.N + V.memRows (tWS hT hP) := rfl

theorem vs_cb4 (V : VerifierData F K hC (shapeVS hT hP)) :
    reqBoundVS hT hP hC V 4 + internalBoundVS hT hP hC V 4 = 2 * V.N := by
  simp [reqBoundVS, internalBoundVS]

end Choice

/-! ## 4. The verifier datum at the VS shape

`shapeVSQ` and `shapeVS` differ only in the table widths and round maps; the verifier datum (claim,
sizes, nodes, orbits) is the same.  `toVSV` re-types it; the checks transport. -/

section Transport
variable {F K : Type} [Field F] [Field K] [Algebra F K] (hT hP hC : ℕ)

theorem height_eq (t : Fin 2) :
    ((shapeVSQ hT hP).table t).height = ((shapeVS hT hP).table t).height := by
  show (if (t : ℕ) = 0 then (⟨238, colRoundCHQ, hT⟩ : TableSpec) else ⟨166, colRoundWHQ, hP⟩).height =
    (if (t : ℕ) = 0 then (⟨232, colRoundCH, hT⟩ : TableSpec) else ⟨151, colRoundWH, hP⟩).height
  split_ifs <;> rfl

/-- Re-type an orbit along a height equality. -/
def castOrbit {a b : ℕ} (h : a = b) (o : StrictOrbitDomain F 3 a) : StrictOrbitDomain F 3 b := h ▸ o

@[simp] theorem castOrbit_ω {a b : ℕ} (h : a = b) (o : StrictOrbitDomain F 3 a) :
    (castOrbit h o).ω = o.ω := by subst h; rfl

/-- **The VSQ verifier datum at the VS shape.** -/
def toVSV (V : VerifierData F K hC (shapeVSQ hT hP)) : VerifierData F K hC (shapeVS hT hP) where
  claim := V.claim
  N := V.N
  hN := V.hN
  Ksz := V.Ksz
  basis := V.basis
  orbitC := V.orbitC
  computeNodes := V.computeNodes
  memRows := V.memRows
  hM := V.hM
  orbitM := fun t => castOrbit (height_eq hT hP t) (V.orbitM t)
  memNodes := V.memNodes

@[simp] theorem toVSV_claim (V : VerifierData F K hC (shapeVSQ hT hP)) : (toVSV hT hP hC V).claim = V.claim :=
  rfl

/-- **The checks transport** (same consumer bound, same IO characteristic). -/
theorem toVSV_checks (V : VerifierData F K hC (shapeVSQ hT hP)) {cb : Fin 5 → ℕ} {pIO : ℕ}
    (hV : V.Checks cb pIO) : (toVSV hT hP hC V).Checks cb pIO where
  hcapC := hV.hcapC
  hcapM t := by
    have := hV.hcapM t
    rw [height_eq hT hP t] at this
    exact this
  hrowsC := hV.hrowsC
  hrowsM := hV.hrowsM
  hKsz := hV.hKsz
  hF := hV.hF
  hp := hV.hp
  hclaim := hV.hclaim
  computeNodes_injective := hV.computeNodes_injective
  memNodes_injective := hV.memNodes_injective
  hcons := hV.hcons
  hadjC := hV.hadjC
  hadjM t i hi := by
    show V.memNodes t _ = V.memNodes t i * (castOrbit (height_eq hT hP t) (V.orbitM t)).ω
    rw [castOrbit_ω]; exact hV.hadjM t i hi

/-- The VSQ cores' consumer bound is the VS cores' (pointwise, at the transported datum). -/
theorem cb_eq (V : VerifierData F K hC (shapeVSQ hT hP)) (a : Fin 5) :
    reqBoundVSQ hT hP hC V a + internalBoundVSQ hT hP hC V a =
      reqBoundVS hT hP hC (toVSV hT hP hC V) a + internalBoundVS hT hP hC (toVSV hT hP hC V) a := rfl

end Transport

/-! ## 5. The watch item at the VSQ instance -/

section AtVSQ
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (hT hP hC : ℕ)

/-- **The choice of `(γ, ρ)` needs no new hypothesis**: at every VSQ verifier datum passing the VSQ
checks (as `StandaloneG.soundness` supplies them) and with `2^63 < p` (from `GoodCVSQ` at any accepted
coin), every VS trace pair — in particular every re-fill of an accepted VSQ trace — has a `𝕂` coin
pair outside both handle IO events of the transported datum. -/
theorem exists_pair_outsideQ (V : VerifierData F K hC (shapeVSQ hT hP))
    (hV : V.Checks (fun a => reqBoundVSQ hT hP hC V a + internalBoundVSQ hT hP hC V a)
      (ringChar (Quad (algebraMap F K δF))))
    (hp : 2 ^ 63 < ringChar F) (tr : TrVS F hT hP hC) :
    ∃ q : K × K, q ∉ evX hT hP hC (toVSV hT hP hC V) tr ∧ q ∉ evP hT hP hC (toVSV hT hP hC V) tr :=
  exists_pair_outside hT hP hC (toVSV hT hP hC V) tr (toVSV_checks hT hP hC V hV)
    (Chips.ChipRAP.ringChar_quad_eq δF) (vs_cb3 hT hP hC (toVSV hT hP hC V)) (vs_cb4 hT hP hC (toVSV hT hP hC V)) hp

end AtVSQ

end

end Nock.NockVMROM.Thm54.VclL.Handle.ChoiceQ
